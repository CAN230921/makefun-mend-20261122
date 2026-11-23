// mend: one patch tool for every AI edit format (SPEC.md v1).
// Node 22+, standard library only. Run as `node main.ts [options] [PATCH]`.

import { mkdirSync, readdirSync, readFileSync, rmdirSync, rmSync, statSync, writeFileSync, writeSync } from 'node:fs';
import { dirname } from 'node:path';

const FORMATS = ['auto', 'unified', 'search-replace', 'v4a', 'json'];

class Exit2 {
  readonly line: string;
  constructor(line: string) {
    this.line = line;
  }
}

class Fail {
  readonly code: string;
  readonly path: string;
  constructor(code: string, path: string) {
    this.code = code;
    this.path = path;
  }
}

interface ParsedFile {
  lines: string[];
  br: '\r\n' | '\n';
  final: boolean;
}

interface BodyItem {
  kind: ' ' | '-' | '+';
  text: string;
  noEol: boolean;
}

interface UnifiedHunk {
  oldStart: number;
  body: BodyItem[];
}

interface UnifiedSection {
  gitOld: string | null;
  gitNew: string | null;
  renameFrom: string | null;
  renameTo: string | null;
  dashOld: string | null;
  dashNew: string | null;
  hasDashHeader: boolean;
  isNew: boolean;
  isDeleted: boolean;
  hunks: UnifiedHunk[];
}

interface V4aChunk {
  anchor: string;
  body: BodyItem[];
  eof: boolean;
}

const blank = (s: string): boolean => s.trim() === '';

const trimSpaces = (s: string): string => s.replace(/^ +| +$/g, '');

const stripTrailingSpaceTab = (s: string): string => s.replace(/[ \t]+$/, '');

const stripBothSpaceTab = (s: string): string => s.replace(/^[ \t]+|[ \t]+$/g, '');

const leadingSpaceTab = (s: string): string => s.match(/^[ \t]*/)![0];

function patchLines(text: string): string[] {
  if (text === '') return [];
  const lines = text.split('\n');
  if (text.endsWith('\n')) lines.pop();
  return lines.map((l) => (l.endsWith('\r') ? l.slice(0, -1) : l));
}

function safe(p: string): boolean {
  return p !== '' && !p.startsWith('/') && !p.includes('\\') && p.split('/').every((s) => s !== '' && s !== '.' && s !== '..');
}

function splitFile(text: string): ParsedFile {
  if (text === '') return { lines: [], br: '\n', final: false };
  const nl = text.indexOf('\n');
  const br: '\r\n' | '\n' = nl > 0 && text[nl - 1] === '\r' ? '\r\n' : '\n';
  const lines = text.split(br);
  const final = text.endsWith(br);
  if (final) lines.pop();
  return { lines, br, final };
}

function joinFile(lines: string[], br: '\r\n' | '\n', final: boolean): string {
  if (lines.length === 0) return '';
  return lines.join(br) + (final ? br : '');
}

/** Virtual filesystem tree tracking original contents, current state, and successful moves. */
class Tree {
  private readonly orig = new Map<string, string | null>();
  readonly now = new Map<string, string | null>();
  readonly moves: Array<[string, string]> = [];

  original(p: string): string | null {
    if (!this.orig.has(p)) {
      let v: string | null = null;
      try {
        if (statSync(p).isFile()) v = readFileSync(p, 'utf8');
      } catch {
        v = null;
      }
      this.orig.set(p, v);
    }
    return this.orig.get(p)!;
  }

  get(p: string): string | null {
    return this.now.has(p) ? this.now.get(p)! : this.original(p);
  }
}

type Edit = (tree: Tree) => void;

// --- Section 4: Format detection ---

function detect(lines: string[]): string | null {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) return null;
  if (lines[first]!.trim() === '*** Begin Patch') return 'v4a';
  const c = lines[first]!.trimStart()[0];
  if (c === '[' || c === '{') return 'json';
  if (lines.some((l) => l.trimEnd() === '<<<<<<< SEARCH')) return 'search-replace';
  if (lines.some((l, i) => l.startsWith('diff --git ') || (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')))) return 'unified';
  return null;
}

// --- Section 5: 3-tier line matching and re-indentation ---

function normalizeForTier(line: string, tier: number): string {
  if (tier === 0) return line;
  if (tier === 1) return stripTrailingSpaceTab(line);
  return stripBothSpaceTab(line);
}

function findOccurrences(
  fileLines: string[],
  oldLines: string[],
  strict: boolean,
  minPos: number,
  maxPos: number,
): { tier: number; positions: number[] } | null {
  const hi = Math.min(maxPos, fileLines.length - oldLines.length);
  if (oldLines.length === 0 || minPos > hi) return null;
  const maxTier = strict ? 0 : 2;
  const winEnd = hi + oldLines.length;
  for (let tier = 0; tier <= maxTier; tier += 1) {
    const oldNorm = tier === 0 ? oldLines : oldLines.map((l) => normalizeForTier(l, tier));
    const positions: number[] = [];
    const firstOld = oldNorm[0]!;
    if (tier === 0) {
      for (let pos = minPos; pos <= hi; pos += 1) {
        if (fileLines[pos] !== firstOld) continue;
        let ok = true;
        for (let k = 1; k < oldNorm.length; k += 1) {
          if (fileLines[pos + k] !== oldNorm[k]) {
            ok = false;
            break;
          }
        }
        if (ok) positions.push(pos);
      }
    } else {
      const winNorm = new Array<string>(winEnd - minPos);
      for (let idx = minPos; idx < winEnd; idx += 1) {
        winNorm[idx - minPos] = normalizeForTier(fileLines[idx]!, tier);
      }
      const limit = hi - minPos;
      for (let rel = 0; rel <= limit; rel += 1) {
        if (winNorm[rel] !== firstOld) continue;
        let ok = true;
        for (let k = 1; k < oldNorm.length; k += 1) {
          if (winNorm[rel + k] !== oldNorm[k]) {
            ok = false;
            break;
          }
        }
        if (ok) positions.push(minPos + rel);
      }
    }
    if (positions.length > 0) return { tier, positions };
  }
  return null;
}

function reindentLine(line: string, filePrefix: string, patchPrefix: string): string {
  if (!blank(line) && line.startsWith(patchPrefix)) {
    return filePrefix + line.slice(patchPrefix.length);
  }
  return line;
}

function buildBodyReplacement(body: BodyItem[], fileLines: string[], pos: number, tier: number, firstOldLine: string): string[] {
  const filePrefix = tier === 2 ? leadingSpaceTab(fileLines[pos]!) : '';
  const patchPrefix = tier === 2 ? leadingSpaceTab(firstOldLine) : '';
  const out: string[] = [];
  let oldIdx = 0;
  for (const item of body) {
    if (item.kind === ' ') {
      out.push(fileLines[pos + oldIdx]!);
      oldIdx += 1;
    } else if (item.kind === '-') {
      oldIdx += 1;
    } else {
      out.push(tier === 2 ? reindentLine(item.text, filePrefix, patchPrefix) : item.text);
    }
  }
  return out;
}

// --- Section 6: Unified diffs ---

function parseDiffGitLine(line: string): [string, string] | null {
  if (!line.startsWith('diff --git a/')) return null;
  const rest = line.slice('diff --git '.length);
  // Check exact equal-path split first (handles paths containing " b/").
  if (rest.length >= 5 && (rest.length - 1) % 2 === 0) {
    const half = (rest.length - 1) / 2;
    if (rest[half] === ' ' && rest.startsWith('a/') && rest.slice(half + 1, half + 3) === 'b/') {
      const x = rest.slice(2, half);
      const y = rest.slice(half + 3);
      if (x.length > 0 && x === y) return [x, y];
    }
  }
  const sepIdx = rest.indexOf(' b/', 2);
  if (sepIdx < 0) return null;
  const x = rest.slice(2, sepIdx);
  const y = rest.slice(sepIdx + 3);
  if (x.length === 0 || y.length === 0) return null;
  return [x, y];
}

function parseUnifiedDashPath(line: string): string {
  let rest = line.slice(4);
  const tab = rest.indexOf('\t');
  if (tab >= 0) rest = rest.slice(0, tab);
  rest = trimSpaces(rest);
  if (rest === '/dev/null') return '/dev/null';
  if (rest.startsWith('a/') || rest.startsWith('b/')) return rest.slice(2);
  return rest;
}

function makeUnifiedEdit(sec: UnifiedSection, strict: boolean): Edit {
  const oldPath = sec.dashOld ?? sec.renameFrom ?? sec.gitOld ?? '';
  const newPath = sec.dashNew ?? sec.renameTo ?? sec.gitNew ?? '';
  const isCreation = sec.isNew || oldPath === '/dev/null';
  const isDeletion = !isCreation && (sec.isDeleted || newPath === '/dev/null');

  if (isCreation) {
    return (tree) => {
      if (!safe(newPath)) throw new Fail('unsafe', newPath);
      if (tree.get(newPath) !== null) throw new Fail('exists', newPath);
      const added: BodyItem[] = [];
      for (const h of sec.hunks) {
        for (const item of h.body) {
          if (item.kind === '+') added.push(item);
        }
      }
      if (added.length === 0) {
        tree.now.set(newPath, '');
      } else {
        const final = !added[added.length - 1]!.noEol;
        tree.now.set(newPath, joinFile(added.map((x) => x.text), '\n', final));
      }
    };
  }

  if (isDeletion) {
    return (tree) => {
      if (!safe(oldPath)) throw new Fail('unsafe', oldPath);
      if (tree.get(oldPath) === null) throw new Fail('missing', oldPath);
      tree.now.set(oldPath, null);
    };
  }

  const isMove = oldPath !== newPath;

  return (tree) => {
    if (!safe(oldPath)) throw new Fail('unsafe', oldPath);
    if (isMove && !safe(newPath)) throw new Fail('unsafe', newPath);
    const before = tree.get(oldPath);
    if (before === null) throw new Fail('missing', oldPath);
    if (isMove && tree.get(newPath) !== null) throw new Fail('exists', newPath);

    let resultText: string;
    if (sec.hunks.length === 0) {
      resultText = before;
    } else {
      const parsed = splitFile(before);
      const fileLines = parsed.lines;
      let final = parsed.final;
      let drift = 0;

      for (const h of sec.hunks) {
        const oldLines: string[] = [];
        const newLines: string[] = [];
        let lastOutputNoEol = false;
        for (const item of h.body) {
          if (item.kind === ' ') {
            oldLines.push(item.text);
            newLines.push(item.text);
            lastOutputNoEol = item.noEol;
          } else if (item.kind === '-') {
            oldLines.push(item.text);
          } else {
            newLines.push(item.text);
            lastOutputNoEol = item.noEol;
          }
        }

        if (oldLines.length === 0) {
          const insertPos = Math.max(0, Math.min(fileLines.length, h.oldStart + drift));
          const atEnd = insertPos === fileLines.length;
          fileLines.splice(insertPos, 0, ...newLines);
          if (atEnd) final = !lastOutputNoEol;
          drift += newLines.length;
        } else {
          const found = findOccurrences(fileLines, oldLines, strict, 0, fileLines.length - oldLines.length);
          if (found === null) throw new Fail('no-match', oldPath);
          const target = h.oldStart - 1 + drift;
          let bestPos = found.positions[0]!;
          let bestDist = Math.abs(bestPos - target);
          for (let j = 1; j < found.positions.length; j += 1) {
            const candidate = found.positions[j]!;
            const dist = Math.abs(candidate - target);
            if (dist < bestDist) {
              bestPos = candidate;
              bestDist = dist;
            }
          }
          const runsToEnd = bestPos + oldLines.length === fileLines.length;
          const replacement = buildBodyReplacement(h.body, fileLines, bestPos, found.tier, oldLines[0]!);
          fileLines.splice(bestPos, oldLines.length, ...replacement);
          if (runsToEnd) final = !lastOutputNoEol;
          drift += replacement.length - oldLines.length;
        }
      }

      resultText = joinFile(fileLines, parsed.br, final);
    }

    if (isMove) {
      tree.now.set(oldPath, null);
      tree.now.set(newPath, resultText);
      tree.moves.push([oldPath, newPath]);
    } else {
      tree.now.set(oldPath, resultText);
    }
  };
}

function unifiedEdits(lines: string[], strict: boolean): Edit[] {
  const sections: UnifiedSection[] = [];
  let cur: UnifiedSection | null = null;
  let inHeader = false;

  let i = 0;
  while (i < lines.length) {
    const line = lines[i]!;

    if (line === 'diff --git' || line.startsWith('diff --git ')) {
      const paths = parseDiffGitLine(line);
      if (paths === null) throw new Exit2(`error: parse ${i + 1}`);
      cur = {
        gitOld: paths[0],
        gitNew: paths[1],
        renameFrom: null,
        renameTo: null,
        dashOld: null,
        dashNew: null,
        hasDashHeader: false,
        isNew: false,
        isDeleted: false,
        hunks: [],
      };
      sections.push(cur);
      inHeader = true;
      i += 1;
      continue;
    }

    if (line.startsWith('--- ')) {
      const next = lines[i + 1];
      const nextIsPlus = next !== undefined && next.startsWith('+++ ');
      if (cur !== null && inHeader && !cur.hasDashHeader) {
        if (!nextIsPlus) throw new Exit2(`error: parse ${i + 2}`);
        cur.dashOld = parseUnifiedDashPath(line);
        cur.dashNew = parseUnifiedDashPath(next!);
        cur.hasDashHeader = true;
        i += 2;
        continue;
      }
      if (nextIsPlus) {
        cur = {
          gitOld: null,
          gitNew: null,
          renameFrom: null,
          renameTo: null,
          dashOld: parseUnifiedDashPath(line),
          dashNew: parseUnifiedDashPath(next!),
          hasDashHeader: true,
          isNew: false,
          isDeleted: false,
          hunks: [],
        };
        sections.push(cur);
        inHeader = true;
        i += 2;
        continue;
      }
      if (cur !== null && inHeader) {
        throw new Exit2(`error: parse ${i + 2}`);
      }
      // Outside a section header: ignore prose line.
      i += 1;
      continue;
    }

    if (line.startsWith('@@')) {
      const m = /^@@ -(\d+)(?:,\d+)? \+(\d+)(?:,\d+)? @@/.exec(line);
      if (m === null || cur === null) throw new Exit2(`error: parse ${i + 1}`);
      inHeader = false;
      const oldStart = Number.parseInt(m[1]!, 10);
      i += 1;

      const rawBody: string[] = [];
      while (i < lines.length) {
        const bl = lines[i]!;
        if (bl.startsWith('diff --git ')) break;
        if (bl.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) break;
        if (bl === '' || bl.startsWith(' ') || bl.startsWith('-') || bl.startsWith('+') || bl.startsWith('\\')) {
          rawBody.push(bl);
          i += 1;
        } else {
          break;
        }
      }
      while (rawBody.length > 0 && rawBody[rawBody.length - 1] === '') rawBody.pop();

      const body: BodyItem[] = [];
      for (const bl of rawBody) {
        if (bl.startsWith('\\')) {
          if (body.length > 0) body[body.length - 1]!.noEol = true;
        } else if (bl === '') {
          body.push({ kind: ' ', text: '', noEol: false });
        } else if (bl.startsWith(' ')) {
          body.push({ kind: ' ', text: bl.slice(1), noEol: false });
        } else if (bl.startsWith('-')) {
          body.push({ kind: '-', text: bl.slice(1), noEol: false });
        } else {
          body.push({ kind: '+', text: bl.slice(1), noEol: false });
        }
      }

      cur.hunks.push({ oldStart, body });
      continue;
    }

    if (cur !== null && inHeader) {
      if (line.startsWith('rename from ')) cur.renameFrom = trimSpaces(line.slice('rename from '.length));
      else if (line.startsWith('rename to ')) cur.renameTo = trimSpaces(line.slice('rename to '.length));
      else if (line === 'new file mode' || line.startsWith('new file mode ')) cur.isNew = true;
      else if (line === 'deleted file mode' || line.startsWith('deleted file mode ')) cur.isDeleted = true;
    }

    i += 1;
  }

  return sections.map((sec) => makeUnifiedEdit(sec, strict));
}

// --- Section 7: SEARCH/REPLACE blocks ---

function searchReplaceEdits(lines: string[], strict: boolean): Edit[] {
  const edits: Edit[] = [];
  let prevEndIdx = -1;
  let prevPath: string | null = null;

  let i = 0;
  while (i < lines.length) {
    if (lines[i]!.trimEnd() !== '<<<<<<< SEARCH') {
      i += 1;
      continue;
    }
    const searchIdx = i;

    let path: string | null = null;
    for (let j = searchIdx - 1; j > prevEndIdx; j -= 1) {
      const candidate = lines[j]!;
      if (!blank(candidate) && !candidate.trim().startsWith('```')) {
        path = candidate.trim();
        break;
      }
    }
    if (path === null) {
      if (prevPath === null) throw new Exit2(`error: parse ${searchIdx + 1}`);
      path = prevPath;
    }

    let sepIdx = -1;
    for (let j = searchIdx + 1; j < lines.length; j += 1) {
      if (lines[j]!.trimEnd() === '=======') {
        sepIdx = j;
        break;
      }
    }
    if (sepIdx < 0) throw new Exit2(`error: parse ${searchIdx + 1}`);

    let endIdx = -1;
    for (let j = sepIdx + 1; j < lines.length; j += 1) {
      if (lines[j]!.trimEnd() === '>>>>>>> REPLACE') {
        endIdx = j;
        break;
      }
    }
    if (endIdx < 0) throw new Exit2(`error: parse ${searchIdx + 1}`);

    const oldLines = lines.slice(searchIdx + 1, sepIdx);
    const newLines = lines.slice(sepIdx + 1, endIdx);
    const blockPath = path;

    edits.push((tree) => {
      if (!safe(blockPath)) throw new Fail('unsafe', blockPath);
      if (oldLines.length === 0) {
        if (tree.get(blockPath) !== null) throw new Fail('exists', blockPath);
        tree.now.set(blockPath, joinFile(newLines, '\n', true));
        return;
      }
      const before = tree.get(blockPath);
      if (before === null) throw new Fail('missing', blockPath);
      const parsed = splitFile(before);
      const found = findOccurrences(parsed.lines, oldLines, strict, 0, parsed.lines.length - oldLines.length);
      if (found === null) throw new Fail('no-match', blockPath);
      if (found.positions.length > 1) throw new Fail('ambiguous', blockPath);
      const pos = found.positions[0]!;
      let replacement: string[];
      if (found.tier === 2) {
        const filePrefix = leadingSpaceTab(parsed.lines[pos]!);
        const patchPrefix = leadingSpaceTab(oldLines[0]!);
        replacement = newLines.map((l) => reindentLine(l, filePrefix, patchPrefix));
      } else {
        replacement = newLines;
      }
      parsed.lines.splice(pos, oldLines.length, ...replacement);
      tree.now.set(blockPath, joinFile(parsed.lines, parsed.br, parsed.final));
    });

    prevPath = path;
    prevEndIdx = endIdx;
    i = endIdx + 1;
  }

  return edits;
}

// --- Section 8: V4A patches ---

function v4aEdits(lines: string[], strict: boolean): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  if (lines[first]!.trim() !== '*** Begin Patch') throw new Exit2(`error: parse ${first + 1}`);

  let last = lines.length - 1;
  while (last >= 0 && blank(lines[last]!)) last -= 1;
  if (last === first || lines[last]!.trim() !== '*** End Patch') {
    throw new Exit2(`error: parse ${lines.length + 1}`);
  }

  type RawSection = {
    kind: 'add' | 'delete' | 'update';
    path: string;
    headerLine: number;
    entries: Array<{ text: string; lineNum: number }>;
  };

  const sections: RawSection[] = [];
  let cur: RawSection | null = null;

  for (let i = first + 1; i < last; i += 1) {
    const text = lines[i]!;
    const lineNum = i + 1;
    if (text.startsWith('*** Add File: ')) {
      cur = { kind: 'add', path: trimSpaces(text.slice('*** Add File: '.length)), headerLine: lineNum, entries: [] };
      sections.push(cur);
    } else if (text.startsWith('*** Delete File: ')) {
      cur = { kind: 'delete', path: trimSpaces(text.slice('*** Delete File: '.length)), headerLine: lineNum, entries: [] };
      sections.push(cur);
    } else if (text.startsWith('*** Update File: ')) {
      cur = { kind: 'update', path: trimSpaces(text.slice('*** Update File: '.length)), headerLine: lineNum, entries: [] };
      sections.push(cur);
    } else if (cur === null) {
      if (!blank(text)) throw new Exit2(`error: parse ${lineNum}`);
    } else {
      cur.entries.push({ text, lineNum });
    }
  }

  const edits: Edit[] = [];

  for (const sec of sections) {
    // Strip trailing blank lines belonging between sections or before *** End Patch.
    while (sec.entries.length > 0 && blank(sec.entries[sec.entries.length - 1]!.text)) {
      sec.entries.pop();
    }

    if (sec.kind === 'add') {
      const newLines: string[] = [];
      for (const e of sec.entries) {
        if (e.text === '') newLines.push('');
        else if (e.text.startsWith('+')) newLines.push(e.text.slice(1));
        else throw new Exit2(`error: parse ${e.lineNum}`);
      }
      const p = sec.path;
      edits.push((tree) => {
        if (!safe(p)) throw new Fail('unsafe', p);
        if (tree.get(p) !== null) throw new Fail('exists', p);
        tree.now.set(p, joinFile(newLines, '\n', true));
      });
      continue;
    }

    if (sec.kind === 'delete') {
      if (sec.entries.length > 0) throw new Exit2(`error: parse ${sec.entries[0]!.lineNum}`);
      const p = sec.path;
      edits.push((tree) => {
        if (!safe(p)) throw new Fail('unsafe', p);
        if (tree.get(p) === null) throw new Fail('missing', p);
        tree.now.set(p, null);
      });
      continue;
    }

    // Update File
    let moveTo: string | null = null;
    let idx = 0;
    if (sec.entries.length > 0 && sec.entries[0]!.text.startsWith('*** Move to: ')) {
      moveTo = trimSpaces(sec.entries[0]!.text.slice('*** Move to: '.length));
      idx = 1;
    }

    const chunks: V4aChunk[] = [];
    let curChunk: V4aChunk | null = null;
    let closedByEof = false;

    for (; idx < sec.entries.length; idx += 1) {
      const { text, lineNum } = sec.entries[idx]!;
      if (text.startsWith('@@')) {
        curChunk = { anchor: trimSpaces(text.slice(2)), body: [], eof: false };
        chunks.push(curChunk);
        closedByEof = false;
      } else if (text.trimEnd() === '*** End of File') {
        if (curChunk === null) throw new Exit2(`error: parse ${lineNum}`);
        curChunk.eof = true;
        curChunk = null;
        closedByEof = true;
      } else if (text === '' || text.startsWith(' ') || text.startsWith('-') || text.startsWith('+')) {
        if (curChunk === null) {
          if (chunks.length === 0 && !closedByEof) {
            curChunk = { anchor: '', body: [], eof: false };
            chunks.push(curChunk);
          } else {
            throw new Exit2(`error: parse ${lineNum}`);
          }
        }
        if (text === '') curChunk.body.push({ kind: ' ', text: '', noEol: false });
        else if (text.startsWith(' ')) curChunk.body.push({ kind: ' ', text: text.slice(1), noEol: false });
        else if (text.startsWith('-')) curChunk.body.push({ kind: '-', text: text.slice(1), noEol: false });
        else curChunk.body.push({ kind: '+', text: text.slice(1), noEol: false });
      } else {
        throw new Exit2(`error: parse ${lineNum}`);
      }
    }

    if (chunks.length === 0 && moveTo === null) {
      throw new Exit2(`error: parse ${sec.headerLine}`);
    }

    const oldPath = sec.path;
    const destPath = moveTo;

    edits.push((tree) => {
      if (!safe(oldPath)) throw new Fail('unsafe', oldPath);
      if (destPath !== null && !safe(destPath)) throw new Fail('unsafe', destPath);
      const before = tree.get(oldPath);
      if (before === null) throw new Fail('missing', oldPath);
      if (destPath !== null && tree.get(destPath) !== null) throw new Fail('exists', destPath);

      let resultText: string;
      if (chunks.length === 0) {
        resultText = before;
      } else {
        const parsed = splitFile(before);
        const fileLines = parsed.lines;
        let cursor = 0;

        for (const chunk of chunks) {
          if (chunk.anchor !== '') {
            const foundAnchor = findOccurrences(fileLines, [chunk.anchor], strict, cursor, fileLines.length - 1);
            if (foundAnchor === null) throw new Fail('no-match', oldPath);
            cursor = foundAnchor.positions[0]! + 1;
          }

          const oldLines: string[] = [];
          const newLines: string[] = [];
          for (const item of chunk.body) {
            if (item.kind === ' ') {
              oldLines.push(item.text);
              newLines.push(item.text);
            } else if (item.kind === '-') {
              oldLines.push(item.text);
            } else {
              newLines.push(item.text);
            }
          }

          if (oldLines.length === 0) {
            const insertPos = chunk.eof ? fileLines.length : cursor;
            fileLines.splice(insertPos, 0, ...newLines);
            cursor = insertPos + newLines.length;
          } else {
            const minPos = chunk.eof ? fileLines.length - oldLines.length : cursor;
            const maxPos = fileLines.length - oldLines.length;
            if (minPos < cursor) throw new Fail('no-match', oldPath);
            const found = findOccurrences(fileLines, oldLines, strict, minPos, maxPos);
            if (found === null) throw new Fail('no-match', oldPath);
            const pos = found.positions[0]!;
            const replacement = buildBodyReplacement(chunk.body, fileLines, pos, found.tier, oldLines[0]!);
            fileLines.splice(pos, oldLines.length, ...replacement);
            cursor = pos + replacement.length;
          }
        }

        resultText = joinFile(fileLines, parsed.br, parsed.final);
      }

      if (destPath !== null) {
        tree.now.set(oldPath, null);
        tree.now.set(destPath, resultText);
        tree.moves.push([oldPath, destPath]);
      } else {
        tree.now.set(oldPath, resultText);
      }
    });
  }

  return edits;
}

// --- Section 9: JSON edits ---

function jsonEdit(v: unknown): Edit | null {
  if (v === null || typeof v !== 'object' || Array.isArray(v)) return null;
  const o = v as Record<string, unknown>;
  const p = o.path;
  if (typeof p !== 'string') return null;

  const exists = (tree: Tree): string => {
    if (!safe(p)) throw new Fail('unsafe', p);
    const t = tree.get(p);
    if (t === null) throw new Fail('missing', p);
    return t;
  };

  if (o.command === 'create' && typeof o.file_text === 'string') {
    const text = o.file_text;
    return (tree) => {
      if (!safe(p)) throw new Fail('unsafe', p);
      if (tree.get(p) !== null) throw new Fail('exists', p);
      tree.now.set(p, text);
    };
  }

  if (o.command === 'str_replace' && typeof o.old_str === 'string' && o.old_str !== '' && (o.new_str === undefined || typeof o.new_str === 'string')) {
    const oldStr = o.old_str;
    const newStr = (o.new_str as string | undefined) ?? '';
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const crlf = nl > 0 && before[nl - 1] === '\r';
      const lf = (s: string): string => (crlf ? s.replaceAll('\r\n', '\n') : s);
      const t = lf(before);
      const old = lf(oldStr);
      let count = 0;
      for (let k = t.indexOf(old); k >= 0; k = t.indexOf(old, k + 1)) count += 1;
      if (count === 0) throw new Fail('no-match', p);
      if (count > 1) throw new Fail('ambiguous', p);
      const at = t.indexOf(old);
      const out = t.slice(0, at) + lf(newStr) + t.slice(at + old.length);
      tree.now.set(p, crlf ? out.replaceAll('\n', '\r\n') : out);
    };
  }

  if (o.command === 'insert' && typeof o.insert_line === 'number' && Number.isInteger(o.insert_line) && typeof o.new_str === 'string') {
    const line = o.insert_line;
    const add = patchLines(o.new_str);
    return (tree) => {
      const before = exists(tree);
      const parsed = splitFile(before);
      if (line < 0 || line > parsed.lines.length) throw new Fail('no-match', p);
      parsed.lines.splice(line, 0, ...add);
      tree.now.set(p, joinFile(parsed.lines, parsed.br, parsed.final));
    };
  }

  return null;
}

function jsonEdits(text: string, lines: string[]): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  const edits: Edit[] = [];
  if (lines[first]!.trimStart().startsWith('[')) {
    let v: unknown;
    try {
      v = JSON.parse(text);
    } catch {
      throw new Exit2(`error: parse ${first + 1}`);
    }
    if (!Array.isArray(v)) throw new Exit2(`error: parse ${first + 1}`);
    for (const x of v) {
      const e = jsonEdit(x);
      if (e === null) throw new Exit2(`error: parse ${first + 1}`);
      edits.push(e);
    }
    return edits;
  }
  lines.forEach((l, i) => {
    if (blank(l)) return;
    let e: Edit | null = null;
    try {
      e = jsonEdit(JSON.parse(l));
    } catch {
      e = null;
    }
    if (e === null) throw new Exit2(`error: parse ${i + 1}`);
    edits.push(e);
  });
  return edits;
}

// --- Section 1, 2, 10: CLI entry and atomic apply ---

function removeEmptyParentDirs(filePath: string): void {
  let dir = dirname(filePath);
  while (dir !== '.' && dir !== '' && dir !== '/') {
    try {
      if (readdirSync(dir).length > 0) break;
      rmdirSync(dir);
    } catch {
      break;
    }
    const parent = dirname(dir);
    if (parent === dir) break;
    dir = parent;
  }
}

function run(args: string[]): { code: number; out: string[] } {
  let format: string | null = null;
  let check = false;
  let strict = false;
  const pos: string[] = [];
  let ended = false;

  for (const a of args) {
    if (!ended && a === '--') ended = true;
    else if (!ended && a.startsWith('-') && a !== '-') {
      if (a.startsWith('--format=') && format === null && FORMATS.includes(a.slice(9))) format = a.slice(9);
      else if (a === '--check' && !check) check = true;
      else if (a === '--strict' && !strict) strict = true;
      else return { code: 2, out: ['error: usage'] };
    } else {
      pos.push(a);
    }
  }
  if (pos.length > 1) return { code: 2, out: ['error: usage'] };

  const file = pos.length === 0 || pos[0] === '-' ? null : pos[0]!;
  let text = '';
  try {
    text = readFileSync(file ?? 0, 'utf8');
  } catch {
    if (file !== null) return { code: 2, out: ['error: no-patch'] };
  }

  const lines = patchLines(text);
  const kind = format === null || format === 'auto' ? detect(lines) : format;
  if (kind === null) return { code: 2, out: ['error: format'] };

  let edits: Edit[];
  try {
    if (kind === 'unified') edits = unifiedEdits(lines, strict);
    else if (kind === 'search-replace') edits = searchReplaceEdits(lines, strict);
    else if (kind === 'v4a') edits = v4aEdits(lines, strict);
    else edits = jsonEdits(text, lines);
    if (edits.length === 0) throw new Exit2('error: parse 1');
  } catch (e) {
    if (e instanceof Exit2) return { code: 2, out: [e.line] };
    throw e;
  }

  const tree = new Tree();
  const fails: Fail[] = [];
  for (const edit of edits) {
    const beforeNow = new Map(tree.now);
    const beforeMovesLen = tree.moves.length;
    try {
      edit(tree);
    } catch (e) {
      if (!(e instanceof Fail)) throw e;
      tree.now.clear();
      for (const [k, v] of beforeNow) tree.now.set(k, v);
      tree.moves.length = beforeMovesLen;
      fails.push(e);
    }
  }

  if (fails.length > 0) {
    return {
      code: 1,
      out: [...fails.map((f) => `error: ${f.code} ${f.path}`), `failed: ${fails.length} of ${edits.length} edits`],
    };
  }

  // Pair up qualifying moves into R <old> -> <new> lines.
  const rows: Array<{ key: string; line: string }> = [];
  const consumedDeleted = new Set<string>();
  const consumedAdded = new Set<string>();

  for (const [oldPath, newPath] of tree.moves) {
    if (consumedDeleted.has(oldPath) || consumedAdded.has(newPath)) continue;
    const oldWas = tree.original(oldPath);
    const oldNow = tree.get(oldPath);
    const newWas = tree.original(newPath);
    const newNow = tree.get(newPath);
    if (oldWas !== null && oldNow === null && newWas === null && newNow !== null) {
      consumedDeleted.add(oldPath);
      consumedAdded.add(newPath);
      rows.push({ key: newPath, line: `R ${oldPath} -> ${newPath}` });
    }
  }

  for (const p of tree.now.keys()) {
    const was = tree.original(p);
    const now = tree.now.get(p)!;
    if (was === now) continue;
    if (was !== null && now === null) {
      if (!consumedDeleted.has(p)) rows.push({ key: p, line: `D ${p}` });
    } else if (was === null && now !== null) {
      if (!consumedAdded.has(p)) rows.push({ key: p, line: `A ${p}` });
    } else {
      rows.push({ key: p, line: `M ${p}` });
    }
  }

  rows.sort((a, b) => Buffer.compare(Buffer.from(a.key), Buffer.from(b.key)));

  if (!check) {
    const changedPaths = [...tree.now.keys()].sort((a, b) => Buffer.compare(Buffer.from(a), Buffer.from(b)));
    for (const p of changedPaths) {
      const was = tree.original(p);
      const now = tree.now.get(p)!;
      if (was !== null && now === null) {
        rmSync(p, { force: true });
        removeEmptyParentDirs(p);
      }
    }
    for (const p of changedPaths) {
      const was = tree.original(p);
      const now = tree.now.get(p)!;
      if (now !== null && now !== was) {
        mkdirSync(dirname(p), { recursive: true });
        writeFileSync(p, now);
      }
    }
  }

  return {
    code: 0,
    out: [...rows.map((r) => r.line), `ok: ${rows.length} ${rows.length === 1 ? 'file' : 'files'}`],
  };
}

const trialEnv = process.env.MAKEFUN_ENV_URL;
if (trialEnv !== undefined && trialEnv !== '') {
  // A trial: the kit's runner reads the checks from the env and runs this file on each one, without this variable.
  const { runTrial } = await import('./runner.ts');
  await runTrial(trialEnv);
} else {
  const r = run(process.argv.slice(2));
  writeSync(1, r.out.map((l) => `${l}\n`).join(''));
  process.exitCode = r.code;
}
