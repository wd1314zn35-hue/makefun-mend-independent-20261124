// mend: a deterministic patch applier for the four formats in SPEC.md.
import { mkdirSync, readFileSync, rmSync, statSync, writeFileSync, writeSync } from 'node:fs';
import { dirname } from 'node:path';

const FORMATS = ['auto', 'unified', 'search-replace', 'v4a', 'json'] as const;
type Format = (typeof FORMATS)[number];

class Exit2 {
  readonly line: string;
  constructor(line: string) { this.line = line; }
}
class Fail {
  readonly code: string;
  readonly path: string;
  constructor(code: string, path: string) { this.code = code; this.path = path; }
}

const blank = (s: string): boolean => s.trim() === '';
const trimEnd = (s: string): string => s.replace(/[ \t]+$/, '');

function patchLines(text: string): string[] {
  if (text === '') return [];
  const lines = text.split('\n');
  if (text.endsWith('\n')) lines.pop();
  return lines.map((line) => (line.endsWith('\r') ? line.slice(0, -1) : line));
}

type FileText = { lines: string[]; br: string; final: boolean };
function splitFile(text: string): FileText {
  const firstLf = text.indexOf('\n');
  const br = firstLf >= 1 && text[firstLf - 1] === '\r' ? '\r\n' : '\n';
  if (text === '') return { lines: [], br, final: false };
  const lines = text.split(br);
  const final = text.endsWith(br);
  if (final) lines.pop();
  return { lines, br, final };
}
function joinFile(file: FileText): string {
  if (file.lines.length === 0) return '';
  return file.lines.join(file.br) + (file.final ? file.br : '');
}
function createdText(lines: string[], final = true): string {
  return lines.length === 0 ? '' : lines.join('\n') + (final ? '\n' : '');
}

function safe(path: string): boolean {
  return path !== '' && !path.startsWith('/') && !path.includes('\\') &&
    path.split('/').every((part) => part !== '' && part !== '.' && part !== '..');
}

class Tree {
  private readonly originals = new Map<string, string | null>();
  readonly now = new Map<string, string | null>();
  readonly moves: Array<[string, string]> = [];

  original(path: string): string | null {
    if (!this.originals.has(path)) {
      let value: string | null = null;
      try { if (statSync(path).isFile()) value = readFileSync(path, 'utf8'); } catch { /* missing */ }
      this.originals.set(path, value);
    }
    return this.originals.get(path)!;
  }
  get(path: string): string | null { return this.now.has(path) ? this.now.get(path)! : this.original(path); }
  set(path: string, value: string | null): void { this.now.set(path, value); }
}

type Edit = (tree: Tree, strict: boolean) => void;
type Match = { tier: number; positions: number[] };

function normal(line: string, tier: number): string {
  if (tier === 0) return line;
  if (tier === 1) return line.replace(/[ \t]+$/, '');
  return line.replace(/^[ \t]+|[ \t]+$/g, '');
}
function occurrences(have: string[], want: string[], start = 0, strict = false): Match | null {
  if (want.length === 0) return { tier: 0, positions: [Math.max(0, Math.min(start, have.length))] };
  const lastTier = strict ? 0 : 2;
  for (let tier = 0; tier <= lastTier; tier += 1) {
    const positions: number[] = [];
    for (let i = Math.max(0, start); i + want.length <= have.length; i += 1) {
      let equal = true;
      for (let j = 0; j < want.length; j += 1) {
        if (normal(have[i + j]!, tier) !== normal(want[j]!, tier)) { equal = false; break; }
      }
      if (equal) positions.push(i);
    }
    if (positions.length > 0) return { tier, positions };
  }
  return null;
}
function leading(line: string): string { return line.match(/^[ \t]*/)?.[0] ?? ''; }

type LineToken = { kind: 'context' | 'old' | 'new'; text: string };
type Hunk = { at: number; newAt: number; old: LineToken[]; next: LineToken[]; noEol: boolean };

function writeReplacement(file: FileText, old: LineToken[], next: LineToken[], pos: number, tier: number, eof: boolean, noEol: boolean): void {
  const oldLines = old.map((token) => token.text);
  const contextValues: string[] = [];
  for (let i = 0; i < old.length; i += 1) if (old[i]!.kind === 'context') contextValues.push(file.lines[pos + i]!);
  let contextIndex = 0;
  const prefix = tier === 2 && oldLines.length > 0 ? leading(oldLines[0]!) : '';
  const filePrefix = tier === 2 && pos < file.lines.length ? leading(file.lines[pos]!) : '';
  const replacement: string[] = [];
  for (const token of next) {
    if (token.kind === 'context') replacement.push(contextValues[contextIndex++] ?? token.text);
    else if (tier === 2 && token.text !== '' && !/^\s*$/.test(token.text) && (prefix === '' || token.text.startsWith(prefix))) replacement.push(filePrefix + (prefix === '' ? token.text : token.text.slice(prefix.length)));
    else replacement.push(token.text);
  }
  const atEnd = old.length === 0 ? pos >= file.lines.length : pos + old.length >= file.lines.length;
  file.lines.splice(pos, old.length, ...replacement);
  if (eof && atEnd) file.final = !noEol;
}

function parseFormat(lines: string[]): Format | null {
  const first = lines.findIndex((line) => !blank(line));
  if (first < 0) return null;
  if (lines[first]!.trim() === '*** Begin Patch') return 'v4a';
  const firstChar = lines[first]!.trimStart()[0];
  if (firstChar === '[' || firstChar === '{') return 'json';
  if (lines.some((line) => trimEnd(line) === '<<<<<<< SEARCH')) return 'search-replace';
  if (lines.some((line, i) => line.startsWith('diff --git ') || (line.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')))) return 'unified';
  return null;
}

function parseDiffPath(value: string): string { return value.split('\t', 1)[0]!.trim().replace(/^[ab]\//, ''); }
function sectionStart(lines: string[], i: number): boolean {
  return lines[i]?.startsWith('diff --git ') === true || (lines[i]?.startsWith('--- ') === true && (lines[i + 1] ?? '').startsWith('+++ '));
}

function parseUnified(lines: string[]): Array<{ oldPath: string | null; newPath: string | null; oldMode: boolean; deleted: boolean; hunks: Hunk[] }> {
  const sections: Array<{ oldPath: string | null; newPath: string | null; oldMode: boolean; deleted: boolean; hunks: Hunk[] }> = [];
  let i = 0;
  while (i < lines.length) {
    if (!sectionStart(lines, i)) { i += 1; continue; }
    const sectionLine = i + 1; let diffOld: string | null = null; let diffNew: string | null = null;
    const fromDiffHeader = lines[i]!.startsWith('diff --git ');
    if (fromDiffHeader) {
      const match = /^diff --git a\/(.+) b\/(.+)$/.exec(lines[i]!);
      if (!match) throw new Exit2(`error: parse ${sectionLine}`);
      diffOld = match[1]!; diffNew = match[2]!; i += 1;
    }
    let oldPath: string | null = null; let newPath: string | null = null; let oldMode = false; let deleted = false; const hunks: Hunk[] = [];
    let headerConsumed = false;
    while (i < lines.length) {
      const newSection = lines[i]!.startsWith('diff --git ') || (headerConsumed && hunks.length > 0 && sectionStart(lines, i));
      if (newSection) break;
      const line = lines[i]!;
      if (line.startsWith('--- ')) {
        if (!(lines[i + 1] ?? '').startsWith('+++ ')) throw new Exit2(`error: parse ${i + 2}`);
        if (headerConsumed) break;
        oldPath = parseDiffPath(line.slice(4)); newPath = parseDiffPath(lines[i + 1]!.slice(4)); headerConsumed = true; i += 2; continue;
      }
      if (line.startsWith('rename from ')) { oldPath = line.slice(12).trim(); i += 1; continue; }
      if (line.startsWith('rename to ')) { newPath = line.slice(10).trim(); i += 1; continue; }
      if (line.startsWith('new file mode')) { oldMode = true; i += 1; continue; }
      if (line.startsWith('deleted file mode')) { deleted = true; i += 1; continue; }
      if (line.startsWith('@@')) {
        const match = /^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@(?:.*)$/.exec(line);
        if (!match) throw new Exit2(`error: parse ${i + 1}`);
        const at = Number(match[1]); const newAt = Number(match[3]); i += 1; const body: string[] = [];
        while (i < lines.length && !sectionStart(lines, i) && !lines[i]!.startsWith('@@')) {
          const bodyLine = lines[i]!;
          if (bodyLine !== '' && ![' ', '+', '-', '\\'].includes(bodyLine[0]!)) break;
          body.push(bodyLine); i += 1;
        }
        while (body.length > 0 && body[body.length - 1] === '') body.pop();
        const old: LineToken[] = []; const next: LineToken[] = []; let noEol = false;
        for (const value of body) {
          if (value.startsWith('\\')) { if (value.startsWith('\\ No newline at end of file')) noEol = true; continue; }
          if (value === '' || value.startsWith(' ')) { const text = value === '' ? '' : value.slice(1); old.push({ kind: 'context', text }); next.push({ kind: 'context', text }); }
          else if (value.startsWith('-')) old.push({ kind: 'old', text: value.slice(1) });
          else if (value.startsWith('+')) next.push({ kind: 'new', text: value.slice(1) });
        }
        hunks.push({ at, newAt, old, next, noEol }); continue;
      }
      i += 1;
    }
    if (oldPath === null) oldPath = diffOld; if (newPath === null) newPath = diffNew;
    if (oldPath === null && newPath === null) throw new Exit2(`error: parse ${sectionLine}`);
    sections.push({ oldPath, newPath, oldMode, deleted, hunks });
  }
  if (sections.length === 0) throw new Exit2('error: parse 1');
  return sections;
}

function unifiedEdits(lines: string[]): Edit[] {
  return parseUnified(lines).map((section) => (tree, strict) => {
    const oldPath = section.oldPath === '/dev/null' ? null : section.oldPath; const newPath = section.newPath === '/dev/null' ? null : section.newPath;
    if (oldPath !== null && !safe(oldPath)) throw new Fail('unsafe', oldPath); if (newPath !== null && !safe(newPath)) throw new Fail('unsafe', newPath);
    if (newPath === null || section.deleted) { if (oldPath === null) throw new Fail('missing', ''); if (tree.get(oldPath) === null) throw new Fail('missing', oldPath); tree.set(oldPath, null); return; }
    const create = oldPath === null || section.oldMode;
    if (create) { if (tree.get(newPath) !== null) throw new Fail('exists', newPath); const out: string[] = []; let noEol = false; for (const hunk of section.hunks) { for (const token of hunk.next) out.push(token.text); noEol = hunk.noEol; } tree.set(newPath, createdText(out, !noEol)); return; }
    if (oldPath === null || tree.get(oldPath) === null) throw new Fail('missing', oldPath ?? newPath); if (oldPath !== newPath && tree.get(newPath) !== null) throw new Fail('exists', newPath);
    const file = splitFile(tree.get(oldPath)!); let delta = 0;
    for (const hunk of section.hunks) {
      const oldLines = hunk.old.map((token) => token.text); const expected = (oldLines.length === 0 ? hunk.newAt : hunk.at) - 1 + delta; const found = occurrences(file.lines, oldLines, 0, strict); if (found === null) throw new Fail('no-match', oldPath);
      const pos = oldLines.length === 0 ? Math.max(0, Math.min(expected, file.lines.length)) : found.positions.reduce((best, candidate) => Math.abs(candidate - expected) < Math.abs(best - expected) || (Math.abs(candidate - expected) === Math.abs(best - expected) && candidate < best) ? candidate : best, found.positions[0]!);
      writeReplacement(file, hunk.old, hunk.next, pos, found.tier, pos + oldLines.length >= file.lines.length, hunk.noEol); delta += hunk.next.length - hunk.old.length;
    }
    const result = joinFile(file); if (oldPath !== newPath) { tree.set(oldPath, null); tree.set(newPath, result); tree.moves.push([oldPath, newPath]); } else tree.set(oldPath, result);
  });
}

type SearchBlock = { path: string; old: string[]; next: string[] };
function parseSearch(lines: string[]): SearchBlock[] {
  const blocks: SearchBlock[] = []; let i = 0; let previousPath: string | null = null; let previousEnd = -1;
  while (i < lines.length) {
    if (trimEnd(lines[i]!) !== '<<<<<<< SEARCH') { i += 1; continue; }
    const searchLine = i + 1; let path: string | null = null;
    for (let p = i - 1; p > previousEnd; p -= 1) { const candidate = lines[p]!.trim(); if (candidate !== '' && !candidate.startsWith('```')) { path = candidate; break; } }
    if (path === null) path = previousPath; if (path === null) throw new Exit2(`error: parse ${searchLine}`);
    let equal = -1; for (let p = i + 1; p < lines.length; p += 1) if (trimEnd(lines[p]!) === '=======') { equal = p; break; } if (equal < 0) throw new Exit2(`error: parse ${searchLine}`);
    let replace = -1; for (let p = equal + 1; p < lines.length; p += 1) if (trimEnd(lines[p]!) === '>>>>>>> REPLACE') { replace = p; break; } if (replace < 0) throw new Exit2(`error: parse ${searchLine}`);
    blocks.push({ path, old: lines.slice(i + 1, equal), next: lines.slice(equal + 1, replace) }); previousPath = path; previousEnd = replace; i = replace + 1;
  }
  if (blocks.length === 0) throw new Exit2('error: parse 1'); return blocks;
}
function searchEdits(lines: string[]): Edit[] {
  return parseSearch(lines).map((block) => (tree, strict) => {
    const path = block.path; if (!safe(path)) throw new Fail('unsafe', path);
    if (block.old.length === 0) { if (tree.get(path) !== null) throw new Fail('exists', path); tree.set(path, createdText(block.next)); return; }
    const text = tree.get(path); if (text === null) throw new Fail('missing', path); const file = splitFile(text); const found = occurrences(file.lines, block.old, 0, strict); if (found === null) throw new Fail('no-match', path); if (found.positions.length !== 1) throw new Fail('ambiguous', path);
    const prefix = found.tier === 2 && block.old.length > 0 ? leading(block.old[0]!) : '';
    const filePrefix = found.tier === 2 ? leading(file.lines[found.positions[0]!] ?? '') : '';
    const replacement = block.next.map((line) => found.tier === 2 && line !== '' && !/^\s*$/.test(line) && (prefix === '' || line.startsWith(prefix)) ? filePrefix + (prefix === '' ? line : line.slice(prefix.length)) : line);
    file.lines.splice(found.positions[0]!, block.old.length, ...replacement); tree.set(path, joinFile(file));
  });
}

type VChunk = { anchor: string | null; old: LineToken[]; next: LineToken[]; eof: boolean };
type VSection = { kind: 'add' | 'delete' | 'update'; path: string; move: string | null; chunks: VChunk[]; addLines: string[] };
function isVSection(line: string): boolean { return /^\*\*\* (?:Add File|Delete File|Update File):/.test(line); }
function parseV4a(lines: string[]): VSection[] {
  const first = lines.findIndex((line) => !blank(line)); const reverse = [...lines].reverse().findIndex((line) => !blank(line)); if (first < 0 || lines[first]!.trim() !== '*** Begin Patch') throw new Exit2(`error: parse ${first < 0 ? 1 : first + 1}`);
  const end = lines.length - 1 - reverse; if (lines[end]!.trim() !== '*** End Patch') throw new Exit2(`error: parse ${lines.length + 1}`);
  const sections: VSection[] = []; let i = first + 1;
  while (i < end) {
    if (blank(lines[i]!)) { i += 1; continue; }
    const header = lines[i]!; const add = /^\*\*\* Add File:\s*(.*)$/.exec(header); const del = /^\*\*\* Delete File:\s*(.*)$/.exec(header); const upd = /^\*\*\* Update File:\s*(.*)$/.exec(header); if (!add && !del && !upd) throw new Exit2(`error: parse ${i + 1}`);
    const section: VSection = { kind: add ? 'add' : del ? 'delete' : 'update', path: (add ?? del ?? upd)![1]!.trim(), move: null, chunks: [], addLines: [] }; i += 1;
    if (section.kind === 'add') {
      while (i < end && !isVSection(lines[i]!)) { if (lines[i] === '') { section.addLines.push(''); i += 1; continue; } if (!lines[i]!.startsWith('+')) throw new Exit2(`error: parse ${i + 1}`); section.addLines.push(lines[i]!.slice(1)); i += 1; }
    } else if (section.kind === 'delete') {
      while (i < end && !isVSection(lines[i]!)) { if (!blank(lines[i]!)) throw new Exit2(`error: parse ${i + 1}`); i += 1; }
    } else {
      if (lines[i]?.startsWith('*** Move to:')) { section.move = lines[i]!.slice(13).trim(); i += 1; }
      let current: VChunk | null = null;
      while (i < end && !isVSection(lines[i]!)) {
        const line = lines[i]!;
        if (line.startsWith('*** End of File')) { if (current === null) throw new Exit2(`error: parse ${i + 1}`); current.eof = true; section.chunks.push(current); current = null; i += 1; continue; }
        if (line.startsWith('@@')) { if (current !== null) { while (current.old.length > 0 && current.old[current.old.length - 1]!.text === '' && current.next[current.next.length - 1]!.text === '') { current.old.pop(); current.next.pop(); } section.chunks.push(current); } current = { anchor: line.slice(2).trim() || null, old: [], next: [], eof: false }; i += 1; continue; }
        if (current === null) current = { anchor: null, old: [], next: [], eof: false };
        if (line === '' || line.startsWith(' ') || line.startsWith('-') || line.startsWith('+')) { if (line === '' || line.startsWith(' ')) { const value = line === '' ? '' : line.slice(1); current.old.push({ kind: 'context', text: value }); current.next.push({ kind: 'context', text: value }); } else if (line.startsWith('-')) current.old.push({ kind: 'old', text: line.slice(1) }); else current.next.push({ kind: 'new', text: line.slice(1) }); i += 1; continue; }
        throw new Exit2(`error: parse ${i + 1}`);
      }
      if (current !== null) { while (current.old.length > 0 && current.old[current.old.length - 1]!.text === '' && current.next[current.next.length - 1]!.text === '') { current.old.pop(); current.next.pop(); } section.chunks.push(current); } if (section.chunks.length === 0 && section.move === null) throw new Exit2(`error: parse ${i === 0 ? 1 : i}`);
    }
    sections.push(section);
  }
  if (sections.length === 0) throw new Exit2('error: parse 1'); return sections;
}
function v4aEdits(lines: string[]): Edit[] {
  return parseV4a(lines).map((section) => (tree, strict) => {
    if (!safe(section.path)) throw new Fail('unsafe', section.path);
    if (section.kind === 'add') { if (tree.get(section.path) !== null) throw new Fail('exists', section.path); tree.set(section.path, createdText(section.addLines)); return; }
    if (section.kind === 'delete') { if (tree.get(section.path) === null) throw new Fail('missing', section.path); tree.set(section.path, null); return; }
    if (tree.get(section.path) === null) throw new Fail('missing', section.path); if (section.move !== null) { if (!safe(section.move)) throw new Fail('unsafe', section.move); if (tree.get(section.move) !== null) throw new Fail('exists', section.move); }
    const file = splitFile(tree.get(section.path)!); let cursor = 0;
    for (const chunk of section.chunks) {
      if (chunk.anchor !== null) { const anchor = occurrences(file.lines, [chunk.anchor], cursor, strict); if (anchor === null) throw new Fail('no-match', section.path); cursor = anchor.positions[0]! + 1; }
      const oldLines = chunk.old.map((token) => token.text); const found = occurrences(file.lines, oldLines, chunk.eof ? 0 : cursor, strict); let pos: number;
      if (oldLines.length === 0) pos = chunk.eof ? file.lines.length : cursor;
      else { if (found === null) throw new Fail('no-match', section.path); const positions = chunk.eof ? found.positions.filter((candidate) => candidate + oldLines.length === file.lines.length) : found.positions; if (positions.length === 0) throw new Fail('no-match', section.path); pos = positions[0]!; }
      writeReplacement(file, chunk.old, chunk.next, pos, found?.tier ?? 0, false, false); cursor = pos + chunk.next.length;
    }
    const result = joinFile(file); if (section.move !== null) { tree.set(section.path, null); tree.set(section.move, result); tree.moves.push([section.path, section.move]); } else tree.set(section.path, result);
  });
}

function jsonEdit(value: unknown): Edit | null {
  if (value === null || typeof value !== 'object' || Array.isArray(value)) return null; const object = value as Record<string, unknown>; const path = object.path;
  if (typeof path !== 'string' || typeof object.command !== 'string') return null;
  const exists = (tree: Tree): string => { if (!safe(path)) throw new Fail('unsafe', path); const text = tree.get(path); if (text === null) throw new Fail('missing', path); return text; };
  if (object.command === 'create' && typeof object.file_text === 'string') return (tree) => { if (!safe(path)) throw new Fail('unsafe', path); if (tree.get(path) !== null) throw new Fail('exists', path); tree.set(path, object.file_text as string); };
  if (object.command === 'str_replace' && typeof object.old_str === 'string' && object.old_str !== '' && (object.new_str === undefined || typeof object.new_str === 'string')) return (tree) => { const before = exists(tree); const crlf = splitFile(before).br === '\r\n'; const toLf = (s: string) => s.replaceAll('\r\n', '\n'); const text = toLf(before); const old = toLf(object.old_str as string); const replacement = toLf((object.new_str as string | undefined) ?? ''); let count = 0; for (let at = text.indexOf(old); at >= 0; at = text.indexOf(old, at + 1)) count += 1; if (count === 0) throw new Fail('no-match', path); if (count > 1) throw new Fail('ambiguous', path); const at = text.indexOf(old); const result = text.slice(0, at) + replacement + text.slice(at + old.length); tree.set(path, crlf ? result.replaceAll('\n', '\r\n') : result); };
  if (object.command === 'insert' && Number.isInteger(object.insert_line) && typeof object.new_str === 'string') return (tree) => { const before = exists(tree); const file = splitFile(before); const line = object.insert_line as number; if (line < 0 || line > file.lines.length) throw new Fail('no-match', path); file.lines.splice(line, 0, ...patchLines(object.new_str as string)); tree.set(path, joinFile(file)); };
  return null;
}
function jsonEdits(text: string, lines: string[]): Edit[] {
  const first = lines.findIndex((line) => !blank(line)); if (first < 0) throw new Exit2('error: parse 1'); const edits: Edit[] = [];
  if (lines[first]!.trimStart().startsWith('[')) { let parsed: unknown; try { parsed = JSON.parse(text); } catch { throw new Exit2(`error: parse ${first + 1}`); } if (!Array.isArray(parsed)) throw new Exit2(`error: parse ${first + 1}`); for (const value of parsed) { const edit = jsonEdit(value); if (edit === null) throw new Exit2(`error: parse ${first + 1}`); edits.push(edit); } return edits; }
  lines.forEach((line, i) => { if (blank(line)) return; let edit: Edit | null = null; try { edit = jsonEdit(JSON.parse(line)); } catch { edit = null; } if (edit === null) throw new Exit2(`error: parse ${i + 1}`); edits.push(edit); }); return edits;
}

function output(tree: Tree, check: boolean): string[] {
  const rename = new Map<string, string>(); for (const [oldPath, newPath] of tree.moves) if (tree.original(oldPath) !== null && tree.original(newPath) === null && tree.get(oldPath) === null && tree.get(newPath) !== null) rename.set(newPath, oldPath);
  const paths = new Set([...tree.now.keys()]); for (const [newPath, oldPath] of rename) { paths.delete(oldPath); paths.delete(newPath); }
  const rows: Array<{ sort: string; line: string; old?: string; now?: string | null }> = [];
  for (const path of paths) { const before = tree.original(path); const after = tree.get(path); if (before === after) continue; rows.push({ sort: path, line: `${before === null ? 'A' : after === null ? 'D' : 'M'} ${path}`, old: path, now: after }); }
  for (const [newPath, oldPath] of rename) rows.push({ sort: newPath, line: `R ${oldPath} -> ${newPath}` }); rows.sort((a, b) => Buffer.compare(Buffer.from(a.sort), Buffer.from(b.sort)));
  if (!check) for (const row of rows) { if (row.line.startsWith('R ')) { const match = /^R (.+) -> (.+)$/.exec(row.line)!; mkdirSync(dirname(match[2]!), { recursive: true }); writeFileSync(match[2]!, tree.get(match[2]!)!); rmSync(match[1]!, { force: true }); } else if (row.now === null) rmSync(row.old!, { force: true }); else { mkdirSync(dirname(row.old!), { recursive: true }); writeFileSync(row.old!, row.now!); } }
  return [...rows.map((row) => row.line), `ok: ${rows.length} ${rows.length === 1 ? 'file' : 'files'}`];
}

function run(args: string[]): { code: number; out: string[] } {
  let format: string | null = null; let check = false; let strict = false; const positional: string[] = []; let ended = false;
  for (const arg of args) {
    if (!ended && arg === '--') { ended = true; continue; }
    if (!ended && arg.startsWith('-') && arg !== '-') {
      if (arg.startsWith('--format=') && format === null && FORMATS.includes(arg.slice(9) as Format)) format = arg.slice(9);
      else if (arg === '--check' && !check) check = true; else if (arg === '--strict' && !strict) strict = true; else return { code: 2, out: ['error: usage'] };
    } else positional.push(arg);
  }
  if (positional.length > 1) return { code: 2, out: ['error: usage'] };
  const file = positional.length === 0 || positional[0] === '-' ? null : positional[0]!; let text = '';
  try { text = readFileSync(file ?? 0, 'utf8'); } catch { if (file !== null) return { code: 2, out: ['error: no-patch'] }; }
  const lines = patchLines(text); const kind = format === null || format === 'auto' ? parseFormat(lines) : format as Format; if (kind === null) return { code: 2, out: ['error: format'] };
  let edits: Edit[];
  try { edits = kind === 'json' ? jsonEdits(text, lines) : kind === 'unified' ? unifiedEdits(lines) : kind === 'search-replace' ? searchEdits(lines) : v4aEdits(lines); if (edits.length === 0) throw new Exit2('error: parse 1'); }
  catch (error) { if (error instanceof Exit2) return { code: 2, out: [error.line] }; throw error; }
  const tree = new Tree(); const failures: Fail[] = [];
  for (const edit of edits) { const snapshot = new Map(tree.now); const moves = tree.moves.length; try { edit(tree, strict); } catch (error) { if (!(error instanceof Fail)) throw error; tree.now.clear(); for (const [key, value] of snapshot) tree.now.set(key, value); tree.moves.splice(moves); failures.push(error); } }
  if (failures.length > 0) return { code: 1, out: [...failures.map((failure) => `error: ${failure.code} ${failure.path}`), `failed: ${failures.length} of ${edits.length} edits`] };
  return { code: 0, out: output(tree, check) };
}

const trialEnv = process.env.MAKEFUN_ENV_URL;
if (trialEnv !== undefined && trialEnv !== '') { const { runTrial } = await import('./runner.ts'); await runTrial(trialEnv); }
else { const result = run(process.argv.slice(2)); writeSync(1, result.out.map((line) => `${line}\n`).join('')); process.exitCode = result.code; }
