#!/usr/bin/env python3
"""Reject library imports of research modules, including in the library umbrella.

What is live code is decided by the shared Lean lexer (scripts/lean_lexer.py),
the same one the forbidden-token precheck and the sorry census use: comments
and literal string text are blanked, so `/- import Research.X -/` or a string
containing that text is not an import, while a `"` inside a real comment does
not hide a later import line.
"""
from pathlib import Path
import re
import lean_lexer

# Escaped components have the same meaning. Also reject obsolete research roots.
RESEARCH_MODULE = re.compile(
    r'(?:(?:ArkLib|«ArkLib»)\.)?(?:Research|«Research»)(?:\.|$)')


# A continuation line that starts with one of these is the next command, not
# another module name. `all` is handled separately: it is the optional keyword
# in `import all`, not a module.
_NEXT_COMMAND = re.compile(
    r'(?:public|meta|import|open|namespace|end|section|theorem|lemma|def|axiom|'
    r'opaque|abbrev|noncomputable|private|protected|instance|example|inductive|'
    r'structure|class|mutual|variable|universe|prelude|module|set_option|#)\b')
_IMPORT_LINE = re.compile(
    r'[ \t]*(?:(?:public|meta)[ \t]+)*import(?:[ \t]+all(?=\s|$))?[ \t]*(.*)$')


def research_imports(text: str) -> list[tuple[int, str]]:
    if "Research" not in text:
        return []
    # Code in at least one reading of the file's string literals (all of the
    # text if the lexer gives up, which can only add findings).
    # Lean's import grammar is `public? meta? "import " all? ident`: the symbol
    # consumes the newline, so the module name may sit on the following line.
    # A same-line extra token is still reported; that is outside the grammar
    # and must not hide a research module.
    live, _exhausted = lean_lexer.live_text(text)
    lines = live.splitlines()
    found = []
    for index, line in enumerate(lines):
        match = _IMPORT_LINE.match(line)
        if not match:
            continue
        tokens = [(index + 1, module) for module in match.group(1).split()]
        if not tokens:
            tokens.extend(_import_continuation(lines, index + 1))
        found.extend((number, module) for number, module in tokens
                     if RESEARCH_MODULE.match(module))
    return found


def _import_continuation(lines: list[str], start: int) -> list[tuple[int, str]]:
    """Module tokens of an `import` whose identifier was not on that line."""
    cursor = start
    if cursor < len(lines) and lines[cursor].strip() == 'all':
        cursor += 1
    if cursor >= len(lines):
        return []
    stripped = lines[cursor].strip()
    if not stripped or _NEXT_COMMAND.match(stripped):
        return []
    tokens = stripped.split()
    if tokens and tokens[0] == 'all':
        tokens = tokens[1:]
    return [(cursor + 1, module) for module in tokens]


def production_sources(root: Path) -> list[Path]:
    """Canonical and extension sources, excluding research and acceptance clients."""
    sources = [path for path in (root / 'ArkLib').rglob('*.lean')
               if path.relative_to(root).parts[:2] not in
               {('ArkLib', 'Research'), ('ArkLib', 'Tests')}]
    umbrella = root / 'ArkLib.lean'
    return sorted(sources + ([umbrella] if umbrella.is_file() else []))


def main() -> int:
    root = Path(__file__).resolve().parents[1]
    failures = []
    for path in production_sources(root):
        failures.extend(f'{path.relative_to(root).as_posix()}:{line}: forbidden import {module}'
                        for line, module in research_imports(path.read_text(encoding="utf-8")))
    if failures:
        print('\n'.join(failures))
        return 1
    print('Research import boundary passed: production does not import ArkLib.Research.')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
