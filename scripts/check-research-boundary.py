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


def research_imports(text: str) -> list[tuple[int, str]]:
    if "Research" not in text:
        return []
    # Code in at least one reading of the file's string literals (all of the
    # text if the lexer gives up, which can only add findings).
    live, _exhausted = lean_lexer.live_text(text)
    found = []
    for number, line in enumerate(live.splitlines(), 1):
        match = re.match(r'\s*(?:(?:public|meta)\s+)*import\s+(?:all\s+)?(.+)', line)
        if match:
            found.extend((number, module) for module in match[1].split()
                         if RESEARCH_MODULE.match(module))
    return found


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
