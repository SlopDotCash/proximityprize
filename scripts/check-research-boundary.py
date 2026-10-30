#!/usr/bin/env python3
"""Reject library imports of research modules, including in the library umbrella."""
from pathlib import Path
import re
from forbidden_tokens import comment_mask


def _module_name(token: str) -> str:
    # A module component may be a «quoted» identifier; the quoting is only
    # spelling, not a different module: Lean resolves `import «Research».Foo`
    # to the module Research.Foo. Compare the unquoted name.
    return token.replace('«', '').replace('»', '')


def research_imports(text: str) -> list[tuple[int, str]]:
    if "Research" not in text:
        return []
    mask = comment_mask(text)
    live = ''.join(' ' if hidden and char != '\n' else char
                   for char, hidden in zip(text, mask))
    found = []
    for number, line in enumerate(live.splitlines(), 1):
        match = re.match(r'\s*(?:(?:public|meta)\s+)*import\s+(?:all\s+)?(.+)', line)
        if match:
            for module in match[1].split():
                name = _module_name(module)
                if name == 'Research' or name.startswith('Research.'):
                    found.append((number, module))
    return found


def main() -> int:
    root = Path(__file__).resolve().parents[1]
    failures = []
    for path in [root / 'ArkLib.lean', *sorted((root / 'ArkLib').rglob('*.lean'))]:
        failures.extend(f'{path.relative_to(root)}:{line}: forbidden import {module}'
                        for line, module in research_imports(path.read_text()))
    if failures:
        print('\n'.join(failures))
        return 1
    print('Research import boundary passed: ArkLib does not import Research.')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
