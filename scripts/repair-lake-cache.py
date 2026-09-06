#!/usr/bin/env python3
"""Quarantine broken Git packages from a restored CI Lake cache before Lake runs."""
import json
from pathlib import Path
import shutil
import subprocess
import tempfile


def git_output(package: Path, *args: str) -> str | None:
    result = subprocess.run(['git', '-C', str(package), *args],
                            capture_output=True, text=True)
    return result.stdout.strip() if result.returncode == 0 else None


def repair(root: Path) -> list[str]:
    manifest = json.loads((root / 'lake-manifest.json').read_text())
    packages = root / manifest.get('packagesDir', '.lake/packages')
    repaired = []
    quarantine = None
    for entry in manifest['packages']:
        if entry['type'] != 'git':
            continue
        name = entry['name'].removeprefix('«').removesuffix('»')
        if Path(name).name != name or name in ('.', '..'):
            raise ValueError(f'Invalid package name: {name}')
        package = packages / name
        if not package.exists():
            continue
        # Without its own .git, Git can accidentally resolve the parent checkout.
        own_git = (package / '.git').exists()
        top = git_output(package, 'rev-parse', '--show-toplevel') if own_git else None
        head = git_output(package, 'rev-parse', '--verify', 'HEAD^{commit}') if top else None
        if top and Path(top).resolve() == package.resolve() and head:
            continue
        if quarantine is None:
            quarantine = Path(tempfile.mkdtemp(prefix='lake-cache-quarantine-'))
        shutil.move(str(package), str(quarantine / name))
        print(f'Quarantined broken cached package {name}: {quarantine / name}', flush=True)
        repaired.append(name)
    print(f'Lake cache Git check: {len(repaired)} broken package(s) quarantined.', flush=True)
    return repaired


if __name__ == '__main__':
    repair(Path(__file__).resolve().parents[1])
