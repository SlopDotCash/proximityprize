#!/usr/bin/env python3
"""Generate the research umbrella from tracked modules; preserve explicit CI exclusions."""
from pathlib import Path
import shlex
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
TARGET = 'Research/ProximityPrize/All.lean'
RESEARCH_LEAN = 'Research/ProximityPrize/*.lean'
EXCLUDED = {
    TARGET,
    'Research/ProximityPrize/PROXIMITY_PRIZE_WORKBENCH.lean',
    'Research/ProximityPrize/Scratch/TmpCheck.lean',
    'Research/ProximityPrize/Frontier/_FSMA_SecondMomentPairPartition.lean',
    'Research/ProximityPrize/Frontier/_FSMC_ForcedCoreSpread.lean',
    'Research/ProximityPrize/Frontier/_P1RateQuarterSharedFreshTripleRefuted.lean',
    'Research/ProximityPrize/Frontier/_P1RateQuarterCommonFactorConcreteLocatorAttempt.lean',
}


def git_bytes(root: Path, *args: str) -> bytes:
    return subprocess.check_output(['git', *args], cwd=root)


def untracked_research_lean(root: Path) -> list[str]:
    """Lean files `git ls-files` will not import until they are staged."""
    raw = git_bytes(
        root, 'ls-files', '--others', '--exclude-standard', '-z', '--', RESEARCH_LEAN)
    return sorted(path.decode() for path in raw.split(b'\0') if path)


def module_name(path: str) -> str:
    parts = Path(path).with_suffix('').parts
    return '.'.join(f'«{part}»' if part[0].isdigit() else part for part in parts)


def render_umbrella(root: Path) -> str:
    paths = git_bytes(root, 'ls-files', '-z', '--', RESEARCH_LEAN).split(b'\0')
    tracked = sorted({path.decode() for path in paths if path} - EXCLUDED)
    modules = [module_name(path) for path in tracked]
    return ''.join(f'import {module}\n' for module in modules)


def update(root: Path = ROOT) -> int:
    untracked = untracked_research_lean(root)
    if untracked:
        print(
            'ERROR: Untracked Lean files under Research/ProximityPrize/ are not '
            'included in All.lean generation.',
            file=sys.stderr)
        print('Stage them first, then rerun this script:', file=sys.stderr)
        for path in untracked:
            print(f'  git add {shlex.quote(path)}', file=sys.stderr)
        return 1
    text = render_umbrella(root)
    (root / TARGET).write_text(text)
    print(f'Generated {TARGET}: {text.count(chr(10))} imports')
    return 0


if __name__ == '__main__':
    raise SystemExit(update())
