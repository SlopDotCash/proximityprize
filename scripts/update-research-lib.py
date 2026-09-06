#!/usr/bin/env python3
"""Generate the research umbrella from tracked modules; preserve explicit CI exclusions."""
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
TARGET = 'Research/ProximityPrize/All.lean'
EXCLUDED = {
    TARGET,
    'Research/ProximityPrize/PROXIMITY_PRIZE_WORKBENCH.lean',
    'Research/ProximityPrize/Scratch/TmpCheck.lean',
    'Research/ProximityPrize/Frontier/_FSMA_SecondMomentPairPartition.lean',
    'Research/ProximityPrize/Frontier/_FSMC_ForcedCoreSpread.lean',
    'Research/ProximityPrize/Frontier/_P1RateQuarterSharedFreshTripleRefuted.lean',
    'Research/ProximityPrize/Frontier/_P1RateQuarterCommonFactorConcreteLocatorAttempt.lean',
}
paths = subprocess.check_output(
    ['git', 'ls-files', '--', 'Research/ProximityPrize/*.lean'], cwd=ROOT, text=True).splitlines()
modules = []
for path in sorted(set(paths) - EXCLUDED):
    parts = Path(path).with_suffix('').parts
    modules.append('.'.join('«'+x+'»' if x[0].isdigit() else x for x in parts))
(ROOT / TARGET).write_text(''.join('import '+m+'\n' for m in modules))
print(f'Generated {TARGET}: {len(modules)} imports')
