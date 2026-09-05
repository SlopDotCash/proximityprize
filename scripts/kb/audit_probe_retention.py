#!/usr/bin/env python3
"""Inventory tracked research evidence and direct references without executing probes."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
from collections import defaultdict
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
EVIDENCE_ROOTS = ('scripts/probes/', '_nubs_research/', '_research_357/',
                  '_research_ll/', 'scratchpad/')


def inventory() -> dict:
    tracked = subprocess.check_output(
        ['git', 'ls-files', '-z'], cwd=REPO_ROOT
    ).decode().split('\0')
    tracked = sorted(path for path in tracked if path)
    evidence = [path for path in tracked if path.startswith(EVIDENCE_ROOTS)]
    by_name = defaultdict(list)
    for path in evidence:
        by_name[Path(path).name].append(path)
    references = defaultdict(set)
    # A filename mention is a review pointer, not proof that a claim was reproduced.
    pattern = re.compile(r'[A-Za-z0-9_.-]+')
    for source in tracked:
        if Path(source).suffix not in {'.md', '.lean', '.py', '.json', '.txt', '.yml', '.yaml', '.sh'}:
            continue
        if source.startswith('docs/kb/_generated/'):
            continue
        text = (REPO_ROOT / source).read_text(encoding='utf-8', errors='replace')
        for match in pattern.finditer(text):
            for target in by_name.get(match.group(), []):
                if source != target:
                    references[target].add(source)
    records = []
    for path in evidence:
        content = (REPO_ROOT / path).read_bytes()
        records.append({
            'path': path, 'bytes': len(content),
            'sha256': hashlib.sha256(content).hexdigest(),
            'references': sorted(references[path]),
            'disposition': 'retain',
        })
    return {
        'scope': list(EVIDENCE_ROOTS),
        'policy': 'Retain all evidence; direct filename mentions are review pointers only. '
                  'Unreferenced does not mean obsolete. This inventory does not execute or validate claims.',
        'files': len(records), 'bytes': sum(row['bytes'] for row in records),
        'files_with_direct_references': sum(bool(row['references']) for row in records),
        'records': records,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, help='Write the full JSON inventory to this local path')
    args = parser.parse_args()
    result = inventory()
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    print(json.dumps({key: value for key, value in result.items() if key != 'records'}, indent=2))


if __name__ == '__main__':
    main()
