#!/usr/bin/env python3
"""Materialize reviewed ArkLib PR heads without changing the native checkout.

Only fetches from the fixed read-only upstream URL. Never pushes or merges.
The manifest binds every PR number to its reviewed commit rather than a moving ref.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parent.parent
SOURCE = "https://github.com/Verified-zkEVM/ArkLib.git"
MANIFEST = ROOT / "docs/upstream/arklib-prs-2026-10-06.json"
REFERENCE = ROOT / "external/arklib"


def git(*args: str, capture: bool = False) -> str:
    result = subprocess.run(
        ["git", "-C", str(REFERENCE), *args], check=True,
        text=True, stdout=subprocess.PIPE if capture else None,
    )
    return result.stdout.strip() if capture else ""


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=["list", "fetch", "worktree"])
    parser.add_argument("--pr", type=int, help="Select one reviewed PR (fetch defaults to all)")
    parser.add_argument("--path", type=Path, help="New, separate checkout for worktree")
    args = parser.parse_args()
    records = json.loads(MANIFEST.read_text())["pull_requests"]
    if args.pr is not None:
        records = [record for record in records if record["number"] == args.pr]
        if not records:
            parser.error("PR is not in the reviewed manifest")
    if args.action == "worktree" and (args.pr is None or args.path is None):
        parser.error("worktree requires --pr and --path")
    if args.action == "worktree":
        destination = args.path.resolve()
        if destination == ROOT or ROOT in destination.parents:
            parser.error("PR worktrees must be outside the native repository")
        if destination.exists():
            parser.error("PR worktree destination must not already exist")
    if args.action == "list":
        for record in records:
            print(f"#{record['number']} {record['head']} {record['disposition']}")
        return
    if not (REFERENCE / ".git").exists():
        parser.error("run git submodule update --init external/arklib first")
    for record in records:
        sha = record["head"]
        ref = f"refs/remotes/pr-audit/pr-{record['number']}"
        # Fetch by the immutable reviewed SHA, never by today's possibly different PR head.
        git("fetch", "--no-tags", "--depth=1", SOURCE, f"{sha}:{ref}")
        if git("rev-parse", ref, capture=True) != sha:
            raise RuntimeError(f"PR #{record['number']} did not resolve to its reviewed head")
        print(f"Fetched #{record['number']} at {sha}", flush=True)
    if args.action == "worktree":
        git("worktree", "add", "--detach", str(destination), records[0]["head"])
        print(f"Created isolated PR checkout: {destination}")
        print(f"Use {ROOT / 'scripts/lake-locked.sh'} from that directory for Lake builds.")


if __name__ == "__main__":
    main()
