#!/usr/bin/env python3
# Copyright (c) 2026 nubs
# SPDX-License-Identifier: MIT OR Apache-2.0
# Authors: nubs (with Codex assistance)
"""Reject tracked source files outside the documented repository layout."""
from pathlib import PurePosixPath, Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
DIRECTORIES = {".codex", ".github", "ArkLib", "docs", "external", "scripts", "website"}
FILES = {".gitattributes", ".gitignore", ".gitmodules", "AGENTS.md", "CLAUDE.md",
         "AUTHORS", "ArkLib.lean", "CONTRIBUTING.md", "LICENSE", "LICENSE-MIT",
         "README.md", "lake-manifest.json", "lakefile.toml", "lean-toolchain"}


def violations(paths: list[str]) -> list[str]:
    return sorted(path for path in paths if (
        PurePosixPath(path).parts[0] not in DIRECTORIES
        if len(PurePosixPath(path).parts) > 1 else path not in FILES))


def main() -> int:
    paths = subprocess.check_output(["git", "ls-files", "-z"], cwd=ROOT).decode().split("\0")
    errors = violations([p for p in paths if p])
    if errors:
        print("Tracked files outside the repository layout:", file=sys.stderr)
        print("\n".join(errors), file=sys.stderr)
        return 1
    print("Repository layout passed: source, documentation, tools and websites have distinct roots.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
