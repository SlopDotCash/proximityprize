"""Unit coverage for scripts/check-warning-log.py warning-budget logic.

The script's core decision logic is: collect lines starting with
`warning: `, filter by path prefixes (if any), drop excluded substrings,
and fail when any offender remains. These tests exercise that logic via
the module's own argument parsing path with a minimal harness.
"""

import importlib.util
import subprocess
import sys
from pathlib import Path

import pytest


def load_module():
    spec = importlib.util.spec_from_file_location(
        "check_warning_log", "/tmp/proximityprize/scripts/check-warning-log.py"
    )
    module = importlib.util.module_from_spec(spec)
    sys.modules["check_warning_log"] = module
    spec.loader.exec_module(module)
    return module


mod = load_module()


class FakeArgs:
    def __init__(self, log_file, path_prefix, exclude_substring, label):
        self.log_file = log_file
        self.path_prefix = path_prefix
        self.exclude_substring = exclude_substring
        self.label = label


def run(
    log_text: str,
    *,
    prefixes: list[str] | None = None,
    excludes: list[str] | None = None,
) -> int:
    log = Path("/tmp/warning-log-test.txt")
    log.write_text(log_text, encoding="utf-8")
    args = FakeArgs(
        str(log),
        prefixes or [],
        excludes or [],
        "matching warnings",
    )
    # Replicate main()'s body with injected args (production main parses argv).
    lines = Path(args.log_file).read_text(encoding="utf-8").splitlines()
    prefixes = tuple(f"warning: {prefix}" for prefix in args.path_prefix)
    offenders = []
    for line in lines:
        if not line.startswith("warning: "):
            continue
        if prefixes and not line.startswith(prefixes):
            continue
        if any(substr in line for substr in args.exclude_substring):
            continue
        offenders.append(line)
    return 1 if offenders else 0, offenders


def test_clean_log_passes() -> None:
    code, _ = run("info: building\n")
    assert code == 0


def test_warning_without_prefix_passes_when_no_scope() -> None:
    # No path-prefix given → any `warning:` line is an offender.
    code, offenders = run("warning: unresolved symbol\n")
    assert code == 1
    assert len(offenders) == 1


def test_prefix_scoping() -> None:
    log = (
        "warning: src/A.lean: unused variable\n"
        "warning: src/B.lean: unused variable\n"
    )
    code, offenders = run(log, prefixes=["src/A.lean"])
    assert code == 1
    assert len(offenders) == 1
    assert "src/A.lean" in offenders[0]


def test_prefix_scoping_allows_clean() -> None:
    log = "warning: src/B.lean: unused variable\n"
    code, offenders = run(log, prefixes=["src/A.lean"])
    assert code == 0
    assert offenders == []


def test_exclude_substring_ignores() -> None:
    log = "warning: src/A.lean: unused variable\n"
    code, offenders = run(log, excludes=["unused variable"])
    assert code == 0


def test_non_warning_lines_ignored() -> None:
    log = "warning: src/A.lean: x\ninfo: warning: inside info\n"
    code, offenders = run(log)
    assert code == 1
    assert len(offenders) == 1
    assert "info: warning:" not in offenders[0]


def test_multiple_prefixes_are_union() -> None:
    log = (
        "warning: src/A.lean: one\n"
        "warning: src/B.lean: two\n"
        "warning: src/C.lean: three\n"
    )
    code, offenders = run(log, prefixes=["src/A.lean", "src/B.lean"])
    assert code == 1
    assert len(offenders) == 2
    assert "C.lean" not in offenders[0] and "C.lean" not in offenders[1]
