"""Unit coverage for scripts/lint-style.py.

Exercises the style-lint checks: comment/string annotation state machines,
set_option prohibition, Windows line endings + trailing whitespace, second
line indentation for def/lemma/theorem, nonterminal simp detection, and
long-line limits.
"""

import importlib.util
import sys
from pathlib import Path

import pytest


def load_module():
    # lint-style.py has no __main__ guard — it reads sys.argv at import time.
    # Blank argv so pytest's args are not treated as file paths.
    saved_argv = sys.argv[:]
    sys.argv = ["lint-style.py"]
    try:
        spec = importlib.util.spec_from_file_location(
            "lint_style", str((Path(__file__).resolve().parents[1] / "scripts" / "lint-style.py"))
        )
        module = importlib.util.module_from_spec(spec)
        sys.modules["lint_style"] = module
        spec.loader.exec_module(module)
    finally:
        sys.argv = saved_argv
    return module


mod = load_module()


def test_annotate_comments_basic() -> None:
    lines = [(0, "theorem x : True := by\n"), (1, "  trivial\n"), (2, "-- comment\n")]
    result = list(mod.annotate_comments(lines))
    assert result[0][-1] is False
    assert result[1][-1] is False
    assert result[2][-1] is True


def test_annotate_comments_multiline() -> None:
    lines = [(0, "/- open\n"), (1, "still comment -/\n"), (2, "code\n")]
    result = list(mod.annotate_comments(lines))
    assert result[0][-1] is True
    assert result[1][-1] is True
    assert result[2][-1] is False


def test_set_option_check_forbids_pp() -> None:
    lines = [(0, "set_option pp.universes true\n")]
    errors, newlines = mod.set_option_check(lines, "Test.lean")
    assert len(errors) == 1
    assert errors[0][0] == mod.ERR_OPT
    assert len(newlines) == 0  # line suggested for removal


def test_set_option_check_allows_others() -> None:
    lines = [(0, "set_option maxHeartbeats 100000\n")]
    errors, newlines = mod.set_option_check(lines, "Test.lean")
    assert errors == []
    assert len(newlines) == 1


def test_line_endings_check_windows() -> None:
    lines = [(0, "line1\r\n")]
    errors, newlines = mod.line_endings_check(lines, "Test.lean")
    assert len(errors) == 1
    assert errors[0][0] == mod.ERR_WIN
    assert newlines[0][1] == "line1\n"


def test_line_endings_check_trailing_whitespace() -> None:
    lines = [(0, "line with space \n")]
    errors, newlines = mod.line_endings_check(lines, "Test.lean")
    assert len(errors) == 1
    assert errors[0][0] == mod.ERR_TWS
    assert newlines[0][1] == "line with space\n"


def test_four_spaces_in_second_line_ok() -> None:
    lines = [
        (0, "def foo : Nat where\n"),
        (1, "  bar := 1\n"),
        (2, "\n"),
    ]
    errors, newlines = mod.four_spaces_in_second_line(lines, "Test.lean")
    assert errors == []


def test_four_spaces_in_second_line_where_ok() -> None:
    lines = [
        (0, "def foo : Nat where\n"),
        (1, "  bar := 1\n"),  # 2 spaces for where-body
        (2, "\n"),
    ]
    errors, _ = mod.four_spaces_in_second_line(lines, "Test.lean")
    assert errors == []


def test_four_spaces_in_second_line_where_bad() -> None:
    lines = [
        (0, "def foo : Nat where\n"),
        (1, "    bar := 1\n"),  # 4 spaces wrong for where (needs 2)
        (2, "\n"),
    ]
    errors, newlines = mod.four_spaces_in_second_line(lines, "Test.lean")
    assert len(errors) == 1
    assert errors[0][0] == mod.ERR_IND
    assert newlines[1][1] == "  bar := 1\n"  # fixed to 2 spaces


def test_four_spaces_in_second_line_decl_ok() -> None:
    # theorem with where body also uses 2-space body (Lean convention).
    lines = [
        (0, "theorem foo : True where\n"),
        (1, "  proof := trivial\n"),
        (2, "\n"),
    ]
    errors, _ = mod.four_spaces_in_second_line(lines, "Test.lean")
    assert errors == []


def test_nonterminal_simp_detected() -> None:
    lines = [
        (0, "  simp\n"),
        (1, "  trivial\n"),
        (2, "\n"),
    ]
    errors, newlines = mod.nonterminal_simp_check(lines, "Test.lean")
    assert len(errors) == 1
    assert errors[0][0] == mod.ERR_NSP
    assert "simp?" in newlines[0][1]


def test_nonterminal_simp_ok_when_next_is_flexible() -> None:
    lines = [
        (0, "  simp\n"),
        (1, "  ring\n"),
        (2, "\n"),
    ]
    errors, _ = mod.nonterminal_simp_check(lines, "Test.lean")
    assert errors == []


def test_long_lines_check() -> None:
    lines = [
        (0, "short\n"),
        (1, "x" * 150 + "\n"),
        (2, "has http://example.com " + "y" * 150 + "\n"),  # URL → skipped
    ]
    errors, _ = mod.long_lines_check(lines, "Test.lean")
    assert len(errors) == 1
    assert errors[0][0] == mod.ERR_LIN
    assert errors[0][1] == 1
