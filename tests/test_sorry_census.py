"""Unit coverage for scripts/sorry_census.py.

Exercises the comment-masking state machine (line comments, nested block
comments, docstrings), declaration-header parsing, token classification
(hole vs doc), containing-declaration attribution, and summary
aggregation, using a synthetic ArkLib/ tree.
"""

import importlib.util
import sys
from pathlib import Path

import pytest


def load_module():
    spec = importlib.util.spec_from_file_location(
        "sorry_census", "/tmp/proximityprize/scripts/sorry_census.py"
    )
    module = importlib.util.module_from_spec(spec)
    sys.modules["sorry_census"] = module
    spec.loader.exec_module(module)
    return module


mod = load_module()


def write_lean(root: Path, rel: str, content: str) -> None:
    path = root / "ArkLib" / rel
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def test_line_comment_masked() -> None:
    text = "-- sorry here\nreal code"
    mask = mod.strip_comments_map(text)
    assert mask[3] is True  # inside `-- sorry`
    assert mask[len("-- sorry here\n")] is False  # `real code` unmasked


def test_line_comment_stops_at_newline() -> None:
    text = "-- comment\nsorry"
    mask = mod.strip_comments_map(text)
    assert mask[len("-- comment\n")] is False


def test_block_comment_nested() -> None:
    text = "/- outer /- inner -/ still outer -/ sorry"
    mask = mod.strip_comments_map(text)
    # All comment chars masked; trailing `sorry` unmasked.
    for i in range(len("/- outer /- inner -/ still outer -/")):
        assert mask[i] is True
    assert mask[-1] is False  # 'sorry' outside


def test_block_comment_unclosed_masks_rest() -> None:
    text = "/- never closed ... sorry"
    mask = mod.strip_comments_map(text)
    assert all(mask)


def test_single_line_docstring_masked() -> None:
    text = "/-- docstring with admit --/\ncode"
    mask = mod.strip_comments_map(text)
    assert mask[10] is True  # inside docstring
    assert mask[-1] is False


def test_decl_re_matches_kinds() -> None:
    cases = [
        ("theorem foo : True := by sorry", "theorem", "foo"),
        ("lemma bar (x : Nat) : x = x := rfl", "lemma", "bar"),
        ("def baz : Nat := 1", "def", "baz"),
        ("instance myInst : Inhabited Nat := ⟨0⟩", "instance", "myInst"),
        ("example named_ex : 1 = 1 := rfl", "example", "named_ex"),
        ("noncomputable def qux : Nat := 1", "def", "qux"),
        ("private theorem priv : True := by trivial", "theorem", "priv"),
    ]
    for text, kind, name in cases:
        m = mod.DECL_RE.match(text)
        assert m is not None, f"no match: {text}"
        assert m.group(1) == kind
        assert m.group(2) == name


def test_token_re_matches_sorry_and_admit() -> None:
    text = "sorry admit"
    matches = [(m.group(1), m.start()) for m in mod.TOKEN_RE.finditer(text)]
    assert matches == [("sorry", 0), ("admit", 6)]


def test_census_classifies_hole_vs_doc(tmp_path: Path) -> None:
    write_lean(
        tmp_path,
        "Test.lean",
        "import Mathlib\n\n"
        "-- doc mention of sorry\n"
        "theorem live : True := by\n"
        "  sorry\n",
    )
    rows = mod.census(tmp_path)
    assert len(rows) == 2
    doc = [r for r in rows if r["kind"] == "doc"]
    hole = [r for r in rows if r["kind"] == "hole"]
    assert len(doc) == 1
    assert doc[0]["token"] == "sorry"
    assert len(hole) == 1
    assert hole[0]["decl"] == "theorem live"
    assert hole[0]["line"] == 5


def test_census_attributes_to_nearest_preceding_decl(tmp_path: Path) -> None:
    write_lean(
        tmp_path,
        "Test.lean",
        "def one : Nat := 1\n"
        "theorem two : True := by\n"
        "  admit\n"
        "lemma three : True := by\n"
        "  sorry\n",
    )
    rows = mod.census(tmp_path)
    holes = sorted(r["decl"] for r in rows if r["kind"] == "hole")
    assert holes == ["lemma three", "theorem two"]


def test_census_file_level_for_loose_sorry(tmp_path: Path) -> None:
    write_lean(tmp_path, "Test.lean", "#check sorry\n")
    rows = mod.census(tmp_path)
    assert rows[0]["decl"] == "<file-level>"


def test_summarize_counts() -> None:
    rows = [
        {"kind": "hole", "file": "a.lean", "decl": "theorem x"},
        {"kind": "hole", "file": "a.lean", "decl": "theorem x"},
        {"kind": "hole", "file": "b.lean", "decl": "def y"},
        {"kind": "doc", "file": "c.lean", "decl": "theorem z"},
    ]
    summary = mod.summarize(rows)
    assert summary["total_tokens"] == 4
    assert summary["holes"] == 3
    assert summary["doc_mentions"] == 1
    assert summary["files_with_holes"] == 2
    assert summary["decls_with_holes"] == 2
