"""Unit coverage for scripts/kb/extract_declarations.py.

Tests the declaration-catalog parser: regex matching of canonical decl kinds,
docstring-head extraction, namespace/section stack tracking, wrapped-name
lookahead, and end-to-end parse_file on synthetic Lean sources.
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts" / "kb"))

from extract_declarations import (  # noqa: E402
    DECL_RE,
    _docstring_head,
    parse_file,
)


def test_decl_re_matches_canonical_kinds() -> None:
    for line, kind in [
        ("theorem foo : True := by trivial", "theorem"),
        ("lemma bar : 1 + 1 = 2 := rfl", "lemma"),
        ("def baz : Nat := 0", "def"),
        ("inductive Tree : Type", "inductive"),
        ("instance instFoo : Foo", "instance"),
        ("axiom ax : Prop", "axiom"),
        ("opaque secret : Nat", "opaque"),
    ]:
        m = DECL_RE.match(line)
        assert m, f"no match for {line!r}"
        assert m.group("kind") == kind
        assert m.group("name") == line.split()[1]


def test_decl_re_anonymous_instance() -> None:
    m = DECL_RE.match("instance : Foo where")
    assert m is not None
    assert m.group("kind") == "instance"
    assert m.group("name") is None


def test_decl_re_attributes_and_modifiers() -> None:
    m = DECL_RE.match('@[simp] private noncomputable def fast : Nat := 1')
    assert m is not None
    assert m.group("kind") == "def"
    assert m.group("name") == "fast"


def test_docstring_head_strips_delimiters() -> None:
    assert _docstring_head("/-- A docstring -/") == "A docstring"
    assert _docstring_head("A plain line") == "A plain line"


def test_docstring_head_collapses_lines_and_caps() -> None:
    doc = "/-- Line one\nLine two -/"
    head = _docstring_head(doc)
    assert "Line one Line two" in head
    long = "/-- " + "x " * 700 + "-/"
    assert len(_docstring_head(long)) <= 600


def test_parse_file_tracks_namespace(tmp_path: Path) -> None:
    src = tmp_path / "Test.lean"
    src.write_text(
        "namespace Outer\n"
        "namespace Inner\n"
        "/-- Useful theorem -/\n"
        "theorem thm : True := by trivial\n"
        "end Inner\n"
        "end Outer\n",
        encoding="utf-8",
    )
    decls = parse_file(src)
    assert len(decls) == 1
    d = decls[0]
    assert d["name"] == "Outer.Inner.thm"  # fully-qualified
    assert d["short_name"] == "thm"
    assert d["namespace"] == "Outer.Inner"
    assert d["kind"] == "theorem"
    assert "Useful theorem" in d["doc"]


def test_parse_file_multiple_kinds(tmp_path: Path) -> None:
    src = tmp_path / "Multi.lean"
    src.write_text(
        "def alpha : Nat := 1\n"
        "lemma beta : alpha = 1 := rfl\n"
        "inductive Tree : Type\n",
        encoding="utf-8",
    )
    decls = parse_file(src)
    assert [d["name"] for d in decls] == ["alpha", "beta", "Tree"]
    assert [d["kind"] for d in decls] == ["def", "lemma", "inductive"]


def test_parse_file_wrapped_name(tmp_path: Path) -> None:
    src = tmp_path / "Wrapped.lean"
    src.write_text(
        "theorem\n"
        "  longTheoremName : True := by trivial\n",
        encoding="utf-8",
    )
    decls = parse_file(src)
    assert len(decls) == 1
    assert decls[0]["name"] == "longTheoremName"
