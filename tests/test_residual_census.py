"""Unit coverage for scripts/residual_census.py.

Exercises the parsing and classification primitives: comment masking,
signature splitting, forall-prefix stripping, result heads, top-level
splitting, binder-group parsing, proof-assumption heuristics, extra
binder detection, namespace affinity, and top-dir derivation.
"""

import sys
import types
from pathlib import Path

import pytest

SCRIPT = str((Path(__file__).resolve().parents[1] / "scripts" / "residual_census.py"))


def load():
    import importlib.util

    spec = importlib.util.spec_from_file_location("residual_census", SCRIPT)
    m = importlib.util.module_from_spec(spec)
    sys.modules["residual_census"] = m
    spec.loader.exec_module(m)
    return m


mod = load()


def test_strip_comments() -> None:
    masked = mod.strip_comments("x -- line comment\ny")
    assert "comment" not in masked
    assert masked.endswith("\ny")
    assert mod.strip_comments("a /- block -/ b") == "a             b"
    # Nested block comment: outer still open after inner close → b is masked.
    assert mod.strip_comments("a /- nested /- -/ b") == "a                  "
    # Docstrings use block comment syntax in Lean.
    assert "def" in mod.strip_comments("/-- doc -/ def x := 1")


def test_split_signature_basic() -> None:
    binders, result = mod.split_signature("(x : Nat) : x = x")
    assert binders.strip() == "(x : Nat)"
    assert result.strip() == "x = x"


def test_split_signature_binder_colon() -> None:
    # Named argument (k := k) must not be treated as the signature colon.
    binders, result = mod.split_signature("(k := k) (x : Nat) : x = x")
    assert binders.strip() == "(k := k) (x : Nat)"
    assert result.strip() == "x = x"


def test_split_signature_no_result() -> None:
    binders, result = mod.split_signature("(x : Nat) := 1")
    assert binders.strip() == "(x : Nat)"
    assert result == ""


def test_strip_forall_prefix() -> None:
    assert mod.strip_forall_prefix("∀ x, x = x") == "x = x"
    assert mod.strip_forall_prefix("∀ x y, x = y") == "x = y"
    assert mod.strip_forall_prefix("x = x") == "x = x"


def test_result_head() -> None:
    assert mod.result_head("FooResidual") == "FooResidual"
    assert mod.result_head("∀ x, FooResidual x") == "FooResidual"
    assert mod.result_head("¬ FooResidual") == "¬"


def test_split_top_level_once() -> None:
    assert mod.split_top_level_once("x : Nat", ":") == ("x ", " Nat")
    # Parenthesized content keeps the colon at depth 1 → not split.
    assert mod.split_top_level_once("(x : Nat)", ":") is None
    assert mod.split_top_level_once("no separator", ":") is None


def test_mentions_word() -> None:
    assert mod.mentions_word("FooResidual x", "FooResidual") is True
    # A dot BEFORE is allowed (qualifying); a dot AFTER is a namespace use.
    assert mod.mentions_word("Foo.Residual", "Residual") is True
    assert mod.mentions_word("FooResidualX", "FooResidual") is False  # not whole word


def test_binder_groups() -> None:
    groups = mod.binder_groups("(x : Nat) {y : Bool}")
    assert len(groups) == 2
    assert groups[0][0] == "("
    assert groups[0][1] == "x : Nat"


def test_binder_names_and_type() -> None:
    names, typ = mod.binder_names_and_type("x : Nat")
    assert names == ["x"]
    assert typ == "Nat"
    names2, _ = mod.binder_names_and_type("x y : Nat")
    assert names2 == ["x", "y"]


def test_looks_like_proof_assumption() -> None:
    assert mod.looks_like_proof_assumption(["h"], "x = y") is True
    assert mod.looks_like_proof_assumption(["h"], "Type") is False
    assert mod.looks_like_proof_assumption(["x"], "Prop") is True  # Prop marker
    assert mod.looks_like_proof_assumption(["x"], "Nat") is False


def test_extra_explicit_binders() -> None:
    extras = mod.extra_explicit_binders("(h : x = x)", "x = x")
    assert "h" in extras
    # Instance binders are ignored.
    extras2 = mod.extra_explicit_binders("[DecidableEq α]", "α")
    assert extras2 == []


def test_lower_first() -> None:
    assert mod.lower_first("Foo") == "foo"
    assert mod.lower_first("") == ""


def test_namespace_affinity() -> None:
    assert mod._ns_affinity("Foo", "Foo") is True
    assert mod._ns_affinity("Foo", "Bar") is False
    assert mod._ns_affinity("Foo.Bar", "Foo.Bar") is True  # same fq
    assert mod._ns_affinity("Foo.Bar", "Bar.Baz") is False  # different last segments


def test_top_dir() -> None:
    assert mod.top_dir("ArkLib/Mathlib/Data/Nat.lean") == "Mathlib"
    assert mod.top_dir("Lean.lean") == "(root)"
