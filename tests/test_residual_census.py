"""Unit coverage for scripts/residual_census.py.

Exercises the parsing and classification primitives: comment stripping,
signature splitting (binders vs result), forall-prefix stripping, result
head extraction, top-level splitting, whole-word mention detection,
binder grouping, binder name/type parsing, proof-assumption heuristics,
extra-explicit-binder detection, and lower_first.
"""

import importlib.util
import sys
from pathlib import Path

import pytest


def load_module():
    spec = importlib.util.spec_from_file_location(
        "residual_census", str((Path(__file__).resolve().parents[1] / "scripts" / "residual_census.py"))
    )
    module = importlib.util.module_from_spec(spec)
    sys.modules["residual_census"] = module
    spec.loader.exec_module(module)
    return module


mod = load_module()


def test_strip_comments_line_and_block() -> None:
    text = "code -- line comment\n/- block\ncomment -/\nmore"
    stripped = mod.strip_comments(text)
    assert "code" in stripped
    assert "line comment" not in stripped
    assert "block" not in stripped
    assert "more" in stripped


def test_split_signature_basic() -> None:
    binders, result = mod.split_signature("(x : Nat) : x = x")
    assert binders.strip() == "(x : Nat)"
    assert result.strip() == "x = x"


def test_split_signature_no_binders() -> None:
    binders, result = mod.split_signature(" : True")
    assert binders.strip() == ""
    assert result.strip() == "True"


def test_split_signature_with_colon_in_binders() -> None:
    binders, result = mod.split_signature("(x : Nat) (h : x = x) : Prop")
    assert result.strip() == "Prop"


def test_strip_forall_prefix() -> None:
    assert mod.strip_forall_prefix("∀ x, x = x") == "x = x"
    assert mod.strip_forall_prefix("∀ (x : Nat), ∀ y, x + y = y + x") == "x + y = y + x"
    assert mod.strip_forall_prefix("True") == "True"


def test_result_head() -> None:
    assert mod.result_head("FooResidual") == "FooResidual"
    assert mod.result_head("∀ x, FooResidual x") == "FooResidual"
    assert mod.result_head("¬ FooResidual") == "¬"  # negation symbol is a head token


def test_split_top_level_once() -> None:
    assert mod.split_top_level_once("x : Nat", ":") == ("x ", " Nat")
    assert mod.split_top_level_once("(x : Nat) : Prop", ":") == ("(x : Nat) ", " Prop")
    assert mod.split_top_level_once("no separator", ":") is None


def test_is_ident_char() -> None:
    assert mod.is_ident_char("a") is True
    assert mod.is_ident_char("_") is True
    assert mod.is_ident_char("'") is True
    assert mod.is_ident_char("-") is False


def test_mentions_word() -> None:
    assert mod.mentions_word("(h : FooResidual)", "FooResidual") is True
    assert mod.mentions_word("FooResidual.bar", "FooResidual") is False  # namespace use
    assert mod.mentions_word("other FooResidual thing", "FooResidual") is True
    assert mod.mentions_word("FooResidualExtra", "FooResidual") is False  # suffix


def test_binder_groups() -> None:
    groups = mod.binder_groups("(x : Nat) (h : Prop) [inst : Inhabited Nat]")
    assert len(groups) == 3
    assert groups[0][0] == "("
    assert groups[0][1] == "x : Nat"
    assert groups[2][0] == "["


def test_binder_names_and_type() -> None:
    parsed = mod.binder_names_and_type("x y : Nat")
    assert parsed == (["x", "y"], "Nat")
    parsed2 = mod.binder_names_and_type("h : FooResidual")
    assert parsed2 == (["h"], "FooResidual")


def test_looks_like_proof_assumption() -> None:
    assert mod.looks_like_proof_assumption(["h"], "FooResidual") is True
    assert mod.looks_like_proof_assumption(["x"], "Nat") is False
    assert mod.looks_like_proof_assumption(["h"], "Type") is False
    assert mod.looks_like_proof_assumption(["p"], "Prop") is True


def test_extra_explicit_binders() -> None:
    binders = "(h : FooResidual) (x : Nat)"
    result = "FooResidual"
    extras = mod.extra_explicit_binders(binders, result)
    assert "h" in extras
    assert "x" not in extras  # x is data, not proof-like


def test_lower_first() -> None:
    assert mod.lower_first("Foo") == "foo"
    assert mod.lower_first("foo") == "foo"
    assert mod.lower_first("") == ""
