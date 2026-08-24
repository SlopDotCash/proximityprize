"""Unit coverage for scripts/forbidden_tokens.py.

The axiom-laundering precheck gate. Exercises: comment masking, allowlist
loading, name classification (allowlisted / residual-like), outer-paren
stripping, top-level result-type extraction, vacuous-True placebo
detection, bodyless opaque/constant detection, and scan-plan path
resolution.
"""

import importlib.util
import sys
from pathlib import Path

import pytest


def load_module():
    spec = importlib.util.spec_from_file_location(
        "forbidden_tokens", str((Path(__file__).resolve().parents[1] / "scripts/forbidden_tokens.py"))
    )
    module = importlib.util.module_from_spec(spec)
    sys.modules["forbidden_tokens"] = module
    spec.loader.exec_module(module)
    return module


mod = load_module()


def test_comment_mask_line_comments() -> None:
    mask = mod.comment_mask("-- sorry native_decide\nreal")
    assert mask[6] is True  # inside comment
    assert mask[len("-- sorry native_decide\n") + 1] is False  # 'real' live


def test_comment_mask_block_comments() -> None:
    mask = mod.comment_mask("/- native_decide -/ live")
    assert mask[4] is True
    assert mask[-1] is False


def test_simple_name() -> None:
    assert mod.simple_name("foo") == "foo"
    assert mod.simple_name("a.b.c") == "c"
    assert mod.simple_name("foo_residual") == "foo_residual"


def test_is_allowlisted() -> None:
    allow = {"my_axiom", "shared"}
    assert mod.is_allowlisted("my_axiom", allow) is True
    assert mod.is_allowlisted("Ns.shared", allow) is True  # final component
    assert mod.is_allowlisted("other", allow) is False


def test_is_residual_like() -> None:
    allow = {"tracked_axiom"}
    assert mod.is_residual_like("tracked_axiom", allow) is True
    assert mod.is_residual_like("foo_residual", allow) is True
    assert mod.is_residual_like("FooKeystone", allow) is True
    assert mod.is_residual_like("bar_conjecture", allow) is True
    assert mod.is_residual_like("normal_lemma", allow) is False


def test_strip_outer_parens() -> None:
    assert mod.strip_outer_parens("(True)") == "True"
    assert mod.strip_outer_parens("((True))") == "True"
    assert mod.strip_outer_parens("(True) -> False") == "(True) -> False"
    assert mod.strip_outer_parens("True") == "True"
    assert mod.strip_outer_parens("(A) (B)") == "(A) (B)"


def test_top_level_result_type() -> None:
    assert mod.top_level_result_type(" : True") == "True"
    assert mod.top_level_result_type(" (x : Nat) : x = x") == "x = x"
    assert mod.top_level_result_type(" : (True)") == "True"
    assert mod.top_level_result_type("") is None
    assert mod.top_level_result_type(" : Nat → Bool") == "Nat → Bool"


def test_load_allowlist(tmp_path: Path) -> None:
    f = tmp_path / "residual_axioms.txt"
    f.write_text("# comment\nresidual_one\nresidual_two # trailing\n\n", encoding="utf-8")
    assert mod.load_allowlist(f) == {"residual_one", "residual_two"}
    assert mod.load_allowlist(tmp_path / "missing.txt") == set()


def test_find_true_placebos_basic() -> None:
    text = "theorem foo : True := by trivial\nlemma bar : Nat := 1\n"
    mask = mod.comment_mask(text)
    hits = mod.find_true_placebos(text, mask)
    assert hits == [(1, "foo")]


def test_find_true_placebos_ignores_binders() -> None:
    text = "theorem foo (x : Nat) : True := by trivial\n"
    mask = mod.comment_mask(text)
    hits = mod.find_true_placebos(text, mask)
    assert hits == [(1, "foo")]


def test_find_true_placebos_ignores_in_proof_have() -> None:
    text = "theorem foo : True := by\n  have h : True := trivial\n  exact h\n"
    mask = mod.comment_mask(text)
    hits = mod.find_true_placebos(text, mask)
    assert hits == [(1, "foo")]


def test_find_true_placebos_ignores_comments() -> None:
    text = "theorem foo : True := by trivial\n-- theorem commented : True := by trivial\n"
    mask = mod.comment_mask(text)
    hits = mod.find_true_placebos(text, mask)
    assert hits == [(1, "foo")]


def test_find_true_placebos_no_false_positive() -> None:
    text = "theorem real : 1 = 1 := by rfl\n"
    mask = mod.comment_mask(text)
    assert mod.find_true_placebos(text, mask) == []


def test_scan_plan_default_full_scan(tmp_path: Path) -> None:
    # No args → ArkLib scan (assume cwd is repo root; this test just checks
    # the empty-args branch returns the ArkLib glob without erroring).
    files, full, errors = mod.scan_plan([])
    assert full is True
    assert errors == []
    assert all(f.suffix == ".lean" for f in files)


def test_scan_plan_explicit_file(tmp_path: Path) -> None:
    lean = tmp_path / "Test.lean"
    lean.write_text("-- x", encoding="utf-8")
    files, full, errors = mod.scan_plan([str(lean)])
    assert files == [lean]
    assert full is False
    assert errors == []


def test_scan_plan_missing_path() -> None:
    files, full, errors = mod.scan_plan(["/nonexistent/x.lean"])
    assert files == []
    assert full is False
    assert len(errors) == 1


def test_scan_plan_rejects_non_lean_file(tmp_path: Path) -> None:
    txt = tmp_path / "x.txt"
    txt.write_text("x", encoding="utf-8")
    files, full, errors = mod.scan_plan([str(txt)])
    assert files == []
    assert len(errors) == 1
    assert "expected a .lean file" in errors[0]


def test_bodyless_opaque_flagging_logic() -> None:
    # A bodyless `opaque` declaration has no `:=` before the next decl.
    live_text = "opaque foo : Nat\n\ndef bar : Nat := 1\n"
    decls = list(mod.DECL_RE.finditer(live_text))
    dm = decls[0]
    assert dm.group(1) == "opaque"
    assert dm.group(2) == "foo"
    next_start = decls[1].start()
    assert live_text.find(":=", dm.end(), next_start) == -1


def test_bodyless_opaque_with_body_not_flagged() -> None:
    live_text = "opaque foo : Nat := 1\n"
    decls = list(mod.DECL_RE.finditer(live_text))
    dm = decls[0]
    assert live_text.find(":=", dm.end()) != -1


def test_axiom_re_matches_custom_axiom() -> None:
    line = "axiom my_custom : True\n"
    m = mod.AXIOM_RE.match(line)
    assert m is not None
    assert m.group(1) == "my_custom"


def test_token_re_matches_native_decide_bv_decide() -> None:
    text = "native_decide bv_decide"
    tokens = [m.group(1) for m in mod.TOKEN_RE.finditer(text)]
    assert tokens == ["native_decide", "bv_decide"]
