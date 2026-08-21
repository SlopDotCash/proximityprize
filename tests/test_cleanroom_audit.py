"""Unit coverage for scripts/proximity_prize_cleanroom_audit.py.

Exercises the manifest parser (field validation), probe builder (imports +
#check/#print axioms lines), axiom-report parser, and the signature
checker (conclusion placement, residual tokens, extra forbidden tokens).
"""

import importlib.util
import sys
from pathlib import Path

import pytest


def load_module():
    spec = importlib.util.spec_from_file_location(
        "cleanroom_audit", "/tmp/proximityprize/scripts/proximity_prize_cleanroom_audit.py"
    )
    module = importlib.util.module_from_spec(spec)
    sys.modules["cleanroom_audit"] = module
    spec.loader.exec_module(module)
    return module


mod = load_module()


def test_parse_manifest_basic(tmp_path: Path) -> None:
    f = tmp_path / "manifest.txt"
    f.write_text(
        "# comment\n"
        "active Module.A theorem_x conclusion_tok\n"
        "pending Module.B lemma_y other_tok extra1 extra2\n",
        encoding="utf-8",
    )
    entries = mod.parse_manifest(f)
    assert len(entries) == 2
    assert entries[0].status == "active"
    assert entries[0].module == "Module.A"
    assert entries[0].decl == "theorem_x"
    assert entries[0].conclusion == "conclusion_tok"
    assert entries[0].line_no == 2
    assert entries[1].extra_forbidden == ("extra1", "extra2")


def test_parse_manifest_rejects_short_line(tmp_path: Path) -> None:
    f = tmp_path / "manifest.txt"
    f.write_text("active Module.A only3\n", encoding="utf-8")
    with pytest.raises(ValueError, match="at least 4 fields"):
        mod.parse_manifest(f)


def test_parse_manifest_rejects_bad_status(tmp_path: Path) -> None:
    f = tmp_path / "manifest.txt"
    f.write_text("bogus Module.A decl conclusion\n", encoding="utf-8")
    with pytest.raises(ValueError, match="status must be active or pending"):
        mod.parse_manifest(f)


def test_build_probe_imports_sorted_and_checks() -> None:
    e1 = mod.Entry("active", "Z.Mod", "z_decl", "Z", (), 1)
    e2 = mod.Entry("active", "A.Mod", "a_decl", "A", (), 2)
    probe = mod.build_probe([e1, e2])
    lines = probe.splitlines()
    assert lines[0] == "import A.Mod"
    assert lines[1] == "import Z.Mod"
    assert "#check z_decl" in lines
    assert "#print axioms z_decl" in lines
    assert "#check a_decl" in lines


def test_parse_axioms() -> None:
    output = (
        "'theorem_x' depends on axioms: [propext, sorryAx]\n"
        "'lemma_y' does not depend on any axioms\n"
    )
    reported = mod.parse_axioms(output)
    assert reported["theorem_x"] == {"propext", "sorryAx"}
    assert reported["lemma_y"] == set()


def test_check_signature_ok() -> None:
    entry = mod.Entry("active", "M", "thm", "ConclusionToken", (), 1)
    output = "thm : Hypotheses → ConclusionToken\n'thm' depends on axioms: []\n"
    assert mod.check_signature(entry, output) == []


def test_check_signature_missing() -> None:
    entry = mod.Entry("active", "M", "thm", "ConclusionToken", (), 1)
    output = "'thm' depends on axioms: []\n"
    failures = mod.check_signature(entry, output)
    assert any("no #check signature" in f for f in failures)


def test_check_signature_conclusion_not_found() -> None:
    entry = mod.Entry("active", "M", "thm", "ConclusionToken", (), 1)
    output = "thm : Hypotheses → OtherThing\n'thm' depends on axioms: []\n"
    failures = mod.check_signature(entry, output)
    assert any("conclusion token" in f for f in failures)


def test_check_signature_conclusion_in_hypotheses() -> None:
    entry = mod.Entry("active", "M", "thm", "ConclusionToken", (), 1)
    output = "thm : ConclusionToken → ConclusionToken\n'thm' depends on axioms: []\n"
    failures = mod.check_signature(entry, output)
    assert any("appears in hypotheses" in f for f in failures)


def test_check_signature_extra_forbidden_token() -> None:
    entry = mod.Entry("active", "M", "thm", "ConclusionToken", ("EvilProp",), 1)
    output = "thm : EvilProp → ConclusionToken\n'thm' depends on axioms: []\n"
    failures = mod.check_signature(entry, output)
    assert any("EvilProp" in f for f in failures)
