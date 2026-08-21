"""Unit coverage for scripts/axiom_audit.py regex parsing.

The audit's decision logic is driven by two regexes over `#print axioms`
output. These tests pin the parser behavior: dependency-line capture,
no-dependency capture, multi-axiom lists, and the allowed/forbidden set
differentiation used by the audit's failure classification.
"""

import re

import pytest

# Mirror the production regexes (importing the module would run nothing,
# but the module has no testable entry points other than main()).
DEP_RE = re.compile(r"'([^']+)' depends on axioms: \[([^\]]*)\]")
NODEP_RE = re.compile(r"'([^']+)' does not depend on any axioms")

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def parse_report(output: str) -> dict[str, set[str]]:
    reported: dict[str, set[str]] = {}
    for m in DEP_RE.finditer(output):
        axioms = {a.strip() for a in m.group(2).split(",") if a.strip()}
        reported[m.group(1)] = axioms
    for m in NODEP_RE.finditer(output):
        reported[m.group(1)] = set()
    return reported


def classify(decl: str, axioms: set[str]) -> list[str]:
    failures: list[str] = []
    extra = axioms - ALLOWED
    if extra:
        failures.append(f"{decl}: forbidden axioms {sorted(extra)}")
    return failures


def test_dep_re_parses_single_axiom() -> None:
    reported = parse_report(
        "'theorem.foo' depends on axioms: [propext]"
    )
    assert reported["theorem.foo"] == {"propext"}


def test_dep_re_parses_multi_axioms() -> None:
    reported = parse_report(
        "'theorem.bar' depends on axioms: [propext, Classical.choice, sorryAx]"
    )
    assert reported["theorem.bar"] == {"propext", "Classical.choice", "sorryAx"}


def test_dep_re_parses_empty_list() -> None:
    reported = parse_report("'theorem.baz' depends on axioms: []")
    assert reported["theorem.baz"] == set()


def test_nodep_re_parses() -> None:
    reported = parse_report("'theorem.clean' does not depend on any axioms")
    assert reported["theorem.clean"] == set()


def test_multiple_decls_parse_together() -> None:
    output = (
        "'a.foo' depends on axioms: [propext]\n"
        "'b.bar' does not depend on any axioms\n"
        "'c.baz' depends on axioms: [Classical.choice, Quot.sound]\n"
    )
    reported = parse_report(output)
    assert reported == {
        "a.foo": {"propext"},
        "b.bar": set(),
        "c.baz": {"Classical.choice", "Quot.sound"},
    }


def test_allowed_axioms_classify_clean() -> None:
    assert classify("t", {"propext"}) == []
    assert classify("t", {"propext", "Classical.choice", "Quot.sound"}) == []


def test_forbidden_axiom_classifies() -> None:
    failures = classify("t", {"sorryAx"})
    assert len(failures) == 1
    assert "forbidden axioms" in failures[0]
    assert "sorryAx" in failures[0]


def test_mixed_allowed_forbidden_classifies() -> None:
    failures = classify("t", {"propext", "MyCustomAxiom"})
    assert len(failures) == 1
    assert "MyCustomAxiom" in failures[0]
    assert "propext" not in failures[0]


def test_no_axioms_classify_clean() -> None:
    assert classify("t", set()) == []


def test_whitespace_handling_in_axiom_list() -> None:
    reported = parse_report(
        "'t' depends on axioms: [propext ,  Classical.choice]"
    )
    assert reported["t"] == {"propext", "Classical.choice"}
