"""Axiom reports for declarations whose names end in a prime must be parsed.

Lean 4 (v4.30.0-rc2, the pinned toolchain) prints `#print axioms foo'` as
`'foo'' depends on axioms: [...]`: the closing quote follows the prime.
"""
import contextlib
import io
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import axiom_audit
import proximity_prize_cleanroom_audit as cleanroom


PRIMED = "ProximityGap.flagship_bound'"
DOUBLE = "ProximityGap.flagship_bound''"
GUILLEMET = "ProximityGap.«flagship bound»"


def dep(name, axioms):
    return f"'{name}' depends on axioms: [{axioms}]\n"


def nodep(name):
    return f"'{name}' does not depend on any axioms\n"


def run_flagship_gate(decls, output):
    with tempfile.TemporaryDirectory() as folder:
        manifest = Path(folder) / "flagships.txt"
        manifest.write_text("".join(f"Research.ProximityPrize.Resolution {d}\n"
                                    for d in decls))
        result = subprocess.CompletedProcess([], 0, output, "")
        err = io.StringIO()
        with patch.object(axiom_audit, "MANIFEST", manifest), \
                patch.object(axiom_audit.subprocess, "run", return_value=result), \
                contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(err):
            return axiom_audit.main(), err.getvalue()


class PrimedAxiomReports(unittest.TestCase):
    def test_cleanroom_parses_primed_names(self):
        output = (dep(PRIMED, "propext, sorryAx") + nodep(DOUBLE)
                  + dep(GUILLEMET, "Classical.choice"))
        reported = cleanroom.parse_axioms(output)
        self.assertEqual(reported.get(PRIMED), {"propext", "sorryAx"})
        self.assertEqual(reported.get(DOUBLE), set())
        self.assertEqual(reported.get(GUILLEMET), {"Classical.choice"})

    def test_cleanroom_keeps_unprimed_neighbour_distinct(self):
        base = PRIMED[:-1]
        reported = cleanroom.parse_axioms(dep(PRIMED, "sorryAx") + nodep(base))
        self.assertEqual(reported, {PRIMED: {"sorryAx"}, base: set()})

    def test_flagship_gate_accepts_clean_primed_declaration(self):
        code, err = run_flagship_gate(
            [PRIMED, DOUBLE],
            dep(PRIMED, "propext, Classical.choice, Quot.sound") + nodep(DOUBLE))
        self.assertEqual(code, 0, err)

    def test_flagship_gate_names_forbidden_axiom_of_primed_declaration(self):
        code, err = run_flagship_gate([PRIMED], dep(PRIMED, "propext, sorryAx"))
        self.assertEqual(code, 1)
        self.assertIn(f"{PRIMED}: forbidden axioms ['sorryAx']", err)
        self.assertNotIn("no axiom report produced", err)


if __name__ == "__main__":
    unittest.main()
