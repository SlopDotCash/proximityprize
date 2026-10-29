"""sorry_census must count Lean's `stop` tactic (`repeat sorry`) as a live hole."""
from pathlib import Path
import json
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import sorry_census

# Each declaration compiles on Lean v4.30.0-rc2 with only a "declaration uses
# `sorry`" warning, and `#print axioms` reports [sorryAx].
HOLES = """\
theorem stop_false : False := by
  stop
  trivial

theorem stop_inline (n : Nat) : n + 1 = n := by stop rfl

theorem stop_bullet : 1 = 2 ∧ True := by
  constructor
  · stop exact rfl
  · trivial
"""

# `stop` is also an ordinary identifier; none of these is a hole.
IDENTIFIERS = """\
def slice (start stop : Nat) (h : start ≤ stop) : Nat := stop - start
example : (fun (_ stop : Nat) => stop ≤ 3) 0 1 := by decide
variable {m start stop : Nat} {h2 : stop ≤ m}
/-- `stop` in a docstring.
stop here too -/
-- stop in a line comment
"""

BRANCH_HOLES = {
    "first": "by first | stop trivial",
    "later_first": "by first | fail | stop trivial",
    "solve": "by solve | stop trivial",
    "nested": "by first | first | stop trivial",
    "multiline": "by\n  first\n  | stop trivial",
}


class StopTactic(unittest.TestCase):
    def census(self, text: str) -> list[dict]:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "Research").mkdir()
            (root / "ArkLib").mkdir()
            (root / "Research" / "Probe.lean").write_text(text, encoding="utf-8")
            return [r for r in sorry_census.census(root) if r["kind"] == "hole"]

    def test_stop_tactic_is_a_hole(self):
        holes = self.census(HOLES)
        self.assertEqual([(r["line"], r["token"]) for r in holes],
                         [(2, "stop"), (5, "stop"), (9, "stop")])
        self.assertEqual({r["decl"] for r in holes},
                         {"theorem stop_false", "theorem stop_inline", "theorem stop_bullet"})

    def test_stop_identifier_is_not_a_hole(self):
        self.assertEqual(self.census(IDENTIFIERS), [])

    def test_stop_in_tactic_alternatives_is_a_hole(self):
        for name, proof in BRANCH_HOLES.items():
            with self.subTest(name=name):
                source = f"theorem branchProbe : False := {proof}\n"
                self.assertEqual(
                    [(r["token"], r["decl"]) for r in self.census(source)],
                    [("stop", "theorem branchProbe")])

    def test_alternative_text_and_term_operators_are_not_holes(self):
        source = (
            '-- first | stop trivial\n'
            '/- solve | stop trivial -/\n'
            'def message := "first | stop trivial"\n'
            'def rawMessage := r#"solve | stop trivial"#\n'
            'def bitwise (stop : Nat) : Nat := 1 ||| stop\n'
            'def applyStop (f : Nat → Nat) (stop : Nat) : Nat := f <| stop\n'
            'inductive Signal where | stop : Nat → Signal\n'
            'open Signal in def signalValue : Signal → Nat | stop n => n\n'
        )
        self.assertEqual(self.census(source), [])

    def test_branch_cli_rejects_a_false_provider_of_the_actual_list_residual(self):
        # Gate 2 protects the open residual feeding explainableCoreSupply_of_listBound.
        # Copy the real declaration so this exercises the downstream census interface.
        repo = Path(__file__).resolve().parents[2]
        relative = Path("ArkLib/Data/CodingTheory/ProximityGap/SubJohnsonListSupply.lean")
        provider = """
namespace ProximityGap.Ownership
variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {n : Nat} [NeZero n]
theorem subJohnsonListResidual_stop_probe (dom : Fin n ↪ F) (k m L A : Nat) :
    SubJohnsonListResidual dom k m L A := by first | stop trivial
end ProximityGap.Ownership
"""
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            target = root / relative
            target.parent.mkdir(parents=True)
            target.write_text((repo / relative).read_text(encoding="utf-8") + provider,
                              encoding="utf-8")
            report = root / "residuals.json"
            result = subprocess.run(
                [sys.executable, str(repo / "scripts/residual_census.py"),
                 "--root", str(root), "--out", str(report)],
                capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            residuals = json.loads(report.read_text(encoding="utf-8"))["residuals"]
            residual = next(r for r in residuals if r["name"] == "SubJohnsonListResidual")
            self.assertEqual(residual["status"], "discharged")
            result = subprocess.run(
                [sys.executable, str(repo / "scripts/sorry_census.py"), "--root", str(root),
                 "--fail-on-holes", "--baseline", str(root / "missing-baseline.json")],
                capture_output=True, text=True)
            self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
            self.assertIn("subJohnsonListResidual_stop_probe", result.stderr)


if __name__ == "__main__":
    unittest.main()
