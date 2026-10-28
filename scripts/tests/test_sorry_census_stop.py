"""sorry_census must count Lean's `stop` tactic (`repeat sorry`) as a live hole."""
from pathlib import Path
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


if __name__ == "__main__":
    unittest.main()
