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

# `stop` consumes the following tactic sequence and elaborates to `repeat sorry`.
# These are the forms the `by`-only check missed. Line numbers are the `stop`
# token, not the theorem header, when the two differ.
COMBINATORS = """\
theorem brace_block : False := by { stop done }

theorem indented_brace : False := by
  { stop done }

theorem bullet_same_line : False := by · stop done

theorem dot_bullet_same_line : False := by . stop done

theorem all_goals_stop : False := by all_goals stop done

theorem any_goals_stop : False := by any_goals stop done

theorem focus_stop : False := by focus stop done

theorem try_stop : False := by try stop done

theorem repeat_brace : False := by repeat { stop done }

theorem repeat_prime_brace : False := by repeat' { stop done }

theorem repeat1_prime_brace : False := by repeat1' { stop done }

theorem with_reducible_stop : False := by with_reducible stop done

theorem with_reducible_instances_stop : False := by with_reducible_and_instances stop done

theorem with_unfolding_all_stop : False := by with_unfolding_all stop done

theorem with_unfolding_none_stop : False := by with_unfolding_none stop done

theorem classical_stop : False := by classical stop done

theorem unhygienic_stop : False := by unhygienic stop done

theorem show_term_stop : False := by show_term stop done

theorem set_option_stop : False := by set_option pp.all false in stop done

theorem open_in_stop : False := by open Classical in stop done

theorem nested_stop : False := by all_goals try focus stop done
"""

COMBINATOR_HOLES = [
    (1, "theorem brace_block"),
    (4, "theorem indented_brace"),
    (6, "theorem bullet_same_line"),
    (8, "theorem dot_bullet_same_line"),
    (10, "theorem all_goals_stop"),
    (12, "theorem any_goals_stop"),
    (14, "theorem focus_stop"),
    (16, "theorem try_stop"),
    (18, "theorem repeat_brace"),
    (20, "theorem repeat_prime_brace"),
    (22, "theorem repeat1_prime_brace"),
    (24, "theorem with_reducible_stop"),
    (26, "theorem with_reducible_instances_stop"),
    (28, "theorem with_unfolding_all_stop"),
    (30, "theorem with_unfolding_none_stop"),
    (32, "theorem classical_stop"),
    (34, "theorem unhygienic_stop"),
    (36, "theorem show_term_stop"),
    (38, "theorem set_option_stop"),
    (40, "theorem open_in_stop"),
    (42, "theorem nested_stop"),
]

# The same words in term position, comments and strings are not proof holes.
COMBINATOR_TEXT = """\
def bundle {stop : Nat} : Nat := stop
def struct := { stop := 1 }
-- all_goals stop done
def msg := "try focus stop done"
/-- classical stop done in a docstring -/
example : (fun (_ stop : Nat) => stop ≤ 3) 0 1 := by decide
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

    def test_stop_under_combinators_and_braces_is_a_hole(self):
        # Each of these compiles on Lean v4.30.0-rc2 (`#print axioms` reports
        # `[sorryAx]`). `stop` is not the first tactic, so the `by`-only
        # position check missed it.
        holes = self.census(COMBINATORS)
        self.assertEqual(
            [(r["line"], r["token"], r["decl"]) for r in holes],
            [(line, "stop", decl) for line, decl in COMBINATOR_HOLES],
        )

    def test_combinator_wording_outside_tactic_position_is_not_a_hole(self):
        self.assertEqual(self.census(COMBINATOR_TEXT), [])


if __name__ == "__main__":
    unittest.main()
