import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import ArkLib.Data.CodingTheory.ProximityGap.MomentExponentThreshold

open scoped Real

namespace ProximityGap.MomentExponentThreshold

/-- **The gap at depth 2 is half the depth-1 gap for any β.**
`θ(2,β) - 1/2 = (θ(1,β) - 1/2)/2` — the first halving of the gap as
depth goes 1 → 2, valid for every aspect β. -/
theorem momentExponent_gap_halving_base {beta : ℝ} :
    momentExponent 2 beta - 1 / 2 = (momentExponent 1 beta - 1 / 2) / 2 := by
  rw [momentExponent_sub_half (by norm_num : (0 : ℝ) < 2),
      momentExponent_sub_half (by norm_num : (0 : ℝ) < 1)]
  field_simp

/-- **The gap at depth 2r is half the gap at depth r (general aspect).**
For every `β` and `0 < r`, `θ(2r,β) - 1/2 = (θ(r,β) - 1/2)/2` — the
halving law in full generality. -/
theorem momentExponent_gap_halving_general {beta r : ℝ} (hr : 0 < r) :
    momentExponent (2 * r) beta - 1 / 2 =
      (momentExponent r beta - 1 / 2) / 2 := by
  rw [momentExponent_sub_half (by positivity : (0 : ℝ) < 2 * r),
      momentExponent_sub_half hr]
  field_simp

/-- **The gap is positive for β > 1 at any depth.**
For `0 < r` and `1 < β`, `0 < θ(r,β) - 1/2` — the strict positivity of
the gap in the production regime. -/
theorem momentExponent_gap_pos {r beta : ℝ} (hr : 0 < r) (hb : 1 < beta) :
    0 < momentExponent r beta - 1 / 2 := by
  rw [momentExponent_sub_half hr]
  have hden : (0 : ℝ) < 2 * r := by positivity
  have hnum : 0 < beta - 1 := by linarith
  exact div_pos hnum hden

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms momentExponent_gap_halving_base
#print axioms momentExponent_gap_halving_general
#print axioms momentExponent_gap_pos

end ProximityGap.MomentExponentThreshold
