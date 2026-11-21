/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.TwoHeadLinearBudget
import ArkLib.Research.ProximityGap.Frontier.OptimalOverlapPacking

/-! # The two-head budget crossing on any field and domain
The two constructions meet when 2(e+1) equals the length. Only min(q,2(e+1))
distinct scalars can be occupied in a field of size q; this supply suffices
for the first over-budget step at every nontrivial inverse-integer tolerance.
-/
set_option autoImplicit false
namespace ProximityGap.UniversalTwoHeadBudget
open MCAThresholdLedger
open scoped NNReal ENNReal

/-- On the entire feasible error range, without a condition on field size,
two heads produce the indicated count on any evaluation embedding. -/
theorem mass {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I] [Field F] [Fintype F]
    [DecidableEq F] (x : I ↪ F) {k e : ℕ} (hk : 2≤k)
    (room : Fintype.card I ≤ k+2*e) (cap : k+e+1 ≤ Fintype.card I) :
    ((min (Fintype.card F) (2*(e+1)) : ℕ) : ℝ≥0∞)/(Fintype.card F) ≤
      epsMCA (F:=F) (ReedSolomon.code x k : Set (I → F)) ((e:ℝ≥0)/Fintype.card I) := by
  by_cases small : 2*(e+1)≤Fintype.card I
  · rw [min_eq_right (small.trans (Fintype.card_le_of_injective x x.injective))]
    exact TwoHeadLinearBudget.errors x small room cap
  · exact ArkLib.ProximityGap.Frontier.OptimalOverlapPacking.errors x k e hk (by omega) (by omega)

/-- A single bad grid point controls the operational cutoff over every finite
field, even when the candidate count exceeds the number of field elements. -/
theorem ceiling {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I] [Field F] [Fintype F]
    [DecidableEq F] (x : I ↪ F) {k e Q : ℕ} (hk : 2≤k) (two : 2≤Q)
    (room : Fintype.card I ≤ k+2*e) (cap : k+e+1 ≤ Fintype.card I)
    (excess : Fintype.card F/Q < 2*(e+1)) :
    mcaDeltaStar (F:=F) (ReedSolomon.code x k : Set (I → F)) (1/(Q:ℝ≥0∞)) ≤
      (e:ℝ≥0)/Fintype.card I := by
  apply mcaDeltaStar_le_of_bad
  apply lt_of_lt_of_le _ (mass x hk room cap)
  apply lt_of_not_ge
  rw [BoundarySecurityBudget.count_ratio_le_iff Fintype.card_pos (by omega : 0<Q)]
  exact Nat.not_le_of_lt (lt_min (Nat.div_lt_self Fintype.card_pos (by omega)) excess)

end ProximityGap.UniversalTwoHeadBudget
#print axioms ProximityGap.UniversalTwoHeadBudget.mass
#print axioms ProximityGap.UniversalTwoHeadBudget.ceiling
