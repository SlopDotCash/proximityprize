/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.InteriorWorstCaseIncompleteSum
import Mathlib.Tactic

/-!
# BGK sup-bound ⟹ the full even-moment tower (every depth r) — #466

The named open BGK Prop `WorstCaseIncompleteSumBound ψ G M` (= `∀ b ≠ 0, ‖η_b‖² ≤ M`) was so far
consumed in-tree only at depth 2 (`addEnergy_le_of_worstCase`: the additive-energy lane). The
prize-facing depth ladder (G86/G111/G112) runs at depth 5 and, per the §8 independence form,
ultimately at depth `r ≈ log p`. This file closes the gap between the single named Prop and
*all* depths at once:

* `eta_zero` / `offZero_secondMoment` — the exact off-zero Parseval base case
  `∑_{b≠0} ‖η_b‖² = q·|G| − |G|²` (unconditional, no Weil input).
* `etaMomentTower_of_worstCase` — **the tower**: for every `r ≥ 1`,
  `∑_{b≠0} ‖η_b‖^(2r) ≤ M^(r−1) · (q·|G| − |G|²)`.
  One Hölder-free chaining step: `x^r ≤ M^(r−1)·x` for `0 ≤ x ≤ M`, then the exact base case.
* `etaMomentTower_of_worstCase_relaxed` — the subtraction-free envelope `≤ M^(r−1)·q·|G|`.
* `etaTenthMoment_of_worstCase` — the depth-five specialization `r = 5`
  (`∑_{b≠0} ‖η_b‖^10 ≤ M⁴·q·|G|`), the moment-side quantity behind the G112 collision socket.

Consequence for the campaign map: the BGK sup-bound is not merely "necessary context" for the
energy lane — it unconditionally dominates the entire even-moment tower at every finite depth,
so every depth-r rung (including the deployed depth-five envelope) is exactly ONE named
inequality away. The open content stays 100% inside `WorstCaseIncompleteSumBound`; nothing here
discharges it. Issue #466.
-/

set_option autoImplicit false

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.InteriorWorstCaseIncompleteSum

namespace ArkLib.ProximityGap.Frontier.BGKSupBoundMomentTower

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The zero-frequency subgroup Gauss sum is exactly `|G|`. -/
theorem eta_zero (ψ : AddChar F ℂ) (G : Finset F) : eta ψ G 0 = (G.card : ℂ) := by
  unfold eta
  simp

/-- **Exact off-zero Parseval**: `∑_{b≠0} ‖η_b‖² = q·|G| − |G|²`. Unconditional (pure
orthogonality); splits the in-tree second moment `∑_b ‖η_b‖² = q·|G|` at the zero frequency,
where `‖η_0‖² = |G|²`. -/
theorem offZero_secondMoment {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) :
    ∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ 2
      = (Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2 := by
  have hsplit : ∑ b : F, ‖eta ψ G b‖ ^ 2
      = ‖eta ψ G 0‖ ^ 2 + ∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ 2 :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ 0)).symm
  have h0 : ‖eta ψ G 0‖ ^ 2 = (G.card : ℝ) ^ 2 := by
    rw [eta_zero]
    simp [Complex.norm_natCast]
  have htot := subgroup_gaussSum_secondMoment hψ G
  rw [hsplit, h0] at htot
  linarith

/-- Pointwise chaining step: `0 ≤ x ≤ M` gives `x^r ≤ M^(r−1) · x` for `r ≥ 1`. -/
theorem pow_le_pow_pred_mul {x M : ℝ} (hx0 : 0 ≤ x) (hxM : x ≤ M) {r : ℕ} (hr : 1 ≤ r) :
    x ^ r ≤ M ^ (r - 1) * x := by
  calc x ^ r = x ^ (r - 1) * x := by
        conv_lhs => rw [show r = (r - 1) + 1 from (Nat.succ_pred_eq_of_pos hr).symm]
        rw [pow_succ]
    _ ≤ M ^ (r - 1) * x :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx0 hxM _) hx0

/-- **The BGK moment tower.** The single named sup-bound `WorstCaseIncompleteSumBound ψ G M`
dominates the even moment of EVERY depth `r ≥ 1`, with the exact Parseval mass on the right:

  `∑_{b≠0} ‖η_b‖^(2r) ≤ M^(r−1) · (q·|G| − |G|²)`.

At `r = 2` this recovers the in-tree additive-energy lane; at `r = 5` it is the depth-five
prize rung; at `r ≈ log p` it is the §8 independence form. The open content is entirely the
hypothesis. -/
theorem etaMomentTower_of_worstCase {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {M : ℝ} (hM0 : 0 ≤ M) (hwc : WorstCaseIncompleteSumBound ψ G M)
    {r : ℕ} (hr : 1 ≤ r) :
    ∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ (2 * r)
      ≤ M ^ (r - 1) * ((Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2) := by
  have hterm : ∀ b ∈ Finset.univ.erase (0 : F),
      ‖eta ψ G b‖ ^ (2 * r) ≤ M ^ (r - 1) * ‖eta ψ G b‖ ^ 2 := by
    intro b hb
    have hb0 : b ≠ 0 := Finset.ne_of_mem_erase hb
    have hxM : ‖eta ψ G b‖ ^ 2 ≤ M := hwc b hb0
    have hx0 : (0 : ℝ) ≤ ‖eta ψ G b‖ ^ 2 := sq_nonneg _
    calc ‖eta ψ G b‖ ^ (2 * r) = (‖eta ψ G b‖ ^ 2) ^ r := by
          rw [← pow_mul, Nat.mul_comm]
      _ ≤ M ^ (r - 1) * ‖eta ψ G b‖ ^ 2 := pow_le_pow_pred_mul hx0 hxM hr
  calc ∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ (2 * r)
      ≤ ∑ b ∈ Finset.univ.erase (0 : F), M ^ (r - 1) * ‖eta ψ G b‖ ^ 2 :=
        Finset.sum_le_sum hterm
    _ = M ^ (r - 1) * ∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ 2 := by
        rw [Finset.mul_sum]
    _ = M ^ (r - 1) * ((Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2) := by
        rw [offZero_secondMoment hψ G]

/-- Subtraction-free envelope form of the tower: `∑_{b≠0} ‖η_b‖^(2r) ≤ M^(r−1)·q·|G|`. -/
theorem etaMomentTower_of_worstCase_relaxed {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) {M : ℝ} (hM0 : 0 ≤ M) (hwc : WorstCaseIncompleteSumBound ψ G M)
    {r : ℕ} (hr : 1 ≤ r) :
    ∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ (2 * r)
      ≤ M ^ (r - 1) * ((Fintype.card F : ℝ) * G.card) := by
  have h := etaMomentTower_of_worstCase hψ G hM0 hwc hr
  have hMr : (0 : ℝ) ≤ M ^ (r - 1) := pow_nonneg hM0 _
  nlinarith [sq_nonneg ((G.card : ℝ))]

/-- **Depth-five specialization** (the G112 moment side): the BGK sup-bound alone gives
`∑_{b≠0} ‖η_b‖^10 ≤ M⁴ · q · |G|`. -/
theorem etaTenthMoment_of_worstCase {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {M : ℝ} (hM0 : 0 ≤ M) (hwc : WorstCaseIncompleteSumBound ψ G M) :
    ∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ 10
      ≤ M ^ 4 * ((Fintype.card F : ℝ) * G.card) := by
  simpa using etaMomentTower_of_worstCase_relaxed hψ G hM0 hwc (r := 5) (by norm_num)

end ArkLib.ProximityGap.Frontier.BGKSupBoundMomentTower

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ArkLib.ProximityGap.Frontier.BGKSupBoundMomentTower.offZero_secondMoment
#print axioms ArkLib.ProximityGap.Frontier.BGKSupBoundMomentTower.etaMomentTower_of_worstCase
#print axioms
  ArkLib.ProximityGap.Frontier.BGKSupBoundMomentTower.etaMomentTower_of_worstCase_relaxed
#print axioms ArkLib.ProximityGap.Frontier.BGKSupBoundMomentTower.etaTenthMoment_of_worstCase
