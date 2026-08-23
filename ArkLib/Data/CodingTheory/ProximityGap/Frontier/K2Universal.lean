/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.K2Multiplicity
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.K2NearAffine

/-!
# The universal k = 2 below-UDR law (scratch)

The dichotomy on the collinearity of `u₁` combines the two halves into a single
unconditional bound: for every stack and every radius `δ ≤ w/n` (with `2w+2 ≤ n`),

  `#bad · (n − 2w − 1)² ≤ n³`,

hence `ε_mca(RS₂, δ) ≤ n³/((n−2w−1)²·q)` — the k = 2 analog of the universal
k = 1 below-UDR law, production-silent at every below-UDR radius.
-/

open Finset
open scoped NNReal ENNReal

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- **The universal k = 2 below-UDR law.** Every stack, every radius `δ ≤ w/n`
with `2w+2 ≤ n`: `#bad · ((n−w−w)+1−2)² ≤ n³`. -/
theorem k2_badScalars_card_mul_le_universal (dom : Fin n ↪ F) {w : ℕ}
    (h2w : 2 ≤ n - w - w) {δ : ℝ≥0} (hδn : δ * (Fintype.card (Fin n) : ℝ≥0) ≤ w)
    (u₀ u₁ : Fin n → F) :
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom 2 : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)).card
      * ((n - w - w) + 1 - 2) ^ 2 ≤ n ^ 3 := by
  have hcard3 : Fintype.card (Fin 3 → Fin n) = n ^ 3 := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  by_cases hex : ∃ i j : Fin n, i ≠ j ∧ n - w ≤
      (Finset.univ.filter (fun c => residual dom 2 ![i, j, c] u₁ = 0)).card
  · -- near-affine regime
    obtain ⟨i, j, hijne, hcompl⟩ := hex
    have hij : dom i ≠ dom j := fun h => hijne (dom.injective h)
    have hna := badScalars_card_mul_le_of_nearAffine dom hδn h2w (u₀ := u₀) hij hcompl
    calc (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
            ((rsCode dom 2 : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)).card
          * ((n - w - w) + 1 - 2) ^ 2
        ≤ n ^ 2 * w := hna
      _ ≤ n ^ 2 * n := Nat.mul_le_mul le_rfl (by omega)
      _ = n ^ 3 := by ring
  · -- high-spread regime: ν = n − w − 1
    push Not at hex
    have hw : w ≤ n := by omega
    have hν : ∀ i j : Fin n, i ≠ j →
        (Finset.univ.filter (fun c => residual dom 2 ![i, j, c] u₁ = 0)).card ≤ n - w - 1 := by
      intro i j hne
      have := hex i j hne; omega
    have hhs := badScalars_card_mul_le_of_collinearity dom hw hδn (u₀ := u₀) hν
    rw [hcard3] at hhs
    calc (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
            ((rsCode dom 2 : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)).card
          * ((n - w - w) + 1 - 2) ^ 2
        ≤ (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
            ((rsCode dom 2 : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)).card
          * ((n - w) * ((n - w) - 1) * ((n - w) - (n - w - 1))) := by
          refine Nat.mul_le_mul le_rfl ?_
          have h1 : (n - w) - (n - w - 1) = 1 := by omega
          rw [h1, mul_one, pow_two]
          exact Nat.mul_le_mul (by omega) (by omega)
      _ ≤ n ^ 3 := hhs

open Classical in
/-- **The probability form**: `ε_mca(RS₂, δ) ≤ n³/((n−2w−1)²·q)` for every
`δ ≤ w/n` with `2w+2 ≤ n` — the universal below-UDR law at `k = 2`. -/
theorem k2_epsMCA_le_universal (dom : Fin n ↪ F) {w : ℕ} (h2w : 2 ≤ n - w - w)
    {δ : ℝ≥0} (hδn : δ * (Fintype.card (Fin n) : ℝ≥0) ≤ w) :
    epsMCA (F := F) (A := F)
        ((rsCode dom 2 : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
      ≤ ((n ^ 3 / ((n - w - w) + 1 - 2) ^ 2 : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  rw [epsMCA]
  refine iSup_le fun u => ?_
  rw [prob_uniform_eq_card_filter_div_card]
  refine ENNReal.div_le_div_right ?_ _
  have h := k2_badScalars_card_mul_le_universal dom h2w hδn (u 0) (u 1)
  have hpos : 0 < ((n - w - w) + 1 - 2) ^ 2 := by
    have : 0 < (n - w - w) + 1 - 2 := by omega
    positivity
  have hdiv : (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
      ((rsCode dom 2 : Submodule F (Fin n → F)) : Set (Fin n → F)) δ (u 0) (u 1)
      γ)).card ≤ n ^ 3 / ((n - w - w) + 1 - 2) ^ 2 :=
    Nat.le_div_iff_mul_le hpos |>.mpr h
  exact_mod_cast hdiv

end ProximityGap.Ownership

#print axioms ProximityGap.Ownership.k2_badScalars_card_mul_le_universal
#print axioms ProximityGap.Ownership.k2_epsMCA_le_universal
