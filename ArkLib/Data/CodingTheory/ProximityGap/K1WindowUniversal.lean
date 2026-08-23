/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.OwnershipMultiplicity
import ArkLib.Data.CodingTheory.ProximityGap.SparseDirectionWindow
import ArkLib.Data.CodingTheory.ProximityGap.MCAEquivariance

/-!
# The universal k = 1 below-UDR law (#371): no class hypotheses

The k = 1 window closure, assembled: for **every** stack and every radius
`δ ≤ w/n`,

  **`#bad · (n − 2w) ≤ n²`**.

The classes dissolve into a trivial dichotomy on the direction's maximum value-
multiplicity `μ` (= maximum constant-codeword agreement at `k = 1`):

* `μ < n − w`: the multiplicity theorem applies with denominator
  `(n−w)(n−w−μ) ≥ n−w ≥ n−2w`;
* `μ ≥ n − w`: the direction is within `w` of a constant; translation equivariance
  (in-tree) reduces to a sparse direction with support `≤ w`, and the sparse bound
  gives `(n−w−e) ≥ n−2w`.

No WB-solvability, no rationality, no class analysis: the below-UDR `k = 1` MCA
problem is **completely solved unconditionally** — mass `≤ n²/((n−2w)q)`,
production-silent at every radius below the unique-decoding slack.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- **THE UNIVERSAL k = 1 BELOW-UDR LAW**: every stack, every radius `δ ≤ w/n`,
`#bad · (n − 2w) ≤ n²`. -/
theorem k1_badScalars_card_mul_le_universal (dom : Fin n ↪ F)
    {w : ℕ} (hw : w ≤ n) {δ : ℝ≥0} (hδn : δ * (Fintype.card (Fin n) : ℝ≥0) ≤ w)
    (u₀ u₁ : Fin n → F) :
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom 1 : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)).card
      * (n - 2 * w) ≤ n * n := by
  -- the dichotomy on the maximum value-multiplicity of the direction
  by_cases hcase : ∀ v : F, (Finset.univ.filter (fun i => u₁ i = v)).card ≤ n - w - 1
  · -- multiplicity regime
    have hmult := badScalars_card_mul_le_of_multiplicity dom hw hδn
      (u₀ := u₀) (u₁ := u₁) hcase
    have hcardfun : Fintype.card (Fin 2 → Fin n) = n * n := by
      rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, sq]
    rw [hcardfun] at hmult
    refine le_trans (Nat.mul_le_mul_left _ ?_) hmult
    -- n − 2w ≤ (n−w)·(n−w−(n−w−1)) = (n−w)·1... careful with truncation
    have h1 : n - w - (n - w - 1) = min 1 (n - w) := by omega
    rcases Nat.eq_zero_or_pos (n - w) with hz | hpos
    · -- n ≤ w: n − 2w = 0, trivial
      have : n - 2 * w = 0 := by omega
      rw [this]
      exact Nat.zero_le _
    · calc n - 2 * w ≤ (n - w) * 1 := by omega
        _ ≤ (n - w) * (n - w - (n - w - 1)) := by
            refine Nat.mul_le_mul_left _ ?_
            omega
  · -- near-constant regime: translate and use the sparse bound
    push Not at hcase
    obtain ⟨a, ha⟩ := hcase
    have haN : n - w ≤ (Finset.univ.filter (fun i => u₁ i = a)).card := by omega
    set ε : Fin n → F := u₁ - (fun _ => a) with hε
    -- support of ε is the complement of the a-fiber
    have hsupp : (Finset.univ.filter (fun i => ε i ≠ 0)).card ≤ w := by
      have hcompl : Finset.univ.filter (fun i => ε i ≠ 0)
          = Finset.univ.filter (fun i => ¬ u₁ i = a) := by
        refine Finset.filter_congr fun i _ => ?_
        rw [hε]
        simp [sub_eq_zero]
      rw [hcompl]
      have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
        (s := (Finset.univ : Finset (Fin n))) (p := fun i => u₁ i = a)
      have huniv : (Finset.univ : Finset (Fin n)).card = n := by
        rw [Finset.card_univ, Fintype.card_fin]
      omega
    -- translation: the bad sets agree
    have htrans : ∀ γ : F, mcaEvent (F := F)
        ((rsCode dom 1 : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ ↔
        mcaEvent (F := F)
        ((rsCode dom 1 : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ ε γ := by
      intro γ
      have h := ProximityGap.MCAEquivariance.mcaEvent_translate
        (rsCode dom 1 : Submodule F (Fin n → F)) (δ := δ)
        (u₀ := u₀) (u₁ := ε)
        (c₀ := 0) (c₁ := (fun _ => a))
        ((rsCode dom 1 : Submodule F (Fin n → F)).zero_mem)
        (const_mem_rsCode_one dom a) γ
      have he0 : u₀ + 0 = u₀ := by funext i; simp
      have he1 : ε + (fun _ => a) = u₁ := by
        funext i
        rw [hε]
        simp
      rw [he0, he1] at h
      exact h
    have hfilter : (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom 1 : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ))
        = (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom 1 : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ ε γ)) := by
      refine Finset.filter_congr fun γ _ => ?_
      rw [htrans γ]
    rw [hfilter]
    have hsparse := sparse_direction_badScalars_card_le dom (w := w) (e := w) hδn
      (u₀ := u₀) (ε := ε) hsupp
    calc (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom 1 : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ ε γ)).card
          * (n - 2 * w)
        ≤ (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
          ((rsCode dom 1 : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ ε γ)).card
          * (n - w - w) := by
          refine Nat.mul_le_mul_left _ ?_
          omega
      _ ≤ n * w := hsparse
      _ ≤ n * n := Nat.mul_le_mul_left _ hw

open Classical in
/-- **The probability form**: `ε_mca(RS_1, δ) ≤ n²/((n−2w)·q)` for every
`δ ≤ w/n` — the complete unconditional below-UDR law at `k = 1`. -/
theorem k1_epsMCA_le_universal (dom : Fin n ↪ F)
    {w : ℕ} (hw : w ≤ n) (h2w : 2 * w < n) {δ : ℝ≥0}
    (hδn : δ * (Fintype.card (Fin n) : ℝ≥0) ≤ w) :
    epsMCA (F := F) (A := F)
        ((rsCode dom 1 : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
      ≤ ((n * n / (n - 2 * w) : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  rw [epsMCA]
  refine iSup_le fun u => ?_
  rw [prob_uniform_eq_card_filter_div_card]
  refine ENNReal.div_le_div_right ?_ _
  have h := k1_badScalars_card_mul_le_universal dom hw hδn (u 0) (u 1)
  have hpos : 0 < n - 2 * w := by omega
  have hdiv : (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
      ((rsCode dom 1 : Submodule F (Fin n → F)) : Set (Fin n → F)) δ (u 0) (u 1)
      γ)).card ≤ n * n / (n - 2 * w) :=
    Nat.le_div_iff_mul_le hpos |>.mpr h
  exact_mod_cast hdiv

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.k1_badScalars_card_mul_le_universal
#print axioms ProximityGap.Ownership.k1_epsMCA_le_universal
