/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.Compliance
import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.Lift
import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.PreTensorFar

/-!
## Binary Basefold Soundness Fold Distance

Distance and disagreement transfer lemmas from fiber views to folded codewords.
This file packages:
1. helper lemmas turning fiber agreement into fold agreement
2. disagreement propagation from noncompliant fibers to folded evaluations
3. the folded-distance lower bounds used in the later bad-block analysis

## References

* [Diamond, B.E. and Posen, J., *Polylogarithmic proofs for multilinears over binary towers*][DP24]
  Statement numbering follows the archived revision of [DP24].
-/

namespace Binius.BinaryBasefold

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
  Binius.BinaryBasefold
open scoped NNReal
open ReedSolomon Code BerlekampWelch Function
open Finset AdditiveNTT Polynomial MvPolynomial Nat Matrix
open ProbabilityTheory

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} (γ_repetitions : ℕ) [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ] -- Should we allow ℓ = 0?
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r} -- ℓ ∈ {1, ..., r-1}
variable {𝓑 : Fin 2 ↪ L}
noncomputable section
variable [SampleableType L]
variable [hdiv : Fact (ϑ ∣ ℓ)]

open scoped NNReal ProbabilityTheory

open Classical in
omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] [NeZero 𝓡]
  [SampleableType L] in
/-- Pair-closeness to a concrete BBF codeword implies UDR-closeness to the BBF code. -/
lemma UDRClose_of_pair_UDRClose_to_BBF_Codeword (i : Fin r) (h_i : i ≤ ℓ)
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    (hg : g ∈ BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    (h_pair : pair_UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := i) h_i (f := f) (g := g)) :
    UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := i) (h_i := h_i) (f := f) := by
  unfold UDRClose pair_UDRClose at *
  calc
    2 * Δ₀(f, (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)) ≤
        2 * Δ₀(f, g) := by
      rw [ENat.mul_le_mul_left_iff
        (ha := by simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true])
        (h_top := by simp only [ne_eq, ENat.ofNat_ne_top, not_false_eq_true])]
      exact Code.distFromCode_le_dist_to_mem
        (C := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
        (u := f) (v := g) hg
    _ < BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) := by
      simpa only [Nat.cast_ofNat, Nat.cast_mul] using (ENat.coe_lt_coe.mpr h_pair)

omit [SampleableType L] in
/-- Folding a fiberwise-close word and its source UDR codeword stays pair-UDR-close. -/
lemma pair_UDRClose_iterated_fold_UDRCodeword_of_fiberwiseClose
    (i_star : Fin ℓ) (steps : ℕ) [NeZero steps]
    {destIdx : Fin r} (h_destIdx : destIdx.val = i_star.val + steps)
    (h_destIdx_le : destIdx ≤ ℓ)
    (f_star : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i_star, by omega⟩)
    (r_challenges : Fin steps → L)
    (h_close : fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨i_star, by omega⟩) (steps := steps) (destIdx := destIdx)
      (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f_star)) :
    let h_source_close := UDRClose_of_fiberwiseClose 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i_star, by omega⟩)
      (steps := steps) (destIdx := destIdx) (h_destIdx := h_destIdx)
      (h_destIdx_le := h_destIdx_le) (f := f_star) h_close
    let f_bar_star := UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ⟨i_star, by omega⟩ (Nat.le_of_lt i_star.isLt) (f := f_star)
      (h_within_radius := h_source_close)
    let folded_f := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ⟨i_star, by omega⟩ steps h_destIdx h_destIdx_le f_star
      (r_challenges := r_challenges)
    let folded_bar := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ⟨i_star, by omega⟩ steps h_destIdx h_destIdx_le f_bar_star
      (r_challenges := r_challenges)
    pair_UDRClose 𝔽q β destIdx h_destIdx_le folded_f folded_bar := by
  classical
  dsimp only
  let sourceIdx : Fin r := ⟨i_star, by omega⟩
  let h_source_close := UDRClose_of_fiberwiseClose 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := sourceIdx)
    (steps := steps) (destIdx := destIdx) (h_destIdx := h_destIdx)
    (h_destIdx_le := h_destIdx_le) (f := f_star) h_close
  let f_bar_star := UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    sourceIdx (Nat.le_of_lt i_star.isLt) (f := f_star)
    (h_within_radius := h_source_close)
  let folded_f := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    sourceIdx steps h_destIdx h_destIdx_le f_star (r_challenges := r_challenges)
  let folded_bar := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    sourceIdx steps h_destIdx h_destIdx_le f_bar_star (r_challenges := r_challenges)
  have h_containment :
      disagreementSet 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := destIdx) (destIdx := destIdx) (h_destIdx := rfl)
        (f := folded_f) (g := folded_bar) ⊆
      fiberwiseDisagreementSetPerFiber 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := sourceIdx) (steps := steps) (destIdx := destIdx)
        (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
        f_star f_bar_star := by
    intro y hy
    rw [mem_fiberwiseDisagreementSetPerFiber]
    by_contra hno
    have hfiber :
        fiberEvaluations 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (i := sourceIdx) (destIdx := destIdx) (steps := steps)
            h_destIdx h_destIdx_le f_star y =
        fiberEvaluations 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (i := sourceIdx) (destIdx := destIdx) (steps := steps)
            h_destIdx h_destIdx_le f_bar_star y := by
      funext idx
      by_contra hne
      exact hno ⟨idx, hne⟩
    have hfold := iterated_fold_eq_of_fiberEvaluations_eq 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := i_star) (steps := steps) (destIdx := destIdx)
      h_destIdx h_destIdx_le f_star f_bar_star r_challenges y hfiber
    have hy_ne : folded_f y ≠ folded_bar y := by
      simpa [disagreementSet, folded_f, folded_bar] using hy
    exact hy_ne hfold
  have h_hamming_le :
      hammingDist folded_f folded_bar ≤
        (fiberwiseDisagreementSetPerFiber 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := sourceIdx) (steps := steps) (destIdx := destIdx)
          (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
          f_star f_bar_star).card := by
    have h_card := Finset.card_le_card h_containment
    simpa [hammingDist, folded_f, folded_bar] using h_card
  have h_min_eq :
      fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := sourceIdx) (steps := steps) (destIdx := destIdx)
        h_destIdx h_destIdx_le (f := f_star) =
      pair_fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := sourceIdx) (steps := steps) (destIdx := destIdx)
        h_destIdx h_destIdx_le (f := f_star) (g := f_bar_star) := by
    rcases exists_fiberwiseClosestCodeword_within_close 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := sourceIdx)
      (destIdx := destIdx) (steps := steps) (h_destIdx := h_destIdx)
      (h_destIdx_le := h_destIdx_le) (f := f_star) h_close with ⟨g, hg_mem, hg_min⟩
    let C_source : Set (sDomain 𝔽q β h_ℓ_add_R_rate sourceIdx → L) :=
      BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) sourceIdx
    haveI h_C_source_dist_ne :
        NeZero (‖(C_source : Set (sDomain 𝔽q β h_ℓ_add_R_rate sourceIdx → L))‖₀) := ⟨by
      dsimp only [C_source]
      change BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) sourceIdx ≠ 0
      rw [BBF_CodeDistance_eq 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := sourceIdx) (h_i := Nat.le_of_lt i_star.isLt)]
      omega⟩
    have h_pair_fw : pair_fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := sourceIdx) (steps := steps) (destIdx := destIdx)
        h_destIdx h_destIdx_le (f := f_star) (g := g) := by
      unfold pair_fiberwiseClose
      rw [← hg_min]
      exact h_close.2
    have h_pair_udr : pair_UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := sourceIdx) (h_i := Nat.le_of_lt i_star.isLt) (f := f_star) (g := g) :=
      by
        simpa [sourceIdx] using
          pairUDRClose_of_pairFiberwiseClose 𝔽q β
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i_star)
            (steps := steps) (destIdx := destIdx) h_destIdx h_destIdx_le
            (f := f_star) (g := g) h_pair_fw
    have h_g_le :
        Δ₀(f_star, g) ≤ Code.uniqueDecodingRadius (C := C_source) := by
      exact (Code.UDRClose_iff_two_mul_proximity_lt_d_UDR (C := C_source)).2 (by
        simpa [C_source, pair_UDRClose, BBF_CodeDistance] using h_pair_udr)
    have h_bar_mem : f_bar_star ∈ C_source := by
      dsimp only [C_source]
      exact UDRCodeword_mem_BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := sourceIdx) (h_i := Nat.le_of_lt i_star.isLt)
        (f := f_star) (h_within_radius := h_source_close)
    have h_bar_le :
        Δ₀(f_star, f_bar_star) ≤ Code.uniqueDecodingRadius (C := C_source) := by
      simpa [C_source, f_bar_star] using
        dist_to_UDRCodeword_le_uniqueDecodingRadius 𝔽q β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := sourceIdx) (h_i := Nat.le_of_lt i_star.isLt)
          (f := f_star) (h_within_radius := h_source_close)
    have hg_eq : g = f_bar_star :=
      Code.eq_of_le_uniqueDecodingRadius (C := C_source) (u := f_star)
        (v := g) (w := f_bar_star) (hv := by simpa [C_source] using hg_mem)
        (hw := h_bar_mem) (huv := h_g_le) (huw := h_bar_le)
    rw [hg_eq] at hg_min
    simpa [f_bar_star, h_source_close] using hg_min
  have h_source_lt :
      2 *
          (fiberwiseDisagreementSetPerFiber 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (i := sourceIdx) (steps := steps) (destIdx := destIdx)
            (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
            f_star f_bar_star).card <
        BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := destIdx) := by
    unfold fiberwiseClose at h_close
    rw [h_min_eq] at h_close
    simpa [pair_fiberwiseDistance, sourceIdx, f_bar_star] using h_close.2
  unfold pair_UDRClose
  exact lt_of_le_of_lt (Nat.mul_le_mul_left 2 h_hamming_le) h_source_lt

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] [SampleableType L] in
/-- Helper: global agreement of two source words is preserved by iterated folding. -/
lemma fold_agreement_of_fiber_agreement (i : Fin ℓ) (steps : ℕ)
    {destIdx : Fin r} (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (r_challenges : Fin steps → L) (y : sDomain 𝔽q β h_ℓ_add_R_rate destIdx) :
    (∀ x, f x = g x) →
    (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ steps h_destIdx h_destIdx_le f (r_challenges := r_challenges) y =
    (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ steps h_destIdx h_destIdx_le g (r_challenges := r_challenges) y)) := by
  intro h_agree
  have hfg : f = g := funext h_agree
  rw [hfg]

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] [SampleableType L] in
/-- Helper: The disagreement set of the folded functions is a subset of the fiberwise disagreement set. -/
lemma disagreement_fold_subset_fiberwiseDisagreement (i : Fin ℓ) (steps : ℕ) [NeZero steps]
    {destIdx : Fin r} (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (r_challenges : Fin steps → L) :
    let folded_f := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ steps h_destIdx h_destIdx_le f (r_challenges := r_challenges)
    let folded_g := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ steps h_destIdx h_destIdx_le g (r_challenges := r_challenges)
    disagreementSet 𝔽q β (i := destIdx) (destIdx := destIdx) (h_destIdx := rfl) (f := folded_f) (g := folded_g) ⊆
    fiberwiseDisagreementSet 𝔽q β (i := ⟨i, by omega⟩) steps h_destIdx h_destIdx_le f g := by
  classical
  dsimp only
  intro y hy
  have h_steps_ne : steps ≠ 0 := NeZero.ne steps
  have h_exists : ∃ x, f x ≠ g x := by
    by_contra hnone
    have hfg : f = g := by
      funext x
      exact not_not.mp (by
        intro hx
        exact hnone ⟨x, hx⟩)
    rw [hfg] at hy
    simp [disagreementSet] at hy
  simp [fiberwiseDisagreementSet, h_steps_ne, h_exists]

omit [SampleableType L] in
/-- **Lemma 4.25 distance bridge.**
If the last noncompliant block has no folding bad event and the next word is UDR-close, then
the folded source is not pair-UDR-close to the decoded next codeword. In the close branch,
otherwise two destination codewords would both lie inside the unique-decoding ball around the
folded source, forcing compliance; in the far branch this is exactly the bad-event negation. -/
lemma lemma_4_24_dist_folded_ge_of_last_noncompliant (i_star : Fin ℓ) (steps : ℕ) [NeZero steps]
    {destIdx : Fin r} (h_destIdx : destIdx.val = i_star.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f_star : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i_star, by omega⟩)
    (f_next : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx)
    (r_challenges : Fin steps → L)
    -- 1. f_next is the actual folded function
    -- 2. i* is non-compliant
    (h_not_compliant : ¬ isCompliant 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i_star, by omega⟩ steps h_destIdx h_destIdx_le
       f_star f_next (challenges := r_challenges))
    -- 3. No bad event occurred at i*
    (h_no_bad_event : ¬ foldingBadEvent 𝔽q β (i := ⟨i_star, by omega⟩) steps h_destIdx h_destIdx_le f_star r_challenges)
    -- 4. The next function `f_next` IS close enough to have a unique codeword `f_bar_next`
    (h_next_close : UDRClose 𝔽q β destIdx h_destIdx_le f_next) :
      let folded_f := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        ⟨i_star, by omega⟩ steps h_destIdx h_destIdx_le f_star
        (r_challenges := r_challenges)
      let f_bar_next := UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        destIdx h_destIdx_le (f := f_next) (h_within_radius := h_next_close)
      ¬ pair_UDRClose 𝔽q β destIdx h_destIdx_le folded_f f_bar_next := by
  dsimp only
  intro h_pair
  let folded_f := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    ⟨i_star, by omega⟩ steps h_destIdx h_destIdx_le f_star
    (r_challenges := r_challenges)
  let f_bar_next := UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    destIdx h_destIdx_le (f := f_next) (h_within_radius := h_next_close)
  by_cases h_close : fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨i_star, by omega⟩) (steps := steps) (destIdx := destIdx)
      (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f_star)
  · let sourceIdx : Fin r := ⟨i_star, by omega⟩
    let h_source_close := UDRClose_of_fiberwiseClose 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := sourceIdx)
      (steps := steps) (destIdx := destIdx) (h_destIdx := h_destIdx)
      (h_destIdx_le := h_destIdx_le) (f := f_star) h_close
    let f_bar_star := UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      sourceIdx (Nat.le_of_lt i_star.isLt) (f := f_star)
      (h_within_radius := h_source_close)
    let folded_bar := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      sourceIdx steps h_destIdx h_destIdx_le f_bar_star
      (r_challenges := r_challenges)
    have h_pair_bar : pair_UDRClose 𝔽q β destIdx h_destIdx_le folded_f folded_bar := by
      simpa [folded_f, folded_bar, f_bar_star, h_source_close] using
        pair_UDRClose_iterated_fold_UDRCodeword_of_fiberwiseClose 𝔽q β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i_star := i_star) (steps := steps) (destIdx := destIdx)
          (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
          (f_star := f_star) (r_challenges := r_challenges) h_close
    let C_dest : Set (sDomain 𝔽q β h_ℓ_add_R_rate destIdx → L) :=
      BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx
    have h_bar_next_mem : f_bar_next ∈ C_dest := by
      simpa [C_dest, f_bar_next] using
        UDRCodeword_mem_BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := destIdx) (h_i := h_destIdx_le) (f := f_next)
          (h_within_radius := h_next_close)
    have h_bar_star_mem :
        f_bar_star ∈ BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) sourceIdx :=
      UDRCodeword_mem_BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := sourceIdx) (h_i := Nat.le_of_lt i_star.isLt)
        (f := f_star) (h_within_radius := h_source_close)
    have h_steps_lt : steps < ℓ + 1 := by
      have hle : i_star.val + steps ≤ ℓ := by
        rw [← h_destIdx]
        exact h_destIdx_le
      omega
    have h_i_add_steps : sourceIdx.val + steps < ℓ + 𝓡 := by
      have hle : i_star.val + steps ≤ ℓ := by
        rw [← h_destIdx]
        exact h_destIdx_le
      exact Nat.lt_of_le_of_lt hle (Nat.lt_add_of_pos_right (Nat.pos_of_neZero 𝓡))
    have h_destIdx_fin :
        destIdx =
          (⟨sourceIdx.val + steps, Nat.lt_trans h_i_add_steps h_ℓ_add_R_rate⟩ : Fin r) :=
      Fin.eq_of_val_eq h_destIdx
    have h_folded_bar_mem : folded_bar ∈ C_dest := by
      let f_bar_subtype :
          BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            sourceIdx := ⟨f_bar_star, h_bar_star_mem⟩
      have h_mem := iterated_fold_preserves_BBF_Code_membership 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := sourceIdx)
        (destIdx := destIdx) (steps := ⟨steps, h_steps_lt⟩)
        (h_i_add_steps := h_i_add_steps) (h_destIdx := h_destIdx_fin)
        (h_destIdx_le := h_destIdx_le) (f := f_bar_subtype)
        (r_challenges := r_challenges)
      simpa [C_dest, folded_bar, f_bar_subtype]
        using h_mem
    haveI h_C_dest_dist_ne :
        NeZero (‖(C_dest : Set (sDomain 𝔽q β h_ℓ_add_R_rate destIdx → L))‖₀) := ⟨by
      dsimp only [C_dest]
      change BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx ≠ 0
      rw [BBF_CodeDistance_eq 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := destIdx) (h_i := h_destIdx_le)]
      omega⟩
    have h_pair_bar_le :
        Δ₀(folded_f, folded_bar) ≤ Code.uniqueDecodingRadius (C := C_dest) := by
      exact (Code.UDRClose_iff_two_mul_proximity_lt_d_UDR (C := C_dest)).2 (by
        simpa [C_dest, pair_UDRClose] using h_pair_bar)
    have h_pair_next_le :
        Δ₀(folded_f, f_bar_next) ≤ Code.uniqueDecodingRadius (C := C_dest) := by
      exact (Code.UDRClose_iff_two_mul_proximity_lt_d_UDR (C := C_dest)).2 (by
        simpa [C_dest, pair_UDRClose, BBF_CodeDistance, folded_f, f_bar_next] using h_pair)
    have h_folded_bar_eq_next : folded_bar = f_bar_next :=
      Code.eq_of_le_uniqueDecodingRadius (C := C_dest) (u := folded_f)
        (v := folded_bar) (w := f_bar_next)
        (hv := h_folded_bar_mem) (hw := h_bar_next_mem)
        (huv := h_pair_bar_le) (huw := h_pair_next_le)
    have h_compliant : isCompliant 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := sourceIdx) (steps := steps) (destIdx := destIdx)
        (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
        (f_i := f_star) (f_i_plus_steps := f_next) (challenges := r_challenges) := by
      refine ⟨h_close, h_next_close, ?_⟩
      simpa [folded_bar, f_bar_star, f_bar_next, h_source_close] using h_folded_bar_eq_next
    exact h_not_compliant (by simpa [sourceIdx] using h_compliant)
  · have h_bar_mem : f_bar_next ∈
        BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx :=
      UDRCodeword_mem_BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := destIdx) (h_i := h_destIdx_le) (f := f_next)
        (h_within_radius := h_next_close)
    have h_folded_close : UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := destIdx) (h_i := h_destIdx_le) (f := folded_f) :=
      UDRClose_of_pair_UDRClose_to_BBF_Codeword 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := destIdx)
        (h_i := h_destIdx_le) (f := folded_f) (g := f_bar_next)
        h_bar_mem h_pair
    have h_far' : ¬ fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := ⟨i_star, by omega⟩) (steps := steps) (destIdx := destIdx)
        (h_destIdx := by omega) (h_destIdx_le := h_destIdx_le) (f := f_star) := by
      simpa using h_close
    apply h_no_bad_event
    simp [foldingBadEvent, h_far', folded_f, h_folded_close]

end

end Binius.BinaryBasefold
