/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.Lift

/-!
## Pre-tensor fiber congruence

This file isolates the fiber-local part of the Binary Basefold pre-tensor proximity argument.
Keeping these lemmas behind a small module boundary prevents downstream soundness files from
rechecking the heavier fold-recursion proof terms in `Soundness.Lift`.
-/

namespace Binius.BinaryBasefold

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
  Binius.BinaryBasefold
open scoped NNReal
open ReedSolomon Code BerlekampWelch Function
open Finset AdditiveNTT Polynomial MvPolynomial Nat Matrix
open ProbabilityTheory

noncomputable section

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ]
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r}
variable {𝓑 : Fin 2 ↪ L}

private lemma fiber_split_div
    {n : ℕ} (c : Fin 2) (b : Fin (2 ^ n)) :
    (b.val + 2 ^ n * c.val) / 2 ^ n = c.val := by
  rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos n)]
  rw [Nat.div_eq_of_lt b.isLt]
  simp

private lemma fiber_split_mod
    {n : ℕ} (c : Fin 2) (b : Fin (2 ^ n)) :
    (b.val + 2 ^ n * c.val) % 2 ^ n = b.val := by
  rw [Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt b.isLt

set_option maxHeartbeats 2000000 in
-- The induction repeatedly rewrites quotient-fiber indices through the fold recursion.
private lemma iterated_fold_steps_eq_of_fiber_agree (i : Fin ℓ) :
    ∀ (steps : ℕ) (h_i_add_steps : i.val + steps ≤ ℓ)
      (f g : sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩) → L)
      (r_challenges : Fin steps → L)
      (y : sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨i.val + steps, by omega⟩)),
      (∀ idx : Fin (2 ^ steps),
        f (qMap_total_fiber 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := ⟨i, by omega⟩) (steps := steps)
          (h_i_add_steps := fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps)
          (y := y) idx) =
        g (qMap_total_fiber 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := ⟨i, by omega⟩) (steps := steps)
          (h_i_add_steps := fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps)
          (y := y) idx)) →
      iterated_fold_steps 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := ⟨i, by omega⟩)
        (steps := ⟨steps, Nat.lt_succ_of_le (Nat.le_of_add_left_le h_i_add_steps)⟩)
        (h_i_add_steps := fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps)
        f r_challenges y =
      iterated_fold_steps 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := ⟨i, by omega⟩)
        (steps := ⟨steps, Nat.lt_succ_of_le (Nat.le_of_add_left_le h_i_add_steps)⟩)
        (h_i_add_steps := fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps)
        g r_challenges y := by
  intro steps
  induction steps with
  | zero =>
      intro h_i_add_steps f g r_challenges y hfg
      unfold iterated_fold_steps
      rw [Fin.dfoldl_zero, Fin.dfoldl_zero]
      have h0 := hfg ⟨0, by norm_num⟩
      simpa [qMap_total_fiber] using h0
  | succ n ih =>
      intro h_i_add_steps f g r_challenges y hfg
      let tailChallenges : Fin n → L := fun j => r_challenges j.castSucc
      let z (c : Fin 2) : sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨i.val + n, by omega⟩) :=
        qMap_total_fiber 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := ⟨i.val + n, by omega⟩) (steps := 1)
          (h_i_add_steps := by
            simp only
            exact Nat.lt_of_le_of_lt (by omega)
              (Nat.lt_add_of_pos_right (Nat.pos_of_neZero 𝓡)))
          (y := y) c
      have htail (c : Fin 2) :
          iterated_fold_steps 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (i := ⟨i, by omega⟩)
            (steps := ⟨n, by omega⟩)
            (h_i_add_steps := fin_ℓ_steps_lt_ℓ_add_R i n (by omega))
            f tailChallenges (z c) =
          iterated_fold_steps 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (i := ⟨i, by omega⟩)
            (steps := ⟨n, by omega⟩)
            (h_i_add_steps := fin_ℓ_steps_lt_ℓ_add_R i n (by omega))
            g tailChallenges (z c) := by
        refine ih (by omega) f g tailChallenges (z c) ?_
        intro b
        let idx : Fin (2 ^ (n + 1)) := ⟨b.val + 2 ^ n * c.val, by
          fin_cases c
          · simp only [mul_zero, add_zero]
            rw [pow_succ]
            have hb := b.isLt
            have hm : 0 < 2 ^ n := Nat.two_pow_pos n
            omega
          · simp only [mul_one]
            rw [pow_succ]
            have hb := b.isLt
            have hm : 0 < 2 ^ n := Nat.two_pow_pos n
            omega⟩
        have hsplit := qMap_total_fiber_succ_peel_last 𝔽q β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := i) (n := n) (h_i_add_steps := h_i_add_steps) y idx
        have hdiv :
            (⟨idx.val / 2 ^ n, by
              have hb' : idx.val < 2 ^ n * 2 := by
                exact Nat.lt_of_lt_of_eq idx.isLt (by rw [pow_succ])
              exact Nat.div_lt_of_lt_mul hb'⟩ : Fin 2) = c := by
          ext
          exact fiber_split_div c b
        have hmod :
            (⟨idx.val % 2 ^ n, Nat.mod_lt _ (Nat.two_pow_pos n)⟩ :
              Fin (2 ^ n)) = b := by
          ext
          exact fiber_split_mod c b
        have hfg_idx := hfg idx
        rw [hsplit, hdiv, hmod] at hfg_idx
        exact hfg_idx
      rw [iterated_fold_succ_last 𝔽q β i n h_i_add_steps,
        iterated_fold_succ_last 𝔽q β i n h_i_add_steps]
      unfold fold_legacy
      simp [tailChallenges, z, htail]

set_option maxHeartbeats 2000000 in
-- The wrapper reconciles the concrete destination index with the nat-indexed fold recursion.
lemma iterated_fold_eq_of_fiberEvaluations_eq
    (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (r_challenges : Fin steps → L)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate destIdx)
    (hfiber :
      fiberEvaluations 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := (⟨i, by omega⟩ : Fin r)) (destIdx := destIdx) (steps := steps)
        h_destIdx h_destIdx_le f y =
      fiberEvaluations 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := (⟨i, by omega⟩ : Fin r)) (destIdx := destIdx) (steps := steps)
        h_destIdx h_destIdx_le g y) :
    iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := (⟨i, by omega⟩ : Fin r)) (destIdx := destIdx) (steps := steps)
      h_destIdx h_destIdx_le f r_challenges y =
    iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := (⟨i, by omega⟩ : Fin r)) (destIdx := destIdx) (steps := steps)
      h_destIdx h_destIdx_le g r_challenges y := by
  rcases destIdx with ⟨destVal, hdestVal⟩
  have hdest :
      (⟨destVal, hdestVal⟩ : Fin r) =
        (⟨i.val + steps, by
          have hlt : i.val + steps < ℓ + 𝓡 := by
            have hle : i.val + steps ≤ ℓ := by
              rw [← h_destIdx]
              exact h_destIdx_le
            exact Nat.lt_of_le_of_lt hle (Nat.lt_add_of_pos_right (Nat.pos_of_neZero 𝓡))
          exact Nat.lt_trans hlt h_ℓ_add_R_rate⟩ : Fin r) := by
    exact Fin.eq_of_val_eq (by simpa using h_destIdx)
  cases hdest
  have h_i_add_steps : i.val + steps ≤ ℓ := by
    simpa using h_destIdx_le
  rw [iterated_fold_eq_iterated_fold_steps 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := (⟨i, by omega⟩ : Fin r)) (steps := steps)
      (h_steps := Nat.lt_succ_of_le (Nat.le_of_add_left_le h_i_add_steps))
      (h_i_add_steps := fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps)
      (h_destIdx_le := by simpa using h_destIdx_le)
      (f := f) (r_challenges := r_challenges) (y := y),
    iterated_fold_eq_iterated_fold_steps 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := (⟨i, by omega⟩ : Fin r)) (steps := steps)
      (h_steps := Nat.lt_succ_of_le (Nat.le_of_add_left_le h_i_add_steps))
      (h_i_add_steps := fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps)
      (h_destIdx_le := by simpa using h_destIdx_le)
      (f := g) (r_challenges := r_challenges) (y := y)]
  refine iterated_fold_steps_eq_of_fiber_agree 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps h_i_add_steps
    f g r_challenges y ?_
  intro idx
  have hidx := congrFun hfiber idx
  simpa [fiberEvaluations] using hidx

lemma preTensorCombine_row_eq_of_fiberEvaluations_eq
    (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (rowIdx : Fin (2 ^ steps))
    (y : sDomain 𝔽q β h_ℓ_add_R_rate destIdx)
    (hfiber :
      fiberEvaluations 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := (⟨i, by omega⟩ : Fin r)) (destIdx := destIdx) (steps := steps)
        h_destIdx h_destIdx_le f y =
      fiberEvaluations 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := (⟨i, by omega⟩ : Fin r)) (destIdx := destIdx) (steps := steps)
        h_destIdx h_destIdx_le g y) :
    (preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le f) rowIdx y =
    (preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le g) rowIdx y := by
  dsimp [preTensorCombine_WordStack]
  exact iterated_fold_eq_of_fiberEvaluations_eq 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := i) (steps := steps) (destIdx := destIdx)
    h_destIdx h_destIdx_le f g (bitsOfIndex (L := L) rowIdx) y hfiber

/-- A differing pre-tensor row over a quotient point certifies that the quotient point lies in the
honest per-fiber disagreement set. -/
lemma preTensorCombine_exists_row_ne_mem_fiberwiseDisagreementSetPerFiber
    (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate destIdx)
    (hrow : ∃ rowIdx : Fin (2 ^ steps),
      (preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le f) rowIdx y ≠
      (preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le g) rowIdx y) :
    y ∈
      fiberwiseDisagreementSetPerFiber 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := ⟨i, by omega⟩) (destIdx := destIdx) (steps := steps)
        h_destIdx h_destIdx_le f g := by
  by_contra hy_not
  rcases hrow with ⟨rowIdx, hne⟩
  apply hne
  have hfiber :
      fiberEvaluations 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := (⟨i, by omega⟩ : Fin r)) (destIdx := destIdx) (steps := steps)
          h_destIdx h_destIdx_le f y =
      fiberEvaluations 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := (⟨i, by omega⟩ : Fin r)) (destIdx := destIdx) (steps := steps)
          h_destIdx h_destIdx_le g y := by
    funext idx
    by_contra hne
    exact hy_not ((mem_fiberwiseDisagreementSetPerFiber 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := (⟨i, by omega⟩ : Fin r)) (destIdx := destIdx) (steps := steps)
      h_destIdx h_destIdx_le f g y).2 ⟨idx, hne⟩)
  exact preTensorCombine_row_eq_of_fiberEvaluations_eq 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := i) (steps := steps) (destIdx := destIdx)
    h_destIdx h_destIdx_le f g rowIdx y hfiber

end
end Binius.BinaryBasefold
