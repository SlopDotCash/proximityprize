/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.Lift

/-!
# Binary Basefold pre-tensor metric bounds

Fiber congruence, disagreement and Hamming bounds, unique decoding, closest-codeword
bounds, and witness transport for the pre-tensor map.
-/

section PreTensorFiber

/-!
## Pre-tensor fiber congruence

Agreement on a quotient fiber is preserved by iterated folding and the pre-tensor map.
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

end PreTensorFiber

section PreTensorDisagreement

/-!
## Pre-tensor column disagreements

The finite-set bridge used in Lemma 4.22 states that if two pre-tensor stacks disagree in
an interleaved column, then the corresponding quotient point is in the honest per-fiber
disagreement set.
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

private lemma exists_row_ne_of_interleave_ne
    {κ ι A : Type*} (U V : Code.WordStack A κ ι) {y : ι}
    (h : (Code.interleaveWordStack U) y ≠ (Code.interleaveWordStack V) y) :
    ∃ rowIdx : κ, U rowIdx y ≠ V rowIdx y := by
  by_contra hnone
  apply h
  funext rowIdx
  by_contra hne
  exact hnone ⟨rowIdx, hne⟩

/-- Column disagreements of two pre-tensor stacks are contained in the honest per-fiber
disagreement set. -/
lemma preTensorCombine_disagreementCols_subset_fiberwiseDisagreementSetPerFiber
    (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩) :
    Code.disagreementCols
      (Code.interleaveWordStack
        (preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le f))
      (Code.interleaveWordStack
        (preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le g)) ⊆
    fiberwiseDisagreementSetPerFiber 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨i, by omega⟩) (destIdx := destIdx) (steps := steps)
      h_destIdx h_destIdx_le f g := by
  intro y hy
  rw [Code.mem_disagreementCols] at hy
  refine preTensorCombine_exists_row_ne_mem_fiberwiseDisagreementSetPerFiber 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := i) (steps := steps) (destIdx := destIdx)
    h_destIdx h_destIdx_le f g y ?_
  exact exists_row_ne_of_interleave_ne
    (preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le f)
    (preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le g) hy

end
end Binius.BinaryBasefold

end PreTensorDisagreement

section PreTensorHamming

/-!
## Pre-tensor Hamming distance

The column-disagreement subset gives the concrete Hamming bound used by the
pre-tensor proximity lemma.
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

private lemma hammingDist_le_card_of_disagreementCols_subset
    {ι A : Type*} [Fintype ι] [DecidableEq A]
    (u v : ι → A) {B : Finset ι}
    (hsubset : Code.disagreementCols u v ⊆ B) :
    Δ₀(u, v) ≤ B.card := by
  rw [Code.hammingDist_eq_disagreementCols_card]
  exact Finset.card_le_card hsubset

/-- The interleaved Hamming distance between two pre-tensor stacks is bounded by the number of
quotient points whose whole source fiber contains a disagreement. -/
lemma preTensorCombine_interleaved_hamming_le_pair_fiberwiseDistance
    (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩) :
    Δ₀((⋈|preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le f),
      (⋈|preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le g)) ≤
    pair_fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨i, by omega⟩) (destIdx := destIdx) (steps := steps)
      h_destIdx h_destIdx_le f g := by
  let Uf := preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le f
  let Ug := preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le g
  have hsubset :
      Code.disagreementCols (Code.interleaveWordStack Uf) (Code.interleaveWordStack Ug) ⊆
        fiberwiseDisagreementSetPerFiber 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := ⟨i, by omega⟩) (destIdx := destIdx) (steps := steps)
          h_destIdx h_destIdx_le f g := by
    simpa [Uf, Ug] using
      preTensorCombine_disagreementCols_subset_fiberwiseDisagreementSetPerFiber 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := i) (steps := steps) (destIdx := destIdx)
        h_destIdx h_destIdx_le f g
  simpa [Uf, Ug, pair_fiberwiseDistance] using
    hammingDist_le_card_of_disagreementCols_subset
      (Code.interleaveWordStack Uf) (Code.interleaveWordStack Ug) hsubset

end
end Binius.BinaryBasefold

end PreTensorHamming

section PreTensorUDR

/-!
## Pre-tensor unique-decoding radius arithmetic

For the numeric part of Lemma 4.22, the `fiberwiseClose` hypothesis places the
fiberwise distance below the destination code's unique-decoding radius.
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

/-- The destination half of `fiberwiseClose` is exactly the UDR inequality needed for the
interleaved-code proximity witness. -/
lemma fiberwiseDistance_le_uniqueDecodingRadius_of_fiberwiseClose
    (i : Fin ℓ) (steps : ℕ) [NeZero steps] {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (h_close : fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨i, by omega⟩) (steps := steps) (h_destIdx := by
        simpa using h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f_i)) :
    fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := ⟨i, by omega⟩) (destIdx := destIdx) (steps := steps)
        h_destIdx h_destIdx_le f_i ≤
      Code.uniqueDecodingRadius
        (C := (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx :
          Set (sDomain 𝔽q β h_ℓ_add_R_rate destIdx → L))) := by
  let C_dest : Set (sDomain 𝔽q β h_ℓ_add_R_rate destIdx → L) :=
    BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx
  have h_dist_pos : 0 <
      ‖(C_dest : Set (sDomain 𝔽q β h_ℓ_add_R_rate destIdx → L))‖₀ := by
    have h_pos : 0 <
        BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx := by
      simp [BBF_CodeDistance_eq (L := L) 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := destIdx) (h_i := h_destIdx_le)]
    simpa [C_dest, BBF_CodeDistance] using h_pos
  haveI : NeZero
      ‖(C_dest : Set (sDomain 𝔽q β h_ℓ_add_R_rate destIdx → L))‖₀ :=
    NeZero.of_pos h_dist_pos
  exact (Code.UDRClose_iff_two_mul_proximity_lt_d_UDR (C := C_dest)).2 (by
    simpa [C_dest, BBF_CodeDistance] using h_close.2)

end
end Binius.BinaryBasefold

end PreTensorUDR

section PreTensorClosest

/-!
## Pre-tensor closest-codeword distance

The Hamming bound controls fiberwise distance to a chosen fiberwise-closest source codeword.
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

/-- A fiberwise-closest source codeword gives a pre-tensor stack within the fiberwise distance. -/
lemma preTensorCombine_hamming_le_fiberwiseDistance_of_closest
    (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f_i g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (hg_min :
      fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := ⟨i, by omega⟩) (destIdx := destIdx) (steps := steps)
        h_destIdx h_destIdx_le f_i =
      pair_fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := ⟨i, by omega⟩) (destIdx := destIdx) (steps := steps)
        h_destIdx h_destIdx_le f_i g) :
    Δ₀((⋈|preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le f_i),
      (⋈|preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le g)) ≤
    fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨i, by omega⟩) (destIdx := destIdx) (steps := steps)
      h_destIdx h_destIdx_le f_i := by
  have hdist_le_pair :
      Δ₀((⋈|preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le f_i),
        (⋈|preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le g)) ≤
      pair_fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := ⟨i, by omega⟩) (destIdx := destIdx) (steps := steps)
        h_destIdx h_destIdx_le f_i g :=
    preTensorCombine_interleaved_hamming_le_pair_fiberwiseDistance 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := i) (steps := steps) (destIdx := destIdx)
      h_destIdx h_destIdx_le f_i g
  simpa [hg_min] using hdist_le_pair

end
end Binius.BinaryBasefold

end PreTensorClosest

section PreTensorCodeDistance

/-!
## Pre-tensor distance to the destination interleaved code

A chosen closest source codeword bounds the distance from the pre-tensor stack to the
destination interleaved code.
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

/-- The interleaved word associated to a pre-tensor stack. -/
def preTensorCombine_interleavedWord
    (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩) :
    Code.InterleavedWord L (Fin (2 ^ steps))
      (sDomain 𝔽q β h_ℓ_add_R_rate destIdx) :=
  ⋈|preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le f_i

/-- Destination interleaved BBF code for a pre-tensor stack. -/
def preTensorCombine_destInterleavedCode
    (steps : ℕ) (destIdx : Fin r) :
    Set (Code.InterleavedWord L (Fin (2 ^ steps))
      (sDomain 𝔽q β h_ℓ_add_R_rate destIdx)) :=
  interleavedCodeSet
    (C := (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx :
      Set (sDomain 𝔽q β h_ℓ_add_R_rate destIdx → L)))

/-- Distance from a pre-tensor stack to the destination interleaved BBF code. -/
noncomputable def preTensorCombine_distFromInterleavedCode
    (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩) : ℕ∞ :=
  Δ₀(preTensorCombine_interleavedWord 𝔽q β i steps h_destIdx h_destIdx_le f_i,
    preTensorCombine_destInterleavedCode (L := L) 𝔽q β steps destIdx)

/-- Hamming distance between two pre-tensor interleaved words. -/
def preTensorCombine_interleavedHamming
    (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (g : BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    : ℕ :=
  Δ₀(preTensorCombine_interleavedWord 𝔽q β i steps h_destIdx h_destIdx_le f_i,
    preTensorCombine_interleavedWord 𝔽q β i steps h_destIdx h_destIdx_le
      (g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩))

/-- A source BBF codeword's pre-tensor interleaved word is in the destination interleaved code. -/
lemma preTensorCombine_interleavedWord_mem_destInterleavedCode
    (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (g : BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩) :
    preTensorCombine_interleavedWord 𝔽q β i steps h_destIdx h_destIdx_le
      (g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩) ∈
    preTensorCombine_destInterleavedCode (L := L) 𝔽q β steps destIdx := by
  unfold preTensorCombine_interleavedWord preTensorCombine_destInterleavedCode
  exact preTensorCombine_is_interleavedCodeword_of_codeword 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := i) (steps := steps) (destIdx := destIdx)
    h_destIdx h_destIdx_le g

/-- Distance to the destination interleaved code is at most distance to any concrete interleaved
codeword. -/
lemma preTensorCombine_distFromInterleavedCode_le_interleavedHamming_of_codeword
    (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (g : BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩) :
    preTensorCombine_distFromInterleavedCode 𝔽q β i steps h_destIdx h_destIdx_le f_i ≤
    preTensorCombine_interleavedHamming 𝔽q β i steps h_destIdx h_destIdx_le f_i g := by
  change
    Δ₀(preTensorCombine_interleavedWord 𝔽q β i steps h_destIdx h_destIdx_le f_i,
      preTensorCombine_destInterleavedCode (L := L) 𝔽q β steps destIdx) ≤
    Δ₀(preTensorCombine_interleavedWord 𝔽q β i steps h_destIdx h_destIdx_le f_i,
      preTensorCombine_interleavedWord 𝔽q β i steps h_destIdx h_destIdx_le
        (g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩))
  exact Code.distFromCode_le_dist_to_mem
    (preTensorCombine_interleavedWord 𝔽q β i steps h_destIdx h_destIdx_le f_i)
    (preTensorCombine_interleavedWord 𝔽q β i steps h_destIdx h_destIdx_le
      (g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩))
    (preTensorCombine_interleavedWord_mem_destInterleavedCode 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := i) (steps := steps) (destIdx := destIdx)
      h_destIdx h_destIdx_le g)

/-- A closest source codeword gives a pre-tensor interleaved word within the fiberwise distance. -/
lemma preTensorCombine_interleavedHamming_le_fiberwiseDistance_of_closest
    (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (g : BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (hg_min :
      fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := ⟨i, by omega⟩) (destIdx := destIdx) (steps := steps)
        h_destIdx h_destIdx_le f_i =
      pair_fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := ⟨i, by omega⟩) (destIdx := destIdx) (steps := steps)
        h_destIdx h_destIdx_le f_i
        (g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)) :
    preTensorCombine_interleavedHamming 𝔽q β i steps h_destIdx h_destIdx_le f_i g ≤
    fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨i, by omega⟩) (destIdx := destIdx) (steps := steps)
      h_destIdx h_destIdx_le f_i := by
  unfold preTensorCombine_interleavedHamming preTensorCombine_interleavedWord
  exact preTensorCombine_hamming_le_fiberwiseDistance_of_closest 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := i) (steps := steps) (destIdx := destIdx)
    h_destIdx h_destIdx_le f_i
    (g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    hg_min

/-- A closest source codeword gives a direct distance-to-the-interleaved-code bound. -/
lemma preTensorCombine_distFromInterleavedCode_le_fiberwiseDistance_of_closest
    (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (g : BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (hg_min :
      fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := ⟨i, by omega⟩) (destIdx := destIdx) (steps := steps)
        h_destIdx h_destIdx_le f_i =
      pair_fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := ⟨i, by omega⟩) (destIdx := destIdx) (steps := steps)
        h_destIdx h_destIdx_le f_i
        (g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)) :
    preTensorCombine_distFromInterleavedCode 𝔽q β i steps h_destIdx h_destIdx_le f_i ≤
    fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨i, by omega⟩) (destIdx := destIdx) (steps := steps)
      h_destIdx h_destIdx_le f_i := by
  exact le_trans
    (preTensorCombine_distFromInterleavedCode_le_interleavedHamming_of_codeword 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := i) (steps := steps) (destIdx := destIdx)
      h_destIdx h_destIdx_le f_i g)
    (by
      exact_mod_cast
        preTensorCombine_interleavedHamming_le_fiberwiseDistance_of_closest 𝔽q β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := i) (steps := steps) (destIdx := destIdx)
          h_destIdx h_destIdx_le f_i g hg_min)

end
end Binius.BinaryBasefold

end PreTensorCodeDistance

section PreTensorDistance

/-!
## Pre-tensor distance and proximity

Row/fiber congruence gives the distance-facing half of Lemma 4.22.
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

/-- Fiberwise closeness of a source word gives joint proximity of its pre-tensor stack to the
destination interleaved code. -/
lemma preTensorCombine_jointProximityNat_of_fiberwiseClose
    (i : Fin ℓ) (steps : ℕ) [NeZero steps] {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (h_close : fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨i, by omega⟩) (steps := steps) (h_destIdx := by
        simpa using h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f_i)) :
    jointProximityNat
      (C := (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx :
        Set (sDomain 𝔽q β h_ℓ_add_R_rate destIdx → L)))
      (u := preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le f_i)
      (Code.uniqueDecodingRadius (C := (BBF_Code 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx :
          Set (sDomain 𝔽q β h_ℓ_add_R_rate destIdx → L)))) := by
  classical
  let C_dest : Set (sDomain 𝔽q β h_ℓ_add_R_rate destIdx → L) :=
    BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx
  rcases exists_fiberwiseClosestCodeword 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := (⟨i, by omega⟩ : Fin r)) (destIdx := destIdx) (steps := steps)
      h_destIdx h_destIdx_le f_i with
    ⟨g, hg_mem, hg_min⟩
  have hdist_le_fiber :
      Δ₀((⋈|preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le f_i),
        interleavedCodeSet (C := C_dest)) ≤
      fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := ⟨i, by omega⟩) (destIdx := destIdx) (steps := steps)
        h_destIdx h_destIdx_le f_i := by
    simpa [C_dest] using
      preTensorCombine_distFromInterleavedCode_le_fiberwiseDistance_of_closest 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := i) (steps := steps) (destIdx := destIdx)
        h_destIdx h_destIdx_le f_i ⟨g, hg_mem⟩ hg_min
  have hfiber_le_udr :
      fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := ⟨i, by omega⟩) (destIdx := destIdx) (steps := steps)
        h_destIdx h_destIdx_le f_i ≤
      Code.uniqueDecodingRadius (C := C_dest) := by
    simpa [C_dest] using
      fiberwiseDistance_le_uniqueDecodingRadius_of_fiberwiseClose 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := i) (steps := steps) (destIdx := destIdx)
        h_destIdx h_destIdx_le f_i h_close
  have hbound_nat :
      fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := ⟨i, by omega⟩) (destIdx := destIdx) (steps := steps)
        h_destIdx h_destIdx_le f_i ≤
      Code.uniqueDecodingRadius
        (C := (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx :
          Set (sDomain 𝔽q β h_ℓ_add_R_rate destIdx → L))) := by
    simpa [C_dest] using hfiber_le_udr
  have hfiber_le_udr_enat :
      (fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := ⟨i, by omega⟩) (destIdx := destIdx) (steps := steps)
        h_destIdx h_destIdx_le f_i : ℕ∞) ≤
      (Code.uniqueDecodingRadius
        (C := (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx :
          Set (sDomain 𝔽q β h_ℓ_add_R_rate destIdx → L))) : ℕ∞) := by
    exact_mod_cast hbound_nat
  unfold jointProximityNat
  simpa [C_dest] using le_trans hdist_le_fiber hfiber_le_udr_enat

end
end Binius.BinaryBasefold

end PreTensorDistance

section PreTensorWitness

/-!
## Pre-tensor proximity witness

An explicit nearby interleaved codeword witnesses the proximity bound in Lemma 4.22.
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

set_option maxHeartbeats 1600000 in
/-- Fiberwise closeness gives an explicit interleaved codeword within the destination UDR. -/
lemma preTensorCombine_exists_close_interleavedCodeword_of_fiberwiseClose
    (i : Fin ℓ) (steps : ℕ) [NeZero steps] {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (h_close : fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨i, by omega⟩) (steps := steps) (h_destIdx := by
        simpa using h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f_i)) :
    let C_dest : Set (sDomain 𝔽q β h_ℓ_add_R_rate destIdx → L) :=
      BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx
    ∃ (v : Code.InterleavedCodeword L (Fin (2 ^ steps))
        (sDomain 𝔽q β h_ℓ_add_R_rate destIdx) C_dest),
      let u_interleaved : Code.InterleavedWord L (Fin (2 ^ steps))
          (sDomain 𝔽q β h_ℓ_add_R_rate destIdx) :=
        ⋈|preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le f_i
      Δ₀(u_interleaved, v.val) ≤
        Code.uniqueDecodingRadius (C := C_dest) := by
  classical
  let C_dest : Set (sDomain 𝔽q β h_ℓ_add_R_rate destIdx → L) :=
    BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx
  rcases exists_fiberwiseClosestCodeword 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := (⟨i, by omega⟩ : Fin r)) (destIdx := destIdx) (steps := steps)
      h_destIdx h_destIdx_le f_i with
    ⟨g, hg_mem, hg_min⟩
  have hg_interleaved :
      (⋈|preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le g) ∈
        interleavedCodeSet (C := C_dest) := by
    simpa [C_dest] using
      preTensorCombine_is_interleavedCodeword_of_codeword 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := i) (steps := steps) (destIdx := destIdx)
        h_destIdx h_destIdx_le ⟨g, hg_mem⟩
  have hdist_le_fiber :
      Δ₀((⋈|preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le f_i),
        (⋈|preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le g)) ≤
      fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := ⟨i, by omega⟩) (destIdx := destIdx) (steps := steps)
        h_destIdx h_destIdx_le f_i :=
    preTensorCombine_hamming_le_fiberwiseDistance_of_closest 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := i) (steps := steps) (destIdx := destIdx)
      h_destIdx h_destIdx_le f_i g hg_min
  have hfiber_le_udr :
      fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := ⟨i, by omega⟩) (destIdx := destIdx) (steps := steps)
        h_destIdx h_destIdx_le f_i ≤
      Code.uniqueDecodingRadius (C := C_dest) := by
    simpa [C_dest] using
      fiberwiseDistance_le_uniqueDecodingRadius_of_fiberwiseClose 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := i) (steps := steps) (destIdx := destIdx)
        h_destIdx h_destIdx_le f_i h_close
  refine ⟨⟨(⋈|preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le g),
    hg_interleaved⟩, ?_⟩
  exact le_trans hdist_le_fiber hfiber_le_udr

end

end Binius.BinaryBasefold

end PreTensorWitness
