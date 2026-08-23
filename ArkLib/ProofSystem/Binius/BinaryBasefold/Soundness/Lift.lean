/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.Data.CodingTheory.InterleavedCode
import ArkLib.ProofSystem.Binius.BinaryBasefold.Code
import ArkLib.ProofSystem.Binius.BinaryBasefold.BitsOfIndex

/-!
## Binary Basefold Soundness Lift

This file provides local lift utilities consumed by the split Binary Basefold soundness files.
The constructions below keep the API total by extracting polynomial representatives from proven
BBF codewords and by packaging interleaved rows through the existing `InterleavedCode` interface.
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

private lemma getBit_eq_testBit (n k : ℕ) :
    Nat.getBit k n = 1 ↔ n.testBit k = true := by
  unfold Nat.getBit Nat.testBit
  have hcomm : n >>> k &&& 1 = 1 &&& n >>> k := Nat.land_comm _ _
  rw [hcomm]
  generalize hb : 1 &&& n >>> k = b
  have hb_lt : b < 2 := by
    rw [← hb, Nat.and_comm, Nat.and_one_is_mod]
    exact Nat.mod_lt _ (by norm_num)
  interval_cases b <;> simp

private lemma getBit_eq_zero_of_lt_two_pow {a n k : ℕ} (ha : a < 2 ^ n) (hnk : n ≤ k) :
    Nat.getBit k a = 0 := by
  unfold Nat.getBit
  rw [Nat.shiftRight_eq_div_pow]
  have ha' : a < 2 ^ k := by
    exact lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) hnk)
  rw [Nat.div_eq_of_lt ha']
  simp

private lemma exists_fin_getBit_ne_of_ne {n : ℕ} (j k : Fin (2 ^ n)) (hjk : j ≠ k) :
    ∃ b : Fin n, Nat.getBit b.val j.val ≠ Nat.getBit b.val k.val := by
  by_contra h
  push_neg at h
  have h_all : ∀ b : ℕ, Nat.getBit b j.val = Nat.getBit b k.val := by
    intro b
    by_cases hb : b < n
    · exact h ⟨b, hb⟩
    · have hnb : n ≤ b := by omega
      rw [getBit_eq_zero_of_lt_two_pow j.isLt hnb,
        getBit_eq_zero_of_lt_two_pow k.isLt hnb]
  have h_val : j.val = k.val := by
    apply Nat.eq_iff_eq_all_getBits.mpr
    intro b
    simpa [Nat.getBit] using h_all b
  exact hjk (Fin.ext h_val)

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] [NeZero 𝓡] in
lemma multilinearWeight_bitsOfIndex_eq_indicator {n : ℕ} (j k : Fin (2 ^ n)) :
    multilinearWeight (F := L) (bitsOfIndex (L := L) k) j =
      if j = k then 1 else 0 := by
  by_cases hjk : j = k
  · subst j
    simp only [↓reduceIte]
    unfold multilinearWeight bitsOfIndex
    refine Finset.prod_eq_one ?_
    intro b _
    by_cases hbit : Nat.getBit b.val k.val = 1
    · have htest : k.val.testBit b.val = true := (getBit_eq_testBit k.val b.val).mp hbit
      simp [hbit, htest]
    · have htest : k.val.testBit b.val = false := by
        cases h : k.val.testBit b.val
        · rfl
        · exact (hbit ((getBit_eq_testBit k.val b.val).mpr h)).elim
      simp [hbit, htest]
  · simp only [hjk, ↓reduceIte]
    obtain ⟨b, hb_ne⟩ := exists_fin_getBit_ne_of_ne j k hjk
    unfold multilinearWeight bitsOfIndex
    rw [Finset.prod_eq_zero_iff]
    refine ⟨b, Finset.mem_univ b, ?_⟩
    by_cases htest : j.val.testBit b.val = true
    · have hj_bit : Nat.getBit b.val j.val = 1 := (getBit_eq_testBit j.val b.val).mpr htest
      have hk_not_one : Nat.getBit b.val k.val ≠ 1 := by
        intro hk_bit
        exact hb_ne (hj_bit.trans hk_bit.symm)
      simp [htest, hk_not_one]
    · have hj_not_one : Nat.getBit b.val j.val ≠ 1 := by
        intro hj_bit
        exact htest ((getBit_eq_testBit j.val b.val).mp hj_bit)
      have hj_zero : Nat.getBit b.val j.val = 0 := by
        rcases Nat.getBit_eq_zero_or_one (k := b.val) (n := j.val) with h | h
        · exact h
        · exact (hj_not_one h).elim
      have hk_one : Nat.getBit b.val k.val = 1 := by
        rcases Nat.getBit_eq_zero_or_one (k := b.val) (n := k.val) with h | h
        · exact (hb_ne (hj_zero.trans h.symm)).elim
        · exact h
      simp [htest, hk_one]

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] [NeZero 𝓡] in
lemma challengeTensorExpansion_bitsOfIndex_is_eq_indicator {n : ℕ} (k : Fin (2 ^ n)) :
    challengeTensorExpansion (L := L) n (bitsOfIndex (L := L) k) =
      fun j => if j = k then 1 else 0 := by
  funext j
  exact multilinearWeight_bitsOfIndex_eq_indicator (L := L) j k

section Lift_PreTensorCombine

/-- Interleaved word-stack obtained by folding with binary row challenges. -/
def preTensorCombine_WordStack (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩) :
    WordStack (A := L) (κ := Fin (2 ^ steps))
      (ι := sDomain 𝔽q β h_ℓ_add_R_rate destIdx) :=
  fun rowIdx =>
    iterated_fold 𝔽q β ⟨i, by omega⟩ steps
      (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f_i)
      (r_challenges := bitsOfIndex (L := L) rowIdx)

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] in
lemma preTensorCombine_row_eq_fold_with_binary_row_challenges
    (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (rowIdx : Fin (2 ^ steps)) :
    ∀ y : sDomain 𝔽q β h_ℓ_add_R_rate destIdx,
      (preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le f) rowIdx y =
      iterated_fold 𝔽q β ⟨i, by omega⟩ steps
        (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f)
        (r_challenges := bitsOfIndex (L := L) rowIdx) y := by
  intro y
  rfl

private lemma iterated_fold_of_BBF_Code_mem (i : Fin ℓ) (steps : ℕ)
    {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f : BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (r_challenges : Fin steps → L) :
    iterated_fold 𝔽q β ⟨i, by omega⟩ steps
      (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f)
      (r_challenges := r_challenges) ∈
      (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx) := by
  let srcIdx : Fin r := ⟨i.val, by omega⟩
  let stepsIdx : Fin (ℓ + 1) := ⟨steps, by
    have hle : i.val + steps ≤ ℓ := by
      rw [← h_destIdx]
      exact h_destIdx_le
    omega⟩
  have h_i_add_steps : srcIdx.val + stepsIdx.val < ℓ + 𝓡 := by
    have hle : srcIdx.val + stepsIdx.val ≤ ℓ := by
      simp only [srcIdx, stepsIdx]
      rw [← h_destIdx]
      exact h_destIdx_le
    exact Nat.lt_of_le_of_lt hle (Nat.lt_add_of_pos_right (Nat.pos_of_neZero 𝓡))
  have h_destIdx_eq :
      destIdx = ⟨srcIdx.val + stepsIdx.val,
        Nat.lt_trans h_i_add_steps h_ℓ_add_R_rate⟩ := by
    apply Fin.ext
    simp [srcIdx, stepsIdx, h_destIdx]
  simpa [srcIdx, stepsIdx] using
    iterated_fold_preserves_BBF_Code_membership 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := srcIdx) (destIdx := destIdx) (steps := stepsIdx)
      (h_i_add_steps := h_i_add_steps) (h_destIdx := h_destIdx_eq)
      (h_destIdx_le := h_destIdx_le) (f := f) (r_challenges := r_challenges)

theorem preTensorCombine_is_interleavedCodeword_of_codeword (i : Fin ℓ) (steps : ℕ)
    {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f : BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩) :
    (⋈|(preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le
      (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩))) ∈
      (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx ^⋈ (Fin (2 ^ steps))) := by
  change (⋈|preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le
      (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)) ∈
    Code.interleavedCodeSet
      (C := (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx :
        Set (sDomain 𝔽q β h_ℓ_add_R_rate destIdx → L)))
  rw [Code.mem_interleavedCode_iff]
  intro rowIdx
  simpa [preTensorCombine_WordStack, Code.InterleavedWord.getRowWord,
    Code.interleaveWordStack] using
    iterated_fold_of_BBF_Code_mem 𝔽q β i steps h_destIdx h_destIdx_le f
      (bitsOfIndex (L := L) rowIdx)

/-- The `rowIdx`-th row of an input interleaved BBF codeword, as a BBF codeword. -/
def inputRowCodeword (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (V_codeword : ((BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx)
      ^⋈ (Fin (2 ^ steps)))) (rowIdx : Fin (2 ^ steps)) :
    BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx :=
  ⟨Code.InterleavedWord.getRowWord V_codeword.val rowIdx, by
    exact V_codeword.property rowIdx⟩

/-- Polynomial representative of an input interleaved row. -/
def getInputRowPoly (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (V_codeword : ((BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx)
      ^⋈ (Fin (2 ^ steps)))) (rowIdx : Fin (2 ^ steps)) :
    L⦃< 2 ^ (ℓ - destIdx.val)⦄[X] :=
  getBBF_Codeword_poly 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx
    (inputRowCodeword 𝔽q β i steps h_destIdx h_destIdx_le V_codeword rowIdx)

lemma inputRowCodeword_eq_polyToOracleFunc (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (V_codeword : ((BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx)
      ^⋈ (Fin (2 ^ steps)))) (rowIdx : Fin (2 ^ steps)) :
    (inputRowCodeword 𝔽q β i steps h_destIdx h_destIdx_le V_codeword rowIdx :
      OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx) =
    polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (domainIdx := destIdx)
      (getInputRowPoly 𝔽q β i steps h_destIdx h_destIdx_le V_codeword rowIdx) := by
  simpa [getInputRowPoly] using
    getBBF_Codeword_poly_spec 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx
      (inputRowCodeword 𝔽q β i steps h_destIdx h_destIdx_le V_codeword rowIdx)

/-- Coefficients of the source-level lift polynomial, packed row-major from input row polynomials. -/
def getLiftCoeffs (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (V_codeword : ((BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx)
      ^⋈ (Fin (2 ^ steps)))) :
    Fin (2 ^ (ℓ - i.val)) → L :=
  fun coeffIdx =>
    let rowIdx : Fin (2 ^ steps) :=
      ⟨coeffIdx.val % 2 ^ steps, Nat.mod_lt _ (Nat.two_pow_pos steps)⟩
    let rowCoeffIdx : Fin (2 ^ (ℓ - destIdx.val)) := ⟨coeffIdx.val / 2 ^ steps, by
      have h_exp : ℓ - i.val = steps + (ℓ - destIdx.val) := by omega
      have h_factor : 2 ^ (ℓ - i.val) = 2 ^ steps * 2 ^ (ℓ - destIdx.val) := by
        rw [h_exp, pow_add]
      have hlt : coeffIdx.val < 2 ^ steps * 2 ^ (ℓ - destIdx.val) := by
        simpa [h_factor] using coeffIdx.isLt
      exact Nat.div_lt_of_lt_mul hlt⟩
    ((getInputRowPoly 𝔽q β i steps h_destIdx h_destIdx_le V_codeword rowIdx).val).coeff
      rowCoeffIdx.val

/-- Source-level polynomial obtained from the packed row coefficients. -/
def getLiftPoly (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (V_codeword : ((BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx)
      ^⋈ (Fin (2 ^ steps)))) :
    L⦃< 2 ^ (ℓ - i.val)⦄[X] :=
  (Polynomial.degreeLTEquiv L (2 ^ (ℓ - i.val))).symm
    (getLiftCoeffs 𝔽q β i steps h_destIdx h_destIdx_le V_codeword)

/-- The source-level BBF codeword determined by the packed lift polynomial. -/
def lift_interleavedCodeword (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (V_codeword : ((BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx)
      ^⋈ (Fin (2 ^ steps)))) :
    BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ⟨i, by omega⟩ :=
  getBBF_Codeword_of_poly 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := ⟨i, by omega⟩)
    (h_i := by exact Nat.le_of_lt i.isLt)
    (P := getLiftPoly 𝔽q β i steps h_destIdx h_destIdx_le V_codeword)

/-- The `j`-th folded row of the lifted codeword, bundled as a destination BBF codeword. -/
def foldedLiftRowCodeword (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (V_codeword : ((BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx)
      ^⋈ (Fin (2 ^ steps)))) (j : Fin (2 ^ steps)) :
    BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx :=
  ⟨iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ steps
      (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
      (f := (lift_interleavedCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        i steps h_destIdx h_destIdx_le V_codeword :
        OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩))
      (r_challenges := bitsOfIndex (L := L) j),
    iterated_fold_of_BBF_Code_mem 𝔽q β i steps h_destIdx h_destIdx_le
      (lift_interleavedCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        i steps h_destIdx h_destIdx_le V_codeword)
      (bitsOfIndex (L := L) j)⟩

/-- Polynomial representative of a folded row of the lifted codeword. -/
def getRowPoly (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (V_codeword : ((BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx)
      ^⋈ (Fin (2 ^ steps)))) (rowIdx : Fin (2 ^ steps)) :
    L⦃< 2 ^ (ℓ - destIdx.val)⦄[X] :=
  getBBF_Codeword_poly 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx
    (foldedLiftRowCodeword 𝔽q β i steps h_destIdx h_destIdx_le V_codeword rowIdx)

theorem folded_lifted_IC_eq_IC_row_polyToOracleFunc (i : Fin ℓ) (steps : ℕ)
    {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (V_codeword : ((BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx)
      ^⋈ (Fin (2 ^ steps)))) (j : Fin (2 ^ steps)) :
    let g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ :=
      lift_interleavedCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        i steps h_destIdx h_destIdx_le V_codeword
    let P_j := getRowPoly 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps
      h_destIdx h_destIdx_le V_codeword j
    iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ steps
      (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) g
      (bitsOfIndex (L := L) j) =
    polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (domainIdx := destIdx) P_j := by
  dsimp only
  change
    (foldedLiftRowCodeword 𝔽q β i steps h_destIdx h_destIdx_le V_codeword j :
      OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx) =
    polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (domainIdx := destIdx)
      (getBBF_Codeword_poly 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx
        (foldedLiftRowCodeword 𝔽q β i steps h_destIdx h_destIdx_le V_codeword j))
  exact getBBF_Codeword_poly_spec 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx
    (foldedLiftRowCodeword 𝔽q β i steps h_destIdx h_destIdx_le V_codeword j)

def fiberDiff (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate destIdx) : Prop :=
  y ∈ fiberwiseDisagreementSet 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := ⟨i, by omega⟩) (steps := steps) h_destIdx h_destIdx_le f g

lemma fiberwise_disagreement_isomorphism (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩) :
    ∀ y : sDomain 𝔽q β h_ℓ_add_R_rate destIdx,
      fiberDiff 𝔽q β i steps h_destIdx h_destIdx_le f g y ↔
        y ∈ fiberwiseDisagreementSet 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := ⟨i, by omega⟩) (steps := steps) h_destIdx h_destIdx_le f g := by
  intro y
  rfl

lemma lemma_4_21_interleaved_word_UDR_far (i : Fin ℓ) (steps : ℕ)
    {destIdx : Fin r} (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (e : ℕ)
    (h_far :
      e <
        Δ₀((⋈|preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le f_i),
          interleavedCodeSet
            (C := (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx :
              Set (sDomain 𝔽q β h_ℓ_add_R_rate destIdx → L))))) :
    ¬ jointProximityNat
      (C := (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx :
        Set (sDomain 𝔽q β h_ℓ_add_R_rate destIdx → L)))
      (u := preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le f_i) e := by
  intro h_close
  unfold jointProximityNat at h_close
  exact not_lt_of_ge h_close h_far

end Lift_PreTensorCombine
end
end Binius.BinaryBasefold
