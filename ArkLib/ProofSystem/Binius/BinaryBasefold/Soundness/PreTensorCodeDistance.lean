/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.PreTensorClosest

/-!
## Pre-tensor distance to the destination interleaved code

This file packages the step from a chosen closest source codeword to the distance from the
pre-tensor stack to the destination interleaved code.
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
