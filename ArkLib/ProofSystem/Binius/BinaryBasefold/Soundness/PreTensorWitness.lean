/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.PreTensorClosest

/-!
## Pre-tensor proximity witness

This file builds the explicit nearby interleaved codeword used by Lemma 4.22. The final
`jointProximityNat` theorem is kept in `PreTensorDistance`.
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
