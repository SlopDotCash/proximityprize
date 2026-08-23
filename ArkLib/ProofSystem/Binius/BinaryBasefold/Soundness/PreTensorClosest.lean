/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.PreTensorUDR

/-!
## Pre-tensor closest-codeword distance

This file packages the Hamming-to-fiberwise-distance step for a chosen fiberwise-closest source
codeword.
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
