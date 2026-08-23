/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.PreTensorFiber

/-!
## Pre-tensor column disagreements

This file isolates the finite-set bridge used in Lemma 4.22: if two pre-tensor stacks disagree in
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
