/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.Code

/-!
## Binary Basefold compliance compatibility

The main compliance and full folding-bad-event predicates live in `Prelude`/`Basic`.  This file
keeps the incremental bad-event surface used by the folded-step and soundness development.
-/

namespace Binius.BinaryBasefold

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
  Binius.BinaryBasefold
open scoped NNReal
open Function
open Finset AdditiveNTT Polynomial MvPolynomial Nat Matrix
open Code ReedSolomon BerlekampWelch ProbabilityTheory

noncomputable section SoundnessTools

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ]
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r}

/-- Incremental folding bad event for a partially consumed block.

At `k = 0` no folding challenge has been consumed, so the event is false. At `k = ϑ` this is the
canonical full `foldingBadEvent`. Intermediate prefixes are retained as a named predicate surface
for the current soundness plumbing. -/
def incrementalFoldingBadEvent
    (block_start_idx : Fin r) (k : ℕ) (h_k_le : k ≤ ϑ)
    {midIdx destIdx : Fin r}
    (h_midIdx : midIdx.val = block_start_idx.val + k)
    (h_destIdx : destIdx.val = block_start_idx.val + ϑ)
    (h_destIdx_le : destIdx.val ≤ ℓ)
    (f_block_start : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ⟨block_start_idx.val, by
        have hϑ_pos : 0 < ϑ := pos_of_neZero ϑ
        have hblock_lt : block_start_idx.val < ℓ := by omega
        exact Nat.lt_succ_of_lt hblock_lt⟩)
    (r_challenges : Fin k → L) : Prop :=
  if h_zero : k = 0 then
    False
  else if h_full : k = ϑ then
    foldingBadEvent 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨block_start_idx.val, by
        have hϑ_pos : 0 < ϑ := pos_of_neZero ϑ
        omega⟩) (steps := ϑ)
      (h_i_add_steps := by
        have h : block_start_idx.val + ϑ ≤ ℓ := by
          simpa [h_destIdx] using h_destIdx_le
        simpa using h)
      (f_i := f_block_start)
      (challenges := fun j => r_challenges ⟨j.val, by omega⟩)
  else
    True

/-- With no consumed folding challenge, the incremental bad event is false. -/
lemma incrementalFoldingBadEvent_of_k_eq_0_is_false
    (block_start_idx : Fin r) {midIdx destIdx : Fin r}
    (h_midIdx : midIdx.val = block_start_idx.val)
    (h_destIdx : destIdx.val = block_start_idx.val + ϑ)
    (h_destIdx_le : destIdx.val ≤ ℓ)
    (f_block_start : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ⟨block_start_idx.val, by
        have hϑ_pos : 0 < ϑ := pos_of_neZero ϑ
        have hblock_lt : block_start_idx.val < ℓ := by omega
        exact Nat.lt_succ_of_lt hblock_lt⟩)
    (r_challenges : Fin 0 → L) :
    ¬ incrementalFoldingBadEvent 𝔽q β (block_start_idx := block_start_idx) (ϑ := ϑ)
      (k := 0) (h_k_le := Nat.zero_le ϑ) (midIdx := midIdx) (destIdx := destIdx)
      (h_midIdx := h_midIdx) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
      (f_block_start := f_block_start) (r_challenges := r_challenges) := by
  simp [incrementalFoldingBadEvent]

/-- At the end of a block, the incremental event is the full folding bad event. -/
lemma incrementalFoldingBadEvent_eq_foldingBadEvent_of_k_eq_ϑ
    (block_start_idx : Fin r) {midIdx destIdx : Fin r}
    (h_midIdx : midIdx.val = block_start_idx.val + ϑ)
    (h_destIdx : destIdx.val = block_start_idx.val + ϑ)
    (h_destIdx_le : destIdx.val ≤ ℓ)
    (f_block_start : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ⟨block_start_idx.val, by
        have hϑ_pos : 0 < ϑ := pos_of_neZero ϑ
        have hblock_lt : block_start_idx.val < ℓ := by omega
        exact Nat.lt_succ_of_lt hblock_lt⟩)
    (r_challenges : Fin ϑ → L) :
    incrementalFoldingBadEvent 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (block_start_idx := block_start_idx) (k := ϑ) (h_k_le := le_rfl)
      (midIdx := midIdx) (destIdx := destIdx) (h_midIdx := h_midIdx)
      (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
      (f_block_start := f_block_start) (r_challenges := r_challenges) =
    foldingBadEvent 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨block_start_idx.val, by
        have hϑ_pos : 0 < ϑ := pos_of_neZero ϑ
        omega⟩) (steps := ϑ)
      (h_i_add_steps := by
        have h : block_start_idx.val + ϑ ≤ ℓ := by
          simpa [h_destIdx] using h_destIdx_le
        simpa using h)
      (f_i := f_block_start) (challenges := r_challenges) := by
  simp [incrementalFoldingBadEvent, NeZero.ne ϑ]

end SoundnessTools

end Binius.BinaryBasefold
