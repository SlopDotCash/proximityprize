/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.Incremental

/-!
# Issue #317: preTensorCombine residuals retired

The former `PreTensorCombineMultilinearResidual` and
`FoldPreTensorCombineAffineSplitResidual` typeclass surfaces have been removed from the active
Binius API.  Their mathematical content is now provided directly by the residual-free theorems
in `Soundness.Incremental`:

* `iterated_fold_eq_multilinearCombine_preTensorCombine`
* `fold_preTensorCombine_eq_affineLineEvaluation_split`

This module keeps short issue-oriented wrapper names for downstream imports that still route
through `Soundness.PreTensorMultilinear`.
-/

namespace Binius.BinaryBasefold

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
variable [SampleableType L]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 : ℕ} [NeZero ℓ] [NeZero 𝓡]
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r}

noncomputable section

/-- Issue #317 wrapper: `iterated_fold` is the multilinear combination of the rows of its
`preTensorCombine_WordStack`. -/
theorem iterated_fold_eq_multilinearCombine_preTensorCombine_proven
    (i : Fin ℓ) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (r_chal : Fin steps → L) :
    iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ steps
      (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f_i)
      (r_challenges := r_chal) =
    multilinearCombine (F := L)
      (preTensorCombine_WordStack 𝔽q β i steps h_destIdx h_destIdx_le f_i) r_chal :=
  iterated_fold_eq_multilinearCombine_preTensorCombine 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps h_destIdx h_destIdx_le f_i r_chal

/-- Issue #317 wrapper: one fold step on `preTensorCombine` is affine line evaluation on the
even/odd row split. -/
theorem fold_preTensorCombine_affineSplit_proven
    (i : Fin ℓ) (steps : ℕ) [NeZero steps] {midIdx destIdx : Fin r}
    (h_midIdx : midIdx.val = i.val + 1)
    (h_destIdx : destIdx.val = i.val + (steps + 1))
    (h_destIdx_le : destIdx ≤ ℓ)
    (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (r_new : L) :
    let h_midIdx_lt_ℓ : midIdx.val < ℓ := by
      have := NeZero.pos steps; omega
    let U := preTensorCombine_WordStack (r := r) (L := L) (ℓ := ℓ) (𝓡 := 𝓡)
      𝔽q β i (steps + 1)
      (destIdx := destIdx) (h_destIdx := h_destIdx)
      (h_destIdx_le := h_destIdx_le) f_i
    let U_even := (splitEvenOddRowWiseInterleavedWords (ϑ := steps) U).1
    let U_odd := (splitEvenOddRowWiseInterleavedWords (ϑ := steps) U).2
    let fold_1_f := fold (r := r) (L := L) (ℓ := ℓ) (𝓡 := 𝓡)
      𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ⟨i, by omega⟩ (destIdx := midIdx) (h_destIdx := h_midIdx)
      (h_destIdx_le := by omega) f_i r_new
    let midIdx_fin_ℓ : Fin ℓ := ⟨midIdx.val, h_midIdx_lt_ℓ⟩
    let V := preTensorCombine_WordStack (r := r) (L := L) (ℓ := ℓ) (𝓡 := 𝓡)
      𝔽q β midIdx_fin_ℓ steps
      (destIdx := destIdx)
      (h_destIdx := by simp [midIdx_fin_ℓ]; omega)
      (h_destIdx_le := h_destIdx_le) (by exact fold_1_f)
    V = affineLineEvaluation (F := L) U_even U_odd r_new :=
  fold_preTensorCombine_eq_affineLineEvaluation_split 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := i) (steps := steps) (midIdx := midIdx) (destIdx := destIdx)
    h_midIdx h_destIdx h_destIdx_le f_i r_new

end

end Binius.BinaryBasefold
