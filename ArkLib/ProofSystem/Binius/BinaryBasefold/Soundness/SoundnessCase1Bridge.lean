/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.FoldDetDischarge
import ArkLib.ProofSystem.Binius.BinaryBasefold.Code

/-!
# Proposition 4.21 Case 1: fold-difference matrix bridge

Bridges the per-point fold collision event of the Case-1 (fiberwise-close) residual to the
linear-algebra layer:

* `foldDiff_eq_dotProduct_mulVec`: the difference of two iterated folds at a point `y` is the
  challenge tensor dotted with `foldMatrix y *ᵥ (fiber evaluations difference)` — assembled from
  `single_point_localized_fold_matrix_form_eq_iterated_fold` applied to each fold plus
  `Matrix.mulVec_sub`/`dotProduct_sub` linearity.
* `foldDiff_coeff_ne_zero`: when some fiber evaluation of `f` and `g` over `y` differs (the
  membership condition of `fiberwiseDisagreementSetPerFiber`), the coefficient vector
  `foldMatrix y *ᵥ (fiberEvaluations f y - fiberEvaluations g y)` is nonzero — via
  `foldMatrix_det_ne_zero` and `Matrix.eq_zero_of_mulVec_eq_zero`.
* `foldDiff_zero_iff`: the fold collision `iterated_fold f y = iterated_fold g y` is equivalent
  to the vanishing of the challenge-tensor dot product against that coefficient vector.

These are exactly the per-point inputs the tensor Schwartz–Zippel step of
`Prop421Case1FiberwiseCloseResidual` needs.
-/

set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false

namespace Binius.BinaryBasefold

open AdditiveNTT Matrix

noncomputable section

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 : ℕ} [NeZero ℓ] [NeZero 𝓡]
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r}

/-- **Fold-difference matrix form.** The pointwise difference of two iterated folds equals the
challenge tensor dotted with `foldMatrix y` applied to the difference of fiber evaluations. -/
lemma foldDiff_eq_dotProduct_mulVec (i : Fin r) {destIdx : Fin r} (steps : ℕ)
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (h_i_lt : i.val < ℓ)
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    (r_challenges : Fin steps → L)
    (y : (sDomain 𝔽q β h_ℓ_add_R_rate) destIdx) :
    iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps)
        (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f)
        (r_challenges := r_challenges) y
      - iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps)
        (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := g)
        (r_challenges := r_challenges) y
    = dotProduct
        (fun idx => (challengeTensorProduct (L := L) (ℓ := ℓ) (𝓡 := 𝓡) (r := r)
          steps r_challenges).get idx)
        (Matrix.mulVec
          (foldMatrix 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps)
            h_destIdx h_destIdx_le y)
          (fiberEvaluations 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps)
              (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f) (y := y)
            - fiberEvaluations 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps)
              (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := g) (y := y))) := by
  rw [← single_point_localized_fold_matrix_form_eq_iterated_fold 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps h_destIdx h_destIdx_le h_i_lt
        f r_challenges y,
      ← single_point_localized_fold_matrix_form_eq_iterated_fold 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps h_destIdx h_destIdx_le h_i_lt
        g r_challenges y]
  simp only [single_point_localized_fold_matrix_form]
  rw [Matrix.mulVec_sub, dotProduct_sub]

/-- **Nonvanishing coefficient vector.** If the fiber evaluations of `f` and `g` over `y`
disagree at some index (i.e. `y ∈ fiberwiseDisagreementSetPerFiber … f g`), then
`foldMatrix y *ᵥ (fiberEvaluations f y - fiberEvaluations g y) ≠ 0`, because the fold matrix is
nonsingular (`foldMatrix_det_ne_zero`). -/
lemma foldDiff_coeff_ne_zero (i : Fin r) {destIdx : Fin r} (steps : ℕ)
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    (y : (sDomain 𝔽q β h_ℓ_add_R_rate) destIdx)
    (h_ne : ∃ idx : Fin (2 ^ steps),
      fiberEvaluations 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps)
          (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f) (y := y) idx ≠
        fiberEvaluations 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps)
          (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := g) (y := y) idx) :
    Matrix.mulVec
        (foldMatrix 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps)
          h_destIdx h_destIdx_le y)
        (fiberEvaluations 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps)
            (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f) (y := y)
          - fiberEvaluations 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps)
            (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := g) (y := y)) ≠ 0 := by
  have hdet := foldMatrix_det_ne_zero 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := i) (steps := steps) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (y := y)
  intro hc
  have hv := Matrix.eq_zero_of_mulVec_eq_zero hdet hc
  rcases h_ne with ⟨idx, hidx⟩
  apply hidx
  have hcoord := congrFun hv idx
  simp only [Pi.sub_apply, Pi.zero_apply] at hcoord
  exact sub_eq_zero.mp hcoord

/-- **Per-point collision criterion.** The two iterated folds collide at `y` exactly when the
challenge tensor annihilates the (matrix-transformed) fiber-evaluation difference. -/
lemma foldDiff_zero_iff (i : Fin r) {destIdx : Fin r} (steps : ℕ)
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (h_i_lt : i.val < ℓ)
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    (r_challenges : Fin steps → L)
    (y : (sDomain 𝔽q β h_ℓ_add_R_rate) destIdx) :
    iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps)
        (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f)
        (r_challenges := r_challenges) y
      = iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps)
        (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := g)
        (r_challenges := r_challenges) y
    ↔ dotProduct
        (fun idx => (challengeTensorProduct (L := L) (ℓ := ℓ) (𝓡 := 𝓡) (r := r)
          steps r_challenges).get idx)
        (Matrix.mulVec
          (foldMatrix 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps)
            h_destIdx h_destIdx_le y)
          (fiberEvaluations 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps)
              (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f) (y := y)
            - fiberEvaluations 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps)
              (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := g) (y := y))) = 0 := by
  rw [← foldDiff_eq_dotProduct_mulVec 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        i steps h_destIdx h_destIdx_le h_i_lt f g r_challenges y,
      sub_eq_zero]

end

end Binius.BinaryBasefold
