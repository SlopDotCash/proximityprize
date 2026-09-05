/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors, Chung Thai Nguyen, Quang Dao
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.FoldDetDischarge
import ArkLib.ProofSystem.Binius.BinaryBasefold.Code
import ArkLib.Data.Probability.TensorSchwartzZippel
import ArkLib.Data.Probability.PrUnionBound
import ArkLib.Data.CodingTheory.ProximityGap.DG25
import ArkLib.ProofSystem.Binius.BinaryBasefold.Compliance
import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.Lift

/-!
# Binary Basefold first-case soundness

The deterministic first-case bridge, its probability bounds, and the conditional soundness proposition.
-/

section SoundnessCase1Bridge

/-!
## Deterministic first-case soundness bridge.
-/

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

end SoundnessCase1Bridge

section SoundnessCase1Discharge

/-!
## Probability bounds for the first soundness case.
-/

/-!
# Proposition 4.21 Case 1 probability bound

DP24 Proposition 4.21, Case 1 (fiberwise-close branch), proven: for every point `y` of the
honest per-fiber disagreement set, the difference of the two iterated folds at `y` is the
challenge tensor dotted with `foldMatrix y *ᵥ Δv` (`foldDiff_eq_dotProduct_mulVec`); the fold
matrix is nonsingular (`foldMatrix_det_ne_zero`), so the coefficient vector is nonzero and the
tensor polynomial `TensorSZ.tensorComb` is a nonzero multilinear polynomial of total degree at
most `steps`; Schwartz–Zippel (`TensorSZ.tensorComb_vanish_prob_le`) bounds the per-point
collision probability by `steps / |L|`, and the finset union bound
(`PrUnion.Pr_finset_exists_le_card_mul`) over `Δ ⊆ S^{(i+steps)}` gives
`steps · |S^{(i+steps)}| / |L|`.

The connection between the Binius `challengeTensorProduct` and the generic `TensorSZ`
tensor-basis polynomials is the entrywise identity
`challengeTensorProduct_get_eq_tensorWeight_eval`, proven by induction along the named
`ctpAux` recursion: both place the LAST challenge/variable on the LOW bit of the index.
-/

set_option linter.unusedSectionVars false

namespace Binius.BinaryBasefold

open AdditiveNTT Matrix MvPolynomial Finset
open scoped NNReal
open ProbabilityTheory

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

/-!
## The tensor connection: `challengeTensorProduct` entries are `TensorSZ.tensorWeight` values
-/

/-- Entries of the named tensor recursion `ctpAux` are evaluations of the generic
`TensorSZ.tensorWeight` basis polynomials (both use low-bit ↔ last-challenge orientation). -/
lemma ctpAux_get_eq_tensorWeight_eval (m : ℕ) (rc : Fin m → L) :
    ∀ (k : ℕ) (hk : k ≤ m) (idx : Fin (2 ^ k)),
      (ctpAux (ℓ := ℓ) (𝓡 := 𝓡) (r := r) m rc k hk).get idx
        = MvPolynomial.eval (fun j : Fin k => rc ⟨j.val, lt_of_lt_of_le j.isLt hk⟩)
            (TensorSZ.tensorWeight L k idx) := by
  intro k
  induction k with
  | zero =>
    intro hk idx
    fin_cases idx
    simp [ctpAux, TensorSZ.tensorWeight]
  | succ k ih =>
    intro hk idx
    simp only [ctpAux, Vector.get_ofFn]
    rw [TensorSZ.tensorWeight_eval_succ]
    rw [ih (by omega) ⟨idx.val / 2, TensorSZ.halfLt idx⟩]
    have hcomp :
        ((fun j : Fin (k + 1) => rc ⟨j.val, lt_of_lt_of_le j.isLt hk⟩) ∘ Fin.castSucc)
          = fun j : Fin k => rc ⟨j.val, lt_of_lt_of_le j.isLt (by omega)⟩ := by
      funext j
      rfl
    rw [hcomp]
    simp only [Fin.val_last]
    split_ifs <;> ring

/-- **The tensor connection (entrywise).** For nonzero `m`, the `idx` entry of
`challengeTensorProduct m rc` is the evaluation of the `idx`-th tensor basis polynomial. -/
lemma challengeTensorProduct_get_eq_tensorWeight_eval (m : ℕ) (hm : m ≠ 0)
    (rc : Fin m → L) (idx : Fin (2 ^ m)) :
    (challengeTensorProduct (L := L) (ℓ := ℓ) (𝓡 := 𝓡) (r := r) m rc).get idx
      = MvPolynomial.eval rc (TensorSZ.tensorWeight L m idx) := by
  rw [challengeTensorProduct_eq_ctpAux m hm rc,
    ctpAux_get_eq_tensorWeight_eval m rc m (le_refl m) idx]

/-- **The tensor connection (dot-product level).** Dotting the challenge tensor against a
coefficient vector `a` is evaluating the multilinear polynomial `TensorSZ.tensorComb m a`. -/
lemma dotProduct_challengeTensor_eq_tensorComb_eval (m : ℕ) (hm : m ≠ 0)
    (rc : Fin m → L) (a : Fin (2 ^ m) → L) :
    dotProduct
        (fun idx => (challengeTensorProduct (L := L) (ℓ := ℓ) (𝓡 := 𝓡) (r := r) m rc).get idx)
        a
      = MvPolynomial.eval rc (TensorSZ.tensorComb L m a) := by
  rw [TensorSZ.tensorComb_eval]
  unfold dotProduct
  refine Finset.sum_congr rfl fun idx _ => ?_
  dsimp only
  rw [challengeTensorProduct_get_eq_tensorWeight_eval (hm := hm), mul_comm]

/-!
## Per-point collision probability
-/

/-- **Per-point Schwartz–Zippel bound (DP24 eq. (39)).** If the fiber evaluations of `f` and `g`
over `y` disagree somewhere, the two iterated folds collide at `y` with probability at most
`steps / |L|` over the uniform challenge vector. -/
lemma per_point_fold_collision_prob_le (i : Fin r) {destIdx : Fin r} (steps : ℕ)
    (hsteps : steps ≠ 0)
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (h_i_lt : i.val < ℓ)
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    (y : (sDomain 𝔽q β h_ℓ_add_R_rate) destIdx)
    (h_ne : ∃ idx : Fin (2 ^ steps),
      fiberEvaluations 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps)
          (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f) (y := y) idx ≠
        fiberEvaluations 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps)
          (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := g) (y := y) idx) :
    Pr_{ let rch ←$ᵖ (Fin steps → L) }[
      iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps)
          (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f)
          (r_challenges := rch) y
        = iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps)
          (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := g)
          (r_challenges := rch) y ]
      ≤ (steps : ℝ≥0) / (Fintype.card L : ℝ≥0) := by
  set a : Fin (2 ^ steps) → L :=
    Matrix.mulVec
      (foldMatrix 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps)
        h_destIdx h_destIdx_le y)
      (fiberEvaluations 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps)
          (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f) (y := y)
        - fiberEvaluations 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps)
          (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := g) (y := y))
    with ha_def
  have ha : a ≠ 0 :=
    foldDiff_coeff_ne_zero 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := i) (steps := steps) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
      f g y h_ne
  have hiff : ∀ rch : Fin steps → L,
      (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps)
          (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f)
          (r_challenges := rch) y
        = iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps)
          (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := g)
          (r_challenges := rch) y)
      ↔ MvPolynomial.eval rch (TensorSZ.tensorComb L steps a) = 0 := by
    intro rch
    rw [foldDiff_zero_iff 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := i) (steps := steps) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
      h_i_lt f g rch y]
    rw [← dotProduct_challengeTensor_eq_tensorComb_eval (r := r) (ℓ := ℓ) (𝓡 := 𝓡)
      (m := steps) (hm := hsteps) (rc := rch) (a := a)]
  rw [Pr_congr hiff]
  exact TensorSZ.tensorComb_vanish_prob_le L steps a ha

/-!
## The theorem
-/

open Classical in
/-- **DP24 Proposition 4.21, Case 1 — proven.**
Per-fiber Schwartz–Zippel plus a union bound over the fiberwise disagreement set. -/
lemma prop421Case1_probability_bound
    (i : Fin ℓ) (steps : ℕ) [NeZero steps] {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (h_close : fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨i, by omega⟩) (steps := steps) (h_destIdx := h_destIdx)
      (h_destIdx_le := h_destIdx_le) (f := f_i)) :
    let S_next := sDomain 𝔽q β h_ℓ_add_R_rate destIdx
    let domain_size := Fintype.card S_next
    Pr_{ let r_challenges ←$ᵖ (Fin steps → L) }[
        let f_bar_i := UDRCodeword 𝔽q β (i := ⟨i, by omega⟩) (h_i := by
          exact Nat.le_of_lt i.isLt) f_i
          (UDRClose_of_fiberwiseClose 𝔽q β ⟨i, by omega⟩ steps h_destIdx h_destIdx_le f_i h_close)
        let folded_f_i := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩
          steps h_destIdx h_destIdx_le f_i r_challenges
        let folded_f_bar_i := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩
          steps h_destIdx h_destIdx_le f_bar_i r_challenges
        ¬ (fiberwiseDisagreementSetPerFiber 𝔽q β
            (i := ⟨i, by omega⟩) steps h_destIdx h_destIdx_le f_i f_bar_i ⊆
           disagreementSet 𝔽q β (i := destIdx) (destIdx := destIdx)
             (h_destIdx := rfl) (f := folded_f_i) (g := folded_f_bar_i))
    ] ≤ ((steps * domain_size) / Fintype.card L) := by
    intro S_next domain_size
    -- The closest-codeword comparison word and the (challenge-independent) disagreement set.
    have hU := UDRClose_of_fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ⟨i, by omega⟩ steps h_destIdx h_destIdx_le f_i h_close
    set f_bar : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ :=
      UDRCodeword 𝔽q β (i := ⟨i, by omega⟩) (h_i := by exact Nat.le_of_lt i.isLt) f_i hU
      with hf_bar_def
    set Δ : Finset ((sDomain 𝔽q β h_ℓ_add_R_rate) destIdx) :=
      fiberwiseDisagreementSetPerFiber 𝔽q β (i := ⟨i, by omega⟩) steps
        h_destIdx h_destIdx_le f_i f_bar with hΔ_def
    -- Rewrite the bad event as a finset-existential of per-point fold collisions.
    have hevent : ∀ rch : Fin steps → L,
        (¬ (fiberwiseDisagreementSetPerFiber 𝔽q β
              (i := ⟨i, by omega⟩) steps h_destIdx h_destIdx_le f_i f_bar ⊆
            disagreementSet 𝔽q β (i := destIdx) (destIdx := destIdx)
              (h_destIdx := rfl)
              (f := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩
                steps h_destIdx h_destIdx_le f_i rch)
              (g := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩
                steps h_destIdx h_destIdx_le f_bar rch)))
        ↔ ∃ y ∈ Δ,
            iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩
              steps h_destIdx h_destIdx_le f_i rch y
            = iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩
              steps h_destIdx h_destIdx_le f_bar rch y := by
      intro rch
      rw [Finset.not_subset]
      constructor
      · rintro ⟨y, hyΔ, hynot⟩
        refine ⟨y, hyΔ, ?_⟩
        by_contra hne
        exact hynot (by
          unfold disagreementSet
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, cast_eq]
          exact hne)
      · rintro ⟨y, hyΔ, heq⟩
        refine ⟨y, hyΔ, ?_⟩
        unfold disagreementSet
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, cast_eq, not_not]
        exact heq
    refine le_trans (le_of_eq (Pr_congr hevent)) ?_
    refine le_trans
      (PrUnion.Pr_finset_exists_le_card_mul _ Δ _
        (((steps : ℝ≥0) / (Fintype.card L : ℝ≥0) : ENNReal)) (fun y hy => ?_)) ?_
    · -- per-point Schwartz–Zippel bound
      have h_ne := (mem_fiberwiseDisagreementSetPerFiber 𝔽q β
        (i := ⟨i, by omega⟩) (destIdx := destIdx) steps
        h_destIdx h_destIdx_le f_i f_bar y).mp (hΔ_def ▸ hy)
      exact per_point_fold_collision_prob_le 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := (⟨i, by omega⟩ : Fin r)) (steps := steps)
        (hsteps := Nat.pos_iff_ne_zero.mp (Nat.pos_of_neZero steps))
        (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
        (h_i_lt := i.isLt)
        f_i f_bar y h_ne
    · -- counting + ENNReal algebra: |Δ| · (steps/|L|) ≤ steps · |S_next| / |L|
      have hcard : Δ.card ≤ domain_size := Finset.card_le_univ Δ
      calc (Δ.card : ENNReal) * (((steps : ℝ≥0) / (Fintype.card L : ℝ≥0) : ENNReal))
          ≤ (domain_size : ENNReal) * (((steps : ℝ≥0) / (Fintype.card L : ℝ≥0) : ENNReal)) := by
            gcongr
        _ ≤ ((steps * domain_size) / Fintype.card L) := by
            push_cast
            rw [mul_comm ((domain_size : ℕ) : ENNReal)]
            exact le_of_eq (by rw [div_eq_mul_inv, mul_right_comm, ← div_eq_mul_inv])

end

end Binius.BinaryBasefold

end SoundnessCase1Discharge

section SoundnessProposition

/-!
## Conditional soundness proposition.
-/

/-!
## Binary Basefold Soundness Proposition 4.21

Case analyses and probability bounds around Proposition 4.21 and its supporting lemmas.
This file packages:
1. the fiberwise-close case of Proposition 4.21
2. the fiberwise-far case, using the interleaved-distance bridge from `Soundness.Lift`
3. the resulting one-step bad-event probability estimate

**NOTE**: Proposition 4.21 is the numbering in the archived DP24 PDF. This file and some internal
identifiers retain the older draft-number suffix `4_20`. In our formalization of FRI-Binius, we
also developed incremental variants Definition 4.20.2 and Proposition 4.21.2 in
`Soundness.Incremental` to enable more granular round-by-round analysis of the fold steps.

## References

* [Diamond, B.E. and Posen, J., *Polylogarithmic proofs for multilinears over binary towers*][DP24]
  Statement numbering follows the archived revision of [DP24].
-/

namespace Binius.BinaryBasefold

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
  Binius.BinaryBasefold
open scoped NNReal
open ReedSolomon Code BerlekampWelch Function
open Finset AdditiveNTT Polynomial MvPolynomial Nat Matrix
open ProbabilityTheory

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} (γ_repetitions : ℕ) [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ] -- Should we allow ℓ = 0?
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r} -- ℓ ∈ {1, ..., r-1}
variable {𝓑 : Fin 2 ↪ L}
noncomputable section
variable [SampleableType L]
variable [hdiv : Fact (ϑ ∣ ℓ)]

open scoped NNReal ProbabilityTheory

/-- **Proposition 4.21 (Case 1)**:
If f⁽ⁱ⁾ is fiber-wise close to the code, the probability of the bad event is bounded.
The bad event here is: `Δ⁽ⁱ⁾(f⁽ⁱ⁾, f̄⁽ⁱ⁾) ⊄ Δ(fold(f⁽ⁱ⁾), fold(f̄⁽ⁱ⁾))`.
-/
lemma prop_4_21_case_1_fiberwise_close (i : Fin ℓ) (steps : ℕ) [NeZero steps]
    {destIdx : Fin r} (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (h_close : fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨i, by omega⟩) (steps := steps) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f_i)) :
    let S_next := sDomain 𝔽q β h_ℓ_add_R_rate destIdx
    let domain_size := Fintype.card S_next
    Pr_{ let r_challenges ←$ᵖ (Fin steps → L) }[
        -- The definition of foldingBadEvent under the "then" branch of h_close
        let f_bar_i := UDRCodeword 𝔽q β (i := ⟨i, by omega⟩) (h_i := by
          exact Nat.le_of_lt i.isLt) f_i
          (UDRClose_of_fiberwiseClose 𝔽q β ⟨i, by omega⟩ steps h_destIdx h_destIdx_le f_i h_close)
        let folded_f_i := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩
          steps h_destIdx h_destIdx_le f_i r_challenges
        let folded_f_bar_i := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩
          steps h_destIdx h_destIdx_le f_bar_i r_challenges
        ¬ (fiberwiseDisagreementSetPerFiber 𝔽q β
            (i := ⟨i, by omega⟩) steps h_destIdx h_destIdx_le f_i f_bar_i ⊆
           disagreementSet 𝔽q β (i := destIdx) (destIdx := destIdx)
             (h_destIdx := rfl) (f := folded_f_i) (g := folded_f_bar_i))
    ] ≤ ((steps * domain_size) / Fintype.card L) := by
  exact prop421Case1_probability_bound 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    i steps h_destIdx h_destIdx_le f_i h_close
/-
  let S_next := sDomain 𝔽q β h_ℓ_add_R_rate destIdx
  let L_card := Fintype.card L
  -- 1. Setup Definitions
  let f_bar_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ :=
    UDRCodeword 𝔽q β (i := ⟨i, by omega⟩) (h_i := by
      exact Nat.le_of_lt i.isLt)
      (f := f_i) (h_within_radius := UDRClose_of_fiberwiseClose 𝔽q β ⟨i, by omega⟩ steps h_destIdx h_destIdx_le f_i h_close)
  let Δ_fiber : Set (sDomain 𝔽q β h_ℓ_add_R_rate destIdx) :=
    fiberwiseDisagreementSet 𝔽q β (i := ⟨i, by omega⟩) steps h_destIdx h_destIdx_le f_i f_bar_i
  -- We apply the Union Bound over `y ∈ Δ_fiber`
    -- `Pr[ ∃ y ∈ Δ_fiber, y ∉ Disagreement(folded) ] ≤ ∑ Pr[ y ∉ Disagreement(folded) ]`
  have h_union_bound :
    Pr_{ let r ←$ᵖ (Fin steps → L) }[
      ¬(Δ_fiber ⊆ disagreementSet 𝔽q β (i := destIdx) (destIdx := destIdx) (h_destIdx := rfl)
        (f := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ steps h_destIdx h_destIdx_le f_i r)
        (g := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ steps h_destIdx h_destIdx_le f_bar_i r))
    ] ≤ ∑ y ∈ Δ_fiber.toFinset,
        Pr_{ let r ←$ᵖ (Fin steps → L) }[
            -- The condition y ∉ Disagreement(folded) implies folded values are equal at y
            (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ steps h_destIdx h_destIdx_le f_i r) y =
            (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ steps h_destIdx h_destIdx_le f_bar_i r) y
        ] := by
      -- Standard probability union bound logic
      -- Convert probability to cardinality ratio for the Union Bound
      rw [prob_uniform_eq_card_filter_div_card]
      simp_rw [prob_uniform_eq_card_filter_div_card]
      simp only [ENNReal.coe_natCast, Fintype.card_pi, prod_const, Finset.card_univ,
        Fintype.card_fin, cast_pow, ENNReal.coe_pow]
      set left_set : Finset (Fin steps → L) :=
        Finset.univ.filter fun r =>
          ¬(Δ_fiber ⊆
            disagreementSet 𝔽q β (i := destIdx) (destIdx := destIdx) (h_destIdx := rfl) (f := iterated_fold 𝔽q β ⟨i, by omega⟩ steps
              h_destIdx h_destIdx_le f_i r)
              (g := iterated_fold 𝔽q β ⟨↑i, by omega⟩ steps
              h_destIdx h_destIdx_le f_bar_i r))
      set right_set :
          (x : sDomain 𝔽q β h_ℓ_add_R_rate destIdx) →
            Finset (Fin steps → L) :=
        fun x =>
          (Finset.univ.filter fun r =>
            iterated_fold 𝔽q β ⟨↑i, by omega⟩ steps
                h_destIdx h_destIdx_le
                f_i r x =
              iterated_fold 𝔽q β ⟨↑i, by omega⟩ steps
                h_destIdx h_destIdx_le
                f_bar_i r x)
      conv_lhs =>
        change _ * ((Fintype.card L : ENNReal) ^ steps)⁻¹
        rw [mul_comm]
      conv_rhs =>
        change
          ∑ y ∈ Δ_fiber.toFinset,
            ((#(right_set y) : ENNReal) * ((Fintype.card L : ENNReal) ^ steps)⁻¹)
      conv_rhs =>
        simp only [mul_comm]
        rw [←Finset.mul_sum]
      -- ⊢ (↑(Fintype.card L) ^ steps)⁻¹ * ↑(#left_set)
      --     ≤ (↑(Fintype.card L) ^ steps)⁻¹ * ∑ i ∈ Δ_fiber.toFinset, ↑(#(right_set i))
      let left_le_right_if := (ENNReal.mul_le_mul_left (a := ((Fintype.card L : ENNReal) ^ steps)⁻¹) (b := (#left_set)) (c := ∑ i ∈ Δ_fiber.toFinset, (#(right_set i))) (h0 := by simp only [ne_eq,
        ENNReal.inv_eq_zero, ENNReal.pow_eq_top_iff, ENNReal.natCast_ne_top, false_and,
        not_false_eq_true]) (hinf := by simp only [ne_eq, ENNReal.inv_eq_top, pow_eq_zero_iff',
          cast_eq_zero, Fintype.card_ne_zero, false_and, not_false_eq_true])).mpr
      apply left_le_right_if
      -- ⊢ ↑(#left_set) ≤ ∑ i ∈ Δ_fiber.toFinset, ↑(#(right_set i))
      -- 1. Prove the subset relation: left_set ⊆ ⋃_{y ∈ Δ} right_set y
      -- This formally connects the failure condition (∃ y, agree) to the union of agreement sets.
      have h_subset : left_set ⊆ Δ_fiber.toFinset.biUnion right_set := by
        intro r hr
        -- Unpack membership in left_set: r is bad if Δ_fiber ⊈ disagreementSet
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, left_set] at hr
        rw [Set.not_subset] at hr
        rcases hr with ⟨y, hy_mem, hy_not_dis⟩
        -- We found a y ∈ Δ_fiber where they do NOT disagree (i.e., they agree)
        rw [Finset.mem_biUnion]
        use y
        constructor
        · exact Set.mem_toFinset.mpr hy_mem
        · -- Show r ∈ right_set y (which is defined as the set of r where they agree at y)
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, right_set]
          -- hy_not_dis is ¬(folded_f_i y ≠ folded_f_bar_i y) ↔ folded_f_i y = folded_f_bar_i y
          simp only [disagreementSet, ne_eq, coe_filter, mem_univ, true_and, Set.mem_setOf_eq,
            Decidable.not_not] at hy_not_dis
          exact hy_not_dis
      -- 2. Apply cardinality bounds (Union Bound)
      calc
        (left_set.card : ENNReal)
        _ ≤ (Δ_fiber.toFinset.biUnion right_set).card := by
          -- Monotonicity of measure/cardinality: A ⊆ B → |A| ≤ |B|
          gcongr
        _ ≤ ∑ i ∈ Δ_fiber.toFinset, (right_set i).card := by
          -- Union Bound: |⋃ S_i| ≤ ∑ |S_i|
          -- push_cast moves the ENNReal coercion inside the sum
          push_cast
          let h_le_in_Nat := Finset.card_biUnion_le (s := Δ_fiber.toFinset) (t := right_set)
          norm_cast
        _ = _ := by push_cast; rfl
  apply le_trans h_union_bound
  -- Now bound the individual probabilities using Schwartz-Zippel
  have h_prob_y : ∀ y ∈ Δ_fiber,
    Pr_{ let r ←$ᵖ (Fin steps → L) }[
        (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ steps h_destIdx h_destIdx_le f_i r) y =
        (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ steps h_destIdx h_destIdx_le f_bar_i r) y
    ] ≤ (steps) / L_card := by
    intro y hy
    -- 1. Apply Lemma 4.9 (iterated_fold_eq_matrix_form) to express the equality as a matrix eq.
    --    Equality holds iff Tensor(r) * M_y * (f - f_bar)|_fiber = 0.
    -- 2. Define the polynomial P(r) = Tensor(r) * w, where w = M_y * (vals_f - vals_f_bar).
    -- 3. Show w ≠ 0:
    --      a. vals_f - vals_f_bar ≠ 0 because y ∈ Δ_fiber (definitions).
    --      b. M_y is nonsingular (Lemma 4.9 / Butterfly structure).
    -- 4. Apply prob_schwartz_zippel_mv_polynomial to P(r).
    --      degree(P) = steps.
    -- 1. Apply Lemma 4.9 to express folding as Matrix Form
    -- Equality holds iff [Tensor(r)] * [M_y] * [f - f_bar] = 0
    let vals_f : Fin (2 ^ steps) → L := fiberEvaluations 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
      (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) f_i y
    let vals_f_bar : Fin (2 ^ steps) → L := fiberEvaluations 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
      (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) f_bar_i y
    let v_diff : Fin (2 ^ steps) → L := vals_f - vals_f_bar
    -- 2. Show `v_diff ≠ 0` because `y ∈ Δ_fiber`, this is actually by definition of `Δ_fiber`.
    have hv_ne_zero : v_diff ≠ 0 := by
      unfold v_diff
      have h_exists_diff_point: ∃ x: Fin (2 ^ steps), vals_f x ≠ vals_f_bar x := by
        dsimp only [fiberwiseDisagreementSet, ne_eq, Δ_fiber] at hy
        -- ∃ x, iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ (k := steps) h_destIdx
        --   h_destIdx_le x = y ∧ f_i x ≠ f_bar_i x
        simp only [Subtype.exists, coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hy
        -- rcases hy with ⟨xL, h_quot, h_ne⟩
        rcases hy with ⟨xL, h_prop_xL⟩
        rcases h_prop_xL with ⟨xL_mem_sDomain, h_quot, h_ne⟩
        set xSDomain : sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩) := ⟨xL, xL_mem_sDomain⟩
        let x_is_fiber_of_y :=
          is_fiber_iff_generates_quotient_point 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
            (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
          (x := xSDomain) (y := y).mp (by exact id (Eq.symm h_quot))
        let x_fiberIdx : Fin (2 ^ steps) := pointToIterateQuotientIndex 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
          (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (x := xSDomain)
        use x_fiberIdx
        have h_left_eval : vals_f x_fiberIdx = f_i xSDomain := by
          unfold vals_f fiberEvaluations
          rw [x_is_fiber_of_y]
        have h_right_eval : vals_f_bar x_fiberIdx = f_bar_i xSDomain := by
          unfold vals_f_bar fiberEvaluations
          rw [x_is_fiber_of_y]
        rw [h_left_eval, h_right_eval]
        exact h_ne
      by_contra h_eq_zero
      rw [funext_iff] at h_eq_zero
      rcases h_exists_diff_point with ⟨x, h_ne⟩
      have h_eq: vals_f x = vals_f_bar x := by
        have res := h_eq_zero x
        simp only [Pi.sub_apply, Pi.zero_apply] at res
        rw [sub_eq_zero] at res
        exact res
      exact h_ne h_eq
    -- 3. M_y is nonsingular (from Lemma 4.9 context/properties of AdditiveNTT)
    let M_y := foldMatrix 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
      (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) y
    have hMy_det_ne_zero : M_y.det ≠ 0 := by
      apply foldMatrix_det_ne_zero 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i, by omega⟩) (steps := steps)
        (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (y := y)
    -- 4. w = M_y * v_diff is non-zero
    let w := M_y *ᵥ v_diff
    have hw_ne_zero : w ≠ 0 := by
      intro h
      exact hv_ne_zero (by exact Matrix.eq_zero_of_mulVec_eq_zero hMy_det_ne_zero h)
    -- 5. Construct the polynomial P(r) = Tensor(r) ⬝ w
    -- This is a multilinear polynomial of degree `steps`
    -- Tensor(r)_k corresponds to the Lagrange basis polynomial evaluated at r
    let P : MvPolynomial (Fin steps) L :=
        ∑ k : Fin (2^steps), (MvPolynomial.C (w k)) * (MvPolynomial.eqPolynomial (r := bitsOfIndex k))
    have hP_eval : ∀ r, P.eval r = (challengeTensorExpansion steps r) ⬝ᵥ w := by
      intro r
      simp only [P, MvPolynomial.eval_sum, MvPolynomial.eval_mul, MvPolynomial.eval_C]
      rw [dotProduct]
      apply Finset.sum_congr rfl
      intro k hk_univ
      conv_lhs => rw [mul_comm]
      congr 1
      -- evaluation of Lagrange basis matches tensor expansion
      -- ⊢ (MvPolynomial.eval r) (eqPolynomial (bitsOfIndex k)) = challengeTensorExpansion steps r k
      -- Unfold definitions to expose the product structure
      unfold eqPolynomial singleEqPolynomial bitsOfIndex challengeTensorExpansion multilinearWeight
      rw [MvPolynomial.eval_prod] -- prod structure of `eqPolynomial`
      -- Now both sides have form `∏ (j : Fin steps), ...`
      apply Finset.prod_congr rfl
      intro j _
      -- Simplify polynomial evaluation
      simp only [MonoidWithZeroHom.map_ite_one_zero, ite_mul, one_mul, zero_mul,
        MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_sub, map_one,
        MvPolynomial.eval_X]
      split_ifs with h_bit
      · -- Case: Bit is 1
        simp only [sub_self, zero_mul, MvPolynomial.eval_X, zero_add]
      · -- Case: Bit is 0
        simp only [sub_zero, one_mul, map_zero, add_zero]
    have hP_nonzero : P ≠ 0 := by
      -- Assume P = 0 for contradiction
      intro h_P_zero
      -- Since w ≠ 0, there exists some index k such that w k ≠ 0
      rcases Function.ne_iff.mp hw_ne_zero with ⟨k, hk_ne_zero⟩
      -- Let r_k be the bit-vector corresponding to index k
      let r_k := bitsOfIndex (L := L) k
      -- If P = 0, then P(r_k) must be 0
      have h_eval_zero : MvPolynomial.eval r_k P = 0 := by
        rw [h_P_zero]; simp only [map_zero]
      -- On the other hand, we proved P(r) = Tensor(r) ⬝ w
      rw [hP_eval r_k] at h_eval_zero
      -- Key Property: Tensor(r_k) is the indicator vector for k.
      -- Tensor(r_k)[j] = 1 if j=k, 0 if j≠k.
      have h_tensor_k : ∀ j, (challengeTensorExpansion steps r_k) j = if j = k then 1 else 0 := by
        intro j
        rw [challengeTensorExpansion_bitsOfIndex_is_eq_indicator (L := L) (n := steps) (k := k)]
      -- Thus the dot product is exactly w[k]
      rw [dotProduct, Finset.sum_eq_single k] at h_eval_zero
      · simp only [h_tensor_k, if_true, one_mul] at h_eval_zero
        exact hk_ne_zero h_eval_zero
      · -- Other terms are zero
        intro j _ h_ne
        simp [h_tensor_k, h_ne]
      · simp only [mem_univ, not_true_eq_false, _root_.mul_eq_zero, IsEmpty.forall_iff] -- Case where index k is not in univ (impossible for Fin n)
    have hP_deg : P.totalDegree ≤ steps := by
      -- Use the correct lemma from the list: sum degree ≤ d if all terms degree ≤ d
      apply MvPolynomial.totalDegree_finsetSum_le
      intro k _
      -- Bound degree of each term: deg(C * eqPoly) ≤ deg(C) + deg(eqPoly) = 0 + deg(eqPoly)
      apply le_trans (MvPolynomial.totalDegree_mul _ _)
      simp only [MvPolynomial.totalDegree_C, zero_add]
      -- Bound degree of eqPolynomial (product of linear terms)
      unfold eqPolynomial
      -- deg(∏ f) ≤ ∑ deg(f)
      apply le_trans (MvPolynomial.totalDegree_finset_prod _ _)
      -- The sum of `steps` terms, each of degree ≤ 1
      trans ∑ (i : Fin steps), 1
      · apply Finset.sum_le_sum
        intro i _
        -- Check degree of singleEqPolynomial: r*X + (1-r)*(1-X)
        unfold singleEqPolynomial
        -- deg(A + B) ≤ max(deg A, deg B)
        apply (MvPolynomial.totalDegree_add _ _).trans
        rw [max_le_iff]
        constructor
        · -- deg(C * X) ≤ 1
          apply (MvPolynomial.totalDegree_mul _ _).trans
          -- simp [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]
          -- ⊢ (1 - MvPolynomial.C (bitsOfIndex k i)).totalDegree
          --     + (1 - MvPolynomial.X i).totalDegree ≤ 1
          calc
            _ ≤ ((1 : L[X Fin steps]) - MvPolynomial.X i).totalDegree := by
              have h_left_le := MvPolynomial.totalDegree_sub_C_le (p := (1 : L[X Fin steps])) (r := bitsOfIndex k i)
              simp only [totalDegree_one] at h_left_le -- (1 - C (bitsOfIndex k i)).totalDegree ≤ 0
              omega
            _ ≤ max ((1 : L[X Fin steps]).totalDegree) ((MvPolynomial.X (R := L) i).totalDegree) := by
              apply MvPolynomial.totalDegree_sub
            _ = _ := by
              simp only [totalDegree_one, totalDegree_X, _root_.zero_le, sup_of_le_right]
        · -- deg(C * (X)) ≤ 1
          apply (MvPolynomial.totalDegree_mul _ _).trans
          simp only [MvPolynomial.totalDegree_C, zero_add]
          -- ⊢ (MvPolynomial.X i).totalDegree ≤ 1
          simp only [totalDegree_X, le_refl]
      · simp only [sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one, le_refl]
    -- 6. Apply Schwartz-Zippel using Pr_congr to switch the event
    rw [Pr_congr (Q := fun r => MvPolynomial.eval r P = 0)]
    · apply prob_schwartz_zippel_mv_polynomial P hP_nonzero hP_deg
    · intro r
      -- Show that (Folding Eq) ↔ (P(r) = 0)
      rw [iterated_fold_eq_matrix_form 𝔽q β (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le), iterated_fold_eq_matrix_form 𝔽q β (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)]
      -- Expand the dot product logic:
      unfold localized_fold_matrix_form single_point_localized_fold_matrix_form
      rw [hP_eval]
      rw [Matrix.dotProduct_mulVec]
      simp only
      -- ⊢ challengeTensorExpansion steps r ᵥ* foldMatrix 𝔽q β ⟨↑i, ⋯⟩ steps ⋯ y ⬝ᵥ
      --     fiberEvaluations 𝔽q β ⟨↑i, ⋯⟩ steps ⋯ f_i y =
      --     challengeTensorExpansion steps r ⬝ᵥ
      --       foldMatrix 𝔽q β ⟨↑i, ⋯⟩ steps ⋯ y *ᵥ
      --         fiberEvaluations 𝔽q β ⟨↑i, ⋯⟩ steps ⋯ f_bar_i y ↔
      --   challengeTensorExpansion steps r ⬝ᵥ w = 0
      rw [←sub_eq_zero]
      -- Transform LHS: u ⬝ (M * a) - u ⬝ (M * b) = u ⬝ (M * a - M * b)
      rw [←Matrix.dotProduct_mulVec]
      rw [←dotProduct_sub]
      -- Transform inner vector: M * a - M * b = M * (a - b)
      rw [←Matrix.mulVec_sub]
      -- Substitute definition of w: w = M * (vals_f - vals_f_bar)
      -- Note: v_diff was defined as vals_f - vals_f_bar
      -- And w was defined as M_y *ᵥ v_diff
  -- Sum the bounds: |Δ_fiber| * (steps / |L|)
  -- Since |Δ_fiber| ≤ |S_next|, this is bounded by |S_next| * steps / |L|
  have h_card_fiber : Δ_fiber.toFinset.card ≤ Fintype.card S_next :=
    Finset.card_le_univ Δ_fiber.toFinset
  calc
    _ ≤ ∑ y ∈ Δ_fiber.toFinset, (steps : ENNReal)  / L_card := by
        apply Finset.sum_le_sum
        intro y hy -- hy : y ∈ Δ_fiber.toFinset
        let res := h_prob_y y (by exact Set.mem_toFinset.mp hy)
        exact res
    _ = (Δ_fiber.toFinset.card) * (steps / L_card) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Fintype.card S_next) * (steps / L_card) := by
        gcongr
    _ = (steps * Fintype.card S_next) / L_card := by
      ring_nf
      conv_rhs => rw [mul_div_assoc]
-/

/-!
### Soundness Lemmas Around Proposition 4.21

The residual-free fiberwise-far branch and the resulting full bad-event probability theorem live
in `Soundness.Prop421Case2Probability`, where the fold/pre-tensor bridge and Lemma 4.22 far-lift
are both available without an import cycle.
-/

end

end Binius.BinaryBasefold

end SoundnessProposition
