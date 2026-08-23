/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.SoundnessCase1Bridge
import ArkLib.Data.Probability.TensorSchwartzZippel
import ArkLib.Data.Probability.PrUnionBound

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
