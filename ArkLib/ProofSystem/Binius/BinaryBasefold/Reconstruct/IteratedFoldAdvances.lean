/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.Code

/-!
# Iterated fold advances the intermediate evaluation polynomial (BCIKS Lemma 4.13, iterated)

This file proves `iterated_fold_advances_evaluation_poly`: iterating the single-step fold
`steps` times (from level `i` to `destIdx = i + steps`) on the oracle function of the
intermediate evaluation polynomial `intermediateEvaluationPoly i coeffs` yields the oracle
function of `intermediateEvaluationPoly destIdx new_coeffs`, where `new_coeffs` is the iterated
coefficient refinement `fun j => ∑ x, multilinearWeight r_challenges x * coeffs ⟨j*2^steps + x⟩`.

It is the iterated form of the single-step `fold_advances_evaluation_poly_legacy`, proven by
induction on `steps`.
-/

namespace Binius.BinaryBasefold

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
  Binius.BinaryBasefold
open scoped NNReal
open ReedSolomon Code BerlekampWelch Function
open Finset AdditiveNTT Polynomial MvPolynomial Nat Matrix

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

/-- The iterated coefficient refinement: after `steps` folds with challenges `r_challenges`,
coefficient `j` of the resulting polynomial is the multilinear-weight combination of the
original coefficients in the block `[j*2^steps, (j+1)*2^steps)`. -/
def iteratedRefineCoeffs {i destIdx : Fin r} (steps : ℕ)
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (coeffs : Fin (2 ^ (ℓ - i.val)) → L) (r_challenges : Fin steps → L) :
    Fin (2 ^ (ℓ - destIdx.val)) → L :=
  fun j => ∑ x : Fin (2 ^ steps), multilinearWeight r_challenges x *
    coeffs ⟨j.val * 2 ^ steps + x.val, by
      have hle : i.val + steps ≤ ℓ := by rw [← h_destIdx]; exact h_destIdx_le
      have hpow : 2 ^ (ℓ - i.val) = 2 ^ (ℓ - destIdx.val) * 2 ^ steps := by
        rw [← pow_add]; congr 1; omega
      rw [hpow]
      have hj := j.isLt
      have hx := x.isLt
      calc j.val * 2 ^ steps + x.val
          < j.val * 2 ^ steps + 2 ^ steps := by omega
        _ = (j.val + 1) * 2 ^ steps := by ring
        _ ≤ 2 ^ (ℓ - destIdx.val) * 2 ^ steps := by
            apply Nat.mul_le_mul_right; omega⟩

omit [CharP L 2] [DecidableEq 𝔽q] [NeZero ℓ] in
/-- Single-step new-API version of `fold_advances_evaluation_poly_legacy`: folding the raw-eval
oracle function of `intermediateEvaluationPoly i coeffs` (via the `{destIdx}`-keyed `fold`)
yields the raw-eval oracle function of `intermediateEvaluationPoly destIdx new_coeffs`, where
`new_coeffs j = (1 - r_chal) * coeffs⟨2j⟩ + r_chal * coeffs⟨2j+1⟩`. -/
theorem fold_advances_evaluation_poly_step
    (i : Fin r) {destIdx : Fin r} (h_i_lt : i.val < ℓ)
    (h_destIdx : destIdx.val = i.val + 1) (h_destIdx_le : destIdx ≤ ℓ)
    (coeffs : Fin (2 ^ (ℓ - i.val)) → L) (r_chal : L)
    (new_coeffs : Fin (2 ^ (ℓ - destIdx.val)) → L)
    (h_new_coeffs : ∀ j : Fin (2 ^ (ℓ - destIdx.val)),
      new_coeffs j =
        (1 - r_chal) * coeffs ⟨j.val * 2, by
          have hpow : 2 ^ (ℓ - i.val) = 2 ^ (ℓ - destIdx.val) * 2 := by
            rw [← pow_succ]; congr 1; omega
          have := j.isLt; rw [hpow]; omega⟩ +
        r_chal * coeffs ⟨j.val * 2 + 1, by
          have hpow : 2 ^ (ℓ - i.val) = 2 ^ (ℓ - destIdx.val) * 2 := by
            rw [← pow_succ]; congr 1; omega
          have := j.isLt; rw [hpow]; omega⟩) :
    fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (destIdx := destIdx)
        (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
        (f := fun x => (intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate
          ⟨i.val, by omega⟩ coeffs).eval x.val) (r_chal := r_chal) =
      fun y => (intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate
        ⟨destIdx.val, by omega⟩ new_coeffs).eval y.val := by
  classical
  -- Reduce `destIdx` to its canonical `⟨i+1, _⟩` form. The index bound is derived from
  -- `h_i_lt`/`h_ℓ_add_R_rate` alone (independent of `h_destIdx`), so `subst` is unobstructed.
  have ha_lt0 : i.val + 1 < r := by
    have hR : 0 < 𝓡 := Nat.pos_of_neZero 𝓡
    omega
  have hdest : destIdx = (⟨i.val + 1, ha_lt0⟩ : Fin r) := Fin.eq_of_val_eq h_destIdx
  subst hdest
  -- Invoke the legacy single-step advance lemma at `i' : Fin ℓ`.
  have h_i_succ_lt : i.val + 1 < ℓ + 𝓡 := by
    have hR : 0 < 𝓡 := Nat.pos_of_neZero 𝓡
    omega
  have h_legacy := fold_advances_evaluation_poly_legacy 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i.val, h_i_lt⟩)
    (h_i_succ_lt := by simpa using h_i_succ_lt) (coeffs := coeffs) (r_chal := r_chal)
  simp only at h_legacy
  funext y
  -- Unfold `fold`: at the canonical destination index `⟨i+1, _⟩` the cast collapses.
  unfold fold
  simp only [cast_eq]
  -- Apply the legacy advance at the point `y` (now at the canonical index).
  rw [h_legacy ⟨y.val, y.property⟩]
  -- Reconcile the legacy `new_coeffs` with our `new_coeffs` pointwise.
  congr 1
  unfold intermediateEvaluationPoly
  apply Finset.sum_congr rfl
  rintro ⟨j, hj⟩ _
  simp only
  rw [h_new_coeffs ⟨j, hj⟩]

omit [NeZero r] [Fintype L] [DecidableEq L] [CharP L 2] [NeZero ℓ] [NeZero 𝓡] in
/-- **Low half of the multilinear weight tensor.** For `x : Fin (2^n)` (so the top bit `n` of
`x` is `0`), the `(n+1)`-challenge weight at index `x` factors as the `n`-challenge weight at
`x` (over `Fin.init r`) times `(1 - r (last n))`. -/
theorem multilinearWeight_castSucc_low {n : ℕ} (r : Fin (n + 1) → L) (x : Fin (2 ^ n)) :
    multilinearWeight r ⟨x.val, by
      have := x.isLt; calc x.val < 2 ^ n := this
        _ ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by omega) (by omega)⟩ =
      multilinearWeight (Fin.init r) x * (1 - r (Fin.last n)) := by
  have h_getLastBit : Nat.getBit (Fin.last n) x.val = 0 := by
    have h := Nat.getBit_of_lt_two_pow (a := x) (k := Fin.last n)
    simp only [Fin.val_last, lt_self_iff_false, ↓reduceIte] at h
    exact h
  dsimp only [multilinearWeight]
  rw [Fin.prod_univ_castSucc]
  simp_rw [Nat.testBit_true_eq_getBit_eq_1]
  simp_rw [h_getLastBit]
  simp only [Fin.val_castSucc, Fin.init]
  congr 1

omit [NeZero r] [Fintype L] [DecidableEq L] [CharP L 2] [NeZero ℓ] [NeZero 𝓡] in
/-- **High half of the multilinear weight tensor.** For `x : Fin (2^n)`, the `(n+1)`-challenge
weight at index `2^n + x` (top bit `n` set) factors as the `n`-challenge weight at `x`
(over `Fin.init r`) times `r (last n)`. -/
theorem multilinearWeight_castSucc_high {n : ℕ} (r : Fin (n + 1) → L) (x : Fin (2 ^ n)) :
    multilinearWeight r ⟨2 ^ n + x.val, by
      have := x.isLt; rw [pow_succ]; omega⟩ =
      multilinearWeight (Fin.init r) x * (r (Fin.last n)) := by
  have h_getLastBit : Nat.getBit (Fin.last n) x.val = 0 := by
    have h := Nat.getBit_of_lt_two_pow (a := x) (k := Fin.last n)
    simp only [Fin.val_last, lt_self_iff_false, ↓reduceIte] at h
    exact h
  have h_x_and_two_pow : x.val &&& (2 ^ n) = 0 := by
    apply Nat.and_two_pow_eq_zero_of_getBit_0 (n := x.val) (i := n)
    exact h_getLastBit
  have h_x_add_two_pow := Nat.sum_of_and_eq_zero_is_xor
    (n := x.val) (m := 2 ^ n) (h_n_AND_m := h_x_and_two_pow)
  have h_x_add_two_pow_comm : 2 ^ n + x.val = x.val ^^^ 2 ^ n := by
    rw [Nat.add_comm]
    exact h_x_add_two_pow
  have h_getLastBit_add_pow : Nat.getBit (Fin.last n) (2 ^ n + x.val) = 1 := by
    rw [h_x_add_two_pow_comm]
    rw [Nat.getBit_of_xor]
    rw [h_getLastBit]
    rw [Nat.getBit_two_pow]
    simp only [Fin.val_last, BEq.rfl, ↓reduceIte, Nat.zero_xor]
  dsimp only [multilinearWeight]
  rw [Fin.prod_univ_castSucc]
  simp_rw [Nat.testBit_true_eq_getBit_eq_1]
  simp_rw [h_getLastBit_add_pow]
  simp only [Fin.val_last, Fin.val_castSucc, Fin.init, ↓reduceIte]
  congr 1
  apply Finset.prod_congr rfl
  intro k _
  rw [h_x_add_two_pow_comm]
  simp_rw [Nat.getBit_of_xor, Nat.getBit_two_pow]
  simp only [beq_iff_eq]
  have h_k_ne_n : n ≠ k.val := by omega
  simp only [h_k_ne_n, ↓reduceIte, Nat.xor_zero]


omit [NeZero r] [Fintype L] [DecidableEq L] [CharP L 2] [NeZero ℓ] [NeZero 𝓡] in
/-- `multilinearWeight` depends only on the underlying value of its index. -/
theorem multilinearWeight_val_eq {n : ℕ} (rc : Fin n → L) {a b : Fin (2 ^ n)}
    (h : a.val = b.val) : multilinearWeight rc a = multilinearWeight rc b := by
  congr 1; exact Fin.ext h

omit [Fintype L] [DecidableEq L] [CharP L 2] [NeZero ℓ] [NeZero 𝓡] in
/-- **Coefficient-refinement recursion (peel last challenge).** The `(n+1)`-step iterated
refinement equals one single-step (last-challenge) refinement of the `n`-step iterated refinement
(over the truncated challenges `Fin.init r`). The `2j`/`2j+1` "low bit of the `coeffs` index" of
the single step becomes the **high bit** of the `2^n`-block offset, matching the multilinear-weight
tensor split. -/
theorem iteratedRefineCoeffs_succ {i mid destIdx : Fin r} (n : ℕ)
    (h_mid : mid.val = i.val + n) (h_destIdx : destIdx.val = i.val + (n + 1))
    (h_mid_le : mid ≤ ℓ) (h_destIdx_le : destIdx ≤ ℓ)
    (coeffs : Fin (2 ^ (ℓ - i.val)) → L) (r_challenges : Fin (n + 1) → L)
    (j : Fin (2 ^ (ℓ - destIdx.val))) :
    iteratedRefineCoeffs (𝓡 := 𝓡) (i := i) (destIdx := destIdx) (n + 1) h_destIdx h_destIdx_le
        coeffs r_challenges j =
      (1 - r_challenges (Fin.last n)) *
        iteratedRefineCoeffs (𝓡 := 𝓡) (i := i) (destIdx := mid) n h_mid h_mid_le coeffs
          (Fin.init r_challenges) ⟨j.val * 2, by
            have hpow : 2 ^ (ℓ - mid.val) = 2 ^ (ℓ - destIdx.val) * 2 := by
              rw [← pow_succ]; congr 1; omega
            have := j.isLt; rw [hpow]; omega⟩ +
      r_challenges (Fin.last n) *
        iteratedRefineCoeffs (𝓡 := 𝓡) (i := i) (destIdx := mid) n h_mid h_mid_le coeffs
          (Fin.init r_challenges) ⟨j.val * 2 + 1, by
            have hpow : 2 ^ (ℓ - mid.val) = 2 ^ (ℓ - destIdx.val) * 2 := by
              rw [← pow_succ]; congr 1; omega
            have := j.isLt; rw [hpow]; omega⟩ := by
  -- Block-index bounds (used to repackage the `coeffs` arguments).
  have hbound_low : ∀ x : Fin (2 ^ n),
      (j.val * 2) * 2 ^ n + x.val < 2 ^ (ℓ - i.val) := by
    intro x
    have hpow : 2 ^ (ℓ - i.val) = 2 ^ (ℓ - mid.val) * 2 ^ n := by
      rw [← pow_add]; congr 1; omega
    have hjlt : j.val * 2 < 2 ^ (ℓ - mid.val) := by
      have hpow2 : 2 ^ (ℓ - mid.val) = 2 ^ (ℓ - destIdx.val) * 2 := by
        rw [← pow_succ]; congr 1; omega
      have := j.isLt; rw [hpow2]; omega
    have := x.isLt; rw [hpow]; nlinarith [hjlt, this]
  have hbound_high : ∀ x : Fin (2 ^ n),
      (j.val * 2 + 1) * 2 ^ n + x.val < 2 ^ (ℓ - i.val) := by
    intro x
    have hpow : 2 ^ (ℓ - i.val) = 2 ^ (ℓ - mid.val) * 2 ^ n := by
      rw [← pow_add]; congr 1; omega
    have hjlt : j.val * 2 + 1 < 2 ^ (ℓ - mid.val) := by
      have hpow2 : 2 ^ (ℓ - mid.val) = 2 ^ (ℓ - destIdx.val) * 2 := by
        rw [← pow_succ]; congr 1; omega
      have := j.isLt; rw [hpow2]; omega
    have := x.isLt; rw [hpow]; nlinarith [hjlt, this]
  have hsplit : (2 : ℕ) ^ (n + 1) = 2 ^ n + 2 ^ n := Nat.two_pow_succ n
  -- Unfold both sides to explicit sums.
  simp only [iteratedRefineCoeffs]
  -- Split the LHS sum over `Fin (2^(n+1))` into the two `Fin (2^n)` halves.
  rw! (castMode := .all) [hsplit]
  rw [Fin.sum_univ_add (a := 2 ^ n) (b := 2 ^ n)]
  -- Normalise the `cast`/`castAdd`/`natAdd` index gymnastics introduced by the split.
  simp only [Fin.natAdd_eq_addNat, eq_mp_eq_cast, Fin.cast_mk, Fin.val_castAdd, Fin.val_addNat,
    Fin.coe_cast]
  -- Combine the two LHS halves into a single sum over `Fin (2^n)`.
  rw [← Finset.sum_add_distrib]
  -- Distribute the scalar factors on the RHS through its sums, and combine those too.
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  -- Match termwise on `Fin (2^n)`.
  apply Finset.sum_congr rfl
  intro x _
  -- Re-express the two LHS weights via the low/high tensor split.
  have h_low := multilinearWeight_castSucc_low (r := r) (ℓ := ℓ) (𝓡 := 𝓡) (L := L) (n := n)
    r_challenges x
  have h_high := multilinearWeight_castSucc_high (r := r) (ℓ := ℓ) (𝓡 := 𝓡) (L := L) (n := n)
    r_challenges x
  -- Split into the two summands; match the weight and coefficient factors separately.
  rw [show (1 - r_challenges (Fin.last n)) *
        (multilinearWeight (Fin.init r_challenges) x * coeffs ⟨↑j * 2 * 2 ^ n + ↑x, hbound_low x⟩)
      = (multilinearWeight (Fin.init r_challenges) x * (1 - r_challenges (Fin.last n))) *
        coeffs ⟨↑j * 2 * 2 ^ n + ↑x, hbound_low x⟩ from by ring]
  rw [show r_challenges (Fin.last n) *
        (multilinearWeight (Fin.init r_challenges) x * coeffs ⟨(↑j * 2 + 1) * 2 ^ n + ↑x,
          hbound_high x⟩)
      = (multilinearWeight (Fin.init r_challenges) x * r_challenges (Fin.last n)) *
        coeffs ⟨(↑j * 2 + 1) * 2 ^ n + ↑x, hbound_high x⟩ from by ring]
  rw [← h_low, ← h_high]
  congr 1
  · -- low summand
    congr 1
    · apply multilinearWeight_val_eq
      rw [eqRec_eq_cast, ← Fin.cast_eq_cast (Nat.two_pow_succ n).symm, Fin.coe_cast,
        Fin.val_castAdd]
    · congr 1; apply Fin.ext; simp only; ring
  · -- high summand
    congr 1
    · apply multilinearWeight_val_eq
      rw [eqRec_eq_cast, ← Fin.cast_eq_cast (Nat.two_pow_succ n).symm, Fin.coe_cast,
        Fin.val_addNat, Nat.add_comm]
    · congr 1; apply Fin.ext; simp only; ring

/-- **Lemma 4.13 (iterated), ℕ-indexed core.** Iterating the single-step fold `steps` times from
level `i` to `destIdx = i + steps` on the raw-eval oracle function of `intermediateEvaluationPoly i
coeffs` yields the raw-eval oracle function of `intermediateEvaluationPoly destIdx new_coeffs`,
where `new_coeffs = iteratedRefineCoeffs steps … coeffs r_challenges` is the iterated multilinear-
weight refinement. Proven by induction on `steps`: base case `iterated_fold_zero_steps`; inductive
step peels the last fold (`iterated_fold_last`), advances one level
(`fold_advances_evaluation_poly_step`), and rewrites the coefficient recursion
(`iteratedRefineCoeffs_succ`). -/
theorem iterated_fold_advances_evaluation_poly_nat
    (i : Fin r) (steps : ℕ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (coeffs : Fin (2 ^ (ℓ - i.val)) → L) (r_challenges : Fin steps → L) :
    iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps)
        (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
        (f := fun x => (intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate
          ⟨i.val, by omega⟩ coeffs).eval x.val) (r_challenges := r_challenges) =
      fun y => (intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate
        ⟨destIdx.val, by omega⟩
        (iteratedRefineCoeffs (𝓡 := 𝓡) (i := i) (destIdx := destIdx) steps h_destIdx h_destIdx_le
          coeffs r_challenges)).eval y.val := by
  induction steps generalizing destIdx with
  | zero =>
    -- Base: `0` folds. Reduce `destIdx` to `⟨i.val, _⟩`.
    have hdest : destIdx = (⟨i.val, i.isLt⟩ : Fin r) := Fin.eq_of_val_eq (by omega)
    subst hdest
    funext y
    rw [iterated_fold_zero_steps 𝔽q β (i := i) (h_destIdx := by simp only)
      (h_destIdx_le := h_destIdx_le)
      (f := fun x => (intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate ⟨i.val, by omega⟩ coeffs).eval
        x.val) (r_challenges := r_challenges) y]
    simp only [eq_mp_eq_cast, cast_eq]
    -- `iteratedRefineCoeffs 0 … = coeffs`, so the two eval-polys agree.
    have h_coeffs : (iteratedRefineCoeffs (𝓡 := 𝓡) (i := i) (destIdx := ⟨i.val, i.isLt⟩) 0
        h_destIdx h_destIdx_le coeffs r_challenges) = coeffs := by
      funext j
      unfold iteratedRefineCoeffs
      haveI huniq : Unique (Fin (2 ^ (0 : ℕ))) := by rw [pow_zero]; infer_instance
      rw [Fintype.sum_unique]
      simp only [multilinearWeight, Finset.univ_eq_empty, Finset.prod_empty, one_mul, Nat.mul_one]
      congr 1
      apply Fin.ext
      have hd : (default : Fin (2 ^ 0)).val = 0 := by
        have := (default : Fin (2 ^ 0)).isLt; simp only [pow_zero] at this; omega
      simp only [Fin.val_mk, pow_zero, Nat.mul_one, Nat.add_zero]
      omega
    rw [h_coeffs]
  | succ n ih =>
    -- Peel the last fold: `iterated_fold (n+1) = fold (at mid) (iterated_fold n) (r (last n))`.
    funext y
    -- The intermediate index `mid = i + n`.
    set mid : Fin r := ⟨i.val + n, by
      have hle : i.val + (n + 1) ≤ ℓ := by rw [← h_destIdx]; exact h_destIdx_le
      have hℓr : ℓ < r := ℓ_lt_r (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      omega⟩ with hmid_def
    have h_mid_val : mid.val = i.val + n := by rw [hmid_def]
    have h_mid_le : mid ≤ ℓ := by
      have : mid.val ≤ ℓ := by rw [h_mid_val]; omega
      exact this
    rw [iterated_fold_last 𝔽q β (i := i) (midIdx := mid) (destIdx := destIdx) (steps := n)
      (h_midIdx := h_mid_val) (h_destIdx := by omega) (h_destIdx_le := h_destIdx_le)
      (f := fun x => (intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate ⟨i.val, by omega⟩ coeffs).eval
        x.val) (r_challenges := r_challenges)]
    -- Apply the induction hypothesis to the inner `n`-fold (over `Fin.init r_challenges`).
    rw [ih (destIdx := mid) (h_destIdx := h_mid_val) (h_destIdx_le := h_mid_le)
      (r_challenges := Fin.init r_challenges)]
    -- Advance one level via the single-step new-API lemma.
    rw [fold_advances_evaluation_poly_step 𝔽q β (i := mid) (destIdx := destIdx)
      (h_i_lt := by rw [hmid_def]; simp only; omega) (h_destIdx := by omega)
      (h_destIdx_le := h_destIdx_le)
      (coeffs := iteratedRefineCoeffs (𝓡 := 𝓡) (i := i) (destIdx := mid) n h_mid_val h_mid_le
        coeffs (Fin.init r_challenges))
      (r_chal := r_challenges (Fin.last n))
      (new_coeffs := iteratedRefineCoeffs (𝓡 := 𝓡) (i := i) (destIdx := destIdx) (n + 1) h_destIdx
        h_destIdx_le coeffs r_challenges)
      (h_new_coeffs := by
        intro k
        rw [iteratedRefineCoeffs_succ (i := i) (mid := mid) (destIdx := destIdx) n
          h_mid_val h_destIdx h_mid_le h_destIdx_le coeffs r_challenges k])]


/-- **Lemma 4.13 (iterated), `Fin (ℓ+1)`-indexed form** consumed by `ReductionLogic`. Iterating
the fold `steps` times (with `steps : Fin (ℓ+1)`) from level `i` to `destIdx = i + steps` advances
the raw-eval oracle function of `intermediateEvaluationPoly i coeffs` to that of
`intermediateEvaluationPoly destIdx new_coeffs`, where `new_coeffs` is the explicit
multilinear-weight refinement `fun j => ∑ x, multilinearWeight r_challenges x * coeffs ⟨j*2^steps +
x⟩`. Thin wrapper around `iterated_fold_advances_evaluation_poly_nat`. -/
theorem iterated_fold_advances_evaluation_poly
    (i : Fin r) (steps : Fin (ℓ + 1)) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + steps.val) (h_destIdx_le : destIdx ≤ ℓ)
    (coeffs : Fin (2 ^ (ℓ - i.val)) → L) (r_challenges : Fin steps.val → L) :
    iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps.val)
        (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
        (f := fun x => (intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate
          ⟨i.val, by omega⟩ coeffs).eval x.val) (r_challenges := r_challenges) =
      fun y => (intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate
        ⟨destIdx.val, by omega⟩
        (iteratedRefineCoeffs (𝓡 := 𝓡) (i := i) (destIdx := destIdx) steps.val h_destIdx
          h_destIdx_le coeffs r_challenges)).eval y.val :=
  iterated_fold_advances_evaluation_poly_nat 𝔽q β (i := i) (steps := steps.val)
    (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (coeffs := coeffs)
    (r_challenges := r_challenges)

end

end Binius.BinaryBasefold

-- Axiom audit.
#print axioms Binius.BinaryBasefold.iterated_fold_advances_evaluation_poly
