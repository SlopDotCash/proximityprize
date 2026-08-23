/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.Probability.Instances

/-!
# Tensor-affine Schwartz-Zippel engine

Generic (field-level, no Binius imports) machinery for the "tensor combination"
polynomial `tensorComb n a = ∑ idx, C (a idx) * tensorWeight n idx`, where
`tensorWeight n idx` is the multilinear tensor basis polynomial in `n` variables
whose evaluation at the Boolean cube point `cubePoint n j` is the Kronecker delta
`if idx = j then 1 else 0`.

Orientation convention (chosen to match Binius `challengeTensorProduct_succ_get`
downstream): the LOW bit `idx.val % 2` selects the factor in the LAST variable
`Fin.last n`; the remaining bits `idx.val / 2` recurse into the first `n` variables
via `rename Fin.castSucc`.

Key export: `TensorSZ.tensorComb_vanish_prob_le` — if `a ≠ 0` then a uniformly
random evaluation point kills `tensorComb n a` with probability at most
`n / |L|` (Schwartz-Zippel, since `tensorComb` has total degree ≤ n and is
nonzero by interpolation on the cube).
-/

open MvPolynomial NNReal ProbabilityTheory

namespace TensorSZ

/-- `idx.val / 2 < 2^n` for `idx : Fin (2^(n+1))` — the "high bits" of an index. -/
lemma halfLt {n : ℕ} (idx : Fin (2 ^ (n + 1))) : idx.val / 2 < 2 ^ n := by
  have h := idx.isLt
  omega

variable (L : Type) [Field L] [Fintype L] [DecidableEq L]

/-- The multilinear tensor basis polynomial: low bit of `idx` selects the factor in
the last variable (`1 - X (Fin.last n)` for bit 0, `X (Fin.last n)` for bit 1), and
the high bits recurse into the first `n` variables. -/
noncomputable def tensorWeight : ∀ n : ℕ, Fin (2 ^ n) → MvPolynomial (Fin n) L
  | 0, _ => 1
  | n + 1, idx =>
    (if idx.val % 2 = 0 then 1 - MvPolynomial.X (Fin.last n) else MvPolynomial.X (Fin.last n)) *
      MvPolynomial.rename Fin.castSucc (tensorWeight n ⟨idx.val / 2, halfLt idx⟩)

@[simp] lemma tensorWeight_zero (idx : Fin (2 ^ 0)) : tensorWeight L 0 idx = 1 := rfl

lemma tensorWeight_succ (n : ℕ) (idx : Fin (2 ^ (n + 1))) :
    tensorWeight L (n + 1) idx =
      (if idx.val % 2 = 0 then 1 - MvPolynomial.X (Fin.last n)
        else MvPolynomial.X (Fin.last n)) *
      MvPolynomial.rename Fin.castSucc (tensorWeight L n ⟨idx.val / 2, halfLt idx⟩) := rfl

/-- The tensor combination of coefficients `a` with the tensor basis. -/
noncomputable def tensorComb (n : ℕ) (a : Fin (2 ^ n) → L) : MvPolynomial (Fin n) L :=
  ∑ idx, MvPolynomial.C (a idx) * tensorWeight L n idx

/-- The Boolean cube point indexed by `j`: the last coordinate is the low bit
`j.val % 2` (as `0`/`1` in `L`); the earlier coordinates recurse on `j.val / 2`. -/
def cubePoint : ∀ n : ℕ, Fin (2 ^ n) → (Fin n → L)
  | 0, _ => Fin.elim0
  | n + 1, j =>
    Fin.snoc (cubePoint n ⟨j.val / 2, halfLt j⟩) (if j.val % 2 = 0 then (0 : L) else 1)

lemma cubePoint_succ (n : ℕ) (j : Fin (2 ^ (n + 1))) :
    cubePoint L (n + 1) j =
      Fin.snoc (cubePoint L n ⟨j.val / 2, halfLt j⟩)
        (if j.val % 2 = 0 then (0 : L) else 1) := rfl

/-- Closed recursion for evaluating `tensorWeight` at any point: low bit picks the
affine factor in the last coordinate; high bits evaluate the lower tensor weight at
the restricted point. Matches Binius `challengeTensorProduct_succ_get` orientation. -/
lemma tensorWeight_eval_succ (n : ℕ) (idx : Fin (2 ^ (n + 1))) (r : Fin (n + 1) → L) :
    MvPolynomial.eval r (tensorWeight L (n + 1) idx) =
      (if idx.val % 2 = 0 then 1 - r (Fin.last n) else r (Fin.last n)) *
        MvPolynomial.eval (r ∘ Fin.castSucc) (tensorWeight L n ⟨idx.val / 2, halfLt idx⟩) := by
  rw [tensorWeight_succ, map_mul, MvPolynomial.eval_rename]
  congr 1
  split <;> simp

/-- `tensorWeight n idx` evaluates on the Boolean cube to the Kronecker delta. -/
lemma tensorWeight_eval_cube (n : ℕ) (idx j : Fin (2 ^ n)) :
    MvPolynomial.eval (cubePoint L n j) (tensorWeight L n idx) =
      if idx = j then 1 else 0 := by
  induction n with
  | zero =>
    have hij : idx = j := Fin.ext (by omega)
    simp [hij]
  | succ n ih =>
    rw [cubePoint_succ, tensorWeight_eval_succ]
    have hcomp :
        (Fin.snoc (cubePoint L n ⟨j.val / 2, halfLt j⟩)
            (if j.val % 2 = 0 then (0 : L) else 1)) ∘ Fin.castSucc =
          cubePoint L n ⟨j.val / 2, halfLt j⟩ := Fin.snoc_comp_castSucc
    rw [hcomp, Fin.snoc_last, ih]
    have h1 : (if (⟨idx.val / 2, halfLt idx⟩ : Fin (2 ^ n)) = ⟨j.val / 2, halfLt j⟩
          then (1 : L) else 0) =
        if idx.val / 2 = j.val / 2 then 1 else 0 := by
      simp
    have h2 : (if idx = j then (1 : L) else 0) = if idx.val = j.val then 1 else 0 := by
      simp [Fin.ext_iff]
    rw [h1, h2]
    rcases Nat.mod_two_eq_zero_or_one idx.val with hi | hi <;>
      rcases Nat.mod_two_eq_zero_or_one j.val with hj | hj <;>
        by_cases hd : idx.val / 2 = j.val / 2 <;>
          by_cases he : idx.val = j.val <;>
            first
              | (exfalso; omega)
              | simp [hi, hj, hd, he]

/-- `tensorComb n a` interpolates `a` on the Boolean cube. -/
lemma tensorComb_eval_cube (n : ℕ) (a : Fin (2 ^ n) → L) (j : Fin (2 ^ n)) :
    MvPolynomial.eval (cubePoint L n j) (tensorComb L n a) = a j := by
  unfold tensorComb
  rw [map_sum]
  simp only [map_mul, MvPolynomial.eval_C, tensorWeight_eval_cube]
  simp [Finset.sum_ite_eq']

/-- Evaluation of `tensorComb` as a sum of weighted tensor-weight evaluations. -/
lemma tensorComb_eval (n : ℕ) (a : Fin (2 ^ n) → L) (r : Fin n → L) :
    MvPolynomial.eval r (tensorComb L n a) =
      ∑ idx, a idx * MvPolynomial.eval r (tensorWeight L n idx) := by
  unfold tensorComb
  rw [map_sum]
  simp [map_mul]

/-- If the coefficient vector is nonzero, so is the tensor combination
(by interpolation: a zero polynomial would have all cube evaluations zero). -/
lemma tensorComb_ne_zero (n : ℕ) (a : Fin (2 ^ n) → L) (ha : a ≠ 0) :
    tensorComb L n a ≠ 0 := by
  intro h
  apply ha
  funext j
  have hj := tensorComb_eval_cube L n a j
  rw [h] at hj
  simpa using hj.symm

/-- Each tensor weight is multilinear, hence of total degree at most `n`. -/
lemma tensorWeight_totalDegree (n : ℕ) (idx : Fin (2 ^ n)) :
    (tensorWeight L n idx).totalDegree ≤ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [tensorWeight_succ]
    refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
    have h1 : (if idx.val % 2 = 0 then 1 - MvPolynomial.X (Fin.last n)
          else (MvPolynomial.X (Fin.last n) : MvPolynomial (Fin (n + 1)) L)).totalDegree ≤ 1 := by
      split
      · refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
        simp [MvPolynomial.totalDegree_one, MvPolynomial.totalDegree_X]
      · simp [MvPolynomial.totalDegree_X]
    have h2 : (MvPolynomial.rename Fin.castSucc
          (tensorWeight L n ⟨idx.val / 2, halfLt idx⟩)).totalDegree ≤ n :=
      le_trans (MvPolynomial.totalDegree_rename_le _ _) (ih _)
    omega

/-- The tensor combination has total degree at most `n`. -/
lemma tensorComb_totalDegree (n : ℕ) (a : Fin (2 ^ n) → L) :
    (tensorComb L n a).totalDegree ≤ n := by
  refine le_trans (MvPolynomial.totalDegree_finset_sum _ _) ?_
  refine Finset.sup_le fun idx _ => ?_
  refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
  have := tensorWeight_totalDegree L n idx
  simp only [MvPolynomial.totalDegree_C, zero_add]
  exact this

/-- **Tensor-affine Schwartz-Zippel.** If the coefficient vector `a` is nonzero, then
a uniformly random point kills the tensor combination with probability at most
`n / |L|`. -/
lemma tensorComb_vanish_prob_le (n : ℕ) (a : Fin (2 ^ n) → L) (ha : a ≠ 0) :
    Pr_{ let r ←$ᵖ (Fin n → L) }[ MvPolynomial.eval r (tensorComb L n a) = 0 ] ≤
      (n : ℝ≥0) / (Fintype.card L : ℝ≥0) :=
  prob_schwartz_zippel_mv_polynomial_of_totalDegree_le (tensorComb L n a)
    (tensorComb_ne_zero L n a ha) (tensorComb_totalDegree L n a)

end TensorSZ

#print axioms TensorSZ.tensorComb_vanish_prob_le
#print axioms TensorSZ.tensorComb_eval_cube
#print axioms TensorSZ.tensorComb_ne_zero
#print axioms TensorSZ.tensorWeight_eval_cube
#print axioms TensorSZ.tensorWeight_eval_succ
#print axioms TensorSZ.tensorComb_eval
#print axioms TensorSZ.tensorComb_totalDegree
