/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic

/-! # Evaluation matrices for the shifted binomial Hankel determinant

Clearing a row of the shifted binomial Hankel matrix gives evaluations of products
of linear factors. On a translated grid these products form a triangular matrix.
This certifies invertibility on any other grid of the same size.
-/

namespace ProximityGap.RationalObservableHankel

open Finset Polynomial

variable {K : Type*} [Field K]

/-- Column of the interpolation matrix after clearing its row denominators. -/
noncomputable def column (u v : ℕ → K) (h j : ℕ) : K[X] :=
  (∏ k ∈ range j, (X - C (u k))) *
  (∏ k ∈ range (h - j), (X - C (v (j + k))))

private theorem column_degree (u v : ℕ → K) {h j : ℕ} (hj : j ≤ h) :
    (column u v h j).natDegree ≤ h := by
  unfold column
  apply Polynomial.natDegree_mul_le.trans
  have deg (m : ℕ) (f : ℕ → K) :
      (∏ k ∈ range m, (X - C (f k))).natDegree ≤ m := by
    simp
  exact (add_le_add (deg j u) (deg (h - j) (fun k ↦ v (j + k)))).trans (by omega)

private theorem eval_matrix (h : ℕ) (p : Fin (h+1) → K[X])
    (hp : ∀ j, (p j).natDegree ≤ h) (x : Fin (h+1) → K) :
    Matrix.of (fun i j ↦ (p j).eval (x i)) =
      Matrix.vandermonde x * Matrix.of (fun (i j : Fin (h+1)) ↦ (p j).coeff i) := by
  ext i j
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.vandermonde_apply]
  rw [Polynomial.eval_eq_sum_range' (n := h+1) (by have := hp j; omega),
    ← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl fun k _ ↦ mul_comm _ _

/-- The cleared matrix has nonzero determinant as soon as the two entries used
on each diagonal are distinct and the evaluating grid is injective. -/
theorem column_det_ne_zero (h : ℕ) (u v : ℕ → K) (x : Fin (h+1) → K)
    (hx : Function.Injective x)
    (hu : ∀ i ≤ h, ∀ k < i, u i ≠ u k)
    (hv : ∀ i ≤ h, ∀ k, i ≤ k → k < h → u i ≠ v k) :
    (Matrix.of (fun (i j : Fin (h+1)) ↦ (column u v h j).eval (x i))).det ≠ 0 := by
  classical
  let p : Fin (h+1) → K[X] := fun j ↦ column u v h j
  let grid : Fin (h+1) → K := fun i ↦ u i
  let M := Matrix.of (fun (i j : Fin (h+1)) ↦ (p j).eval (grid i))
  have hp (j : Fin (h+1)) : (p j).natDegree ≤ h :=
    column_degree _ _ (by have := j.isLt; omega)
  have tri : M.IsLowerTriangular := by
    intro i j hij
    change i.val < j.val at hij
    simp only [M, Matrix.of_apply, p, grid, column, Polynomial.eval_mul, Polynomial.eval_prod,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    have hz : (∏ k ∈ range j.val, (u i.val - u k)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_range.mpr hij) (sub_self _)
    rw [hz, zero_mul]
  have diagonal (i : Fin (h+1)) : M i i ≠ 0 := by
    simp only [M, Matrix.of_apply, p, grid, column, Polynomial.eval_mul, Polynomial.eval_prod,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    have ih : i.val ≤ h := by have := i.isLt; omega
    apply mul_ne_zero
    · apply Finset.prod_ne_zero_iff.mpr
      exact fun k hk ↦ sub_ne_zero.mpr (hu i ih k (Finset.mem_range.mp hk))
    · apply Finset.prod_ne_zero_iff.mpr
      intro k hk
      have := Finset.mem_range.mp hk
      exact sub_ne_zero.mpr (hv i ih (i+k) (by omega) (by omega))
  have hM : M.det ≠ 0 := by
    rw [Matrix.det_of_isLowerTriangular M tri]
    exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ diagonal i
  change (Matrix.of (fun i j ↦ (p j).eval (grid i))).det ≠ 0 at hM
  rw [eval_matrix h p hp grid, Matrix.det_mul] at hM
  change (Matrix.of (fun i j ↦ (p j).eval (x i))).det ≠ 0
  rw [eval_matrix h p hp x, Matrix.det_mul]
  exact mul_ne_zero (Matrix.det_vandermonde_ne_zero_iff.mpr hx) (right_ne_zero_of_mul hM)


/-- Rising product, also over fields of finite characteristic. -/
noncomputable def rising (a : K) (j : ℕ) : K := ∏ k ∈ range j, (a + k)

private theorem rising_add (a : K) (i j : ℕ) :
    rising a (i+j) = rising a i * rising (a+i) j := by
  simp only [rising, Finset.prod_range_add, Nat.cast_add, add_assoc]

/-- The moments whose generating function is the truncated binomial series. -/
noncomputable def moment (a : K) (j : ℕ) : K := rising a j / rising 1 j

/-- The shifted binomial Hankel determinant over a field. Bounded nonvanishing
of rising products makes the formula meaningful in positive characteristic. -/
theorem binomial_hankel_ne_zero (h : ℕ) (a : K)
    (hx : Function.Injective (fun i : Fin (h+1) ↦ (i.val : K)))
    (ha : ∀ i : Fin (h+1), rising a (i+1) ≠ 0)
    (hd : ∀ m ≤ 2*h+1, rising (1 : K) m ≠ 0)
    (hgap : ∀ i ≤ h, ∀ k, i ≤ k → k < h → a + 1 + (i : K) ≠ 2 + (k : K)) :
    (Matrix.of (fun (i j : Fin (h+1)) ↦ moment a (i.val+j.val+1))).det ≠ 0 := by
  classical
  let x (i : Fin (h+1)) : K := i.val
  let u (k : ℕ) := -(a + 1 + (k : K))
  let v (k : ℕ) := -(2 + (k : K))
  let E := Matrix.of (fun (i j : Fin (h+1)) ↦ (column u v h j).eval (x i))
  let M := Matrix.of (fun (i j : Fin (h+1)) ↦ moment a (i.val+j.val+1))
  have hE : E.det ≠ 0 := by
    apply column_det_ne_zero h u v x hx
    · intro i hi k hk he
      have heq : (i : K) = (k : K) := by dsimp [u] at he; linear_combination -he
      have hf := hx (a₁ := ⟨i, by omega⟩) (a₂ := ⟨k, by omega⟩) heq
      have hsame : i = k := congrArg Fin.val hf
      omega
    · intro i hi k hik hk he
      exact hgap i hi k hik hk (neg_inj.mp he)
  let d₁ (i : Fin (h+1)) := moment a (i+1)
  let d₂ (i : Fin (h+1)) := rising ((i.val : K)+2) h
  have hmatrix : Matrix.diagonal d₁ * E = Matrix.diagonal d₂ * M := by
    ext i j
    simp only [Matrix.diagonal_mul, E, M, Matrix.of_apply, d₁, d₂, x, u, v, column,
      Polynomial.eval_mul, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C, sub_neg_eq_add, Nat.cast_add]
    have hj : j.val ≤ h := by have := j.isLt; omega
    have heval :
        (∏ k ∈ range j.val, ((i.val : K) + (a + 1 + k))) *
        (∏ k ∈ range (h-j.val), ((i.val : K) + (2 + ((j.val : K) + k)))) =
        rising (a+((i.val : K)+1)) j.val *
        rising ((i.val : K)+2+(j.val : K)) (h-j.val) := by
      unfold rising
      congr 1 <;> apply Finset.prod_congr rfl <;> intros <;> ring
    rw [heval]
    have hr := rising_add ((i.val : K)+2) j.val (h-j.val)
    rw [Nat.add_sub_of_le hj] at hr
    have hab := rising_add a (i.val+1) j.val
    have hdb := rising_add (1 : K) (i.val+1) j.val
    rw [show i.val+1+j.val = i.val+j.val+1 by omega] at hab hdb
    push_cast at hab hdb
    rw [show (1 : K) + ((i.val : K) + 1) = (i.val : K) + 2 by ring] at hdb
    have hi : i.val ≤ h := by have := i.isLt; omega
    have hd1 := hd (i.val+1) (by omega)
    have hd2 := hd (i.val+j.val+1) (by omega)
    simp only [moment]
    field_simp [hd1, hd2]
    rw [hab, hdb, hr]
    ring
  have hd₁ : (Matrix.diagonal d₁).det ≠ 0 := by
    rw [Matrix.det_diagonal]
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    have := i.isLt
    exact div_ne_zero (ha i) (hd (i.val+1) (by omega))
  have heq := congrArg Matrix.det hmatrix
  rw [Matrix.det_mul, Matrix.det_mul] at heq
  exact right_ne_zero_of_mul (heq ▸ mul_ne_zero hd₁ hE)

end ProximityGap.RationalObservableHankel

#print axioms ProximityGap.RationalObservableHankel.column_det_ne_zero

#print axioms ProximityGap.RationalObservableHankel.binomial_hankel_ne_zero
