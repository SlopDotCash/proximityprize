/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.WronskianGeneral
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# Sparse-polynomial (lacunary) multiplicity bound (#389, Stepanov route)

A polynomial with `m` nonzero terms vanishes to order at most `m − 1` at any nonzero point
(over a field where the exponents stay distinct — e.g. characteristic `0` or characteristic
exceeding the degree).  This is a classical fact — the "Descartes bound" / confluent-Vandermonde
nonvanishing — that **Mathlib does not have**, and it is the engine that drives the linear
independence of the Garcia–Voloch / Heath-Brown–Konyagin Stepanov generators in the genuine
`n ∣ p − 1` split case (Shkredov–Vyugin Lemma 3.1), **without** the bracket induction or the
`W = 0 ⟹ dependent` converse:

> grouping the generators `x^{a+t·b₀}(x−α)^{t·b₁}` by their `(x−α)`-power `b₁` writes a
> dependence as `∑_{β} (x−α)^{tβ} P_β(x) = 0` with each `P_β` a `≤ DB`-sparse polynomial in `x`;
> this bound gives `ord_α P_β ≤ DB − 1 < t`, so the `(x−α)`-valuations `tβ + ord_α P_β` lie in
> disjoint length-`t` blocks — no cancellation is possible, forcing every `P_β = 0`.

The development:

* `evalDerivMatrix_det_ne_zero` — the **confluent Vandermonde at one point**: the matrix of
  `i`-th derivatives of `x^{e_k}` evaluated at `α ≠ 0` has determinant
  `(∏_{i<j}(e_j − e_i)) · α^{∑ e − C(m,2)}`, hence is nonzero when the exponents are distinct.
* `eq_zero_of_pow_dvd_sparse` — **the engine**: `(X − α)^m ∣ ∑_k c_k X^{e_k}` forces `c = 0`.
* `rootMultiplicity_sparse_lt` — **the clean form**: a nonzero `m`-term polynomial has
  `rootMultiplicity α < m` at any nonzero `α`.
-/

open Polynomial Matrix Finset

namespace ArkLib.ProximityGap.Wronskian

variable {R : Type*} [Field R] {m : ℕ}

/-- **The confluent Vandermonde at a single nonzero point.** The matrix whose `(i, k)` entry is
the `i`-th derivative of the monomial `X^{e_k}` evaluated at `α`, namely
`descFactorial(e_k, i) · α^{e_k − i}`, has nonzero determinant whenever `α ≠ 0` and the
exponents `e` are distinct in `R` (i.e. the ordinary Vandermonde of the `e_k` is nonzero).
Proof: scaling row `i` by `α^i` and column `k` by `α^{-e_k}` turns it into the matrix
`(descPochhammer R i).eval (e_k)`, whose determinant is the Vandermonde determinant. -/
theorem evalDerivMatrix_det_ne_zero (e : Fin m → ℕ) (α : R) (hα : α ≠ 0)
    (hvand : (Matrix.vandermonde (fun k => (e k : R))).det ≠ 0) :
    (Matrix.of (fun (i k : Fin m) =>
      ((e k).descFactorial (i:ℕ) : R) * α ^ ((e k) - (i:ℕ)))).det ≠ 0 := by
  set B : Matrix (Fin m) (Fin m) R :=
    Matrix.of (fun (i k : Fin m) => ((e k).descFactorial (i:ℕ) : R) * α ^ ((e k) - (i:ℕ))) with hB
  set MP : Matrix (Fin m) (Fin m) R :=
    Matrix.of (fun (i k : Fin m) => (descPochhammer R (i:ℕ)).eval ((e k : ℕ) : R)) with hMP
  -- `diag(α^i) * B = MP * diag(α^{e_k})`.
  have hkey : (Matrix.diagonal (fun i : Fin m => α ^ (i:ℕ))) * B
      = MP * (Matrix.diagonal (fun k : Fin m => α ^ (e k))) := by
    ext i k
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal, hB, hMP, Matrix.of_apply, Matrix.of_apply,
      descPochhammer_eval_eq_descFactorial]
    by_cases hle : (i:ℕ) ≤ e k
    · rw [show α ^ (i:ℕ) * (((e k).descFactorial i : R) * α ^ ((e k) - (i:ℕ)))
          = ((e k).descFactorial i : R) * (α ^ (i:ℕ) * α ^ ((e k) - (i:ℕ))) by ring,
        ← pow_add, Nat.add_sub_cancel' hle, mul_comm]
    · have hz : (e k).descFactorial (i:ℕ) = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
      rw [hz]; push_cast; ring
  have hdet : (∏ i : Fin m, α ^ (i:ℕ)) * B.det = MP.det * (∏ k : Fin m, α ^ (e k)) := by
    have := congrArg Matrix.det hkey
    rwa [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal] at this
  have hMPdet : MP.det = (Matrix.vandermonde (fun k => (e k : R))).det := by
    have hpoly := Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde
      (fun k => ((e k : ℕ) : R)) (fun i => descPochhammer R (i:ℕ))
      (fun i => descPochhammer_natDegree (R := R) (i:ℕ))
      (fun i => monic_descPochhammer (R := R) (i:ℕ))
    rw [← Matrix.det_transpose MP, hpoly]; congr 1
  have hRneq : MP.det * (∏ k : Fin m, α ^ (e k)) ≠ 0 := by
    rw [hMPdet]
    exact mul_ne_zero hvand (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ hα)
  intro hBzero
  rw [hBzero, mul_zero] at hdet
  exact hRneq hdet.symm

/-- **The `m`-sparse multiplicity engine**: if a sum of `m` monomials with distinct exponents
(nonzero Vandermonde over `R`) is divisible by `(X − α)^m` at a nonzero `α`, every coefficient is
zero.  The order-`m` vanishing makes the coefficient vector lie in the kernel of the (nonzero)
confluent Vandermonde `evalDerivMatrix`. -/
theorem eq_zero_of_pow_dvd_sparse (e : Fin m → ℕ) (c : Fin m → R) (α : R) (hα : α ≠ 0)
    (hvand : (Matrix.vandermonde (fun k => (e k : R))).det ≠ 0)
    (hdvd : (X - C α) ^ m ∣ ∑ k, C (c k) * X ^ (e k)) : c = 0 := by
  set B : Matrix (Fin m) (Fin m) R :=
    Matrix.of (fun (i k : Fin m) => ((e k).descFactorial (i:ℕ) : R) * α ^ ((e k) - (i:ℕ))) with hB
  have hBc : B.mulVec c = 0 := by
    funext i
    -- the `i`-th derivative of `P` is still divisible by `(X − α)`, so it vanishes at `α`.
    have hd : (X - C α) ∣ (Polynomial.derivative^[(i:ℕ)]) (∑ k, C (c k) * X ^ (e k)) := by
      have hdd := pow_sub_dvd_iterate_derivative hdvd (i:ℕ)
      have hne : m - (i:ℕ) ≠ 0 := by have := i.isLt; omega
      exact dvd_trans (dvd_pow_self (X - C α) hne) hdd
    have heval : ((Polynomial.derivative^[(i:ℕ)]) (∑ k, C (c k) * X ^ (e k))).eval α = 0 :=
      Polynomial.dvd_iff_isRoot.mp hd
    rw [Pi.zero_apply, Matrix.mulVec, dotProduct]
    rw [iterate_derivative_sum, Polynomial.eval_finset_sum] at heval
    rw [← heval]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [iterate_derivative_C_mul, iterate_derivative_X_pow_eq_C_mul, hB, Matrix.of_apply,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    ring
  exact Matrix.eq_zero_of_mulVec_eq_zero (evalDerivMatrix_det_ne_zero e α hα hvand) hBc

/-- **The sparse multiplicity bound (clean form)**: a nonzero polynomial that is a sum of `m`
monomials with distinct exponents (nonzero Vandermonde over `R`) has root multiplicity strictly
less than `m` at any nonzero point.  This is the input the Stepanov valuation-grouping argument
consumes: a `≤ DB`-sparse `P_β` cannot vanish to order `t > DB − 1` at `α ≠ 0`. -/
theorem rootMultiplicity_sparse_lt (e : Fin m → ℕ) (c : Fin m → R) (α : R) (hα : α ≠ 0)
    (hvand : (Matrix.vandermonde (fun k => (e k : R))).det ≠ 0)
    (hP : (∑ k, C (c k) * X ^ (e k)) ≠ 0) :
    rootMultiplicity α (∑ k, C (c k) * X ^ (e k)) < m := by
  by_contra h
  rw [not_lt] at h
  refine hP ?_
  have hdvd : (X - C α) ^ m ∣ (∑ k, C (c k) * X ^ (e k)) :=
    dvd_trans (pow_dvd_pow _ h) (pow_rootMultiplicity_dvd _ _)
  rw [eq_zero_of_pow_dvd_sparse e c α hα hvand hdvd]
  simp

end ArkLib.ProximityGap.Wronskian
