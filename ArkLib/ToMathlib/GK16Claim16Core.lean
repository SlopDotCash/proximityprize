/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Determinant column-divisibility core for GK16 Claim 16

The combinatorial heart of GK16 Claim 16 (the multiplicity-lower-bound half of the
folded-Wronskian degree budget) is a purely linear-algebraic fact about determinants:

  **If a common factor `g` divides every entry of each column in a subset `T`, then
  `g ^ |T|` divides the determinant.**

This factors `g` out of each of the `|T|` columns by column-multilinearity
(`Matrix.det_mul_row`, which scales columns). We package the two consequences GK16 needs:

* `pow_dvd_det_of_col_dvd` — the generic ring statement `g ^ |T| ∣ det M`;
* `le_rootMultiplicity_det_of_col_dvd` — its specialisation to `g = X - C a` over a
  polynomial ring, giving `|T| ≤ rootMultiplicity a (det M)` (when `det M ≠ 0`), which is
  exactly the per-point multiplicity bound `rootMultiplicity a L ≥ dim A_i` once `T` is the
  index set of an `A_i`-adapted basis.

Everything here is `sorry`/axiom-clean.
-/

open Polynomial Matrix

namespace ArkLib.FRS.GK16

/-- **Common column factor ⟹ power divides the determinant.** Let `M` be an `n × n`
matrix over a commutative ring `R`, `T ⊆ n` a set of column indices, and `g : R` a ring
element dividing *every* entry in *every* column of `T` (`∀ j ∈ T, ∀ i, g ∣ M i j`). Then
`g ^ |T|` divides `det M`.

Proof: build `N` with `M i j = (if j ∈ T then g else 1) * N i j` (choosing the cofactor
`N i j` from the divisibility witness when `j ∈ T`, and `N i j = M i j` otherwise). Then
`det M = (∏ j, if j ∈ T then g else 1) * det N = g ^ |T| * det N` by the column-scaling
determinant identity `Matrix.det_mul_row`. -/
theorem pow_dvd_det_of_col_dvd {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [CommRing R] (M : Matrix n n R) (T : Finset n) (g : R)
    (h : ∀ j ∈ T, ∀ i, g ∣ M i j) :
    g ^ T.card ∣ M.det := by
  classical
  -- Cofactor: `N i j = M i j / g` (a chosen witness) for `j ∈ T`, else `M i j`.
  set N : Matrix n n R := Matrix.of fun i j =>
    if hj : j ∈ T then (h j hj i).choose else M i j with hN
  -- The column-scaling vector: `g` on `T`, `1` off `T`.
  set v : n → R := fun j => if j ∈ T then g else 1 with hv
  -- Reconstruct `M` columnwise as `M i j = v j * N i j`.
  have hMrec : M = Matrix.of fun i j => v j * N i j := by
    funext i j
    simp only [hN, hv, Matrix.of_apply]
    by_cases hj : j ∈ T
    · rw [if_pos hj, dif_pos hj]
      exact (h j hj i).choose_spec
    · rw [if_neg hj, dif_neg hj, one_mul]
  -- Determinant scales by the product of the column factors.
  rw [hMrec, Matrix.det_mul_row]
  -- The product of the column factors is `g ^ |T|`.
  have hprod : (∏ j, v j) = g ^ T.card := by
    rw [hv]
    rw [Finset.prod_ite_mem Finset.univ T (fun _ => g)]
    simp [Finset.univ_inter, Finset.prod_const]
  rw [hprod]
  exact dvd_mul_right _ _

/-- **GK16 Claim 16 core (polynomial specialisation).** Over a polynomial ring `R[X]`, if
`(X - C a)` divides every entry of each column in a set `T` of a (nonzero-determinant)
matrix `M`, then `rootMultiplicity a (det M) ≥ |T|`.

This is `pow_dvd_det_of_col_dvd` (with `g = X - C a`) fed into
`Polynomial.le_rootMultiplicity_iff` (`n ≤ rootMultiplicity a p ↔ (X - C a) ^ n ∣ p`).
Setting `T` to the index set of a basis of `A_i = A ⊓ ker(eval_i)` adapted inside the
folded-Wronskian column family yields exactly Claim 16's
`rootMultiplicity (domain i) L ≥ dim A_i`. -/
theorem le_rootMultiplicity_det_of_col_dvd {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [CommRing R] [IsDomain R]
    (M : Matrix n n R[X]) (T : Finset n) (a : R)
    (hdet : M.det ≠ 0)
    (h : ∀ j ∈ T, ∀ i, (X - C a) ∣ M i j) :
    T.card ≤ rootMultiplicity a M.det :=
  (Polynomial.le_rootMultiplicity_iff hdet).mpr
    (pow_dvd_det_of_col_dvd M T (X - C a) h)

end ArkLib.FRS.GK16
