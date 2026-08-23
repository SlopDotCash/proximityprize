/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Degree bounds for resultants and discriminants of bivariate polynomials

For `f, g : R[X][Y]` (polynomials in `Y` whose coefficients are polynomials in `X`), the
Sylvester matrix `sylvester f g m n` has entries among the `Y`-coefficients of `f` and `g`
(plus zeros), so if every coefficient has `X`-degree `≤ B` then the resultant — a determinant
of an `(m+n) × (m+n)` matrix of such entries — has `X`-degree `≤ (m+n)·B`:

* `Polynomial.natDegree_det_le` — determinant of any square matrix of polynomials with entry
  degrees `≤ B` has degree `≤ card · B`;
* `Polynomial.natDegree_resultant_le` — `natDegree (resultant f g m n) ≤ (m+n)·B`;
* `Polynomial.natDegree_discr_le` — `natDegree (discr f) ≤ (d-1+d)·B` for `d = natDegree f`,
  i.e. the classical `deg_X disc_Y(f) ≤ (2·deg_Y f − 1)·deg_X f`.

This is the degree half of **Step S5** of the Haböck §3 endgame
(`ArkLib/Data/CodingTheory/ProximityGap/Hab25Johnson.lean`): the `X`-degree of the
`Y`-discriminant of the Guruswami–Sudan interpolant over `K = F(Z)` is polynomially bounded
(paper: `deg_X disc_Y(Q) < ℓ²·ρn`), which feeds the common-nonvanishing-point argument in
`ArkLib/Data/CodingTheory/GuruswamiSudan/GSDiscriminantOverRatFunc.lean`.

All statements are Mathlib-only and `R` is an arbitrary commutative ring.

Axiom-clean: `[propext, Classical.choice, Quot.sound]`.
-/

open Polynomial.Bivariate

namespace Polynomial

variable {R : Type*} [CommRing R]

/-- **Determinant degree bound.** The determinant of a square matrix of polynomials whose
entries all have `natDegree ≤ B` has `natDegree ≤ card · B`: each permutation term is a
product of `card` entries (times a degree-`0` sign). -/
theorem natDegree_det_le {ι : Type*} [DecidableEq ι] [Fintype ι]
    (M : Matrix ι ι R[X]) {B : ℕ} (hM : ∀ i j, (M i j).natDegree ≤ B) :
    M.det.natDegree ≤ Fintype.card ι * B := by
  rw [Matrix.det_apply']
  refine natDegree_sum_le_of_forall_le _ _ fun σ _ => ?_
  refine natDegree_mul_le.trans ?_
  rw [natDegree_intCast, zero_add]
  refine (natDegree_prod_le _ _).trans ?_
  calc ∑ i, (M (σ i) i).natDegree
      ≤ ∑ _i : ι, B := Finset.sum_le_sum fun i _ => hM _ _
    _ = Fintype.card ι * B := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

/-- Every entry of the Sylvester matrix of `f, g : R[X][Y]` is `0` or a `Y`-coefficient of
`f` or `g`; in particular its `X`-degree is bounded by any common coefficient bound `B`. -/
theorem natDegree_sylvester_apply_le (f g : R[X][Y]) (m n : ℕ) {B : ℕ}
    (hf : ∀ k, (f.coeff k).natDegree ≤ B) (hg : ∀ k, (g.coeff k).natDegree ≤ B)
    (i j : Fin (m + n)) : ((sylvester f g m n) i j).natDegree ≤ B := by
  simp only [sylvester, Matrix.of_apply]
  induction j using Fin.addCases with
  | left j₁ =>
      rw [Fin.addCases_left]
      split_ifs
      · exact hg _
      · simp
  | right j₁ =>
      rw [Fin.addCases_right]
      split_ifs
      · exact hf _
      · simp

/-- **Resultant degree bound.** If every `Y`-coefficient of `f, g : R[X][Y]` has
`X`-degree `≤ B`, then `resultant f g m n` (an `(m+n) × (m+n)` Sylvester determinant)
has `X`-degree `≤ (m+n)·B`. -/
theorem natDegree_resultant_le (f g : R[X][Y]) (m n : ℕ) {B : ℕ}
    (hf : ∀ k, (f.coeff k).natDegree ≤ B) (hg : ∀ k, (g.coeff k).natDegree ≤ B) :
    (resultant f g m n).natDegree ≤ (m + n) * B := by
  rw [resultant]
  simpa [Fintype.card_fin] using
    natDegree_det_le (sylvester f g m n) (natDegree_sylvester_apply_le f g m n hf hg)

/-- The `Y`-coefficients of `derivative f` inherit any common `X`-degree bound on the
`Y`-coefficients of `f` (each is `(k+1) · coeff f (k+1)`, and the scalar has degree `0`). -/
theorem natDegree_coeff_derivative_le (f : R[X][Y]) {B : ℕ}
    (hf : ∀ k, (f.coeff k).natDegree ≤ B) (k : ℕ) :
    ((derivative f).coeff k).natDegree ≤ B := by
  rw [coeff_derivative]
  refine natDegree_mul_le.trans ?_
  have h1 : ((k : R[X]) + 1).natDegree = 0 := by
    rw [← Nat.cast_add_one, natDegree_natCast]
  rw [h1, add_zero]
  exact hf (k + 1)

/-- Every entry of `sylvesterDeriv f` (the discriminant's Sylvester matrix) has `X`-degree
bounded by any common bound `B` on the `Y`-coefficients of `f`: the entries are coefficients
of `f`, coefficients of `derivative f`, or the scalars `0`, `1`, `natDegree f`. -/
theorem natDegree_sylvesterDeriv_apply_le (f : R[X][Y]) {B : ℕ}
    (hf : ∀ k, (f.coeff k).natDegree ≤ B)
    (i j : Fin (f.natDegree - 1 + f.natDegree)) :
    ((sylvesterDeriv f) i j).natDegree ≤ B := by
  rw [sylvesterDeriv]
  split_ifs with hn
  · simp
  · rw [Matrix.updateRow_apply]
    split_ifs with hi h1 h2
    · simp
    · simp [natDegree_natCast]
    · simp
    · exact natDegree_sylvester_apply_le (derivative f) f _ _
        (natDegree_coeff_derivative_le f hf) hf i j

/-- **Discriminant degree bound** (the S5 degree estimate). If every `Y`-coefficient of
`f : R[X][Y]` has `X`-degree `≤ B`, then with `d := natDegree f` (the `Y`-degree),

  `natDegree (discr f) ≤ (d - 1 + d) · B`,

i.e. the classical `deg_X disc_Y(f) ≤ (2·deg_Y(f) − 1) · deg_X(f)`. -/
theorem natDegree_discr_le (f : R[X][Y]) {B : ℕ}
    (hf : ∀ k, (f.coeff k).natDegree ≤ B) :
    (discr f).natDegree ≤ (f.natDegree - 1 + f.natDegree) * B := by
  rw [discr]
  refine natDegree_mul_le.trans ?_
  have h1 : ((-1 : R[X]) ^ (f.natDegree * (f.natDegree - 1) / 2)).natDegree = 0 :=
    Nat.le_zero.mp (natDegree_pow_le.trans (by simp))
  rw [h1, add_zero]
  simpa [Fintype.card_fin] using
    natDegree_det_le (sylvesterDeriv f) (natDegree_sylvesterDeriv_apply_le f hf)

end Polynomial

/-! ## Axiom audit — all kernel-clean. -/
#print axioms Polynomial.natDegree_det_le
#print axioms Polynomial.natDegree_sylvester_apply_le
#print axioms Polynomial.natDegree_resultant_le
#print axioms Polynomial.natDegree_coeff_derivative_le
#print axioms Polynomial.natDegree_sylvesterDeriv_apply_le
#print axioms Polynomial.natDegree_discr_le
