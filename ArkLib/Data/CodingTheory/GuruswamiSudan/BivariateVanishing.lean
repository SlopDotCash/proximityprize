/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliza
-/

import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Bivariate

/-!
# Bivariate multiplicity-vanishing API on `F[X][Y]` (Guruswami–Sudan substitution step)

This file develops the load-bearing "order-`m` vanishing implies substitution multiplicity"
step of the Guruswami–Sudan list-decoding chain (BCHKS25 §A, GS99 Lemma 4), formalized
directly on Mathlib's nested bivariate surface `F[X][Y] = Polynomial (Polynomial F)` where
`Y` is the *outer* variable and `X` lives inside the coefficients.

## Design

For a bivariate `Q : F[X][Y]` and a point `(a, b) : F × F`, the order-`m` vanishing condition
is phrased through the **outer Taylor shift** `taylor (C b) Q : F[X][Y]`, whose `j`-th
`Y`-coefficient `(taylor (C b) Q).coeff j : F[X]` is the inner univariate polynomial collecting
all bidegree-`(·, j)` Taylor data of `Q` around `(a, b)`. We say `Q` vanishes to order `m` at
`(a, b)` when, for every `j`, that inner coefficient is divisible by `(X - C a) ^ (m - j)`, i.e.
its order-`(m - j)` vanishing at `a`.

* `vanishesToOrder` — the order-`m` vanishing predicate (the divisibility form).
* `hasseCoeff` — the bivariate Hasse–Taylor coefficient
  `(hasseDeriv i ((taylor (C b) Q).coeff j)).eval a`, and `hasseCoeff_isLinear` /
  `hasseCoeffLinearMap` showing `Q ↦ hasseCoeff …` is `F`-**linear**.
* `vanishesToOrder_iff_hasseCoeff` — the predicate is equivalent to the vanishing of all
  Hasse–Taylor coefficients of bidegree `i + j < m` (the linear-conditions form).
* `vanishesToOrder.dvd_eval` and `vanishesToOrder.le_rootMultiplicity_eval` — the **substitution
  lemma**: if `Q` vanishes to order `m` at `(a, b)` and `p : F[X]` satisfies `p.eval a = b`, then
  `(X - C a) ^ m ∣ Q.eval p`, hence `m ≤ rootMultiplicity a (Q.eval p)` (when `Q.eval p ≠ 0`).

All proofs are kernel-checked; the only axioms used are `propext`, `Classical.choice`, `Quot.sound`.
-/

open Polynomial

namespace ArkLib.GS

noncomputable section

variable {F : Type*}

/-- The `j`-th inner Taylor coefficient of `Q : F[X][Y]` around the point `(a, b)`:
the `Y`-coefficient of the outer Taylor shift `taylor (C b) Q`, an element of `F[X]`. -/
def innerTaylorCoeff [CommRing F] (Q : Polynomial (Polynomial F)) (b : F) (j : ℕ) : Polynomial F :=
  (taylor (C b) Q).coeff j

/-- `Q : F[X][Y]` **vanishes to order `m` at `(a, b)`** when, for every `Y`-index `j`, the inner
Taylor coefficient `(taylor (C b) Q).coeff j : F[X]` is divisible by `(X - C a) ^ (m - j)`.

Equivalently (`vanishesToOrder_iff_hasseCoeff`), every bivariate Hasse–Taylor coefficient of
bidegree `i + j < m` evaluates to `0` at `(a, b)`. -/
def vanishesToOrder [CommRing F] (m : ℕ) (Q : Polynomial (Polynomial F)) (a b : F) : Prop :=
  ∀ j : ℕ, (X - C a) ^ (m - j) ∣ innerTaylorCoeff Q b j

/-- The bivariate Hasse–Taylor coefficient of bidegree `(i, j)` of `Q` at `(a, b)`:
take the `j`-th outer Taylor coefficient `(taylor (C b) Q).coeff j : F[X]`, apply the `i`-th
(inner) Hasse derivative, and evaluate at `a`. By `taylor_coeff` this equals the `(i, j)`
bivariate Taylor coefficient. -/
def hasseCoeff [CommRing F] (i j : ℕ) (Q : Polynomial (Polynomial F)) (a b : F) : F :=
  (hasseDeriv i (innerTaylorCoeff Q b j)).eval a

section Linear

variable [CommRing F]

/-- `innerTaylorCoeff · b j` is additive in `Q`. -/
@[simp] lemma innerTaylorCoeff_add (Q₁ Q₂ : Polynomial (Polynomial F)) (b : F) (j : ℕ) :
    innerTaylorCoeff (Q₁ + Q₂) b j = innerTaylorCoeff Q₁ b j + innerTaylorCoeff Q₂ b j := by
  simp only [innerTaylorCoeff, map_add, coeff_add]

/-- `innerTaylorCoeff · b j` commutes with scalar multiplication in `Q`. -/
@[simp] lemma innerTaylorCoeff_smul (c : F) (Q : Polynomial (Polynomial F)) (b : F) (j : ℕ) :
    innerTaylorCoeff (c • Q) b j = c • innerTaylorCoeff Q b j := by
  -- `taylor (C b)` is `F`-linear via the scalar tower `F → F[X] → F[X][Y]`.
  rw [innerTaylorCoeff, innerTaylorCoeff, LinearMap.map_smul_of_tower, coeff_smul]

@[simp] lemma innerTaylorCoeff_zero (b : F) (j : ℕ) :
    innerTaylorCoeff (0 : Polynomial (Polynomial F)) b j = 0 := by
  simp only [innerTaylorCoeff, map_zero, coeff_zero]

/-- The bivariate Hasse–Taylor coefficient map `Q ↦ hasseCoeff i j Q a b` is `F`-**linear**:
the order-`m` vanishing conditions are linear constraints on `Q`. -/
lemma hasseCoeff_isLinear (i j : ℕ) (a b : F) :
    (∀ Q₁ Q₂, hasseCoeff i j (Q₁ + Q₂) a b = hasseCoeff i j Q₁ a b + hasseCoeff i j Q₂ a b) ∧
      (∀ (c : F) Q, hasseCoeff i j (c • Q) a b = c • hasseCoeff i j Q a b) := by
  refine ⟨fun Q₁ Q₂ => ?_, fun c Q => ?_⟩
  · simp only [hasseCoeff, innerTaylorCoeff_add, map_add, eval_add]
  · simp only [hasseCoeff, innerTaylorCoeff_smul, map_smul, eval_smul, smul_eq_mul]

/-- The bivariate Hasse–Taylor coefficient packaged as an honest `F`-linear map
`F[X][Y] →ₗ[F] F`. -/
@[simps] def hasseCoeffLinearMap (i j : ℕ) (a b : F) :
    Polynomial (Polynomial F) →ₗ[F] F where
  toFun Q := hasseCoeff i j Q a b
  map_add' := (hasseCoeff_isLinear i j a b).1
  map_smul' := (hasseCoeff_isLinear i j a b).2

end Linear

section Characterization

variable [CommRing F]

/-- The Hasse–Taylor coefficient is the corresponding coefficient of the inner Taylor expansion. -/
lemma hasseCoeff_eq_innerTaylorCoeff_taylor (i j : ℕ) (Q : Polynomial (Polynomial F)) (a b : F) :
    hasseCoeff i j Q a b = (taylor a (innerTaylorCoeff Q b j)).coeff i := by
  rw [hasseCoeff, taylor_coeff]

/-- The Taylor shift sends `X - C a` to `X`; the key normalization for the dvd characterization. -/
lemma taylor_X_sub_C (a : F) : taylor a (X - C a) = X := by
  rw [map_sub, taylor_X, taylor_C, add_sub_cancel_right]

/-- `(X - C a) ^ n` divides a univariate `c` iff `X ^ n` divides its Taylor shift `taylor a c`,
since `taylorEquiv a` is a ring automorphism sending `X - C a` to `X`. -/
lemma X_sub_C_pow_dvd_iff_X_pow_dvd_taylor (n : ℕ) (c : Polynomial F) (a : F) :
    (X - C a) ^ n ∣ c ↔ X ^ n ∣ taylor a c := by
  rw [← map_dvd_iff (taylorEquiv a)]
  have h1 : (taylorEquiv a) ((X - C a) ^ n) = X ^ n := by
    rw [map_pow]
    congr 1
    rw [show (taylorEquiv a) (X - C a) = taylor a (X - C a) from rfl, taylor_X_sub_C]
  have h2 : (taylorEquiv a) c = taylor a c := rfl
  rw [h1, h2]

/-- The order-`(m-j)` vanishing of the `j`-th inner Taylor coefficient is equivalent to the
vanishing of its Hasse–Taylor coefficients of inner-degree `i < m - j`. This is the bridge from
the divisibility form of `vanishesToOrder` to the *linear-conditions* form: `(X - C a)^n` divides
`c` iff the Taylor expansion of `c` at `a` has no terms of degree below `n`. -/
lemma dvd_innerTaylorCoeff_iff (m j : ℕ) (Q : Polynomial (Polynomial F)) (a b : F) :
    (X - C a) ^ (m - j) ∣ innerTaylorCoeff Q b j ↔
      ∀ i < m - j, hasseCoeff i j Q a b = 0 := by
  rw [X_sub_C_pow_dvd_iff_X_pow_dvd_taylor, X_pow_dvd_iff]
  simp only [hasseCoeff_eq_innerTaylorCoeff_taylor]

/-- **Linear-conditions form of order-`m` vanishing.** `Q` vanishes to order `m` at `(a, b)` iff
every bivariate Hasse–Taylor coefficient of bidegree `i + j < m` vanishes at `(a, b)`. The right
side is a finite family of `F`-linear constraints on `Q` (`hasseCoeffLinearMap`). -/
theorem vanishesToOrder_iff_hasseCoeff (m : ℕ) (Q : Polynomial (Polynomial F)) (a b : F) :
    vanishesToOrder m Q a b ↔ ∀ i j, i + j < m → hasseCoeff i j Q a b = 0 := by
  unfold vanishesToOrder
  constructor
  · intro h i j hij
    exact (dvd_innerTaylorCoeff_iff m j Q a b).mp (h j) i (by omega)
  · intro h j
    rw [dvd_innerTaylorCoeff_iff]
    intro i hi
    exact h i j (by omega)

end Characterization

section Substitution

variable [CommRing F]

/-- Substitution evaluation: evaluating the outer `Y` of `Q : F[X][Y]` at `p : F[X]` equals
evaluating the outer Taylor shift `taylor (C b) Q` at `p - C b`. -/
lemma eval_eq_eval_taylor (Q : Polynomial (Polynomial F)) (b : F) (p : Polynomial F) :
    Q.eval p = (taylor (C b) Q).eval (p - C b) := by
  rw [taylor_eval, sub_add_cancel]

/-- **Substitution lemma (divisibility form).** If `Q` vanishes to order `m` at `(a, b)` and
`p : F[X]` satisfies `p.eval a = b`, then `(X - C a) ^ m` divides the univariate substitution
`Q.eval p`. This is GS99 Lemma 4 / BCHKS25 §A, the load-bearing multiplicity-transfer step. -/
theorem vanishesToOrder.dvd_eval {m : ℕ} {Q : Polynomial (Polynomial F)} {a b : F}
    (h : vanishesToOrder m Q a b) (p : Polynomial F) (hp : p.eval a = b) :
    (X - C a) ^ m ∣ Q.eval p := by
  -- `g = Q.eval p = T.eval (p - C b)` where `T = taylor (C b) Q`.
  rw [eval_eq_eval_taylor Q b p]
  set T := taylor (C b) Q with hT
  -- Expand as a finite sum of `T.coeff j * (p - C b) ^ j`.
  rw [eval_eq_sum_range]
  -- `(X - C a) ∣ p - C b` since `(p - C b).eval a = 0`.
  have hroot : (X - C a) ∣ p - C b := by
    have := X_sub_C_dvd_sub_C_eval (a := a) (p := p)
    rwa [hp] at this
  refine Finset.dvd_sum ?_
  intro j _
  -- `(X - C a)^(m - j) ∣ T.coeff j` from vanishing; `(X - C a)^j ∣ (p - C b)^j`.
  have h1 : (X - C a) ^ (m - j) ∣ T.coeff j := h j
  have h2 : (X - C a) ^ j ∣ (p - C b) ^ j := pow_dvd_pow_of_dvd hroot j
  have h3 : (X - C a) ^ ((m - j) + j) ∣ T.coeff j * (p - C b) ^ j := by
    rw [pow_add]; exact mul_dvd_mul h1 h2
  exact dvd_trans (pow_dvd_pow _ (by omega)) h3

/-- **Substitution lemma (multiplicity form).** Under the same hypotheses, if the substitution
`Q.eval p` is nonzero then `a` is a root of `Q.eval p` of multiplicity at least `m`. -/
theorem vanishesToOrder.le_rootMultiplicity_eval {m : ℕ} {Q : Polynomial (Polynomial F)}
    {a b : F} (h : vanishesToOrder m Q a b) (p : Polynomial F) (hp : p.eval a = b)
    (hne : Q.eval p ≠ 0) :
    m ≤ rootMultiplicity a (Q.eval p) :=
  (le_rootMultiplicity_iff hne).mpr (h.dvd_eval p hp)

end Substitution

end

end ArkLib.GS
