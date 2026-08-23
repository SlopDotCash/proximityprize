/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations

/-!
# Top-coefficient of a finite product of polynomials (variable degree bounds)

Mathlib's `Polynomial.coeff_prod_of_natDegree_le` computes
`coeff (∏ f i) (#s * n) = ∏ coeff (f i) n` only for a **uniform** degree bound `n`
shared by all factors. The GK16 folded-Wronskian leading-term extraction needs the
**variable-bound** version: each factor `f i` carries its own bound `e i`, and the
coefficient of the product at the *sum* `∑ e i` equals the product of the factor
coefficients at `e i`.

This is the polynomial fact underlying "the coefficient of the top monomial of a
determinant of columns with distinct degrees is the determinant of the leading-term
matrix". It is proven here as a clean `Finset.induction`, sorry-free.

## Main statement

- `Polynomial.coeff_prod_sum_of_natDegree_le` —
  `coeff (∏ i ∈ s, f i) (∑ i ∈ s, e i) = ∏ i ∈ s, coeff (f i) (e i)`
  whenever `natDegree (f i) ≤ e i` for all `i ∈ s`.
-/

open Polynomial Finset

namespace Polynomial

variable {R : Type*} [CommSemiring R] {ι : Type*}

/-- **Top-coefficient of a product, variable degree bounds.** If each factor `f i`
(`i ∈ s`) has `natDegree (f i) ≤ e i`, then the coefficient of the product at the
total bound `∑ e i` is the product of the factor coefficients at their own bounds:

  `coeff (∏ i ∈ s, f i) (∑ i ∈ s, e i) = ∏ i ∈ s, coeff (f i) (e i)`.

This generalizes `Polynomial.coeff_prod_of_natDegree_le` (uniform `n`) to per-factor
bounds, which is exactly the shape needed to read off the leading term of a determinant
whose columns have *distinct* degrees. -/
theorem coeff_prod_sum_of_natDegree_le
    (f : ι → R[X]) (e : ι → ℕ) (s : Finset ι)
    (h : ∀ i ∈ s, (f i).natDegree ≤ e i) :
    coeff (∏ i ∈ s, f i) (∑ i ∈ s, e i) = ∏ i ∈ s, coeff (f i) (e i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.prod_insert ha]
    -- `coeff (f a * ∏ rest) (e a + ∑ rest e)`.
    have ha_deg : (f a).natDegree ≤ e a := h a (Finset.mem_insert_self a s)
    have hrest_deg : ∀ i ∈ s, (f i).natDegree ≤ e i := fun i hi =>
      h i (Finset.mem_insert_of_mem hi)
    -- Degree of the product of the rest is at most `∑ rest e`.
    have hprod_deg : (∏ i ∈ s, f i).natDegree ≤ ∑ i ∈ s, e i :=
      (natDegree_prod_le s f).trans (Finset.sum_le_sum hrest_deg)
    -- Compute the coefficient of the product at `e a + ∑ rest e` via `coeff_mul`,
    -- isolating the single antidiagonal cell `(e a, ∑ rest e)`.
    rw [coeff_mul]
    rw [Finset.sum_eq_single (e a, ∑ i ∈ s, e i)]
    · rw [ih hrest_deg]
    · rintro ⟨i, j⟩ hmem hne
      rw [Finset.mem_antidiagonal] at hmem
      simp only at hmem
      have hne' : i ≠ e a ∨ j ≠ ∑ i ∈ s, e i := by
        by_contra hc
        push Not at hc
        exact hne (by rw [hc.1, hc.2])
      -- Either `i > e a` (then `coeff (f a) i = 0`) or `j > ∑ rest e` (then the rest is 0).
      by_cases hi : e a < i
      · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt ha_deg hi), zero_mul]
      · push Not at hi
        -- `i ≤ e a` and `i + j = e a + ∑ rest e` force `j ≥ ∑ rest e`; `(i,j) ≠ peak` forces `>`.
        have hj : (∑ i ∈ s, e i) < j := by omega
        rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hprod_deg hj), mul_zero]
    · intro hcontra
      exact absurd (Finset.mem_antidiagonal.mpr (by simp)) hcontra

/-- **Leading coefficient of a finite product, at the natural total degree.** The coefficient of
`∏ i ∈ s, f i` at the sum `∑ i ∈ s, natDegree (f i)` of the factors' degrees equals the product
`∏ i ∈ s, leadingCoeff (f i)` of the factors' leading coefficients.

This is the `e i = natDegree (f i)` specialisation of `coeff_prod_sum_of_natDegree_le` (each
factor's own bound is its degree, and `coeff (f i) (natDegree (f i)) = leadingCoeff (f i)`), and is
exactly the diagonal-term computation underlying "the coefficient of the top monomial of a
determinant whose columns have distinct degrees is the determinant of the leading-term matrix". -/
theorem coeff_prod_sum_natDegree_eq_prod_leadingCoeff
    (f : ι → R[X]) (s : Finset ι) :
    coeff (∏ i ∈ s, f i) (∑ i ∈ s, (f i).natDegree) = ∏ i ∈ s, (f i).leadingCoeff := by
  rw [coeff_prod_sum_of_natDegree_le f (fun i => (f i).natDegree) s (fun _ _ => le_rfl)]
  rfl

end Polynomial
