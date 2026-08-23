/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib
import CompPoly.ToMathlib.Polynomial.BivariateDegree

/-!
# Polynomial Representation of Finitely Supported Power Series

This module establishes the algebraic correspondence between finitely supported power series
and polynomials, and analyzes the degree properties of their bivariate representatives.
This provides the mathematical foundation for showing that truncated solutions to algebraic
equations over power series correspond to honest bivariate polynomials with bounded degree.

## Mathematical Formulation

Let $k$ be a commutative ring. A power series $\varphi \in k[[X]]$ is finitely supported if
there exists $N \in \mathbb{N}$ such that for all $n \ge N$, the coefficient
$\text{coeff}_n(\varphi) = 0$.
Under this condition, $\varphi$ coincides with its truncation polynomial:
$$P(X) = \sum_{i=0}^{N-1} \text{coeff}_i(\varphi) X^i \in k[X]$$

In the bivariate setting, let $F$ be a field and $P \in F[X][Y]$ be a bivariate polynomial. We
relate the
degree bounds of the coefficients $P_n(X) \in F[X]$ to the total degree properties. Specifically,
we formalize that the bivariate degree satisfies $\text{degree}_X(P) \le 1$ if and only if
every coefficient polynomial has degree at most 1, which allows us to decompose $P$ as:
$$P(X,Y) = v_0(Y) + X \cdot v_1(Y)$$
for some polynomials $v_0, v_1$.

## Key Formalizations
* `truncPoly`: The canonical polynomial truncation of a power series.
* `exists_polynomial_coe_of_coeff_eq_zero_ge`: Realizes the equivalence between finitely supported
power series and polynomials.
* `exists_linear_decomposition_of_degreeX_le_one`: Proves that a bivariate polynomial of degree at
most 1 in $X$ decomposes linearly.
-/

open Polynomial
open scoped Polynomial.Bivariate

namespace ArkLib

namespace FiniteSeriesToPoly

/-! ## Part 1: `PowerSeries` with finite support ⟹ `Polynomial` -/

section Univariate

variable {k : Type*} [CommRing k]

/-- The finite truncation of a power series $\varphi$ at degree $N$, viewed as a polynomial. -/
noncomputable def truncPoly (φ : PowerSeries k) (N : ℕ) : k[X] :=
  ∑ i ∈ Finset.range N, Polynomial.C (PowerSeries.coeff i φ) * X ^ i

/-- The coefficients of the truncation polynomial. -/
theorem coeff_truncPoly (φ : PowerSeries k) (N n : ℕ) :
    (truncPoly φ N).coeff n =
      if n < N then PowerSeries.coeff n φ else 0 := by
  classical
  unfold truncPoly
  rw [Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one,
    mul_zero]
  by_cases hn : n < N
  · rw [if_pos hn]
    rw [Finset.sum_eq_single n]
    · simp
    · intro b _ hbn
      rw [if_neg (by omega)]
    · intro hmem
      exact absurd (Finset.mem_range.mpr hn) hmem
  · rw [if_neg hn]
    apply Finset.sum_eq_zero
    intro b hb
    have : b < N := Finset.mem_range.mp hb
    rw [if_neg (by omega)]

/-- The degree of the truncation polynomial is strictly bounded by $N$ for positive $N$. -/
theorem natDegree_truncPoly_lt (φ : PowerSeries k) {N : ℕ} (hN : 0 < N) :
    (truncPoly φ N).natDegree < N := by
  classical
  rw [Nat.lt_iff_le_pred hN, Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  rw [coeff_truncPoly]
  rw [if_neg (by omega)]

/-- The degree of the truncation polynomial is bounded by $N - 1$. -/
theorem natDegree_truncPoly_le (φ : PowerSeries k) (N : ℕ) :
    (truncPoly φ N).natDegree ≤ N - 1 := by
  classical
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  rw [coeff_truncPoly]
  rw [if_neg (by omega)]

/-- A finitely supported power series is equal to the canonical coercion of its truncation
polynomial. -/
theorem coe_truncPoly_eq_of_coeff_eq_zero_ge (φ : PowerSeries k) {N : ℕ}
    (h : ∀ n, N ≤ n → PowerSeries.coeff n φ = 0) :
    ((truncPoly φ N : k[X]) : PowerSeries k) = φ := by
  ext n
  rw [Polynomial.coeff_coe, coeff_truncPoly]
  by_cases hn : n < N
  · rw [if_pos hn]
  · rw [if_neg hn, (h n (by omega)).symm]

/-- A finitely supported power series is the coercion of some polynomial of degree strictly less
than $N$. -/
theorem exists_polynomial_coe_of_coeff_eq_zero_ge (φ : PowerSeries k) {N : ℕ}
    (hN : 0 < N) (h : ∀ n, N ≤ n → PowerSeries.coeff n φ = 0) :
    ∃ p : k[X], p.natDegree < N ∧ ((p : k[X]) : PowerSeries k) = φ :=
  ⟨truncPoly φ N, natDegree_truncPoly_lt φ hN,
    coe_truncPoly_eq_of_coeff_eq_zero_ge φ h⟩

/-- Variant of the polynomial existence lemma using the standard inequality condition. -/
theorem exists_polynomial_coe_of_coeff_eq_zero_ge' (φ : PowerSeries k) {N : ℕ}
    (hN : 0 < N) (h : ∀ n ≥ N, PowerSeries.coeff n φ = 0) :
    ∃ p : k[X], p.natDegree < N ∧ ((p : k[X]) : PowerSeries k) = φ :=
  exists_polynomial_coe_of_coeff_eq_zero_ge φ hN (fun n hn => h n hn)

end Univariate

/-! ## Part 2: degree-≤1 representative (the shape Claim 5.9 needs) -/

section DegreeBound

variable {F : Type*} [CommRing F]

/-- If the coefficients of a bivariate polynomial $P$ have degree at most $d$, then the total degree
in the corresponding variable is bounded by $d$. -/
theorem degreeX_le_of_forall_coeff_natDegree_le
    {P : F[X][Y]} {d : ℕ}
    (h : ∀ n, (P.coeff n).natDegree ≤ d) :
    Polynomial.Bivariate.degreeX P ≤ d := by
  classical
  unfold Polynomial.Bivariate.degreeX
  apply Finset.sup_le
  intro n _
  exact h n

/-- The degree of each coefficient polynomial is bounded by the total degree in that variable. -/
theorem coeff_natDegree_le_degreeX (P : F[X][Y]) (n : ℕ) :
    (P.coeff n).natDegree ≤ Polynomial.Bivariate.degreeX P :=
  Polynomial.Bivariate.coeff_natDegree_le_degreeX P n

/-- A bivariate polynomial has degree at most 1 in $X$ if and only if each of its coefficient
polynomials has degree at most 1. -/
theorem degreeX_le_one_iff_forall_coeff_natDegree_le_one (P : F[X][Y]) :
    Polynomial.Bivariate.degreeX P ≤ 1 ↔
      ∀ n, (P.coeff n).natDegree ≤ 1 :=
  ⟨fun h n => le_trans (coeff_natDegree_le_degreeX P n) h,
    fun h => degreeX_le_of_forall_coeff_natDegree_le h⟩

/-- Decomposition of a bivariate polynomial into a linear combination when high-degree terms vanish.
-/
theorem exists_linear_decomposition_of_coeff_high_X_eq_zero
    {P : F[X][Y]}
    (h : ∀ n, ∀ j, 2 ≤ j → (P.coeff n).coeff j = 0) :
    ∃ v₀ v₁ : F[X],
      P = (Polynomial.map Polynomial.C v₀)
            + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁) := by
  classical
  -- Each `X`-coefficient has `natDegree ≤ 1`, hence `degreeX P ≤ 1`.
  have hdeg : Polynomial.Bivariate.degreeX P ≤ 1 := by
    refine degreeX_le_of_forall_coeff_natDegree_le (fun n => ?_)
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro j hj
    exact h n j (by omega)
  -- Build the constant- and linear-coefficient polynomials in `X`.
  refine ⟨P.sum fun n p => Polynomial.monomial n (p.coeff 0),
          P.sum fun n p => Polynomial.monomial n (p.coeff 1), ?_⟩
  apply Polynomial.ext
  intro n
  apply Polynomial.ext
  intro j
  simp only [coeff_add, coeff_map, coeff_C_mul]
  simp only [Polynomial.sum]
  rw [Polynomial.finset_sum_coeff, Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_monomial]
  by_cases hn : n ∈ P.support
  · have hne : P.coeff n ≠ 0 := Polynomial.mem_support_iff.mp hn
    have hdegn : (P.coeff n).natDegree ≤ 1 :=
      le_trans (coeff_natDegree_le_degreeX P n) hdeg
    rw [Polynomial.eq_X_add_C_of_natDegree_le_one hdegn]
    simp [hne, Polynomial.coeff_add, Polynomial.coeff_C_mul]
    ring_nf
  · have hp0 : P.coeff n = 0 := Polynomial.notMem_support_iff.mp hn
    simp [hn, hp0]

/-- Linear decomposition of a bivariate polynomial when the degree with respect to $X$ is at most 1.
-/
theorem exists_linear_decomposition_of_degreeX_le_one
    {P : F[X][Y]} (hP : Polynomial.Bivariate.degreeX P ≤ 1) :
    ∃ v₀ v₁ : F[X],
      P = (Polynomial.map Polynomial.C v₀)
            + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁) := by
  refine exists_linear_decomposition_of_coeff_high_X_eq_zero (fun n j hj => ?_)
  have hdegn : (P.coeff n).natDegree ≤ 1 :=
    le_trans (coeff_natDegree_le_degreeX P n) hP
  exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

end DegreeBound

/-! ## Part 3: combined brick — finite series ⟹ degree-≤1 polynomial representative

The exact assembly Claim 5.9 needs.  Here the power-series variable is the
*top* (`X`) variable of the bivariate ring: with coefficient ring `F[X]` (the
`Z`-line), `truncPoly` lands in `(F[X])[X] = F[X][Y]`, so its `degreeX` (the
`X`-degree, indexing along the `Z`-line) is exactly the quantity Claim 5.9
controls via `R = Y − P, deg_Z P ≤ 1`.  The univariate `Part 1` and the bivariate
`Part 2` then compose with no ArkLib-specific glue. -/

section Combined

variable {F : Type*} [CommRing F]

/-- Combined end-to-end representation theorem.
If a power series $\varphi$ over $F[X]$ has finite support and its truncation is linear in $X$,
then it corresponds to a bivariate polynomial $P$ of degree less than $N$ which is linear in $X$. -/
theorem exists_linear_polynomial_coe_of_finite_and_degreeX_le_one
    (φ : PowerSeries F[X]) {N : ℕ} (hN : 0 < N)
    (hfin : ∀ n, N ≤ n → PowerSeries.coeff n φ = 0)
    (hlin : Polynomial.Bivariate.degreeX (truncPoly φ N) ≤ 1) :
    ∃ (p : F[X][Y]) (v₀ v₁ : F[X]),
      p.natDegree < N ∧
      ((p : F[X][Y]) : PowerSeries F[X]) = φ ∧
      p = (Polynomial.map Polynomial.C v₀)
            + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁) := by
  obtain ⟨v₀, v₁, hlin'⟩ := exists_linear_decomposition_of_degreeX_le_one hlin
  exact ⟨truncPoly φ N, v₀, v₁,
    natDegree_truncPoly_lt φ hN,
    coe_truncPoly_eq_of_coeff_eq_zero_ge φ hfin,
    hlin'⟩

end Combined

end FiniteSeriesToPoly

end ArkLib


