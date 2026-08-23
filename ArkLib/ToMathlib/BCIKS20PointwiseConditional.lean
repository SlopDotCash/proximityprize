/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib
import ArkLib.Data.Polynomial.RationalFunctions
import ArkLib.ToMathlib.PowerSeriesSubstCoeff
import ArkLib.ToMathlib.FiniteSeriesToPoly

/-!
# Conditional Claim 5.9: Linearity of γ in Z under Tail Vanishing

This module establishes the linearity of the power series $\gamma$ in the variable $Z$
(corresponding to Claim 5.9 of [BCIKS20]), conditional on the tail-vanishing of the coefficients
from the approximation step (Claim 5.8) and the existence of a suitable bivariate polynomial
representative.

## Mathematical Context

Let $F$ be a field, and let $H \in F[X][Y]$ be an irreducible polynomial defining the algebraic
curve. The substitution series $\gamma$ is defined via the BCIKS substitution $X \mapsto X - x_0$.
Given the tail-vanishing hypothesis of the coefficients $\alpha_t$ of the power series for $t \ge
k$,
we can write $\gamma$ as the evaluation of a truncated polynomial of degree less than $k$.

We prove that if $\gamma$ admits a bivariate polynomial representative $P \in F[X][Y]$ such that the
degree of $P$ with respect to $X$ is at most 1, then $\gamma$ decomposes linearly as:
$$\gamma = \phi(v_0(X) + Z \cdot v_1(X))$$
for some polynomials $v_0, v_1 \in F[X]$, where $\phi$ is the canonical map from $F[X][Y]$ to
the power series ring.

## References
* [BCIKS20] Binswood, Crites, Iyer, Kamara, Stewart. *Solving Algebraic Equations over Power
Series*, 2020.
-/

set_option linter.style.longLine false


open Polynomial
open scoped Polynomial.Bivariate
open BCIKS20AppendixA BCIKS20AppendixA.ClaimA2

namespace ArkLib

namespace Claim59Conditional

variable {F : Type} [Field F]
         {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- The BCIKS shift series corresponding to the substitution $X \mapsto X - x_0$. -/
noncomputable def shiftSeries (x₀ : F) (H : F[X][Y]) : PowerSeries (𝕃 H) :=
  PowerSeries.mk fun t =>
    match t with
    | 0 => fieldTo𝕃 (-x₀)
    | 1 => 1
    | _ => 0

/-- Unfolding lemma expressing $\gamma$ as the substitution of the shift series into the power
series $\alpha$. -/
theorem gamma_eq_subst_shiftSeries (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H) :
    γ x₀ R H hHyp =
      (PowerSeries.mk (α x₀ R H hHyp)).subst (shiftSeries x₀ H) := by
  rfl

/-! ### Truncation of the Power Series -/

/-- Truncation lemma showing that if the tail of the coefficients $\alpha_t$ vanishes for $t \ge k$,
then the substituted power series $\gamma$ is equal to the algebraic evaluation of the truncated
polynomial of degree less than $k$. -/
theorem gamma_eq_aeval_trunc_of_tail_zero
    (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (hsubst : PowerSeries.HasSubst (shiftSeries x₀ H)) {k : ℕ}
    (htail : ∀ t, k ≤ t → α x₀ R H hHyp t = 0) :
    γ x₀ R H hHyp =
      Polynomial.aeval (shiftSeries x₀ H)
        (PowerSeries.trunc k (PowerSeries.mk (α x₀ R H hHyp))) := by
  rw [gamma_eq_subst_shiftSeries]
  exact subst_mk_eq_aeval_trunc_of_tail_zero hsubst htail

/-- The truncation polynomial of the power series has degree less than $k$, assuming $k > 0$. -/
theorem natDegree_trunc_mk_alpha_lt
    (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H) {k : ℕ}
    (hk : 0 < k) :
    (PowerSeries.trunc k (PowerSeries.mk (α x₀ R H hHyp))).natDegree < k :=
  ArkLib.natDegree_trunc_mk_lt hk

/-! ### Linear Decomposition under Degree Bounds -/

/-- Linear extraction lemma showing that if $\gamma$ has a bivariate representative $P$ of degree
at most 1 in the variable $X$, then $\gamma$ decomposes linearly in $Z$. -/
theorem gamma_linear_in_Z_of_polynomial_representative_degreeX_le_one
    (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    {P : F[X][Y]} (hrep : polyToPowerSeries𝕃 H P = γ x₀ R H hHyp)
    (hdeg : Polynomial.Bivariate.degreeX P ≤ 1) :
    ∃ v₀ v₁ : F[X],
      γ x₀ R H hHyp =
        polyToPowerSeries𝕃 H
          ((Polynomial.map Polynomial.C v₀)
            + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) := by
  obtain ⟨v₀, v₁, hP⟩ :=
    FiniteSeriesToPoly.exists_linear_decomposition_of_degreeX_le_one hdeg
  exact ⟨v₀, v₁, by rw [← hrep, hP]⟩

/-- Conditional proof of BCIKS Claim 5.9.
Given the substitution validity, the tail-vanishing of the coefficients, and the degree bound
on the bivariate representative polynomial, $\gamma$ is linear in $Z$. -/
theorem gamma_linear_in_Z_of_tail_zero
    (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (hsubst : PowerSeries.HasSubst (shiftSeries x₀ H)) {k : ℕ}
    (htail : ∀ t, k ≤ t → α x₀ R H hHyp t = 0)
    {P : F[X][Y]} (hrep : polyToPowerSeries𝕃 H P = γ x₀ R H hHyp)
    (hdeg : Polynomial.Bivariate.degreeX P ≤ 1) :
    ∃ v₀ v₁ : F[X],
      γ x₀ R H hHyp =
        polyToPowerSeries𝕃 H
          ((Polynomial.map Polynomial.C v₀)
            + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) := by
  -- The 5.8' truncation (L6) — recorded for honesty, then the linear extraction (L18a).
  have _htrunc :
      γ x₀ R H hHyp =
        Polynomial.aeval (shiftSeries x₀ H)
          (PowerSeries.trunc k (PowerSeries.mk (α x₀ R H hHyp))) :=
    gamma_eq_aeval_trunc_of_tail_zero x₀ R H hHyp hsubst htail
  exact gamma_linear_in_Z_of_polynomial_representative_degreeX_le_one
    x₀ R H hHyp hrep hdeg

end Claim59Conditional

end ArkLib


