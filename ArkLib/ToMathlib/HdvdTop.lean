/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.HasseDerivNumeratorGeneral
import ArkLib.ToMathlib.HasseDerivNumeratorConcrete
import ArkLib.ToMathlib.HasseDerivNumerators
import ArkLib.Data.Polynomial.RationalFunctions
import Mathlib

/-!
# Divisibility of the Leading Coefficient in Hasse Derivatives

This module establishes divisibility properties for the leading coefficients of bivariate
polynomials under Hasse derivatives, providing the algebraic foundation for the mixed
Hasse derivative $W$-power-numerator theorems (Claim A.2 of [BCIKS20]).

## Mathematical Context

Let $F$ be a field, and $H \in F[X][Y]$ be an irreducible polynomial defining the algebraic
curve, with leading coefficient $W = H.\text{leadingCoeff}$. Let $R \in F[X][X][Y]$ be a
trivariate polynomial representing the polynomial system.

The Hasse derivative operator $\Delta^{i_1}_X$ acts on polynomials in the variable $X$.
We analyze the divisibility of the $n$-th coefficient (with respect to $Y$) of the Hasse derivative:
$$(\Delta^{i_1}_X R)_n$$
when evaluated at $X = C(x_0)$.

We formalize the core reduction that if the leading coefficient polynomial $W$ (coerced as
$C(W)$) divides the leading $Y$-coefficient of $R$ in $(F[X])[X]$, i.e.,
$$C(W) \mid R_n$$
then this divisibility propagates through the Hasse derivative and evaluation, yielding:
$$W \mid (\Delta^{i_1}_X R_n)(C(x_0))$$
for all orders $i_1 \in \mathbb{N}$.

## Key Formalizations
* `evalX_innerXHasse_coeff`: Relates the evaluated coefficient of the inner Hasse derivative
  to the Hasse-Taylor derivative of the coefficient.
* `hdvd_top_of_dvd_C`: Establishes the propagation of $W$-divisibility to all Hasse
  derivative orders under the structural divisibility hypothesis.
* `genHasseCoeff_hasWPowerNumerator_of_dvd_C`: Discharges the divisibility residual in the
  general $W$-power-numerator theorem.

## References
* [BCIKS20] Binswood, Crites, Iyer, Kamara, Stewart. *Solving Algebraic Equations over
  Power Series*, 2020.
-/

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2

namespace ArkLib

variable {F : Type} [Field F]

/-! ### Coefficient Representation under Hasse Derivatives -/

/-- Relates the evaluated coefficient of the inner Hasse derivative to the Hasse derivative
of the coefficient polynomial. -/
lemma evalX_innerXHasse_coeff (x₀ : F) (R : F[X][X][Y]) (i₁ n : ℕ) :
    (Bivariate.evalX (Polynomial.C x₀) (innerXHasse i₁ R)).coeff n =
      (Polynomial.hasseDeriv i₁ (R.coeff n)).eval (Polynomial.C x₀) := by
  rw [Bivariate.evalX_eq_map, Polynomial.coeff_map]
  -- Rephrase polynomial evaluation and rewrite the inner derivative coefficient.
  rw [show ((Polynomial.evalRingHom (Polynomial.C x₀)) ((innerXHasse i₁ R).coeff n)) =
      ((innerXHasse i₁ R).coeff n).eval (Polynomial.C x₀) from rfl]
  rw [innerXHasse_coeff]

/-! ### Post-Evaluation Divisibility Reduction -/

/-- Derives the divisibility bound from the post-evaluation Hasse derivative divisibility. -/
lemma hdvd_top_of_dvd_hasseTaylor {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]} {i₁ : ℕ}
    (hdvd : H.leadingCoeff ∣
      (Polynomial.hasseDeriv i₁ (R.coeff R.natDegree)).eval (Polynomial.C x₀)) :
    H.leadingCoeff ∣ (Bivariate.evalX (Polynomial.C x₀) (innerXHasse i₁ R)).coeff R.natDegree := by
  rw [evalX_innerXHasse_coeff]
  exact hdvd

/-! ### Divisibility Propagation via Structural Multiplicity -/

/-- Discharges the leading coefficient divisibility for all Hasse derivative orders
under the hypothesis that $C(W)$ divides the coefficient polynomial. -/
lemma hdvd_top_of_dvd_C {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    (hdvd_C : (Polynomial.C H.leadingCoeff : (F[X])[X]) ∣ R.coeff R.natDegree) (i₁ : ℕ) :
    H.leadingCoeff ∣ (Bivariate.evalX (Polynomial.C x₀) (innerXHasse i₁ R)).coeff R.natDegree := by
  rw [evalX_innerXHasse_coeff]
  obtain ⟨c', hc'⟩ := hdvd_C
  rw [hc']
  -- Commute the scalar coefficient and evaluate.
  rw [← Polynomial.smul_eq_C_mul, map_smul, Polynomial.smul_eq_C_mul,
      Polynomial.eval_mul, Polynomial.eval_C]
  exact Dvd.intro _ rfl

/-- Shows that the structural hypothesis $C(W) \mid R_n$ implies the zero-order evaluation
divisibility. -/
lemma hdvd_C_implies_zero_case {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    (hdvd_C : (Polynomial.C H.leadingCoeff : (F[X])[X]) ∣ R.coeff R.natDegree) :
    H.leadingCoeff ∣ (R.coeff R.natDegree).eval (Polynomial.C x₀) := by
  obtain ⟨c', hc'⟩ := hdvd_C
  rw [hc', Polynomial.eval_mul, Polynomial.eval_C]
  exact Dvd.intro _ rfl

/-! ### Zero-Order Derivation Recovery -/

/-- Proves the zero-order case directly from the polynomial hypotheses. -/
lemma hdvd_top_zero {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]} (hHyp : Hypotheses x₀ R H) :
    H.leadingCoeff ∣ (Bivariate.evalX (Polynomial.C x₀) (innerXHasse 0 R)).coeff R.natDegree := by
  rw [evalX_innerXHasse_coeff, Polynomial.hasseDeriv_zero]
  rw [show ((LinearMap.id : (F[X])[X] →ₗ[F[X]] (F[X])[X]) (R.coeff R.natDegree)) =
      R.coeff R.natDegree from rfl]
  have h := leadingCoeff_dvd_evalX_coeff_natDegree hHyp
  rwa [Bivariate.evalX_eq_map, Polynomial.coeff_map] at h

/-! ### Theorem Integration -/

/-- Establishes the $W$-power-numerator property for general Hasse derivatives using the
structural divisibility hypothesis. -/
lemma genHasseCoeff_hasWPowerNumerator_of_dvd_C {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    {i₁ σ : ℕ} (hσ : σ + 1 ≤ R.natDegree)
    (hdvd_C : (Polynomial.C H.leadingCoeff : (F[X])[X]) ∣ R.coeff R.natDegree) :
    HasWPowerNumerator (genHasseCoeff x₀ R H i₁ σ) (R.natDegree - σ - 1) :=
  genHasseCoeff_hasWPowerNumerator_of_dvd_top hσ (hdvd_top_of_dvd_C hdvd_C i₁)

/-- Entry point showing the general coefficient is a regular element of $\mathcal{O}_H$. -/
lemma genHasseCoeff_mem_regularElms_set_of_dvd_C {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    {i₁ σ : ℕ} (hσ : σ + 1 ≤ R.natDegree)
    (hdvd_C : (Polynomial.C H.leadingCoeff : (F[X])[X]) ∣ R.coeff R.natDegree)
    (hdvd : ∀ B : 𝒪 H,
      genHasseCoeff x₀ R H i₁ σ * W_𝕃 H ^ (R.natDegree - σ - 1) = embeddingOf𝒪Into𝕃 H B →
        W_𝒪 H ^ (R.natDegree - σ - 1) ∣ B) :
    genHasseCoeff x₀ R H i₁ σ ∈ regularElms_set H :=
  genHasseCoeff_mem_regularElms_set hσ (hdvd_top_of_dvd_C hdvd_C i₁) hdvd

end ArkLib


