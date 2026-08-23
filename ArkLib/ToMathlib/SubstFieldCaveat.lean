/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib
import ArkLib.Data.Polynomial.RationalFunctions

/-!
# Substitution Caveats for Power Series over Fields

This module analyzes the algebraic conditions under which the power series substitution operator
`PowerSeries.subst` is well-defined. In particular, we formalize the condition that substitution
into a power series over a field requires the substituted series to have a constant coefficient
of zero (i.e., a positive order).

## Mathematical Formulation

Let $K$ be a field, and let $g(X) \in K[[X]]$ be a power series. Mathlib defines the substitution
operator $f(g(X))$ for $f \in K[[X]]$ to be well-defined if the constant coefficient of $g$
is nilpotent, which is packaged as the `PowerSeries.HasSubst` predicate.

Over a field $K$, the only nilpotent element is zero. Therefore, we have the equivalence:
$$\text{HasSubst}(g) \iff \text{constantCoeff}(g) = 0$$

In the context of the BCIKS substitution $X \mapsto X - x_0$ used in Hensel lifting, the
shift series is
$$g(X) = -x_0 + X$$
If the field is $K = \mathbb{L}_H$, which contains the base field $F$, the constant
coefficient is $0$ if and only if $x_0 = 0$. For any off-center point $x_0 \neq 0$, the
substitution operator is not well-defined under the standard Mathlib definition.

## Key Formalizations
* `hasSubst_iff_constantCoeff_eq_zero_of_field`: Pointwise equivalence of the substitution
  condition to a zero constant coefficient over a field.
* `constantCoeff_shiftSeries`: Computes the constant coefficient of the shift series.
* `hasSubst_shiftSeries_iff_eq_zero`: Shows that the BCIKS shift series is substitutable if
  and only if the expansion center is $0$.
-/

open Polynomial PowerSeries
open scoped Polynomial.Bivariate
open BCIKS20AppendixA BCIKS20AppendixA.ClaimA2

namespace ArkLib

namespace SubstFieldCaveat

/-! ### Substitution Conditions over Fields -/

/-- Characterizes the substitution condition in terms of the nilpotency of the constant
coefficient. -/
theorem hasSubst_iff_isNilpotent_constantCoeff {S : Type*} [CommRing S] (g : PowerSeries S) :
    PowerSeries.HasSubst g ↔ IsNilpotent (PowerSeries.constantCoeff g) := by
  unfold PowerSeries.HasSubst
  rfl

/-- Over a field, a power series is substitutable if and only if its constant coefficient is
zero. -/
theorem hasSubst_iff_constantCoeff_eq_zero_of_field {K : Type*} [Field K] (g : PowerSeries K) :
    PowerSeries.HasSubst g ↔ PowerSeries.constantCoeff g = 0 := by
  rw [hasSubst_iff_isNilpotent_constantCoeff]
  exact isNilpotent_iff_eq_zero

/-- Contrapositive form showing that a non-zero constant coefficient obstructs substitution. -/
theorem not_hasSubst_of_constantCoeff_ne_zero_of_field {K : Type*} [Field K] {g : PowerSeries K}
    (hg : PowerSeries.constantCoeff g ≠ 0) : ¬ PowerSeries.HasSubst g :=
  fun h => hg ((hasSubst_iff_constantCoeff_eq_zero_of_field g).mp h)

/-! ### The Shift Series and Constant Coefficient -/

variable {F : Type} [Field F]

/-- The shift series corresponding to the substitution $X \mapsto X - x_0$. -/
noncomputable def shiftSeries (x₀ : F) (H : F[X][Y]) : PowerSeries (𝕃 H) :=
  PowerSeries.mk fun t =>
    match t with
    | 0 => fieldTo𝕃 (-x₀)
    | 1 => 1
    | _ => 0

/-- Computes the constant coefficient of the shift series. -/
@[simp]
theorem constantCoeff_shiftSeries (x₀ : F) (H : F[X][Y]) :
    PowerSeries.constantCoeff (shiftSeries x₀ H) = fieldTo𝕃 (-x₀) := by
  unfold shiftSeries
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]

/-- Injectivity of the canonical embedding into the function field. -/
theorem fieldTo𝕃_injective {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)] :
    Function.Injective (fieldTo𝕃 (H := H)) := by
  unfold fieldTo𝕃
  exact RingHom.injective _

/-- The specialized coordinate embedding vanishes if and only if the coordinate center is zero. -/
theorem fieldTo𝕃_neg_eq_zero_iff {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ : F) : fieldTo𝕃 (H := H) (-x₀) = 0 ↔ x₀ = 0 := by
  rw [map_neg, neg_eq_zero]
  exact ⟨fun h => fieldTo𝕃_injective (by rw [h, map_zero]),
         fun h => by rw [h, map_zero]⟩

/-! ### Substitution Validity of the Shift Series -/

variable {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- Proves that the shift series satisfies the substitution condition if and only if the
expansion center is $0$. -/
theorem hasSubst_shiftSeries_iff_eq_zero (x₀ : F) :
    PowerSeries.HasSubst (shiftSeries x₀ H) ↔ x₀ = 0 := by
  rw [hasSubst_iff_constantCoeff_eq_zero_of_field, constantCoeff_shiftSeries,
    fieldTo𝕃_neg_eq_zero_iff]

/-- The centered case always satisfies the substitution condition. -/
theorem hasSubst_shiftSeries_zero :
    PowerSeries.HasSubst (shiftSeries (0 : F) H) :=
  (hasSubst_shiftSeries_iff_eq_zero 0).mpr rfl

/-- For any non-zero center, the shift series does not satisfy the substitution condition. -/
theorem not_hasSubst_shiftSeries_of_ne_zero {x₀ : F} (hx₀ : x₀ ≠ 0) :
    ¬ PowerSeries.HasSubst (shiftSeries x₀ H) :=
  fun h => hx₀ ((hasSubst_shiftSeries_iff_eq_zero x₀).mp h)

/-! ### The substitution-free recentering description (F1)

`SubstFieldCaveat` above shows the BCIKS shift series is `PowerSeries.subst`-substitutable
**iff** `x₀ = 0`.  For an off-center expansion (`x₀ ≠ 0`) the keystone must therefore avoid
`PowerSeries.subst`.  The substitution-free route is the *polynomial recentering*
`Polynomial.aeval (shiftSeries x₀ H) p`: this is the value of the numerator polynomial `p`
at the series `X - x₀` and is well-defined for **every** `x₀` (no `HasSubst`/nilpotent-constant
requirement), because evaluating a *finite* polynomial needs no convergence condition.  When the
numerator is tail-zero (the genuine `betaRec` output), it *is* such a finite polynomial
(`PowerSeries.trunc k (mk α)`), so this is the correct off-center replacement for the invalid
`(mk α).subst (shiftSeries x₀ H)`.

The two facts below make that precise and show the affine-curve (linear) structure is preserved
under recentering — exactly the `degreeX ≤ 1` payload the curve-coefficient extraction reads off. -/

omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
/-- The shift series is the recentering map `X ↦ X - x₀`, exhibited as the substitution-free
power series `X - C (fieldTo𝕃 x₀)`. -/
theorem shiftSeries_eq_X_sub_C (x₀ : F) :
    shiftSeries x₀ H = PowerSeries.X - PowerSeries.C (fieldTo𝕃 x₀) := by
  ext t
  rw [shiftSeries, PowerSeries.coeff_mk, map_sub, PowerSeries.coeff_X, PowerSeries.coeff_C]
  match t with
  | 0 => simp [map_neg]
  | 1 => simp
  | (n + 2) => simp

set_option synthInstance.maxHeartbeats 400000 in
-- The `aeval`/power-series instances are expensive to synthesize in the linear recentering proof.
omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
/-- **Recentering preserves the affine-curve (linear) structure.**  Applying the off-center
shift `aeval (shiftSeries x₀ H) ·` to a linear numerator `C a + b·X` returns the linear series
`C (a − b·x₀) + b·X`: the `X`-coefficient `b` is unchanged and only the constant term is shifted.
This is the substitution-free, all-`x₀` version of the `degreeX ≤ 1` preservation consumed by the
curve-coefficient-polynomial extraction. -/
theorem aeval_shiftSeries_linear (x₀ : F) (a b : 𝕃 H) :
    Polynomial.aeval (shiftSeries x₀ H)
        (Polynomial.C a + Polynomial.C b * Polynomial.X)
      = PowerSeries.C (a - b * fieldTo𝕃 x₀)
        + PowerSeries.C b * PowerSeries.X := by
  rw [shiftSeries_eq_X_sub_C]
  simp [Polynomial.aeval_def]
  ring_nf

end SubstFieldCaveat

end ArkLib
