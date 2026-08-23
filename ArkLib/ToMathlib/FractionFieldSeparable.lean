/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib
import ArkLib.ToMathlib.DiscriminantSeparable

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Separability over the fraction field from a nonvanishing discriminant (issue #8)

`ArkLib/ToMathlib/DiscriminantSeparable.lean` proves the separability converse over a **field**
(`Polynomial.separable_of_discr_ne_zero`) and the specialization payoff bridges
(`ne_zero_and_separable_of_specialized_discr_ne_zero`) for a ring hom `φ` whose codomain is a field.
Its module docstring flags the BCIKS20 §5 obstruction explicitly: the good-`x₀` specialization
`Bivariate.evalX (C x₀) R = R.map (evalRingHom (C x₀))` lands in the **domain** `F[Z]`, *not* a
field, so over `F[Z]` separability is strictly stronger than `discr ≠ 0` and one must "compose with
the fraction-field embedding" to use the field-level converse.

This file packages exactly that composition as reusable, mathlib-only lemmas: from
`discr ≠ 0` over a domain `A`, the image of the polynomial in `(FractionRing A)[X]` is `Separable`.
This is the separability statement that the §5 Guruswami–Sudan argument over the rational-function
field `F(Z)` actually consumes (the function-field form of the `hsep` / `hsepPt` residual of
`Claim57Residuals`).

Mathlib-only (imports `DiscriminantSeparable`, itself mathlib-only): builds independently of the
`CompPoly`-backed `evalX` / `discr_y` chain.  The remaining `evalX (C x₀) R` / `discr_y` wiring into
`Agreement.lean`'s `hsep` field is the in-tree (issue-#8) integration step.

All results audit to `[propext, Classical.choice, Quot.sound]`.
-/

open scoped Polynomial

namespace Polynomial

variable {A : Type*} [CommRing A] [IsDomain A]

/-- **Separability over the fraction field from a nonvanishing discriminant.**

For a positive-`natDegree` polynomial `f` over a domain `A`, if `f.discr ≠ 0` then the image of `f`
in `(FractionRing A)[X]` is `Separable`.  The fraction-field embedding is injective, so it preserves
`natDegree` and sends the nonzero `f.discr` to a nonzero (hence, over the field `FractionRing A`,
separability-witnessing) discriminant; the conclusion is then `separable_of_discr_ne_zero` over the
field.  (Over the *domain* `A` itself, `discr ≠ 0` does **not** suffice — see
`DiscriminantSeparable.lean` — which is exactly why the §5 argument passes to `F(Z)`.) -/
theorem separable_map_fractionRing_of_discr_ne_zero {f : A[X]}
    (hdeg : 0 < f.natDegree) (hdiscr : f.discr ≠ 0) :
    (f.map (algebraMap A (FractionRing A))).Separable := by
  have hinj : Function.Injective (algebraMap A (FractionRing A)) :=
    IsFractionRing.injective A (FractionRing A)
  have hmap : (f.map (algebraMap A (FractionRing A))).natDegree = f.natDegree :=
    natDegree_map_eq_of_injective hinj f
  have hdiscr' : (algebraMap A (FractionRing A)) f.discr ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ hinj]; exact hdiscr
  exact (ne_zero_and_separable_of_specialized_base_discr_ne_zero hdeg hmap hdiscr').2

/-- **Specialization-then-fraction-field separability.**

The shape the BCIKS20 §5 good-`x₀` step produces: `f` is a factor over `A` (e.g. `A = F[Z][X]`,
`f : F[Z][X][Y]`), `φ : A →+* A'` is the `X`-specialization `evalRingHom (C x₀)` into the domain
`A' = F[Z]`, and `(f.map φ).discr ≠ 0` is the nonvanishing specialized discriminant supplied by the
avoidance argument.  The conclusion is separability of the specialized factor over the
function field `FractionRing A' = F(Z)` — the form consumed by the GS list-decoder over `F(Z)`. -/
theorem separable_mapFractionRing_of_specialized_discr_ne_zero
    {A' : Type*} [CommRing A'] [IsDomain A'] {φ : A →+* A'} {f : A[X]}
    (hdeg : 0 < (f.map φ).natDegree) (hdiscr : (f.map φ).discr ≠ 0) :
    ((f.map φ).map (algebraMap A' (FractionRing A'))).Separable :=
  separable_map_fractionRing_of_discr_ne_zero hdeg hdiscr

end Polynomial

/-! ## Axiom audit (issue #8): every result is kernel-clean. -/
#print axioms Polynomial.separable_map_fractionRing_of_discr_ne_zero
#print axioms Polynomial.separable_mapFractionRing_of_specialized_discr_ne_zero
