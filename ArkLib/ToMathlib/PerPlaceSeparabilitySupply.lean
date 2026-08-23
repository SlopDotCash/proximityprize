/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.DiscriminantSeparable
import ArkLib.ToMathlib.DiscriminantBadSet
import ArkLib.ToMathlib.HenselDatumProducer

/-!
# Per-place separability supply (issue #304, BCIKS20 §5 per-z geometry)

This file is the issue-#304 *per-place separability supply*: a **single** `F[X]`-discriminant
object (`discLC`, the product of the bivariate discriminant and the leading coefficient of a
source `fB : (F[X])[Y]`) simultaneously feeds

* the **§6 bad-set counting** side — its nonvanishing locus is exactly the input shape of
  `ArkLib.Match304.card_matching_gt_of_disc` (and from there `gradedConcreteFin_of_disc`-style
  graded counting consumers): `discLC fB ≠ 0` plus a degree budget bounds the bad places; and
* the **per-z Hensel separability / unit-derivative front** — at every place `z` where
  `(discLC fB).eval z ≠ 0`, the `z`-specialization `fB.map (evalRingHom z)` is nonzero,
  degree-preserving, and `Separable` (the `SepHenselInput.hsep` / `PlaceGeometry.hsep` payload),
  and any `f : (F⟦X⟧)[Y]` whose residue `f.map constantCoeff` *is* that specialization has a
  **unit** derivative at every approximate root (the `HenselDatum.hderiv` payload).

## Main declarations

* `discLC` — the combined discriminant–leading-coefficient polynomial in `F[X]`.
* `discLC_ne_zero` — nonvanishing of `discLC` from `discr ≠ 0` and `fB ≠ 0`.
* `specialized_ne_zero_and_separable` — per-`z` nonzero + separable specialization from one
  evaluation `(discLC fB).eval z ≠ 0`.
* `sep_on_cover` — the matchingSet-shaped corollary (separability on a whole covered set).
* `constantCoeff_eval` — the residue map `π = constantCoeff` commutes with polynomial
  evaluation: `π (f.eval a) = (f.map π).eval (π a)`.
* `isUnit_derivative_eval_of_residue_separable` — residue-level separability + residue root
  gives a *unit* derivative over `F⟦X⟧` (the Hensel `hderiv` front).
* `isUnit_derivative_of_discLC` — the composed end-to-end statement: one `discLC` evaluation
  nonvanishing at `z` plus "the residue of the per-`z` matching polynomial is the
  `z`-specialized bivariate source" yields the Hensel unit-derivative.
-/

namespace ArkLib.PerPlaceSep

open Polynomial

variable {F : Type} [Field F]

/-! ## Part 1 — the per-`z` specialization separability supplier -/

/-- The combined discriminant–leading-coefficient polynomial of a bivariate source
`fB : (F[X])[Y]` (coefficients in `F[X]` = the place-parameter line). Its nonvanishing at a
place `z` guarantees the `z`-specialization of `fB` is nonzero, degree-preserving, and
separable. -/
noncomputable def discLC (fB : Polynomial (Polynomial F)) : Polynomial F :=
  fB.discr * fB.leadingCoeff

/-- `discLC` is a *nonzero* polynomial as soon as the bivariate discriminant is nonzero and the
source is nonzero — the exact input shape of the §6 bad-set counter
`ArkLib.Match304.card_matching_gt_of_disc`. -/
theorem discLC_ne_zero {fB : Polynomial (Polynomial F)}
    (hd : fB.discr ≠ 0) (hf : fB ≠ 0) : discLC fB ≠ 0 :=
  mul_ne_zero hd (Polynomial.leadingCoeff_ne_zero.mpr hf)

/-- **Per-`z` specialization separability.** At any place `z` where the combined
discriminant–leading-coefficient polynomial does not vanish, the `z`-specialization
`fB.map (evalRingHom z)` is nonzero *and* separable (and silently degree-preserving: the
leading-coefficient factor of `discLC` survives evaluation). -/
theorem specialized_ne_zero_and_separable (fB : Polynomial (Polynomial F))
    (hdeg : 0 < fB.natDegree) {z : F} (hz : (discLC fB).eval z ≠ 0) :
    fB.map (Polynomial.evalRingHom z) ≠ 0 ∧ (fB.map (Polynomial.evalRingHom z)).Separable := by
  -- split the product nonvanishing into the discriminant and leading-coefficient halves
  have hz' : fB.discr.eval z * fB.leadingCoeff.eval z ≠ 0 := by
    simpa only [discLC, Polynomial.eval_mul] using hz
  have hd : fB.discr.eval z ≠ 0 := left_ne_zero_of_mul hz'
  have hlc : fB.leadingCoeff.eval z ≠ 0 := right_ne_zero_of_mul hz'
  -- the surviving leading coefficient preserves the degree
  have hmap : (fB.map (Polynomial.evalRingHom z)).natDegree = fB.natDegree :=
    Polynomial.natDegree_map_of_leadingCoeff_ne_zero (Polynomial.evalRingHom z) hlc
  -- the discriminant–separability bridge of `DiscriminantSeparable.lean`
  exact Polynomial.ne_zero_and_separable_of_specialized_base_discr_ne_zero hdeg hmap hd

/-- **The matchingSet-shaped corollary**: on any finite set of places covered by the
nonvanishing locus of `discLC fB`, every specialization is nonzero and separable. -/
theorem sep_on_cover (fB : Polynomial (Polynomial F)) (hdeg : 0 < fB.natDegree)
    {matchingSet : Finset F}
    (hmem : ∀ z ∈ matchingSet, (discLC fB).eval z ≠ 0) :
    ∀ z ∈ matchingSet,
      fB.map (Polynomial.evalRingHom z) ≠ 0 ∧ (fB.map (Polynomial.evalRingHom z)).Separable :=
  fun z hz => specialized_ne_zero_and_separable fB hdeg (hmem z hz)

/-! ## Part 2 — the residue-level unit-derivative producer over `F⟦X⟧` -/

/-- The residue map `F⟦X⟧ →+* F` (constant coefficient): for `f : (F⟦X⟧)[Y]`, the residue
polynomial is `f.map π : F[X]`. -/
noncomputable def π : PowerSeries F →+* F := PowerSeries.constantCoeff

/-- The residue map commutes with polynomial evaluation:
`π (f.eval a) = (f.map π).eval (π a)`. -/
theorem constantCoeff_eval (f : Polynomial (PowerSeries F)) (a : PowerSeries F) :
    π (f.eval a) = (f.map π).eval (π a) := by
  rw [Polynomial.eval_map, Polynomial.eval₂_hom]

/-- **The residue-level unit-derivative producer** (the Hensel `hderiv` front): if the residue
polynomial `f.map π` is separable and the residue `π a₀` is a root of it, then the derivative
of `f` evaluated at `a₀` is a *unit* of `F⟦X⟧`.

Route: a power series is a unit iff its constant coefficient is
(`PowerSeries.isUnit_iff_constantCoeff`); the constant coefficient of `f.derivative.eval a₀` is
`(f.map π).derivative.eval (π a₀)` (`constantCoeff_eval` + `Polynomial.derivative_map`), which
is nonzero at a root of a separable polynomial
(`Polynomial.Separable.eval₂_derivative_ne_zero`). -/
theorem isUnit_derivative_eval_of_residue_separable (f : Polynomial (PowerSeries F))
    (a₀ : PowerSeries F) (hsep : (f.map π).Separable) (hroot : (f.map π).IsRoot (π a₀)) :
    IsUnit (f.derivative.eval a₀) := by
  -- separable + root ⟹ derivative of the residue polynomial does not vanish at the root
  have hne : (Polynomial.derivative (f.map π)).eval (π a₀) ≠ 0 := by
    have h0 : (f.map π).eval₂ (RingHom.id F) (π a₀) = 0 := by
      rw [Polynomial.eval₂_id]; exact hroot
    have h := hsep.eval₂_derivative_ne_zero (RingHom.id F) h0
    rwa [Polynomial.eval₂_id] at h
  -- a power series with nonzero constant coefficient is a unit
  rw [PowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero]
  show π (f.derivative.eval a₀) ≠ 0
  rw [constantCoeff_eval, ← Polynomial.derivative_map]
  exact hne

/-- **The composed end-to-end supply** (issue #304): if the residue of the per-`z` matching
polynomial `f : (F⟦X⟧)[Y]` *is* the `z`-specialized bivariate source `fB.map (evalRingHom z)`,
then ONE `discLC` nonvanishing at `z` yields the Hensel unit-derivative at every residue-level
approximate root — the `HenselDatum.hderiv` payload, fed by the same `F[X]`-polynomial that
drives the §6 bad-set counting. -/
theorem isUnit_derivative_of_discLC (fB : Polynomial (Polynomial F))
    (hdeg : 0 < fB.natDegree) {z : F} (hz : (discLC fB).eval z ≠ 0)
    (f : Polynomial (PowerSeries F))
    (hres : f.map π = fB.map (Polynomial.evalRingHom z))
    (a₀ : PowerSeries F) (hroot : (f.map π).IsRoot (π a₀)) :
    IsUnit (f.derivative.eval a₀) := by
  have hsep : (f.map π).Separable := by
    rw [hres]
    exact (specialized_ne_zero_and_separable fB hdeg hz).2
  exact isUnit_derivative_eval_of_residue_separable f a₀ hsep hroot

end ArkLib.PerPlaceSep

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`; no `sorry`/`admit`/extra axioms. -/
#print axioms ArkLib.PerPlaceSep.discLC
#print axioms ArkLib.PerPlaceSep.discLC_ne_zero
#print axioms ArkLib.PerPlaceSep.specialized_ne_zero_and_separable
#print axioms ArkLib.PerPlaceSep.sep_on_cover
#print axioms ArkLib.PerPlaceSep.π
#print axioms ArkLib.PerPlaceSep.constantCoeff_eval
#print axioms ArkLib.PerPlaceSep.isUnit_derivative_eval_of_residue_separable
#print axioms ArkLib.PerPlaceSep.isUnit_derivative_of_discLC
