/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shaw
-/
import ArkLib.ToMathlib.BranchCollapse

/-!
# Issue #304 — the exact boundary of the general-monic half of `MonicHighYResidual`

`GSFactorData.MonicHighYResidual b` packages the two per-bundle GS-factor side conditions of
the genuine-monic capstone: (i) `b.H.Monic` (in `Y`) and (ii) `2 ≤ natDegreeY b.R`.  The
in-tree state before this file:

* `FaithfulFrontierWitness.residualw` — discharged at the explicit witness bundle;
* `BranchCollapse.monic_bundle_of_isUnit_leadingCoeff` — the *hmonic half only*, at bundles
  whose factor has a **unit** leading `Y`-coefficient (the shape forced at the endpoint by
  `ZLinearRatFuncDegreeOne.isUnit_leadingCoeff_of_gammaGenuine_Z_linear_target_all`).

This file **closes the general-monic half at its exact boundary**, in both directions:

## Positive direction (the unit-lc case, welded end-to-end)

* `monicHighYResidual_of_isUnit_leadingCoeff` — the **full** residual (both (i) and (ii)) holds
  at the transported bundle `monic_bundle_of_isUnit_leadingCoeff b hu`, given the unit leading
  coefficient and the (intentionally per-bundle) `Y`-degree dichotomy `2 ≤ natDegreeY b.R`:
  the transport keeps `R` verbatim, so (ii) carries over, and (i) is the transport's monicity.
* `monicHighYResidual_graded_of_isUnit_leadingCoeff` — the same, re-graded: the residual for
  `(GradedBundle.ofBundle …).toBundle`, i.e. **directly consumable** by the proven capstone
  consumer `section5DataOffcentreFin_of_gradedBundle_residual` (which wants a `GradedBundle`
  plus the residual for its underlying bundle).

## Negative direction (the unit-lc hypothesis is *sharp* — the A.4 wall, kernel-checked)

* `isUnit_leadingCoeff_of_associated_monic` — over any integral domain, a polynomial with a
  monic associate has a **unit** leading coefficient (units of `R[X]` over a domain live in
  `R`, so association can only rescale the leading coefficient by a unit).
* `exists_monic_associated_iff_isUnit_leadingCoeff` — the iff: a monic associate exists *iff*
  the leading coefficient is a unit.  Hence `monic_bundle_of_isUnit_leadingCoeff` is the *best
  possible* associate-class transport — its hypothesis is necessary, not a convenience.
* `no_monic_associate_bundle_of_not_isUnit_leadingCoeff` — the bundle-level wall: a GS bundle
  whose factor has a non-unit leading `Y`-coefficient admits **no** bundle transport with an
  associate monic factor.  Any general monicization must leave the associate class — i.e. the
  `clearDenomY` change of variables `Y ↦ Y / lc` of [BCIKS20, A.4], which changes the curve.
* `isUnit_of_separable_C_mul` — why the *naive* curve-side denominator-clearing also fails:
  multiplying a polynomial by a non-unit constant `C a` destroys separability (any Bézout
  combination would make `C a` divide `1`).  Since the bundle's `hHyp.separable_evalX` field is
  separability of `evalX (C x₀) R`, a non-unit rescaling of the evaluated curve cannot produce
  a valid `Hypotheses` field: the wall is genuinely the substitution route, not bookkeeping.

Together with the witness/endpoint dischargers this pins `MonicHighYResidual` exactly: it is
**proven** wherever an associate-class transport can possibly reach (unit leading coefficient +
the non-affine branch), and **provably unreachable** by rescaling beyond that — the remaining
general case *is* the A.4 substitution wall, now as a kernel-checked boundary rather than a
docstring claim.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, §5, Appendix A.4 (monicization).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Polynomial Polynomial.Bivariate
open scoped BigOperators

namespace ArkLib

namespace MonicResidualBoundary

/-! ## Part 1 — the general algebra: monic associates need unit leading coefficients -/

/-- Over an integral domain, a polynomial with a **monic associate** has a unit leading
coefficient: if `p * u = q` with `q` monic, then `leadingCoeff p · leadingCoeff u = 1`. -/
theorem isUnit_leadingCoeff_of_associated_monic {R : Type*} [CommRing R] [IsDomain R]
    {p q : R[X]} (hassoc : Associated p q) (hq : q.Monic) : IsUnit p.leadingCoeff := by
  obtain ⟨u, hu⟩ := hassoc
  have h1 : p.leadingCoeff * ((u : R[X])).leadingCoeff = 1 := by
    rw [← Polynomial.leadingCoeff_mul, hu, hq.leadingCoeff]
  exact IsUnit.of_mul_eq_one _ h1

/-- **The associate-class monicization boundary, as an iff.**  A polynomial over an integral
domain has a monic associate exactly when its leading coefficient is a unit (in which case
`C lc⁻¹ * p` is the monic associate).  The hypothesis of
`BranchCollapse.monic_bundle_of_isUnit_leadingCoeff` is therefore *necessary*: no transport
within the associate class can monicize past it. -/
theorem exists_monic_associated_iff_isUnit_leadingCoeff {R : Type*} [CommRing R] [IsDomain R]
    {p : R[X]} :
    (∃ q : R[X], Associated p q ∧ q.Monic) ↔ IsUnit p.leadingCoeff := by
  constructor
  · rintro ⟨q, hassoc, hq⟩
    exact isUnit_leadingCoeff_of_associated_monic hassoc hq
  · intro hu
    obtain ⟨w, hw⟩ := hu
    refine ⟨Polynomial.C (↑w⁻¹ : R) * p, ?_, ?_⟩
    · exact ⟨(Polynomial.isUnit_C.mpr (Units.isUnit w⁻¹)).unit,
        by rw [IsUnit.unit_spec]; ring⟩
    · rw [Polynomial.Monic, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, ← hw]
      exact Units.inv_mul w

/-- **Why the naive curve-side denominator-clearing fails.**  Multiplying any polynomial by a
non-unit constant destroys separability: from a Bézout identity
`u·(C a·p) + v·(C a·p′) = 1` the constant `C a` divides `1`.  Applied to the GS bundle, the
field `hHyp.separable_evalX : (evalX (C x₀) R).Separable` cannot survive a non-unit rescaling
of the evaluated curve — the A.4 wall is genuinely the `Y ↦ Y / lc` substitution, not a
rescaling. -/
theorem isUnit_of_separable_C_mul {R : Type*} [CommSemiring R]
    {a : R} {p : R[X]} (h : (Polynomial.C a * p).Separable) : IsUnit a := by
  obtain ⟨u, v, huv⟩ := h
  rw [Polynomial.derivative_C_mul] at huv
  have hdvd : Polynomial.C a ∣ 1 :=
    ⟨u * p + v * Polynomial.derivative p, by rw [← huv]; ring⟩
  exact Polynomial.isUnit_C.mp (isUnit_of_dvd_one hdvd)

end MonicResidualBoundary

namespace GSFactorData

open MonicResidualBoundary BranchCollapse

variable {F : Type} [Field F]

/-! ## Part 2 — the positive direction: the full residual at unit leading coefficient -/

/-- **The full `MonicHighYResidual` at unit-leading-coefficient bundles.**  Given the unit
leading `Y`-coefficient (the endpoint shape) and the `Y`-degree dichotomy `2 ≤ natDegreeY R`
(intentionally per-bundle: the `deg_Y ≤ 1` affine branch is handled by a different pathway),
the transported bundle `monic_bundle_of_isUnit_leadingCoeff b hu` satisfies **both** halves of
the residual: the transport's factor is monic and its `R` is `b.R` verbatim. -/
theorem monicHighYResidual_of_isUnit_leadingCoeff {x₀ : F}
    (b : Bundle (F := F) x₀) (hu : IsUnit b.H.leadingCoeff)
    (hd2 : 2 ≤ Bivariate.natDegreeY b.R) :
    MonicHighYResidual (F := F) (monic_bundle_of_isUnit_leadingCoeff b hu).1 := by
  obtain ⟨hm, hR, -⟩ := (monic_bundle_of_isUnit_leadingCoeff b hu).2
  exact ⟨hm, by rw [hR]; exact hd2⟩

/-- **The full residual, re-graded and consumer-ready.**  The same discharge for the *graded*
transport `GradedBundle.ofBundle (monic_bundle_of_isUnit_leadingCoeff b hu).1`: this is exactly
the `(gb, hres)` input pair of the proven capstone consumer
`section5DataOffcentreFin_of_gradedBundle_residual`, so at unit-leading-coefficient bundles
with the non-affine `Y`-degree the *entire* graded side-condition battery (i)–(v) is now
discharged. -/
theorem monicHighYResidual_graded_of_isUnit_leadingCoeff {x₀ : F}
    (b : Bundle (F := F) x₀) (hu : IsUnit b.H.leadingCoeff)
    (hd2 : 2 ≤ Bivariate.natDegreeY b.R) :
    MonicHighYResidual (F := F)
      (GradedBundle.ofBundle (monic_bundle_of_isUnit_leadingCoeff b hu).1).toBundle := by
  obtain ⟨hm, hR, -⟩ := (monic_bundle_of_isUnit_leadingCoeff b hu).2
  exact ⟨hm, by rw [show (GradedBundle.ofBundle (monic_bundle_of_isUnit_leadingCoeff b hu).1).toBundle.R
      = (monic_bundle_of_isUnit_leadingCoeff b hu).1.R from rfl, hR]; exact hd2⟩

/-! ## Part 3 — the negative direction: the wall is sharp -/

/-- **The bundle-level A.4 wall, kernel-checked.**  A GS bundle whose factor has a non-unit
leading `Y`-coefficient (e.g. a `normalizedFactors` factor whose leading coefficient is a
non-constant monic element of `F[X]`) admits **no** bundle with an associate monic factor:
the `hmonic` half of `MonicHighYResidual` is *unreachable* by any associate-class transport,
and the general discharge necessarily goes through the curve-changing `clearDenomY`
substitution of [BCIKS20, A.4]. -/
theorem no_monic_associate_bundle_of_not_isUnit_leadingCoeff {x₀ : F}
    (b : Bundle (F := F) x₀) (h : ¬ IsUnit b.H.leadingCoeff) :
    ¬ ∃ b' : Bundle (F := F) x₀, Associated b.H b'.H ∧ b'.H.Monic := by
  rintro ⟨b', hassoc, hmonic⟩
  exact h (isUnit_leadingCoeff_of_associated_monic hassoc hmonic)

end GSFactorData

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`. -/
#print axioms ArkLib.MonicResidualBoundary.isUnit_leadingCoeff_of_associated_monic
#print axioms ArkLib.MonicResidualBoundary.exists_monic_associated_iff_isUnit_leadingCoeff
#print axioms ArkLib.MonicResidualBoundary.isUnit_of_separable_C_mul
#print axioms ArkLib.GSFactorData.monicHighYResidual_of_isUnit_leadingCoeff
#print axioms ArkLib.GSFactorData.monicHighYResidual_graded_of_isUnit_leadingCoeff
#print axioms ArkLib.GSFactorData.no_monic_associate_bundle_of_not_isUnit_leadingCoeff
