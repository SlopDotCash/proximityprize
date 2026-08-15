/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ToMathlib.InterpolatedRepresentativeWiring
import ArkLib.ToMathlib.GSResidueSliceWeld

/-!
# Issue #304 — the sliced-separability weld into the line apex

`TrivariateSeparabilityCharacterization.lean` machine-checked that the trivariate Bézout
hypothesis `hR : R.Separable` is a **unit-discriminant** condition over the polynomial base —
refuted at squarefree trivariates with nonconstant discriminant (`Y² − Z` witnesses), i.e.
generically unsatisfiable for honest GS integer representatives.  The honest currency is the
per-place **sliced** separability `MappedSliceSeparabilityOn` (`GSResidueSliceWeld.lean`),
which the in-tree leading-coefficient/discriminant lanes produce
(`mappedSliceSeparabilityOn_of_slice_leadingCoeff`).

This module re-derives the `InterpolatedRepresentativeWiring` line-apex chain at that sliced
hypothesis: every theorem here is the `Wiring` original with `hR : R.Separable` replaced by
`hsep : MappedSliceSeparabilityOn T hHyp` — a **strict generalization**
(`MappedSliceSeparability.of_separable` recovers the originals), and the shape the matching
lane can actually instantiate.

Main results:
* `localSeries_eq_aPTaylor_sliced` — per-`z` Hensel uniqueness at the sliced hypothesis;
* `hvan_line_of_perz_data_sliced` — Brick V at the sliced hypothesis;
* `hrep_line_of_perz_data_sliced` — the apex weld: the bundle's `hrep` for the §6.2 line
  representative from per-`z` matching data + sliced separability;
* `exists_representative_pair_line_of_perz_data_sliced` — the existential bundle pair;
* `exists_representative_pair_line_of_slice_leadingCoeff` — the same with separability
  **produced** from the slice leading-coefficient avoidance locus (no separability
  hypothesis of any kind remains).
-/

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2

namespace ArkLib

namespace InterpolatedRepresentativeSliced

open InterpolatedRepresentative InterpolatedRepresentativeWiring MappedSeparability

variable {F : Type} [Field F]
variable {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- **Per-`z` Hensel uniqueness at the sliced hypothesis** — `localSeries_eq_aPTaylor` with
`R.Separable` replaced by the per-place mapped separability fact (the only consequence the
proof ever used). -/
theorem localSeries_eq_aPTaylor_sliced {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0) (hlc : H.leadingCoeff = 1)
    (z : F) (root : rationalRoot (H_tilde' H) z)
    (hx : (π_z z root) (ξ x₀ R H hHyp) ≠ 0) {P : F[X]}
    (hdvd : Polynomial.X - Polynomial.C P ∣
      R.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)))
    (hval : (P.eval x₀ : F) = root.1)
    (hsep : ((R.map (coeffHom_loc x₀ hHyp)).map
      (PowerSeries.map (π_hat_z hHyp z root hx))).Separable) :
    localSeries hHyp z root hx = PerZProximateRoot.aPTaylor x₀ P := by
  let g := placeGeometry_of_localSeries hHyp hξ hlc z root hx
    (PerZProximateRoot.aPTaylor x₀ P)
    (Polynomial.dvd_iff_isRoot.mp (PerZProximateRoot.aPTaylor_dvd hHyp z root hx hdvd))
    (PerZProximateRoot.aPTaylor_cong hHyp z root hval)
    hsep
  exact IngredientC.specialization_eq_proximate_root_of_hensel
    g.f g.haβ_root g.haP_root g.haβ_cong g.haP_cong g.hderiv

/-- **Brick V at the sliced hypothesis** — `hvan_line_of_perz_data` with the trivariate
`R.Separable` replaced by `MappedSliceSeparabilityOn T`. -/
theorem hvan_line_of_perz_data_sliced {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0) (hlc : H.leadingCoeff = 1)
    {u₀ u₁ : F[X]} {T : Finset F}
    (root : (z : F) → rationalRoot (H_tilde' H) z)
    (hx : ∀ z ∈ T, (π_z z (root z)) (ξ x₀ R H hHyp) ≠ 0)
    (hdvd : ∀ z ∈ T, Polynomial.X - Polynomial.C (u₀ + z • u₁) ∣
      R.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)))
    (hval : ∀ z ∈ T, ((u₀ + z • u₁).eval x₀ : F) = (root z).1)
    (hsep : MappedSliceSeparabilityOn T hHyp) :
    ∀ (t : ℕ), ∀ z ∈ T,
      (π_z z (root z)) (betaRec x₀ R H hHyp (BetaRecGenuineBridge.BcoeffSigned H x₀ R) t)
        = (π_z z (root z)) (InterpolatedRepresentative.clearedCoeff x₀ R H hHyp
            ((InterpolatedRepresentative.linearShape (Polynomial.taylor x₀ u₀)
              (Polynomial.taylor x₀ u₁)).coeff t) t) := by
  intro t z hz
  exact hvan_signed_of_match hHyp hlc z (root z) (hx z hz)
    (localSeries_eq_aPTaylor_sliced hHyp hξ hlc z (root z) (hx z hz) (hdvd z hz) (hval z hz)
      (hsep z hz (root z) (hx z hz)))
    (coeff_eval_linearShape_taylor x₀ z u₀ u₁ t).symm

section Apex

variable (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
variable [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- **The apex weld at sliced separability** — `hrep_line_of_perz_data` with
`hR : R.Separable` (machine-refuted generically) replaced by the producible
`MappedSliceSeparabilityOn T`. -/
theorem hrep_line_of_perz_data_sliced (hHyp : Hypotheses x₀ R H)
    {D : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hmonic : H.Monic) (hd2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hRgrade : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hξ : ξ x₀ R H hHyp ≠ 0)
    {u₀ u₁ : F[X]} {k : ℕ} (h₀ : u₀.natDegree < k) (h₁ : u₁.natDegree < k)
    {T : Finset F} (root : (z : F) → rationalRoot (H_tilde' H) z)
    (hx : ∀ z ∈ T, (π_z z (root z)) (ξ x₀ R H hHyp) ≠ 0)
    (hdvd : ∀ z ∈ T, Polynomial.X - Polynomial.C (u₀ + z • u₁) ∣
      R.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)))
    (hval : ∀ z ∈ T, ((u₀ + z • u₁).eval x₀ : F) = (root z).1)
    (hsep : MappedSliceSeparabilityOn T hHyp)
    (hcard : clearedPairBudget (Bivariate.natDegreeY R) D H.natDegree 1 k * H.natDegree
      < T.card)
    (htailα : ∀ t, k ≤ t →
      BetaToCurveCoeffPolys.αFromBeta x₀ R H hHyp
        (BetaRecGenuineBridge.BcoeffSigned H x₀ R) t = 0) :
    polyToPowerSeries𝕃 H (InterpolatedRepresentative.linearShape
        (Polynomial.taylor x₀ u₀) (Polynomial.taylor x₀ u₁))
      = BetaToCurveCoeffPolys.gammaLocal x₀ R H hHyp
          (BetaRecGenuineBridge.BcoeffSigned H x₀ R) :=
  InterpolatedRepresentative.hrep_of_cleared_counting x₀ R H hHyp
    (BetaRecGenuineBridge.BcoeffSigned H x₀ R) hH D hD
    (emb_ξ_ne_zero hHyp hξ) root
    (fun t _ z hz =>
      hvan_line_of_perz_data_sliced hHyp hξ hmonic.leadingCoeff root hx hdvd hval hsep t z hz)
    (hw_of_graded_signed x₀ R H hHyp hD hH hmonic hd2 hdHD hD_Rx0 hRgrade
      (fun t _ => natDegree_coeff_linearShape_le_one _ _ t))
    hcard
    (fun t hkt => InterpolatedRepresentative.coeff_linearShape_eq_zero
      (by rw [Polynomial.natDegree_taylor]; exact h₀)
      (by rw [Polynomial.natDegree_taylor]; exact h₁) hkt)
    htailα

/-- **The existential bundle pair at sliced separability.** -/
theorem exists_representative_pair_line_of_perz_data_sliced (hHyp : Hypotheses x₀ R H)
    {D : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hmonic : H.Monic) (hd2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hRgrade : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hξ : ξ x₀ R H hHyp ≠ 0)
    {u₀ u₁ : F[X]} {k : ℕ} (h₀ : u₀.natDegree < k) (h₁ : u₁.natDegree < k)
    {T : Finset F} (root : (z : F) → rationalRoot (H_tilde' H) z)
    (hx : ∀ z ∈ T, (π_z z (root z)) (ξ x₀ R H hHyp) ≠ 0)
    (hdvd : ∀ z ∈ T, Polynomial.X - Polynomial.C (u₀ + z • u₁) ∣
      R.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)))
    (hval : ∀ z ∈ T, ((u₀ + z • u₁).eval x₀ : F) = (root z).1)
    (hsep : MappedSliceSeparabilityOn T hHyp)
    (hcard : clearedPairBudget (Bivariate.natDegreeY R) D H.natDegree 1 k * H.natDegree
      < T.card)
    (htailα : ∀ t, k ≤ t →
      BetaToCurveCoeffPolys.αFromBeta x₀ R H hHyp
        (BetaRecGenuineBridge.BcoeffSigned H x₀ R) t = 0) :
    ∃ Ppoly : F[X][Y],
      polyToPowerSeries𝕃 H Ppoly
          = BetaToCurveCoeffPolys.gammaLocal x₀ R H hHyp
              (BetaRecGenuineBridge.BcoeffSigned H x₀ R)
        ∧ Polynomial.Bivariate.degreeX Ppoly ≤ 1
        ∧ Ppoly.natDegree < k :=
  ⟨InterpolatedRepresentative.linearShape (Polynomial.taylor x₀ u₀) (Polynomial.taylor x₀ u₁),
    hrep_line_of_perz_data_sliced x₀ R H hHyp hD hH hmonic hd2 hdHD hD_Rx0 hRgrade hξ h₀ h₁
      root hx hdvd hval hsep hcard htailα,
    InterpolatedRepresentative.degreeX_linearShape_le_one _ _,
    lt_of_le_of_lt (InterpolatedRepresentative.natDegree_linearShape_le _ _)
      (by rw [Polynomial.natDegree_taylor, Polynomial.natDegree_taylor]; exact max_lt h₀ h₁)⟩

/-- **The producer-closed apex: NO separability hypothesis of any kind.**  Separability is
PRODUCED from the slice leading-coefficient avoidance locus
(`mappedSliceSeparabilityOn_of_slice_leadingCoeff`): if every `z ∈ T` avoids the roots of the
centre slice's `Y`-leading coefficient (at preserved centre degree), the bundle pair exists.
This is the fully-honest replacement for both the refuted trivariate `R.Separable` and the
sharp Claim 5.9. -/
theorem exists_representative_pair_line_of_slice_leadingCoeff (hHyp : Hypotheses x₀ R H)
    {D : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hmonic : H.Monic) (hd2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hRgrade : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hξ : ξ x₀ R H hHyp ≠ 0)
    (hRdeg : 0 < R.natDegree)
    (hcdeg : (Bivariate.evalX (Polynomial.C x₀) R).natDegree = R.natDegree)
    {u₀ u₁ : F[X]} {k : ℕ} (h₀ : u₀.natDegree < k) (h₁ : u₁.natDegree < k)
    {T : Finset F} (root : (z : F) → rationalRoot (H_tilde' H) z)
    (hx : ∀ z ∈ T, (π_z z (root z)) (ξ x₀ R H hHyp) ≠ 0)
    (hdvd : ∀ z ∈ T, Polynomial.X - Polynomial.C (u₀ + z • u₁) ∣
      R.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)))
    (hval : ∀ z ∈ T, ((u₀ + z • u₁).eval x₀ : F) = (root z).1)
    (hlcT : ∀ z ∈ T, (Bivariate.evalX (Polynomial.C x₀) R).leadingCoeff.eval z ≠ 0)
    (hcard : clearedPairBudget (Bivariate.natDegreeY R) D H.natDegree 1 k * H.natDegree
      < T.card)
    (htailα : ∀ t, k ≤ t →
      BetaToCurveCoeffPolys.αFromBeta x₀ R H hHyp
        (BetaRecGenuineBridge.BcoeffSigned H x₀ R) t = 0) :
    ∃ Ppoly : F[X][Y],
      polyToPowerSeries𝕃 H Ppoly
          = BetaToCurveCoeffPolys.gammaLocal x₀ R H hHyp
              (BetaRecGenuineBridge.BcoeffSigned H x₀ R)
        ∧ Polynomial.Bivariate.degreeX Ppoly ≤ 1
        ∧ Ppoly.natDegree < k :=
  exists_representative_pair_line_of_perz_data_sliced x₀ R H hHyp hD hH hmonic hd2 hdHD
    hD_Rx0 hRgrade hξ h₀ h₁ root hx hdvd hval
    (mappedSliceSeparabilityOn_of_slice_leadingCoeff hHyp hRdeg hcdeg hlcT)
    hcard htailα

end Apex

end InterpolatedRepresentativeSliced

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.InterpolatedRepresentativeSliced.localSeries_eq_aPTaylor_sliced
#print axioms ArkLib.InterpolatedRepresentativeSliced.hvan_line_of_perz_data_sliced
#print axioms ArkLib.InterpolatedRepresentativeSliced.hrep_line_of_perz_data_sliced
#print axioms ArkLib.InterpolatedRepresentativeSliced.exists_representative_pair_line_of_perz_data_sliced
#print axioms ArkLib.InterpolatedRepresentativeSliced.exists_representative_pair_line_of_slice_leadingCoeff
