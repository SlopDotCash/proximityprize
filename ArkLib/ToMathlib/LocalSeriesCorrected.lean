/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.HvanishSupply
import ArkLib.ToMathlib.GenuinePpolyConverter
import ArkLib.ToMathlib.GSGradedBundle
import ArkLib.ToMathlib.OffcentreFaithfulBundle

/-!
# Issue #304 — the F6-consumer disposition map: every consumer of the refuted representative,
re-plumbed or kernel-proved legacy

`GenuinePpolyConverter` (FINDING F6) kernel-proved that the legacy genuine representative

  `hrepG : polyToPowerSeries𝕃 H Ppoly = gammaGenuine x₀ R H hHyp`

is **unsatisfiable for every `d_H ≥ 2`** (the ground-line order-0 coefficient cannot reach
`α₀ = T/W`), and built the satisfiable corrected (T-affine pair) representative
`hrepT : polyToPowerSeries𝕃T H P₀ P₁ = gammaGenuine …`.  This file is the authoritative
disposition map for **all** in-tree consumers of the refuted shape, and the mechanical
re-plumbing of those that survive on `hrepT`.

## The complete consumer inventory and dispositions

1. `GenuineTruncationFin.gammaGenuine_eq_trunc_of_graded_disc` (`hrepG` input) —
   **already repaired** by `GenuinePpolyConverter.gammaGenuine_eq_trunc_of_graded_disc_corrected`
   (not this file).
2. The decoded chain (`DecodedProximateRoot` / `DecodedRootSupply` / `BranchCertificates`
   capstones) — **already repaired** by `DecodedCapstonesCorrected` (not this file).
3. `HvanishSupply.gammaGenuine_eq_trunc_of_mpPoint` / `…_of_localSeries` /
   `…_of_localSeries_dvd_sep` (`hrepG` input) — **REPAIRED HERE** (Part 1):
   `hrepG → hrepT`, tail/counting index `deg Ppoly → max (deg P₀) (deg P₁)`, routed through
   `gammaGenuine_eq_trunc_of_graded_disc_corrected` exactly as `DecodedCapstonesCorrected`
   did for the decoded chain.
4. `GenuineMonicCapstone.section5DataOffcentreFin_of_producers_genuineMonic` (`hrep` input
   against `gammaGenuine`) and `GSFactorData.section5DataOffcentreFin_of_gradedBundle_residual`
   (same shape at a graded bundle) — inputs **kernel-proved EMPTY** at `d_H ≥ 2`
   (Part 3, `hrep_genuineMonic_unsat_of_two_le_natDegree` /
   `hrep_gradedBundle_unsat_of_two_le_natDegree`); see the legacy verdict below.
5. `BetaRecGenuineBridge.hrep_BcoeffSigned_of_genuine_monic` — a *transport* of `hrepG` into
   the `gammaLocal`-shape; both its input and its output are empty at `d_H ≥ 2` (Part 2), so
   it is a legacy transport needing no repair (it is vacuously sound).

## FINDING F6-Ω (Part 2): the bundle field itself is empty at `d_H ≥ 2`, for EVERY `Bcoeff`

The off-centre bundles do not consume `hrepG` directly: their structural field is

  `hrep : polyToPowerSeries𝕃 H Ppoly = gammaLocal x₀ R H hHyp Bcoeff`.

The task-level expectation was that this collapses to the refuted shape only at the signed
family with monic `H` (via `gammaLocal_BcoeffSigned_eq_gammaGenuine_of_monic`).  The audit
shows it is strictly worse: the `betaRec` **base case is `Bcoeff`-independent**
(`betaRec_zero : β₀ = mk X`), so the order-0 local coefficient is

  `αFromBeta … Bcoeff 0 = T / W = α₀ H`   (`alphaFromBeta_zero_eq_α₀`)

for **every** coefficient family `Bcoeff` — off the ground line whenever `d_H ≥ 2`
(`ZLinearClosureAudit.α₀_ne_lift`).  Hence (`not_hrep_gammaLocal_of_two_le_natDegree`):

* the `hrep` field of `OffcentreKeystone.Section5StrictDataOffcentreFin` is unsatisfiable at
  `d_H ≥ 2` for every `Bcoeff` (no monicity, no signed family needed), and the **bundle type
  itself is empty there**: every inhabitant has `d_H = 1`
  (`section5DataOffcentreFin_natDegree_eq_one`);
* the same holds verbatim for `OffcentreFaithful.Section5StrictDataOffcentreFaithful`, which
  carries the identical `hrep` field
  (`section5DataOffcentreFaithful_natDegree_eq_one`);
* the monic-signed route requested by the task is the special case
  `hrep_BcoeffSigned_unsat_of_monic_two_le_natDegree`, proved through the bridge
  `gammaLocal_BcoeffSigned_eq_gammaGenuine_of_monic` to confirm the two refutation routes
  agree.

## The bundle-repair verdict (the (b)(2) question)

**Does the bundle's `Ppoly` field admit a T-affine generalization without structural change?
NO.**  `Ppoly : F[X][Y]`, `hrep` (against `polyToPowerSeries𝕃`) and `hdegX : degreeX Ppoly ≤ 1`
are *fields of the structure*, consumed by
`BetaToCurveCoeffPolys.curveCoeffPolys_of_betaRec_offcentreFin`, whose Prop-5.5 reading
extracts the per-coefficient interpolants from a **single ground-line representative of
`Z`-degree ≤ 1**.  A T-affine pair `(P₀, P₁)` changes the field types and the extraction
interface — a structural change to both bundles and their consumer chain.  Therefore the two
off-centre bundles are marked **LEGACY at `d_H ≥ 2`** (now a kernel-checked emptiness, not a
judgement call): they remain sound, satisfiable vehicles exactly on the `d_H = 1` lane (where
`T` is on the ground line and `hrep` can hold).  The `d_H ≥ 2` surface is served by:

* the corrected truncation chain on `polyToPowerSeries𝕃T`
  (`GenuinePpolyConverter` Part 5, `DecodedCapstonesCorrected`, and Part 1 here), and
* the `hrep`-free lean faithful datum `FaithfulCurveExtraction.CurveFamilyData`
  (fields `x₀ / n / hn / c / hPz` only), which `OffcentreFaithfulBundle` forgets onto — the
  faithful-extraction lane does NOT pass through the empty `hrep` field.

## Honest residuals

* Producing `hrepT` *ab initio* at `d_H = 2` is the open converter loop documented in
  `GenuinePpolyConverter` (the converter consumes the truncation identity that the corrected
  capstones produce); the Part-1 capstones here inherit that residual unchanged — they are
  satisfiable in the shape `hrepT` (unlike `hrepG`), but the in-tree producer of `hrepT`
  currently routes through the truncation identity itself.
* No corrected `hdegX` companion (the ground `Z`-degree budget on `P₀`/`P₁`) exists — the open
  #138 X-degree residual, untouched here.
* The `d_H = 1` lane of both off-centre bundles is genuinely NOT refuted (excluded from every
  emptiness statement here), and nothing in this file restricts it.

## References

* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, §5 (Prop. 5.5, Claims 5.8′/5.9), §6.2, Appendix A.2/A.4.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2 ToRatFunc Ideal
open ProximityGap Code NNReal Finset Function ProbabilityTheory
open BCIKS20.HenselNumerator BCIKS20.HenselNumerator.S5Genuine
open ProximityPrize.BCIKS20.GammaGenuine
open scoped BigOperators ENNReal ProbabilityTheory LinearCode

namespace ArkLib

namespace LocalSeriesCorrected

/-! ## Part 1 — the `HvanishSupply` capstones re-plumbed onto the corrected representative

The three `HvanishSupply` truncation capstones consumed the F6-unsatisfiable `hrepG`.  Each is
restated on the satisfiable corrected representative `hrepT` (T-affine pair `(P₀, P₁)`), with
the finite counting range `[k, deg Ppoly]` replaced by `[k, max (deg P₀) (deg P₁)]` and the
counting budget re-indexed accordingly, routed through
`GenuinePpolyConverter.gammaGenuine_eq_trunc_of_graded_disc_corrected`.  The `hvanish`
producers of `HvanishSupply` are range-generic and are reused verbatim. -/

section HvanishCorrected

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
variable [Fintype F] [DecidableEq F]

/-- **The `MatchingPoint` truncation capstone, F6-repaired.**  As
`HvanishSupply.gammaGenuine_eq_trunc_of_mpPoint`, with the unsatisfiable `hrepG` replaced by
the corrected T-affine `hrepT` and the counting range/budget re-indexed at
`max (deg P₀) (deg P₁)`. -/
theorem gammaGenuine_eq_trunc_of_mpPoint_corrected {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H)
    {D k : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hmonic : H.Monic) (hd2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hR : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    {P₀ P₁ : F[X][Y]}
    (hrepT : GenuinePpolyConverter.polyToPowerSeries𝕃T H P₀ P₁ = gammaGenuine x₀ R H hHyp)
    {matchingSet : Finset F}
    {root : (z : F) → rationalRoot (H_tilde' H) z}
    (mp : ∀ t, k ≤ t → t ≤ max P₀.natDegree P₁.natDegree → ∀ z ∈ matchingSet,
      BetaMatchingVanishes.MatchingPoint x₀ R H hHyp
        (BetaRecGenuineBridge.BcoeffSigned H x₀ R) t z (root z))
    {disc : F[X]} (hdisc : disc ≠ 0)
    (hcover : ∀ z : F, disc.eval z ≠ 0 → z ∈ matchingSet)
    (hbig : gradedCardBudget (Bivariate.natDegreeY R) D H.natDegree
        (max P₀.natDegree P₁.natDegree) + disc.natDegree < Fintype.card F) :
    gammaGenuine x₀ R H hHyp
      = (↑(PowerSeries.trunc k (gammaGenuine x₀ R H hHyp)) : PowerSeries (𝕃 H)) :=
  GenuinePpolyConverter.gammaGenuine_eq_trunc_of_graded_disc_corrected H hHyp hD hH hmonic
    hd2 hdHD hD_Rx0 hR hrepT (HvanishSupply.hvanish_of_mpPoint H mp) hdisc hcover hbig

/-- **The local-series truncation capstone, F6-repaired.**  As
`HvanishSupply.gammaGenuine_eq_trunc_of_localSeries` (GS-side per-place inputs: proximate
roots `aP z` with root membership, order-0 congruence, separable specialization, finite-range
coefficient vanishing), with `hrepG → hrepT` and the range/budget at
`max (deg P₀) (deg P₁)`. -/
theorem gammaGenuine_eq_trunc_of_localSeries_corrected {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H)
    {D k : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hmonic : H.Monic) (hd2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hR : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    {P₀ P₁ : F[X][Y]}
    (hrepT : GenuinePpolyConverter.polyToPowerSeries𝕃T H P₀ P₁ = gammaGenuine x₀ R H hHyp)
    (hξ : ξ x₀ R H hHyp ≠ 0)
    {matchingSet : Finset F}
    (root : (z : F) → rationalRoot (H_tilde' H) z)
    (hx : ∀ z ∈ matchingSet, (π_z z (root z)) (ξ x₀ R H hHyp) ≠ 0)
    (aP : F → PowerSeries F)
    (haP_root : ∀ z, (hz : z ∈ matchingSet) →
      ((R.map (coeffHom_loc x₀ hHyp)).map
        (PowerSeries.map (π_hat_z hHyp z (root z) (hx z hz)))).IsRoot (aP z))
    (haP_cong : ∀ z ∈ matchingSet,
      aP z - PowerSeries.C ((π_z z (root z)) (βHensel H x₀ R hHyp 0))
        ∈ Ideal.span {(PowerSeries.X : PowerSeries F)})
    (hsep : ∀ z, (hz : z ∈ matchingSet) →
      ((R.map (coeffHom_loc x₀ hHyp)).map
        (PowerSeries.map (π_hat_z hHyp z (root z) (hx z hz)))).Separable)
    (haP_coeff : ∀ t, k ≤ t → t ≤ max P₀.natDegree P₁.natDegree → ∀ z ∈ matchingSet,
      PowerSeries.coeff t (aP z) = 0)
    {disc : F[X]} (hdisc : disc ≠ 0)
    (hcover : ∀ z : F, disc.eval z ≠ 0 → z ∈ matchingSet)
    (hbig : gradedCardBudget (Bivariate.natDegreeY R) D H.natDegree
        (max P₀.natDegree P₁.natDegree) + disc.natDegree < Fintype.card F) :
    gammaGenuine x₀ R H hHyp
      = (↑(PowerSeries.trunc k (gammaGenuine x₀ R H hHyp)) : PowerSeries (𝕃 H)) :=
  GenuinePpolyConverter.gammaGenuine_eq_trunc_of_graded_disc_corrected H hHyp hD hH hmonic
    hd2 hdHD hD_Rx0 hR hrepT
    (HvanishSupply.hvanish_of_localSeries H hHyp hξ hmonic.leadingCoeff root hx aP haP_root
      haP_cong hsep haP_coeff)
    hdisc hcover hbig

/-- **The GS-handshake truncation capstone, F6-repaired.**  As
`HvanishSupply.gammaGenuine_eq_trunc_of_localSeries_dvd_sep` (root membership as the
matching-factor divisibility `(Y − C (aP z)) ∣ f_z`, separability inherited from
`R.Separable`), with `hrepG → hrepT` and the range/budget at `max (deg P₀) (deg P₁)`. -/
theorem gammaGenuine_eq_trunc_of_localSeries_dvd_sep_corrected {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H)
    {D k : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hmonic : H.Monic) (hd2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hR : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    {P₀ P₁ : F[X][Y]}
    (hrepT : GenuinePpolyConverter.polyToPowerSeries𝕃T H P₀ P₁ = gammaGenuine x₀ R H hHyp)
    (hξ : ξ x₀ R H hHyp ≠ 0) (hRsep : R.Separable)
    {matchingSet : Finset F}
    (root : (z : F) → rationalRoot (H_tilde' H) z)
    (hx : ∀ z ∈ matchingSet, (π_z z (root z)) (ξ x₀ R H hHyp) ≠ 0)
    (aP : F → PowerSeries F)
    (hdvd : ∀ z, (hz : z ∈ matchingSet) →
      (Polynomial.X - Polynomial.C (aP z)) ∣
        ((R.map (coeffHom_loc x₀ hHyp)).map
          (PowerSeries.map (π_hat_z hHyp z (root z) (hx z hz)))))
    (haP_cong : ∀ z ∈ matchingSet,
      aP z - PowerSeries.C ((π_z z (root z)) (βHensel H x₀ R hHyp 0))
        ∈ Ideal.span {(PowerSeries.X : PowerSeries F)})
    (haP_coeff : ∀ t, k ≤ t → t ≤ max P₀.natDegree P₁.natDegree → ∀ z ∈ matchingSet,
      PowerSeries.coeff t (aP z) = 0)
    {disc : F[X]} (hdisc : disc ≠ 0)
    (hcover : ∀ z : F, disc.eval z ≠ 0 → z ∈ matchingSet)
    (hbig : gradedCardBudget (Bivariate.natDegreeY R) D H.natDegree
        (max P₀.natDegree P₁.natDegree) + disc.natDegree < Fintype.card F) :
    gammaGenuine x₀ R H hHyp
      = (↑(PowerSeries.trunc k (gammaGenuine x₀ R H hHyp)) : PowerSeries (𝕃 H)) :=
  GenuinePpolyConverter.gammaGenuine_eq_trunc_of_graded_disc_corrected H hHyp hD hH hmonic
    hd2 hdHD hD_Rx0 hR hrepT
    (HvanishSupply.hvanish_of_localSeries_dvd_sep H hHyp hξ hmonic.leadingCoeff hRsep root hx
      aP hdvd haP_cong haP_coeff)
    hdisc hcover hbig

end HvanishCorrected

/-! ## Part 2 — FINDING F6-Ω: the `gammaLocal`-shaped `hrep` is empty at `d_H ≥ 2` for EVERY
`Bcoeff`

The `betaRec` base case `β₀ = mk X` does not consult `Bcoeff`, so the order-0 coefficient of
`gammaLocal` is `α₀ = T/W` for every coefficient family — the bundle-level refutation needs
neither monicity nor the signed family. -/

section OrderZero

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- **The `Bcoeff`-uniform order-0 reading.**  `αFromBeta … Bcoeff 0 = α₀ = T/W` for EVERY
coefficient family `Bcoeff`: the recursion base `β₀ = mk X` is `Bcoeff`-independent
(`betaRec_zero`), and the order-0 denominator is `W¹ · ξ⁰ = W`
(`henselDenominatorExponent_zero`). -/
theorem alphaFromBeta_zero_eq_α₀ (x₀ : F) (R : F[X][X][Y]) (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H) :
    BetaToCurveCoeffPolys.αFromBeta x₀ R H hHyp Bcoeff 0 = α₀ H := by
  have h : BetaToCurveCoeffPolys.αFromBeta x₀ R H hHyp Bcoeff 0
      = embeddingOf𝒪Into𝕃 H (betaRec x₀ R H hHyp Bcoeff 0)
        / (liftToFunctionField (H := H) H.leadingCoeff ^ (0 + 1)
            * embeddingOf𝒪Into𝕃 H (ξ x₀ R H hHyp) ^ henselDenominatorExponent 0) := rfl
  rw [h, betaRec_zero, henselDenominatorExponent_zero, pow_zero, mul_one, zero_add, pow_one,
    embeddingOf𝒪Into𝕃_mk, liftBivariate_X, α₀]

/-- **FINDING F6-Ω (refutation).**  For every curve with `d_H ≥ 2` and EVERY coefficient
family `Bcoeff`, NO bivariate polynomial represents the off-centre local Hensel series
`gammaLocal` through `polyToPowerSeries𝕃`: the order-0 coefficient is the `Bcoeff`-independent
`α₀ = T/W` (`alphaFromBeta_zero_eq_α₀`), off the ground line (`α₀_ne_lift`).  This is the
`hrep` FIELD of `Section5StrictDataOffcentreFin` / `Section5StrictDataOffcentreFaithful` —
strictly stronger than the monic-signed route the bridge suggests. -/
theorem not_hrep_gammaLocal_of_two_le_natDegree (hdeg : 2 ≤ H.natDegree)
    {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H) (Ppoly : F[X][Y]) :
    polyToPowerSeries𝕃 H Ppoly ≠ BetaToCurveCoeffPolys.gammaLocal x₀ R H hHyp Bcoeff := by
  intro h
  have h0 : liftToFunctionField (H := H) (Ppoly.coeff 0) = α₀ H := by
    have hc := congrArg (fun s : PowerSeries (𝕃 H) => PowerSeries.coeff 0 s) h
    simpa only [coeff_polyToPowerSeries𝕃, BetaToCurveCoeffPolys.coeff_gammaLocal,
      alphaFromBeta_zero_eq_α₀] using hc
  exact BCIKS20.ZLinearClosureAudit.α₀_ne_lift H hdeg (Ppoly.coeff 0) h0.symm

/-- **FINDING F6-Ω (existential form).**  The `hrep`-shaped input of the off-centre bundle
producers (`section5DataOffcentreFin_of_producers`,
`section5DataOffcentreFaithful_of_producers`, and their graded/disc capstones) is EMPTY for
`d_H ≥ 2`, at every `Bcoeff`. -/
theorem hrep_gammaLocal_unsat_of_two_le_natDegree (hdeg : 2 ≤ H.natDegree)
    {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H) :
    ¬ ∃ Ppoly : F[X][Y],
      polyToPowerSeries𝕃 H Ppoly = BetaToCurveCoeffPolys.gammaLocal x₀ R H hHyp Bcoeff :=
  fun ⟨Ppoly, h⟩ => not_hrep_gammaLocal_of_two_le_natDegree H hdeg hHyp Bcoeff Ppoly h

/-- **The monic-signed corollary (the task-requested route), through the bridge.**  At the
signed canonical family with monic `H`, the bundle's `hrep` field IS the refuted genuine
shape (`gammaLocal_BcoeffSigned_eq_gammaGenuine_of_monic`), hence empty for `d_H ≥ 2`.
Subsumed by `hrep_gammaLocal_unsat_of_two_le_natDegree` (which needs neither monicity nor the
signed family); proved via the bridge to confirm the two refutation routes agree. -/
theorem hrep_BcoeffSigned_unsat_of_monic_two_le_natDegree
    (hmonic : H.Monic) (hdeg : 2 ≤ H.natDegree)
    {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H) :
    ¬ ∃ Ppoly : F[X][Y],
      polyToPowerSeries𝕃 H Ppoly
        = BetaToCurveCoeffPolys.gammaLocal x₀ R H hHyp
            (BetaRecGenuineBridge.BcoeffSigned H x₀ R) := by
  rintro ⟨Ppoly, h⟩
  rw [BetaRecGenuineBridge.gammaLocal_BcoeffSigned_eq_gammaGenuine_of_monic x₀ R hHyp
    hmonic] at h
  exact GenuinePpolyConverter.not_hrepG_of_two_le_natDegree H hdeg hHyp Ppoly h

end OrderZero

/-! ## Part 3 — the bundle-level dispositions: emptiness at `d_H ≥ 2`, legacy verdicts

The `Ppoly`/`hrep`/`hdegX` triple is structural in both off-centre bundles and is consumed by
the single-representative Prop-5.5 extraction (`curveCoeffPolys_of_betaRec_offcentreFin`); no
T-affine pair fits without changing the structures and their consumer chain.  The kernel-level
content of the legacy verdict is the emptiness below. -/

section BundleDisposition

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **Bundle-level F6 (emptiness).**  `Section5StrictDataOffcentreFin` has NO inhabitant whose
curve has `d_H ≥ 2`: its own `hrep` field is the F6-Ω-refuted shape, at whatever `Bcoeff` the
inhabitant carries. -/
theorem section5DataOffcentreFin_false_of_two_le_natDegree
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    (d : OffcentreKeystone.Section5StrictDataOffcentreFin
      (k := k) (deg := deg) (domain := domain) (δ := δ) u P)
    (hdeg : 2 ≤ d.H.natDegree) : False := by
  haveI := d.hIrr
  haveI := d.hPos
  exact not_hrep_gammaLocal_of_two_le_natDegree d.H hdeg d.hHyp d.Bcoeff d.Ppoly d.hrep

/-- **The off-centre bundle is a `d_H = 1` vehicle.**  Every inhabitant of
`Section5StrictDataOffcentreFin` has curve degree exactly `1` — the kernel-checked legacy
verdict: the bundle is sound but cannot carry the `d_H ≥ 2` target regime. -/
theorem section5DataOffcentreFin_natDegree_eq_one
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    (d : OffcentreKeystone.Section5StrictDataOffcentreFin
      (k := k) (deg := deg) (domain := domain) (δ := δ) u P) :
    d.H.natDegree = 1 := by
  have h1 : 0 < d.H.natDegree := d.hH
  by_contra hne
  exact section5DataOffcentreFin_false_of_two_le_natDegree d (by omega)

/-- **Bundle-level F6 for the faithful off-centre bundle.**  The faithful bundle carries the
identical `hrep` field, so it is equally empty at `d_H ≥ 2`.  NOTE: the faithful
*extraction lane* is unaffected — the lean datum `FaithfulCurveExtraction.CurveFamilyData`
(no `hrep` field) is the surviving `d_H ≥ 2` vehicle. -/
theorem section5DataOffcentreFaithful_false_of_two_le_natDegree
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    (d : OffcentreFaithful.Section5StrictDataOffcentreFaithful
      (k := k) (deg := deg) (domain := domain) (δ := δ) u P)
    (hdeg : 2 ≤ d.H.natDegree) : False := by
  haveI := d.hIrr
  haveI := d.hPos
  exact not_hrep_gammaLocal_of_two_le_natDegree d.H hdeg d.hHyp d.Bcoeff d.Ppoly d.hrep

/-- **The faithful off-centre bundle is a `d_H = 1` vehicle** (same verdict as the plain
bundle; the faithful `hPz` repair did not touch the `hrep` wall). -/
theorem section5DataOffcentreFaithful_natDegree_eq_one
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    (d : OffcentreFaithful.Section5StrictDataOffcentreFaithful
      (k := k) (deg := deg) (domain := domain) (δ := δ) u P) :
    d.H.natDegree = 1 := by
  have h1 : 0 < d.H.natDegree := d.hH
  by_contra hne
  exact section5DataOffcentreFaithful_false_of_two_le_natDegree d (by omega)

/-- **Producer-input emptiness at a GS factor bundle (any `Bcoeff`).**  The `hrep` input of
`OffcentreKeystone.section5DataOffcentreFin_of_producers` (and of every downstream producer
that threads it) is unsatisfiable at `d_H ≥ 2`, for every coefficient family. -/
theorem hrep_producers_unsat_of_two_le_natDegree
    {x₀ : F} (b : GSFactorData.Bundle (F := F) x₀)
    [_inst_hIrr : Fact (Irreducible b.H)] [_inst_hPos : Fact (0 < b.H.natDegree)]
    (hdeg : 2 ≤ b.H.natDegree)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 b.H) :
    ¬ ∃ Ppoly : F[X][Y],
      polyToPowerSeries𝕃 b.H Ppoly
        = BetaToCurveCoeffPolys.gammaLocal x₀ b.R b.H b.hHyp Bcoeff :=
  hrep_gammaLocal_unsat_of_two_le_natDegree b.H hdeg b.hHyp Bcoeff

/-- **Producer-input emptiness for the genuine-monic capstone.**  The `hrep` input of
`GenuineMonicCapstone.section5DataOffcentreFin_of_producers_genuineMonic` is literally the F6
shape (against `gammaGenuine`), hence empty at `d_H ≥ 2` — the capstone is vacuous in the
target regime and is marked legacy alongside its bundle. -/
theorem hrep_genuineMonic_unsat_of_two_le_natDegree
    {x₀ : F} (b : GSFactorData.Bundle (F := F) x₀)
    [_inst_hIrr : Fact (Irreducible b.H)] [_inst_hPos : Fact (0 < b.H.natDegree)]
    (hdeg : 2 ≤ b.H.natDegree) :
    ¬ ∃ Ppoly : F[X][Y],
      polyToPowerSeries𝕃 b.H Ppoly = gammaGenuine x₀ b.R b.H b.hHyp :=
  GenuinePpolyConverter.hrepG_unsat_of_two_le_natDegree b.H hdeg b.hHyp

/-- **Producer-input emptiness for the graded-bundle residual consumer.**  The `hrep` input of
`GSFactorData.section5DataOffcentreFin_of_gradedBundle_residual` is the same F6 shape at the
graded bundle, hence empty at `d_H ≥ 2`. -/
theorem hrep_gradedBundle_unsat_of_two_le_natDegree
    {x₀ : F} (gb : GSFactorData.GradedBundle (F := F) x₀)
    [_inst_hIrr : Fact (Irreducible gb.H)] [_inst_hPos : Fact (0 < gb.H.natDegree)]
    (hdeg : 2 ≤ gb.H.natDegree) :
    ¬ ∃ Ppoly : F[X][Y],
      polyToPowerSeries𝕃 gb.H Ppoly = gammaGenuine x₀ gb.R gb.H gb.hHyp :=
  GenuinePpolyConverter.hrepG_unsat_of_two_le_natDegree gb.H hdeg gb.hHyp

end BundleDisposition

end LocalSeriesCorrected

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.LocalSeriesCorrected.gammaGenuine_eq_trunc_of_mpPoint_corrected
#print axioms ArkLib.LocalSeriesCorrected.gammaGenuine_eq_trunc_of_localSeries_corrected
#print axioms ArkLib.LocalSeriesCorrected.gammaGenuine_eq_trunc_of_localSeries_dvd_sep_corrected
#print axioms ArkLib.LocalSeriesCorrected.alphaFromBeta_zero_eq_α₀
#print axioms ArkLib.LocalSeriesCorrected.not_hrep_gammaLocal_of_two_le_natDegree
#print axioms ArkLib.LocalSeriesCorrected.hrep_gammaLocal_unsat_of_two_le_natDegree
#print axioms ArkLib.LocalSeriesCorrected.hrep_BcoeffSigned_unsat_of_monic_two_le_natDegree
#print axioms ArkLib.LocalSeriesCorrected.section5DataOffcentreFin_false_of_two_le_natDegree
#print axioms ArkLib.LocalSeriesCorrected.section5DataOffcentreFin_natDegree_eq_one
#print axioms ArkLib.LocalSeriesCorrected.section5DataOffcentreFaithful_false_of_two_le_natDegree
#print axioms ArkLib.LocalSeriesCorrected.section5DataOffcentreFaithful_natDegree_eq_one
#print axioms ArkLib.LocalSeriesCorrected.hrep_producers_unsat_of_two_le_natDegree
#print axioms ArkLib.LocalSeriesCorrected.hrep_genuineMonic_unsat_of_two_le_natDegree
#print axioms ArkLib.LocalSeriesCorrected.hrep_gradedBundle_unsat_of_two_le_natDegree
