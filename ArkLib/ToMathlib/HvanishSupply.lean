/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.GenuineTruncationFin
import ArkLib.ToMathlib.MatchingPointFromLocalSeries

/-!
# Issue #304 — the `hvanish` supply: per-point vanishing of `βHensel` from `MatchingPoint`
families

`GenuineTruncationFin.SβLargeAtFin_of_graded_disc` (and its capstone
`gammaGenuine_eq_trunc_of_graded_disc`) consume the per-point vanishing input
```
hvanish : ∀ t ∈ [k, T], ∀ z ∈ matchingSet,
  ∃ r : rationalRoot (H_tilde' H) z, π_z z r (βHensel H x₀ R hHyp t) = 0
```
This file *produces* that input from the standard §5 currency — per-`(t, z)`
`BetaMatchingVanishes.MatchingPoint` families at the signed coefficients
`BcoeffSigned H x₀ R`:

* a `MatchingPoint x₀ R H hHyp Bcoeff t z root` carries
  `.pi_z_eq_zero : π_z z root (betaRec x₀ R H hHyp Bcoeff t) = 0`
  (Hensel uniqueness + the `(X−x₀)^t` coefficient extraction);
* at `Bcoeff := BcoeffSigned H x₀ R` the recursion bridge
  `BetaRecGenuineBridge.betaRec_BcoeffSigned_eq_βHensel` rewrites `betaRec` into `βHensel`,
  so the per-point conclusion IS the `hvanish` body, with the root packaged existentially.

Declarations:

* `hvanish_of_mpPoint` — **the `hvanish` producer**: a finite-range `MatchingPoint` family at
  the signed coefficients yields `GenuineTruncationFin`'s exact `hvanish` shape.
* `gammaGenuine_eq_trunc_of_mpPoint` — **the composed capstone**: the genuine truncation
  identity `γ = γ_k` (Claim 5.8′) with `hvanish` eliminated in favour of the `MatchingPoint`
  family — the currency `MatchingPointFromLocalSeries`/`MpFinSupply` produce.
* `hvanish_of_localSeries` — the construction-level producer: `hvanish` directly from the
  GS-side per-place inputs of `matchingPoint_of_localSeries` (proximate root `aP` with root
  membership, order-0 congruence, separability, and index-`t` coefficient vanishing on the
  finite range).
* `gammaGenuine_eq_trunc_of_localSeries` — the fully-composed capstone from those
  construction-level inputs.
* `hvanish_of_localSeries_dvd_sep` / `gammaGenuine_eq_trunc_of_localSeries_dvd_sep` — the
  GS-handshake variants: root membership as the matching-factor divisibility
  `(Y − C aP) ∣ f_z` and separability inherited from `R.Separable`
  (`specialized_separable_of_R_separable`).

Everything is definitional plumbing over proven bricks; no new mathematical content is
asserted, and no hypothesis is goal-shaped (each producer's inputs are GS-side geometric data
or `MatchingPoint` bundles, never the vanishing conclusion itself).

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, §5 (Claims 5.8/5.8′, §5.2.6), Appendix A.
-/

set_option linter.style.longLine false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2
open BCIKS20.HenselNumerator BCIKS20.HenselNumerator.S5Genuine
open ProximityPrize.BCIKS20.GammaGenuine
open PowerSeries

namespace ArkLib

namespace HvanishSupply

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-! ## Part 1 — `hvanish` from a `MatchingPoint` family at the signed coefficients -/

/-- **The `hvanish` producer.**  A finite-range per-`(t, z)` `MatchingPoint` family at the
signed coefficients `BcoeffSigned H x₀ R` yields the exact `hvanish` input of
`GenuineTruncationFin.SβLargeAtFin_of_graded_disc`: each `MatchingPoint` fires Hensel
uniqueness (`pi_z_eq_zero`, giving `π_z (betaRec … (BcoeffSigned …) t) = 0`), and the
recursion bridge `betaRec_BcoeffSigned_eq_βHensel` transports the vanishing to the concrete
`(A.1)` numerator `βHensel`; the root section is packaged existentially. -/
theorem hvanish_of_mpPoint {x₀ : F} {R : F[X][X][Y]}
    {hHyp : Hypotheses x₀ R H} {k T : ℕ} {matchingSet : Finset F}
    {root : (z : F) → rationalRoot (H_tilde' H) z}
    (mp : ∀ t, k ≤ t → t ≤ T → ∀ z ∈ matchingSet,
      BetaMatchingVanishes.MatchingPoint x₀ R H hHyp
        (BetaRecGenuineBridge.BcoeffSigned H x₀ R) t z (root z)) :
    ∀ t, k ≤ t → t ≤ T → ∀ z ∈ matchingSet,
      ∃ r : rationalRoot (H_tilde' H) z,
        (π_z z r) (βHensel H x₀ R hHyp t) = 0 := by
  intro t hkt htT z hz
  refine ⟨root z, ?_⟩
  rw [← BetaRecGenuineBridge.betaRec_BcoeffSigned_eq_βHensel x₀ R hHyp t]
  exact (mp t hkt htT z hz).pi_z_eq_zero

/-! ## Part 2 — the composed capstone: `γ = γ_k` from the `MatchingPoint` family -/

section Capstone

variable [Fintype F] [DecidableEq F]

/-- **The genuine truncation identity from `MatchingPoint` families (monic).**  Claim 5.8′
`gammaGenuine = trunc k gammaGenuine`, with the `hvanish` input of
`GenuineTruncationFin.gammaGenuine_eq_trunc_of_graded_disc` eliminated in favour of the
finite-range `MatchingPoint` family at the signed coefficients — the standard §5 currency
produced by `matchingPoint_of_localSeries` / `MpFinSupply.mpFin_of_close_word`.  All other
inputs (graded side conditions, the §6 discriminant counting, the genuine Prop-5.5
representative) are unchanged. -/
theorem gammaGenuine_eq_trunc_of_mpPoint {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H)
    {D k : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hmonic : H.Monic) (hd2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hR : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    {Ppoly : F[X][Y]}
    (hrepG : polyToPowerSeries𝕃 H Ppoly = gammaGenuine x₀ R H hHyp)
    {matchingSet : Finset F}
    {root : (z : F) → rationalRoot (H_tilde' H) z}
    (mp : ∀ t, k ≤ t → t ≤ Ppoly.natDegree → ∀ z ∈ matchingSet,
      BetaMatchingVanishes.MatchingPoint x₀ R H hHyp
        (BetaRecGenuineBridge.BcoeffSigned H x₀ R) t z (root z))
    {disc : F[X]} (hdisc : disc ≠ 0)
    (hcover : ∀ z : F, disc.eval z ≠ 0 → z ∈ matchingSet)
    (hbig : gradedCardBudget (Bivariate.natDegreeY R) D H.natDegree Ppoly.natDegree
        + disc.natDegree < Fintype.card F) :
    gammaGenuine x₀ R H hHyp
      = (↑(PowerSeries.trunc k (gammaGenuine x₀ R H hHyp)) : PowerSeries (𝕃 H)) :=
  GenuineTruncationFin.gammaGenuine_eq_trunc_of_graded_disc H hHyp hD hH hmonic hd2 hdHD
    hD_Rx0 hR hrepG (hvanish_of_mpPoint H mp) hdisc hcover hbig

end Capstone

/-! ## Part 3 — the construction-level producers (GS-side inputs)

`matchingPoint_of_localSeries` builds the per-`(t, z)` `MatchingPoint` at the signed
coefficients from exclusively GS-side data: the proximate root `aP z` (root membership,
order-0 congruence with `βHensel 0`, index-`t` coefficient vanishing) and separability of the
specialized matching polynomial.  Threading it pointwise over the finite range gives
`hvanish` (and hence the truncation capstone) directly from those construction-level
inputs. -/

/-- **`hvanish` from the local-series construction.**  The per-point vanishing input of
`SβLargeAtFin_of_graded_disc`, produced from the GS-side per-place data: for each matching
place `z`, a proximate root `aP z` that is a root of the specialized matching polynomial,
agrees with `βHensel 0` at order 0, lives over a separable specialization, and has vanishing
`t`-th coefficient for every `t` in the finite range. -/
theorem hvanish_of_localSeries {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0) (hlc : H.leadingCoeff = 1)
    {k T : ℕ} {matchingSet : Finset F}
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
    (haP_coeff : ∀ t, k ≤ t → t ≤ T → ∀ z ∈ matchingSet,
      PowerSeries.coeff t (aP z) = 0) :
    ∀ t, k ≤ t → t ≤ T → ∀ z ∈ matchingSet,
      ∃ r : rationalRoot (H_tilde' H) z,
        (π_z z r) (βHensel H x₀ R hHyp t) = 0 :=
  hvanish_of_mpPoint H (root := root) fun t hkt htT z hz =>
    matchingPoint_of_localSeries hHyp hξ hlc z (root z) (hx z hz) (aP z)
      (haP_root z hz) (haP_cong z hz) (hsep z hz) t (haP_coeff t hkt htT z hz)

/-- **The GS-handshake `hvanish` producer.**  Same as `hvanish_of_localSeries`, but the root
membership arrives as the matching-factor divisibility `(Y − C (aP z)) ∣ f_z` (the exact
shape of the GS matching-factor cargo) and separability is inherited from `R.Separable`
itself via `specialized_separable_of_R_separable`. -/
theorem hvanish_of_localSeries_dvd_sep {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0) (hlc : H.leadingCoeff = 1) (hRsep : R.Separable)
    {k T : ℕ} {matchingSet : Finset F}
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
    (haP_coeff : ∀ t, k ≤ t → t ≤ T → ∀ z ∈ matchingSet,
      PowerSeries.coeff t (aP z) = 0) :
    ∀ t, k ≤ t → t ≤ T → ∀ z ∈ matchingSet,
      ∃ r : rationalRoot (H_tilde' H) z,
        (π_z z r) (βHensel H x₀ R hHyp t) = 0 :=
  hvanish_of_localSeries H hHyp hξ hlc root hx aP
    (fun z hz => Polynomial.dvd_iff_isRoot.mp (hdvd z hz))
    haP_cong
    (fun z hz => specialized_separable_of_R_separable hHyp z (root z) (hx z hz) hRsep)
    haP_coeff

/-! ## Part 4 — the fully-composed capstones from construction-level inputs -/

section FullCapstone

variable [Fintype F] [DecidableEq F]

/-- **The genuine truncation identity from local-series construction data (monic).**
Claim 5.8′ `gammaGenuine = trunc k gammaGenuine`, end-to-end from:
* the GS-side per-place data (proximate roots `aP z`: root membership, order-0 agreement
  with `βHensel 0`, separable specialization, index-`t` vanishing on `[k, deg Ppoly]`);
* the §6 discriminant counting (`hdisc`/`hcover`/`hbig`);
* the graded side conditions;
* the genuine Prop-5.5 representative `hrepG`.

No `MatchingPoint`, no `hvanish`, no unbounded-range largeness — every input is
construction-level. -/
theorem gammaGenuine_eq_trunc_of_localSeries {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H)
    {D k : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hmonic : H.Monic) (hd2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hR : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    {Ppoly : F[X][Y]}
    (hrepG : polyToPowerSeries𝕃 H Ppoly = gammaGenuine x₀ R H hHyp)
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
    (haP_coeff : ∀ t, k ≤ t → t ≤ Ppoly.natDegree → ∀ z ∈ matchingSet,
      PowerSeries.coeff t (aP z) = 0)
    {disc : F[X]} (hdisc : disc ≠ 0)
    (hcover : ∀ z : F, disc.eval z ≠ 0 → z ∈ matchingSet)
    (hbig : gradedCardBudget (Bivariate.natDegreeY R) D H.natDegree Ppoly.natDegree
        + disc.natDegree < Fintype.card F) :
    gammaGenuine x₀ R H hHyp
      = (↑(PowerSeries.trunc k (gammaGenuine x₀ R H hHyp)) : PowerSeries (𝕃 H)) :=
  GenuineTruncationFin.gammaGenuine_eq_trunc_of_graded_disc H hHyp hD hH hmonic hd2 hdHD
    hD_Rx0 hR hrepG
    (hvanish_of_localSeries H hHyp hξ hmonic.leadingCoeff root hx aP haP_root haP_cong
      hsep haP_coeff)
    hdisc hcover hbig

/-- **The GS-handshake truncation capstone (monic).**  As
`gammaGenuine_eq_trunc_of_localSeries`, with root membership as the matching-factor
divisibility `(Y − C (aP z)) ∣ f_z` and separability inherited from `R.Separable` — the
exact cargo shapes of the GS factor handshake. -/
theorem gammaGenuine_eq_trunc_of_localSeries_dvd_sep {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H)
    {D k : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hmonic : H.Monic) (hd2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hR : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    {Ppoly : F[X][Y]}
    (hrepG : polyToPowerSeries𝕃 H Ppoly = gammaGenuine x₀ R H hHyp)
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
    (haP_coeff : ∀ t, k ≤ t → t ≤ Ppoly.natDegree → ∀ z ∈ matchingSet,
      PowerSeries.coeff t (aP z) = 0)
    {disc : F[X]} (hdisc : disc ≠ 0)
    (hcover : ∀ z : F, disc.eval z ≠ 0 → z ∈ matchingSet)
    (hbig : gradedCardBudget (Bivariate.natDegreeY R) D H.natDegree Ppoly.natDegree
        + disc.natDegree < Fintype.card F) :
    gammaGenuine x₀ R H hHyp
      = (↑(PowerSeries.trunc k (gammaGenuine x₀ R H hHyp)) : PowerSeries (𝕃 H)) :=
  GenuineTruncationFin.gammaGenuine_eq_trunc_of_graded_disc H hHyp hD hH hmonic hd2 hdHD
    hD_Rx0 hR hrepG
    (hvanish_of_localSeries_dvd_sep H hHyp hξ hmonic.leadingCoeff hRsep root hx aP hdvd
      haP_cong haP_coeff)
    hdisc hcover hbig

end FullCapstone

end HvanishSupply

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.HvanishSupply.hvanish_of_mpPoint
#print axioms ArkLib.HvanishSupply.gammaGenuine_eq_trunc_of_mpPoint
#print axioms ArkLib.HvanishSupply.hvanish_of_localSeries
#print axioms ArkLib.HvanishSupply.hvanish_of_localSeries_dvd_sep
#print axioms ArkLib.HvanishSupply.gammaGenuine_eq_trunc_of_localSeries
#print axioms ArkLib.HvanishSupply.gammaGenuine_eq_trunc_of_localSeries_dvd_sep
