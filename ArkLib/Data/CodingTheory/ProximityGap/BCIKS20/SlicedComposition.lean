/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AgreementSupply

/-!
# The fully-sliced grand composition (#302): NO trivariate separability anywhere

The trivariate `R.Separable` is a unit-discriminant condition, generically false (the #304
verdicts); the honest supply is per-place specialized separability on the matching loci
(the `MappedSliceSeparabilityOn` producers).  The agreement lane was sliced in
`Claim510AgreementSupply`; this file slices the TRUNCATION lane and re-lands the grand
composition with no trivariate-separability input at all:

* `matchingPoint_of_decoded_sliced` / `hvanish_of_decoded_sliced` /
  `gammaGenuine_eq_trunc_of_decoded_sliced` — the truncation chain with the per-place
  separability `hsepT` replacing `R.Separable` (the only use of `R.Separable` in the
  `t = 1` chain was deriving exactly this per-place fact);
* **`natDegree_eq_one_of_decoded_fold_sliced`** — the grand composition (hlin from GS-side
  data) with BOTH lanes sliced: every separability input is a per-place fact on a matching
  locus, exactly the shape the in-tree sliced producers emit.

Axiom-clean: `[propext, Classical.choice, Quot.sound]` (audited at end of file).
-/

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Polynomial Polynomial.Bivariate PowerSeries
open BCIKS20AppendixA BCIKS20AppendixA.ClaimA2
open BCIKS20.HenselNumerator
open ArkLib ArkLib.DecodedProximateRoot

namespace BCIKS20.Claim510SlicedComposition

variable {F : Type} [Field F]
variable {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- `matchingPoint_of_decoded` with the per-place separability supplied directly. -/
noncomputable def matchingPoint_of_decoded_sliced {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0) (hlc : H.leadingCoeff = 1)
    (z : F) (root : rationalRoot (H_tilde' H) z)
    (hx : (π_z z root) (ξ x₀ R H hHyp) ≠ 0)
    {w : F[X][Y]} {k : ℕ} (hdeg : w.natDegree < k)
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    (hbase : (w.eval (Polynomial.C x₀)).eval z = root.1)
    (hsepZ : ((R.map (coeffHom_loc x₀ hHyp)).map
      (PowerSeries.map (π_hat_z hHyp z root hx))).Separable)
    (t : ℕ) (hkt : k ≤ t) :
    BetaMatchingVanishes.MatchingPoint x₀ R H hHyp
      (BetaRecGenuineBridge.BcoeffSigned H x₀ R) t z root :=
  matchingPoint_of_localSeries_dvd hHyp hξ hlc z root hx
    (aPDecoded hHyp z root hx w)
    (aPDecoded_dvd hHyp z root hx hdvd)
    (aPDecoded_cong hHyp z root hx hbase)
    hsepZ
    t (coeff_aPDecoded_eq_zero hHyp z root hx (lt_of_lt_of_le hdeg hkt))

variable [Fintype F] [DecidableEq F]

/-- The `hvanish` capstone with per-place separability. -/
theorem hvanish_of_decoded_sliced {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0) (hlc : H.leadingCoeff = 1)
    {matchingSet : Finset F}
    (root : (z : F) → rationalRoot (H_tilde' H) z)
    (hx : ∀ z ∈ matchingSet, (π_z z (root z)) (ξ x₀ R H hHyp) ≠ 0)
    {w : F[X][Y]} {k : ℕ} (hdeg : w.natDegree < k)
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    (hbase : ∀ z ∈ matchingSet, (w.eval (Polynomial.C x₀)).eval z = (root z).1)
    (hsepT : ∀ z, ∀ hz : z ∈ matchingSet,
      ((R.map (coeffHom_loc x₀ hHyp)).map
        (PowerSeries.map (π_hat_z hHyp z (root z) (hx z hz)))).Separable)
    (T : ℕ) :
    ∀ t, k ≤ t → t ≤ T → ∀ z ∈ matchingSet,
      ∃ r : rationalRoot (H_tilde' H) z,
        (π_z z r) (βHensel H x₀ R hHyp t) = 0 :=
  HvanishSupply.hvanish_of_mpPoint H
    (fun t hkt _ z hz =>
      matchingPoint_of_decoded_sliced hHyp hξ hlc z (root z) (hx z hz) hdeg hdvd
        (hbase z hz) (hsepT z hz) t hkt)

/-- Claim 5.8′ (the truncation identity) with per-place separability. -/
theorem gammaGenuine_eq_trunc_of_decoded_sliced {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0)
    {D k : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hmonic : H.Monic) (hd2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hRgrade : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    {Ppoly : F[X][Y]}
    (hrepG : polyToPowerSeries𝕃 H Ppoly
      = ProximityPrize.BCIKS20.GammaGenuine.gammaGenuine x₀ R H hHyp)
    {matchingSet : Finset F}
    (root : (z : F) → rationalRoot (H_tilde' H) z)
    (hx : ∀ z ∈ matchingSet, (π_z z (root z)) (ξ x₀ R H hHyp) ≠ 0)
    {w : F[X][Y]} (hdeg : w.natDegree < k)
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    (hbase : ∀ z ∈ matchingSet, (w.eval (Polynomial.C x₀)).eval z = (root z).1)
    (hsepT : ∀ z, ∀ hz : z ∈ matchingSet,
      ((R.map (coeffHom_loc x₀ hHyp)).map
        (PowerSeries.map (π_hat_z hHyp z (root z) (hx z hz)))).Separable)
    {disc : F[X]} (hdisc : disc ≠ 0)
    (hcover : ∀ z : F, disc.eval z ≠ 0 → z ∈ matchingSet)
    (hbig : gradedCardBudget (Bivariate.natDegreeY R) D H.natDegree Ppoly.natDegree
        + disc.natDegree < Fintype.card F) :
    ProximityPrize.BCIKS20.GammaGenuine.gammaGenuine x₀ R H hHyp
      = (↑(PowerSeries.trunc k
            (ProximityPrize.BCIKS20.GammaGenuine.gammaGenuine x₀ R H hHyp)) : PowerSeries (𝕃 H)) :=
  GenuineTruncationFin.gammaGenuine_eq_trunc_of_graded_disc H hHyp hD hH hmonic hd2 hdHD
    hD_Rx0 hRgrade hrepG
    (hvanish_of_decoded_sliced hHyp hξ hmonic.leadingCoeff root hx hdeg hdvd hbase hsepT
      Ppoly.natDegree)
    hdisc hcover hbig

/-- **THE FULLY-SLICED GRAND COMPOSITION (hlin from GS-side data, no trivariate
separability anywhere)**: both the truncation and agreement lanes consume only per-place
specialized separability on their matching loci — exactly what the in-tree sliced
producers emit. -/
theorem natDegree_eq_one_of_decoded_fold_sliced {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H)
    {D n : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hmonic : H.Monic) (hd2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hRgrade : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    {Ppoly : F[X][Y]}
    (hrepG : polyToPowerSeries𝕃 H Ppoly
      = ProximityPrize.BCIKS20.GammaGenuine.gammaGenuine x₀ R H hHyp)
    (root : (z : F) → rationalRoot (H_tilde' H) z)
    {w : F[X][Y]} (hdeg : w.natDegree < n)
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    -- the truncation lane (sliced)
    {truncSet : Finset F}
    (hbaseT : ∀ z ∈ truncSet, (w.eval (Polynomial.C x₀)).eval z = (root z).1)
    (hsepT : ∀ z ∈ truncSet,
      ((R.map (coeffHom_loc x₀ hHyp)).map
        (PowerSeries.map (π_hat_z hHyp z (root z)
          (BCIKS20.Claim510AgreementSupply.pi_z_xi_ne_zero_of_monic hHyp
            hmonic.leadingCoeff z (root z))))).Separable)
    {disc : F[X]} (hdisc : disc ≠ 0)
    (hcover : ∀ z : F, disc.eval z ≠ 0 → z ∈ truncSet)
    (hbig : gradedCardBudget (Bivariate.natDegreeY R) D H.natDegree Ppoly.natDegree
        + disc.natDegree < Fintype.card F)
    -- the agreement lane (sliced)
    (e : Fin n → F) (he : Function.Injective e) (u₀ u₁ : Fin n → F)
    (matchingSet : Fin n → Finset F)
    (hbaseA : ∀ j, ∀ z ∈ matchingSet j, (w.eval (Polynomial.C x₀)).eval z = (root z).1)
    (hsepA : ∀ j, ∀ z ∈ matchingSet j,
      ((R.map (coeffHom_loc x₀ hHyp)).map
        (PowerSeries.map (π_hat_z hHyp z (root z)
          (BCIKS20.Claim510AgreementSupply.pi_z_xi_ne_zero_of_monic hHyp
            hmonic.leadingCoeff z (root z))))).Separable)
    (hfold : ∀ j, ∀ z ∈ matchingSet j,
      (w.eval (Polynomial.C (e j) + Polynomial.C x₀)).eval z = u₀ j + z * u₁ j)
    -- the numerics
    {xw : ℕ}
    (hξw : weight_Λ_over_𝒪 hH (ξ x₀ R H hHyp) D ≤ (WithBot.some xw : WithBot ℕ))
    (hcard : ∀ j, BCIKS20.Claim510Supply.killBudget n D H.natDegree
        (Bivariate.natDegreeY R) xw * H.natDegree < (matchingSet j).card) :
    H.natDegree = 1 := by
  have hlc : H.leadingCoeff = 1 := hmonic.leadingCoeff
  have hξ : ξ x₀ R H hHyp ≠ 0 :=
    BCIKS20.Claim510AgreementSupply.xi_ne_zero_of_monic hHyp hlc
  have htail : ∀ t, n ≤ t → αGenuine H x₀ R hHyp t = 0 :=
    BCIKS20.Claim59Lagrange.alphaGenuine_tail_zero_of_trunc H hHyp
      (gammaGenuine_eq_trunc_of_decoded_sliced hHyp hξ hD hH hmonic hd2 hdHD hD_Rx0
        hRgrade hrepG root
        (fun z _ => BCIKS20.Claim510AgreementSupply.pi_z_xi_ne_zero_of_monic hHyp hlc z
          (root z))
        hdeg hdvd hbaseT (fun z hz => hsepT z hz) hdisc hcover hbig)
  have hagree := BCIKS20.Claim510AgreementSupply.hagree_of_decoded hHyp hξ hlc e u₀ u₁
    matchingSet root
    (fun z => BCIKS20.Claim510AgreementSupply.pi_z_xi_ne_zero_of_monic hHyp hlc z (root z))
    hdeg hdvd hbaseA hsepA hfold
  have hweight := fun j => BCIKS20.Claim510Supply.weight_killTarget_le H x₀ R hHyp hD hH
    hmonic hd2 hdHD hD_Rx0 hRgrade hξw n (e j) (u₀ j) (u₁ j)
  exact BCIKS20.Claim510Supply.natDegree_eq_one_of_heavy_agreement H x₀ R hHyp hlc
    htail e he u₀ u₁ hD matchingSet hagree hweight hcard

/-! ## Sliced improve/capture hand-off -/

/-- The normalized numerators embed to the genuine coefficients (monic): the lift
identity with the `ξ`-unit power cancelled in `𝕃`. -/
theorem embed_aPre_eq_alphaGenuine_sliced {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H) (hlc : H.leadingCoeff = 1) (t : ℕ) :
    embeddingOf𝒪Into𝕃 H (BCIKS20.Claim510Supply.aPre H x₀ R hHyp hlc t)
      = αGenuine H x₀ R hHyp t := by
  have hlift := BCIKS20.Claim510Weld.liftIdentity_of_monic H x₀ R hHyp hlc t
  rw [S5Genuine.LiftIdentityAt, hlc] at hlift
  simp only [map_one, one_pow, mul_one] at hlift
  have hsplit := congrArg (embeddingOf𝒪Into𝕃 H)
    (BCIKS20.Claim510Supply.betaHensel_eq_aPre_mul_xi_pow H x₀ R hHyp hlc t)
  rw [map_mul, map_pow] at hsplit
  have hu : IsUnit ((embeddingOf𝒪Into𝕃 H) (ξ x₀ R H hHyp) ^ (2 * t - 1)) :=
    ((BCIKS20.HenselNumerator.isUnit_ξ_of_monic (H := H) x₀ R hHyp hlc).map
      (embeddingOf𝒪Into𝕃 H)).pow _
  exact hu.mul_right_cancel (by rw [← hsplit, hlift])

/-- The `𝒪`-level affinization under `paperZ`-linearity (embed-injectivity). -/
theorem aPre_eq_groundAffine_of_paperZ_linear_sliced {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H) (hlc : H.leadingCoeff = 1)
    {a b : ℕ → F}
    (hlin : ∀ t, αGenuine H x₀ R hHyp t
      = liftToFunctionField (H := H)
          (Polynomial.C (a t) + Polynomial.X * Polynomial.C (b t)))
    (t : ℕ) :
    BCIKS20.Claim510Supply.aPre H x₀ R hHyp hlc t
      = BCIKS20.Claim510Kill.groundAffine H (a t) (b t) := by
  refine embeddingOf𝒪Into𝕃_injective (Fact.out (p := 0 < H.natDegree)) ?_
  rw [embed_aPre_eq_alphaGenuine_sliced hHyp hlc t, hlin t,
    BCIKS20.Claim510Kill.embed_groundAffine]

/-- **Sliced affine coefficient reading.**  This is the `Claim510AffinePair` coefficient
identity with the same per-place separability surface used by the sliced decoded-fold
theorem above, instead of a global `R.Separable` hypothesis. -/
theorem taylor_coeff_eq_affine_of_heavy_sliced {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0) (hlc : H.leadingCoeff = 1)
    {a b : ℕ → F}
    (hlin : ∀ t, αGenuine H x₀ R hHyp t
      = liftToFunctionField (H := H)
          (Polynomial.C (a t) + Polynomial.X * Polynomial.C (b t)))
    {w : F[X][Y]}
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    (z : F) (root : rationalRoot (H_tilde' H) z)
    (hx : (π_z z root) (ξ x₀ R H hHyp) ≠ 0)
    (hbase : (w.eval (Polynomial.C x₀)).eval z = root.1)
    (hsepZ : ((R.map (coeffHom_loc x₀ hHyp)).map
      (PowerSeries.map (π_hat_z hHyp z root hx))).Separable)
    (t : ℕ) :
    ((Polynomial.taylor (Polynomial.C x₀) w).coeff t).eval z = a t + z * b t := by
  rw [← BCIKS20.Claim510AgreementSupply.pi_z_aPre_eq_taylor_coeff hHyp hξ hlc z root
      hx hdvd hbase hsepZ t,
    aPre_eq_groundAffine_of_paperZ_linear_sliced hHyp hlc hlin t,
    BCIKS20.Claim510Kill.π_z_groundAffine]

end BCIKS20.Claim510SlicedComposition

/-! ## Axiom audit — all kernel-clean. -/
#print axioms BCIKS20.Claim510SlicedComposition.matchingPoint_of_decoded_sliced
#print axioms BCIKS20.Claim510SlicedComposition.hvanish_of_decoded_sliced
#print axioms BCIKS20.Claim510SlicedComposition.gammaGenuine_eq_trunc_of_decoded_sliced
#print axioms BCIKS20.Claim510SlicedComposition.natDegree_eq_one_of_decoded_fold_sliced
#print axioms BCIKS20.Claim510SlicedComposition.taylor_coeff_eq_affine_of_heavy_sliced
