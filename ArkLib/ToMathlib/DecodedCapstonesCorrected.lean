/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.BranchCertificates
import ArkLib.ToMathlib.GenuinePpolyConverter

/-!
# Issue #304 — the decoded capstones re-plumbed onto the CORRECTED representative (F6 repair)

The F6 finding (`GenuinePpolyConverter`) kernel-proved that the legacy representative shape
`hrepG : polyToPowerSeries𝕃 H Ppoly = gammaGenuine …` is **unsatisfiable for every
`d_H ≥ 2`** (the ground-line coefficients cannot reach `α₀ = T/W`).  The decoded-surface
capstones (`DecodedProximateRoot.gammaGenuine_eq_trunc_of_decoded`,
`DecodedRootSupply.gammaGenuine_eq_trunc_of_decoded_roots`,
`BranchCertificates.gammaGenuine_eq_trunc_global`) consumed exactly that shape, so they were
vacuous in the target regime.  This file restates all three on the satisfiable corrected
representative `hrepT : polyToPowerSeries𝕃T H P₀ P₁ = gammaGenuine …` (T-affine coefficients;
producible at monic `d_H ≤ 2` by
`GenuinePpolyConverter.exists_corrected_representative_of_monic_natDegree_le_two`), with the
tail index `max (deg P₀) (deg P₁)`:

* `gammaGenuine_eq_trunc_of_decoded_corrected` — roots given, base-point hypothesis explicit;
* `gammaGenuine_eq_trunc_of_decoded_roots_corrected` — roots PRODUCED from the GS split +
  branch separation;
* `gammaGenuine_eq_trunc_global_corrected` — **the global form**: matching set constructed
  from the two certificate polynomials; every hypothesis a single global finite fact, and the
  representative input now genuinely satisfiable.

## References
* [BCIKS20] §5–§6, Appendix A; the F6 finding and the corrected shape are documented in
  `GenuinePpolyConverter.lean`.
-/

set_option linter.style.longLine false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2
open PowerSeries
open ProximityPrize.BCIKS20.GammaGenuine

namespace ArkLib

namespace DecodedCapstonesCorrected

variable {F : Type} [Field F]
variable {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
variable [Fintype F] [DecidableEq F]

/-- **The decoded capstone on the corrected representative.**  As
`DecodedProximateRoot.gammaGenuine_eq_trunc_of_decoded`, with the F6-unsatisfiable `hrepG`
replaced by the satisfiable T-affine `hrepT` and the tail index `max (deg P₀) (deg P₁)`. -/
theorem gammaGenuine_eq_trunc_of_decoded_corrected {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0)
    {D k : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hmonic : H.Monic) (hd2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hRgrade : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    {P₀ P₁ : F[X][Y]}
    (hrepT : GenuinePpolyConverter.polyToPowerSeries𝕃T H P₀ P₁ = gammaGenuine x₀ R H hHyp)
    {matchingSet : Finset F}
    (root : (z : F) → rationalRoot (H_tilde' H) z)
    (hx : ∀ z ∈ matchingSet, (π_z z (root z)) (ξ x₀ R H hHyp) ≠ 0)
    {w : F[X][Y]} (hdeg : w.natDegree < k)
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    (hbase : ∀ z ∈ matchingSet, (w.eval (Polynomial.C x₀)).eval z = (root z).1)
    (hR : R.Separable)
    {disc : F[X]} (hdisc : disc ≠ 0)
    (hcover : ∀ z : F, disc.eval z ≠ 0 → z ∈ matchingSet)
    (hbig : gradedCardBudget (Bivariate.natDegreeY R) D H.natDegree
        (max P₀.natDegree P₁.natDegree) + disc.natDegree < Fintype.card F) :
    gammaGenuine x₀ R H hHyp
      = (↑(PowerSeries.trunc k (gammaGenuine x₀ R H hHyp)) : PowerSeries (𝕃 H)) :=
  GenuinePpolyConverter.gammaGenuine_eq_trunc_of_graded_disc_corrected H hHyp hD hH hmonic
    hd2 hdHD hD_Rx0 hRgrade hrepT
    (DecodedProximateRoot.hvanish_of_decoded hHyp hξ hmonic.leadingCoeff root hx hdeg hdvd
      hbase hR (max P₀.natDegree P₁.natDegree))
    hdisc hcover hbig

/-- **The decoded-roots capstone on the corrected representative.**  As
`DecodedRootSupply.gammaGenuine_eq_trunc_of_decoded_roots` (roots PRODUCED from the GS split
+ branch separation), with `hrepG` replaced by the satisfiable `hrepT`. -/
theorem gammaGenuine_eq_trunc_of_decoded_roots_corrected {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0)
    {D k : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hmonic : H.Monic) (hd2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hRgrade : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    {P₀ P₁ : F[X][Y]}
    (hrepT : GenuinePpolyConverter.polyToPowerSeries𝕃T H P₀ P₁ = gammaGenuine x₀ R H hHyp)
    {matchingSet : Finset F} {w G : F[X][Y]}
    (hsplit : Bivariate.evalX (Polynomial.C x₀) R = H * G)
    (hdeg : w.natDegree < k)
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    (hbranch : ∀ z ∈ matchingSet,
      Polynomial.evalEval z ((w.eval (Polynomial.C x₀)).eval z) G ≠ 0)
    (hR : R.Separable)
    (hx : ∀ z (hz : z ∈ matchingSet),
      (π_z z (DecodedRootSupply.rootDecoded (Fact.out) hsplit hdvd z (hbranch z hz)))
        (ξ x₀ R H hHyp) ≠ 0)
    {disc : F[X]} (hdisc : disc ≠ 0)
    (hcover : ∀ z : F, disc.eval z ≠ 0 → z ∈ matchingSet)
    (hbig : gradedCardBudget (Bivariate.natDegreeY R) D H.natDegree
        (max P₀.natDegree P₁.natDegree) + disc.natDegree < Fintype.card F) :
    gammaGenuine x₀ R H hHyp
      = (↑(PowerSeries.trunc k (gammaGenuine x₀ R H hHyp)) : PowerSeries (𝕃 H)) :=
  GenuinePpolyConverter.gammaGenuine_eq_trunc_of_graded_disc_corrected H hHyp hD hH hmonic
    hd2 hdHD hD_Rx0 hRgrade hrepT
    (DecodedRootSupply.hvanish_of_decoded_roots hHyp hξ hmonic.leadingCoeff hsplit hdeg hdvd
      hbranch hR (max P₀.natDegree P₁.natDegree) hx)
    hdisc hcover hbig

/-- **THE GLOBAL CAPSTONE, F6-REPAIRED: Claim 5.8′ from purely global, jointly satisfiable
data.**  As `BranchCertificates.gammaGenuine_eq_trunc_global` — matching set constructed from
the two certificate polynomials, zero per-place hypotheses — with the representative input
now the satisfiable corrected `hrepT` (producible at monic `d_H ≤ 2` by
`exists_corrected_representative_of_monic_natDegree_le_two` from the truncation itself). -/
theorem gammaGenuine_eq_trunc_global_corrected {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0)
    {D k : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hmonic : H.Monic) (hd2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hRgrade : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    {P₀ P₁ : F[X][Y]}
    (hrepT : GenuinePpolyConverter.polyToPowerSeries𝕃T H P₀ P₁ = gammaGenuine x₀ R H hHyp)
    {w G : F[X][Y]}
    (hsplit : Bivariate.evalX (Polynomial.C x₀) R = H * G)
    (hdeg : w.natDegree < k)
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    (hR : R.Separable)
    (hbr : G.eval (w.eval (Polynomial.C x₀)) ≠ 0)
    (hxi : (canonicalRepOf𝒪 hH (ξ x₀ R H hHyp)).eval (w.eval (Polynomial.C x₀)) ≠ 0)
    (hbig : gradedCardBudget (Bivariate.natDegreeY R) D H.natDegree
        (max P₀.natDegree P₁.natDegree)
        + ((G.eval (w.eval (Polynomial.C x₀)))
            * (canonicalRepOf𝒪 hH (ξ x₀ R H hHyp)).eval
                (w.eval (Polynomial.C x₀))).natDegree
        < Fintype.card F) :
    gammaGenuine x₀ R H hHyp
      = (↑(PowerSeries.trunc k (gammaGenuine x₀ R H hHyp)) : PowerSeries (𝕃 H)) := by
  classical
  set vC : F[X] := w.eval (Polynomial.C x₀) with hvC
  set dBr : F[X] := G.eval vC with hdBr
  set dXi : F[X] := (canonicalRepOf𝒪 hH (ξ x₀ R H hHyp)).eval vC with hdXi
  have hdisc : dBr * dXi ≠ 0 := mul_ne_zero hbr hxi
  set ms : Finset F := BranchCertificates.nonvanishingLocus (dBr * dXi) with hms
  have hbranch : ∀ z ∈ ms, Polynomial.evalEval z (vC.eval z) G ≠ 0 := by
    intro z hz
    have h := (BranchCertificates.mem_nonvanishingLocus).mp hz
    rw [Polynomial.eval_mul] at h
    have hBr : dBr.eval z ≠ 0 := fun h0 => h (by rw [h0, zero_mul])
    rw [hdBr] at hBr
    rw [← BranchCertificates.branchCert_eval G w x₀ z]
    exact hBr
  have hx : ∀ z (hz : z ∈ ms),
      (π_z z (DecodedRootSupply.rootDecoded hH hsplit hdvd z (hbranch z hz)))
        (ξ x₀ R H hHyp) ≠ 0 := by
    intro z hz
    have h := (BranchCertificates.mem_nonvanishingLocus).mp hz
    rw [Polynomial.eval_mul] at h
    have hXi : dXi.eval z ≠ 0 := fun h0 => h (by rw [h0, mul_zero])
    rw [BranchCertificates.xiCert_eval_monic hH hmonic.leadingCoeff hsplit hdvd z
      (hbranch z hz)]
    rw [hdXi] at hXi
    exact hXi
  exact gammaGenuine_eq_trunc_of_decoded_roots_corrected hHyp hξ hD hH hmonic hd2 hdHD
    hD_Rx0 hRgrade hrepT hsplit hdeg hdvd hbranch hR hx hdisc
    (fun z hz => (BranchCertificates.mem_nonvanishingLocus).mpr hz) hbig

end DecodedCapstonesCorrected

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.DecodedCapstonesCorrected.gammaGenuine_eq_trunc_of_decoded_corrected
#print axioms ArkLib.DecodedCapstonesCorrected.gammaGenuine_eq_trunc_of_decoded_roots_corrected
#print axioms ArkLib.DecodedCapstonesCorrected.gammaGenuine_eq_trunc_global_corrected
