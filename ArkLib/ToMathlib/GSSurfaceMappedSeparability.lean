/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.GSSurfaceSupply
import ArkLib.ToMathlib.DiscriminantSeparableConverse

/-!
# Issues #301/#302/#304 — the trivariate-separability consumer consolidated to per-place
residue separability (`MappedSliceSeparability`)

**The audit.**  The open Node-B input `hR : R.Separable` (trivariate separability over the
non-field base `F[Z][X]`, `GSSurfaceSupply.SurfaceSeparabilitySupply`) is consumed by the
entire decoded-capstone chain through **exactly one** lemma:
`specialized_separable_of_R_separable` (`MatchingPointFromLocalSeries.lean`), which only
ever uses the *image* separability of the doubly-mapped matching polynomial

  `(R.map (coeffHom_loc x₀ hHyp)).map (PowerSeries.map (π̂_z …)) ∈ (PowerSeries F)[Y]`

at each place `(z, root)` of the matching set.  This file therefore:

1. names that genuinely weaker per-place hypothesis (`MappedSliceSeparability`, with the
   bridge `MappedSliceSeparability.of_separable` from the trivariate Prop — so it is
   *strictly* below Node B);

2. **produces it from FIELD-level data**: `PowerSeries F` is a local ring whose units are
   detected by the constant term, so a polynomial over it whose **residue** (constant-term
   image in `F[Y]`) has the same degree and is separable *over the field `F`* is already
   separable over `PowerSeries F` (`separable_of_powerSeries_residue`: residue separable ⟹
   residue `discr ≠ 0` ⟹ `discr` and `leadingCoeff` are units of `PowerSeries F` ⟹ Bézout
   by the in-tree Lemma 2′ `separable_of_leadingCoeff_isUnit_of_discr_isUnit`).  This turns
   the open non-field-base separability into a per-place finite *field* condition — the
   same kind of datum the good-centre discriminant counting
   (`GSSurfaceRadicalSupply.exists_good_centre_slice_discr_ne_zero`) supplies
   (`MappedSliceSeparability.of_residue`);

3. re-proves the capstone chain on the weaker hypothesis, mirroring the `hR`-consuming
   chain declaration-for-declaration with `hsepM z root hx` in place of
   `specialized_separable_of_R_separable … hR`:
   `matchingPoint_of_decoded_mapped` → `mpFin_of_decoded_roots_mapped` →
   `hvanish_of_decoded_roots_mapped` → `gammaGenuine_eq_trunc_of_decoded_roots_mapped` →
   `gammaGenuine_eq_trunc_global_mapped` → `gammaGenuine_eq_trunc_of_surface_mapped`
   (the `GSSurfaceSupply` §5 shape with `hsplit` eliminated via `cofactor`).

The strong-hypothesis originals (`…_of_decoded_roots_corrected`,
`…_global_corrected`, `gammaGenuine_eq_trunc_of_surface`) remain valid; they now factor
through these via `MappedSliceSeparability.of_separable`.  Nothing here discharges Node B
itself — it relocates the open content from "Bézout in the trivariate ring `F[Z][X][Y]`"
(false outside unit-resultant regimes) to "per-place residue separability over `F`", which
is finite, discriminant-checkable data.

## References
* [BCIKS20] §5–§6, Appendix A; the F-series ledger on issue #304.
-/

set_option linter.style.longLine false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2
open PowerSeries
open ProximityPrize.BCIKS20.GammaGenuine

namespace ArkLib

namespace MappedSeparability

/-! ## §1 — the `PowerSeries` residue-separability brick -/

/-- **Separability over `PowerSeries F` from residue separability over `F`.**  If the
residue `f.map (constantCoeff F) : F[Y]` of `f : (PowerSeries F)[Y]` has the same (positive)
degree and is separable over the *field* `F`, then `f` is separable over `PowerSeries F`:
the residue separability gives `discr ≠ 0` over `F`, the discriminant specializes along the
degree-preserving residue map, units of `PowerSeries F` are exactly the series with nonzero
constant term, and Lemma 2′ (`separable_of_leadingCoeff_isUnit_of_discr_isUnit`) converts
the two unit conditions into the Bézout identity.  This is the local-ring mechanism that
makes the per-place separability hypothesis *field-checkable*. -/
theorem separable_of_powerSeries_residue {F : Type*} [Field F] {f : (PowerSeries F)[X]}
    (hdeg : 0 < f.natDegree)
    (hmap : (f.map (PowerSeries.constantCoeff (R := F))).natDegree = f.natDegree)
    (hsep : (f.map (PowerSeries.constantCoeff (R := F))).Separable) :
    f.Separable := by
  have hresdeg : 0 < (f.map (PowerSeries.constantCoeff (R := F))).natDegree := by
    rw [hmap]; exact hdeg
  have hd0 : (f.map (PowerSeries.constantCoeff (R := F))).discr ≠ 0 :=
    Polynomial.discr_ne_zero_of_separable hresdeg hsep
  have hdres : (f.map (PowerSeries.constantCoeff (R := F))).discr
      = (PowerSeries.constantCoeff (R := F)) f.discr :=
    Polynomial.discr_map_of_natDegree_preserved hdeg hmap
  have hdunit : IsUnit f.discr := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    rw [hdres] at hd0
    exact isUnit_iff_ne_zero.mpr hd0
  have hfne : f.map (PowerSeries.constantCoeff (R := F)) ≠ 0 := by
    intro h0
    rw [h0, Polynomial.natDegree_zero] at hresdeg
    exact absurd hresdeg (lt_irrefl 0)
  have hlcres : (PowerSeries.constantCoeff (R := F)) f.leadingCoeff ≠ 0 := by
    have h1 : (f.map (PowerSeries.constantCoeff (R := F))).leadingCoeff ≠ 0 :=
      Polynomial.leadingCoeff_ne_zero.mpr hfne
    rwa [Polynomial.leadingCoeff, hmap, Polynomial.coeff_map] at h1
  have hlcunit : IsUnit f.leadingCoeff := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    exact isUnit_iff_ne_zero.mpr hlcres
  exact Polynomial.separable_of_leadingCoeff_isUnit_of_discr_isUnit hdeg hlcunit hdunit

/-! ## §2 — the weak per-place hypothesis and its producers -/

variable {F : Type} [Field F]
variable {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- **The consolidated separability hypothesis** — the exact (and only) shape in which the
decoded-capstone chain consumes `hR : R.Separable`: separability of the doubly-mapped
matching polynomial over `PowerSeries F`, at each place `(z, root)` with nonvanishing
`ξ`-image.  Strictly weaker than Node B (`SurfaceSeparabilitySupply`, see `of_separable`),
and producible from per-place *field-level residue* data (see `of_residue` +
`separable_of_powerSeries_residue`). -/
def MappedSliceSeparability {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H) : Prop :=
  ∀ (z : F) (root : rationalRoot (H_tilde' H) z)
    (hx : (π_z z root) (ξ x₀ R H hHyp) ≠ 0),
    ((R.map (coeffHom_loc x₀ hHyp)).map
      (PowerSeries.map (π_hat_z hHyp z root hx))).Separable

/-- The trivariate Node B implies the consolidated hypothesis (so every theorem below is a
strict generalization of its `hR`-consuming original). -/
theorem MappedSliceSeparability.of_separable {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H) (hR : R.Separable) :
    MappedSliceSeparability hHyp :=
  fun z root hx => specialized_separable_of_R_separable hHyp z root hx hR

/-- **The consolidated hypothesis from per-place field-level residue data**: at each place,
positive degree + degree preservation under the constant-term residue + separability of the
residue polynomial *over the field `F`* suffice.  This is the honest producible surface the
open Node B is relocated to. -/
theorem MappedSliceSeparability.of_residue {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H)
    (hres : ∀ (z : F) (root : rationalRoot (H_tilde' H) z)
      (hx : (π_z z root) (ξ x₀ R H hHyp) ≠ 0),
      0 < ((R.map (coeffHom_loc x₀ hHyp)).map
        (PowerSeries.map (π_hat_z hHyp z root hx))).natDegree ∧
      (((R.map (coeffHom_loc x₀ hHyp)).map
        (PowerSeries.map (π_hat_z hHyp z root hx))).map
          (PowerSeries.constantCoeff (R := F))).natDegree
        = ((R.map (coeffHom_loc x₀ hHyp)).map
            (PowerSeries.map (π_hat_z hHyp z root hx))).natDegree ∧
      (((R.map (coeffHom_loc x₀ hHyp)).map
        (PowerSeries.map (π_hat_z hHyp z root hx))).map
          (PowerSeries.constantCoeff (R := F))).Separable) :
    MappedSliceSeparability hHyp :=
  fun z root hx =>
    separable_of_powerSeries_residue (hres z root hx).1 (hres z root hx).2.1
      (hres z root hx).2.2

/-! ## §3 — the capstone chain on the weak hypothesis -/

/-- `DecodedProximateRoot.matchingPoint_of_decoded` on the consolidated hypothesis. -/
noncomputable def matchingPoint_of_decoded_mapped {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0) (hlc : H.leadingCoeff = 1)
    (z : F) (root : rationalRoot (H_tilde' H) z)
    (hx : (π_z z root) (ξ x₀ R H hHyp) ≠ 0)
    {w : F[X][Y]} {k : ℕ} (hdeg : w.natDegree < k)
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    (hbase : (w.eval (Polynomial.C x₀)).eval z = root.1)
    (hsepM : MappedSliceSeparability hHyp)
    (t : ℕ) (hkt : k ≤ t) :
    BetaMatchingVanishes.MatchingPoint x₀ R H hHyp
      (BetaRecGenuineBridge.BcoeffSigned H x₀ R) t z root :=
  matchingPoint_of_localSeries_dvd hHyp hξ hlc z root hx
    (DecodedProximateRoot.aPDecoded hHyp z root hx w)
    (DecodedProximateRoot.aPDecoded_dvd hHyp z root hx hdvd)
    (DecodedProximateRoot.aPDecoded_cong hHyp z root hx hbase)
    (hsepM z root hx)
    t (DecodedProximateRoot.coeff_aPDecoded_eq_zero hHyp z root hx
      (lt_of_lt_of_le hdeg hkt))

/-- `DecodedRootSupply.mpFin_of_decoded_roots` on the consolidated hypothesis. -/
noncomputable def mpFin_of_decoded_roots_mapped {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0) (hlc : H.leadingCoeff = 1)
    {matchingSet : Finset F} {w G : F[X][Y]} {k : ℕ}
    (hsplit : Bivariate.evalX (Polynomial.C x₀) R = H * G)
    (hdeg : w.natDegree < k)
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    (hbranch : ∀ z ∈ matchingSet,
      Polynomial.evalEval z ((w.eval (Polynomial.C x₀)).eval z) G ≠ 0)
    (hsepM : MappedSliceSeparability hHyp) (T : ℕ)
    (hx : ∀ z (hz : z ∈ matchingSet),
      (π_z z (DecodedRootSupply.rootDecoded (Fact.out) hsplit hdvd z (hbranch z hz)))
        (ξ x₀ R H hHyp) ≠ 0) :
    ∀ t, k ≤ t → t ≤ T → ∀ z, ∀ hz : z ∈ matchingSet,
      BetaMatchingVanishes.MatchingPoint x₀ R H hHyp
        (BetaRecGenuineBridge.BcoeffSigned H x₀ R) t z
        (DecodedRootSupply.rootDecoded (Fact.out) hsplit hdvd z (hbranch z hz)) :=
  fun t hkt _ z hz =>
    matchingPoint_of_decoded_mapped hHyp hξ hlc z
      (DecodedRootSupply.rootDecoded (Fact.out) hsplit hdvd z (hbranch z hz)) (hx z hz)
      hdeg hdvd
      (DecodedRootSupply.rootDecoded_val_monic (Fact.out) hlc hsplit hdvd z (hbranch z hz))
      hsepM t hkt

/-- `DecodedRootSupply.hvanish_of_decoded_roots` on the consolidated hypothesis. -/
theorem hvanish_of_decoded_roots_mapped {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0) (hlc : H.leadingCoeff = 1)
    {matchingSet : Finset F} {w G : F[X][Y]} {k : ℕ}
    (hsplit : Bivariate.evalX (Polynomial.C x₀) R = H * G)
    (hdeg : w.natDegree < k)
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    (hbranch : ∀ z ∈ matchingSet,
      Polynomial.evalEval z ((w.eval (Polynomial.C x₀)).eval z) G ≠ 0)
    (hsepM : MappedSliceSeparability hHyp) (T : ℕ)
    (hx : ∀ z (hz : z ∈ matchingSet),
      (π_z z (DecodedRootSupply.rootDecoded (Fact.out) hsplit hdvd z (hbranch z hz)))
        (ξ x₀ R H hHyp) ≠ 0) :
    ∀ t, k ≤ t → t ≤ T → ∀ z ∈ matchingSet,
      ∃ r : rationalRoot (H_tilde' H) z,
        (π_z z r) (BCIKS20.HenselNumerator.βHensel H x₀ R hHyp t) = 0 := by
  intro t hkt htT z hz
  refine ⟨DecodedRootSupply.rootDecoded (Fact.out) hsplit hdvd z (hbranch z hz), ?_⟩
  rw [← BetaRecGenuineBridge.betaRec_BcoeffSigned_eq_βHensel x₀ R hHyp t]
  exact (mpFin_of_decoded_roots_mapped hHyp hξ hlc hsplit hdeg hdvd hbranch hsepM T
    hx t hkt htT z hz).pi_z_eq_zero

section Capstones

variable [Fintype F] [DecidableEq F]

/-- **`gammaGenuine_eq_trunc_of_decoded_roots_corrected` on the consolidated hypothesis**:
the decoded-roots truncation capstone with `hR : R.Separable` weakened to
`MappedSliceSeparability hHyp`. -/
theorem gammaGenuine_eq_trunc_of_decoded_roots_mapped {x₀ : F} {R : F[X][X][Y]}
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
    (hsepM : MappedSliceSeparability hHyp)
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
    (hvanish_of_decoded_roots_mapped hHyp hξ hmonic.leadingCoeff hsplit hdeg hdvd
      hbranch hsepM (max P₀.natDegree P₁.natDegree) hx)
    hdisc hcover hbig

/-- **`gammaGenuine_eq_trunc_global_corrected` on the consolidated hypothesis**: THE global
F6-repaired capstone with `hR : R.Separable` weakened to `MappedSliceSeparability hHyp`
(matching set constructed from the two certificate polynomials, zero per-place
hypotheses). -/
theorem gammaGenuine_eq_trunc_global_mapped {x₀ : F} {R : F[X][X][Y]}
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
    (hsepM : MappedSliceSeparability hHyp)
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
  exact gammaGenuine_eq_trunc_of_decoded_roots_mapped hHyp hξ hD hH hmonic hd2 hdHD
    hD_Rx0 hRgrade hrepT hsplit hdeg hdvd hbranch hsepM hx hdisc
    (fun z hz => (BranchCertificates.mem_nonvanishingLocus).mpr hz) hbig

/-- **`GSSurfaceSupply.gammaGenuine_eq_trunc_of_surface` on the consolidated hypothesis**:
the §5 shape with `hsplit` eliminated (`G := cofactor hHyp`) and `hR : R.Separable`
weakened to `MappedSliceSeparability hHyp`.  Together with
`MappedSliceSeparability.of_residue`, the trivariate Node B is fully relocated to per-place
field-level residue data in the deepest available capstone shape. -/
theorem gammaGenuine_eq_trunc_of_surface_mapped {x₀ : F} {R : F[X][X][Y]}
    (hHyp : Hypotheses x₀ R H)
    (hξ : ξ x₀ R H hHyp ≠ 0)
    {D k : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hmonic : H.Monic) (hd2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hRgrade : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    {P₀ P₁ : F[X][Y]}
    (hrepT : GenuinePpolyConverter.polyToPowerSeries𝕃T H P₀ P₁ = gammaGenuine x₀ R H hHyp)
    {w : F[X][Y]} (hdeg : w.natDegree < k)
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    (hsepM : MappedSliceSeparability hHyp)
    (hbr : (GSSurfaceSupply.cofactor hHyp).eval (w.eval (Polynomial.C x₀)) ≠ 0)
    (hxi : (canonicalRepOf𝒪 hH (ξ x₀ R H hHyp)).eval (w.eval (Polynomial.C x₀)) ≠ 0)
    (hbig : gradedCardBudget (Bivariate.natDegreeY R) D H.natDegree
        (max P₀.natDegree P₁.natDegree)
        + (((GSSurfaceSupply.cofactor hHyp).eval (w.eval (Polynomial.C x₀)))
            * (canonicalRepOf𝒪 hH (ξ x₀ R H hHyp)).eval
                (w.eval (Polynomial.C x₀))).natDegree
        < Fintype.card F) :
    gammaGenuine x₀ R H hHyp
      = (↑(PowerSeries.trunc k (gammaGenuine x₀ R H hHyp)) : PowerSeries (𝕃 H)) :=
  gammaGenuine_eq_trunc_global_mapped hHyp hξ hD hH hmonic hd2 hdHD hD_Rx0 hRgrade hrepT
    (GSSurfaceSupply.cofactor_spec hHyp) hdeg hdvd hsepM hbr hxi hbig

end Capstones

end MappedSeparability

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.MappedSeparability.separable_of_powerSeries_residue
#print axioms ArkLib.MappedSeparability.MappedSliceSeparability
#print axioms ArkLib.MappedSeparability.MappedSliceSeparability.of_separable
#print axioms ArkLib.MappedSeparability.MappedSliceSeparability.of_residue
#print axioms ArkLib.MappedSeparability.matchingPoint_of_decoded_mapped
#print axioms ArkLib.MappedSeparability.mpFin_of_decoded_roots_mapped
#print axioms ArkLib.MappedSeparability.hvanish_of_decoded_roots_mapped
#print axioms ArkLib.MappedSeparability.gammaGenuine_eq_trunc_of_decoded_roots_mapped
#print axioms ArkLib.MappedSeparability.gammaGenuine_eq_trunc_global_mapped
#print axioms ArkLib.MappedSeparability.gammaGenuine_eq_trunc_of_surface_mapped
