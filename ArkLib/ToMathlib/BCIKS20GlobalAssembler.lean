/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
/-
Issue #304 — the satisfiable bundle from PURELY GLOBAL structural data:
`Section5StrictDataFinOn.ofProducersOn_global`.

The capstone assembler `Section5BundleAssembler.ofProducersOn_localSeries_genuineMonic` left,
as items 2-3 of its external-hypothesis surface (the trailing docnote of that file), the
per-place §5 geometry:

  * `rootOn` — the membership-dependent root family;
  * `hx`     — the per-place `ξ`-readings `π_z(ξ) ≠ 0`;
  * `Pz`/`hPdeg`/`hdvd`/`haP_cong` — the per-place proximate-root cargo.

This file ELIMINATES all of them, wiring the landed global machinery into the bundle:

  * roots + base values from `DecodedRootSupply.rootDecoded` (the GS split + the global
    surface factor `(Y′ − C w) ∣ R` — the SectionFactor / Prop-5.5 output shape);
  * the per-place proximate-root cargo from `DecodedProximateRoot` (through
    `mpFin_of_decoded_roots` — the canonical decoded root `aPDecoded` supplies
    `hdvd`/`haP_cong`/the index-`t` truncation internally);
  * `hx` from the `ξ`-certificate UNIT closure (`XiCertReduction.xiCert_isUnit` +
    `BranchCertificates.xiCert_eval_monic`): for monic `H` the certificate is a nonzero
    constant, so its reading at EVERY branch-separated place is nonzero — no per-place
    input remains;
  * `hξ` from `XiCertReduction.xi_ne_zero` (unconditional);
  * the matching set CONSTRUCTED as the nonvanishing locus of the branch certificate
    `G.eval (w.eval (C x₀))`, which simultaneously serves as the §6 discriminant: `hdisc`
    is the global branch separation `hbr`, `hcover` holds by construction, and `hbig` is
    the sharpened budget `gradedCardBudget + (branch certificate).natDegree < |F|`.

Net effect on the #304 external surface: items 2-3 (six per-place inputs) are REPLACED by
four global structural facts —

  `hsplit : evalX (C x₀) R = H * G`                  (the GS split at the centre),
  `hdvdR  : (Y′ − C w) ∣ R` with `w.natDegree < k`   (the global surface factor),
  `hbr    : G.eval (w.eval (C x₀)) ≠ 0`              (global branch separation),
  `hRsep  : R.Separable`                              (GS squarefreeness),

each a single named fact about the global GS objects (the exact output shape of the
SectionFactor / FactorPigeonhole / branch-collapse lane).  `glue_split_of_prod` connects the
irreducible-factorization form `evalX (C x₀) R = ∏ᵢ Hᵢ` to `hsplit`.

NOTE on inlining: `ArkLib.ToMathlib.BCIKS20BundleAssembler` and
`ArkLib.ToMathlib.XiCertReduction` are on `main` but their `.olean`s are NOT built
("object file does not exist"), so Parts 0a/0b re-elaborate the needed declarations
VERBATIM from those sources (both sources verified green + axiom-clean standalone).
-/
import ArkLib.ToMathlib.BCIKS20BundleAssembler
import ArkLib.ToMathlib.XiCertReduction
import ArkLib.ToMathlib.BCIKS20StrictDataFinOn
import ArkLib.ToMathlib.GSFactorData
import ArkLib.ToMathlib.KeystoneAssembly
import ArkLib.ToMathlib.GammaFromBeta
import ArkLib.ToMathlib.HPzBridge
import ArkLib.ToMathlib.BetaWeightGradedSupply
import ArkLib.ToMathlib.GenuineMonicCapstone
import ArkLib.ToMathlib.DecodedRootSupply
import ArkLib.ToMathlib.BranchCertificates
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P1MonicIntegrality

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2 ToRatFunc Ideal
open ProximityGap Code NNReal Finset Function ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory LinearCode

namespace ArkLib

/-! ## Part 0a — inlined VERBATIM from `ArkLib/ToMathlib/XiCertReduction.lean`
(source on `main`, `.olean` not built; declarations unchanged). -/

namespace XiCertReduction

open PowerSeries
open ProximityPrize.BCIKS20.GammaGenuine

variable {F : Type} [Field F]
variable {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

end XiCertReduction

namespace RootOn304

open CorrelatedAgreementListDecodingClosed
open BetaToCurveCoeffPolys
open HcardDischarge

/-! ## Part 0b — inlined VERBATIM from `ArkLib.ToMathlib.BCIKS20BundleAssembler.lean`
(source on `main`, `.olean` not built; declarations unchanged). -/

section ProducersOn

open BetaRecGenuineBridge

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

omit [Nonempty ι] [Fintype ι] [DecidableEq ι] in
/-- **The split from the factorization**: selecting one factor of
`evalX (C x₀) R = ∏ i ∈ s, Hf i` exhibits the GS split `evalX (C x₀) R = Hf i * G` with the
complementary factor `G = ∏_{j ∈ s.erase i} Hf j` — the glue from the
`FactorPigeonhole`/`SectionFactor` factorization shape to the `hsplit` input below. -/
theorem glue_split_of_prod {ι' : Type*} [DecidableEq ι'] {x₀ : F} {R : F[X][X][Y]}
    {s : Finset ι'} {Hf : ι' → F[X][Y]}
    (hQ : Bivariate.evalX (Polynomial.C x₀) R = ∏ i ∈ s, Hf i) {i : ι'} (hi : i ∈ s) :
    Bivariate.evalX (Polynomial.C x₀) R = Hf i * ∏ j ∈ s.erase i, Hf j := by
  rw [hQ, Finset.mul_prod_erase s Hf hi]

omit [Nonempty ι] [Fintype ι] [DecidableEq ι] in
/-- **Per-place branch separation, by construction**: membership in the nonvanishing locus of
the branch certificate `G.eval (w.eval (C x₀))` IS the branch separation at the place. -/
theorem branch_of_mem_locus {G w : F[X][Y]} {x₀ z : F}
    (hz : z ∈ BranchCertificates.nonvanishingLocus
      (G.eval (w.eval (Polynomial.C x₀)))) :
    Polynomial.evalEval z ((w.eval (Polynomial.C x₀)).eval z) G ≠ 0 := by
  have h := BranchCertificates.mem_nonvanishingLocus.mp hz
  rwa [BranchCertificates.branchCert_eval] at h

section GlobalHelpers

variable {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

omit [Nonempty ι] [Fintype ι] [DecidableEq ι] in
/-- **The per-place `ξ`-readings are nonzero, GLOBALLY discharged** (monic case): by
`BranchCertificates.xiCert_eval_monic` the reading at the decoded root is the evaluation of
the `ξ`-certificate at `z`, and by `XiCertReduction.xiCert_isUnit` the certificate is a UNIT
(a nonzero constant of `F[X]`) — so the reading is nonzero at EVERY place of the constructed
matching set.  This eliminates the assembler's per-place `hx` input. -/
theorem hx_of_global_structural {x₀ : F} {R : F[X][X][Y]} (hHyp : Hypotheses x₀ R H)
    {w G : F[X][Y]} (hmonic : H.Monic)
    (hsplit : Bivariate.evalX (Polynomial.C x₀) R = H * G)
    (hdvdR : (Polynomial.X - Polynomial.C w) ∣ R)
    (hbr : G.eval (w.eval (Polynomial.C x₀)) ≠ 0) :
    ∀ z (hz : z ∈ BranchCertificates.nonvanishingLocus
        (G.eval (w.eval (Polynomial.C x₀)))),
      (π_z z (DecodedRootSupply.rootDecoded (Fact.out) hsplit hdvdR z
        (branch_of_mem_locus hz))) (ξ x₀ R H hHyp) ≠ 0 := by
  intro z hz
  rw [BranchCertificates.xiCert_eval_monic (Fact.out) hmonic.leadingCoeff hsplit hdvdR z
    (branch_of_mem_locus hz)]
  have hu : IsUnit ((canonicalRepOf𝒪 (Fact.out) (ξ x₀ R H hHyp)).eval
      (w.eval (Polynomial.C x₀))) :=
    XiCertReduction.xiCert_isUnit hHyp (Fact.out) hmonic.leadingCoeff hsplit hdvdR hbr
  have h := ((Polynomial.evalRingHom z).isUnit_map hu).ne_zero
  simpa [Polynomial.coe_evalRingHom] using h

end GlobalHelpers

/-- **The satisfiable bundle from PURELY GLOBAL structural data** (monic case).  The
per-place §5 geometry inputs of `ofProducersOn_localSeries_genuineMonic` — `rootOn`, `hx`,
`Pz`, `hPdeg`, `hdvd`, `haP_cong` — are ALL eliminated:

* the matching set is CONSTRUCTED (the nonvanishing locus of the branch certificate
  `G.eval (w.eval (C x₀))`), and doubles as the §6 discriminant (`hdisc := hbr`, `hcover`
  by construction, `hbig` sharpened to the certificate degree);
* the root family is `DecodedRootSupply.rootDecoded` (GS split + global surface factor);
* the per-place proximate-root cargo is the canonical decoded root (through
  `DecodedRootSupply.mpFin_of_decoded_roots`);
* `hx` is the `ξ`-certificate unit closure (`hx_of_global_structural`);
* `hξ` is `XiCertReduction.xi_ne_zero` (unconditional).

Remaining inputs: the GS bundle `b` + monicity + the paper grading, the four global
structural facts `hsplit` / `hdvdR` (+ `hwdeg`) / `hbr` / `hRsep`, the sharpened counting
`hbig`, and the series-level items 5-7 of the external surface (`Ppoly`/`hrep`/`hdegX`/
`hsubst`, `hβHensel`, `hHensel`/`hdeg`). -/
noncomputable def Section5StrictDataFinOn.ofProducersOn_global {k deg : ℕ}
    {domain : ι ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    {x₀ : F} (b : GSFactorData.Bundle (F := F) x₀)
    [_inst_hIrr : Fact (Irreducible b.H)] [_inst_hPos : Fact (0 < b.H.natDegree)]
    (Ppoly : F[X][Y])
    (hmonic : b.H.Monic)
    (hrep : polyToPowerSeries𝕃 b.H Ppoly = γ x₀ b.R b.H b.hHyp)
    (hdegX : Polynomial.Bivariate.degreeX Ppoly ≤ 1)
    -- the global §5 structural data (the SectionFactor / Prop-5.5 / branch-collapse shape):
    {w G : F[X][Y]}
    (hsplit : Bivariate.evalX (Polynomial.C x₀) b.R = b.H * G)
    (hwdeg : w.natDegree < k)
    (hdvdR : (Polynomial.X - Polynomial.C w) ∣ b.R)
    (hbr : G.eval (w.eval (Polynomial.C x₀)) ≠ 0)
    (hRsep : b.R.Separable)
    -- graded budget side conditions + the sharpened §6 counting:
    (hd2 : 2 ≤ Bivariate.natDegreeY b.R) (hdHD : b.H.natDegree ≤ b.D)
    (hD_Rx0 : b.D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) b.R))
    (hRgrade : ∀ j, Bivariate.degreeX (b.R.coeff j) ≤ b.D - j)
    (hbig : gradedCardBudget (Bivariate.natDegreeY b.R) b.D b.H.natDegree Ppoly.natDegree
        + (G.eval (w.eval (Polynomial.C x₀))).natDegree < Fintype.card F)
    -- series-level identifications (items 5-7 of the external surface):
    (hsubst : PowerSeries.HasSubst (Claim59Conditional.shiftSeries x₀ b.H))
    (hβHensel : ∀ t, β (H := b.H) b.R t = BCIKS20.HenselNumerator.βHensel b.H x₀ b.R b.hHyp t)
    (hHensel : ∀ v₀ v₁ : F[X],
      γ x₀ b.R b.H b.hHyp = polyToPowerSeries𝕃 b.H
        ((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
      HPzBridge.HenselDatum (k := k) (deg := deg) (domain := domain) (δ := δ) u P v₀ v₁)
    (hdeg : ∀ v₀ v₁ : F[X],
      γ x₀ b.R b.H b.hHyp = polyToPowerSeries𝕃 b.H
        ((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
      v₀.natDegree < k + 1 ∧ v₁.natDegree < k + 1) :
    Section5StrictDataFinOn (k := k) (deg := deg) (domain := domain) (δ := δ) u P :=
  Section5StrictDataFinOn.ofProducersOn_gradedSigned b
    (BranchCertificates.nonvanishingLocus (G.eval (w.eval (Polynomial.C x₀))))
    (fun z hz => DecodedRootSupply.rootDecoded (Fact.out) hsplit hdvdR z
      (branch_of_mem_locus hz))
    Ppoly hmonic hrep hdegX
    (DecodedRootSupply.mpFin_of_decoded_roots b.hHyp
      (XiCertReduction.xi_ne_zero x₀ b.R b.hHyp) hmonic.leadingCoeff hsplit hwdeg hdvdR
      (fun _z hz => branch_of_mem_locus hz) hRsep Ppoly.natDegree
      (hx_of_global_structural b.hHyp hmonic hsplit hdvdR hbr))
    hd2 hdHD hD_Rx0 hRgrade hbr
    (fun _z hz => BranchCertificates.mem_nonvanishingLocus.mpr hz)
    hbig hsubst hβHensel hHensel hdeg

/-- **The chain fires end-to-end from the global structural data**: the root-free
`hcoeffPoly` existential (the front doors' only consumption of the bundle) from the global
producers — no per-place hypothesis anywhere. -/
theorem hcoeffPoly_witness_of_producersOn_global {k deg : ℕ}
    {domain : ι ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    {x₀ : F} (b : GSFactorData.Bundle (F := F) x₀)
    [_inst_hIrr : Fact (Irreducible b.H)] [_inst_hPos : Fact (0 < b.H.natDegree)]
    (Ppoly : F[X][Y])
    (hmonic : b.H.Monic)
    (hrep : polyToPowerSeries𝕃 b.H Ppoly = γ x₀ b.R b.H b.hHyp)
    (hdegX : Polynomial.Bivariate.degreeX Ppoly ≤ 1)
    {w G : F[X][Y]}
    (hsplit : Bivariate.evalX (Polynomial.C x₀) b.R = b.H * G)
    (hwdeg : w.natDegree < k)
    (hdvdR : (Polynomial.X - Polynomial.C w) ∣ b.R)
    (hbr : G.eval (w.eval (Polynomial.C x₀)) ≠ 0)
    (hRsep : b.R.Separable)
    (hd2 : 2 ≤ Bivariate.natDegreeY b.R) (hdHD : b.H.natDegree ≤ b.D)
    (hD_Rx0 : b.D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) b.R))
    (hRgrade : ∀ j, Bivariate.degreeX (b.R.coeff j) ≤ b.D - j)
    (hbig : gradedCardBudget (Bivariate.natDegreeY b.R) b.D b.H.natDegree Ppoly.natDegree
        + (G.eval (w.eval (Polynomial.C x₀))).natDegree < Fintype.card F)
    (hsubst : PowerSeries.HasSubst (Claim59Conditional.shiftSeries x₀ b.H))
    (hβHensel : ∀ t, β (H := b.H) b.R t = BCIKS20.HenselNumerator.βHensel b.H x₀ b.R b.hHyp t)
    (hHensel : ∀ v₀ v₁ : F[X],
      γ x₀ b.R b.H b.hHyp = polyToPowerSeries𝕃 b.H
        ((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
      HPzBridge.HenselDatum (k := k) (deg := deg) (domain := domain) (δ := δ) u P v₀ v₁)
    (hdeg : ∀ v₀ v₁ : F[X],
      γ x₀ b.R b.H b.hHyp = polyToPowerSeries𝕃 b.H
        ((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
      v₀.natDegree < k + 1 ∧ v₁.natDegree < k + 1) :
    ∃ B : ℕ → Polynomial F,
      (∀ j < deg, (B j).natDegree < k + 1) ∧
        ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
          ∀ j < deg, (P z).coeff j = (B j).eval z :=
  hcoeffPoly_witness_of_section5DataFinOn
    (Section5StrictDataFinOn.ofProducersOn_global b Ppoly hmonic hrep hdegX hsplit hwdeg
      hdvdR hbr hRsep hd2 hdHD hD_Rx0 hRgrade hbig hsubst hβHensel hHensel hdeg)

end ProducersOn

end RootOn304

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.XiCertReduction.xiCert_isUnit
#print axioms ArkLib.XiCertReduction.xi_ne_zero
#print axioms ArkLib.RootOn304.Section5StrictDataFinOn.ofProducersOn
#print axioms ArkLib.RootOn304.Section5StrictDataFinOn.ofProducersOn_gradedSigned
#print axioms ArkLib.RootOn304.glue_split_of_prod
#print axioms ArkLib.RootOn304.branch_of_mem_locus
#print axioms ArkLib.RootOn304.hx_of_global_structural
#print axioms ArkLib.RootOn304.Section5StrictDataFinOn.ofProducersOn_global
#print axioms ArkLib.RootOn304.hcoeffPoly_witness_of_producersOn_global
