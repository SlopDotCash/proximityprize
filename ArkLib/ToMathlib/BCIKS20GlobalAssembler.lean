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

omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
/-- **The centre fold is a global root of the specialized trivariate**:
`(evalX (C x₀) R).eval (w.eval (C x₀)) = 0`, from the surface factor `(Y′ − C w) ∣ R`. -/
theorem evalX_eval_centreFold_eq_zero {x₀ : F} {R : F[X][X][Y]} {w : F[X][Y]}
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R) :
    (Bivariate.evalX (Polynomial.C x₀) R).eval (w.eval (Polynomial.C x₀)) = 0 :=
  Polynomial.dvd_iff_isRoot.mp (DecodedRootSupply.centreFold_dvd hdvd)

omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
/-- **The centre fold globally roots `H`**: through the GS split `evalX (C x₀) R = H·G` and
the global branch separation `G.eval v ≠ 0`, the centre fold `v` is a root of `H` itself. -/
theorem H_eval_centreFold_eq_zero {x₀ : F} {R : F[X][X][Y]} {w G : F[X][Y]}
    (hsplit : Bivariate.evalX (Polynomial.C x₀) R = H * G)
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    (hbr : G.eval (w.eval (Polynomial.C x₀)) ≠ 0) :
    H.eval (w.eval (Polynomial.C x₀)) = 0 := by
  have h0 : H.eval (w.eval (Polynomial.C x₀)) * G.eval (w.eval (Polynomial.C x₀)) = 0 := by
    rw [← Polynomial.eval_mul, ← hsplit]
    exact evalX_eval_centreFold_eq_zero hdvd
  rcases mul_eq_zero.mp h0 with h | h
  · exact h
  · exact absurd h hbr

omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
/-- **Separability makes the derivative reading along the surface a UNIT**:
`IsCoprime Q (∂_Y Q)` evaluated along `Y = v` with `Q.eval v = 0` exhibits
`(∂_Y Q).eval v` as a unit of `F[X]` (a nonzero constant). -/
theorem derivative_eval_centreFold_isUnit {x₀ : F} {R : F[X][X][Y]} {w : F[X][Y]}
    (hsep : (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R) :
    IsUnit (((Bivariate.evalX (Polynomial.C x₀) R).derivative).eval
      (w.eval (Polynomial.C x₀))) := by
  rw [Polynomial.separable_def] at hsep
  have hmap := hsep.map (Polynomial.evalRingHom (w.eval (Polynomial.C x₀)))
  simp only [Polynomial.coe_evalRingHom] at hmap
  rw [show Polynomial.eval (w.eval (Polynomial.C x₀)) (Bivariate.evalX (Polynomial.C x₀) R)
      = 0 from evalX_eval_centreFold_eq_zero hdvd] at hmap
  exact isCoprime_zero_left.mp hmap

/-! ## The closure: the `ξ`-certificate IS the derivative reading, hence a unit -/

/-- **The value identity (monic)**: the `ξ`-certificate equals the derivative reading along
the surface, `(canonicalRepOf𝒪 ξ).eval v = (∂_Y (evalX (C x₀) R)).eval v`.  The `%ₘ H`
remainder shift is killed by `H.eval v = 0`. -/
theorem xiCert_eq_derivativeCert {x₀ : F} {R : F[X][X][Y]} {w G : F[X][Y]}
    (hHyp : Hypotheses x₀ R H) (hH : 0 < H.natDegree) (hlc : H.leadingCoeff = 1)
    (hsplit : Bivariate.evalX (Polynomial.C x₀) R = H * G)
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    (hbr : G.eval (w.eval (Polynomial.C x₀)) ≠ 0) :
    (canonicalRepOf𝒪 hH (ξ x₀ R H hHyp)).eval (w.eval (Polynomial.C x₀))
      = ((Bivariate.evalX (Polynomial.C x₀) R).derivative).eval
          (w.eval (Polynomial.C x₀)) := by
  -- the certificate's bivariate is the monic remainder `∂_Y Q %ₘ H`
  have hrep : canonicalRepOf𝒪 hH (ξ x₀ R H hHyp)
      = (Bivariate.evalX (Polynomial.C x₀) R).derivative %ₘ H := by
    have hrfl : ξ x₀ R H hHyp
        = Ideal.Quotient.mk (Ideal.span {H_tilde' H}) (ξ_pre x₀ R H) := rfl
    rw [hrfl, canonicalRepOf𝒪_mk hH,
      BCIKS20.HenselNumerator.ξ_pre_eq_of_monic H x₀ R hlc,
      evalX_derivative_comm x₀ R,
      BCIKS20.HenselNumerator.H_tilde'_eq_self_of_monic H hlc]
  -- evaluate the division identity along `Y = v`; the `H` term dies
  have hHv : H.eval (w.eval (Polynomial.C x₀)) = 0 :=
    H_eval_centreFold_eq_zero hsplit hdvd hbr
  have hdm := Polynomial.modByMonic_add_div
    ((Bivariate.evalX (Polynomial.C x₀) R).derivative) H
  have hev := congrArg (Polynomial.eval (w.eval (Polynomial.C x₀))) hdm
  rw [Polynomial.eval_add, Polynomial.eval_mul, hHv, zero_mul, add_zero] at hev
  rw [hrep]
  exact hev

/-- **The `ξ`-certificate is a UNIT** (monic): the structural GS facts force the certificate
to be a nonzero constant of `F[X]`. -/
theorem xiCert_isUnit {x₀ : F} {R : F[X][X][Y]} {w G : F[X][Y]}
    (hHyp : Hypotheses x₀ R H) (hH : 0 < H.natDegree) (hlc : H.leadingCoeff = 1)
    (hsplit : Bivariate.evalX (Polynomial.C x₀) R = H * G)
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    (hbr : G.eval (w.eval (Polynomial.C x₀)) ≠ 0) :
    IsUnit ((canonicalRepOf𝒪 hH (ξ x₀ R H hHyp)).eval (w.eval (Polynomial.C x₀))) := by
  rw [xiCert_eq_derivativeCert hHyp hH hlc hsplit hdvd hbr]
  exact derivative_eval_centreFold_isUnit hHyp.separable_evalX hdvd

/-- **THE CLOSURE: `hxi` holds.**  The `ξ`-certificate nonvanishing of
`BranchCertificates.gammaGenuine_eq_trunc_global` follows from the structural GS facts
already in its hypothesis list: the GS split, the surface factor, the branch certificate, and
separability (inside `hHyp`).  No witness place, no extra hypothesis. -/
theorem xiCert_ne_zero {x₀ : F} {R : F[X][X][Y]} {w G : F[X][Y]}
    (hHyp : Hypotheses x₀ R H) (hH : 0 < H.natDegree) (hlc : H.leadingCoeff = 1)
    (hsplit : Bivariate.evalX (Polynomial.C x₀) R = H * G)
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    (hbr : G.eval (w.eval (Polynomial.C x₀)) ≠ 0) :
    (canonicalRepOf𝒪 hH (ξ x₀ R H hHyp)).eval (w.eval (Polynomial.C x₀)) ≠ 0 :=
  (xiCert_isUnit hHyp hH hlc hsplit hdvd hbr).ne_zero

/-- The `ξ`-certificate has degree zero: it contributes nothing to the `hbig` budget. -/
theorem xiCert_natDegree_eq_zero {x₀ : F} {R : F[X][X][Y]} {w G : F[X][Y]}
    (hHyp : Hypotheses x₀ R H) (hH : 0 < H.natDegree) (hlc : H.leadingCoeff = 1)
    (hsplit : Bivariate.evalX (Polynomial.C x₀) R = H * G)
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    (hbr : G.eval (w.eval (Polynomial.C x₀)) ≠ 0) :
    ((canonicalRepOf𝒪 hH (ξ x₀ R H hHyp)).eval (w.eval (Polynomial.C x₀))).natDegree = 0 :=
  Polynomial.natDegree_eq_zero_of_isUnit (xiCert_isUnit hHyp hH hlc hsplit hdvd hbr)

/-- **`ξ ≠ 0` holds unconditionally** (from `embeddingOf𝒪Into𝕃_ξ_ne_zero`): the `hξ`
hypothesis of the truncation capstones is also redundant. -/
theorem xi_ne_zero (x₀ : F) (R : F[X][X][Y]) (hHyp : Hypotheses x₀ R H) :
    ξ x₀ R H hHyp ≠ 0 := fun h0 =>
  BCIKS20.HenselNumerator.embeddingOf𝒪Into𝕃_ξ_ne_zero H x₀ R hHyp (by rw [h0, map_zero])


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

/-- **The satisfiable-bundle producer assembly** — the restricted (`rootOn`/`mpFinOn`) mirror of
`KeystoneAssembly.section5DataFin_of_producers`: constructs `Section5StrictDataFinOn` from the
GS-factor bundle and per-field suppliers, with `T := Ppoly.natDegree`, `htailDeg` discharged by
`KeystoneAssembly.htailDeg_field`, `hγ` by `GammaFromBeta.hγ_field_of_betaEq`, and `hPz` by
`HPzBridge.hPz_of_henselDatum`.  Unlike the total assembler, NO total root family is demanded:
`rootOn` and `mpPointOn` are membership-dependent (finding #3). -/
noncomputable def Section5StrictDataFinOn.ofProducersOn {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    {x₀ : F} (b : GSFactorData.Bundle (F := F) x₀)
    [_inst_hIrr : Fact (Irreducible b.H)] [_inst_hPos : Fact (0 < b.H.natDegree)]
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 b.H)
    (matchingSet : Finset F)
    (rootOn : ∀ z ∈ matchingSet, rationalRoot (H_tilde' b.H) z)
    (Ppoly : F[X][Y])
    (hrep : polyToPowerSeries𝕃 b.H Ppoly = γ x₀ b.R b.H b.hHyp)
    (hdegX : Polynomial.Bivariate.degreeX Ppoly ≤ 1)
    (mpPointOn : ∀ t, k ≤ t → t ≤ Ppoly.natDegree → ∀ z (hz : z ∈ matchingSet),
      BetaMatchingVanishes.MatchingPoint x₀ b.R b.H b.hHyp Bcoeff t z (rootOn z hz))
    (hcardFin : ∀ t, k ≤ t → t ≤ Ppoly.natDegree → (↑matchingSet.card : WithBot ℕ)
        > weight_Λ_over_𝒪 b.hH (betaRec x₀ b.R b.H b.hHyp Bcoeff t) b.D * b.H.natDegree)
    (hsubst : PowerSeries.HasSubst (Claim59Conditional.shiftSeries x₀ b.H))
    (hβ : ∀ t, β (H := b.H) b.R t = betaRec x₀ b.R b.H b.hHyp Bcoeff t)
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
  haveI := b.hIrr
  haveI := b.hPos
  { x₀ := x₀
    R := b.R
    H := b.H
    hIrr := b.hIrr
    hPos := b.hPos
    hHyp := b.hHyp
    Bcoeff := Bcoeff
    hH := b.hH
    D := b.D
    hD := b.hD
    matchingSet := matchingSet
    rootOn := rootOn
    T := Ppoly.natDegree
    mpFinOn := mpPointOn
    hcardFin := hcardFin
    htailDeg := KeystoneAssembly.htailDeg_field hsubst
      (GammaFromBeta.hγ_field_of_betaEq x₀ b.R b.H b.hHyp Bcoeff hβ) hrep
    hsubst := hsubst
    hγ := GammaFromBeta.hγ_field_of_betaEq x₀ b.R b.H b.hHyp Bcoeff hβ
    Ppoly := Ppoly
    hrep := hrep
    hdegX := hdegX
    hPz := HPzBridge.hPz_of_henselDatum hHensel hdeg }

/-- **Producer assembly at the signed canonical family with the PROVEN graded weight chain**
(monic case): `Bcoeff := BcoeffSigned`, `hcardFin` fully discharged by
`GenuineMonicCapstone.hcardFin_of_graded_signed` ∘ `gradedConcreteFin_of_disc` (the App-A.4
budgets are theorems, not inputs), and the `hγ` numerator identification taken in its honest
genuine form `β = βHensel` (transported through `betaRec_BcoeffSigned_eq_βHensel`). -/
noncomputable def Section5StrictDataFinOn.ofProducersOn_gradedSigned {k deg : ℕ}
    {domain : ι ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    {x₀ : F} (b : GSFactorData.Bundle (F := F) x₀)
    [_inst_hIrr : Fact (Irreducible b.H)] [_inst_hPos : Fact (0 < b.H.natDegree)]
    (matchingSet : Finset F)
    (rootOn : ∀ z ∈ matchingSet, rationalRoot (H_tilde' b.H) z)
    (Ppoly : F[X][Y])
    (hmonic : b.H.Monic)
    (hrep : polyToPowerSeries𝕃 b.H Ppoly = γ x₀ b.R b.H b.hHyp)
    (hdegX : Polynomial.Bivariate.degreeX Ppoly ≤ 1)
    (mpPointOn : ∀ t, k ≤ t → t ≤ Ppoly.natDegree → ∀ z (hz : z ∈ matchingSet),
      BetaMatchingVanishes.MatchingPoint x₀ b.R b.H b.hHyp
        (BcoeffSigned b.H x₀ b.R) t z (rootOn z hz))
    -- the graded budget side conditions (paper grading of `R`):
    (hd2 : 2 ≤ Bivariate.natDegreeY b.R) (hdHD : b.H.natDegree ≤ b.D)
    (hD_Rx0 : b.D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) b.R))
    (hR : ∀ j, Bivariate.degreeX (b.R.coeff j) ≤ b.D - j)
    -- the §6 discriminant counting:
    {disc : F[X]} (hdisc : disc ≠ 0)
    (hcover : ∀ z : F, disc.eval z ≠ 0 → z ∈ matchingSet)
    (hbig : gradedCardBudget (Bivariate.natDegreeY b.R) b.D b.H.natDegree Ppoly.natDegree
        + disc.natDegree < Fintype.card F)
    (hsubst : PowerSeries.HasSubst (Claim59Conditional.shiftSeries x₀ b.H))
    -- the genuine numerator identification (L13 content, in `βHensel` form):
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
  Section5StrictDataFinOn.ofProducersOn b (BcoeffSigned b.H x₀ b.R) matchingSet rootOn Ppoly
    hrep hdegX mpPointOn
    (GenuineMonicCapstone.hcardFin_of_graded_signed x₀ b.R b.H b.hHyp b.hD b.hH hmonic hd2
      hdHD hD_Rx0 hR (gradedConcreteFin_of_disc hdisc hcover hbig))
    hsubst
    (fun t => (hβHensel t).trans
      (betaRec_BcoeffSigned_eq_βHensel x₀ b.R b.hHyp t).symm)
    hHensel hdeg

/-! ## Part 1 — NEW (#304): the per-place inputs ELIMINATED

The assembler from purely global structural data: matching set constructed, roots decoded,
`hx` discharged by the `ξ`-certificate unit closure, `hξ` unconditional, the §6 discriminant
taken to be the branch certificate itself. -/

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
