/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.DecodedRootSupply

/-!
# Issue #304 — the certificate polynomials: Claim 5.8′ from purely GLOBAL data

`DecodedRootSupply.gammaGenuine_eq_trunc_of_decoded_roots` left two per-place hypotheses:
branch separation `G(z, w(x₀,z)) ≠ 0` and `ξ`-nonvanishing `π_z(ξ) ≠ 0` at the decoded roots.
This file converts both into **single global nonvanishing facts** about two certificate
polynomials in `F[X]`, built by substituting the surface's centre fold
`v := w.eval (C x₀) : F[X]` into the relevant bivariate objects:

* `branchCert G w x₀ := G.eval v` — the **branch-separation certificate**: its value at `z` is
  exactly `G(z, w(x₀,z))` (`branchCert_eval`, via the substitution-composition bridge
  `evalEval_eval_eval`).  `branchCert ≠ 0` is the honest global branch-assignment fact (the
  surface's centre fold does not lie in the complementary factor `G`).
* `xiCert hH ξ w x₀ := (canonicalRepOf𝒪 hH ξ).eval v` — the **`ξ`-regularity certificate**:
  for monic `H` its value at `z` is exactly `π_z(ξ)` at the decoded root
  (`xiCert_eval_monic`, via `mk_canonicalRepOf𝒪` + `π_z_mk` + the bridge).  `xiCert ≠ 0` is
  the global regularity of `ξ` along the decoded surface.

**The capstone** `gammaGenuine_eq_trunc_global`: the Claim 5.8′ truncation identity
`gammaGenuine = trunc k gammaGenuine` with the matching set CONSTRUCTED as the joint
nonvanishing locus of `disc · branchCert · xiCert`, from purely global hypotheses:

1.  `hsplit : evalX (C x₀) R = H · G` — the GS split (`hHyp.dvd_evalX` witness);
2.  `hdvd : (Y′ − C w) ∣ R`, `hdeg : w.natDegree < k` — the Prop-5.5 matching surface;
3.  `hbr : branchCert ≠ 0` — branch assignment;
4.  `hxi : xiCert ≠ 0` — `ξ`-regularity along the surface;
5.  `hR : R.Separable`;
6.  `hrepG` — the genuine representative;
7.  the graded side conditions;
8.  `hbig` — ONE field-size inequality against the graded budget plus the certificate degrees.

**No per-place hypothesis remains.**  Every input is a single named finite fact about the
global GS objects `(R, H, G, w, Ppoly)`.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, §5–§6, Appendix A (the branch assignment and the `ξ`-regularity along the decoded
  surface are the §6.2/A.3 geometry, here quantified by resultant-style certificates).
-/

set_option linter.style.longLine false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2
open PowerSeries

namespace ArkLib

namespace BranchCertificates

variable {F : Type} [Field F]
variable {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-! ## The certificate polynomials -/

omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
/-- **The branch-separation certificate evaluates to the per-place branch value**:
`(G.eval v).eval z = G(z, v(z))` for the centre fold `v := w.eval (C x₀)`. -/
theorem branchCert_eval (G w : F[X][Y]) (x₀ z : F) :
    ((G.eval (w.eval (Polynomial.C x₀))).eval z : F)
      = Polynomial.evalEval z ((w.eval (Polynomial.C x₀)).eval z) G :=
  (RationalRootSupply.evalEval_eval_eval z G (w.eval (Polynomial.C x₀))).symm

omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
/-- **The `ξ`-certificate evaluates to the per-place `ξ`-reading at the decoded root**
(monic case): with the decoded root's value pinned to `w(x₀, z)` by monicity, the place
reading of any `a : 𝒪 H` is the evaluation of its certificate
`(canonicalRepOf𝒪 a).eval (w.eval (C x₀))` at `z`. -/
theorem xiCert_eval_monic {x₀ : F} {R : F[X][X][Y]} {w G : F[X][Y]}
    (hH : 0 < H.natDegree) (hlc : H.leadingCoeff = 1)
    (hsplit : Bivariate.evalX (Polynomial.C x₀) R = H * G)
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R) (z : F)
    (hbranch : Polynomial.evalEval z ((w.eval (Polynomial.C x₀)).eval z) G ≠ 0)
    (a : 𝒪 H) :
    (π_z z (DecodedRootSupply.rootDecoded hH hsplit hdvd z hbranch)) a
      = (((canonicalRepOf𝒪 hH a).eval (w.eval (Polynomial.C x₀))).eval z : F) := by
  conv_lhs => rw [← mk_canonicalRepOf𝒪 hH a]
  rw [π_z_mk]
  rw [← DecodedRootSupply.rootDecoded_val_monic hH hlc hsplit hdvd z hbranch]
  exact RationalRootSupply.evalEval_eval_eval z _ _

/-! ## The constructed matching set -/

section Capstone

variable [Fintype F] [DecidableEq F]

/-- The joint nonvanishing locus of a polynomial — the constructed matching set. -/
noncomputable def nonvanishingLocus (d : F[X]) : Finset F :=
  Finset.univ.filter (fun z => d.eval z ≠ 0)

omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
theorem mem_nonvanishingLocus {d : F[X]} {z : F} :
    z ∈ nonvanishingLocus (F := F) d ↔ d.eval z ≠ 0 := by
  simp [nonvanishingLocus]

/-- **THE GLOBAL CAPSTONE: Claim 5.8′ from purely global data.**
`gammaGenuine = trunc k gammaGenuine`, with the matching set constructed as the joint
nonvanishing locus of `disc · branchCert · xiCert`.  Every hypothesis is a single named
finite fact about the global GS objects; no per-place input remains. -/
theorem gammaGenuine_eq_trunc_global {x₀ : F} {R : F[X][X][Y]}
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
    {w G : F[X][Y]}
    (hsplit : Bivariate.evalX (Polynomial.C x₀) R = H * G)
    (hdeg : w.natDegree < k)
    (hdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    (hR : R.Separable)
    -- the two global certificates:
    (hbr : G.eval (w.eval (Polynomial.C x₀)) ≠ 0)
    (hxi : (canonicalRepOf𝒪 hH (ξ x₀ R H hHyp)).eval (w.eval (Polynomial.C x₀)) ≠ 0)
    -- the single field-size inequality:
    (hbig : gradedCardBudget (Bivariate.natDegreeY R) D H.natDegree Ppoly.natDegree
        + ((G.eval (w.eval (Polynomial.C x₀)))
            * (canonicalRepOf𝒪 hH (ξ x₀ R H hHyp)).eval
                (w.eval (Polynomial.C x₀))).natDegree
        < Fintype.card F) :
    ProximityPrize.BCIKS20.GammaGenuine.gammaGenuine x₀ R H hHyp
      = (↑(PowerSeries.trunc k (ProximityPrize.BCIKS20.GammaGenuine.gammaGenuine x₀ R H hHyp))
          : PowerSeries (𝕃 H)) := by
  classical
  -- the one discriminant: the product of the two certificates
  set vC : F[X] := w.eval (Polynomial.C x₀) with hvC
  set dBr : F[X] := G.eval vC with hdBr
  set dXi : F[X] := (canonicalRepOf𝒪 hH (ξ x₀ R H hHyp)).eval vC with hdXi
  have hdisc : dBr * dXi ≠ 0 := mul_ne_zero hbr hxi
  -- the constructed matching set
  set ms : Finset F := nonvanishingLocus (dBr * dXi) with hms
  -- per-place branch separation on the locus
  have hbranch : ∀ z ∈ ms, Polynomial.evalEval z (vC.eval z) G ≠ 0 := by
    intro z hz
    have h := (mem_nonvanishingLocus).mp hz
    rw [Polynomial.eval_mul] at h
    have hBr : dBr.eval z ≠ 0 := fun h0 => h (by rw [h0, zero_mul])
    rw [hdBr] at hBr
    rw [← branchCert_eval G w x₀ z]
    exact hBr
  -- per-place ξ-nonvanishing at the decoded roots on the locus
  have hx : ∀ z (hz : z ∈ ms),
      (π_z z (DecodedRootSupply.rootDecoded hH hsplit hdvd z (hbranch z hz)))
        (ξ x₀ R H hHyp) ≠ 0 := by
    intro z hz
    have h := (mem_nonvanishingLocus).mp hz
    rw [Polynomial.eval_mul] at h
    have hXi : dXi.eval z ≠ 0 := fun h0 => h (by rw [h0, mul_zero])
    rw [xiCert_eval_monic hH hmonic.leadingCoeff hsplit hdvd z (hbranch z hz)]
    rw [hdXi] at hXi
    exact hXi
  -- fire the decoded-roots capstone with cover := the locus itself
  exact DecodedRootSupply.gammaGenuine_eq_trunc_of_decoded_roots hHyp hξ hD hH hmonic hd2
    hdHD hD_Rx0 hRgrade hrepG hsplit hdeg hdvd hbranch hR hx hdisc
    (fun z hz => (mem_nonvanishingLocus).mpr hz) hbig

end Capstone

end BranchCertificates

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.BranchCertificates.branchCert_eval
#print axioms ArkLib.BranchCertificates.xiCert_eval_monic
#print axioms ArkLib.BranchCertificates.nonvanishingLocus
#print axioms ArkLib.BranchCertificates.mem_nonvanishingLocus
#print axioms ArkLib.BranchCertificates.gammaGenuine_eq_trunc_global
