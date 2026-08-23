/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.GSSurfaceTaylorRepair
import ArkLib.ToMathlib.GSSurfaceHtailPigeonhole
import ArkLib.ToMathlib.GSSurfaceDegSupply
import ArkLib.ToMathlib.SectionFromSurface
import ArkLib.ToMathlib.CentreVanishingSupply

/-!
# Issue #304 — THE MATCHING-LANE PRODUCER: `GSSurfaceData` from named §5/§6 facts

The full assembly of every produced field: a single producer of the (Taylor-faithful)
keystone bundle whose inputs are **only** the named §5/§6 GS-construction facts —

* the surface: monic, positive-degree, separable specialization; trivariate separability
  (the known-open supply); fiber-degree ≥ 2;
* the section `v` with the per-place incidence `(P z).eval x₀ = v(z)` (the §6 output);
* the per-place specialized matching divisibility (the S10-converse output);
* the numerics: the uniform section budget/count, the pigeonhole matching pack (decoded
  degree bounds + graded budget/count over a matching subset), and the per-order
  `Λ`-weight bounds (the Claim-5.8 shape);

and whose conclusion instantiates the faithful front door
(`correlatedAgreement_affine_curves_of_GS_surface_taylor`) at the shift `s := x₀`.
Internally: `hdvd`/`Hypotheses` via the monic factorization + pigeonhole
(`SectionFromSurface`, with `hvan` derived from the matching divisibility through the
centre-vanishing swap), `htail` via the Claim-5.8′ ab-initio capstone
(`GSSurfaceHtailPigeonhole`), `hdegc` via the weight collapse (`GSSurfaceDegSupply`),
`hdvdP`/`hcong` via the Taylor-faithful cargo adapters (`GSSurfaceTaylorRepair`).

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, §5–§6, Appendix A.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2
open BCIKS20.HenselNumerator
open scoped BigOperators

namespace ArkLib

namespace GSSurfaceKeystone

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]

open ProximityGap Code NNReal Function ProbabilityTheory
open scoped ENNReal ProbabilityTheory LinearCode

/-- **THE MATCHING-LANE PRODUCER**: the Taylor-faithful keystone bundle from named §5/§6
GS-construction facts only. -/
noncomputable def gsSurfaceData_of_matching_lane
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    {x₀ : F} {v : F[X]} {R : F[X][X][Y]}
    -- the surface
    (hmon : (Bivariate.evalX (Polynomial.C x₀) R).Monic)
    (h0 : 0 < (Bivariate.evalX (Polynomial.C x₀) R).natDegree)
    (hsep : (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    (hsepR : R.Separable)
    (hd2 : 2 ≤ Bivariate.natDegreeY R) (hd2' : 2 ≤ R.natDegree)
    -- the per-place §6 facts on the canonical good set
    (hdvdM : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      Polynomial.X - Polynomial.C (P z) ∣
        R.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)))
    (hval : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
      (P z).eval x₀ = v.eval z)
    -- the uniform section numerics
    {nS : ℕ}
    (hbudgetS : ∀ H : F[X][Y], H.Monic → Irreducible H →
      H ∣ Bivariate.evalX (Polynomial.C x₀) R → (Polynomial.eval v H).natDegree < nS)
    (hcountS : (Bivariate.evalX (Polynomial.C x₀) R).natDegree * nS
      ≤ (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card)
    -- the pigeonhole matching pack (the Claim-5.8′ tail feed)
    {D DX : ℕ} (hk : 0 < k) (hkk : k < k + 2)
    (hD : Bivariate.totalDegree (Polynomial.X - Polynomial.C v : F[X][Y]) ≤ D)
    (hdHD : (Polynomial.X - Polynomial.C v : F[X][Y]).natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hRgrade : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hDX : ∀ i, (R.coeff i).natDegree ≤ DX)
    {matchingSet : Finset F}
    (hsub : matchingSet ⊆ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ)
    (hdeg : ∀ z ∈ matchingSet, (P z).natDegree < k)
    {nM : ℕ}
    (hbudgetM : gradedCardBudget (Bivariate.natDegreeY R) D
        (Polynomial.X - Polynomial.C v : F[X][Y]).natDegree
        (DX + R.natDegree * (k - 1)) < nM)
    (hcardM : nM ≤ matchingSet.card)
    -- the Claim-5.8 weight bounds (the `hdegc` feed)
    (hw : ∀ t < k, weight_Λ_over_𝒪 (Fact.out)
      (βHensel (Polynomial.X - Polynomial.C v) x₀ R
        (section_hypotheses_of_surface hmon h0 hsep
          (fun z hz => by
            rw [← hval z hz]
            exact CentreVanishingSupply.centre_vanishing_of_specialized_dvd (hdvdM z hz) x₀)
          hbudgetS hcountS) t) D < (k : WithBot ℕ)) :
    GSSurfaceData (k := k) (deg := deg) (domain := domain) (δ := δ) u
      (fun z => Polynomial.taylor x₀ (P z)) := by
  -- the section Hypotheses, from the surface + matching divisibility + incidence
  refine
    let hvan : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
        Polynomial.evalEval z (v.eval z) (Bivariate.evalX (Polynomial.C x₀) R) = 0 :=
      fun z hz => by
        rw [← hval z hz]
        exact CentreVanishingSupply.centre_vanishing_of_specialized_dvd (hdvdM z hz) x₀
    let hHyp : Hypotheses x₀ R (Polynomial.X - Polynomial.C v) :=
      section_hypotheses_of_surface hmon h0 hsep hvan hbudgetS hcountS
    { x₀ := x₀
      v := v
      R := R
      hd2 := hd2'
      hsepR := hsepR
      hsep := hsep
      hdvd := section_dvd_of_surface hmon h0 hvan hbudgetS hcountS
      n := k
      hn := hkk
      hdegc := ?_
      htail := ?_
      hdvdP := ?_
      hcong := ?_ }
  · -- hdegc from the weight collapse
    exact natDegree_sectionCurveCoeff_lt_of_weight_lt _ hd2' hk hw
  · -- htail from the Claim-5.8′ ab-initio pigeonhole capstone
    exact htail_sectionH_of_pigeonhole _ hk hD hd2 hd2' hdHD hD_Rx0 hRgrade hDX
      (fun z hz => by
        show Polynomial.evalEval z ((P z).eval x₀) (Polynomial.X - Polynomial.C v) = 0
        rw [← Polynomial.coe_evalEvalRingHom, map_sub]
        simp [Polynomial.evalEval_C, Polynomial.evalEval_X, hval z (hsub hz)])
      (fun z hz => hdvdM z (hsub hz)) hdeg hsepR hbudgetM hcardM
  · -- hdvdP: the Taylor-faithful cargo, verbatim from the matching divisibility
    exact fun z hz => hdvdP_of_matching _ z (rootSection v z) _ (hdvdM z hz)
  · -- hcong: the Taylor-faithful congruence at the decoded branch value
    exact fun z hz => hcong_of_branch_value _ z (rootSection v z) (hval z hz)

/-- **The per-`(u, P)` matching-lane pack**: every named §5/§6 GS-construction fact the
producer consumes, bundled. -/
structure MatchingLaneData {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (u : WordStack F (Fin (k + 1)) ι) (P : F → Polynomial F) : Type where
  x₀ : F
  v : F[X]
  R : F[X][X][Y]
  hmon : (Bivariate.evalX (Polynomial.C x₀) R).Monic
  h0 : 0 < (Bivariate.evalX (Polynomial.C x₀) R).natDegree
  hsep : (Bivariate.evalX (Polynomial.C x₀) R).Separable
  hsepR : R.Separable
  hd2 : 2 ≤ Bivariate.natDegreeY R
  hd2' : 2 ≤ R.natDegree
  hdvdM : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
    Polynomial.X - Polynomial.C (P z) ∣
      R.map (Polynomial.mapRingHom (Polynomial.evalRingHom z))
  hval : ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
    (P z).eval x₀ = v.eval z
  nS : ℕ
  hbudgetS : ∀ H : F[X][Y], H.Monic → Irreducible H →
    H ∣ Bivariate.evalX (Polynomial.C x₀) R → (Polynomial.eval v H).natDegree < nS
  hcountS : (Bivariate.evalX (Polynomial.C x₀) R).natDegree * nS
    ≤ (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card
  D : ℕ
  DX : ℕ
  hk : 0 < k
  hD : Bivariate.totalDegree (Polynomial.X - Polynomial.C v : F[X][Y]) ≤ D
  hdHD : (Polynomial.X - Polynomial.C v : F[X][Y]).natDegree ≤ D
  hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R)
  hRgrade : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j
  hDX : ∀ i, (R.coeff i).natDegree ≤ DX
  matchingSet : Finset F
  hsub : matchingSet ⊆ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ
  hdeg : ∀ z ∈ matchingSet, (P z).natDegree < k
  nM : ℕ
  hbudgetM : gradedCardBudget (Bivariate.natDegreeY R) D
      (Polynomial.X - Polynomial.C v : F[X][Y]).natDegree
      (DX + R.natDegree * (k - 1)) < nM
  hcardM : nM ≤ matchingSet.card
  hw : ∀ t < k, weight_Λ_over_𝒪 (Fact.out)
    (βHensel (Polynomial.X - Polynomial.C v) x₀ R
      (section_hypotheses_of_surface hmon h0 hsep
        (fun z hz => by
          rw [← hval z hz]
          exact CentreVanishingSupply.centre_vanishing_of_specialized_dvd (hdvdM z hz) x₀)
        hbudgetS hcountS) t) D < (k : WithBot ℕ)

/-- **THE END-TO-END KEYSTONE (matching-lane interface)**: correlated agreement for affine
curves in the Johnson regime from a per-`(u, P)` pack of named §5/§6 GS-construction facts —
through the Taylor-faithful front door, the section pigeonhole, the Claim-5.8′ tail, the
weight collapse, and the faithful per-place cargo, all PROVEN. -/
theorem correlatedAgreement_affine_curves_of_matching_lane
    {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain)
    (hkk : k < k + 2)
    (hInput : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      ∀ P : F → Polynomial F,
        (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
          (P z).natDegree < deg ∧
            δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t, (P z).eval ∘ domain) ≤ δ) →
        MatchingLaneData (k := k) (deg := deg) (domain := domain) (δ := δ) u P) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  correlatedAgreement_affine_curves_of_GS_surface_taylor hδ
    (fun hk u hprob hJ hδ' P hP =>
      let M := hInput hk u hprob hJ hδ' P hP
      ⟨M.x₀, gsSurfaceData_of_matching_lane M.hmon M.h0 M.hsep M.hsepR M.hd2 M.hd2'
        M.hdvdM M.hval M.hbudgetS M.hcountS M.hk hkk M.hD M.hdHD M.hD_Rx0 M.hRgrade
        M.hDX M.hsub M.hdeg M.hbudgetM M.hcardM M.hw⟩)

end GSSurfaceKeystone

end ArkLib

/-! ## Axiom audit. -/
#print axioms ArkLib.GSSurfaceKeystone.gsSurfaceData_of_matching_lane
#print axioms ArkLib.GSSurfaceKeystone.correlatedAgreement_affine_curves_of_matching_lane
