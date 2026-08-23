/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.GSFactorData
import ArkLib.ToMathlib.GammaFromBeta
import ArkLib.ToMathlib.MpProducer
import ArkLib.ToMathlib.TailDegProducer
import ArkLib.ToMathlib.HPzBridge
import ArkLib.ToMathlib.BoundaryDischarge
import ArkLib.ToMathlib.HcardDischarge

/-!
# Final Assembly of the Correlated Agreement Keystone

This module performs the final assembly of the list-decoding proximity gap keystone theorem
(Claim A.2 / Theorem 6.2 of [BCIKS20]). It integrates the various subfield/sub-reduction producers
established in the other modules of this directory to obtain the final correlated agreement
probability bounds.

## Mathematical Context

Let $C \subset F^\iota$ be a Reed-Solomon code of rate $\rho$. The goal of the proximity gap
keystone is to establish a bound on the multi-correlated agreement (MCA) error:
$$\varepsilon_{\mathrm{ca}}(C, \delta, \varepsilon)$$
under the Johnson bound regime $\delta \le 1 - \sqrt{\rho}$.

The reduction proceeds by:
1. Extracting the Guruswami-Sudan factor data and Hensel-lifted recurrence relations.
2. Certifying that the lift $\gamma$ decomposes linearly in $Z$ under tail degree truncation bounds
   and Hensel uniqueness.
3. Matching the specialized algebraic equations at the points $z \in F$ to obtain the existence of a
   witness coefficient polynomial system.
4. Concluding the probability lower bounds for the affine curves.

This file wires the individual modular steps into a unified, clean assembly, establishing
`δ_ε_correlatedAgreementCurves` from the standing mathematical hypotheses.

## Key Formalizations
* `htailDeg_field`: Adapts the tail degree truncation bounds to the finite-range datum.
* `section5DataFin_of_producers`: Constructor integrating the modular sub-reduces into
  `Section5StrictDataFin`.
* `correlatedAgreement_listDecoding_closed_fin`: Front-door theorem proving the correlated
  agreement curve bounds from the finite-range datum.
* `keystone_of_section5Inputs`: The end-to-end assembly theorem discharging all intermediate
  residuals.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon Codes*,
  §5 (list-decoding agreement chain), §6.2 (Theorem 6.2), Appendix A.2/A.4.
-/

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2 ToRatFunc Ideal
open ProximityGap Code NNReal Finset Function ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory LinearCode

namespace ArkLib

namespace KeystoneAssembly

open BetaToCurveCoeffPolys Claim59Conditional
open CorrelatedAgreementListDecodingClosed HcardDischarge

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ### Tail Degree Adaptation -/

omit [Fintype F] [DecidableEq F] in
/-- Adapts the tail degree truncation bound to the polynomial degree of the representative. -/
theorem htailDeg_field {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] {hHyp : Hypotheses x₀ R H}
    {Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H} {Ppoly : F[X][Y]}
    (hsubst : PowerSeries.HasSubst (Claim59Conditional.shiftSeries x₀ H))
    (hγ : γ x₀ R H hHyp =
      (PowerSeries.mk (BetaToCurveCoeffPolys.αFromBeta x₀ R H hHyp Bcoeff)).subst
        (Claim59Conditional.shiftSeries x₀ H))
    (hrep : polyToPowerSeries𝕃 H Ppoly = γ x₀ R H hHyp) :
    ∀ t, Ppoly.natDegree < t → BetaToCurveCoeffPolys.αFromBeta x₀ R H hHyp Bcoeff t = 0 :=
  TailDegProducer.htailDeg_of_polynomial_representative hsubst hγ hrep

/-! ### Assembly of Section 5 Finite Data -/

/-- Constructs the `Section5StrictDataFin` instance by integrating the various modular
sub-reductions. -/
noncomputable def section5DataFin_of_producers {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin (k + 1)) ι} {P : F → Polynomial F}
    {x₀ : F} (b : GSFactorData.Bundle (F := F) x₀)
    [_inst_hIrr : Fact (Irreducible b.H)] [_inst_hPos : Fact (0 < b.H.natDegree)]
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 b.H)
    (matchingSet : Finset F)
    (root : (z : F) → rationalRoot (H_tilde' b.H) z)
    -- the Prop-5.5 linear representative of `γ`
    -- (fixes the truncation index `T := Ppoly.natDegree`):
    (Ppoly : F[X][Y])
    (hrep : polyToPowerSeries𝕃 b.H Ppoly = γ x₀ b.R b.H b.hHyp)
    (hdegX : Polynomial.Bivariate.degreeX Ppoly ≤ 1)
    -- finite-range per-point matching producer (ingredient-C geometry on `[k, Ppoly.natDegree]`):
    (mpPoint : ∀ t, k ≤ t → t ≤ Ppoly.natDegree → ∀ z ∈ matchingSet,
      BetaMatchingVanishes.MatchingPoint x₀ b.R b.H b.hHyp Bcoeff t z (root z))
    -- the satisfiable finite-range L9/L10 weight bound (cf. F5):
    (hcardFin : ∀ t, k ≤ t → t ≤ Ppoly.natDegree → (↑matchingSet.card : WithBot ℕ)
        > weight_Λ_over_𝒪 b.hH (betaRec x₀ b.R b.H b.hHyp Bcoeff t) b.D * b.H.natDegree)
    (hsubst : PowerSeries.HasSubst (Claim59Conditional.shiftSeries x₀ b.H))
    -- the numerator residual replacing `hγ`:
    (hβ : ∀ t, β (H := b.H) b.R t = betaRec x₀ b.R b.H b.hHyp Bcoeff t)
    -- the per-`z` Hensel root datum + degree bounds (yielding `hPz`):
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
    Section5StrictDataFin (k := k) (deg := deg) (domain := domain) (δ := δ) u P :=
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
    root := root
    T := Ppoly.natDegree
    mpFin := MpProducer.mpFin_of_pointwise (k := k) (T := Ppoly.natDegree) mpPoint
    hcardFin := hcardFin
    htailDeg :=
      htailDeg_field hsubst (GammaFromBeta.hγ_field_of_betaEq x₀ b.R b.H b.hHyp Bcoeff hβ) hrep
    hsubst := hsubst
    hγ := GammaFromBeta.hγ_field_of_betaEq x₀ b.R b.H b.hHyp Bcoeff hβ
    Ppoly := Ppoly
    hrep := hrep
    hdegX := hdegX
    hPz := HPzBridge.hPz_of_henselDatum hHensel hdeg }

/-! ### List Decoding Keystone from Finite Data -/

omit [DecidableEq ι] in
/-- Proves the correlated agreement curves bound from the finite-range extraction datum. -/
theorem correlatedAgreement_listDecoding_closed_fin {k deg : ℕ}
    {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hExtractFin : ∀ (u : WordStack F (Fin (k + 1)) ι),
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
        Section5StrictDataFin (k := k) (deg := deg) (domain := domain) (δ := δ) u P)
    (hBoundary : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      ¬δ < 1 - ReedSolomon.sqrtRate deg domain →
      jointAgreement (C := ReedSolomon.code domain deg) (δ := δ) (W := u)) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  refine correlatedAgreement_affine_curves_of_strict_coeff_polys_and_boundary
    (deg := deg) (domain := domain) (δ := δ) hδ ?_ hBoundary
  -- strict-Johnson branch: assemble `hcoeffPoly` from the per-decoding corrected Fin datum.
  intro hk u hprob hJ hsqrt P hP
  exact hcoeffPoly_witness_of_section5DataFin (hExtractFin u hprob hJ hsqrt P hP)

omit [DecidableEq ι] in
/-- Proves the correlated agreement curves bound in the strict Johnson range. -/
theorem correlatedAgreement_listDecoding_strict_fin {k deg : ℕ}
    {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain)
    (hExtractFin : ∀ (u : WordStack F (Fin (k + 1)) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      ∀ P : F → Polynomial F,
        (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
          (P z).natDegree < deg ∧
            δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t, (P z).eval ∘ domain) ≤ δ) →
        Section5StrictDataFin (k := k) (deg := deg) (domain := domain) (δ := δ) u P) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  refine correlatedAgreement_affine_curves_of_strict_coeff_polys
    (deg := deg) (domain := domain) (δ := δ) hδ ?_
  intro hk u hprob hJ P hP
  exact hcoeffPoly_witness_of_section5DataFin (hExtractFin u hprob hJ P hP)

/-! ### End-to-End Keystone Assembly -/

omit [DecidableEq ι] in
/-- Theorem proving the correlated agreement curves bound from the genuine Section 5 inputs,
integrating both the strict and boundary branches of the reduction. -/
theorem keystone_of_section5Inputs {k deg : ℕ}
    {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    -- the genuine §5 standing inputs, per curve/decoding, packaged as a `Section5StrictDataFin`
    -- producer (each component is supplied via `section5DataFin_of_producers`):
    (hSection5 : ∀ (u : WordStack F (Fin (k + 1)) ι),
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
        Section5StrictDataFin (k := k) (deg := deg) (domain := domain) (δ := δ) u P)
    -- the closed square-root boundary standing datum (cardinality bounds + §5 extraction):
    (hBoundaryData : ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      ¬δ < 1 - ReedSolomon.sqrtRate deg domain →
      ((RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card > k) ∧
      ((RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card ≥
        (Fintype.card ι + 1) * k) ∧
      (∀ P : F → Polynomial F,
        (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
          (P z).natDegree < deg ∧
            δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
              (P z).eval ∘ domain) ≤ δ) →
          ∃ B : ℕ → Polynomial F,
            (∀ j < deg, (B j).natDegree < k + 1) ∧
              ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
                ∀ j < deg, (P z).coeff j = (B j).eval z)) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  correlatedAgreement_listDecoding_closed_fin hδ hSection5
    (BoundaryDischarge.hBoundary_of_boundary_cards_and_coeffPolys
      (k := k) (deg := deg) (domain := domain) (δ := δ) hBoundaryData)

omit [DecidableEq ι] in
/-- Strict final assembly theorem without the boundary branch. -/
theorem keystone_of_section5Inputs_strict {k deg : ℕ}
    {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain)
    (hSection5 : ∀ (u : WordStack F (Fin (k + 1)) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      ∀ P : F → Polynomial F,
        (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
          (P z).natDegree < deg ∧
            δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t, (P z).eval ∘ domain) ≤ δ) →
        Section5StrictDataFin (k := k) (deg := deg) (domain := domain) (δ := δ) u P) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  correlatedAgreement_listDecoding_strict_fin hδ hSection5

end KeystoneAssembly

end ArkLib


