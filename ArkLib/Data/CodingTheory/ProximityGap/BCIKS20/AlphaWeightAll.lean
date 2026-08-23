/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AlphaWeightCleared

/-!
# All-prefix packaging for the BCIKS20 Appendix-A weight invariant

This lightweight module sits on top of `AlphaWeight.lean`.  It packages the existing fixed-prefix
`βHenselStructuredWeightInvariant ... k` constructors into the all-`k` family consumed by
`βHensel_weight_bound_of_structured_invariant`, and exposes thin divWeight/normalized consumers for
that older structured-invariant front door.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace BCIKS20.HenselNumerator

open Polynomial Polynomial.Bivariate
open BCIKS20AppendixA
open ProximityPrize.BCIKS20.GammaGenuine

namespace AlphaWeight

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- Package the fixed-prefix structured invariant from carved alpha regularity into the all-`k`
surface consumed by `βHensel_weight_bound_of_structured_invariant`. -/
theorem βHenselStructuredWeightInvariant_all_of_alphaWeight
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hlift : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
        = αGenuine H x₀ R hHyp t
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1))
    (hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D)
    (hξ : weight_Λ_over_𝒪 hH (ClaimA2.ξ x₀ R H hHyp) D
            ≤ WithBot.some ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1))) :
    ∀ k, βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  fun k =>
    βHenselStructuredWeightInvariant_of_alphaWeight H x₀ R hHyp hH
      hDH hlift hα hξ k

/-- Package the all-`k` structured invariant from carved alpha regularity, with the `ξ` side
condition discharged by the proved `ClaimA2.weight_ξ_bound`. -/
theorem βHenselStructuredWeightInvariant_all_of_alphaWeight'
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hlift : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
        = αGenuine H x₀ R hHyp t
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1))
    (hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D) :
    ∀ k, βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  βHenselStructuredWeightInvariant_all_of_alphaWeight H x₀ R hHyp hH
    hDH hlift hα (ClaimA2.weight_ξ_bound x₀ hH hHyp hdR2 hDH hDRx0)

/-- Package the fixed-prefix structured invariant from separated carved alpha base/successor cases
into the all-`k` family. -/
theorem βHenselStructuredWeightInvariant_all_of_alphaWeight_cases
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hlift : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
        = αGenuine H x₀ R hHyp t
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1))
    (h0 : AlphaGenuineRegularWeightLe_zero H x₀ R hHyp hH D)
    (hsucc : ∀ t, AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t)
    (hξ : weight_Λ_over_𝒪 hH (ClaimA2.ξ x₀ R H hHyp) D
            ≤ WithBot.some ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1))) :
    ∀ k, βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  fun k =>
    βHenselStructuredWeightInvariant_of_alphaWeight_cases
      H x₀ R hHyp hH hDH hlift h0 hsucc hξ k

/-- Package the all-`k` case-wise carved-alpha structured invariant, with `ξ` discharged. -/
theorem βHenselStructuredWeightInvariant_all_of_alphaWeight_cases'
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hlift : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
        = αGenuine H x₀ R hHyp t
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1))
    (h0 : AlphaGenuineRegularWeightLe_zero H x₀ R hHyp hH D)
    (hsucc : ∀ t, AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t) :
    ∀ k, βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  βHenselStructuredWeightInvariant_all_of_alphaWeight_cases H x₀ R hHyp hH
    hDH hlift h0 hsucc (ClaimA2.weight_ξ_bound x₀ hH hHyp hdR2 hDH hDRx0)

/-- Package the fixed-prefix structured invariant from `DivWeightLe` into an all-`k` family. -/
theorem βHenselStructuredWeightInvariant_all_of_divWeight
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdiv : DivWeightLe H x₀ R hHyp hH D)
    (hξ : weight_Λ_over_𝒪 hH (ClaimA2.ξ x₀ R H hHyp) D
            ≤ WithBot.some ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1))) :
    ∀ k, βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  fun k =>
    βHenselStructuredWeightInvariant_of_divWeight H x₀ R hHyp hH
      hDH hdiv hξ k

/-- Package the fixed-prefix structured invariant from normalized divisibility targets into an
all-`k` family. -/
theorem βHenselStructuredWeightInvariant_all_of_normalized_divWeight_cases
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (h0 : ∃ a : 𝒪 H,
      βHensel H x₀ R hHyp 0 = a * W𝒪 H ∧
        weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1)
    (hsucc : ∀ t : ℕ, ∃ a : 𝒪 H,
      βHensel H x₀ R hHyp (t + 1)
        = a * (W𝒪 H) ^ (t + 2) * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t + 1) ∧
        weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1)
    (hξ : weight_Λ_over_𝒪 hH (ClaimA2.ξ x₀ R H hHyp) D
            ≤ WithBot.some ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1))) :
    ∀ k, βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  fun k =>
    βHenselStructuredWeightInvariant_of_normalized_divWeight_cases
      H x₀ R hHyp hH hDH h0 hsucc hξ k

/-- Package the all-`k` structured invariant from `DivWeightLe`, with the `ξ` side condition
discharged by the proved `ClaimA2.weight_ξ_bound`. -/
theorem βHenselStructuredWeightInvariant_all_of_divWeight'
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdiv : DivWeightLe H x₀ R hHyp hH D) :
    ∀ k, βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  βHenselStructuredWeightInvariant_all_of_divWeight H x₀ R hHyp hH hDH hdiv
    (ClaimA2.weight_ξ_bound x₀ hH hHyp hdR2 hDH hDRx0)

/-- Package the all-`k` structured invariant from normalized divisibility targets, with `ξ`
discharged by the proved `ClaimA2.weight_ξ_bound`. -/
theorem βHenselStructuredWeightInvariant_all_of_normalized_divWeight_cases'
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (h0 : ∃ a : 𝒪 H,
      βHensel H x₀ R hHyp 0 = a * W𝒪 H ∧
        weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1)
    (hsucc : ∀ t : ℕ, ∃ a : 𝒪 H,
      βHensel H x₀ R hHyp (t + 1)
        = a * (W𝒪 H) ^ (t + 2) * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t + 1) ∧
        weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1) :
    ∀ k, βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  βHenselStructuredWeightInvariant_all_of_normalized_divWeight_cases
    H x₀ R hHyp hH hDH h0 hsucc
      (ClaimA2.weight_ξ_bound x₀ hH hHyp hdR2 hDH hDRx0)

/-- Package the fixed-prefix structured invariant from successor-order lift identities into the
all-`k` family consumed by the structured-invariant weight-bound endpoint. -/
theorem βHenselStructuredWeightInvariant_all_of_alphaWeight_succLift
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hliftSucc : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp (t + 1))
        = αGenuine H x₀ R hHyp (t + 1)
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1))
    (hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D)
    (hξ : weight_Λ_over_𝒪 hH (ClaimA2.ξ x₀ R H hHyp) D
            ≤ WithBot.some ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1))) :
    ∀ k, βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  fun k =>
    βHenselStructuredWeightInvariant_of_alphaWeight_succLift
      H x₀ R hHyp hH hDH hliftSucc hα hξ k

/-- Package the all-`k` successor-lift structured invariant with `ξ` discharged by
`ClaimA2.weight_ξ_bound`. -/
theorem βHenselStructuredWeightInvariant_all_of_alphaWeight_succLift'
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hliftSucc : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp (t + 1))
        = αGenuine H x₀ R hHyp (t + 1)
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1))
    (hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D) :
    ∀ k, βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  βHenselStructuredWeightInvariant_all_of_alphaWeight_succLift
    H x₀ R hHyp hH hDH hliftSucc hα
      (ClaimA2.weight_ξ_bound x₀ hH hHyp hdR2 hDH hDRx0)

/-- Package separated carved alpha base/successor cases with successor-order lift identities into
an all-`k` structured invariant. -/
theorem βHenselStructuredWeightInvariant_all_of_alphaWeight_cases_succLift
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hliftSucc : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp (t + 1))
        = αGenuine H x₀ R hHyp (t + 1)
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1))
    (h0 : AlphaGenuineRegularWeightLe_zero H x₀ R hHyp hH D)
    (hsucc : ∀ t, AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t)
    (hξ : weight_Λ_over_𝒪 hH (ClaimA2.ξ x₀ R H hHyp) D
            ≤ WithBot.some ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1))) :
    ∀ k, βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  fun k =>
    βHenselStructuredWeightInvariant_of_alphaWeight_cases_succLift
      H x₀ R hHyp hH hDH hliftSucc h0 hsucc hξ k

/-- Package the all-`k` successor-lift case-wise structured invariant, with `ξ` discharged. -/
theorem βHenselStructuredWeightInvariant_all_of_alphaWeight_cases_succLift'
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hliftSucc : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp (t + 1))
        = αGenuine H x₀ R hHyp (t + 1)
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1))
    (h0 : AlphaGenuineRegularWeightLe_zero H x₀ R hHyp hH D)
    (hsucc : ∀ t, AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t) :
    ∀ k, βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  βHenselStructuredWeightInvariant_all_of_alphaWeight_cases_succLift
    H x₀ R hHyp hH hDH hliftSucc h0 hsucc
      (ClaimA2.weight_ξ_bound x₀ hH hHyp hdR2 hDH hDRx0)

/-- Route carved alpha regularity through the all-`k` structured-invariant front door for the
full P1 weight bound. -/
theorem βHensel_weight_bound_of_structured_invariant_alphaWeight
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hRgraded : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hlift : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
        = αGenuine H x₀ R hHyp t
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1))
    (hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D)
    (hξ : weight_Λ_over_𝒪 hH (ClaimA2.ξ x₀ R H hHyp) D
            ≤ WithBot.some ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)))
    (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_of_structured_invariant H x₀ R hHyp hH hDH hdR2
    hdHR hW hRgraded hDRx0
      (βHenselStructuredWeightInvariant_all_of_alphaWeight H x₀ R hHyp hH
        hDH hlift hα hξ)
      t

/-- Route carved alpha regularity through the all-`k` structured-invariant front door, with `ξ`
discharged. -/
theorem βHensel_weight_bound_of_structured_invariant_alphaWeight'
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hRgraded : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hlift : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
        = αGenuine H x₀ R hHyp t
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1))
    (hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D) (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_of_structured_invariant_alphaWeight H x₀ R hHyp hH
    hDH hdR2 hdHR hW hRgraded hDRx0 hlift hα
      (ClaimA2.weight_ξ_bound x₀ hH hHyp hdR2 hDH hDRx0)
      t

/-- Route separated carved alpha base/successor cases through the all-`k` structured endpoint. -/
theorem βHensel_weight_bound_of_structured_invariant_alphaWeight_cases
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hRgraded : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hlift : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
        = αGenuine H x₀ R hHyp t
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1))
    (h0 : AlphaGenuineRegularWeightLe_zero H x₀ R hHyp hH D)
    (hsucc : ∀ t, AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t)
    (hξ : weight_Λ_over_𝒪 hH (ClaimA2.ξ x₀ R H hHyp) D
            ≤ WithBot.some ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)))
    (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_of_structured_invariant H x₀ R hHyp hH hDH hdR2
    hdHR hW hRgraded hDRx0
      (βHenselStructuredWeightInvariant_all_of_alphaWeight_cases
        H x₀ R hHyp hH hDH hlift h0 hsucc hξ)
      t

/-- Route separated carved alpha base/successor cases through the all-`k` endpoint, with `ξ`
discharged. -/
theorem βHensel_weight_bound_of_structured_invariant_alphaWeight_cases'
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hRgraded : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hlift : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
        = αGenuine H x₀ R hHyp t
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1))
    (h0 : AlphaGenuineRegularWeightLe_zero H x₀ R hHyp hH D)
    (hsucc : ∀ t, AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t)
    (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_of_structured_invariant_alphaWeight_cases
    H x₀ R hHyp hH hDH hdR2 hdHR hW hRgraded hDRx0 hlift h0 hsucc
      (ClaimA2.weight_ξ_bound x₀ hH hHyp hdR2 hDH hDRx0)
      t

/-- Route successor-order lift identities through the all-`k` structured-invariant front door for
the full P1 weight bound. -/
theorem βHensel_weight_bound_of_structured_invariant_alphaWeight_succLift
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hRgraded : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hliftSucc : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp (t + 1))
        = αGenuine H x₀ R hHyp (t + 1)
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1))
    (hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D)
    (hξ : weight_Λ_over_𝒪 hH (ClaimA2.ξ x₀ R H hHyp) D
            ≤ WithBot.some ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)))
    (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_of_structured_invariant H x₀ R hHyp hH hDH hdR2
    hdHR hW hRgraded hDRx0
      (βHenselStructuredWeightInvariant_all_of_alphaWeight_succLift
        H x₀ R hHyp hH hDH hliftSucc hα hξ)
      t

/-- Route successor-order lift identities through the all-`k` structured-invariant front door,
with `ξ` discharged. -/
theorem βHensel_weight_bound_of_structured_invariant_alphaWeight_succLift'
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hRgraded : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hliftSucc : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp (t + 1))
        = αGenuine H x₀ R hHyp (t + 1)
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1))
    (hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D) (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_of_structured_invariant_alphaWeight_succLift
    H x₀ R hHyp hH hDH hdR2 hdHR hW hRgraded hDRx0 hliftSucc hα
      (ClaimA2.weight_ξ_bound x₀ hH hHyp hdR2 hDH hDRx0)
      t

/-- Route separated carved alpha cases with successor-order lift identities through the all-`k`
structured endpoint. -/
theorem βHensel_weight_bound_of_structured_invariant_alphaWeight_cases_succLift
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hRgraded : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hliftSucc : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp (t + 1))
        = αGenuine H x₀ R hHyp (t + 1)
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1))
    (h0 : AlphaGenuineRegularWeightLe_zero H x₀ R hHyp hH D)
    (hsucc : ∀ t, AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t)
    (hξ : weight_Λ_over_𝒪 hH (ClaimA2.ξ x₀ R H hHyp) D
            ≤ WithBot.some ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)))
    (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_of_structured_invariant H x₀ R hHyp hH hDH hdR2
    hdHR hW hRgraded hDRx0
      (βHenselStructuredWeightInvariant_all_of_alphaWeight_cases_succLift
        H x₀ R hHyp hH hDH hliftSucc h0 hsucc hξ)
      t

/-- Route separated carved alpha cases with successor-order lift identities through the all-`k`
endpoint, with `ξ` discharged. -/
theorem βHensel_weight_bound_of_structured_invariant_alphaWeight_cases_succLift'
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hRgraded : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hliftSucc : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp (t + 1))
        = αGenuine H x₀ R hHyp (t + 1)
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1))
    (h0 : AlphaGenuineRegularWeightLe_zero H x₀ R hHyp hH D)
    (hsucc : ∀ t, AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t)
    (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_of_structured_invariant_alphaWeight_cases_succLift
    H x₀ R hHyp hH hDH hdR2 hdHR hW hRgraded hDRx0 hliftSucc h0 hsucc
      (ClaimA2.weight_ξ_bound x₀ hH hHyp hdR2 hDH hDRx0)
      t

/-- Route `DivWeightLe` through the all-`k` structured-invariant front door for the full P1 weight
bound. -/
theorem βHensel_weight_bound_of_structured_invariant_divWeight
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hRgraded : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdiv : DivWeightLe H x₀ R hHyp hH D)
    (hξ : weight_Λ_over_𝒪 hH (ClaimA2.ξ x₀ R H hHyp) D
            ≤ WithBot.some ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)))
    (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_of_structured_invariant H x₀ R hHyp hH hDH hdR2
    hdHR hW hRgraded hDRx0
      (βHenselStructuredWeightInvariant_all_of_divWeight H x₀ R hHyp hH
        hDH hdiv hξ)
      t

/-- Route normalized divisibility targets through the all-`k` structured-invariant front door for
the full P1 weight bound. -/
theorem βHensel_weight_bound_of_structured_invariant_normalized_divWeight_cases
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hRgraded : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (h0 : ∃ a : 𝒪 H,
      βHensel H x₀ R hHyp 0 = a * W𝒪 H ∧
        weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1)
    (hsucc : ∀ t : ℕ, ∃ a : 𝒪 H,
      βHensel H x₀ R hHyp (t + 1)
        = a * (W𝒪 H) ^ (t + 2) * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t + 1) ∧
        weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1)
    (hξ : weight_Λ_over_𝒪 hH (ClaimA2.ξ x₀ R H hHyp) D
            ≤ WithBot.some ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)))
    (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_of_structured_invariant H x₀ R hHyp hH hDH hdR2
    hdHR hW hRgraded hDRx0
      (βHenselStructuredWeightInvariant_all_of_normalized_divWeight_cases
        H x₀ R hHyp hH hDH h0 hsucc hξ)
      t

/-- Route `DivWeightLe` through the all-`k` structured-invariant front door, with `ξ` discharged. -/
theorem βHensel_weight_bound_of_structured_invariant_divWeight'
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hRgraded : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdiv : DivWeightLe H x₀ R hHyp hH D) (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_of_structured_invariant_divWeight H x₀ R hHyp hH
    hDH hdR2 hdHR hW hRgraded hDRx0 hdiv
      (ClaimA2.weight_ξ_bound x₀ hH hHyp hdR2 hDH hDRx0)
      t

/-- Route normalized divisibility targets through the all-`k` structured-invariant front door,
with `ξ` discharged. -/
theorem βHensel_weight_bound_of_structured_invariant_normalized_divWeight_cases'
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hRgraded : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (h0 : ∃ a : 𝒪 H,
      βHensel H x₀ R hHyp 0 = a * W𝒪 H ∧
        weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1)
    (hsucc : ∀ t : ℕ, ∃ a : 𝒪 H,
      βHensel H x₀ R hHyp (t + 1)
        = a * (W𝒪 H) ^ (t + 2) * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t + 1) ∧
        weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1)
    (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_of_structured_invariant_normalized_divWeight_cases
    H x₀ R hHyp hH hDH hdR2 hdHR hW hRgraded hDRx0 h0 hsucc
      (ClaimA2.weight_ξ_bound x₀ hH hHyp hdR2 hDH hDRx0)
      t

/-- Package the fixed-prefix structured invariant from repaired cleared-base div-weight cases into
the all-`k` family consumed by `βHensel_weight_bound_of_structured_invariant`. -/
theorem βHenselStructuredWeightInvariant_all_of_divWeight_clearedBaseCases
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ} (hDH : Bivariate.totalDegree H ≤ D)
    (hdiv : DivWeightLe_clearedBaseCases H x₀ R hHyp hH D)
    (hξ : weight_Λ_over_𝒪 hH (ClaimA2.ξ x₀ R H hHyp) D
            ≤ WithBot.some ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1))) :
    ∀ k, βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  fun k =>
    βHenselStructuredWeightInvariant_of_divWeight_clearedBaseCases
      H x₀ R hHyp hH hDH hdiv hξ k

/-- Package the all-`k` structured invariant from repaired cleared-base div-weight cases, with the
`ξ` side condition discharged by `ClaimA2.weight_ξ_bound`. -/
theorem βHenselStructuredWeightInvariant_all_of_divWeight_clearedBaseCases'
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdiv : DivWeightLe_clearedBaseCases H x₀ R hHyp hH D) :
    ∀ k, βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  βHenselStructuredWeightInvariant_all_of_divWeight_clearedBaseCases
    H x₀ R hHyp hH hDH hdiv
    (ClaimA2.weight_ξ_bound x₀ hH hHyp hdR2 hDH hDRx0)

/-- Package repaired alpha-side cleared-base cases into the all-`k` structured-invariant surface,
using successor-order lift identities to reach the div-weight side. -/
theorem βHenselStructuredWeightInvariant_all_of_alphaWeight_clearedBaseCases_succLift
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ} (hDH : Bivariate.totalDegree H ≤ D)
    (hliftSucc : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp (t + 1))
        = αGenuine H x₀ R hHyp (t + 1)
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1))
    (hα : AlphaGenuineRegularWeightLe_clearedBaseCases H x₀ R hHyp hH D)
    (hξ : weight_Λ_over_𝒪 hH (ClaimA2.ξ x₀ R H hHyp) D
            ≤ WithBot.some ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1))) :
    ∀ k, βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  fun k =>
    βHenselStructuredWeightInvariant_of_alphaWeight_clearedBaseCases_succLift
      H x₀ R hHyp hH hDH hliftSucc hα hξ k

/-- Package repaired alpha-side cleared-base cases into the all-`k` structured-invariant surface,
with `ξ` discharged by `ClaimA2.weight_ξ_bound`. -/
theorem βHenselStructuredWeightInvariant_all_of_alphaWeight_clearedBaseCases_succLift'
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hliftSucc : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp (t + 1))
        = αGenuine H x₀ R hHyp (t + 1)
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1))
    (hα : AlphaGenuineRegularWeightLe_clearedBaseCases H x₀ R hHyp hH D) :
    ∀ k, βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  βHenselStructuredWeightInvariant_all_of_alphaWeight_clearedBaseCases_succLift
    H x₀ R hHyp hH hDH hliftSucc hα
    (ClaimA2.weight_ξ_bound x₀ hH hHyp hdR2 hDH hDRx0)

/-- Route repaired cleared-base div-weight cases through the all-`k` structured-invariant front
door for the full P1 weight bound. -/
theorem βHensel_weight_bound_of_structured_invariant_divWeight_clearedBaseCases
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hRgraded : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdiv : DivWeightLe_clearedBaseCases H x₀ R hHyp hH D)
    (hξ : weight_Λ_over_𝒪 hH (ClaimA2.ξ x₀ R H hHyp) D
            ≤ WithBot.some ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)))
    (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_of_structured_invariant H x₀ R hHyp hH hDH hdR2
    hdHR hW hRgraded hDRx0
      (βHenselStructuredWeightInvariant_all_of_divWeight_clearedBaseCases
        H x₀ R hHyp hH hDH hdiv hξ)
      t

/-- Route repaired cleared-base div-weight cases through the all-`k` structured-invariant front
door, with `ξ` discharged. -/
theorem βHensel_weight_bound_of_structured_invariant_divWeight_clearedBaseCases'
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hRgraded : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdiv : DivWeightLe_clearedBaseCases H x₀ R hHyp hH D)
    (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_of_structured_invariant_divWeight_clearedBaseCases
    H x₀ R hHyp hH hDH hdR2 hdHR hW hRgraded hDRx0 hdiv
    (ClaimA2.weight_ξ_bound x₀ hH hHyp hdR2 hDH hDRx0) t

/-- Route repaired alpha-side cleared-base cases through the all-`k` structured-invariant front
door via successor-order lift identities. -/
theorem βHensel_weight_bound_of_structured_invariant_alphaWeight_clearedBaseCases_succLift
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hRgraded : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hliftSucc : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp (t + 1))
        = αGenuine H x₀ R hHyp (t + 1)
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1))
    (hα : AlphaGenuineRegularWeightLe_clearedBaseCases H x₀ R hHyp hH D)
    (hξ : weight_Λ_over_𝒪 hH (ClaimA2.ξ x₀ R H hHyp) D
            ≤ WithBot.some ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)))
    (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_of_structured_invariant H x₀ R hHyp hH hDH hdR2
    hdHR hW hRgraded hDRx0
      (βHenselStructuredWeightInvariant_all_of_alphaWeight_clearedBaseCases_succLift
        H x₀ R hHyp hH hDH hliftSucc hα hξ)
      t

/-- Route repaired alpha-side cleared-base cases through the all-`k` structured-invariant front
door via successor-order lift identities, with `ξ` discharged. -/
theorem βHensel_weight_bound_of_structured_invariant_alphaWeight_clearedBaseCases_succLift'
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hRgraded : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hliftSucc : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp (t + 1))
        = αGenuine H x₀ R hHyp (t + 1)
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1))
    (hα : AlphaGenuineRegularWeightLe_clearedBaseCases H x₀ R hHyp hH D)
    (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_of_structured_invariant_alphaWeight_clearedBaseCases_succLift
    H x₀ R hHyp hH hDH hdR2 hdHR hW hRgraded hDRx0 hliftSucc hα
    (ClaimA2.weight_ξ_bound x₀ hH hHyp hdR2 hDH hDRx0) t

end AlphaWeight

end BCIKS20.HenselNumerator

-- Axiom audit: the new packaging layer stays on the existing standard axiom surface only.
#print axioms BCIKS20.HenselNumerator.AlphaWeight.βHenselStructuredWeightInvariant_all_of_alphaWeight
#print axioms BCIKS20.HenselNumerator.AlphaWeight.βHenselStructuredWeightInvariant_all_of_alphaWeight'
#print axioms BCIKS20.HenselNumerator.AlphaWeight.βHenselStructuredWeightInvariant_all_of_alphaWeight_cases
#print axioms BCIKS20.HenselNumerator.AlphaWeight.βHenselStructuredWeightInvariant_all_of_alphaWeight_cases'
#print axioms BCIKS20.HenselNumerator.AlphaWeight.βHenselStructuredWeightInvariant_all_of_divWeight
#print axioms BCIKS20.HenselNumerator.AlphaWeight.βHenselStructuredWeightInvariant_all_of_normalized_divWeight_cases
#print axioms BCIKS20.HenselNumerator.AlphaWeight.βHenselStructuredWeightInvariant_all_of_divWeight'
#print axioms BCIKS20.HenselNumerator.AlphaWeight.βHenselStructuredWeightInvariant_all_of_normalized_divWeight_cases'
#print axioms BCIKS20.HenselNumerator.AlphaWeight.βHenselStructuredWeightInvariant_all_of_alphaWeight_succLift
#print axioms BCIKS20.HenselNumerator.AlphaWeight.βHenselStructuredWeightInvariant_all_of_alphaWeight_succLift'
#print axioms BCIKS20.HenselNumerator.AlphaWeight.βHenselStructuredWeightInvariant_all_of_alphaWeight_cases_succLift
#print axioms BCIKS20.HenselNumerator.AlphaWeight.βHenselStructuredWeightInvariant_all_of_alphaWeight_cases_succLift'
#print axioms BCIKS20.HenselNumerator.AlphaWeight.βHensel_weight_bound_of_structured_invariant_alphaWeight
#print axioms BCIKS20.HenselNumerator.AlphaWeight.βHensel_weight_bound_of_structured_invariant_alphaWeight'
#print axioms BCIKS20.HenselNumerator.AlphaWeight.βHensel_weight_bound_of_structured_invariant_alphaWeight_cases
#print axioms BCIKS20.HenselNumerator.AlphaWeight.βHensel_weight_bound_of_structured_invariant_alphaWeight_cases'
#print axioms BCIKS20.HenselNumerator.AlphaWeight.βHensel_weight_bound_of_structured_invariant_alphaWeight_succLift
#print axioms BCIKS20.HenselNumerator.AlphaWeight.βHensel_weight_bound_of_structured_invariant_alphaWeight_succLift'
#print axioms BCIKS20.HenselNumerator.AlphaWeight.βHensel_weight_bound_of_structured_invariant_alphaWeight_cases_succLift
#print axioms BCIKS20.HenselNumerator.AlphaWeight.βHensel_weight_bound_of_structured_invariant_alphaWeight_cases_succLift'
#print axioms BCIKS20.HenselNumerator.AlphaWeight.βHensel_weight_bound_of_structured_invariant_divWeight
#print axioms BCIKS20.HenselNumerator.AlphaWeight.βHensel_weight_bound_of_structured_invariant_normalized_divWeight_cases
#print axioms BCIKS20.HenselNumerator.AlphaWeight.βHensel_weight_bound_of_structured_invariant_divWeight'
#print axioms BCIKS20.HenselNumerator.AlphaWeight.βHensel_weight_bound_of_structured_invariant_normalized_divWeight_cases'
#print axioms BCIKS20.HenselNumerator.AlphaWeight.βHenselStructuredWeightInvariant_all_of_divWeight_clearedBaseCases
#print axioms BCIKS20.HenselNumerator.AlphaWeight.βHenselStructuredWeightInvariant_all_of_divWeight_clearedBaseCases'
#print axioms BCIKS20.HenselNumerator.AlphaWeight.βHenselStructuredWeightInvariant_all_of_alphaWeight_clearedBaseCases_succLift
#print axioms BCIKS20.HenselNumerator.AlphaWeight.βHenselStructuredWeightInvariant_all_of_alphaWeight_clearedBaseCases_succLift'
#print axioms BCIKS20.HenselNumerator.AlphaWeight.βHensel_weight_bound_of_structured_invariant_divWeight_clearedBaseCases
#print axioms BCIKS20.HenselNumerator.AlphaWeight.βHensel_weight_bound_of_structured_invariant_divWeight_clearedBaseCases'
#print axioms BCIKS20.HenselNumerator.AlphaWeight.βHensel_weight_bound_of_structured_invariant_alphaWeight_clearedBaseCases_succLift
#print axioms BCIKS20.HenselNumerator.AlphaWeight.βHensel_weight_bound_of_structured_invariant_alphaWeight_clearedBaseCases_succLift'
