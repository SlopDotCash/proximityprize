/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P1Conditional
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AlphaWeightAll

/-!
# P1Conditional all-prefix compatibility wrappers

This lightweight layer exposes the all-prefix structured-invariant APIs from `AlphaWeightAll.lean`
in the `BCIKS20.HenselNumerator` namespace used by `P1Conditional.lean`, then routes them through
the older `βHensel_weight_bound_of_structured_invariant` endpoint.  It is compatibility plumbing:
the carved A.4 inputs (`AlphaGenuineRegularWeightLe`, `DivWeightLe`, or normalized factor
witnesses) and any P2 residual hypotheses remain explicit.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace BCIKS20.HenselNumerator

open Polynomial Polynomial.Bivariate
open BCIKS20AppendixA
open ProximityPrize.BCIKS20.GammaGenuine
open AlphaWeight

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-! ## All-prefix structured-invariant wrappers -/

/-- Package the `P1Conditional` carved-alpha route into an all-`k` structured invariant. -/
theorem βHenselStructuredWeightInvariant_all_of_lift
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
  AlphaWeight.βHenselStructuredWeightInvariant_all_of_alphaWeight
    H x₀ R hHyp hH hDH hlift hα hξ

/-- Package the `P1Conditional` carved-alpha route into an all-`k` invariant, with `ξ`
discharged. -/
theorem βHenselStructuredWeightInvariant_all_of_lift'
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
  βHenselStructuredWeightInvariant_all_of_lift H x₀ R hHyp hH hDH hlift hα
    (ClaimA2.weight_ξ_bound x₀ hH hHyp hdR2 hDH hDRx0)

/-- Direct `P1Conditional` alias for the explicit-`ξ` carved-alpha all-prefix route. -/
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
  AlphaWeight.βHenselStructuredWeightInvariant_all_of_alphaWeight
    H x₀ R hHyp hH hDH hlift hα hξ

/-- Direct `P1Conditional` alias for the discharged-`ξ` carved-alpha all-prefix route. -/
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
  βHenselStructuredWeightInvariant_all_of_alphaWeight H x₀ R hHyp hH hDH hlift hα
    (ClaimA2.weight_ξ_bound x₀ hH hHyp hdR2 hDH hDRx0)

/-- Direct all-prefix alias from separated carved-alpha base and successor cases. -/
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
  AlphaWeight.βHenselStructuredWeightInvariant_all_of_alphaWeight_cases
    H x₀ R hHyp hH hDH hlift h0 hsucc hξ

/-- Direct all-prefix alias from separated carved-alpha base and successor cases, with `ξ`
discharged. -/
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
  AlphaWeight.βHenselStructuredWeightInvariant_all_of_alphaWeight_cases'
    H x₀ R hHyp hH hDH hDRx0 hdR2 hlift h0 hsucc

/-- Package the `P1Conditional` `DivWeightLe` route into an all-`k` structured invariant. -/
theorem βHenselStructuredWeightInvariant_all_of_divWeight
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdiv : DivWeightLe H x₀ R hHyp hH D)
    (hξ : weight_Λ_over_𝒪 hH (ClaimA2.ξ x₀ R H hHyp) D
            ≤ WithBot.some ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1))) :
    ∀ k, βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  AlphaWeight.βHenselStructuredWeightInvariant_all_of_divWeight
    H x₀ R hHyp hH hDH hdiv hξ

/-- Package the `P1Conditional` `DivWeightLe` route into an all-`k` invariant, with `ξ`
discharged. -/
theorem βHenselStructuredWeightInvariant_all_of_divWeight'
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdiv : DivWeightLe H x₀ R hHyp hH D) :
    ∀ k, βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  AlphaWeight.βHenselStructuredWeightInvariant_all_of_divWeight'
    H x₀ R hHyp hH hDH hDRx0 hdR2 hdiv

/-- Package normalized base/successor divisibility targets into an all-`k` structured invariant. -/
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
  AlphaWeight.βHenselStructuredWeightInvariant_all_of_normalized_divWeight_cases
    H x₀ R hHyp hH hDH h0 hsucc hξ

/-- Package normalized base/successor divisibility targets into an all-`k` invariant, with `ξ`
discharged. -/
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
  AlphaWeight.βHenselStructuredWeightInvariant_all_of_normalized_divWeight_cases'
    H x₀ R hHyp hH hDH hDRx0 hdR2 h0 hsucc

/-- All-prefix structured invariant from normalized divisibility targets, matching the single-`t`
unlocked normalized P1 front door. -/
theorem βHenselStructuredWeightInvariant_all_unlocked_of_normalized_divWeight_cases
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
  βHenselStructuredWeightInvariant_all_of_normalized_divWeight_cases'
    H x₀ R hHyp hH hDH hDRx0 hdR2 h0 hsucc

/-- Package successor-order lift identities into an all-`k` structured invariant. -/
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
  AlphaWeight.βHenselStructuredWeightInvariant_all_of_alphaWeight_succLift
    H x₀ R hHyp hH hDH hliftSucc hα hξ

/-- Package successor-order lift identities into an all-`k` invariant, with `ξ` discharged. -/
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
  AlphaWeight.βHenselStructuredWeightInvariant_all_of_alphaWeight_succLift'
    H x₀ R hHyp hH hDH hDRx0 hdR2 hliftSucc hα

/-- Direct all-prefix alias from separated carved-alpha cases and successor-order lift identities. -/
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
  AlphaWeight.βHenselStructuredWeightInvariant_all_of_alphaWeight_cases_succLift
    H x₀ R hHyp hH hDH hliftSucc h0 hsucc hξ

/-- Direct all-prefix alias from separated carved-alpha cases and successor-order lift identities,
with `ξ` discharged. -/
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
  AlphaWeight.βHenselStructuredWeightInvariant_all_of_alphaWeight_cases_succLift'
    H x₀ R hHyp hH hDH hDRx0 hdR2 hliftSucc h0 hsucc

/-! ## All-prefix P2-unlocked wrappers -/

/-- All-prefix structured invariant unlocked by the Faà-di-Bruno successor residual. -/
theorem βHenselStructuredWeightInvariant_all_unlocked
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hzero : FaaDiBrunoSuccSumZeroResidual H x₀ R hHyp)
    (hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D) :
    ∀ k, βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  fun k =>
    βHenselStructuredWeightInvariant_unlocked H x₀ R hHyp hH
      hDH hDRx0 hdR2 hzero hα k

/-- All-prefix structured invariant unlocked by the Faà-di-Bruno successor residual, from
`DivWeightLe`. -/
theorem βHenselStructuredWeightInvariant_all_unlocked_of_divWeight
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hzero : FaaDiBrunoSuccSumZeroResidual H x₀ R hHyp)
    (hdiv : DivWeightLe H x₀ R hHyp hH D) :
    ∀ k, βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  fun k =>
    βHenselStructuredWeightInvariant_unlocked_of_divWeight H x₀ R hHyp hH
      hDH hDRx0 hdR2 hzero hdiv k

/-- All-prefix structured invariant unlocked by the Faà-di-Bruno successor residual, from separated
carved-alpha base/successor cases. -/
theorem βHenselStructuredWeightInvariant_all_unlocked_of_alphaWeight_cases
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hzero : FaaDiBrunoSuccSumZeroResidual H x₀ R hHyp)
    (h0 : AlphaGenuineRegularWeightLe_zero H x₀ R hHyp hH D)
    (hsucc : ∀ t, AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t) :
    ∀ k, βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  fun k =>
    βHenselStructuredWeightInvariant_unlocked_of_alphaWeight_cases
      H x₀ R hHyp hH hDH hDRx0 hdR2 hzero h0 hsucc k

/-- All-prefix structured invariant unlocked by full P2 vanishing. -/
theorem βHenselStructuredWeightInvariant_all_unlocked_of_fullVanishes
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hvan : FaaDiBrunoFullSumVanishes H x₀ R hHyp)
    (hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D) :
    ∀ k, βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  fun k =>
    βHenselStructuredWeightInvariant_unlocked_of_fullVanishes H x₀ R hHyp hH
      hDH hDRx0 hdR2 hvan hα k

/-- All-prefix structured invariant unlocked by full P2 vanishing, from `DivWeightLe`. -/
theorem βHenselStructuredWeightInvariant_all_unlocked_of_fullVanishes_divWeight
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hvan : FaaDiBrunoFullSumVanishes H x₀ R hHyp)
    (hdiv : DivWeightLe H x₀ R hHyp hH D) :
    ∀ k, βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  fun k =>
    βHenselStructuredWeightInvariant_unlocked_of_fullVanishes_divWeight
      H x₀ R hHyp hH hDH hDRx0 hdR2 hvan hdiv k

/-- All-prefix structured invariant unlocked by the restricted P2 match. -/
theorem βHenselStructuredWeightInvariant_all_unlocked_of_restrictedMatch
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hmatch : RestrictedFaaDiBrunoMatch H x₀ R hHyp)
    (hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D) :
    ∀ k, βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  fun k =>
    βHenselStructuredWeightInvariant_unlocked_of_restrictedMatch H x₀ R hHyp hH
      hDH hDRx0 hdR2 hmatch hα k

/-- All-prefix structured invariant unlocked by the restricted P2 match, from `DivWeightLe`. -/
theorem βHenselStructuredWeightInvariant_all_unlocked_of_restrictedMatch_divWeight
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hmatch : RestrictedFaaDiBrunoMatch H x₀ R hHyp)
    (hdiv : DivWeightLe H x₀ R hHyp hH D) :
    ∀ k, βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  fun k =>
    βHenselStructuredWeightInvariant_unlocked_of_restrictedMatch_divWeight
      H x₀ R hHyp hH hDH hDRx0 hdR2 hmatch hdiv k

/-! ## Structured-invariant endpoint wrappers -/

/-- Route carved alpha regularity through the all-prefix structured-invariant endpoint. -/
theorem βHensel_weight_bound_of_structured_invariant_lift
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
      (βHenselStructuredWeightInvariant_all_of_lift H x₀ R hHyp hH hDH hlift hα hξ)
      t

/-- Route carved alpha regularity through the all-prefix endpoint, with `ξ` discharged. -/
theorem βHensel_weight_bound_of_structured_invariant_lift'
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
  βHensel_weight_bound_of_structured_invariant_lift H x₀ R hHyp hH hDH hdR2
    hdHR hW hRgraded hDRx0 hlift hα
      (ClaimA2.weight_ξ_bound x₀ hH hHyp hdR2 hDH hDRx0)
      t

/-- Direct `P1Conditional` alias for the explicit-`ξ` carved-alpha structured endpoint. -/
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
  AlphaWeight.βHensel_weight_bound_of_structured_invariant_alphaWeight
    H x₀ R hHyp hH hDH hdR2 hdHR hW hRgraded hDRx0 hlift hα hξ t

/-- Direct `P1Conditional` alias for the discharged-`ξ` carved-alpha structured endpoint. -/
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
  βHensel_weight_bound_of_structured_invariant_alphaWeight
    H x₀ R hHyp hH hDH hdR2 hdHR hW hRgraded hDRx0 hlift hα
      (ClaimA2.weight_ξ_bound x₀ hH hHyp hdR2 hDH hDRx0) t

/-- Direct fixed-`t` endpoint from separated carved-alpha base/successor cases. -/
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

/-- Direct fixed-`t` endpoint from separated carved-alpha base/successor cases, with
`ξ` discharged. -/
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

/-- Route `DivWeightLe` through the all-prefix structured-invariant endpoint. -/
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
      (βHenselStructuredWeightInvariant_all_of_divWeight H x₀ R hHyp hH hDH hdiv hξ)
      t

/-- Route `DivWeightLe` through the all-prefix endpoint, with `ξ` discharged. -/
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

/-- Route normalized divisibility targets through the all-prefix structured-invariant endpoint. -/
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

/-- Route normalized divisibility targets through the all-prefix endpoint, with `ξ` discharged. -/
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

/-- Route successor-lift carved alpha regularity through the all-prefix endpoint. -/
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

/-- Route successor-lift carved alpha regularity through the all-prefix endpoint, with `ξ`
discharged. -/
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

/-- Direct fixed-`t` endpoint from separated carved-alpha cases and successor-order lift
identities. -/
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

/-- Direct fixed-`t` endpoint from separated carved-alpha cases and successor-order lift
identities, with `ξ` discharged. -/
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

/-! ## P2-unlocked structured-invariant endpoint wrappers -/

/-- Route the successor-residual-unlocked all-prefix invariant through the structured endpoint. -/
theorem βHensel_weight_bound_of_structured_invariant_unlocked
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hRgraded : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hzero : FaaDiBrunoSuccSumZeroResidual H x₀ R hHyp)
    (hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D) (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_of_structured_invariant H x₀ R hHyp hH hDH hdR2
    hdHR hW hRgraded hDRx0
      (βHenselStructuredWeightInvariant_all_unlocked H x₀ R hHyp hH
        hDH hDRx0 hdR2 hzero hα)
      t

/-- Route the successor-residual-unlocked all-prefix invariant through the structured endpoint,
from `DivWeightLe`. -/
theorem βHensel_weight_bound_of_structured_invariant_unlocked_of_divWeight
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hRgraded : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hzero : FaaDiBrunoSuccSumZeroResidual H x₀ R hHyp)
    (hdiv : DivWeightLe H x₀ R hHyp hH D) (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_of_structured_invariant H x₀ R hHyp hH hDH hdR2
    hdHR hW hRgraded hDRx0
      (βHenselStructuredWeightInvariant_all_unlocked_of_divWeight H x₀ R hHyp hH
        hDH hDRx0 hdR2 hzero hdiv)
      t

/-- Route the full-vanishing-unlocked all-prefix invariant through the structured endpoint. -/
theorem βHensel_weight_bound_of_structured_invariant_unlocked_of_fullVanishes
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hRgraded : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hvan : FaaDiBrunoFullSumVanishes H x₀ R hHyp)
    (hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D) (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_of_structured_invariant H x₀ R hHyp hH hDH hdR2
    hdHR hW hRgraded hDRx0
      (βHenselStructuredWeightInvariant_all_unlocked_of_fullVanishes H x₀ R hHyp hH
        hDH hDRx0 hdR2 hvan hα)
      t

/-- Route the full-vanishing-unlocked all-prefix invariant through the structured endpoint, from
`DivWeightLe`. -/
theorem βHensel_weight_bound_of_structured_invariant_unlocked_of_fullVanishes_divWeight
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hRgraded : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hvan : FaaDiBrunoFullSumVanishes H x₀ R hHyp)
    (hdiv : DivWeightLe H x₀ R hHyp hH D) (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_of_structured_invariant H x₀ R hHyp hH hDH hdR2
    hdHR hW hRgraded hDRx0
      (βHenselStructuredWeightInvariant_all_unlocked_of_fullVanishes_divWeight
        H x₀ R hHyp hH hDH hDRx0 hdR2 hvan hdiv)
      t

/-- Route the restricted-match-unlocked all-prefix invariant through the structured endpoint. -/
theorem βHensel_weight_bound_of_structured_invariant_unlocked_of_restrictedMatch
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hRgraded : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hmatch : RestrictedFaaDiBrunoMatch H x₀ R hHyp)
    (hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D) (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_of_structured_invariant H x₀ R hHyp hH hDH hdR2
    hdHR hW hRgraded hDRx0
      (βHenselStructuredWeightInvariant_all_unlocked_of_restrictedMatch
        H x₀ R hHyp hH hDH hDRx0 hdR2 hmatch hα)
      t

/-- Route the restricted-match-unlocked all-prefix invariant through the structured endpoint, from
`DivWeightLe`. -/
theorem βHensel_weight_bound_of_structured_invariant_unlocked_of_restrictedMatch_divWeight
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hRgraded : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hmatch : RestrictedFaaDiBrunoMatch H x₀ R hHyp)
    (hdiv : DivWeightLe H x₀ R hHyp hH D) (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_of_structured_invariant H x₀ R hHyp hH hDH hdR2
    hdHR hW hRgraded hDRx0
      (βHenselStructuredWeightInvariant_all_unlocked_of_restrictedMatch_divWeight
        H x₀ R hHyp hH hDH hDRx0 hdR2 hmatch hdiv)
      t

/-! ## All-order structured-invariant endpoint consumers -/

/-- Package the structured-invariant endpoint as a direct all-`t` weight-bound family. -/
theorem βHensel_weight_bound_all_of_structured_invariant
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hRgraded : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hStructuredAll : ∀ k, βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k) :
    ∀ t, weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  fun t =>
    βHensel_weight_bound_of_structured_invariant H x₀ R hHyp hH hDH hdR2
      hdHR hW hRgraded hDRx0 hStructuredAll t

/-- All-`t` P1 weight bound from carved alpha regularity and an explicit `ξ` side condition. -/
theorem βHensel_weight_bound_all_of_structured_invariant_lift
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
            ≤ WithBot.some ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1))) :
    ∀ t, weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_all_of_structured_invariant H x₀ R hHyp hH hDH
    hdR2 hdHR hW hRgraded hDRx0
      (βHenselStructuredWeightInvariant_all_of_lift H x₀ R hHyp hH hDH hlift hα hξ)

/-- All-`t` P1 weight bound from carved alpha regularity with `ξ` discharged. -/
theorem βHensel_weight_bound_all_of_structured_invariant_lift'
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
    (hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D) :
    ∀ t, weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_all_of_structured_invariant H x₀ R hHyp hH hDH
    hdR2 hdHR hW hRgraded hDRx0
      (βHenselStructuredWeightInvariant_all_of_lift' H x₀ R hHyp hH hDH
        hDRx0 hdR2 hlift hα)

/-- Direct all-`t` P1 alias for the explicit-`ξ` carved-alpha structured endpoint. -/
theorem βHensel_weight_bound_all_of_structured_invariant_alphaWeight
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
            ≤ WithBot.some ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1))) :
    ∀ t, weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_all_of_structured_invariant H x₀ R hHyp hH hDH
    hdR2 hdHR hW hRgraded hDRx0
      (AlphaWeight.βHenselStructuredWeightInvariant_all_of_alphaWeight
        H x₀ R hHyp hH hDH hlift hα hξ)

/-- Direct all-`t` P1 alias for the discharged-`ξ` carved-alpha structured endpoint. -/
theorem βHensel_weight_bound_all_of_structured_invariant_alphaWeight'
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
    (hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D) :
    ∀ t, weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_all_of_structured_invariant H x₀ R hHyp hH hDH
    hdR2 hdHR hW hRgraded hDRx0
      (βHenselStructuredWeightInvariant_all_of_alphaWeight' H x₀ R hHyp hH
        hDH hDRx0 hdR2 hlift hα)

/-- All-`t` P1 weight bound from separated carved-alpha base and successor cases. -/
theorem βHensel_weight_bound_all_of_structured_invariant_alphaWeight_cases
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
            ≤ WithBot.some ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1))) :
    ∀ t, weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_all_of_structured_invariant H x₀ R hHyp hH hDH
    hdR2 hdHR hW hRgraded hDRx0
      (βHenselStructuredWeightInvariant_all_of_alphaWeight_cases
        H x₀ R hHyp hH hDH hlift h0 hsucc hξ)

/-- All-`t` P1 weight bound from separated carved-alpha base and successor cases, with `ξ`
discharged. -/
theorem βHensel_weight_bound_all_of_structured_invariant_alphaWeight_cases'
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
    (hsucc : ∀ t, AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t) :
    ∀ t, weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_all_of_structured_invariant H x₀ R hHyp hH hDH
    hdR2 hdHR hW hRgraded hDRx0
      (βHenselStructuredWeightInvariant_all_of_alphaWeight_cases' H x₀ R hHyp hH
        hDH hDRx0 hdR2 hlift h0 hsucc)

/-- All-`t` P1 weight bound from the `DivWeightLe` structured route. -/
theorem βHensel_weight_bound_all_of_structured_invariant_divWeight
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
            ≤ WithBot.some ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1))) :
    ∀ t, weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_all_of_structured_invariant H x₀ R hHyp hH hDH
    hdR2 hdHR hW hRgraded hDRx0
      (βHenselStructuredWeightInvariant_all_of_divWeight H x₀ R hHyp hH hDH hdiv hξ)

/-- All-`t` P1 weight bound from the `DivWeightLe` structured route with `ξ` discharged. -/
theorem βHensel_weight_bound_all_of_structured_invariant_divWeight'
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hRgraded : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdiv : DivWeightLe H x₀ R hHyp hH D) :
    ∀ t, weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_all_of_structured_invariant H x₀ R hHyp hH hDH
    hdR2 hdHR hW hRgraded hDRx0
      (βHenselStructuredWeightInvariant_all_of_divWeight' H x₀ R hHyp hH
        hDH hDRx0 hdR2 hdiv)

/-- All-`t` P1 weight bound from normalized divisibility targets. -/
theorem βHensel_weight_bound_all_of_structured_invariant_normalized_divWeight_cases
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
            ≤ WithBot.some ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1))) :
    ∀ t, weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_all_of_structured_invariant H x₀ R hHyp hH hDH
    hdR2 hdHR hW hRgraded hDRx0
      (βHenselStructuredWeightInvariant_all_of_normalized_divWeight_cases
        H x₀ R hHyp hH hDH h0 hsucc hξ)

/-- All-`t` P1 weight bound from normalized divisibility targets with `ξ` discharged. -/
theorem βHensel_weight_bound_all_of_structured_invariant_normalized_divWeight_cases'
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
        weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1) :
    ∀ t, weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_all_of_structured_invariant H x₀ R hHyp hH hDH
    hdR2 hdHR hW hRgraded hDRx0
      (βHenselStructuredWeightInvariant_all_of_normalized_divWeight_cases'
        H x₀ R hHyp hH hDH hDRx0 hdR2 h0 hsucc)

/-- All-`t` P1 weight bound from normalized divisibility targets, using the same front-door shape as
the single-`t` unlocked normalized endpoint. -/
theorem βHensel_weight_bound_all_unlocked_of_normalized_divWeight_cases
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
        weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1) :
    ∀ t, weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_all_of_structured_invariant_normalized_divWeight_cases'
    H x₀ R hHyp hH hDH hdR2 hdHR hW hRgraded hDRx0 h0 hsucc

/-- All-`t` P1 weight bound from successor-lift carved alpha regularity. -/
theorem βHensel_weight_bound_all_of_structured_invariant_alphaWeight_succLift
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
            ≤ WithBot.some ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1))) :
    ∀ t, weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_all_of_structured_invariant H x₀ R hHyp hH hDH
    hdR2 hdHR hW hRgraded hDRx0
      (βHenselStructuredWeightInvariant_all_of_alphaWeight_succLift
        H x₀ R hHyp hH hDH hliftSucc hα hξ)

/-- All-`t` P1 weight bound from successor-lift carved alpha regularity with `ξ` discharged. -/
theorem βHensel_weight_bound_all_of_structured_invariant_alphaWeight_succLift'
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
    (hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D) :
    ∀ t, weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_all_of_structured_invariant H x₀ R hHyp hH hDH
    hdR2 hdHR hW hRgraded hDRx0
      (βHenselStructuredWeightInvariant_all_of_alphaWeight_succLift'
        H x₀ R hHyp hH hDH hDRx0 hdR2 hliftSucc hα)

/-- All-`t` P1 weight bound from separated carved-alpha cases and successor-order lift
identities. -/
theorem βHensel_weight_bound_all_of_structured_invariant_alphaWeight_cases_succLift
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
            ≤ WithBot.some ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1))) :
    ∀ t, weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_all_of_structured_invariant H x₀ R hHyp hH hDH
    hdR2 hdHR hW hRgraded hDRx0
      (βHenselStructuredWeightInvariant_all_of_alphaWeight_cases_succLift
        H x₀ R hHyp hH hDH hliftSucc h0 hsucc hξ)

/-- All-`t` P1 weight bound from separated carved-alpha cases and successor-order lift identities,
with `ξ` discharged. -/
theorem βHensel_weight_bound_all_of_structured_invariant_alphaWeight_cases_succLift'
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
    (hsucc : ∀ t, AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t) :
    ∀ t, weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_all_of_structured_invariant H x₀ R hHyp hH hDH
    hdR2 hdHR hW hRgraded hDRx0
      (βHenselStructuredWeightInvariant_all_of_alphaWeight_cases_succLift'
        H x₀ R hHyp hH hDH hDRx0 hdR2 hliftSucc h0 hsucc)

/-- All-`t` P1 weight bound from the successor-residual-unlocked route. -/
theorem βHensel_weight_bound_all_of_structured_invariant_unlocked
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hRgraded : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hzero : FaaDiBrunoSuccSumZeroResidual H x₀ R hHyp)
    (hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D) :
    ∀ t, weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_all_of_structured_invariant H x₀ R hHyp hH hDH
    hdR2 hdHR hW hRgraded hDRx0
      (βHenselStructuredWeightInvariant_all_unlocked H x₀ R hHyp hH
        hDH hDRx0 hdR2 hzero hα)

/-- All-`t` P1 weight bound from the successor-residual-unlocked `DivWeightLe` route. -/
theorem βHensel_weight_bound_all_of_structured_invariant_unlocked_of_divWeight
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hRgraded : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hzero : FaaDiBrunoSuccSumZeroResidual H x₀ R hHyp)
    (hdiv : DivWeightLe H x₀ R hHyp hH D) :
    ∀ t, weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_all_of_structured_invariant H x₀ R hHyp hH hDH
    hdR2 hdHR hW hRgraded hDRx0
      (βHenselStructuredWeightInvariant_all_unlocked_of_divWeight H x₀ R hHyp hH
        hDH hDRx0 hdR2 hzero hdiv)

/-- All-`t` P1 weight bound from the successor-residual-unlocked separated alpha cases. -/
theorem βHensel_weight_bound_all_unlocked_of_alphaWeight_cases
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hRgraded : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hzero : FaaDiBrunoSuccSumZeroResidual H x₀ R hHyp)
    (h0 : AlphaGenuineRegularWeightLe_zero H x₀ R hHyp hH D)
    (hsucc : ∀ t, AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t) :
    ∀ t, weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_all_of_structured_invariant H x₀ R hHyp hH hDH
    hdR2 hdHR hW hRgraded hDRx0
      (βHenselStructuredWeightInvariant_all_unlocked_of_alphaWeight_cases
        H x₀ R hHyp hH hDH hDRx0 hdR2 hzero h0 hsucc)

/-- All-`t` P1 weight bound from the full-vanishing-unlocked route. -/
theorem βHensel_weight_bound_all_of_structured_invariant_unlocked_of_fullVanishes
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hRgraded : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hvan : FaaDiBrunoFullSumVanishes H x₀ R hHyp)
    (hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D) :
    ∀ t, weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_all_of_structured_invariant H x₀ R hHyp hH hDH
    hdR2 hdHR hW hRgraded hDRx0
      (βHenselStructuredWeightInvariant_all_unlocked_of_fullVanishes H x₀ R hHyp hH
        hDH hDRx0 hdR2 hvan hα)

/-- All-`t` P1 weight bound from the full-vanishing-unlocked `DivWeightLe` route. -/
theorem βHensel_weight_bound_all_of_structured_invariant_unlocked_of_fullVanishes_divWeight
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hRgraded : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hvan : FaaDiBrunoFullSumVanishes H x₀ R hHyp)
    (hdiv : DivWeightLe H x₀ R hHyp hH D) :
    ∀ t, weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_all_of_structured_invariant H x₀ R hHyp hH hDH
    hdR2 hdHR hW hRgraded hDRx0
      (βHenselStructuredWeightInvariant_all_unlocked_of_fullVanishes_divWeight
        H x₀ R hHyp hH hDH hDRx0 hdR2 hvan hdiv)

/-- All-`t` P1 weight bound from the restricted-match-unlocked route. -/
theorem βHensel_weight_bound_all_of_structured_invariant_unlocked_of_restrictedMatch
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hRgraded : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hmatch : RestrictedFaaDiBrunoMatch H x₀ R hHyp)
    (hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D) :
    ∀ t, weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_all_of_structured_invariant H x₀ R hHyp hH hDH
    hdR2 hdHR hW hRgraded hDRx0
      (βHenselStructuredWeightInvariant_all_unlocked_of_restrictedMatch
        H x₀ R hHyp hH hDH hDRx0 hdR2 hmatch hα)

/-- All-`t` P1 weight bound from the restricted-match-unlocked `DivWeightLe` route. -/
theorem βHensel_weight_bound_all_of_structured_invariant_unlocked_of_restrictedMatch_divWeight
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hRgraded : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hmatch : RestrictedFaaDiBrunoMatch H x₀ R hHyp)
    (hdiv : DivWeightLe H x₀ R hHyp hH D) :
    ∀ t, weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_all_of_structured_invariant H x₀ R hHyp hH hDH
    hdR2 hdHR hW hRgraded hDRx0
      (βHenselStructuredWeightInvariant_all_unlocked_of_restrictedMatch_divWeight
        H x₀ R hHyp hH hDH hDRx0 hdR2 hmatch hdiv)

end BCIKS20.HenselNumerator

-- Axiom audit: this compatibility layer composes existing P1/P2 surfaces and introduces no new
-- axiom dependencies beyond the imported standard surface.
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_all_of_lift
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_all_of_lift'
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_all_of_alphaWeight
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_all_of_alphaWeight'
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_all_of_alphaWeight_cases
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_all_of_alphaWeight_cases'
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_all_of_divWeight
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_all_of_divWeight'
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_all_of_normalized_divWeight_cases
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_all_of_normalized_divWeight_cases'
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_all_unlocked_of_normalized_divWeight_cases
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_all_of_alphaWeight_succLift
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_all_of_alphaWeight_succLift'
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_all_of_alphaWeight_cases_succLift
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_all_of_alphaWeight_cases_succLift'
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_all_unlocked
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_all_unlocked_of_divWeight
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_all_unlocked_of_alphaWeight_cases
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_all_unlocked_of_fullVanishes
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_all_unlocked_of_fullVanishes_divWeight
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_all_unlocked_of_restrictedMatch
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_all_unlocked_of_restrictedMatch_divWeight
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_of_structured_invariant_lift
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_of_structured_invariant_lift'
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_of_structured_invariant_alphaWeight
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_of_structured_invariant_alphaWeight'
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_of_structured_invariant_alphaWeight_cases
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_of_structured_invariant_alphaWeight_cases'
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_of_structured_invariant_divWeight
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_of_structured_invariant_divWeight'
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_of_structured_invariant_normalized_divWeight_cases
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_of_structured_invariant_normalized_divWeight_cases'
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_of_structured_invariant_alphaWeight_succLift
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_of_structured_invariant_alphaWeight_succLift'
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_of_structured_invariant_alphaWeight_cases_succLift
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_of_structured_invariant_alphaWeight_cases_succLift'
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_of_structured_invariant_unlocked
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_of_structured_invariant_unlocked_of_divWeight
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_of_structured_invariant_unlocked_of_fullVanishes
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_of_structured_invariant_unlocked_of_fullVanishes_divWeight
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_of_structured_invariant_unlocked_of_restrictedMatch
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_of_structured_invariant_unlocked_of_restrictedMatch_divWeight
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_all_of_structured_invariant
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_all_of_structured_invariant_lift
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_all_of_structured_invariant_lift'
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_all_of_structured_invariant_alphaWeight
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_all_of_structured_invariant_alphaWeight'
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_all_of_structured_invariant_alphaWeight_cases
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_all_of_structured_invariant_alphaWeight_cases'
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_all_of_structured_invariant_divWeight
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_all_of_structured_invariant_divWeight'
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_all_of_structured_invariant_normalized_divWeight_cases
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_all_of_structured_invariant_normalized_divWeight_cases'
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_all_unlocked_of_normalized_divWeight_cases
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_all_of_structured_invariant_alphaWeight_succLift
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_all_of_structured_invariant_alphaWeight_succLift'
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_all_of_structured_invariant_alphaWeight_cases_succLift
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_all_of_structured_invariant_alphaWeight_cases_succLift'
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_all_of_structured_invariant_unlocked
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_all_of_structured_invariant_unlocked_of_divWeight
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_all_unlocked_of_alphaWeight_cases
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_all_of_structured_invariant_unlocked_of_fullVanishes
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_all_of_structured_invariant_unlocked_of_fullVanishes_divWeight
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_all_of_structured_invariant_unlocked_of_restrictedMatch
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_all_of_structured_invariant_unlocked_of_restrictedMatch_divWeight
