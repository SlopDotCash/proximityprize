/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P1Conditional
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AlphaWeightCleared

/-!
# Corrected cleared-base conditional P1 unlock wrappers

Compatibility wrappers connecting the repaired cleared-base #138 predicates to the existing
`P1Conditional` endpoint surface.  The direct div-weight wrappers are lift-free.  The alpha-side
wrappers use only successor-order lift identities, and the `fullVanishes` / `restrictedMatch`
wrappers obtain those successor identities from the existing P2 closed endpoints.  Fixed-base
successor routes are exposed as direct P1 endpoints by first assembling the corrected cleared-base
case split.

These declarations do not prove the remaining successor witnesses, `RestrictedFaaDiBrunoMatch`, or
full P1 from first principles; they keep downstream consumers off the known-false un-cleared
order-zero predicate.
-/

noncomputable section
set_option linter.style.longLine false

namespace BCIKS20.HenselNumerator

open Polynomial Polynomial.Bivariate
open BCIKS20AppendixA
open ProximityPrize.BCIKS20.GammaGenuine
open AlphaWeight

section P1ConditionalCleared

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- Prefix structured invariant from the repaired cleared-base div-weight cases, exposed from the
P1 conditional namespace with the `ξ` side condition discharged. -/
theorem βHenselStructuredWeightInvariant_unlocked_of_divWeight_clearedBaseCases
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdiv : DivWeightLe_clearedBaseCases H x₀ R hHyp hH D) (k : ℕ) :
    βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  AlphaWeight.βHenselStructuredWeightInvariant_of_divWeight_clearedBaseCases'
    H x₀ R hHyp hH hDH hDRx0 hdR2 hdiv k

/-- Prefix structured invariant from repaired alpha-side cleared-base cases and successor-order
lift identities, exposed from the P1 conditional namespace with `ξ` discharged. -/
theorem βHenselStructuredWeightInvariant_unlocked_of_alphaWeight_clearedBaseCases_succLift
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
    (hα : AlphaGenuineRegularWeightLe_clearedBaseCases H x₀ R hHyp hH D) (k : ℕ) :
    βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  AlphaWeight.βHenselStructuredWeightInvariant_of_alphaWeight_clearedBaseCases_succLift'
    H x₀ R hHyp hH hDH hDRx0 hdR2 hliftSucc hα k

/-- Prefix structured invariant unlocked by full P2 vanishing and repaired alpha-side
cleared-base cases. -/
theorem βHenselStructuredWeightInvariant_unlocked_of_fullVanishes_clearedBaseCases
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hvan : FaaDiBrunoFullSumVanishes H x₀ R hHyp)
    (hα : AlphaGenuineRegularWeightLe_clearedBaseCases H x₀ R hHyp hH D) (k : ℕ) :
    βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  βHenselStructuredWeightInvariant_unlocked_of_alphaWeight_clearedBaseCases_succLift
    H x₀ R hHyp hH hDH hDRx0 hdR2
    (fun t => (P2_closed_of_fullVanishes H x₀ R hHyp hvan).2 (t + 1)) hα k

/-- Prefix structured invariant unlocked by the restricted P2 match and repaired alpha-side
cleared-base cases. -/
theorem βHenselStructuredWeightInvariant_unlocked_of_restrictedMatch_clearedBaseCases
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hmatch : RestrictedFaaDiBrunoMatch H x₀ R hHyp)
    (hα : AlphaGenuineRegularWeightLe_clearedBaseCases H x₀ R hHyp hH D) (k : ℕ) :
    βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  βHenselStructuredWeightInvariant_unlocked_of_alphaWeight_clearedBaseCases_succLift
    H x₀ R hHyp hH hDH hDRx0 hdR2
    (fun t => (P2_closed_of_restrictedMatch H x₀ R hHyp hmatch).2 (t + 1)) hα k

/-- P1 weight bound unlocked directly from repaired cleared-base div-weight cases. -/
theorem βHensel_weight_bound_unlocked_of_divWeight_clearedBaseCases
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hdiv : DivWeightLe_clearedBaseCases H x₀ R hHyp hH D) (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  AlphaWeight.βHensel_weight_bound_of_divWeight_clearedBaseCases'
    H x₀ R hHyp hH hDH hDRx0 hdR2 hdHR hW hdiv t

/-- P1 weight bound from repaired alpha-side cleared-base cases and successor-order lift
identities, with `ξ` discharged. -/
theorem βHensel_weight_bound_unlocked_of_alphaWeight_clearedBaseCases_succLift
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hliftSucc : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp (t + 1))
        = αGenuine H x₀ R hHyp (t + 1)
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1))
    (hα : AlphaGenuineRegularWeightLe_clearedBaseCases H x₀ R hHyp hH D) (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  AlphaWeight.βHensel_weight_bound_of_alphaWeight_clearedBaseCases_succLift'
    H x₀ R hHyp hH hDH hDRx0 hdR2 hdHR hW hliftSucc hα t

/-- P1 weight bound unlocked by full P2 vanishing and repaired alpha-side cleared-base cases. -/
theorem βHensel_weight_bound_unlocked_of_fullVanishes_clearedBaseCases
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hvan : FaaDiBrunoFullSumVanishes H x₀ R hHyp)
    (hα : AlphaGenuineRegularWeightLe_clearedBaseCases H x₀ R hHyp hH D) (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_unlocked_of_alphaWeight_clearedBaseCases_succLift
    H x₀ R hHyp hH hDH hDRx0 hdR2 hdHR hW
    (fun t => (P2_closed_of_fullVanishes H x₀ R hHyp hvan).2 (t + 1)) hα t

/-- P1 weight bound unlocked by the restricted P2 match and repaired alpha-side cleared-base
cases. -/
theorem βHensel_weight_bound_unlocked_of_restrictedMatch_clearedBaseCases
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hmatch : RestrictedFaaDiBrunoMatch H x₀ R hHyp)
    (hα : AlphaGenuineRegularWeightLe_clearedBaseCases H x₀ R hHyp hH D) (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_unlocked_of_alphaWeight_clearedBaseCases_succLift
    H x₀ R hHyp hH hDH hDRx0 hdR2 hdHR hW
    (fun t => (P2_closed_of_restrictedMatch H x₀ R hHyp hmatch).2 (t + 1)) hα t

/-- All-prefix structured invariant unlocked directly from repaired cleared-base div-weight
cases. -/
theorem βHenselStructuredWeightInvariant_all_unlocked_of_divWeight_clearedBaseCases
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdiv : DivWeightLe_clearedBaseCases H x₀ R hHyp hH D) :
    ∀ k, βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  fun k =>
    βHenselStructuredWeightInvariant_unlocked_of_divWeight_clearedBaseCases
      H x₀ R hHyp hH hDH hDRx0 hdR2 hdiv k

/-- All-prefix structured invariant from repaired alpha-side cleared-base cases and successor
lift identities. -/
theorem βHenselStructuredWeightInvariant_all_unlocked_of_alphaWeight_clearedBaseCases_succLift
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
  fun k =>
    βHenselStructuredWeightInvariant_unlocked_of_alphaWeight_clearedBaseCases_succLift
      H x₀ R hHyp hH hDH hDRx0 hdR2 hliftSucc hα k

/-- All-prefix structured invariant unlocked by full P2 vanishing and repaired alpha-side
cleared-base cases. -/
theorem βHenselStructuredWeightInvariant_all_unlocked_of_fullVanishes_clearedBaseCases
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hvan : FaaDiBrunoFullSumVanishes H x₀ R hHyp)
    (hα : AlphaGenuineRegularWeightLe_clearedBaseCases H x₀ R hHyp hH D) :
    ∀ k, βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  fun k =>
    βHenselStructuredWeightInvariant_unlocked_of_fullVanishes_clearedBaseCases
      H x₀ R hHyp hH hDH hDRx0 hdR2 hvan hα k

/-- All-prefix structured invariant unlocked by the restricted P2 match and repaired alpha-side
cleared-base cases. -/
theorem βHenselStructuredWeightInvariant_all_unlocked_of_restrictedMatch_clearedBaseCases
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hmatch : RestrictedFaaDiBrunoMatch H x₀ R hHyp)
    (hα : AlphaGenuineRegularWeightLe_clearedBaseCases H x₀ R hHyp hH D) :
    ∀ k, βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  fun k =>
    βHenselStructuredWeightInvariant_unlocked_of_restrictedMatch_clearedBaseCases
      H x₀ R hHyp hH hDH hDRx0 hdR2 hmatch hα k

/-- All-prefix P1 weight bound unlocked directly from repaired cleared-base div-weight cases. -/
theorem βHensel_weight_bound_all_unlocked_of_divWeight_clearedBaseCases
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hdiv : DivWeightLe_clearedBaseCases H x₀ R hHyp hH D) :
    ∀ t, weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  fun t =>
    βHensel_weight_bound_unlocked_of_divWeight_clearedBaseCases
      H x₀ R hHyp hH hDH hDRx0 hdR2 hdHR hW hdiv t

/-- All-prefix P1 weight bound from repaired alpha-side cleared-base cases and successor lift
identities. -/
theorem βHensel_weight_bound_all_unlocked_of_alphaWeight_clearedBaseCases_succLift
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hliftSucc : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp (t + 1))
        = αGenuine H x₀ R hHyp (t + 1)
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1))
    (hα : AlphaGenuineRegularWeightLe_clearedBaseCases H x₀ R hHyp hH D) :
    ∀ t, weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  fun t =>
    βHensel_weight_bound_unlocked_of_alphaWeight_clearedBaseCases_succLift
      H x₀ R hHyp hH hDH hDRx0 hdR2 hdHR hW hliftSucc hα t

/-- All-prefix P1 weight bound unlocked by full P2 vanishing and repaired alpha-side
cleared-base cases. -/
theorem βHensel_weight_bound_all_unlocked_of_fullVanishes_clearedBaseCases
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hvan : FaaDiBrunoFullSumVanishes H x₀ R hHyp)
    (hα : AlphaGenuineRegularWeightLe_clearedBaseCases H x₀ R hHyp hH D) :
    ∀ t, weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  fun t =>
    βHensel_weight_bound_unlocked_of_fullVanishes_clearedBaseCases
      H x₀ R hHyp hH hDH hDRx0 hdR2 hdHR hW hvan hα t

/-- All-prefix P1 weight bound unlocked by the restricted P2 match and repaired alpha-side
cleared-base cases. -/
theorem βHensel_weight_bound_all_unlocked_of_restrictedMatch_clearedBaseCases
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hmatch : RestrictedFaaDiBrunoMatch H x₀ R hHyp)
    (hα : AlphaGenuineRegularWeightLe_clearedBaseCases H x₀ R hHyp hH D) :
    ∀ t, weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  fun t =>
    βHensel_weight_bound_unlocked_of_restrictedMatch_clearedBaseCases
      H x₀ R hHyp hH hDH hDRx0 hdR2 hdHR hW hmatch hα t

/-! ## P2-closed alpha/div successor equivalence wrappers -/

/-- Full P2 vanishing supplies the successor-order lift identities needed to convert the
alpha-side and div-weight successor residual families. -/
theorem alphaWeight_successors_iff_divWeight_successors_of_fullVanishes
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (D : ℕ)
    (hvan : FaaDiBrunoFullSumVanishes H x₀ R hHyp) :
    (∀ t, AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t) ↔
      ∀ t, DivWeightLe_succ H x₀ R hHyp hH D t :=
  alphaWeight_successors_iff_divWeight_successors_succLift H x₀ R hHyp hH D
    (fun t => (P2_closed_of_fullVanishes H x₀ R hHyp hvan).2 (t + 1))

/-- Restricted P2 matching supplies the successor-order lift identities needed to convert the
alpha-side and div-weight successor residual families. -/
theorem alphaWeight_successors_iff_divWeight_successors_of_restrictedMatch
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (D : ℕ)
    (hmatch : RestrictedFaaDiBrunoMatch H x₀ R hHyp) :
    (∀ t, AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t) ↔
      ∀ t, DivWeightLe_succ H x₀ R hHyp hH D t :=
  alphaWeight_successors_iff_divWeight_successors_succLift H x₀ R hHyp hH D
    (fun t => (P2_closed_of_restrictedMatch H x₀ R hHyp hmatch).2 (t + 1))

/-- Full P2 vanishing supplies the successor-order lift identities needed to equate carved
alpha-weight regularity with the normalized divisibility base/successor targets. -/
theorem alphaWeight_iff_normalized_divWeight_cases_of_fullVanishes
    (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ)
    (hvan : FaaDiBrunoFullSumVanishes H x₀ R hHyp) :
    AlphaGenuineRegularWeightLe H x₀ R hHyp hH D ↔
      (∃ a : 𝒪 H,
        βHensel H x₀ R hHyp 0 = a * W𝒪 H ∧
          weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1) ∧
        ∀ t : ℕ, ∃ a : 𝒪 H,
          βHensel H x₀ R hHyp (t + 1)
            = a * (W𝒪 H) ^ (t + 2) * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t + 1) ∧
            weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1 :=
  AlphaWeight.alphaWeight_iff_normalized_divWeight_cases_succLift
    H x₀ R hHyp hH D
    (fun t => (P2_closed_of_fullVanishes H x₀ R hHyp hvan).2 (t + 1))

/-- Full P2 vanishing turns normalized divisibility base/successor targets into carved
alpha-weight regularity. -/
theorem alphaWeight_of_normalized_divWeight_cases_of_fullVanishes
    (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ)
    (hvan : FaaDiBrunoFullSumVanishes H x₀ R hHyp)
    (h0 : ∃ a : 𝒪 H,
      βHensel H x₀ R hHyp 0 = a * W𝒪 H ∧
        weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1)
    (hsucc : ∀ t : ℕ, ∃ a : 𝒪 H,
      βHensel H x₀ R hHyp (t + 1)
        = a * (W𝒪 H) ^ (t + 2) * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t + 1) ∧
        weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1) :
    AlphaGenuineRegularWeightLe H x₀ R hHyp hH D :=
  (alphaWeight_iff_normalized_divWeight_cases_of_fullVanishes
    H x₀ R hHyp hH D hvan).2 ⟨h0, hsucc⟩

/-- Restricted P2 matching supplies the successor-order lift identities needed to equate carved
alpha-weight regularity with the normalized divisibility base/successor targets. -/
theorem alphaWeight_iff_normalized_divWeight_cases_of_restrictedMatch
    (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ)
    (hmatch : RestrictedFaaDiBrunoMatch H x₀ R hHyp) :
    AlphaGenuineRegularWeightLe H x₀ R hHyp hH D ↔
      (∃ a : 𝒪 H,
        βHensel H x₀ R hHyp 0 = a * W𝒪 H ∧
          weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1) ∧
        ∀ t : ℕ, ∃ a : 𝒪 H,
          βHensel H x₀ R hHyp (t + 1)
            = a * (W𝒪 H) ^ (t + 2) * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t + 1) ∧
            weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1 :=
  AlphaWeight.alphaWeight_iff_normalized_divWeight_cases_succLift
    H x₀ R hHyp hH D
    (fun t => (P2_closed_of_restrictedMatch H x₀ R hHyp hmatch).2 (t + 1))

/-- Restricted P2 matching turns normalized divisibility base/successor targets into carved
alpha-weight regularity. -/
theorem alphaWeight_of_normalized_divWeight_cases_of_restrictedMatch
    (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ)
    (hmatch : RestrictedFaaDiBrunoMatch H x₀ R hHyp)
    (h0 : ∃ a : 𝒪 H,
      βHensel H x₀ R hHyp 0 = a * W𝒪 H ∧
        weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1)
    (hsucc : ∀ t : ℕ, ∃ a : 𝒪 H,
      βHensel H x₀ R hHyp (t + 1)
        = a * (W𝒪 H) ^ (t + 2) * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t + 1) ∧
        weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1) :
    AlphaGenuineRegularWeightLe H x₀ R hHyp hH D :=
  (alphaWeight_iff_normalized_divWeight_cases_of_restrictedMatch
    H x₀ R hHyp hH D hmatch).2 ⟨h0, hsucc⟩

theorem alphaWeight_iff_divWeight_of_fullVanishes
    (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ)
    (hvan : FaaDiBrunoFullSumVanishes H x₀ R hHyp) :
    AlphaGenuineRegularWeightLe H x₀ R hHyp hH D ↔
      DivWeightLe H x₀ R hHyp hH D :=
  AlphaWeight.alphaWeight_iff_divWeight_of_succLift H x₀ R hHyp hH D
    (fun t => (P2_closed_of_fullVanishes H x₀ R hHyp hvan).2 (t + 1))

theorem divWeight_of_alphaWeight_of_fullVanishes
    (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ)
    (hvan : FaaDiBrunoFullSumVanishes H x₀ R hHyp)
    (hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D) :
    DivWeightLe H x₀ R hHyp hH D :=
  (alphaWeight_iff_divWeight_of_fullVanishes
    H x₀ R hHyp hH D hvan).1 hα

theorem alphaWeight_of_divWeight_of_fullVanishes
    (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ)
    (hvan : FaaDiBrunoFullSumVanishes H x₀ R hHyp)
    (hdiv : DivWeightLe H x₀ R hHyp hH D) :
    AlphaGenuineRegularWeightLe H x₀ R hHyp hH D :=
  (alphaWeight_iff_divWeight_of_fullVanishes
    H x₀ R hHyp hH D hvan).2 hdiv

theorem normalized_divWeight_cases_of_alphaWeight_of_fullVanishes
    (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ)
    (hvan : FaaDiBrunoFullSumVanishes H x₀ R hHyp)
    (hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D) :
      (∃ a : 𝒪 H,
        βHensel H x₀ R hHyp 0 = a * W𝒪 H ∧
          weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1) ∧
        ∀ t : ℕ, ∃ a : 𝒪 H,
          βHensel H x₀ R hHyp (t + 1)
            = a * (W𝒪 H) ^ (t + 2) * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t + 1) ∧
            weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1 :=
  (alphaWeight_iff_normalized_divWeight_cases_of_fullVanishes
    H x₀ R hHyp hH D hvan).1 hα

theorem normalized_divWeight_zero_of_alphaWeight_of_fullVanishes
    (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ)
    (hvan : FaaDiBrunoFullSumVanishes H x₀ R hHyp)
    (hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D) :
    ∃ a : 𝒪 H,
      βHensel H x₀ R hHyp 0 = a * W𝒪 H ∧
        weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1 :=
  (normalized_divWeight_cases_of_alphaWeight_of_fullVanishes
    H x₀ R hHyp hH D hvan hα).1

theorem normalized_divWeight_succ_of_alphaWeight_of_fullVanishes
    (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D t : ℕ)
    (hvan : FaaDiBrunoFullSumVanishes H x₀ R hHyp)
    (hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D) :
    ∃ a : 𝒪 H,
      βHensel H x₀ R hHyp (t + 1)
        = a * (W𝒪 H) ^ (t + 2) * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t + 1) ∧
        weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1 :=
  (normalized_divWeight_cases_of_alphaWeight_of_fullVanishes
    H x₀ R hHyp hH D hvan hα).2 t

theorem alphaWeight_iff_divWeight_of_restrictedMatch
    (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ)
    (hmatch : RestrictedFaaDiBrunoMatch H x₀ R hHyp) :
    AlphaGenuineRegularWeightLe H x₀ R hHyp hH D ↔
      DivWeightLe H x₀ R hHyp hH D :=
  AlphaWeight.alphaWeight_iff_divWeight_of_succLift H x₀ R hHyp hH D
    (fun t => (P2_closed_of_restrictedMatch H x₀ R hHyp hmatch).2 (t + 1))

theorem divWeight_of_alphaWeight_of_restrictedMatch
    (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ)
    (hmatch : RestrictedFaaDiBrunoMatch H x₀ R hHyp)
    (hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D) :
    DivWeightLe H x₀ R hHyp hH D :=
  (alphaWeight_iff_divWeight_of_restrictedMatch
    H x₀ R hHyp hH D hmatch).1 hα

theorem alphaWeight_of_divWeight_of_restrictedMatch
    (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ)
    (hmatch : RestrictedFaaDiBrunoMatch H x₀ R hHyp)
    (hdiv : DivWeightLe H x₀ R hHyp hH D) :
    AlphaGenuineRegularWeightLe H x₀ R hHyp hH D :=
  (alphaWeight_iff_divWeight_of_restrictedMatch
    H x₀ R hHyp hH D hmatch).2 hdiv

theorem normalized_divWeight_cases_of_alphaWeight_of_restrictedMatch
    (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ)
    (hmatch : RestrictedFaaDiBrunoMatch H x₀ R hHyp)
    (hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D) :
      (∃ a : 𝒪 H,
        βHensel H x₀ R hHyp 0 = a * W𝒪 H ∧
          weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1) ∧
        ∀ t : ℕ, ∃ a : 𝒪 H,
          βHensel H x₀ R hHyp (t + 1)
            = a * (W𝒪 H) ^ (t + 2) * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t + 1) ∧
            weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1 :=
  (alphaWeight_iff_normalized_divWeight_cases_of_restrictedMatch
    H x₀ R hHyp hH D hmatch).1 hα

theorem normalized_divWeight_zero_of_alphaWeight_of_restrictedMatch
    (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ)
    (hmatch : RestrictedFaaDiBrunoMatch H x₀ R hHyp)
    (hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D) :
    ∃ a : 𝒪 H,
      βHensel H x₀ R hHyp 0 = a * W𝒪 H ∧
        weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1 :=
  (normalized_divWeight_cases_of_alphaWeight_of_restrictedMatch
    H x₀ R hHyp hH D hmatch hα).1

theorem normalized_divWeight_succ_of_alphaWeight_of_restrictedMatch
    (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D t : ℕ)
    (hmatch : RestrictedFaaDiBrunoMatch H x₀ R hHyp)
    (hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D) :
    ∃ a : 𝒪 H,
      βHensel H x₀ R hHyp (t + 1)
        = a * (W𝒪 H) ^ (t + 2) * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t + 1) ∧
        weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1 :=
  (normalized_divWeight_cases_of_alphaWeight_of_restrictedMatch
    H x₀ R hHyp hH D hmatch hα).2 t

/-- Full P2 vanishing routes normalized divisibility base/successor targets to the structured
`βHensel` weight invariant. -/
theorem βHenselStructuredWeightInvariant_unlocked_of_normalized_divWeight_cases_of_fullVanishes
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hvan : FaaDiBrunoFullSumVanishes H x₀ R hHyp)
    (h0 : ∃ a : 𝒪 H,
      βHensel H x₀ R hHyp 0 = a * W𝒪 H ∧
        weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1)
    (hsucc : ∀ t : ℕ, ∃ a : 𝒪 H,
      βHensel H x₀ R hHyp (t + 1)
        = a * (W𝒪 H) ^ (t + 2) * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t + 1) ∧
        weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1)
    (k : ℕ) :
    βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  AlphaWeight.βHenselStructuredWeightInvariant_of_alphaWeight_succLift'
    H x₀ R hHyp hH hDH hDRx0 hdR2
    (fun t => (P2_closed_of_fullVanishes H x₀ R hHyp hvan).2 (t + 1))
    (alphaWeight_of_normalized_divWeight_cases_of_fullVanishes
      H x₀ R hHyp hH D hvan h0 hsucc)
    k

/-- Restricted P2 matching routes normalized divisibility base/successor targets to the structured
`βHensel` weight invariant. -/
theorem βHenselStructuredWeightInvariant_unlocked_of_normalized_divWeight_cases_of_restrictedMatch
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hmatch : RestrictedFaaDiBrunoMatch H x₀ R hHyp)
    (h0 : ∃ a : 𝒪 H,
      βHensel H x₀ R hHyp 0 = a * W𝒪 H ∧
        weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1)
    (hsucc : ∀ t : ℕ, ∃ a : 𝒪 H,
      βHensel H x₀ R hHyp (t + 1)
        = a * (W𝒪 H) ^ (t + 2) * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t + 1) ∧
        weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1)
    (k : ℕ) :
    βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  AlphaWeight.βHenselStructuredWeightInvariant_of_alphaWeight_succLift'
    H x₀ R hHyp hH hDH hDRx0 hdR2
    (fun t => (P2_closed_of_restrictedMatch H x₀ R hHyp hmatch).2 (t + 1))
    (alphaWeight_of_normalized_divWeight_cases_of_restrictedMatch
      H x₀ R hHyp hH D hmatch h0 hsucc)
    k

/-- All-prefix structured invariants from full P2 vanishing and normalized divisibility cases. -/
theorem βHenselStructuredWeightInvariant_all_unlocked_of_normalized_divWeight_cases_of_fullVanishes
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hvan : FaaDiBrunoFullSumVanishes H x₀ R hHyp)
    (h0 : ∃ a : 𝒪 H,
      βHensel H x₀ R hHyp 0 = a * W𝒪 H ∧
        weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1)
    (hsucc : ∀ t : ℕ, ∃ a : 𝒪 H,
      βHensel H x₀ R hHyp (t + 1)
        = a * (W𝒪 H) ^ (t + 2) * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t + 1) ∧
        weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1) :
    ∀ k, βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  fun k =>
    βHenselStructuredWeightInvariant_unlocked_of_normalized_divWeight_cases_of_fullVanishes
      H x₀ R hHyp hH hDH hDRx0 hdR2 hvan h0 hsucc k

/-- All-prefix structured invariants from restricted P2 matching and normalized divisibility
cases. -/
theorem βHenselStructuredWeightInvariant_all_unlocked_of_normalized_divWeight_cases_of_restrictedMatch
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hmatch : RestrictedFaaDiBrunoMatch H x₀ R hHyp)
    (h0 : ∃ a : 𝒪 H,
      βHensel H x₀ R hHyp 0 = a * W𝒪 H ∧
        weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1)
    (hsucc : ∀ t : ℕ, ∃ a : 𝒪 H,
      βHensel H x₀ R hHyp (t + 1)
        = a * (W𝒪 H) ^ (t + 2) * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t + 1) ∧
        weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1) :
    ∀ k, βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  fun k =>
    βHenselStructuredWeightInvariant_unlocked_of_normalized_divWeight_cases_of_restrictedMatch
      H x₀ R hHyp hH hDH hDRx0 hdR2 hmatch h0 hsucc k

/-- Full P2 vanishing routes normalized divisibility base/successor targets directly to the P1
`βHensel` weight-bound endpoint. -/
theorem βHensel_weight_bound_unlocked_of_normalized_divWeight_cases_of_fullVanishes
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hvan : FaaDiBrunoFullSumVanishes H x₀ R hHyp)
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
  AlphaWeight.βHensel_weight_bound_of_alphaWeight_succLift'
    H x₀ R hHyp hH hDH hDRx0 hdR2 hdHR hW
    (fun t => (P2_closed_of_fullVanishes H x₀ R hHyp hvan).2 (t + 1))
    (alphaWeight_of_normalized_divWeight_cases_of_fullVanishes
      H x₀ R hHyp hH D hvan h0 hsucc)
    t

/-- Restricted P2 matching routes normalized divisibility base/successor targets directly to the
P1 `βHensel` weight-bound endpoint. -/
theorem βHensel_weight_bound_unlocked_of_normalized_divWeight_cases_of_restrictedMatch
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hmatch : RestrictedFaaDiBrunoMatch H x₀ R hHyp)
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
  AlphaWeight.βHensel_weight_bound_of_alphaWeight_succLift'
    H x₀ R hHyp hH hDH hDRx0 hdR2 hdHR hW
    (fun t => (P2_closed_of_restrictedMatch H x₀ R hHyp hmatch).2 (t + 1))
    (alphaWeight_of_normalized_divWeight_cases_of_restrictedMatch
      H x₀ R hHyp hH D hmatch h0 hsucc)
    t

/-- All-prefix P1 weight bounds from full P2 vanishing and normalized divisibility cases. -/
theorem βHensel_weight_bound_all_unlocked_of_normalized_divWeight_cases_of_fullVanishes
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hvan : FaaDiBrunoFullSumVanishes H x₀ R hHyp)
    (h0 : ∃ a : 𝒪 H,
      βHensel H x₀ R hHyp 0 = a * W𝒪 H ∧
        weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1)
    (hsucc : ∀ t : ℕ, ∃ a : 𝒪 H,
      βHensel H x₀ R hHyp (t + 1)
        = a * (W𝒪 H) ^ (t + 2) * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t + 1) ∧
        weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1) :
    ∀ t, weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  fun t =>
    βHensel_weight_bound_unlocked_of_normalized_divWeight_cases_of_fullVanishes
      H x₀ R hHyp hH hDH hDRx0 hdR2 hdHR hW hvan h0 hsucc t

/-- All-prefix P1 weight bounds from restricted P2 matching and normalized divisibility cases. -/
theorem βHensel_weight_bound_all_unlocked_of_normalized_divWeight_cases_of_restrictedMatch
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hmatch : RestrictedFaaDiBrunoMatch H x₀ R hHyp)
    (h0 : ∃ a : 𝒪 H,
      βHensel H x₀ R hHyp 0 = a * W𝒪 H ∧
        weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1)
    (hsucc : ∀ t : ℕ, ∃ a : 𝒪 H,
      βHensel H x₀ R hHyp (t + 1)
        = a * (W𝒪 H) ^ (t + 2) * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t + 1) ∧
        weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1) :
    ∀ t, weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  fun t =>
    βHensel_weight_bound_unlocked_of_normalized_divWeight_cases_of_restrictedMatch
      H x₀ R hHyp hH hDH hDRx0 hdR2 hdHR hW hmatch h0 hsucc t

/-- With the corrected alpha-side base fixed, full P2 vanishing turns the repaired alpha case
split into the div-weight successor family. -/
theorem alphaWeight_clearedBaseCases_iff_divWeight_successors_of_fullVanishes_fixed
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (hd : 2 ≤ H.natDegree) {D : ℕ}
    (hD : D ≤ H.natDegree) (hvan : FaaDiBrunoFullSumVanishes H x₀ R hHyp) :
    AlphaGenuineRegularWeightLe_clearedBaseCases H x₀ R hHyp hH D ↔
      ∀ t, DivWeightLe_succ H x₀ R hHyp hH D t :=
  alphaWeight_clearedBaseCases_iff_divWeight_successors_of_fixed_succLift
    H x₀ R hHyp hH hd hD
    (fun t => (P2_closed_of_fullVanishes H x₀ R hHyp hvan).2 (t + 1))

/-- With the corrected div-weight base fixed, full P2 vanishing turns the repaired div-weight case
split into the alpha-side successor family. -/
theorem divWeight_clearedBaseCases_iff_alphaWeight_successors_of_fullVanishes_fixed
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (hd : 2 ≤ H.natDegree) {D : ℕ}
    (hD : D ≤ H.natDegree) (hvan : FaaDiBrunoFullSumVanishes H x₀ R hHyp) :
    DivWeightLe_clearedBaseCases H x₀ R hHyp hH D ↔
      ∀ t, AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t :=
  divWeight_clearedBaseCases_iff_alphaWeight_successors_of_fixed_succLift
    H x₀ R hHyp hH hd hD
    (fun t => (P2_closed_of_fullVanishes H x₀ R hHyp hvan).2 (t + 1))

/-- With the corrected alpha-side base fixed, restricted P2 matching turns the repaired alpha case
split into the div-weight successor family. -/
theorem alphaWeight_clearedBaseCases_iff_divWeight_successors_of_restrictedMatch_fixed
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (hd : 2 ≤ H.natDegree) {D : ℕ}
    (hD : D ≤ H.natDegree) (hmatch : RestrictedFaaDiBrunoMatch H x₀ R hHyp) :
    AlphaGenuineRegularWeightLe_clearedBaseCases H x₀ R hHyp hH D ↔
      ∀ t, DivWeightLe_succ H x₀ R hHyp hH D t :=
  alphaWeight_clearedBaseCases_iff_divWeight_successors_of_fixed_succLift
    H x₀ R hHyp hH hd hD
    (fun t => (P2_closed_of_restrictedMatch H x₀ R hHyp hmatch).2 (t + 1))

/-- With the corrected div-weight base fixed, restricted P2 matching turns the repaired div-weight
case split into the alpha-side successor family. -/
theorem divWeight_clearedBaseCases_iff_alphaWeight_successors_of_restrictedMatch_fixed
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (hd : 2 ≤ H.natDegree) {D : ℕ}
    (hD : D ≤ H.natDegree) (hmatch : RestrictedFaaDiBrunoMatch H x₀ R hHyp) :
    DivWeightLe_clearedBaseCases H x₀ R hHyp hH D ↔
      ∀ t, AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t :=
  divWeight_clearedBaseCases_iff_alphaWeight_successors_of_fixed_succLift
    H x₀ R hHyp hH hd hD
    (fun t => (P2_closed_of_restrictedMatch H x₀ R hHyp hmatch).2 (t + 1))

/-! ## Fixed-base successor direct P1 endpoint wrappers -/

/-- With the corrected base case fixed, route div-weight successor cases through the direct
cleared-base structured-invariant endpoint. -/
theorem βHenselStructuredWeightInvariant_unlocked_of_divWeight_successors_fixed
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (hd : 2 ≤ H.natDegree) {D : ℕ}
    (hD : D ≤ H.natDegree)
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hsucc : ∀ t, DivWeightLe_succ H x₀ R hHyp hH D t) (k : ℕ) :
    βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  βHenselStructuredWeightInvariant_unlocked_of_divWeight_clearedBaseCases
    H x₀ R hHyp hH hDH hDRx0 hdR2
    (DivWeightLe_clearedBaseCases.of_fixed_successors H x₀ R hHyp hH hd hD hsucc)
    k

/-- With the corrected base case fixed, route alpha-side successor cases through the direct
cleared-base structured-invariant endpoint using successor-order lift identities. -/
theorem βHenselStructuredWeightInvariant_unlocked_of_alphaWeight_successors_fixed_succLift
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (hd : 2 ≤ H.natDegree) {D : ℕ}
    (hD : D ≤ H.natDegree)
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hliftSucc : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp (t + 1))
        = αGenuine H x₀ R hHyp (t + 1)
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1))
    (hsucc : ∀ t, AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t) (k : ℕ) :
    βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  βHenselStructuredWeightInvariant_unlocked_of_alphaWeight_clearedBaseCases_succLift
    H x₀ R hHyp hH hDH hDRx0 hdR2 hliftSucc
    (AlphaGenuineRegularWeightLe_clearedBaseCases.of_fixed_successors
      H x₀ R hHyp hH hd hD hsucc)
    k

/-- With the corrected base case fixed, route alpha-side successor cases and full P2 vanishing
through the direct cleared-base structured-invariant endpoint. -/
theorem βHenselStructuredWeightInvariant_unlocked_of_fullVanishes_successors_fixed
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (hd : 2 ≤ H.natDegree) {D : ℕ}
    (hD : D ≤ H.natDegree)
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hvan : FaaDiBrunoFullSumVanishes H x₀ R hHyp)
    (hsucc : ∀ t, AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t) (k : ℕ) :
    βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  βHenselStructuredWeightInvariant_unlocked_of_fullVanishes_clearedBaseCases
    H x₀ R hHyp hH hDH hDRx0 hdR2 hvan
    (AlphaGenuineRegularWeightLe_clearedBaseCases.of_fixed_successors
      H x₀ R hHyp hH hd hD hsucc)
    k

/-- With the corrected base case fixed, route alpha-side successor cases and restricted P2 match
through the direct cleared-base structured-invariant endpoint. -/
theorem βHenselStructuredWeightInvariant_unlocked_of_restrictedMatch_successors_fixed
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (hd : 2 ≤ H.natDegree) {D : ℕ}
    (hD : D ≤ H.natDegree)
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hmatch : RestrictedFaaDiBrunoMatch H x₀ R hHyp)
    (hsucc : ∀ t, AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t) (k : ℕ) :
    βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  βHenselStructuredWeightInvariant_unlocked_of_restrictedMatch_clearedBaseCases
    H x₀ R hHyp hH hDH hDRx0 hdR2 hmatch
    (AlphaGenuineRegularWeightLe_clearedBaseCases.of_fixed_successors
      H x₀ R hHyp hH hd hD hsucc)
    k

/-- All-prefix structured invariant from fixed corrected base and div-weight successor cases. -/
theorem βHenselStructuredWeightInvariant_all_unlocked_of_divWeight_successors_fixed
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (hd : 2 ≤ H.natDegree) {D : ℕ}
    (hD : D ≤ H.natDegree)
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hsucc : ∀ t, DivWeightLe_succ H x₀ R hHyp hH D t) :
    ∀ k, βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  fun k =>
    βHenselStructuredWeightInvariant_unlocked_of_divWeight_successors_fixed
      H x₀ R hHyp hH hd hD hDH hDRx0 hdR2 hsucc k

/-- All-prefix structured invariant from fixed corrected base and alpha-side successor cases,
using successor-order lift identities. -/
theorem βHenselStructuredWeightInvariant_all_unlocked_of_alphaWeight_successors_fixed_succLift
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (hd : 2 ≤ H.natDegree) {D : ℕ}
    (hD : D ≤ H.natDegree)
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hliftSucc : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp (t + 1))
        = αGenuine H x₀ R hHyp (t + 1)
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1))
    (hsucc : ∀ t, AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t) :
    ∀ k, βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  fun k =>
    βHenselStructuredWeightInvariant_unlocked_of_alphaWeight_successors_fixed_succLift
      H x₀ R hHyp hH hd hD hDH hDRx0 hdR2 hliftSucc hsucc k

/-- All-prefix structured invariant from fixed corrected base, alpha-side successor cases, and
full P2 vanishing. -/
theorem βHenselStructuredWeightInvariant_all_unlocked_of_fullVanishes_successors_fixed
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (hd : 2 ≤ H.natDegree) {D : ℕ}
    (hD : D ≤ H.natDegree)
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hvan : FaaDiBrunoFullSumVanishes H x₀ R hHyp)
    (hsucc : ∀ t, AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t) :
    ∀ k, βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  fun k =>
    βHenselStructuredWeightInvariant_unlocked_of_fullVanishes_successors_fixed
      H x₀ R hHyp hH hd hD hDH hDRx0 hdR2 hvan hsucc k

/-- All-prefix structured invariant from fixed corrected base, alpha-side successor cases, and
restricted P2 match. -/
theorem βHenselStructuredWeightInvariant_all_unlocked_of_restrictedMatch_successors_fixed
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (hd : 2 ≤ H.natDegree) {D : ℕ}
    (hD : D ≤ H.natDegree)
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hmatch : RestrictedFaaDiBrunoMatch H x₀ R hHyp)
    (hsucc : ∀ t, AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t) :
    ∀ k, βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  fun k =>
    βHenselStructuredWeightInvariant_unlocked_of_restrictedMatch_successors_fixed
      H x₀ R hHyp hH hd hD hDH hDRx0 hdR2 hmatch hsucc k

/-- With the corrected base case fixed, route div-weight successor cases through the direct
cleared-base P1 endpoint. -/
theorem βHensel_weight_bound_unlocked_of_divWeight_successors_fixed
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (hd : 2 ≤ H.natDegree) {D : ℕ}
    (hD : D ≤ H.natDegree)
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hsucc : ∀ t, DivWeightLe_succ H x₀ R hHyp hH D t) (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_unlocked_of_divWeight_clearedBaseCases
    H x₀ R hHyp hH hDH hDRx0 hdR2 hdHR hW
    (DivWeightLe_clearedBaseCases.of_fixed_successors H x₀ R hHyp hH hd hD hsucc)
    t

/-- With the corrected base case fixed, route alpha-side successor cases through the direct
cleared-base P1 endpoint using successor-order lift identities. -/
theorem βHensel_weight_bound_unlocked_of_alphaWeight_successors_fixed_succLift
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (hd : 2 ≤ H.natDegree) {D : ℕ}
    (hD : D ≤ H.natDegree)
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hliftSucc : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp (t + 1))
        = αGenuine H x₀ R hHyp (t + 1)
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1))
    (hsucc : ∀ t, AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t) (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_unlocked_of_alphaWeight_clearedBaseCases_succLift
    H x₀ R hHyp hH hDH hDRx0 hdR2 hdHR hW hliftSucc
    (AlphaGenuineRegularWeightLe_clearedBaseCases.of_fixed_successors
      H x₀ R hHyp hH hd hD hsucc)
    t

/-- With the corrected base case fixed, route alpha-side successor cases and full P2 vanishing
through the direct cleared-base P1 endpoint. -/
theorem βHensel_weight_bound_unlocked_of_fullVanishes_successors_fixed
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (hd : 2 ≤ H.natDegree) {D : ℕ}
    (hD : D ≤ H.natDegree)
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hvan : FaaDiBrunoFullSumVanishes H x₀ R hHyp)
    (hsucc : ∀ t, AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t) (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_unlocked_of_fullVanishes_clearedBaseCases
    H x₀ R hHyp hH hDH hDRx0 hdR2 hdHR hW hvan
    (AlphaGenuineRegularWeightLe_clearedBaseCases.of_fixed_successors
      H x₀ R hHyp hH hd hD hsucc)
    t

/-- With the corrected base case fixed, route alpha-side successor cases and restricted P2 match
through the direct cleared-base P1 endpoint. -/
theorem βHensel_weight_bound_unlocked_of_restrictedMatch_successors_fixed
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (hd : 2 ≤ H.natDegree) {D : ℕ}
    (hD : D ≤ H.natDegree)
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hmatch : RestrictedFaaDiBrunoMatch H x₀ R hHyp)
    (hsucc : ∀ t, AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t) (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_unlocked_of_restrictedMatch_clearedBaseCases
    H x₀ R hHyp hH hDH hDRx0 hdR2 hdHR hW hmatch
    (AlphaGenuineRegularWeightLe_clearedBaseCases.of_fixed_successors
      H x₀ R hHyp hH hd hD hsucc)
    t

/-- All-prefix direct P1 weight bound from fixed corrected base and div-weight successor cases. -/
theorem βHensel_weight_bound_all_unlocked_of_divWeight_successors_fixed
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (hd : 2 ≤ H.natDegree) {D : ℕ}
    (hD : D ≤ H.natDegree)
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hsucc : ∀ t, DivWeightLe_succ H x₀ R hHyp hH D t) :
    ∀ t, weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  fun t =>
    βHensel_weight_bound_unlocked_of_divWeight_successors_fixed
      H x₀ R hHyp hH hd hD hDH hDRx0 hdR2 hdHR hW hsucc t

/-- All-prefix direct P1 weight bound from fixed corrected base and alpha-side successor cases,
using successor-order lift identities. -/
theorem βHensel_weight_bound_all_unlocked_of_alphaWeight_successors_fixed_succLift
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (hd : 2 ≤ H.natDegree) {D : ℕ}
    (hD : D ≤ H.natDegree)
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hliftSucc : ∀ t : ℕ,
      embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp (t + 1))
        = αGenuine H x₀ R hHyp (t + 1)
            * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
            * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1))
    (hsucc : ∀ t, AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t) :
    ∀ t, weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  fun t =>
    βHensel_weight_bound_unlocked_of_alphaWeight_successors_fixed_succLift
      H x₀ R hHyp hH hd hD hDH hDRx0 hdR2 hdHR hW hliftSucc hsucc t

/-- All-prefix direct P1 weight bound from fixed corrected base, alpha-side successor cases, and
full P2 vanishing. -/
theorem βHensel_weight_bound_all_unlocked_of_fullVanishes_successors_fixed
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (hd : 2 ≤ H.natDegree) {D : ℕ}
    (hD : D ≤ H.natDegree)
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hvan : FaaDiBrunoFullSumVanishes H x₀ R hHyp)
    (hsucc : ∀ t, AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t) :
    ∀ t, weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  fun t =>
    βHensel_weight_bound_unlocked_of_fullVanishes_successors_fixed
      H x₀ R hHyp hH hd hD hDH hDRx0 hdR2 hdHR hW hvan hsucc t

/-- All-prefix direct P1 weight bound from fixed corrected base, alpha-side successor cases, and
restricted P2 match. -/
theorem βHensel_weight_bound_all_unlocked_of_restrictedMatch_successors_fixed
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (hd : 2 ≤ H.natDegree) {D : ℕ}
    (hD : D ≤ H.natDegree)
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hmatch : RestrictedFaaDiBrunoMatch H x₀ R hHyp)
    (hsucc : ∀ t, AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t) :
    ∀ t, weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  fun t =>
    βHensel_weight_bound_unlocked_of_restrictedMatch_successors_fixed
      H x₀ R hHyp hH hd hD hDH hDRx0 hdR2 hdHR hW hmatch hsucc t

end P1ConditionalCleared

end BCIKS20.HenselNumerator

-- Axiom audit: every new wrapper stays on the inherited standard axiom surface.
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_unlocked_of_divWeight_clearedBaseCases
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_unlocked_of_alphaWeight_clearedBaseCases_succLift
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_unlocked_of_fullVanishes_clearedBaseCases
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_unlocked_of_restrictedMatch_clearedBaseCases
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_unlocked_of_divWeight_clearedBaseCases
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_unlocked_of_alphaWeight_clearedBaseCases_succLift
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_unlocked_of_fullVanishes_clearedBaseCases
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_unlocked_of_restrictedMatch_clearedBaseCases
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_all_unlocked_of_divWeight_clearedBaseCases
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_all_unlocked_of_alphaWeight_clearedBaseCases_succLift
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_all_unlocked_of_fullVanishes_clearedBaseCases
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_all_unlocked_of_restrictedMatch_clearedBaseCases
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_all_unlocked_of_divWeight_clearedBaseCases
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_all_unlocked_of_alphaWeight_clearedBaseCases_succLift
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_all_unlocked_of_fullVanishes_clearedBaseCases
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_all_unlocked_of_restrictedMatch_clearedBaseCases
#print axioms BCIKS20.HenselNumerator.alphaWeight_successors_iff_divWeight_successors_of_fullVanishes
#print axioms BCIKS20.HenselNumerator.alphaWeight_successors_iff_divWeight_successors_of_restrictedMatch
#print axioms BCIKS20.HenselNumerator.alphaWeight_iff_normalized_divWeight_cases_of_fullVanishes
#print axioms BCIKS20.HenselNumerator.alphaWeight_of_normalized_divWeight_cases_of_fullVanishes
#print axioms BCIKS20.HenselNumerator.alphaWeight_iff_normalized_divWeight_cases_of_restrictedMatch
#print axioms BCIKS20.HenselNumerator.alphaWeight_of_normalized_divWeight_cases_of_restrictedMatch
#print axioms BCIKS20.HenselNumerator.alphaWeight_iff_divWeight_of_fullVanishes
#print axioms BCIKS20.HenselNumerator.divWeight_of_alphaWeight_of_fullVanishes
#print axioms BCIKS20.HenselNumerator.alphaWeight_of_divWeight_of_fullVanishes
#print axioms BCIKS20.HenselNumerator.normalized_divWeight_cases_of_alphaWeight_of_fullVanishes
#print axioms BCIKS20.HenselNumerator.normalized_divWeight_zero_of_alphaWeight_of_fullVanishes
#print axioms BCIKS20.HenselNumerator.normalized_divWeight_succ_of_alphaWeight_of_fullVanishes
#print axioms BCIKS20.HenselNumerator.alphaWeight_iff_divWeight_of_restrictedMatch
#print axioms BCIKS20.HenselNumerator.divWeight_of_alphaWeight_of_restrictedMatch
#print axioms BCIKS20.HenselNumerator.alphaWeight_of_divWeight_of_restrictedMatch
#print axioms BCIKS20.HenselNumerator.normalized_divWeight_cases_of_alphaWeight_of_restrictedMatch
#print axioms BCIKS20.HenselNumerator.normalized_divWeight_zero_of_alphaWeight_of_restrictedMatch
#print axioms BCIKS20.HenselNumerator.normalized_divWeight_succ_of_alphaWeight_of_restrictedMatch
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_unlocked_of_normalized_divWeight_cases_of_fullVanishes
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_unlocked_of_normalized_divWeight_cases_of_restrictedMatch
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_all_unlocked_of_normalized_divWeight_cases_of_fullVanishes
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_all_unlocked_of_normalized_divWeight_cases_of_restrictedMatch
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_unlocked_of_normalized_divWeight_cases_of_fullVanishes
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_unlocked_of_normalized_divWeight_cases_of_restrictedMatch
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_all_unlocked_of_normalized_divWeight_cases_of_fullVanishes
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_all_unlocked_of_normalized_divWeight_cases_of_restrictedMatch
#print axioms BCIKS20.HenselNumerator.alphaWeight_clearedBaseCases_iff_divWeight_successors_of_fullVanishes_fixed
#print axioms BCIKS20.HenselNumerator.divWeight_clearedBaseCases_iff_alphaWeight_successors_of_fullVanishes_fixed
#print axioms BCIKS20.HenselNumerator.alphaWeight_clearedBaseCases_iff_divWeight_successors_of_restrictedMatch_fixed
#print axioms BCIKS20.HenselNumerator.divWeight_clearedBaseCases_iff_alphaWeight_successors_of_restrictedMatch_fixed
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_unlocked_of_divWeight_successors_fixed
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_unlocked_of_alphaWeight_successors_fixed_succLift
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_unlocked_of_fullVanishes_successors_fixed
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_unlocked_of_restrictedMatch_successors_fixed
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_all_unlocked_of_divWeight_successors_fixed
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_all_unlocked_of_alphaWeight_successors_fixed_succLift
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_all_unlocked_of_fullVanishes_successors_fixed
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_all_unlocked_of_restrictedMatch_successors_fixed
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_unlocked_of_divWeight_successors_fixed
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_unlocked_of_alphaWeight_successors_fixed_succLift
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_unlocked_of_fullVanishes_successors_fixed
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_unlocked_of_restrictedMatch_successors_fixed
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_all_unlocked_of_divWeight_successors_fixed
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_all_unlocked_of_alphaWeight_successors_fixed_succLift
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_all_unlocked_of_fullVanishes_successors_fixed
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_all_unlocked_of_restrictedMatch_successors_fixed
