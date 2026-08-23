/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P1ConditionalAll
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P1ConditionalCleared

/-!
# Cleared all-prefix structured-endpoint P1 wrappers

This companion keeps the corrected cleared-base conditional route wired into the older
all-prefix structured-invariant endpoint from `P1ConditionalAll.lean`, without growing that
near-cap file.  The declarations here are endpoint packaging: the repaired cleared-base
div/alpha case splits, fixed-base successor routes, and the P2 unlock hypotheses remain explicit.
-/

noncomputable section
set_option linter.style.longLine false

namespace BCIKS20.HenselNumerator

open Polynomial Polynomial.Bivariate
open BCIKS20AppendixA
open ProximityPrize.BCIKS20.GammaGenuine
open AlphaWeight

section P1ConditionalAllCleared

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-! ## Single-order structured-endpoint wrappers -/

/-- Route the repaired cleared-base div-weight all-prefix invariant through the
structured-invariant P1 endpoint. -/
theorem βHensel_weight_bound_of_structured_invariant_unlocked_of_divWeight_clearedBaseCases
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hRgraded : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdiv : DivWeightLe_clearedBaseCases H x₀ R hHyp hH D) (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_of_structured_invariant H x₀ R hHyp hH hDH hdR2
    hdHR hW hRgraded hDRx0
      (βHenselStructuredWeightInvariant_all_unlocked_of_divWeight_clearedBaseCases
        H x₀ R hHyp hH hDH hDRx0 hdR2 hdiv)
      t

/-- Route repaired alpha-side cleared-base cases through the all-prefix structured endpoint,
using only successor-order lift identities. -/
theorem βHensel_weight_bound_of_structured_invariant_unlocked_of_alphaWeight_clearedBaseCases_succLift
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
    (hα : AlphaGenuineRegularWeightLe_clearedBaseCases H x₀ R hHyp hH D) (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_of_structured_invariant H x₀ R hHyp hH hDH hdR2
    hdHR hW hRgraded hDRx0
      (βHenselStructuredWeightInvariant_all_unlocked_of_alphaWeight_clearedBaseCases_succLift
        H x₀ R hHyp hH hDH hDRx0 hdR2 hliftSucc hα)
      t

/-- Route the full-vanishing cleared-base conditional all-prefix invariant through the
structured-invariant P1 endpoint. -/
theorem βHensel_weight_bound_of_structured_invariant_unlocked_of_fullVanishes_clearedBaseCases
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hRgraded : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hvan : FaaDiBrunoFullSumVanishes H x₀ R hHyp)
    (hα : AlphaGenuineRegularWeightLe_clearedBaseCases H x₀ R hHyp hH D) (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_of_structured_invariant H x₀ R hHyp hH hDH hdR2
    hdHR hW hRgraded hDRx0
      (βHenselStructuredWeightInvariant_all_unlocked_of_fullVanishes_clearedBaseCases
        H x₀ R hHyp hH hDH hDRx0 hdR2 hvan hα)
      t

/-- Route the restricted-match cleared-base conditional all-prefix invariant through the
structured-invariant P1 endpoint. -/
theorem βHensel_weight_bound_of_structured_invariant_unlocked_of_restrictedMatch_clearedBaseCases
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hRgraded : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hmatch : RestrictedFaaDiBrunoMatch H x₀ R hHyp)
    (hα : AlphaGenuineRegularWeightLe_clearedBaseCases H x₀ R hHyp hH D) (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_of_structured_invariant H x₀ R hHyp hH hDH hdR2
    hdHR hW hRgraded hDRx0
      (βHenselStructuredWeightInvariant_all_unlocked_of_restrictedMatch_clearedBaseCases
        H x₀ R hHyp hH hDH hDRx0 hdR2 hmatch hα)
      t

/-! ## All-order structured-endpoint wrappers -/

/-- All-`t` P1 weight bound from repaired cleared-base div-weight cases through the
structured-invariant endpoint. -/
theorem βHensel_weight_bound_all_of_structured_invariant_unlocked_of_divWeight_clearedBaseCases
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hRgraded : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdiv : DivWeightLe_clearedBaseCases H x₀ R hHyp hH D) :
    ∀ t, weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  fun t =>
    βHensel_weight_bound_of_structured_invariant_unlocked_of_divWeight_clearedBaseCases
      H x₀ R hHyp hH hDH hdR2 hdHR hW hRgraded hDRx0 hdiv t

/-- All-`t` P1 weight bound from repaired alpha-side cleared-base cases through the
structured-invariant endpoint, using only successor-order lift identities. -/
theorem βHensel_weight_bound_all_of_structured_invariant_unlocked_of_alphaWeight_clearedBaseCases_succLift
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
    (hα : AlphaGenuineRegularWeightLe_clearedBaseCases H x₀ R hHyp hH D) :
    ∀ t, weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  fun t =>
    βHensel_weight_bound_of_structured_invariant_unlocked_of_alphaWeight_clearedBaseCases_succLift
      H x₀ R hHyp hH hDH hdR2 hdHR hW hRgraded hDRx0 hliftSucc hα t

/-- All-`t` P1 weight bound from full P2 vanishing and repaired alpha-side cleared-base cases
through the structured-invariant endpoint. -/
theorem βHensel_weight_bound_all_of_structured_invariant_unlocked_of_fullVanishes_clearedBaseCases
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hRgraded : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hvan : FaaDiBrunoFullSumVanishes H x₀ R hHyp)
    (hα : AlphaGenuineRegularWeightLe_clearedBaseCases H x₀ R hHyp hH D) :
    ∀ t, weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  fun t =>
    βHensel_weight_bound_of_structured_invariant_unlocked_of_fullVanishes_clearedBaseCases
      H x₀ R hHyp hH hDH hdR2 hdHR hW hRgraded hDRx0 hvan hα t

/-- All-`t` P1 weight bound from restricted P2 match and repaired alpha-side cleared-base cases
through the structured-invariant endpoint. -/
theorem βHensel_weight_bound_all_of_structured_invariant_unlocked_of_restrictedMatch_clearedBaseCases
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hRgraded : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hmatch : RestrictedFaaDiBrunoMatch H x₀ R hHyp)
    (hα : AlphaGenuineRegularWeightLe_clearedBaseCases H x₀ R hHyp hH D) :
    ∀ t, weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  fun t =>
    βHensel_weight_bound_of_structured_invariant_unlocked_of_restrictedMatch_clearedBaseCases
      H x₀ R hHyp hH hDH hdR2 hdHR hW hRgraded hDRx0 hmatch hα t

/-! ## Normalized-divisibility structured-endpoint wrappers -/

/-- Route normalized divisibility targets and full P2 vanishing through the structured-invariant
P1 endpoint. -/
theorem βHensel_weight_bound_of_structured_invariant_unlocked_of_normalized_divWeight_cases_of_fullVanishes
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hRgraded : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
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
  βHensel_weight_bound_of_structured_invariant H x₀ R hHyp hH hDH hdR2
    hdHR hW hRgraded hDRx0
      (βHenselStructuredWeightInvariant_all_unlocked_of_normalized_divWeight_cases_of_fullVanishes
        H x₀ R hHyp hH hDH hDRx0 hdR2 hvan h0 hsucc)
      t

/-- Route normalized divisibility targets and restricted P2 matching through the
structured-invariant P1 endpoint. -/
theorem βHensel_weight_bound_of_structured_invariant_unlocked_of_normalized_divWeight_cases_of_restrictedMatch
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hRgraded : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
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
  βHensel_weight_bound_of_structured_invariant H x₀ R hHyp hH hDH hdR2
    hdHR hW hRgraded hDRx0
      (βHenselStructuredWeightInvariant_all_unlocked_of_normalized_divWeight_cases_of_restrictedMatch
        H x₀ R hHyp hH hDH hDRx0 hdR2 hmatch h0 hsucc)
      t

/-- All-`t` P1 weight bound from full P2 vanishing and normalized divisibility targets through
the structured-invariant endpoint. -/
theorem βHensel_weight_bound_all_of_structured_invariant_unlocked_of_normalized_divWeight_cases_of_fullVanishes
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hRgraded : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
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
    βHensel_weight_bound_of_structured_invariant_unlocked_of_normalized_divWeight_cases_of_fullVanishes
      H x₀ R hHyp hH hDH hdR2 hdHR hW hRgraded hDRx0 hvan h0 hsucc t

/-- All-`t` P1 weight bound from restricted P2 matching and normalized divisibility targets
through the structured-invariant endpoint. -/
theorem βHensel_weight_bound_all_of_structured_invariant_unlocked_of_normalized_divWeight_cases_of_restrictedMatch
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hRgraded : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
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
    βHensel_weight_bound_of_structured_invariant_unlocked_of_normalized_divWeight_cases_of_restrictedMatch
      H x₀ R hHyp hH hDH hdR2 hdHR hW hRgraded hDRx0 hmatch h0 hsucc t

/-! ## Fixed-base successor endpoint wrappers -/

/-- With the corrected base case fixed, route div-weight successor cases through the
structured-invariant P1 endpoint. -/
theorem βHensel_weight_bound_of_structured_invariant_unlocked_of_divWeight_successors_fixed
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (hd : 2 ≤ H.natDegree) {D : ℕ}
    (hD : D ≤ H.natDegree)
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hRgraded : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hsucc : ∀ t, DivWeightLe_succ H x₀ R hHyp hH D t) (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_of_structured_invariant_unlocked_of_divWeight_clearedBaseCases
    H x₀ R hHyp hH hDH hdR2 hdHR hW hRgraded hDRx0
    (DivWeightLe_clearedBaseCases.of_fixed_successors H x₀ R hHyp hH hd hD hsucc) t

/-- With the corrected base case fixed, route alpha-side successor cases through the
structured-invariant P1 endpoint using successor-order lift identities. -/
theorem βHensel_weight_bound_of_structured_invariant_unlocked_of_alphaWeight_successors_fixed_succLift
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (hd : 2 ≤ H.natDegree) {D : ℕ}
    (hD : D ≤ H.natDegree)
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
    (hsucc : ∀ t, AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t) (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_of_structured_invariant_unlocked_of_alphaWeight_clearedBaseCases_succLift
    H x₀ R hHyp hH hDH hdR2 hdHR hW hRgraded hDRx0 hliftSucc
    (AlphaGenuineRegularWeightLe_clearedBaseCases.of_fixed_successors
      H x₀ R hHyp hH hd hD hsucc)
    t

/-- With the corrected base case fixed, route alpha-side successor cases and full P2 vanishing
through the structured-invariant P1 endpoint. -/
theorem βHensel_weight_bound_of_structured_invariant_unlocked_of_fullVanishes_successors_fixed
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (hd : 2 ≤ H.natDegree) {D : ℕ}
    (hD : D ≤ H.natDegree)
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hRgraded : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hvan : FaaDiBrunoFullSumVanishes H x₀ R hHyp)
    (hsucc : ∀ t, AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t) (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_of_structured_invariant_unlocked_of_fullVanishes_clearedBaseCases
    H x₀ R hHyp hH hDH hdR2 hdHR hW hRgraded hDRx0 hvan
    (AlphaGenuineRegularWeightLe_clearedBaseCases.of_fixed_successors
      H x₀ R hHyp hH hd hD hsucc)
    t

/-- With the corrected base case fixed, route alpha-side successor cases and restricted P2 match
through the structured-invariant P1 endpoint. -/
theorem βHensel_weight_bound_of_structured_invariant_unlocked_of_restrictedMatch_successors_fixed
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (hd : 2 ≤ H.natDegree) {D : ℕ}
    (hD : D ≤ H.natDegree)
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hRgraded : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hmatch : RestrictedFaaDiBrunoMatch H x₀ R hHyp)
    (hsucc : ∀ t, AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t) (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_of_structured_invariant_unlocked_of_restrictedMatch_clearedBaseCases
    H x₀ R hHyp hH hDH hdR2 hdHR hW hRgraded hDRx0 hmatch
    (AlphaGenuineRegularWeightLe_clearedBaseCases.of_fixed_successors
      H x₀ R hHyp hH hd hD hsucc)
    t

/-- All-`t` P1 weight bound from fixed corrected base and div-weight successor cases. -/
theorem βHensel_weight_bound_all_of_structured_invariant_unlocked_of_divWeight_successors_fixed
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (hd : 2 ≤ H.natDegree) {D : ℕ}
    (hD : D ≤ H.natDegree)
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hRgraded : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hsucc : ∀ t, DivWeightLe_succ H x₀ R hHyp hH D t) :
    ∀ t, weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  fun t =>
    βHensel_weight_bound_of_structured_invariant_unlocked_of_divWeight_successors_fixed
      H x₀ R hHyp hH hd hD hDH hdR2 hdHR hW hRgraded hDRx0 hsucc t

/-- All-`t` P1 weight bound from fixed corrected base and alpha-side successor cases, using
successor-order lift identities. -/
theorem βHensel_weight_bound_all_of_structured_invariant_unlocked_of_alphaWeight_successors_fixed_succLift
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (hd : 2 ≤ H.natDegree) {D : ℕ}
    (hD : D ≤ H.natDegree)
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
    (hsucc : ∀ t, AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t) :
    ∀ t, weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  fun t =>
    βHensel_weight_bound_of_structured_invariant_unlocked_of_alphaWeight_successors_fixed_succLift
      H x₀ R hHyp hH hd hD hDH hdR2 hdHR hW hRgraded hDRx0 hliftSucc hsucc t

/-- All-`t` P1 weight bound from fixed corrected base, alpha-side successor cases, and full P2
vanishing. -/
theorem βHensel_weight_bound_all_of_structured_invariant_unlocked_of_fullVanishes_successors_fixed
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (hd : 2 ≤ H.natDegree) {D : ℕ}
    (hD : D ≤ H.natDegree)
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hRgraded : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hvan : FaaDiBrunoFullSumVanishes H x₀ R hHyp)
    (hsucc : ∀ t, AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t) :
    ∀ t, weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  fun t =>
    βHensel_weight_bound_of_structured_invariant_unlocked_of_fullVanishes_successors_fixed
      H x₀ R hHyp hH hd hD hDH hdR2 hdHR hW hRgraded hDRx0 hvan hsucc t

/-- All-`t` P1 weight bound from fixed corrected base, alpha-side successor cases, and restricted
P2 match. -/
theorem βHensel_weight_bound_all_of_structured_invariant_unlocked_of_restrictedMatch_successors_fixed
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (hd : 2 ≤ H.natDegree) {D : ℕ}
    (hD : D ≤ H.natDegree)
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hRgraded : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hmatch : RestrictedFaaDiBrunoMatch H x₀ R hHyp)
    (hsucc : ∀ t, AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t) :
    ∀ t, weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  fun t =>
    βHensel_weight_bound_of_structured_invariant_unlocked_of_restrictedMatch_successors_fixed
      H x₀ R hHyp hH hd hD hDH hdR2 hdHR hW hRgraded hDRx0 hmatch hsucc t

end P1ConditionalAllCleared

end BCIKS20.HenselNumerator

-- Axiom audit: the new endpoint wrappers stay on the inherited standard axiom surface.
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_of_structured_invariant_unlocked_of_divWeight_clearedBaseCases
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_of_structured_invariant_unlocked_of_alphaWeight_clearedBaseCases_succLift
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_of_structured_invariant_unlocked_of_fullVanishes_clearedBaseCases
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_of_structured_invariant_unlocked_of_restrictedMatch_clearedBaseCases
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_all_of_structured_invariant_unlocked_of_divWeight_clearedBaseCases
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_all_of_structured_invariant_unlocked_of_alphaWeight_clearedBaseCases_succLift
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_all_of_structured_invariant_unlocked_of_fullVanishes_clearedBaseCases
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_all_of_structured_invariant_unlocked_of_restrictedMatch_clearedBaseCases
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_of_structured_invariant_unlocked_of_normalized_divWeight_cases_of_fullVanishes
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_of_structured_invariant_unlocked_of_normalized_divWeight_cases_of_restrictedMatch
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_all_of_structured_invariant_unlocked_of_normalized_divWeight_cases_of_fullVanishes
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_all_of_structured_invariant_unlocked_of_normalized_divWeight_cases_of_restrictedMatch
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_unlocked_of_divWeight_successors_fixed
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_unlocked_of_alphaWeight_successors_fixed_succLift
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_unlocked_of_fullVanishes_successors_fixed
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_unlocked_of_restrictedMatch_successors_fixed
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_all_unlocked_of_divWeight_successors_fixed
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_all_unlocked_of_alphaWeight_successors_fixed_succLift
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_all_unlocked_of_fullVanishes_successors_fixed
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_all_unlocked_of_restrictedMatch_successors_fixed
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_of_structured_invariant_unlocked_of_divWeight_successors_fixed
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_of_structured_invariant_unlocked_of_alphaWeight_successors_fixed_succLift
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_of_structured_invariant_unlocked_of_fullVanishes_successors_fixed
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_of_structured_invariant_unlocked_of_restrictedMatch_successors_fixed
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_all_of_structured_invariant_unlocked_of_divWeight_successors_fixed
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_all_of_structured_invariant_unlocked_of_alphaWeight_successors_fixed_succLift
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_all_of_structured_invariant_unlocked_of_fullVanishes_successors_fixed
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_all_of_structured_invariant_unlocked_of_restrictedMatch_successors_fixed
