/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P1ConditionalAllCleared
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2MonicWfreeConsumers
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2MonicWfreeRange

/-!
# Monic W-free P2 routes into cleared P1 endpoints

This companion connects the monic W-free P2 target from `P2MonicWfreeConsumers.lean` to the
cleared #138 P1 endpoint wrappers.  The declarations are thin aliases over the existing
`RestrictedFaaDiBrunoMatch` and cleared-base P1 infrastructure, with the monic W-free hypothesis
repacked by `RestrictedFaaDiBrunoMatch.of_WfreeMatch`.

No W-free equation, successor witness, or genuine P1 invariant is proved here.
-/

noncomputable section
set_option linter.style.longLine false

open Polynomial Polynomial.Bivariate
open BCIKS20AppendixA
open ProximityPrize.BCIKS20.GammaGenuine
open BCIKS20.HenselNumerator.AlphaWeight

namespace BCIKS20.HenselNumerator

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

theorem alphaWeight_successors_iff_divWeight_successors_of_WfreeMatch
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (D : ℕ)
    (hlc : H.leadingCoeff = 1)
    (hWfree : RestrictedFaaDiBrunoWfreeMatch H x₀ R hHyp) :
    (∀ t, AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t) ↔
      ∀ t, DivWeightLe_succ H x₀ R hHyp hH D t :=
  alphaWeight_successors_iff_divWeight_successors_of_restrictedMatch
    H x₀ R hHyp hH D
    (RestrictedFaaDiBrunoMatch.of_WfreeMatch H x₀ R hHyp hlc hWfree)

theorem alphaWeight_clearedBaseCases_iff_divWeight_successors_of_WfreeMatch_fixed
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (hd : 2 ≤ H.natDegree) {D : ℕ}
    (hD : D ≤ H.natDegree)
    (hlc : H.leadingCoeff = 1)
    (hWfree : RestrictedFaaDiBrunoWfreeMatch H x₀ R hHyp) :
    AlphaGenuineRegularWeightLe_clearedBaseCases H x₀ R hHyp hH D ↔
      ∀ t, DivWeightLe_succ H x₀ R hHyp hH D t :=
  alphaWeight_clearedBaseCases_iff_divWeight_successors_of_restrictedMatch_fixed
    H x₀ R hHyp hH hd hD
    (RestrictedFaaDiBrunoMatch.of_WfreeMatch H x₀ R hHyp hlc hWfree)

theorem divWeight_clearedBaseCases_iff_alphaWeight_successors_of_WfreeMatch_fixed
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (hd : 2 ≤ H.natDegree) {D : ℕ}
    (hD : D ≤ H.natDegree)
    (hlc : H.leadingCoeff = 1)
    (hWfree : RestrictedFaaDiBrunoWfreeMatch H x₀ R hHyp) :
    DivWeightLe_clearedBaseCases H x₀ R hHyp hH D ↔
      ∀ t, AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t :=
  divWeight_clearedBaseCases_iff_alphaWeight_successors_of_restrictedMatch_fixed
    H x₀ R hHyp hH hd hD
    (RestrictedFaaDiBrunoMatch.of_WfreeMatch H x₀ R hHyp hlc hWfree)

theorem alphaWeight_clearedBaseCases_iff_divWeight_successors_of_rangeWfreeMatch_fixed
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (hd : 2 ≤ H.natDegree) {D : ℕ}
    (hD : D ≤ H.natDegree)
    (hlc : H.leadingCoeff = 1)
    (hrange : RestrictedFaaDiBrunoRangeWfreeMatch H x₀ R hHyp) :
    AlphaGenuineRegularWeightLe_clearedBaseCases H x₀ R hHyp hH D ↔
      ∀ t, DivWeightLe_succ H x₀ R hHyp hH D t :=
  alphaWeight_clearedBaseCases_iff_divWeight_successors_of_WfreeMatch_fixed
    H x₀ R hHyp hH hd hD hlc
    (RestrictedFaaDiBrunoWfreeMatch.of_rangeWfreeMatch H x₀ R hHyp hrange)

theorem divWeight_clearedBaseCases_iff_alphaWeight_successors_of_rangeWfreeMatch_fixed
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (hd : 2 ≤ H.natDegree) {D : ℕ}
    (hD : D ≤ H.natDegree)
    (hlc : H.leadingCoeff = 1)
    (hrange : RestrictedFaaDiBrunoRangeWfreeMatch H x₀ R hHyp) :
    DivWeightLe_clearedBaseCases H x₀ R hHyp hH D ↔
      ∀ t, AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t :=
  divWeight_clearedBaseCases_iff_alphaWeight_successors_of_WfreeMatch_fixed
    H x₀ R hHyp hH hd hD hlc
    (RestrictedFaaDiBrunoWfreeMatch.of_rangeWfreeMatch H x₀ R hHyp hrange)

theorem alphaWeight_iff_normalized_divWeight_cases_of_WfreeMatch
    (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ)
    (hlc : H.leadingCoeff = 1)
    (hWfree : RestrictedFaaDiBrunoWfreeMatch H x₀ R hHyp) :
    AlphaGenuineRegularWeightLe H x₀ R hHyp hH D ↔
      (∃ a : 𝒪 H,
        βHensel H x₀ R hHyp 0 = a * W𝒪 H ∧
          weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1) ∧
        ∀ t : ℕ, ∃ a : 𝒪 H,
          βHensel H x₀ R hHyp (t + 1)
            = a * (W𝒪 H) ^ (t + 2) * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t + 1) ∧
            weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1 :=
  alphaWeight_iff_normalized_divWeight_cases_of_restrictedMatch
    H x₀ R hHyp hH D
    (RestrictedFaaDiBrunoMatch.of_WfreeMatch H x₀ R hHyp hlc hWfree)

theorem alphaWeight_of_normalized_divWeight_cases_of_WfreeMatch
    (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ)
    (hlc : H.leadingCoeff = 1)
    (hWfree : RestrictedFaaDiBrunoWfreeMatch H x₀ R hHyp)
    (h0 : ∃ a : 𝒪 H,
      βHensel H x₀ R hHyp 0 = a * W𝒪 H ∧
        weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1)
    (hsucc : ∀ t : ℕ, ∃ a : 𝒪 H,
      βHensel H x₀ R hHyp (t + 1)
        = a * (W𝒪 H) ^ (t + 2) * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t + 1) ∧
        weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1) :
    AlphaGenuineRegularWeightLe H x₀ R hHyp hH D :=
  (alphaWeight_iff_normalized_divWeight_cases_of_WfreeMatch
    H x₀ R hHyp hH D hlc hWfree).2 ⟨h0, hsucc⟩

theorem alphaWeight_iff_normalized_divWeight_cases_of_rangeWfreeMatch
    (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ)
    (hlc : H.leadingCoeff = 1)
    (hrange : RestrictedFaaDiBrunoRangeWfreeMatch H x₀ R hHyp) :
    AlphaGenuineRegularWeightLe H x₀ R hHyp hH D ↔
      (∃ a : 𝒪 H,
        βHensel H x₀ R hHyp 0 = a * W𝒪 H ∧
          weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1) ∧
        ∀ t : ℕ, ∃ a : 𝒪 H,
          βHensel H x₀ R hHyp (t + 1)
            = a * (W𝒪 H) ^ (t + 2) * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t + 1) ∧
            weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1 :=
  alphaWeight_iff_normalized_divWeight_cases_of_WfreeMatch
    H x₀ R hHyp hH D hlc
    (RestrictedFaaDiBrunoWfreeMatch.of_rangeWfreeMatch H x₀ R hHyp hrange)

theorem alphaWeight_of_normalized_divWeight_cases_of_rangeWfreeMatch
    (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ)
    (hlc : H.leadingCoeff = 1)
    (hrange : RestrictedFaaDiBrunoRangeWfreeMatch H x₀ R hHyp)
    (h0 : ∃ a : 𝒪 H,
      βHensel H x₀ R hHyp 0 = a * W𝒪 H ∧
        weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1)
    (hsucc : ∀ t : ℕ, ∃ a : 𝒪 H,
      βHensel H x₀ R hHyp (t + 1)
        = a * (W𝒪 H) ^ (t + 2) * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t + 1) ∧
        weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1) :
    AlphaGenuineRegularWeightLe H x₀ R hHyp hH D :=
  (alphaWeight_iff_normalized_divWeight_cases_of_rangeWfreeMatch
    H x₀ R hHyp hH D hlc hrange).2 ⟨h0, hsucc⟩

theorem alphaWeight_iff_divWeight_of_WfreeMatch
    (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ)
    (hlc : H.leadingCoeff = 1)
    (hWfree : RestrictedFaaDiBrunoWfreeMatch H x₀ R hHyp) :
    AlphaGenuineRegularWeightLe H x₀ R hHyp hH D ↔
      DivWeightLe H x₀ R hHyp hH D :=
  AlphaWeight.alphaWeight_iff_divWeight_of_succLift H x₀ R hHyp hH D
    (fun t => βHensel_lift_identity_of_WfreeMatch H x₀ R hHyp hlc hWfree (t + 1))

theorem divWeight_of_alphaWeight_of_WfreeMatch
    (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ)
    (hlc : H.leadingCoeff = 1)
    (hWfree : RestrictedFaaDiBrunoWfreeMatch H x₀ R hHyp)
    (hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D) :
    DivWeightLe H x₀ R hHyp hH D :=
  (alphaWeight_iff_divWeight_of_WfreeMatch
    H x₀ R hHyp hH D hlc hWfree).1 hα

theorem alphaWeight_of_divWeight_of_WfreeMatch
    (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ)
    (hlc : H.leadingCoeff = 1)
    (hWfree : RestrictedFaaDiBrunoWfreeMatch H x₀ R hHyp)
    (hdiv : DivWeightLe H x₀ R hHyp hH D) :
    AlphaGenuineRegularWeightLe H x₀ R hHyp hH D :=
  (alphaWeight_iff_divWeight_of_WfreeMatch
    H x₀ R hHyp hH D hlc hWfree).2 hdiv

theorem alphaWeight_iff_divWeight_of_rangeWfreeMatch
    (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ)
    (hlc : H.leadingCoeff = 1)
    (hrange : RestrictedFaaDiBrunoRangeWfreeMatch H x₀ R hHyp) :
    AlphaGenuineRegularWeightLe H x₀ R hHyp hH D ↔
      DivWeightLe H x₀ R hHyp hH D :=
  alphaWeight_iff_divWeight_of_WfreeMatch H x₀ R hHyp hH D hlc
    (RestrictedFaaDiBrunoWfreeMatch.of_rangeWfreeMatch H x₀ R hHyp hrange)

theorem divWeight_of_alphaWeight_of_rangeWfreeMatch
    (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ)
    (hlc : H.leadingCoeff = 1)
    (hrange : RestrictedFaaDiBrunoRangeWfreeMatch H x₀ R hHyp)
    (hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D) :
    DivWeightLe H x₀ R hHyp hH D :=
  (alphaWeight_iff_divWeight_of_rangeWfreeMatch
    H x₀ R hHyp hH D hlc hrange).1 hα

theorem alphaWeight_of_divWeight_of_rangeWfreeMatch
    (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ)
    (hlc : H.leadingCoeff = 1)
    (hrange : RestrictedFaaDiBrunoRangeWfreeMatch H x₀ R hHyp)
    (hdiv : DivWeightLe H x₀ R hHyp hH D) :
    AlphaGenuineRegularWeightLe H x₀ R hHyp hH D :=
  (alphaWeight_iff_divWeight_of_rangeWfreeMatch
    H x₀ R hHyp hH D hlc hrange).2 hdiv

theorem normalized_divWeight_cases_of_alphaWeight_of_WfreeMatch
    (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ)
    (hlc : H.leadingCoeff = 1)
    (hWfree : RestrictedFaaDiBrunoWfreeMatch H x₀ R hHyp)
    (hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D) :
      (∃ a : 𝒪 H,
        βHensel H x₀ R hHyp 0 = a * W𝒪 H ∧
          weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1) ∧
        ∀ t : ℕ, ∃ a : 𝒪 H,
          βHensel H x₀ R hHyp (t + 1)
            = a * (W𝒪 H) ^ (t + 2) * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t + 1) ∧
            weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1 :=
  (alphaWeight_iff_normalized_divWeight_cases_of_WfreeMatch
    H x₀ R hHyp hH D hlc hWfree).1 hα

theorem normalized_divWeight_zero_of_alphaWeight_of_WfreeMatch
    (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ)
    (hlc : H.leadingCoeff = 1)
    (hWfree : RestrictedFaaDiBrunoWfreeMatch H x₀ R hHyp)
    (hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D) :
    ∃ a : 𝒪 H,
      βHensel H x₀ R hHyp 0 = a * W𝒪 H ∧
        weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1 :=
  (normalized_divWeight_cases_of_alphaWeight_of_WfreeMatch
    H x₀ R hHyp hH D hlc hWfree hα).1

theorem normalized_divWeight_succ_of_alphaWeight_of_WfreeMatch
    (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D t : ℕ)
    (hlc : H.leadingCoeff = 1)
    (hWfree : RestrictedFaaDiBrunoWfreeMatch H x₀ R hHyp)
    (hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D) :
    ∃ a : 𝒪 H,
      βHensel H x₀ R hHyp (t + 1)
        = a * (W𝒪 H) ^ (t + 2) * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t + 1) ∧
        weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1 :=
  (normalized_divWeight_cases_of_alphaWeight_of_WfreeMatch
    H x₀ R hHyp hH D hlc hWfree hα).2 t

theorem normalized_divWeight_cases_of_alphaWeight_of_rangeWfreeMatch
    (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ)
    (hlc : H.leadingCoeff = 1)
    (hrange : RestrictedFaaDiBrunoRangeWfreeMatch H x₀ R hHyp)
    (hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D) :
      (∃ a : 𝒪 H,
        βHensel H x₀ R hHyp 0 = a * W𝒪 H ∧
          weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1) ∧
        ∀ t : ℕ, ∃ a : 𝒪 H,
          βHensel H x₀ R hHyp (t + 1)
            = a * (W𝒪 H) ^ (t + 2) * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t + 1) ∧
            weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1 :=
  (alphaWeight_iff_normalized_divWeight_cases_of_rangeWfreeMatch
    H x₀ R hHyp hH D hlc hrange).1 hα

theorem normalized_divWeight_zero_of_alphaWeight_of_rangeWfreeMatch
    (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ)
    (hlc : H.leadingCoeff = 1)
    (hrange : RestrictedFaaDiBrunoRangeWfreeMatch H x₀ R hHyp)
    (hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D) :
    ∃ a : 𝒪 H,
      βHensel H x₀ R hHyp 0 = a * W𝒪 H ∧
        weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1 :=
  (normalized_divWeight_cases_of_alphaWeight_of_rangeWfreeMatch
    H x₀ R hHyp hH D hlc hrange hα).1

theorem normalized_divWeight_succ_of_alphaWeight_of_rangeWfreeMatch
    (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D t : ℕ)
    (hlc : H.leadingCoeff = 1)
    (hrange : RestrictedFaaDiBrunoRangeWfreeMatch H x₀ R hHyp)
    (hα : AlphaGenuineRegularWeightLe H x₀ R hHyp hH D) :
    ∃ a : 𝒪 H,
      βHensel H x₀ R hHyp (t + 1)
        = a * (W𝒪 H) ^ (t + 2) * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t + 1) ∧
        weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1 :=
  (normalized_divWeight_cases_of_alphaWeight_of_rangeWfreeMatch
    H x₀ R hHyp hH D hlc hrange hα).2 t

theorem βHenselStructuredWeightInvariant_unlocked_of_WfreeMatch_clearedBaseCases
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hlc : H.leadingCoeff = 1)
    (hWfree : RestrictedFaaDiBrunoWfreeMatch H x₀ R hHyp)
    (hα : AlphaGenuineRegularWeightLe_clearedBaseCases H x₀ R hHyp hH D) (k : ℕ) :
    βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  βHenselStructuredWeightInvariant_unlocked_of_restrictedMatch_clearedBaseCases
    H x₀ R hHyp hH hDH hDRx0 hdR2
    (RestrictedFaaDiBrunoMatch.of_WfreeMatch H x₀ R hHyp hlc hWfree)
    hα k

theorem βHenselStructuredWeightInvariant_all_unlocked_of_WfreeMatch_clearedBaseCases
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hlc : H.leadingCoeff = 1)
    (hWfree : RestrictedFaaDiBrunoWfreeMatch H x₀ R hHyp)
    (hα : AlphaGenuineRegularWeightLe_clearedBaseCases H x₀ R hHyp hH D) :
    ∀ k, βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  fun k =>
    βHenselStructuredWeightInvariant_unlocked_of_WfreeMatch_clearedBaseCases
      H x₀ R hHyp hH hDH hDRx0 hdR2 hlc hWfree hα k

theorem βHensel_weight_bound_unlocked_of_WfreeMatch_clearedBaseCases
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hlc : H.leadingCoeff = 1)
    (hWfree : RestrictedFaaDiBrunoWfreeMatch H x₀ R hHyp)
    (hα : AlphaGenuineRegularWeightLe_clearedBaseCases H x₀ R hHyp hH D) (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_unlocked_of_restrictedMatch_clearedBaseCases
    H x₀ R hHyp hH hDH hDRx0 hdR2 hdHR hW
    (RestrictedFaaDiBrunoMatch.of_WfreeMatch H x₀ R hHyp hlc hWfree)
    hα t

theorem βHensel_weight_bound_all_unlocked_of_WfreeMatch_clearedBaseCases
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hlc : H.leadingCoeff = 1)
    (hWfree : RestrictedFaaDiBrunoWfreeMatch H x₀ R hHyp)
    (hα : AlphaGenuineRegularWeightLe_clearedBaseCases H x₀ R hHyp hH D) :
    ∀ t, weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  fun t =>
    βHensel_weight_bound_unlocked_of_WfreeMatch_clearedBaseCases
      H x₀ R hHyp hH hDH hDRx0 hdR2 hdHR hW hlc hWfree hα t

theorem βHensel_weight_bound_of_structured_invariant_unlocked_of_WfreeMatch_clearedBaseCases
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hRgraded : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hlc : H.leadingCoeff = 1)
    (hWfree : RestrictedFaaDiBrunoWfreeMatch H x₀ R hHyp)
    (hα : AlphaGenuineRegularWeightLe_clearedBaseCases H x₀ R hHyp hH D) (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_of_structured_invariant_unlocked_of_restrictedMatch_clearedBaseCases
    H x₀ R hHyp hH hDH hdR2 hdHR hW hRgraded hDRx0
    (RestrictedFaaDiBrunoMatch.of_WfreeMatch H x₀ R hHyp hlc hWfree)
    hα t

theorem βHensel_weight_bound_all_of_structured_invariant_unlocked_of_WfreeMatch_clearedBaseCases
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hRgraded : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hlc : H.leadingCoeff = 1)
    (hWfree : RestrictedFaaDiBrunoWfreeMatch H x₀ R hHyp)
    (hα : AlphaGenuineRegularWeightLe_clearedBaseCases H x₀ R hHyp hH D) :
    ∀ t, weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  fun t =>
    βHensel_weight_bound_of_structured_invariant_unlocked_of_WfreeMatch_clearedBaseCases
      H x₀ R hHyp hH hDH hdR2 hdHR hW hRgraded hDRx0 hlc hWfree hα t

theorem βHenselStructuredWeightInvariant_unlocked_of_rangeWfreeMatch_clearedBaseCases
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hlc : H.leadingCoeff = 1)
    (hrange : RestrictedFaaDiBrunoRangeWfreeMatch H x₀ R hHyp)
    (hα : AlphaGenuineRegularWeightLe_clearedBaseCases H x₀ R hHyp hH D) (k : ℕ) :
    βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  βHenselStructuredWeightInvariant_unlocked_of_WfreeMatch_clearedBaseCases
    H x₀ R hHyp hH hDH hDRx0 hdR2 hlc
    (RestrictedFaaDiBrunoWfreeMatch.of_rangeWfreeMatch H x₀ R hHyp hrange)
    hα k

theorem βHenselStructuredWeightInvariant_all_unlocked_of_rangeWfreeMatch_clearedBaseCases
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hlc : H.leadingCoeff = 1)
    (hrange : RestrictedFaaDiBrunoRangeWfreeMatch H x₀ R hHyp)
    (hα : AlphaGenuineRegularWeightLe_clearedBaseCases H x₀ R hHyp hH D) :
    ∀ k, βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  fun k =>
    βHenselStructuredWeightInvariant_unlocked_of_rangeWfreeMatch_clearedBaseCases
      H x₀ R hHyp hH hDH hDRx0 hdR2 hlc hrange hα k

theorem βHensel_weight_bound_unlocked_of_rangeWfreeMatch_clearedBaseCases
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hlc : H.leadingCoeff = 1)
    (hrange : RestrictedFaaDiBrunoRangeWfreeMatch H x₀ R hHyp)
    (hα : AlphaGenuineRegularWeightLe_clearedBaseCases H x₀ R hHyp hH D) (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_unlocked_of_WfreeMatch_clearedBaseCases
    H x₀ R hHyp hH hDH hDRx0 hdR2 hdHR hW hlc
    (RestrictedFaaDiBrunoWfreeMatch.of_rangeWfreeMatch H x₀ R hHyp hrange)
    hα t

theorem βHensel_weight_bound_all_unlocked_of_rangeWfreeMatch_clearedBaseCases
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hlc : H.leadingCoeff = 1)
    (hrange : RestrictedFaaDiBrunoRangeWfreeMatch H x₀ R hHyp)
    (hα : AlphaGenuineRegularWeightLe_clearedBaseCases H x₀ R hHyp hH D) :
    ∀ t, weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  fun t =>
    βHensel_weight_bound_unlocked_of_rangeWfreeMatch_clearedBaseCases
      H x₀ R hHyp hH hDH hDRx0 hdR2 hdHR hW hlc hrange hα t

theorem βHensel_weight_bound_of_structured_invariant_unlocked_of_rangeWfreeMatch_clearedBaseCases
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hRgraded : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hlc : H.leadingCoeff = 1)
    (hrange : RestrictedFaaDiBrunoRangeWfreeMatch H x₀ R hHyp)
    (hα : AlphaGenuineRegularWeightLe_clearedBaseCases H x₀ R hHyp hH D) (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_of_structured_invariant_unlocked_of_WfreeMatch_clearedBaseCases
    H x₀ R hHyp hH hDH hdR2 hdHR hW hRgraded hDRx0 hlc
    (RestrictedFaaDiBrunoWfreeMatch.of_rangeWfreeMatch H x₀ R hHyp hrange)
    hα t

theorem βHensel_weight_bound_all_of_structured_invariant_unlocked_of_rangeWfreeMatch_clearedBaseCases
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hRgraded : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hlc : H.leadingCoeff = 1)
    (hrange : RestrictedFaaDiBrunoRangeWfreeMatch H x₀ R hHyp)
    (hα : AlphaGenuineRegularWeightLe_clearedBaseCases H x₀ R hHyp hH D) :
    ∀ t, weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  fun t =>
    βHensel_weight_bound_of_structured_invariant_unlocked_of_rangeWfreeMatch_clearedBaseCases
      H x₀ R hHyp hH hDH hdR2 hdHR hW hRgraded hDRx0 hlc hrange hα t

theorem βHenselStructuredWeightInvariant_unlocked_of_normalized_divWeight_cases_of_WfreeMatch
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hlc : H.leadingCoeff = 1)
    (hWfree : RestrictedFaaDiBrunoWfreeMatch H x₀ R hHyp)
    (h0 : ∃ a : 𝒪 H,
      βHensel H x₀ R hHyp 0 = a * W𝒪 H ∧
        weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1)
    (hsucc : ∀ t : ℕ, ∃ a : 𝒪 H,
      βHensel H x₀ R hHyp (t + 1)
        = a * (W𝒪 H) ^ (t + 2) * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t + 1) ∧
        weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1)
    (k : ℕ) :
    βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  βHenselStructuredWeightInvariant_unlocked_of_normalized_divWeight_cases_of_restrictedMatch
    H x₀ R hHyp hH hDH hDRx0 hdR2
    (RestrictedFaaDiBrunoMatch.of_WfreeMatch H x₀ R hHyp hlc hWfree)
    h0 hsucc k

theorem βHenselStructuredWeightInvariant_all_unlocked_of_normalized_divWeight_cases_of_WfreeMatch
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hlc : H.leadingCoeff = 1)
    (hWfree : RestrictedFaaDiBrunoWfreeMatch H x₀ R hHyp)
    (h0 : ∃ a : 𝒪 H,
      βHensel H x₀ R hHyp 0 = a * W𝒪 H ∧
        weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1)
    (hsucc : ∀ t : ℕ, ∃ a : 𝒪 H,
      βHensel H x₀ R hHyp (t + 1)
        = a * (W𝒪 H) ^ (t + 2) * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t + 1) ∧
        weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1) :
    ∀ k, βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  fun k =>
    βHenselStructuredWeightInvariant_unlocked_of_normalized_divWeight_cases_of_WfreeMatch
      H x₀ R hHyp hH hDH hDRx0 hdR2 hlc hWfree h0 hsucc k

theorem βHensel_weight_bound_unlocked_of_normalized_divWeight_cases_of_WfreeMatch
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hlc : H.leadingCoeff = 1)
    (hWfree : RestrictedFaaDiBrunoWfreeMatch H x₀ R hHyp)
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
  βHensel_weight_bound_unlocked_of_normalized_divWeight_cases_of_restrictedMatch
    H x₀ R hHyp hH hDH hDRx0 hdR2 hdHR hW
    (RestrictedFaaDiBrunoMatch.of_WfreeMatch H x₀ R hHyp hlc hWfree)
    h0 hsucc t

theorem βHensel_weight_bound_all_unlocked_of_normalized_divWeight_cases_of_WfreeMatch
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hlc : H.leadingCoeff = 1)
    (hWfree : RestrictedFaaDiBrunoWfreeMatch H x₀ R hHyp)
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
    βHensel_weight_bound_unlocked_of_normalized_divWeight_cases_of_WfreeMatch
      H x₀ R hHyp hH hDH hDRx0 hdR2 hdHR hW hlc hWfree h0 hsucc t

theorem βHensel_weight_bound_of_structured_invariant_unlocked_of_normalized_divWeight_cases_of_WfreeMatch
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hRgraded : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hlc : H.leadingCoeff = 1)
    (hWfree : RestrictedFaaDiBrunoWfreeMatch H x₀ R hHyp)
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
  βHensel_weight_bound_of_structured_invariant_unlocked_of_normalized_divWeight_cases_of_restrictedMatch
    H x₀ R hHyp hH hDH hdR2 hdHR hW hRgraded hDRx0
    (RestrictedFaaDiBrunoMatch.of_WfreeMatch H x₀ R hHyp hlc hWfree)
    h0 hsucc t

theorem βHensel_weight_bound_all_of_structured_invariant_unlocked_of_normalized_divWeight_cases_of_WfreeMatch
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hRgraded : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hlc : H.leadingCoeff = 1)
    (hWfree : RestrictedFaaDiBrunoWfreeMatch H x₀ R hHyp)
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
    βHensel_weight_bound_of_structured_invariant_unlocked_of_normalized_divWeight_cases_of_WfreeMatch
      H x₀ R hHyp hH hDH hdR2 hdHR hW hRgraded hDRx0 hlc hWfree h0 hsucc t

theorem βHenselStructuredWeightInvariant_unlocked_of_normalized_divWeight_cases_of_rangeWfreeMatch
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hlc : H.leadingCoeff = 1)
    (hrange : RestrictedFaaDiBrunoRangeWfreeMatch H x₀ R hHyp)
    (h0 : ∃ a : 𝒪 H,
      βHensel H x₀ R hHyp 0 = a * W𝒪 H ∧
        weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1)
    (hsucc : ∀ t : ℕ, ∃ a : 𝒪 H,
      βHensel H x₀ R hHyp (t + 1)
        = a * (W𝒪 H) ^ (t + 2) * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t + 1) ∧
        weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1)
    (k : ℕ) :
    βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  βHenselStructuredWeightInvariant_unlocked_of_normalized_divWeight_cases_of_WfreeMatch
    H x₀ R hHyp hH hDH hDRx0 hdR2 hlc
    (RestrictedFaaDiBrunoWfreeMatch.of_rangeWfreeMatch H x₀ R hHyp hrange)
    h0 hsucc k

theorem βHenselStructuredWeightInvariant_all_unlocked_of_normalized_divWeight_cases_of_rangeWfreeMatch
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hlc : H.leadingCoeff = 1)
    (hrange : RestrictedFaaDiBrunoRangeWfreeMatch H x₀ R hHyp)
    (h0 : ∃ a : 𝒪 H,
      βHensel H x₀ R hHyp 0 = a * W𝒪 H ∧
        weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1)
    (hsucc : ∀ t : ℕ, ∃ a : 𝒪 H,
      βHensel H x₀ R hHyp (t + 1)
        = a * (W𝒪 H) ^ (t + 2) * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * t + 1) ∧
        weight_Λ_over_𝒪 hH a D ≤ WithBot.some 1) :
    ∀ k, βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  fun k =>
    βHenselStructuredWeightInvariant_unlocked_of_normalized_divWeight_cases_of_rangeWfreeMatch
      H x₀ R hHyp hH hDH hDRx0 hdR2 hlc hrange h0 hsucc k

theorem βHensel_weight_bound_unlocked_of_normalized_divWeight_cases_of_rangeWfreeMatch
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hlc : H.leadingCoeff = 1)
    (hrange : RestrictedFaaDiBrunoRangeWfreeMatch H x₀ R hHyp)
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
  βHensel_weight_bound_unlocked_of_normalized_divWeight_cases_of_WfreeMatch
    H x₀ R hHyp hH hDH hDRx0 hdR2 hdHR hW hlc
    (RestrictedFaaDiBrunoWfreeMatch.of_rangeWfreeMatch H x₀ R hHyp hrange)
    h0 hsucc t

theorem βHensel_weight_bound_all_unlocked_of_normalized_divWeight_cases_of_rangeWfreeMatch
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hlc : H.leadingCoeff = 1)
    (hrange : RestrictedFaaDiBrunoRangeWfreeMatch H x₀ R hHyp)
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
    βHensel_weight_bound_unlocked_of_normalized_divWeight_cases_of_rangeWfreeMatch
      H x₀ R hHyp hH hDH hDRx0 hdR2 hdHR hW hlc hrange h0 hsucc t

theorem βHensel_weight_bound_of_structured_invariant_unlocked_of_normalized_divWeight_cases_of_rangeWfreeMatch
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hRgraded : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hlc : H.leadingCoeff = 1)
    (hrange : RestrictedFaaDiBrunoRangeWfreeMatch H x₀ R hHyp)
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
  βHensel_weight_bound_of_structured_invariant_unlocked_of_normalized_divWeight_cases_of_WfreeMatch
    H x₀ R hHyp hH hDH hdR2 hdHR hW hRgraded hDRx0 hlc
    (RestrictedFaaDiBrunoWfreeMatch.of_rangeWfreeMatch H x₀ R hHyp hrange)
    h0 hsucc t

theorem βHensel_weight_bound_all_of_structured_invariant_unlocked_of_normalized_divWeight_cases_of_rangeWfreeMatch
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hRgraded : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hlc : H.leadingCoeff = 1)
    (hrange : RestrictedFaaDiBrunoRangeWfreeMatch H x₀ R hHyp)
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
    βHensel_weight_bound_of_structured_invariant_unlocked_of_normalized_divWeight_cases_of_rangeWfreeMatch
      H x₀ R hHyp hH hDH hdR2 hdHR hW hRgraded hDRx0 hlc hrange h0 hsucc t

theorem βHenselStructuredWeightInvariant_unlocked_of_WfreeMatch_successors_fixed
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (hd : 2 ≤ H.natDegree) {D : ℕ}
    (hD : D ≤ H.natDegree)
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hlc : H.leadingCoeff = 1)
    (hWfree : RestrictedFaaDiBrunoWfreeMatch H x₀ R hHyp)
    (hsucc : ∀ t, AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t) (k : ℕ) :
    βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  βHenselStructuredWeightInvariant_unlocked_of_restrictedMatch_successors_fixed
    H x₀ R hHyp hH hd hD hDH hDRx0 hdR2
    (RestrictedFaaDiBrunoMatch.of_WfreeMatch H x₀ R hHyp hlc hWfree)
    hsucc k

theorem βHenselStructuredWeightInvariant_all_unlocked_of_WfreeMatch_successors_fixed
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (hd : 2 ≤ H.natDegree) {D : ℕ}
    (hD : D ≤ H.natDegree)
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hlc : H.leadingCoeff = 1)
    (hWfree : RestrictedFaaDiBrunoWfreeMatch H x₀ R hHyp)
    (hsucc : ∀ t, AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t) :
    ∀ k, βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  fun k =>
    βHenselStructuredWeightInvariant_unlocked_of_WfreeMatch_successors_fixed
      H x₀ R hHyp hH hd hD hDH hDRx0 hdR2 hlc hWfree hsucc k

theorem βHensel_weight_bound_unlocked_of_WfreeMatch_successors_fixed
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (hd : 2 ≤ H.natDegree) {D : ℕ}
    (hD : D ≤ H.natDegree)
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hlc : H.leadingCoeff = 1)
    (hWfree : RestrictedFaaDiBrunoWfreeMatch H x₀ R hHyp)
    (hsucc : ∀ t, AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t) (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_unlocked_of_restrictedMatch_successors_fixed
    H x₀ R hHyp hH hd hD hDH hDRx0 hdR2 hdHR hW
    (RestrictedFaaDiBrunoMatch.of_WfreeMatch H x₀ R hHyp hlc hWfree)
    hsucc t

theorem βHensel_weight_bound_all_unlocked_of_WfreeMatch_successors_fixed
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (hd : 2 ≤ H.natDegree) {D : ℕ}
    (hD : D ≤ H.natDegree)
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hlc : H.leadingCoeff = 1)
    (hWfree : RestrictedFaaDiBrunoWfreeMatch H x₀ R hHyp)
    (hsucc : ∀ t, AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t) :
    ∀ t, weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  fun t =>
    βHensel_weight_bound_unlocked_of_WfreeMatch_successors_fixed
      H x₀ R hHyp hH hd hD hDH hDRx0 hdR2 hdHR hW hlc hWfree hsucc t

theorem βHensel_weight_bound_of_structured_invariant_unlocked_of_WfreeMatch_successors_fixed
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (hd : 2 ≤ H.natDegree) {D : ℕ}
    (hD : D ≤ H.natDegree)
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hRgraded : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hlc : H.leadingCoeff = 1)
    (hWfree : RestrictedFaaDiBrunoWfreeMatch H x₀ R hHyp)
    (hsucc : ∀ t, AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t) (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_of_structured_invariant_unlocked_of_restrictedMatch_successors_fixed
    H x₀ R hHyp hH hd hD hDH hdR2 hdHR hW hRgraded hDRx0
    (RestrictedFaaDiBrunoMatch.of_WfreeMatch H x₀ R hHyp hlc hWfree)
    hsucc t

theorem βHensel_weight_bound_all_of_structured_invariant_unlocked_of_WfreeMatch_successors_fixed
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (hd : 2 ≤ H.natDegree) {D : ℕ}
    (hD : D ≤ H.natDegree)
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hRgraded : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hlc : H.leadingCoeff = 1)
    (hWfree : RestrictedFaaDiBrunoWfreeMatch H x₀ R hHyp)
    (hsucc : ∀ t, AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t) :
    ∀ t, weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  fun t =>
    βHensel_weight_bound_of_structured_invariant_unlocked_of_WfreeMatch_successors_fixed
      H x₀ R hHyp hH hd hD hDH hdR2 hdHR hW hRgraded hDRx0 hlc hWfree hsucc t

theorem βHenselStructuredWeightInvariant_unlocked_of_rangeWfreeMatch_successors_fixed
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (hd : 2 ≤ H.natDegree) {D : ℕ}
    (hD : D ≤ H.natDegree)
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hlc : H.leadingCoeff = 1)
    (hrange : RestrictedFaaDiBrunoRangeWfreeMatch H x₀ R hHyp)
    (hsucc : ∀ t, AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t) (k : ℕ) :
    βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  βHenselStructuredWeightInvariant_unlocked_of_WfreeMatch_successors_fixed
    H x₀ R hHyp hH hd hD hDH hDRx0 hdR2 hlc
    (RestrictedFaaDiBrunoWfreeMatch.of_rangeWfreeMatch H x₀ R hHyp hrange)
    hsucc k

theorem βHenselStructuredWeightInvariant_all_unlocked_of_rangeWfreeMatch_successors_fixed
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (hd : 2 ≤ H.natDegree) {D : ℕ}
    (hD : D ≤ H.natDegree)
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hlc : H.leadingCoeff = 1)
    (hrange : RestrictedFaaDiBrunoRangeWfreeMatch H x₀ R hHyp)
    (hsucc : ∀ t, AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t) :
    ∀ k, βHenselStructuredWeightInvariant (D := D) H x₀ R hHyp hH k :=
  fun k =>
    βHenselStructuredWeightInvariant_unlocked_of_rangeWfreeMatch_successors_fixed
      H x₀ R hHyp hH hd hD hDH hDRx0 hdR2 hlc hrange hsucc k

theorem βHensel_weight_bound_unlocked_of_rangeWfreeMatch_successors_fixed
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (hd : 2 ≤ H.natDegree) {D : ℕ}
    (hD : D ≤ H.natDegree)
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hlc : H.leadingCoeff = 1)
    (hrange : RestrictedFaaDiBrunoRangeWfreeMatch H x₀ R hHyp)
    (hsucc : ∀ t, AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t) (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_unlocked_of_WfreeMatch_successors_fixed
    H x₀ R hHyp hH hd hD hDH hDRx0 hdR2 hdHR hW hlc
    (RestrictedFaaDiBrunoWfreeMatch.of_rangeWfreeMatch H x₀ R hHyp hrange)
    hsucc t

theorem βHensel_weight_bound_all_unlocked_of_rangeWfreeMatch_successors_fixed
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (hd : 2 ≤ H.natDegree) {D : ℕ}
    (hD : D ≤ H.natDegree)
    (hDH : Bivariate.totalDegree H ≤ D)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hlc : H.leadingCoeff = 1)
    (hrange : RestrictedFaaDiBrunoRangeWfreeMatch H x₀ R hHyp)
    (hsucc : ∀ t, AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t) :
    ∀ t, weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  fun t =>
    βHensel_weight_bound_unlocked_of_rangeWfreeMatch_successors_fixed
      H x₀ R hHyp hH hd hD hDH hDRx0 hdR2 hdHR hW hlc hrange hsucc t

theorem βHensel_weight_bound_of_structured_invariant_unlocked_of_rangeWfreeMatch_successors_fixed
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (hd : 2 ≤ H.natDegree) {D : ℕ}
    (hD : D ≤ H.natDegree)
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hRgraded : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hlc : H.leadingCoeff = 1)
    (hrange : RestrictedFaaDiBrunoRangeWfreeMatch H x₀ R hHyp)
    (hsucc : ∀ t, AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t) (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  βHensel_weight_bound_of_structured_invariant_unlocked_of_WfreeMatch_successors_fixed
    H x₀ R hHyp hH hd hD hDH hdR2 hdHR hW hRgraded hDRx0 hlc
    (RestrictedFaaDiBrunoWfreeMatch.of_rangeWfreeMatch H x₀ R hHyp hrange)
    hsucc t

theorem βHensel_weight_bound_all_of_structured_invariant_unlocked_of_rangeWfreeMatch_successors_fixed
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (hd : 2 ≤ H.natDegree) {D : ℕ}
    (hD : D ≤ H.natDegree)
    (hDH : Bivariate.totalDegree H ≤ D)
    (hdR2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHR : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R)
    (hW : (H.leadingCoeff).natDegree + Bivariate.natDegreeY H ≤ D)
    (hRgraded : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    (hDRx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hlc : H.leadingCoeff = 1)
    (hrange : RestrictedFaaDiBrunoRangeWfreeMatch H x₀ R hHyp)
    (hsucc : ∀ t, AlphaGenuineRegularWeightLe_succ H x₀ R hHyp hH D t) :
    ∀ t, weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) :=
  fun t =>
    βHensel_weight_bound_of_structured_invariant_unlocked_of_rangeWfreeMatch_successors_fixed
      H x₀ R hHyp hH hd hD hDH hdR2 hdHR hW hRgraded hDRx0 hlc hrange hsucc t

end BCIKS20.HenselNumerator

-- Axiom audit: these W-free bridge wrappers inherit the existing cleared P1/P2 surface.
#print axioms BCIKS20.HenselNumerator.alphaWeight_successors_iff_divWeight_successors_of_WfreeMatch
#print axioms BCIKS20.HenselNumerator.alphaWeight_clearedBaseCases_iff_divWeight_successors_of_WfreeMatch_fixed
#print axioms BCIKS20.HenselNumerator.divWeight_clearedBaseCases_iff_alphaWeight_successors_of_WfreeMatch_fixed
#print axioms BCIKS20.HenselNumerator.alphaWeight_clearedBaseCases_iff_divWeight_successors_of_rangeWfreeMatch_fixed
#print axioms BCIKS20.HenselNumerator.divWeight_clearedBaseCases_iff_alphaWeight_successors_of_rangeWfreeMatch_fixed
#print axioms BCIKS20.HenselNumerator.alphaWeight_iff_normalized_divWeight_cases_of_WfreeMatch
#print axioms BCIKS20.HenselNumerator.alphaWeight_of_normalized_divWeight_cases_of_WfreeMatch
#print axioms BCIKS20.HenselNumerator.alphaWeight_iff_normalized_divWeight_cases_of_rangeWfreeMatch
#print axioms BCIKS20.HenselNumerator.alphaWeight_of_normalized_divWeight_cases_of_rangeWfreeMatch
#print axioms BCIKS20.HenselNumerator.alphaWeight_iff_divWeight_of_WfreeMatch
#print axioms BCIKS20.HenselNumerator.divWeight_of_alphaWeight_of_WfreeMatch
#print axioms BCIKS20.HenselNumerator.alphaWeight_of_divWeight_of_WfreeMatch
#print axioms BCIKS20.HenselNumerator.alphaWeight_iff_divWeight_of_rangeWfreeMatch
#print axioms BCIKS20.HenselNumerator.divWeight_of_alphaWeight_of_rangeWfreeMatch
#print axioms BCIKS20.HenselNumerator.alphaWeight_of_divWeight_of_rangeWfreeMatch
#print axioms BCIKS20.HenselNumerator.normalized_divWeight_cases_of_alphaWeight_of_WfreeMatch
#print axioms BCIKS20.HenselNumerator.normalized_divWeight_zero_of_alphaWeight_of_WfreeMatch
#print axioms BCIKS20.HenselNumerator.normalized_divWeight_succ_of_alphaWeight_of_WfreeMatch
#print axioms BCIKS20.HenselNumerator.normalized_divWeight_cases_of_alphaWeight_of_rangeWfreeMatch
#print axioms BCIKS20.HenselNumerator.normalized_divWeight_zero_of_alphaWeight_of_rangeWfreeMatch
#print axioms BCIKS20.HenselNumerator.normalized_divWeight_succ_of_alphaWeight_of_rangeWfreeMatch
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_unlocked_of_WfreeMatch_clearedBaseCases
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_all_unlocked_of_WfreeMatch_clearedBaseCases
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_unlocked_of_WfreeMatch_clearedBaseCases
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_all_unlocked_of_WfreeMatch_clearedBaseCases
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_of_structured_invariant_unlocked_of_WfreeMatch_clearedBaseCases
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_all_of_structured_invariant_unlocked_of_WfreeMatch_clearedBaseCases
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_unlocked_of_rangeWfreeMatch_clearedBaseCases
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_all_unlocked_of_rangeWfreeMatch_clearedBaseCases
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_unlocked_of_rangeWfreeMatch_clearedBaseCases
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_all_unlocked_of_rangeWfreeMatch_clearedBaseCases
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_of_structured_invariant_unlocked_of_rangeWfreeMatch_clearedBaseCases
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_all_of_structured_invariant_unlocked_of_rangeWfreeMatch_clearedBaseCases
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_unlocked_of_normalized_divWeight_cases_of_WfreeMatch
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_all_unlocked_of_normalized_divWeight_cases_of_WfreeMatch
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_unlocked_of_normalized_divWeight_cases_of_WfreeMatch
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_all_unlocked_of_normalized_divWeight_cases_of_WfreeMatch
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_of_structured_invariant_unlocked_of_normalized_divWeight_cases_of_WfreeMatch
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_all_of_structured_invariant_unlocked_of_normalized_divWeight_cases_of_WfreeMatch
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_unlocked_of_normalized_divWeight_cases_of_rangeWfreeMatch
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_all_unlocked_of_normalized_divWeight_cases_of_rangeWfreeMatch
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_unlocked_of_normalized_divWeight_cases_of_rangeWfreeMatch
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_all_unlocked_of_normalized_divWeight_cases_of_rangeWfreeMatch
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_of_structured_invariant_unlocked_of_normalized_divWeight_cases_of_rangeWfreeMatch
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_all_of_structured_invariant_unlocked_of_normalized_divWeight_cases_of_rangeWfreeMatch
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_unlocked_of_WfreeMatch_successors_fixed
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_all_unlocked_of_WfreeMatch_successors_fixed
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_unlocked_of_WfreeMatch_successors_fixed
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_all_unlocked_of_WfreeMatch_successors_fixed
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_of_structured_invariant_unlocked_of_WfreeMatch_successors_fixed
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_all_of_structured_invariant_unlocked_of_WfreeMatch_successors_fixed
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_unlocked_of_rangeWfreeMatch_successors_fixed
#print axioms BCIKS20.HenselNumerator.βHenselStructuredWeightInvariant_all_unlocked_of_rangeWfreeMatch_successors_fixed
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_unlocked_of_rangeWfreeMatch_successors_fixed
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_all_unlocked_of_rangeWfreeMatch_successors_fixed
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_of_structured_invariant_unlocked_of_rangeWfreeMatch_successors_fixed
#print axioms BCIKS20.HenselNumerator.βHensel_weight_bound_all_of_structured_invariant_unlocked_of_rangeWfreeMatch_successors_fixed
