/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import ArkLib.Research.ProximityGap.FullPrizeContract
import ArkLib.Research.ProximityGap.Frontier.BudgetTwoMcaBoundary
import ArkLib.Research.ProximityGap.Frontier.BudgetTwoSixteenLower
import ArkLib.Research.ProximityGap.Frontier.BudgetTwoSixteenPeriod
import ArkLib.Research.ProximityGap.Frontier.ThreeWordAgreement

/-!
# Both prize boundaries for smooth sixteen-point domains with budget two

At each of the four rates the first failing MCA step is two. The first failing
list steps are five, eight, ten and eleven. One explicit prime-field domain with
these cutoffs also has a nonprincipal period with real part greater than
sixteen minus one hundred-millionth.
-/

namespace ProximityGap.BudgetTwoSixteen

open Code GrandChallenges CoreDefinitions FullPrizeReview
open scoped NNReal ENNReal

private theorem card_K : Fintype.card K = QuarterBudgetTwoThreshold.p :=
  ZMod.card QuarterBudgetTwoThreshold.p

private theorem budget_number : QuarterBudgetTwoThreshold.p / 2^128 = 2 := by decide

private theorem field_budget : Fintype.card K / 2^128 = 2 :=
  (congrArg (fun q : ℕ => q / 2^128) card_K).trans budget_number

variable {F I : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype I] [Nonempty I] [DecidableEq I]

/-- Every positive width has the same four list cutoffs throughout the budget-two window. -/
theorem smooth_list_threshold (D : I ↪ F) [ReedSolomon.Smooth D] (hn : Fintype.card I = 16)
    (budget : Fintype.card F / 2^128 = 2) (j : Fin 4) (m : ℕ) (hm : 0 < m) (δ : ℝ) :
    ((Lambda (interleavedCodeSet (κ := Fin m)
      (ReedSolomon.code D (dimension j) : Set (I → F))) δ : ℕ∞) : ENNReal) ≤
        ((prizeThreshold : ℝ≥0) : ENNReal) * Fintype.card F ↔ δ < (firstBad j : ℝ) / 16 := by
  rw [FourRateList128.budget_cast, budget]
  constructor
  · intro good
    by_contra! fail
    let lift (v : F) : Fin m → F := fun _ => v
    have hinj : Function.Injective lift := fun _ _ he => congrFun he ⟨0, hm⟩
    have hdiag := Code.Lambda_le_of_injective_comp (e := lift) hinj
      (C := (ReedSolomon.code D (dimension j) : Set (I → F)))
      (D := interleavedCodeSet (κ := Fin m) (ReedSolomon.code D (dimension j) : Set (I → F)))
      (fun _ hc _ => hc) δ
    have lower := (SixteenCosetListLower.smooth_scalar_lower D hn j).trans (Lambda_mono fail)
    exact (by decide : ¬ (3 : ℕ∞) ≤ 2) (lower.trans (hdiag.trans good))
  · intro below
    apply ThreeWordAgreement.interleaved_list_le_two D (dimension j) m (17 - firstBad j) δ
    · rw [hn]
      have h := (lt_div_iff₀ (by norm_num : (0 : ℝ) < 16)).mp below
      fin_cases j <;> norm_num [firstBad] at h ⊢ <;> linarith
    · rw [hn]
      fin_cases j <;> decide

/-- The dimension-independent MCA answer. -/
def mcaAnswerAt {n : ℕ} (hn : n = 16) (_k : ℕ) : Boundary n := some ⟨2, by omega⟩

/-- The four predicted list answers, independent of positive width. -/
def listAnswerAt {n : ℕ} (hn : n = 16) (k _m : ℕ) : Boundary n :=
  if k = 8 then some ⟨5, by omega⟩ else if k = 4 then some ⟨8, by omega⟩
  else if k = 2 then some ⟨10, by omega⟩ else some ⟨11, by omega⟩

/-- The full review contract holds for every supplied smooth length-sixteen domain
whose 128-bit budget is two. -/
theorem correctForSmoothSixteen [SampleableType F] (D : I ↪ F) [ReedSolomon.Smooth D]
    (hn : Fintype.card I = 16) (budget : Fintype.card F / 2^128 = 2) :
    correctForDomain D (prizeThreshold : ℝ≥0) (mcaAnswerAt hn) (listAnswerAt hn) := by
  intro k hk
  have hr : k = 8 ∨ k = 4 ∨ k = 2 ∨ k = 1 := by
    simp only [hasPrizeRate, hn] at hk
    omega
  constructor
  · intro δ _
    exact BudgetTwoMcaBoundary.canonical_good_iff D (by rw [hn]; omega) budget δ
  · intro m hm δ _
    obtain ⟨j, rfl⟩ : ∃ j : Fin 4, k = dimension j := by
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨3, rfl⟩
    refine (smooth_list_threshold D hn budget j m hm δ).trans ?_
    fin_cases j <;> norm_num [dimension, firstBad, listAnswerAt, ← NNReal.coe_lt_coe, hn]

/-- The published prime-field example has these four list cutoffs. -/
theorem list_threshold (j : Fin 4) (m : ℕ) (hm : 0 < m) (δ : ℝ) :
    ((Lambda (interleavedCodeSet (κ := Fin m)
      (ReedSolomon.code domain (dimension j) : Set (Fin 16 → K))) δ : ℕ∞) : ENNReal) ≤
        ((prizeThreshold : ℝ≥0) : ENNReal) * Fintype.card K ↔ δ < (firstBad j : ℝ) / 16 :=
  smooth_list_threshold domain (Fintype.card_fin _) field_budget j m hm δ

/-- The MCA answer for the explicit domain. -/
abbrev mcaAnswer := mcaAnswerAt (Fintype.card_fin 16)

/-- The list answer for the explicit domain. -/
abbrev listAnswer := listAnswerAt (Fintype.card_fin 16)

/-- Both operational answer functions satisfy the review contract on this domain. -/
theorem correctForSixteen : correctForDomain domain (prizeThreshold : ℝ≥0) mcaAnswer listAnswer :=
  correctForSmoothSixteen domain (Fintype.card_fin _) field_budget

/-- The two verified coding cutoffs coexist with a nonprincipal positive period
greater than 16 minus one hundred-millionth on the same evaluation sites. -/
theorem coding_and_period :
    correctForDomain domain (prizeThreshold : ℝ≥0) mcaAnswer listAnswer ∧
    ∃ b : K, b ≠ 0 ∧ 16 - (1 : ℝ) / 100000000 <
      (ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ZMod.stdAddChar
        (Finset.univ.map domain) b).re :=
  ⟨correctForSixteen, BudgetTwoSixteenPeriod.frequency, BudgetTwoSixteenPeriod.frequency_ne_zero,
    BudgetTwoSixteenPeriod.real_period_gt domain (fun _ => rfl)⟩

#print axioms smooth_list_threshold
#print axioms correctForSmoothSixteen
#print axioms coding_and_period

end ProximityGap.BudgetTwoSixteen
