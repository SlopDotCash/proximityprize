/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LineListCodewordSingletonSupportRatio

/-!
# Weighted denominator route for codeword singleton witnesses

`LineListCodewordSingletonSupportRatio.lean` proves both the denominator scalar cap

```text
#singletonScalars(c) <= support(u₁) / (a - #zeroAgreement(c))
```

and its support-choose relaxation.  This file keeps the sharper weighted denominator accounting:
sum the actual denominator cap over appearing codewords on the line, then combine it with the
large-zero line weight.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- Weighted denominator cost of all codeword-indexed singleton scalar caps on one line.  This is
the scalar-count analogue of `codewordSupportChooseWeight`: it pays the older denominator cap for
each appearing codeword with its actual zero-agreement profile. -/
noncomputable def codewordSupportDivWeight
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) : ℕ :=
  ∑ c ∈ lineAppearingCodewords dom k a u₀ u₁,
    (directionSupportSet u₁).card /
      (a - (directionZeroAgreementSet c u₀ u₁).card)

/-- Uniform combined arithmetic budget using the weighted denominator scalar cost. -/
def UniformLargeZeroSafeWeightPlusCodewordSupportDivBudgeted
    (dom : Fin n ↪ F) (k a B : ℕ) : Prop :=
  ∀ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
    ZeroDirectionSafeLine dom k a u₀ u₁ →
      puncturedZeroStratifiedLineWeight dom k a u₀ u₁
        + codewordSupportDivWeight dom k a u₀ u₁ ≤ 2 * B

open Classical in
/-- The singleton defect is bounded by the weighted denominator cost on safe lines. -/
theorem singletonBadScalarDefect_le_codewordSupportDivWeight_of_zeroSafe
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F)
    (hsafe : ZeroDirectionSafeLine dom k a u₀ u₁) :
    singletonBadScalarDefect dom k a u₀ u₁
      ≤ codewordSupportDivWeight dom k a u₀ u₁ := by
  rw [singletonBadScalarDefect_eq_sum_codewordSingletonWitnessScalars,
    codewordSupportDivWeight]
  refine Finset.sum_le_sum ?_
  intro c hc
  have hcCode : c ∈ (rsCode dom k : Submodule F (Fin n → F)) := by
    rw [lineAppearingCodewords, Finset.mem_filter] at hc
    exact hc.2.1
  exact codewordSingletonWitnessScalars_card_le_support_div_of_zeroSafe
    dom k a u₀ u₁ c hsafe hcCode

open Classical in
/-- Fixed-line consumer for the weighted denominator singleton route. -/
theorem lineBadScalars_card_le_of_weight_add_codewordSupportDiv_le_two_mul
    (dom : Fin n ↪ F) (k a B : ℕ) (u₀ u₁ : Fin n → F)
    (hsafe : ZeroDirectionSafeLine dom k a u₀ u₁)
    (hbudget : puncturedZeroStratifiedLineWeight dom k a u₀ u₁
        + codewordSupportDivWeight dom k a u₀ u₁ ≤ 2 * B) :
    (lineBadScalars dom k a u₀ u₁).card ≤ B :=
  lineBadScalars_card_le_of_weight_add_singletonDefect_le_two_mul
    dom k a B u₀ u₁ hsafe
    (le_trans
      (Nat.add_le_add_left
        (singletonBadScalarDefect_le_codewordSupportDivWeight_of_zeroSafe
          dom k a u₀ u₁ hsafe)
        (puncturedZeroStratifiedLineWeight dom k a u₀ u₁))
      hbudget)

open Classical in
/-- The weighted denominator budget discharges the large-zero safe residual. -/
theorem largeZeroSafeLineBadScalarsBudgeted_of_codewordSupportDivWeightBudget
    (dom : Fin n ↪ F) (k a B : ℕ)
    (hbudget : UniformLargeZeroSafeWeightPlusCodewordSupportDivBudgeted dom k a B) :
    LargeZeroSafeLineBadScalarsBudgeted dom k a B := by
  intro u₀ u₁ hnotEligible hsafe
  exact lineBadScalars_card_le_of_weight_add_codewordSupportDiv_le_two_mul
    dom k a B u₀ u₁ hsafe (hbudget u₀ u₁ hnotEligible hsafe)

open Classical in
/-- Production wrapper for the weighted denominator route. -/
theorem uniformLineBadScalarsBudgeted_of_supportAdjusted_and_codewordSupportDivWeightBudget
    (dom : Fin n ↪ F) (k a L B : ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hbudget : UniformLargeZeroSafeWeightPlusCodewordSupportDivBudgeted dom k a B) :
    UniformLineBadScalarsBudgeted dom k a B :=
  uniformLineBadScalarsBudgeted_of_supportAdjustedBudgetFits_and_largeZeroSafe
    dom k a L B hSupport hFits hZeroSafe
    (largeZeroSafeLineBadScalarsBudgeted_of_codewordSupportDivWeightBudget
      dom k a B hbudget)

open Classical in
/-- Exact failure form for the weighted denominator arithmetic budget. -/
theorem
    not_uniformLargeZeroSafeWeightPlusCodewordSupportDivBudgeted_iff_exists_weight_gt
    (dom : Fin n ↪ F) (k a B : ℕ) :
    (¬ UniformLargeZeroSafeWeightPlusCodewordSupportDivBudgeted dom k a B) ↔
      ∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
        ZeroDirectionSafeLine dom k a u₀ u₁ ∧
          2 * B < puncturedZeroStratifiedLineWeight dom k a u₀ u₁
            + codewordSupportDivWeight dom k a u₀ u₁ := by
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro u₀ u₁ hnotEligible hsafe
    exact le_of_not_gt
      (fun hgt => hnone ⟨u₀, u₁, hnotEligible, hsafe, hgt⟩)
  · rintro ⟨u₀, u₁, hnotEligible, hsafe, hgt⟩ hbudget
    exact (not_lt_of_ge (hbudget u₀ u₁ hnotEligible hsafe)) hgt

open Classical in
/-- Scanner for the weighted denominator route.  Once support-side hypotheses are fixed, failed
production exposes a large-zero safe line where the actual weighted denominator arithmetic is
above budget. -/
theorem exists_largeZero_safe_codewordSupportDivWeight_gt_of_not_uniformLineBadScalarsBudgeted
    (dom : Fin n ↪ F) (k a L B : ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hnot : ¬ UniformLineBadScalarsBudgeted dom k a B) :
    ∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
      ZeroDirectionSafeLine dom k a u₀ u₁ ∧
        2 * B < puncturedZeroStratifiedLineWeight dom k a u₀ u₁
          + codewordSupportDivWeight dom k a u₀ u₁ := by
  have hnotBudget :
      ¬ UniformLargeZeroSafeWeightPlusCodewordSupportDivBudgeted dom k a B := by
    intro hbudget
    exact hnot
      (uniformLineBadScalarsBudgeted_of_supportAdjusted_and_codewordSupportDivWeightBudget
        dom k a L B hSupport hFits hZeroSafe hbudget)
  exact
    (not_uniformLargeZeroSafeWeightPlusCodewordSupportDivBudgeted_iff_exists_weight_gt
      dom k a B).mp hnotBudget

open Classical in
/-- The weighted denominator cost sits below the weighted support-choose cost on safe lines. -/
theorem codewordSupportDivWeight_le_codewordSupportChooseWeight_of_zeroSafe
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F)
    (hsafe : ZeroDirectionSafeLine dom k a u₀ u₁) :
    codewordSupportDivWeight dom k a u₀ u₁
      ≤ codewordSupportChooseWeight dom k a u₀ u₁ := by
  rw [codewordSupportDivWeight, codewordSupportChooseWeight]
  refine Finset.sum_le_sum ?_
  intro c hc
  exact support_div_sub_zeroAgreement_le_support_choose_of_zeroSafe
    dom k a u₀ u₁ c hsafe hc

open Classical in
/-- The weighted support-choose arithmetic budget implies the sharper weighted denominator
arithmetic budget. -/
theorem
    uniformLargeZeroSafeWeightPlusCodewordSupportDivBudgeted_of_codewordSupportChooseWeightBudget
    (dom : Fin n ↪ F) (k a B : ℕ)
    (hchoose : UniformLargeZeroSafeWeightPlusCodewordSupportChooseBudgeted dom k a B) :
    UniformLargeZeroSafeWeightPlusCodewordSupportDivBudgeted dom k a B := by
  intro u₀ u₁ hnotEligible hsafe
  exact le_trans
    (Nat.add_le_add_left
      (codewordSupportDivWeight_le_codewordSupportChooseWeight_of_zeroSafe
        dom k a u₀ u₁ hsafe)
      (puncturedZeroStratifiedLineWeight dom k a u₀ u₁))
    (hchoose u₀ u₁ hnotEligible hsafe)

section SourceAudit

#print axioms codewordSupportDivWeight
#print axioms UniformLargeZeroSafeWeightPlusCodewordSupportDivBudgeted
#print axioms singletonBadScalarDefect_le_codewordSupportDivWeight_of_zeroSafe
#print axioms lineBadScalars_card_le_of_weight_add_codewordSupportDiv_le_two_mul
#print axioms largeZeroSafeLineBadScalarsBudgeted_of_codewordSupportDivWeightBudget
#print axioms
  uniformLineBadScalarsBudgeted_of_supportAdjusted_and_codewordSupportDivWeightBudget
#print axioms
  not_uniformLargeZeroSafeWeightPlusCodewordSupportDivBudgeted_iff_exists_weight_gt
#print axioms
  exists_largeZero_safe_codewordSupportDivWeight_gt_of_not_uniformLineBadScalarsBudgeted
#print axioms codewordSupportDivWeight_le_codewordSupportChooseWeight_of_zeroSafe
#print axioms
  uniformLargeZeroSafeWeightPlusCodewordSupportDivBudgeted_of_codewordSupportChooseWeightBudget

end SourceAudit

end ProximityGap.Ownership
