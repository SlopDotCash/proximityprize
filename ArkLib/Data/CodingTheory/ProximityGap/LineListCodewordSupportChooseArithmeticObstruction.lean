/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LineListCodewordSingletonSupportRatio

/-!
# Arithmetic obstruction for the codeword support-choose cap

`LineListCodewordSingletonSupportRatio.lean` proves that the codeword-indexed
support-ratio cover injects into

```text
powersetCard support(u₁) (a - #zeroAgreement(c,u₀,u₁)).
```

This file records the arithmetic no-go surface for that packing baseline.  If a concrete
large-zero safe line and appearing codeword have a support/zero-agreement profile whose binomial
term already exceeds the proposed cap `S`, then the uniform support-choose budget cannot hold.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- A uniform support-choose budget contains every concrete appearing-codeword binomial term. -/
theorem codewordSupportChooseBudget_term_le
    (dom : Fin n ↪ F) (k a S : ℕ) (u₀ u₁ c : Fin n → F)
    (hbudget : UniformLargeZeroSafeCodewordSupportChooseBudgeted dom k a S)
    (hnotEligible : ¬ SupportEligibleLineDirection a u₁)
    (hsafe : ZeroDirectionSafeLine dom k a u₀ u₁)
    (hc : c ∈ lineAppearingCodewords dom k a u₀ u₁) :
    (directionSupportSet u₁).card.choose
      (a - (directionZeroAgreementSet c u₀ u₁).card) ≤ S :=
  hbudget u₀ u₁ hnotEligible hsafe c hc

open Classical in
/-- A single over-budget appearing-codeword support-choose term refutes the uniform cap. -/
theorem not_uniformLargeZeroSafeCodewordSupportChooseBudgeted_of_exists_choose_gt
    (dom : Fin n ↪ F) (k a S : ℕ)
    (hgt : ∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
      ZeroDirectionSafeLine dom k a u₀ u₁ ∧
        ∃ c ∈ lineAppearingCodewords dom k a u₀ u₁,
          S < (directionSupportSet u₁).card.choose
            (a - (directionZeroAgreementSet c u₀ u₁).card)) :
    ¬ UniformLargeZeroSafeCodewordSupportChooseBudgeted dom k a S :=
  (not_uniformLargeZeroSafeCodewordSupportChooseBudgeted_iff_exists_choose_gt
    dom k a S).mpr hgt

open Classical in
/-- Profile form of the support-choose obstruction: exact support and zero-agreement cardinalities
turn the binomial inequality into failure of the uniform support-choose cap. -/
theorem
    not_uniformLargeZeroSafeCodewordSupportChooseBudgeted_of_exists_profile_choose_gt
    (dom : Fin n ↪ F) (k a S : ℕ)
    (hgt : ∃ u₀ u₁ c : Fin n → F, ∃ s z : ℕ,
      ¬ SupportEligibleLineDirection a u₁ ∧
        ZeroDirectionSafeLine dom k a u₀ u₁ ∧
          c ∈ lineAppearingCodewords dom k a u₀ u₁ ∧
            (directionSupportSet u₁).card = s ∧
              (directionZeroAgreementSet c u₀ u₁).card = z ∧
                S < s.choose (a - z)) :
    ¬ UniformLargeZeroSafeCodewordSupportChooseBudgeted dom k a S := by
  rcases hgt with
    ⟨u₀, u₁, c, s, z, hnotEligible, hsafe, hc, hsupport, hzero, hgt⟩
  exact
    not_uniformLargeZeroSafeCodewordSupportChooseBudgeted_of_exists_choose_gt
      dom k a S
      ⟨u₀, u₁, hnotEligible, hsafe, c, hc, by
        simpa [hsupport, hzero] using hgt⟩

open Classical in
/-- Lower-support form of the obstruction.  If a concrete appearing codeword has at least `s`
moving coordinates and zero-agreement size `z`, then `choose(s, a - z)` is a necessary lower
bound for any uniform support-choose cap. -/
theorem
    not_uniformLargeZeroSafeCodewordSupportChooseBudgeted_of_exists_support_lower_choose_gt
    (dom : Fin n ↪ F) (k a S : ℕ)
    (hgt : ∃ u₀ u₁ c : Fin n → F, ∃ s z : ℕ,
      ¬ SupportEligibleLineDirection a u₁ ∧
        ZeroDirectionSafeLine dom k a u₀ u₁ ∧
          c ∈ lineAppearingCodewords dom k a u₀ u₁ ∧
            s ≤ (directionSupportSet u₁).card ∧
              (directionZeroAgreementSet c u₀ u₁).card = z ∧
                S < s.choose (a - z)) :
    ¬ UniformLargeZeroSafeCodewordSupportChooseBudgeted dom k a S := by
  rcases hgt with
    ⟨u₀, u₁, c, s, z, hnotEligible, hsafe, hc, hsupport, hzero, hgt⟩
  have hmono :
      s.choose (a - z) ≤
        (directionSupportSet u₁).card.choose (a - z) :=
    Nat.choose_le_choose (a - z) hsupport
  exact
    not_uniformLargeZeroSafeCodewordSupportChooseBudgeted_of_exists_choose_gt
      dom k a S
      ⟨u₀, u₁, hnotEligible, hsafe, c, hc, by
        exact lt_of_lt_of_le hgt (by simpa [hzero] using hmono)⟩

open Classical in
/-- A failed uniform support-choose budget yields the same obstruction with named support and
zero-agreement profile parameters. -/
theorem exists_codewordSupportChooseProfile_gt_of_not_uniformLargeZeroSafeBudgeted
    (dom : Fin n ↪ F) (k a S : ℕ)
    (hnot : ¬ UniformLargeZeroSafeCodewordSupportChooseBudgeted dom k a S) :
    ∃ u₀ u₁ c : Fin n → F, ∃ s z : ℕ,
      ¬ SupportEligibleLineDirection a u₁ ∧
        ZeroDirectionSafeLine dom k a u₀ u₁ ∧
          c ∈ lineAppearingCodewords dom k a u₀ u₁ ∧
            (directionSupportSet u₁).card = s ∧
              (directionZeroAgreementSet c u₀ u₁).card = z ∧
                S < s.choose (a - z) := by
  rcases
      (not_uniformLargeZeroSafeCodewordSupportChooseBudgeted_iff_exists_choose_gt
        dom k a S).mp hnot with
    ⟨u₀, u₁, hnotEligible, hsafe, c, hc, hgt⟩
  exact
    ⟨u₀, u₁, c, (directionSupportSet u₁).card,
      (directionZeroAgreementSet c u₀ u₁).card, hnotEligible, hsafe, hc, rfl, rfl, by
        simpa using hgt⟩

open Classical in
/-- Scanner-facing profile form for the support-choose route.  Once support-side hypotheses are
fixed, failed production forces either the usual combined arithmetic failure or an appearing
codeword whose named support/zero-agreement profile is already over the proposed support-choose
cap. -/
theorem exists_largeZero_safe_codewordSupportChooseRouteProfileFailure_of_not_budgeted
    (dom : Fin n ↪ F) (k a L S B : ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hnot : ¬ UniformLineBadScalarsBudgeted dom k a B) :
    ∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
      ZeroDirectionSafeLine dom k a u₀ u₁ ∧
        (¬ puncturedZeroStratifiedLineWeight dom k a u₀ u₁
            + (lineAppearingCodewords dom k a u₀ u₁).card * S ≤ 2 * B ∨
          ∃ c ∈ lineAppearingCodewords dom k a u₀ u₁, ∃ s z : ℕ,
            (directionSupportSet u₁).card = s ∧
              (directionZeroAgreementSet c u₀ u₁).card = z ∧
                S < s.choose (a - z)) := by
  rcases
      exists_largeZero_safe_codewordSupportChooseRouteFailure_of_not_budgeted
        dom k a L S B hSupport hFits hZeroSafe hnot with
    ⟨u₀, u₁, hnotEligible, hsafe, hfail | hgt⟩
  · exact ⟨u₀, u₁, hnotEligible, hsafe, Or.inl hfail⟩
  · rcases hgt with ⟨c, hc, hgt⟩
    exact
      ⟨u₀, u₁, hnotEligible, hsafe, Or.inr
        ⟨c, hc, (directionSupportSet u₁).card,
          (directionZeroAgreementSet c u₀ u₁).card, rfl, rfl, by simpa using hgt⟩⟩

section SourceAudit

#print axioms codewordSupportChooseBudget_term_le
#print axioms not_uniformLargeZeroSafeCodewordSupportChooseBudgeted_of_exists_choose_gt
#print axioms
  not_uniformLargeZeroSafeCodewordSupportChooseBudgeted_of_exists_profile_choose_gt
#print axioms
  not_uniformLargeZeroSafeCodewordSupportChooseBudgeted_of_exists_support_lower_choose_gt
#print axioms exists_codewordSupportChooseProfile_gt_of_not_uniformLargeZeroSafeBudgeted
#print axioms
  exists_largeZero_safe_codewordSupportChooseRouteProfileFailure_of_not_budgeted

end SourceAudit

end ProximityGap.Ownership
