/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LineListCodewordSingletonSupportDivWeight

/-!
# Arithmetic obstruction for the weighted denominator baseline

`LineListCodewordSingletonSupportDivWeight.lean` packages the scalar-sharp denominator baseline

```text
sum_{c appearing} #support(u₁) / (a - #zeroAgreement(c,u₀,u₁)).
```

This file records the one-term obstruction surface.  If one appearing codeword already makes

```text
2B < puncturedWeight + #support(u₁) / (a - #zeroAgreement(c,u₀,u₁)),
```

then the uniform weighted denominator budget cannot hold.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- Every appearing-codeword denominator term is bounded by the weighted denominator sum. -/
theorem codewordSupportDivWeight_term_le
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ c : Fin n → F)
    (hc : c ∈ lineAppearingCodewords dom k a u₀ u₁) :
    (directionSupportSet u₁).card /
        (a - (directionZeroAgreementSet c u₀ u₁).card)
      ≤ codewordSupportDivWeight dom k a u₀ u₁ := by
  rw [codewordSupportDivWeight]
  exact Finset.single_le_sum
    (f := fun c =>
      (directionSupportSet u₁).card /
        (a - (directionZeroAgreementSet c u₀ u₁).card))
    (fun _ _ => Nat.zero_le _) hc

open Classical in
/-- A single over-budget denominator term refutes the uniform weighted denominator budget. -/
theorem not_uniformLargeZeroSafeWeightPlusCodewordSupportDivBudgeted_of_exists_term_gt
    (dom : Fin n ↪ F) (k a B : ℕ)
    (hgt : ∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
      ZeroDirectionSafeLine dom k a u₀ u₁ ∧
        ∃ c ∈ lineAppearingCodewords dom k a u₀ u₁,
          2 * B < puncturedZeroStratifiedLineWeight dom k a u₀ u₁
            + (directionSupportSet u₁).card /
              (a - (directionZeroAgreementSet c u₀ u₁).card)) :
    ¬ UniformLargeZeroSafeWeightPlusCodewordSupportDivBudgeted dom k a B := by
  rintro hbudget
  rcases hgt with ⟨u₀, u₁, hnotEligible, hsafe, c, hc, hgt⟩
  have hterm := codewordSupportDivWeight_term_le dom k a u₀ u₁ c hc
  exact
    (not_lt_of_ge
      ((Nat.add_le_add_left hterm
        (puncturedZeroStratifiedLineWeight dom k a u₀ u₁)).trans
          (hbudget u₀ u₁ hnotEligible hsafe)))
      hgt

open Classical in
/-- Exact-profile form of the one-term denominator obstruction. -/
theorem
    not_uniformLargeZeroSafeWeightPlusCodewordSupportDivBudgeted_of_exists_profile_term_gt
    (dom : Fin n ↪ F) (k a B : ℕ)
    (hgt : ∃ u₀ u₁ c : Fin n → F, ∃ s z : ℕ,
      ¬ SupportEligibleLineDirection a u₁ ∧
        ZeroDirectionSafeLine dom k a u₀ u₁ ∧
          c ∈ lineAppearingCodewords dom k a u₀ u₁ ∧
            (directionSupportSet u₁).card = s ∧
              (directionZeroAgreementSet c u₀ u₁).card = z ∧
                2 * B < puncturedZeroStratifiedLineWeight dom k a u₀ u₁
                  + s / (a - z)) :
    ¬ UniformLargeZeroSafeWeightPlusCodewordSupportDivBudgeted dom k a B := by
  rcases hgt with
    ⟨u₀, u₁, c, s, z, hnotEligible, hsafe, hc, hsupport, hzero, hgt⟩
  exact
    not_uniformLargeZeroSafeWeightPlusCodewordSupportDivBudgeted_of_exists_term_gt
      dom k a B
      ⟨u₀, u₁, hnotEligible, hsafe, c, hc, by
        simpa [hsupport, hzero] using hgt⟩

open Classical in
/-- Lower-support form of the denominator obstruction.  If the moving support has size at least
`s`, then the single denominator term is at least `s / (a - z)`. -/
theorem
    not_uniformLargeZeroSafeWeightPlusCodewordSupportDivBudgeted_of_exists_support_lower_term_gt
    (dom : Fin n ↪ F) (k a B : ℕ)
    (hgt : ∃ u₀ u₁ c : Fin n → F, ∃ s z : ℕ,
      ¬ SupportEligibleLineDirection a u₁ ∧
        ZeroDirectionSafeLine dom k a u₀ u₁ ∧
          c ∈ lineAppearingCodewords dom k a u₀ u₁ ∧
            s ≤ (directionSupportSet u₁).card ∧
              (directionZeroAgreementSet c u₀ u₁).card = z ∧
                2 * B < puncturedZeroStratifiedLineWeight dom k a u₀ u₁
                  + s / (a - z)) :
    ¬ UniformLargeZeroSafeWeightPlusCodewordSupportDivBudgeted dom k a B := by
  rcases hgt with
    ⟨u₀, u₁, c, s, z, hnotEligible, hsafe, hc, hsupport, hzero, hgt⟩
  have hmono :
      s / (a - z) ≤
        (directionSupportSet u₁).card / (a - z) :=
    Nat.div_le_div_right hsupport
  exact
    not_uniformLargeZeroSafeWeightPlusCodewordSupportDivBudgeted_of_exists_term_gt
      dom k a B
      ⟨u₀, u₁, hnotEligible, hsafe, c, hc, by
        exact lt_of_lt_of_le hgt (by
          exact Nat.add_le_add_left (by simpa [hzero] using hmono)
            (puncturedZeroStratifiedLineWeight dom k a u₀ u₁))⟩

section SourceAudit

#print axioms codewordSupportDivWeight_term_le
#print axioms
  not_uniformLargeZeroSafeWeightPlusCodewordSupportDivBudgeted_of_exists_term_gt
#print axioms
  not_uniformLargeZeroSafeWeightPlusCodewordSupportDivBudgeted_of_exists_profile_term_gt
#print axioms
  not_uniformLargeZeroSafeWeightPlusCodewordSupportDivBudgeted_of_exists_support_lower_term_gt

end SourceAudit

end ProximityGap.Ownership
