/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LineListAppearanceFiberMixedProfile

/-!
# Named mixed-profile fit consumers

`LineListAppearanceFiberMixedProfile.lean` defines the low mixed choose-profile arithmetic fit and
its expanded production wrappers.  This file keeps the named-fit consumer layer separate so the
base mixed-profile module stays focused and under the local line-count cap.
-/

set_option autoImplicit false

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- Named-fit version of
`uniformLargeZeroSafeLowAppearingCoordinateFiberBudgeted_of_lowExact_mixedChooseProfileSums`.
The mixed choose-profile arithmetic obligation is packaged as
`UniformLargeZeroSafeLowMixedChooseProfileSumsFit`. -/
theorem
    uniformLargeZeroSafeLowAppearingCoordinateFiberBudgeted_of_lowExact_mixedChooseProfileSumsFit
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a : ℕ)
    (Mexact Mcoarse : ℕ → ℕ)
    (hExactLow :
      UniformLargeZeroSafeLowExactAppearingZeroAgreementFiberBudgeted dom k a Mexact)
    (hFit : UniformLargeZeroSafeLowMixedChooseProfileSumsFit dom k a Mexact Mcoarse) :
    UniformLargeZeroSafeLowAppearingCoordinateFiberBudgeted dom k a Mcoarse :=
  uniformLargeZeroSafeLowAppearingCoordinateFiberBudgeted_of_lowExact_mixedChooseProfileSums
    dom hk a Mexact Mcoarse hExactLow
    (by
      intro u₀ u₁ hnotEligible hsafe
      exact hFit u₀ u₁ hnotEligible hsafe)

open Classical in
/-- Production wrapper whose arithmetic side condition is the named low mixed choose-profile fit.
Failure of this named fit is now the explicit arithmetic residual of the low-exact route. -/
theorem uniformLineBadScalarsBudgeted_of_lowExact_mixedChooseProfileSumsFit
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a L B : ℕ)
    (Mexact Mcoarse : ℕ → ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hExactLow :
      UniformLargeZeroSafeLowExactAppearingZeroAgreementFiberBudgeted dom k a Mexact)
    (hProfileFit :
      UniformLargeZeroSafeLowMixedChooseProfileSumsFit dom k a Mexact Mcoarse)
    (hHigh : ∀ t : ℕ, t < a → k ≤ t → 1 ≤ Mcoarse t)
    (hFiberFits :
      UniformLargeZeroSafeAppearingCoordinateFiberBudgetFits (F := F) (n := n) a B Mcoarse) :
    UniformLineBadScalarsBudgeted dom k a B :=
  uniformLineBadScalarsBudgeted_of_lowExact_mixedChooseProfileSums
    dom hk a L B Mexact Mcoarse hSupport hFits hZeroSafe hExactLow
    (by
      intro u₀ u₁ hnotEligible hsafe
      exact hProfileFit u₀ u₁ hnotEligible hsafe)
    hHigh hFiberFits

open Classical in
/-- With support-side production, zero-direction safety, low exact-profile estimates, high
singleton ceilings, and weighted coarse fits fixed, failed bad-scalar production refutes the
named low mixed choose-profile fit. -/
theorem not_uniformLowMixedChooseProfileSumsFit_of_not_uniformLineBadScalarsBudgeted
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a L B : ℕ)
    (Mexact Mcoarse : ℕ → ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hExactLow :
      UniformLargeZeroSafeLowExactAppearingZeroAgreementFiberBudgeted dom k a Mexact)
    (hHigh : ∀ t : ℕ, t < a → k ≤ t → 1 ≤ Mcoarse t)
    (hFiberFits :
      UniformLargeZeroSafeAppearingCoordinateFiberBudgetFits (F := F) (n := n) a B Mcoarse)
    (hnot : ¬ UniformLineBadScalarsBudgeted dom k a B) :
    ¬ UniformLargeZeroSafeLowMixedChooseProfileSumsFit dom k a Mexact Mcoarse := by
  intro hProfileFit
  exact hnot
    (uniformLineBadScalarsBudgeted_of_lowExact_mixedChooseProfileSumsFit
      dom hk a L B Mexact Mcoarse hSupport hFits hZeroSafe hExactLow hProfileFit
      hHigh hFiberFits)

open Classical in
/-- Scanner-facing named residual.  Without assuming zero-direction safety up front, failed
bad-scalar production exposes either zero-direction saturation or failure of the named low mixed
choose-profile fit. -/
theorem unsafe_or_not_uniformLowMixedChooseProfileSumsFit_of_not_budgeted
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a L B : ℕ)
    (Mexact Mcoarse : ℕ → ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hExactLow :
      UniformLargeZeroSafeLowExactAppearingZeroAgreementFiberBudgeted dom k a Mexact)
    (hHigh : ∀ t : ℕ, t < a → k ≤ t → 1 ≤ Mcoarse t)
    (hFiberFits :
      UniformLargeZeroSafeAppearingCoordinateFiberBudgetFits (F := F) (n := n) a B Mcoarse)
    (hnot : ¬ UniformLineBadScalarsBudgeted dom k a B) :
    (∃ u₀ u₁ c : Fin n → F, c ∈ (rsCode dom k : Submodule F (Fin n → F)) ∧
        a ≤ (directionZeroAgreementSet c u₀ u₁).card) ∨
      ¬ UniformLargeZeroSafeLowMixedChooseProfileSumsFit dom k a Mexact Mcoarse := by
  by_cases hZeroSafe : UniformZeroDirectionSafe dom k a
  · exact Or.inr
      (not_uniformLowMixedChooseProfileSumsFit_of_not_uniformLineBadScalarsBudgeted
        dom hk a L B Mexact Mcoarse hSupport hFits hZeroSafe hExactLow hHigh
        hFiberFits hnot)
  · exact Or.inl
      ((not_uniformZeroDirectionSafe_iff_exists_line_codeword_zeroAgreement_ge
        dom k a).mp hZeroSafe)

omit [Field F] [DecidableEq F] [NeZero n] in
/-- The field-power mixed-profile card sum is monotone in `z`; the worst cardinality is `z = n`. -/
theorem fieldPowMixedProfileCardSum_le_topCard
    (a k z t : ℕ) (hz : z ≤ n) :
    fieldPowMixedProfileCardSum (F := F) n a k z t ≤
      fieldPowMixedProfileCardSum (F := F) n a k n t := by
  let Mexact : ℕ → ℕ :=
    fun r => Fintype.card F * (n.choose (a - r) * Fintype.card F ^ (k - a))
  simpa [fieldPowMixedProfileCardSum, Mexact] using
    mixedChooseProfileCardSum_le_topCard (n := n) a k t z Mexact hz

omit [Field F] [DecidableEq F] [NeZero n] in
/-- Pure top-cardinality arithmetic fit for the low field-power mixed-profile sums. -/
def FieldPowMixedProfileTopFit (a k : ℕ) (Mcoarse : ℕ → ℕ) : Prop :=
  ∀ t : ℕ, t < a → t < k →
    fieldPowMixedProfileCardSum (F := F) n a k n t ≤ Mcoarse t

omit [Field F] [DecidableEq F] [NeZero n] in
/-- Pure top-cardinality arithmetic fit for the full field-power mixed-profile sums. -/
def FieldPowFullMixedProfileTopFit (a k : ℕ) (Mcoarse : ℕ → ℕ) : Prop :=
  ∀ t : ℕ, t < a →
    fieldPowMixedProfileCardSum (F := F) n a k n t ≤ Mcoarse t

omit [Field F] [DecidableEq F] [NeZero n] in
open Classical in
/-- Exact failure form for the low top-cardinality field-power mixed-profile fit. -/
theorem not_fieldPowMixedProfileTopFit_iff_exists_sum_gt
    (a k : ℕ) (Mcoarse : ℕ → ℕ) :
    (¬ FieldPowMixedProfileTopFit (F := F) (n := n) a k Mcoarse) ↔
      ∃ t : ℕ, t < a ∧ t < k ∧
        Mcoarse t < fieldPowMixedProfileCardSum (F := F) n a k n t := by
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro t ht htk
    exact le_of_not_gt (fun hgt => hnone ⟨t, ht, htk, hgt⟩)
  · rintro ⟨t, ht, htk, hgt⟩ hFit
    exact not_lt_of_ge (hFit t ht htk) hgt

omit [Field F] [DecidableEq F] [NeZero n] in
open Classical in
/-- Exact failure form for the full top-cardinality field-power mixed-profile fit. -/
theorem not_fieldPowFullMixedProfileTopFit_iff_exists_sum_gt
    (a k : ℕ) (Mcoarse : ℕ → ℕ) :
    (¬ FieldPowFullMixedProfileTopFit (F := F) (n := n) a k Mcoarse) ↔
      ∃ t : ℕ, t < a ∧
        Mcoarse t < fieldPowMixedProfileCardSum (F := F) n a k n t := by
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro t ht
    exact le_of_not_gt (fun hgt => hnone ⟨t, ht, hgt⟩)
  · rintro ⟨t, ht, hgt⟩ hFit
    exact not_lt_of_ge (hFit t ht) hgt

open Classical in
/-- Named top-fit wrapper for the low field-power mixed route. -/
theorem uniformLineBadScalarsBudgeted_of_fieldPow_mixedProfileTopFit
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a L B : ℕ) (Mcoarse : ℕ → ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hProfileTop : FieldPowMixedProfileTopFit (F := F) (n := n) a k Mcoarse)
    (hHigh : ∀ t : ℕ, t < a → k ≤ t → 1 ≤ Mcoarse t)
    (hFiberFits :
      UniformLargeZeroSafeAppearingCoordinateFiberBudgetFits (F := F) (n := n) a B Mcoarse) :
    UniformLineBadScalarsBudgeted dom k a B :=
  uniformLineBadScalarsBudgeted_of_fieldPow_mixedProfileCardSums
    dom hk a L B Mcoarse hSupport hFits hZeroSafe
    (by
      intro z t _hzlo hzhi ht htk
      have hle := fieldPowMixedProfileCardSum_le_topCard
        (F := F) (n := n) a k z t hzhi
      simpa [fieldPowMixedProfileCardSum] using le_trans hle (hProfileTop t ht htk))
    hHigh hFiberFits

open Classical in
/-- Scanner-facing top-fit version of the low field-power mixed route. -/
theorem unsafe_or_not_fieldPow_mixedProfileTopFit_of_not_budgeted
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a L B : ℕ) (Mcoarse : ℕ → ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hHigh : ∀ t : ℕ, t < a → k ≤ t → 1 ≤ Mcoarse t)
    (hFiberFits :
      UniformLargeZeroSafeAppearingCoordinateFiberBudgetFits (F := F) (n := n) a B Mcoarse)
    (hnot : ¬ UniformLineBadScalarsBudgeted dom k a B) :
    (∃ u₀ u₁ c : Fin n → F, c ∈ (rsCode dom k : Submodule F (Fin n → F)) ∧
        a ≤ (directionZeroAgreementSet c u₀ u₁).card) ∨
      ¬ FieldPowMixedProfileTopFit (F := F) (n := n) a k Mcoarse := by
  rcases
      (unsafe_or_largeZero_safe_fieldPow_mixedProfileCard_gt_of_not_budgeted
        dom hk a L B Mcoarse hSupport hFits hHigh hFiberFits hnot) with
    hUnsafe | hProfile
  · exact Or.inl hUnsafe
  · rcases hProfile with ⟨u₁, _hnotEligible, _hzlo, hzhi, t, ht, htk, hgt⟩
    have hle := fieldPowMixedProfileCardSum_le_topCard
      (F := F) (n := n) a k (directionZeroSet u₁).card t hzhi
    exact Or.inr
      ((not_fieldPowMixedProfileTopFit_iff_exists_sum_gt
        (F := F) (n := n) a k Mcoarse).mpr
        ⟨t, ht, htk, lt_of_lt_of_le
          (by simpa [fieldPowMixedProfileCardSum] using hgt) hle⟩)

open Classical in
/-- Named top-fit wrapper for the full field-power mixed route. -/
theorem uniformLineBadScalarsBudgeted_of_fieldPow_fullMixedProfileTopFit
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a L B : ℕ) (Mcoarse : ℕ → ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hProfileTop : FieldPowFullMixedProfileTopFit (F := F) (n := n) a k Mcoarse)
    (hFiberFits :
      UniformLargeZeroSafeAppearingCoordinateFiberBudgetFits (F := F) (n := n) a B Mcoarse) :
    UniformLineBadScalarsBudgeted dom k a B :=
  uniformLineBadScalarsBudgeted_of_fieldPow_fullMixedProfileCardSums
    dom hk a L B Mcoarse hSupport hFits hZeroSafe
    (by
      intro z t _hzlo hzhi ht
      have hle := fieldPowMixedProfileCardSum_le_topCard
        (F := F) (n := n) a k z t hzhi
      simpa [fieldPowMixedProfileCardSum] using le_trans hle (hProfileTop t ht))
    hFiberFits

open Classical in
/-- Scanner-facing top-fit version of the full field-power mixed route. -/
theorem unsafe_or_not_fieldPow_fullMixedProfileTopFit_of_not_budgeted
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a L B : ℕ) (Mcoarse : ℕ → ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hFiberFits :
      UniformLargeZeroSafeAppearingCoordinateFiberBudgetFits (F := F) (n := n) a B Mcoarse)
    (hnot : ¬ UniformLineBadScalarsBudgeted dom k a B) :
    (∃ u₀ u₁ c : Fin n → F, c ∈ (rsCode dom k : Submodule F (Fin n → F)) ∧
        a ≤ (directionZeroAgreementSet c u₀ u₁).card) ∨
      ¬ FieldPowFullMixedProfileTopFit (F := F) (n := n) a k Mcoarse := by
  rcases
      (unsafe_or_largeZero_safe_fieldPow_fullMixedProfileCard_gt_of_not_budgeted
        dom hk a L B Mcoarse hSupport hFits hFiberFits hnot) with
    hUnsafe | hProfile
  · exact Or.inl hUnsafe
  · rcases hProfile with ⟨u₁, _hnotEligible, _hzlo, hzhi, t, ht, hgt⟩
    have hle := fieldPowMixedProfileCardSum_le_topCard
      (F := F) (n := n) a k (directionZeroSet u₁).card t hzhi
    exact Or.inr
      ((not_fieldPowFullMixedProfileTopFit_iff_exists_sum_gt
        (F := F) (n := n) a k Mcoarse).mpr
        ⟨t, ht, lt_of_lt_of_le (by simpa [fieldPowMixedProfileCardSum] using hgt) hle⟩)

section SourceAudit

#print axioms
  uniformLargeZeroSafeLowAppearingCoordinateFiberBudgeted_of_lowExact_mixedChooseProfileSumsFit
#print axioms uniformLineBadScalarsBudgeted_of_lowExact_mixedChooseProfileSumsFit
#print axioms not_uniformLowMixedChooseProfileSumsFit_of_not_uniformLineBadScalarsBudgeted
#print axioms unsafe_or_not_uniformLowMixedChooseProfileSumsFit_of_not_budgeted
#print axioms fieldPowMixedProfileCardSum_le_topCard
#print axioms FieldPowMixedProfileTopFit
#print axioms FieldPowFullMixedProfileTopFit
#print axioms not_fieldPowMixedProfileTopFit_iff_exists_sum_gt
#print axioms not_fieldPowFullMixedProfileTopFit_iff_exists_sum_gt
#print axioms uniformLineBadScalarsBudgeted_of_fieldPow_mixedProfileTopFit
#print axioms unsafe_or_not_fieldPow_mixedProfileTopFit_of_not_budgeted
#print axioms uniformLineBadScalarsBudgeted_of_fieldPow_fullMixedProfileTopFit
#print axioms unsafe_or_not_fieldPow_fullMixedProfileTopFit_of_not_budgeted

end SourceAudit

end ProximityGap.Ownership
