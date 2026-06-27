/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LineListAppearanceFiberMixedProfileFit
import ArkLib.Data.CodingTheory.ProximityGap.LineListSupportRatioFiber

/-!
# Support-ratio inputs for mixed exact-profile budgets

`LineListSupportRatioFiber.lean` proves that low support-ratio-heavy coordinate-fiber budgets
feed the low exact appearance-fiber socket.  `LineListAppearanceFiberMixedProfile.lean` consumes
that socket and sums low exact profiles against a mixed high-profile singleton ceiling.  This file
records the direct composition, so scanner users can work with support-ratio budgets without
manually translating them through exact appearance fibers.
-/

set_option autoImplicit false

open Finset

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- Production wrapper for the low support-ratio-heavy route into the mixed low-exact/high
singleton choose-profile consumer. -/
theorem uniformLineBadScalarsBudgeted_of_lowSupportRatioHeavy_mixedChooseProfileSums
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a L B : ℕ)
    (Mheavy Mcoarse : ℕ → ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hHeavyLow :
      UniformLargeZeroSafeLowSupportRatioHeavyCoordinateFiberBudgeted dom k a Mheavy)
    (hProfile :
      ∀ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
        ZeroDirectionSafeLine dom k a u₀ u₁ →
          ∀ t : ℕ, t < a → t < k →
            ∀ S ∈ (directionZeroSet u₁).powersetCard t,
              (∑ r ∈ Finset.range a,
                ((directionZeroSet u₁).card - t).choose (r - t) *
                  (if r < k then Mheavy r else 1)) ≤ Mcoarse t)
    (hHigh : ∀ t : ℕ, t < a → k ≤ t → 1 ≤ Mcoarse t)
    (hFiberFits :
      UniformLargeZeroSafeAppearingCoordinateFiberBudgetFits (F := F) (n := n) a B Mcoarse) :
    UniformLineBadScalarsBudgeted dom k a B :=
  uniformLineBadScalarsBudgeted_of_lowExact_mixedChooseProfileSums
    dom hk a L B Mheavy Mcoarse hSupport hFits hZeroSafe
    (uniformLargeZeroSafeLowExactAppearingZeroAgreementFiberBudgeted_of_lowSupportRatioHeavyBudgeted
      dom k a Mheavy hHeavyLow)
    hProfile hHigh hFiberFits

open Classical in
/-- Named-fit version of
`uniformLineBadScalarsBudgeted_of_lowSupportRatioHeavy_mixedChooseProfileSums`.  The low
support-ratio-heavy route now consumes the same named mixed arithmetic residual as the low-exact
route. -/
theorem uniformLineBadScalarsBudgeted_of_lowSupportRatioHeavy_mixedChooseProfileSumsFit
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a L B : ℕ)
    (Mheavy Mcoarse : ℕ → ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hHeavyLow :
      UniformLargeZeroSafeLowSupportRatioHeavyCoordinateFiberBudgeted dom k a Mheavy)
    (hProfileFit :
      UniformLargeZeroSafeLowMixedChooseProfileSumsFit dom k a Mheavy Mcoarse)
    (hHigh : ∀ t : ℕ, t < a → k ≤ t → 1 ≤ Mcoarse t)
    (hFiberFits :
      UniformLargeZeroSafeAppearingCoordinateFiberBudgetFits (F := F) (n := n) a B Mcoarse) :
    UniformLineBadScalarsBudgeted dom k a B :=
  uniformLineBadScalarsBudgeted_of_lowExact_mixedChooseProfileSumsFit
    dom hk a L B Mheavy Mcoarse hSupport hFits hZeroSafe
    (uniformLargeZeroSafeLowExactAppearingZeroAgreementFiberBudgeted_of_lowSupportRatioHeavyBudgeted
      dom k a Mheavy hHeavyLow)
    hProfileFit hHigh hFiberFits

open Classical in
/-- Scanner-facing named residual with support-ratio-heavy inputs.  Failed bad-scalar production
exposes either zero-direction saturation or failure of the named mixed profile fit. -/
theorem unsafe_or_not_uniformLowSupportRatioMixedChooseProfileSumsFit_of_not_budgeted
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a L B : ℕ)
    (Mheavy Mcoarse : ℕ → ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hHeavyLow :
      UniformLargeZeroSafeLowSupportRatioHeavyCoordinateFiberBudgeted dom k a Mheavy)
    (hHigh : ∀ t : ℕ, t < a → k ≤ t → 1 ≤ Mcoarse t)
    (hFiberFits :
      UniformLargeZeroSafeAppearingCoordinateFiberBudgetFits (F := F) (n := n) a B Mcoarse)
    (hnot : ¬ UniformLineBadScalarsBudgeted dom k a B) :
    (∃ u₀ u₁ c : Fin n → F, c ∈ (rsCode dom k : Submodule F (Fin n → F)) ∧
        a ≤ (directionZeroAgreementSet c u₀ u₁).card) ∨
      ¬ UniformLargeZeroSafeLowMixedChooseProfileSumsFit dom k a Mheavy Mcoarse :=
  unsafe_or_not_uniformLowMixedChooseProfileSumsFit_of_not_budgeted
    dom hk a L B Mheavy Mcoarse hSupport hFits
    (uniformLargeZeroSafeLowExactAppearingZeroAgreementFiberBudgeted_of_lowSupportRatioHeavyBudgeted
      dom k a Mheavy hHeavyLow)
    hHigh hFiberFits hnot

open Classical in
/-- Scanner-facing low mixed-profile residual with support-ratio-heavy inputs.  Failure exposes
zero-direction saturation or a concrete mixed choose-profile overrun. -/
theorem unsafe_or_largeZero_safe_low_supportRatioMixedChooseProfile_gt_of_not_budgeted
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a L B : ℕ)
    (Mheavy Mcoarse : ℕ → ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hHeavyLow :
      UniformLargeZeroSafeLowSupportRatioHeavyCoordinateFiberBudgeted dom k a Mheavy)
    (hHigh : ∀ t : ℕ, t < a → k ≤ t → 1 ≤ Mcoarse t)
    (hFiberFits :
      UniformLargeZeroSafeAppearingCoordinateFiberBudgetFits (F := F) (n := n) a B Mcoarse)
    (hnot : ¬ UniformLineBadScalarsBudgeted dom k a B) :
    (∃ u₀ u₁ c : Fin n → F, c ∈ (rsCode dom k : Submodule F (Fin n → F)) ∧
        a ≤ (directionZeroAgreementSet c u₀ u₁).card) ∨
      (∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
        ZeroDirectionSafeLine dom k a u₀ u₁ ∧
          ∃ t : ℕ, t < a ∧ t < k ∧ ∃ S : Finset (Fin n),
            S ∈ (directionZeroSet u₁).powersetCard t ∧
            Mcoarse t <
              ∑ r ∈ Finset.range a,
                ((directionZeroSet u₁).card - t).choose (r - t) *
                  (if r < k then Mheavy r else 1)) :=
  unsafe_or_largeZero_safe_low_mixedChooseProfile_gt_of_not_uniformLineBadScalarsBudgeted
    dom hk a L B Mheavy Mcoarse hSupport hFits
    (uniformLargeZeroSafeLowExactAppearingZeroAgreementFiberBudgeted_of_lowSupportRatioHeavyBudgeted
      dom k a Mheavy hHeavyLow)
    hHigh hFiberFits hnot

open Classical in
/-- Production wrapper for the full mixed choose-profile consumer with low support-ratio-heavy
inputs.  The caller pays the mixed profile for every coarse zero profile `t < a`. -/
theorem uniformLineBadScalarsBudgeted_of_lowSupportRatioHeavy_fullMixedChooseProfileSums
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a L B : ℕ)
    (Mheavy Mcoarse : ℕ → ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hHeavyLow :
      UniformLargeZeroSafeLowSupportRatioHeavyCoordinateFiberBudgeted dom k a Mheavy)
    (hProfile :
      ∀ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
        ZeroDirectionSafeLine dom k a u₀ u₁ →
          ∀ t : ℕ, t < a → ∀ S ∈ (directionZeroSet u₁).powersetCard t,
            (∑ r ∈ Finset.range a,
              ((directionZeroSet u₁).card - t).choose (r - t) *
                (if r < k then Mheavy r else 1)) ≤ Mcoarse t)
    (hFiberFits :
      UniformLargeZeroSafeAppearingCoordinateFiberBudgetFits (F := F) (n := n) a B Mcoarse) :
    UniformLineBadScalarsBudgeted dom k a B :=
  uniformLineBadScalarsBudgeted_of_lowExact_fullMixedChooseProfileSums
    dom hk a L B Mheavy Mcoarse hSupport hFits hZeroSafe
    (uniformLargeZeroSafeLowExactAppearingZeroAgreementFiberBudgeted_of_lowSupportRatioHeavyBudgeted
      dom k a Mheavy hHeavyLow)
    hProfile hFiberFits

open Classical in
/-- Scanner-facing full mixed-profile residual with support-ratio-heavy inputs. -/
theorem unsafe_or_largeZero_safe_fullSupportRatioMixedChooseProfile_gt_of_not_budgeted
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a L B : ℕ)
    (Mheavy Mcoarse : ℕ → ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hHeavyLow :
      UniformLargeZeroSafeLowSupportRatioHeavyCoordinateFiberBudgeted dom k a Mheavy)
    (hFiberFits :
      UniformLargeZeroSafeAppearingCoordinateFiberBudgetFits (F := F) (n := n) a B Mcoarse)
    (hnot : ¬ UniformLineBadScalarsBudgeted dom k a B) :
    (∃ u₀ u₁ c : Fin n → F, c ∈ (rsCode dom k : Submodule F (Fin n → F)) ∧
        a ≤ (directionZeroAgreementSet c u₀ u₁).card) ∨
      (∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
        ZeroDirectionSafeLine dom k a u₀ u₁ ∧
          ∃ t : ℕ, t < a ∧ ∃ S : Finset (Fin n),
            S ∈ (directionZeroSet u₁).powersetCard t ∧
            Mcoarse t <
              ∑ r ∈ Finset.range a,
                ((directionZeroSet u₁).card - t).choose (r - t) *
                  (if r < k then Mheavy r else 1)) :=
  unsafe_or_largeZero_safe_fullMixedChooseProfile_gt_of_not_uniformLineBadScalarsBudgeted
    dom hk a L B Mheavy Mcoarse hSupport hFits
    (uniformLargeZeroSafeLowExactAppearingZeroAgreementFiberBudgeted_of_lowSupportRatioHeavyBudgeted
      dom k a Mheavy hHeavyLow)
    hFiberFits hnot

open Classical in
/-- Cardinal-profile version of
`uniformLineBadScalarsBudgeted_of_lowSupportRatioHeavy_mixedChooseProfileSums`.  It keeps the
low support-ratio-heavy budget abstract while reducing the mixed exact-superset arithmetic to
cardinalities `z = #zeroSet(u₁)`. -/
theorem uniformLineBadScalarsBudgeted_of_lowSupportRatioHeavy_mixedChooseProfileCardSums
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a L B : ℕ)
    (Mheavy Mcoarse : ℕ → ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hHeavyLow :
      UniformLargeZeroSafeLowSupportRatioHeavyCoordinateFiberBudgeted dom k a Mheavy)
    (hProfileCard :
      ∀ z t : ℕ, a ≤ z → z ≤ n → t < a → t < k →
        (∑ r ∈ Finset.range a,
          (z - t).choose (r - t) * (if r < k then Mheavy r else 1)) ≤ Mcoarse t)
    (hHigh : ∀ t : ℕ, t < a → k ≤ t → 1 ≤ Mcoarse t)
    (hFiberFits :
      UniformLargeZeroSafeAppearingCoordinateFiberBudgetFits (F := F) (n := n) a B Mcoarse) :
    UniformLineBadScalarsBudgeted dom k a B :=
  uniformLineBadScalarsBudgeted_of_lowExact_mixedChooseProfileCardSums
    dom hk a L B Mheavy Mcoarse hSupport hFits hZeroSafe
    (uniformLargeZeroSafeLowExactAppearingZeroAgreementFiberBudgeted_of_lowSupportRatioHeavyBudgeted
      dom k a Mheavy hHeavyLow)
    hProfileCard hHigh hFiberFits

open Classical in
/-- Scanner-facing cardinal-profile residual with abstract low support-ratio-heavy inputs. -/
theorem unsafe_or_largeZero_safe_low_supportRatioMixedChooseProfileCard_gt_of_not_budgeted
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a L B : ℕ)
    (Mheavy Mcoarse : ℕ → ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hHeavyLow :
      UniformLargeZeroSafeLowSupportRatioHeavyCoordinateFiberBudgeted dom k a Mheavy)
    (hHigh : ∀ t : ℕ, t < a → k ≤ t → 1 ≤ Mcoarse t)
    (hFiberFits :
      UniformLargeZeroSafeAppearingCoordinateFiberBudgetFits (F := F) (n := n) a B Mcoarse)
    (hnot : ¬ UniformLineBadScalarsBudgeted dom k a B) :
    (∃ u₀ u₁ c : Fin n → F, c ∈ (rsCode dom k : Submodule F (Fin n → F)) ∧
        a ≤ (directionZeroAgreementSet c u₀ u₁).card) ∨
      (∃ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
        a ≤ (directionZeroSet u₁).card ∧ (directionZeroSet u₁).card ≤ n ∧
          ∃ t : ℕ, t < a ∧ t < k ∧
            Mcoarse t <
              ∑ r ∈ Finset.range a,
                ((directionZeroSet u₁).card - t).choose (r - t) *
                  (if r < k then Mheavy r else 1)) :=
  unsafe_or_largeZero_safe_low_mixedChooseProfileCard_gt_of_not_uniformLineBadScalarsBudgeted
    dom hk a L B Mheavy Mcoarse hSupport hFits
    (uniformLargeZeroSafeLowExactAppearingZeroAgreementFiberBudgeted_of_lowSupportRatioHeavyBudgeted
      dom k a Mheavy hHeavyLow)
    hHigh hFiberFits hnot

open Classical in
/-- Full cardinal-profile mixed consumer with abstract low support-ratio-heavy inputs. -/
theorem uniformLineBadScalarsBudgeted_of_lowSupportRatioHeavy_fullMixedChooseProfileCardSums
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a L B : ℕ)
    (Mheavy Mcoarse : ℕ → ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hHeavyLow :
      UniformLargeZeroSafeLowSupportRatioHeavyCoordinateFiberBudgeted dom k a Mheavy)
    (hProfileCard :
      ∀ z t : ℕ, a ≤ z → z ≤ n → t < a →
        (∑ r ∈ Finset.range a,
          (z - t).choose (r - t) * (if r < k then Mheavy r else 1)) ≤ Mcoarse t)
    (hFiberFits :
      UniformLargeZeroSafeAppearingCoordinateFiberBudgetFits (F := F) (n := n) a B Mcoarse) :
    UniformLineBadScalarsBudgeted dom k a B :=
  uniformLineBadScalarsBudgeted_of_lowExact_fullMixedChooseProfileCardSums
    dom hk a L B Mheavy Mcoarse hSupport hFits hZeroSafe
    (uniformLargeZeroSafeLowExactAppearingZeroAgreementFiberBudgeted_of_lowSupportRatioHeavyBudgeted
      dom k a Mheavy hHeavyLow)
    hProfileCard hFiberFits

open Classical in
/-- Scanner-facing full cardinal-profile residual with abstract low support-ratio-heavy inputs. -/
theorem unsafe_or_largeZero_safe_fullSupportRatioMixedChooseProfileCard_gt_of_not_budgeted
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a L B : ℕ)
    (Mheavy Mcoarse : ℕ → ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hHeavyLow :
      UniformLargeZeroSafeLowSupportRatioHeavyCoordinateFiberBudgeted dom k a Mheavy)
    (hFiberFits :
      UniformLargeZeroSafeAppearingCoordinateFiberBudgetFits (F := F) (n := n) a B Mcoarse)
    (hnot : ¬ UniformLineBadScalarsBudgeted dom k a B) :
    (∃ u₀ u₁ c : Fin n → F, c ∈ (rsCode dom k : Submodule F (Fin n → F)) ∧
        a ≤ (directionZeroAgreementSet c u₀ u₁).card) ∨
      (∃ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
        a ≤ (directionZeroSet u₁).card ∧ (directionZeroSet u₁).card ≤ n ∧
          ∃ t : ℕ, t < a ∧
            Mcoarse t <
              ∑ r ∈ Finset.range a,
                ((directionZeroSet u₁).card - t).choose (r - t) *
                  (if r < k then Mheavy r else 1)) :=
  unsafe_or_largeZero_safe_fullMixedChooseProfileCard_gt_of_not_uniformLineBadScalarsBudgeted
    dom hk a L B Mheavy Mcoarse hSupport hFits
    (uniformLargeZeroSafeLowExactAppearingZeroAgreementFiberBudgeted_of_lowSupportRatioHeavyBudgeted
      dom k a Mheavy hHeavyLow)
    hFiberFits hnot

open Classical in
/-- Top-cardinality mixed consumer with abstract low support-ratio-heavy inputs.  The caller only
checks the worst zero-cardinality arithmetic profile `z = n`. -/
theorem uniformLineBadScalarsBudgeted_of_lowSupportRatioHeavy_mixedChooseProfileTopSums
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a L B : ℕ)
    (Mheavy Mcoarse : ℕ → ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hHeavyLow :
      UniformLargeZeroSafeLowSupportRatioHeavyCoordinateFiberBudgeted dom k a Mheavy)
    (hProfileTop :
      ∀ t : ℕ, t < a → t < k →
        (∑ r ∈ Finset.range a,
          (n - t).choose (r - t) * (if r < k then Mheavy r else 1)) ≤ Mcoarse t)
    (hHigh : ∀ t : ℕ, t < a → k ≤ t → 1 ≤ Mcoarse t)
    (hFiberFits :
      UniformLargeZeroSafeAppearingCoordinateFiberBudgetFits (F := F) (n := n) a B Mcoarse) :
    UniformLineBadScalarsBudgeted dom k a B :=
  uniformLineBadScalarsBudgeted_of_lowExact_mixedChooseProfileTopSums
    dom hk a L B Mheavy Mcoarse hSupport hFits hZeroSafe
    (uniformLargeZeroSafeLowExactAppearingZeroAgreementFiberBudgeted_of_lowSupportRatioHeavyBudgeted
      dom k a Mheavy hHeavyLow)
    hProfileTop hHigh hFiberFits

open Classical in
/-- Scanner-facing top-cardinality residual with abstract low support-ratio-heavy inputs. -/
theorem unsafe_or_largeZero_safe_low_supportRatioMixedChooseProfileTop_gt_of_not_budgeted
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a L B : ℕ)
    (Mheavy Mcoarse : ℕ → ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hHeavyLow :
      UniformLargeZeroSafeLowSupportRatioHeavyCoordinateFiberBudgeted dom k a Mheavy)
    (hHigh : ∀ t : ℕ, t < a → k ≤ t → 1 ≤ Mcoarse t)
    (hFiberFits :
      UniformLargeZeroSafeAppearingCoordinateFiberBudgetFits (F := F) (n := n) a B Mcoarse)
    (hnot : ¬ UniformLineBadScalarsBudgeted dom k a B) :
    (∃ u₀ u₁ c : Fin n → F, c ∈ (rsCode dom k : Submodule F (Fin n → F)) ∧
        a ≤ (directionZeroAgreementSet c u₀ u₁).card) ∨
      (∃ t : ℕ, t < a ∧ t < k ∧
        Mcoarse t <
          ∑ r ∈ Finset.range a,
            (n - t).choose (r - t) * (if r < k then Mheavy r else 1)) :=
  unsafe_or_largeZero_safe_low_mixedChooseProfileTop_gt_of_not_uniformLineBadScalarsBudgeted
    dom hk a L B Mheavy Mcoarse hSupport hFits
    (uniformLargeZeroSafeLowExactAppearingZeroAgreementFiberBudgeted_of_lowSupportRatioHeavyBudgeted
      dom k a Mheavy hHeavyLow)
    hHigh hFiberFits hnot

open Classical in
/-- Full top-cardinality mixed consumer with abstract low support-ratio-heavy inputs. -/
theorem uniformLineBadScalarsBudgeted_of_lowSupportRatioHeavy_fullMixedChooseProfileTopSums
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a L B : ℕ)
    (Mheavy Mcoarse : ℕ → ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hHeavyLow :
      UniformLargeZeroSafeLowSupportRatioHeavyCoordinateFiberBudgeted dom k a Mheavy)
    (hProfileTop :
      ∀ t : ℕ, t < a →
        (∑ r ∈ Finset.range a,
          (n - t).choose (r - t) * (if r < k then Mheavy r else 1)) ≤ Mcoarse t)
    (hFiberFits :
      UniformLargeZeroSafeAppearingCoordinateFiberBudgetFits (F := F) (n := n) a B Mcoarse) :
    UniformLineBadScalarsBudgeted dom k a B :=
  uniformLineBadScalarsBudgeted_of_lowExact_fullMixedChooseProfileTopSums
    dom hk a L B Mheavy Mcoarse hSupport hFits hZeroSafe
    (uniformLargeZeroSafeLowExactAppearingZeroAgreementFiberBudgeted_of_lowSupportRatioHeavyBudgeted
      dom k a Mheavy hHeavyLow)
    hProfileTop hFiberFits

open Classical in
/-- Scanner-facing full top-cardinality residual with abstract low support-ratio-heavy inputs. -/
theorem unsafe_or_largeZero_safe_fullSupportRatioMixedChooseProfileTop_gt_of_not_budgeted
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a L B : ℕ)
    (Mheavy Mcoarse : ℕ → ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hHeavyLow :
      UniformLargeZeroSafeLowSupportRatioHeavyCoordinateFiberBudgeted dom k a Mheavy)
    (hFiberFits :
      UniformLargeZeroSafeAppearingCoordinateFiberBudgetFits (F := F) (n := n) a B Mcoarse)
    (hnot : ¬ UniformLineBadScalarsBudgeted dom k a B) :
    (∃ u₀ u₁ c : Fin n → F, c ∈ (rsCode dom k : Submodule F (Fin n → F)) ∧
        a ≤ (directionZeroAgreementSet c u₀ u₁).card) ∨
      (∃ t : ℕ, t < a ∧
        Mcoarse t <
          ∑ r ∈ Finset.range a,
            (n - t).choose (r - t) * (if r < k then Mheavy r else 1)) :=
  unsafe_or_largeZero_safe_fullMixedChooseProfileTop_gt_of_not_uniformLineBadScalarsBudgeted
    dom hk a L B Mheavy Mcoarse hSupport hFits
    (uniformLargeZeroSafeLowExactAppearingZeroAgreementFiberBudgeted_of_lowSupportRatioHeavyBudgeted
      dom k a Mheavy hHeavyLow)
    hFiberFits hnot

section SourceAudit

#print axioms uniformLineBadScalarsBudgeted_of_lowSupportRatioHeavy_mixedChooseProfileSums
#print axioms uniformLineBadScalarsBudgeted_of_lowSupportRatioHeavy_mixedChooseProfileSumsFit
#print axioms unsafe_or_not_uniformLowSupportRatioMixedChooseProfileSumsFit_of_not_budgeted
#print axioms unsafe_or_largeZero_safe_low_supportRatioMixedChooseProfile_gt_of_not_budgeted
#print axioms uniformLineBadScalarsBudgeted_of_lowSupportRatioHeavy_fullMixedChooseProfileSums
#print axioms unsafe_or_largeZero_safe_fullSupportRatioMixedChooseProfile_gt_of_not_budgeted
#print axioms uniformLineBadScalarsBudgeted_of_lowSupportRatioHeavy_mixedChooseProfileCardSums
#print axioms unsafe_or_largeZero_safe_low_supportRatioMixedChooseProfileCard_gt_of_not_budgeted
#print axioms uniformLineBadScalarsBudgeted_of_lowSupportRatioHeavy_fullMixedChooseProfileCardSums
#print axioms unsafe_or_largeZero_safe_fullSupportRatioMixedChooseProfileCard_gt_of_not_budgeted
#print axioms uniformLineBadScalarsBudgeted_of_lowSupportRatioHeavy_mixedChooseProfileTopSums
#print axioms unsafe_or_largeZero_safe_low_supportRatioMixedChooseProfileTop_gt_of_not_budgeted
#print axioms uniformLineBadScalarsBudgeted_of_lowSupportRatioHeavy_fullMixedChooseProfileTopSums
#print axioms unsafe_or_largeZero_safe_fullSupportRatioMixedChooseProfileTop_gt_of_not_budgeted

end SourceAudit

end ProximityGap.Ownership
