/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LineListAppearanceFiber

/-!
# Mixed exact-profile budgets for appearance-filtered fibers

`LineListAppearanceFiber.lean` shows that coarse appearance-coordinate fibers can be recovered
from exact zero-agreement appearance fibers by summing over exact-profile supersets.  This file
records the low-profile version needed by the delta-star floor route: exact supersets with size
`< k` are charged to a caller-provided low exact budget, while supersets of size `>= k` are
discharged by Reed--Solomon uniqueness and cost only one.
-/

set_option autoImplicit false

open Finset

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- A low exact-profile budget gives a low coarse appearance-coordinate budget after paying a
mixed binomial profile sum.  Low exact supersets `r < k` are charged to `Mexact r`; high exact
supersets `k <= r` are charged only the Reed--Solomon singleton ceiling. -/
theorem zeroLowAppearingCoordinateFiberBudgeted_of_lowExactBudgeted_mixedChooseProfileSums
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a : ℕ)
    (u₀ u₁ : Fin n → F) (Mexact Mcoarse : ℕ → ℕ)
    (hsafe : ZeroDirectionSafeLine dom k a u₀ u₁)
    (hExactLow : ZeroLowExactAppearingZeroAgreementFiberBudgeted dom k a u₀ u₁ Mexact)
    (hProfile : ∀ t : ℕ, t < a → t < k →
      ∀ S ∈ (directionZeroSet u₁).powersetCard t,
        (∑ r ∈ Finset.range a,
          ((directionZeroSet u₁).card - t).choose (r - t) *
            (if r < k then Mexact r else 1)) ≤ Mcoarse t) :
    ZeroLowAppearingCoordinateFiberBudgeted dom k a u₀ u₁ Mcoarse := by
  intro t ht hlow S hS
  let Mmix : ℕ → ℕ := fun r => if r < k then Mexact r else 1
  have hExactMixed :
      ZeroExactAppearingZeroAgreementFiberBudgeted dom k a u₀ u₁ Mmix := by
    refine zeroExactAppearingZeroAgreementFiberBudgeted_of_low_and_high_one
      dom hk a u₀ u₁ Mmix ?_ ?_
    · intro r hr hrlow T hT
      simpa [Mmix, hrlow] using hExactLow r hr hrlow T hT
    · intro r _hr hkr
      have hrnot : ¬ r < k := not_lt_of_ge hkr
      simp [Mmix, hrnot]
  have hSzero : S ⊆ directionZeroSet u₁ := (Finset.mem_powersetCard.mp hS).1
  have hScard : S.card = t := (Finset.mem_powersetCard.mp hS).2
  exact le_trans
    (appearingCoordinateAgreementFiber_card_le_chooseProfile_exactBudget_safeSupersets
      dom k a u₀ u₁ Mmix hsafe hSzero hExactMixed)
    (by simpa [Mmix, hScard] using hProfile t ht hlow S hS)

open Classical in
/-- Uniform version of
`zeroLowAppearingCoordinateFiberBudgeted_of_lowExactBudgeted_mixedChooseProfileSums`. -/
theorem
    uniformLargeZeroSafeLowAppearingCoordinateFiberBudgeted_of_lowExact_mixedChooseProfileSums
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a : ℕ)
    (Mexact Mcoarse : ℕ → ℕ)
    (hExactLow :
      UniformLargeZeroSafeLowExactAppearingZeroAgreementFiberBudgeted dom k a Mexact)
    (hProfile :
      ∀ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
        ZeroDirectionSafeLine dom k a u₀ u₁ →
          ∀ t : ℕ, t < a → t < k →
            ∀ S ∈ (directionZeroSet u₁).powersetCard t,
              (∑ r ∈ Finset.range a,
                ((directionZeroSet u₁).card - t).choose (r - t) *
                  (if r < k then Mexact r else 1)) ≤ Mcoarse t) :
    UniformLargeZeroSafeLowAppearingCoordinateFiberBudgeted dom k a Mcoarse := by
  intro u₀ u₁ hnotEligible hsafe
  exact zeroLowAppearingCoordinateFiberBudgeted_of_lowExactBudgeted_mixedChooseProfileSums
    dom hk a u₀ u₁ Mexact Mcoarse hsafe
    (hExactLow u₀ u₁ hnotEligible hsafe)
    (hProfile u₀ u₁ hnotEligible hsafe)

open Classical in
/-- Production wrapper for the mixed low-exact/high-singleton exact-profile route.  The only
appearance-coordinate estimates the caller supplies are the mixed choose-profile sums over low
coarse profiles `t < k`; high coarse profiles are discharged separately by RS uniqueness. -/
theorem uniformLineBadScalarsBudgeted_of_lowExact_mixedChooseProfileSums
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a L B : ℕ)
    (Mexact Mcoarse : ℕ → ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hExactLow :
      UniformLargeZeroSafeLowExactAppearingZeroAgreementFiberBudgeted dom k a Mexact)
    (hProfile :
      ∀ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
        ZeroDirectionSafeLine dom k a u₀ u₁ →
          ∀ t : ℕ, t < a → t < k →
            ∀ S ∈ (directionZeroSet u₁).powersetCard t,
              (∑ r ∈ Finset.range a,
                ((directionZeroSet u₁).card - t).choose (r - t) *
                  (if r < k then Mexact r else 1)) ≤ Mcoarse t)
    (hHigh : ∀ t : ℕ, t < a → k ≤ t → 1 ≤ Mcoarse t)
    (hFiberFits :
      UniformLargeZeroSafeAppearingCoordinateFiberBudgetFits (F := F) (n := n) a B Mcoarse) :
    UniformLineBadScalarsBudgeted dom k a B :=
  uniformLineBadScalarsBudgeted_of_lowAppearingCoordinateFibers
    dom hk a L B Mcoarse hSupport hFits hZeroSafe
    (uniformLargeZeroSafeLowAppearingCoordinateFiberBudgeted_of_lowExact_mixedChooseProfileSums
      dom hk a Mexact Mcoarse hExactLow hProfile)
    hHigh hFiberFits

open Classical in
/-- If the low exact-profile estimates, high coarse singleton ceiling, and all production-side
hypotheses are fixed, a failed bad-scalar budget exposes a concrete mixed choose-profile sum that
is too large.  This is the arithmetic residual left by the low-exact route. -/
theorem exists_largeZero_safe_low_mixedChooseProfile_gt_of_not_uniformLineBadScalarsBudgeted
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
    ∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
      ZeroDirectionSafeLine dom k a u₀ u₁ ∧
        ∃ t : ℕ, t < a ∧ t < k ∧ ∃ S ∈ (directionZeroSet u₁).powersetCard t,
          Mcoarse t <
            ∑ r ∈ Finset.range a,
              ((directionZeroSet u₁).card - t).choose (r - t) *
                (if r < k then Mexact r else 1) := by
  by_contra hnone
  have hProfile :
      ∀ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
        ZeroDirectionSafeLine dom k a u₀ u₁ →
          ∀ t : ℕ, t < a → t < k →
            ∀ S ∈ (directionZeroSet u₁).powersetCard t,
              (∑ r ∈ Finset.range a,
                ((directionZeroSet u₁).card - t).choose (r - t) *
                  (if r < k then Mexact r else 1)) ≤ Mcoarse t := by
    intro u₀ u₁ hnotEligible hsafe t ht hlow S hS
    exact le_of_not_gt
      (fun hgt => hnone ⟨u₀, u₁, hnotEligible, hsafe, t, ht, hlow, S, hS, hgt⟩)
  exact hnot
    (uniformLineBadScalarsBudgeted_of_lowExact_mixedChooseProfileSums
      dom hk a L B Mexact Mcoarse hSupport hFits hZeroSafe hExactLow hProfile hHigh
      hFiberFits)

open Classical in
/-- Scanner-facing version without assuming zero-direction safety up front.  Failure exposes either
a saturating zero-direction codeword or a low mixed choose-profile arithmetic overrun. -/
theorem unsafe_or_largeZero_safe_low_mixedChooseProfile_gt_of_not_uniformLineBadScalarsBudgeted
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
      (∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
        ZeroDirectionSafeLine dom k a u₀ u₁ ∧
          ∃ t : ℕ, t < a ∧ t < k ∧ ∃ S ∈ (directionZeroSet u₁).powersetCard t,
            Mcoarse t <
              ∑ r ∈ Finset.range a,
                ((directionZeroSet u₁).card - t).choose (r - t) *
                  (if r < k then Mexact r else 1)) := by
  by_cases hZeroSafe : UniformZeroDirectionSafe dom k a
  · exact Or.inr
      (exists_largeZero_safe_low_mixedChooseProfile_gt_of_not_uniformLineBadScalarsBudgeted
        dom hk a L B Mexact Mcoarse hSupport hFits hZeroSafe hExactLow hHigh hFiberFits hnot)
  · exact Or.inl
      ((not_uniformZeroDirectionSafe_iff_exists_line_codeword_zeroAgreement_ge
        dom k a).mp hZeroSafe)

open Classical in
/-- Full-profile mixed variant: a low exact-profile budget gives the full coarse
appearance-coordinate budget when the caller pays the mixed choose-profile sum for every
coarse profile `t < a`.  Low exact supersets still cost `Mexact r`, and high exact supersets cost
only one by RS uniqueness. -/
theorem uniformLargeZeroSafeAppearingCoordinateFiberBudgeted_of_lowExact_fullMixedChooseProfileSums
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a : ℕ) (Mexact Mcoarse : ℕ → ℕ)
    (hLowExact :
      UniformLargeZeroSafeLowExactAppearingZeroAgreementFiberBudgeted dom k a Mexact)
    (hProfile :
      ∀ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
        ZeroDirectionSafeLine dom k a u₀ u₁ →
          ∀ t : ℕ, t < a → ∀ S ∈ (directionZeroSet u₁).powersetCard t,
            (∑ r ∈ Finset.range a,
              ((directionZeroSet u₁).card - t).choose (r - t) *
                (if r < k then Mexact r else 1)) ≤ Mcoarse t) :
    UniformLargeZeroSafeAppearingCoordinateFiberBudgeted dom k a Mcoarse := by
  exact
    uniformLargeZeroSafeAppearingCoordinateFiberBudgeted_of_exactBudgeted_chooseProfileSums
      dom k a (fun r => if r < k then Mexact r else 1) Mcoarse
      (uniformLargeZeroSafeExactAppearingZeroAgreementFiberBudgeted_of_low_and_high_one
        dom hk a (fun r => if r < k then Mexact r else 1)
        (by
          intro u₀ u₁ hnotEligible hsafe t ht htk S hS
          simpa [htk] using hLowExact u₀ u₁ hnotEligible hsafe t ht htk S hS)
        (by
          intro t _ht hkt
          simp [not_lt_of_ge hkt]))
      hProfile

open Classical in
/-- Production wrapper for the full-profile mixed low-exact/high-singleton choose-profile route. -/
theorem uniformLineBadScalarsBudgeted_of_lowExact_fullMixedChooseProfileSums
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a L B : ℕ)
    (Mexact Mcoarse : ℕ → ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hLowExact :
      UniformLargeZeroSafeLowExactAppearingZeroAgreementFiberBudgeted dom k a Mexact)
    (hProfile :
      ∀ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
        ZeroDirectionSafeLine dom k a u₀ u₁ →
          ∀ t : ℕ, t < a → ∀ S ∈ (directionZeroSet u₁).powersetCard t,
            (∑ r ∈ Finset.range a,
              ((directionZeroSet u₁).card - t).choose (r - t) *
                (if r < k then Mexact r else 1)) ≤ Mcoarse t)
    (hFiberFits :
      UniformLargeZeroSafeAppearingCoordinateFiberBudgetFits (F := F) (n := n) a B Mcoarse) :
    UniformLineBadScalarsBudgeted dom k a B :=
  uniformLineBadScalarsBudgeted_of_supportAdjustedBudgetFits_and_appearingCoordinateFibers
    dom k a L B Mcoarse hSupport hFits hZeroSafe
    (uniformLargeZeroSafeAppearingCoordinateFiberBudgeted_of_lowExact_fullMixedChooseProfileSums
      dom hk a Mexact Mcoarse hLowExact hProfile)
    hFiberFits

open Classical in
/-- Scanner-facing converse for the full mixed choose-profile route.  If the support-side
hypotheses and weighted arithmetic fit are fixed, failed production exposes either zero-direction
saturation or a large-zero safe coarse profile whose full mixed choose-profile sum exceeds the
proposed coarse budget. -/
theorem unsafe_or_largeZero_safe_fullMixedChooseProfile_gt_of_not_uniformLineBadScalarsBudgeted
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a L B : ℕ)
    (Mexact Mcoarse : ℕ → ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hLowExact :
      UniformLargeZeroSafeLowExactAppearingZeroAgreementFiberBudgeted dom k a Mexact)
    (hFiberFits :
      UniformLargeZeroSafeAppearingCoordinateFiberBudgetFits (F := F) (n := n) a B Mcoarse)
    (hnot : ¬ UniformLineBadScalarsBudgeted dom k a B) :
    (∃ u₀ u₁ c : Fin n → F, c ∈ (rsCode dom k : Submodule F (Fin n → F)) ∧
        a ≤ (directionZeroAgreementSet c u₀ u₁).card) ∨
      (∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
        ZeroDirectionSafeLine dom k a u₀ u₁ ∧
          ∃ t : ℕ, t < a ∧ ∃ S ∈ (directionZeroSet u₁).powersetCard t,
            Mcoarse t <
              ∑ r ∈ Finset.range a,
                ((directionZeroSet u₁).card - t).choose (r - t) *
                  (if r < k then Mexact r else 1)) := by
  by_cases hZeroSafe : UniformZeroDirectionSafe dom k a
  · right
    by_contra hnone
    have hProfile :
        ∀ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
          ZeroDirectionSafeLine dom k a u₀ u₁ →
            ∀ t : ℕ, t < a → ∀ S ∈ (directionZeroSet u₁).powersetCard t,
              (∑ r ∈ Finset.range a,
                ((directionZeroSet u₁).card - t).choose (r - t) *
                  (if r < k then Mexact r else 1)) ≤ Mcoarse t := by
      intro u₀ u₁ hnotEligible hsafe t ht S hS
      exact le_of_not_gt
        (fun hgt => hnone ⟨u₀, u₁, hnotEligible, hsafe, t, ht, S, hS, hgt⟩)
    exact hnot
      (uniformLineBadScalarsBudgeted_of_lowExact_fullMixedChooseProfileSums
        dom hk a L B Mexact Mcoarse hSupport hFits hZeroSafe hLowExact hProfile hFiberFits)
  · exact Or.inl
      ((not_uniformZeroDirectionSafe_iff_exists_line_codeword_zeroAgreement_ge
        dom k a).mp hZeroSafe)

section SourceAudit

#print axioms zeroLowAppearingCoordinateFiberBudgeted_of_lowExactBudgeted_mixedChooseProfileSums
#print axioms
  uniformLargeZeroSafeLowAppearingCoordinateFiberBudgeted_of_lowExact_mixedChooseProfileSums
#print axioms uniformLineBadScalarsBudgeted_of_lowExact_mixedChooseProfileSums
#print axioms
  exists_largeZero_safe_low_mixedChooseProfile_gt_of_not_uniformLineBadScalarsBudgeted
#print axioms
  unsafe_or_largeZero_safe_low_mixedChooseProfile_gt_of_not_uniformLineBadScalarsBudgeted
#print axioms
  uniformLargeZeroSafeAppearingCoordinateFiberBudgeted_of_lowExact_fullMixedChooseProfileSums
#print axioms uniformLineBadScalarsBudgeted_of_lowExact_fullMixedChooseProfileSums
#print axioms
  unsafe_or_largeZero_safe_fullMixedChooseProfile_gt_of_not_uniformLineBadScalarsBudgeted

end SourceAudit

end ProximityGap.Ownership
