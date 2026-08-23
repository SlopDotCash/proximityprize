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

omit [Field F] [Fintype F] [DecidableEq F] [NeZero n] in
/-- Pure top-cardinality arithmetic fit for the low mixed choose-profile sums.  This is the
generic `z = n` analogue of `UniformLargeZeroSafeLowMixedChooseProfileSumsFit`. -/
def LowMixedChooseProfileTopSumsFit
    (a k : ℕ) (Mexact Mcoarse : ℕ → ℕ) : Prop :=
  ∀ t : ℕ, t < a → t < k →
    (∑ r ∈ Finset.range a,
      (n - t).choose (r - t) * (if r < k then Mexact r else 1)) ≤ Mcoarse t

omit [Field F] [Fintype F] [DecidableEq F] [NeZero n] in
/-- Pure top-cardinality arithmetic fit for the full mixed choose-profile sums. -/
def FullMixedChooseProfileTopSumsFit
    (a k : ℕ) (Mexact Mcoarse : ℕ → ℕ) : Prop :=
  ∀ t : ℕ, t < a →
    (∑ r ∈ Finset.range a,
      (n - t).choose (r - t) * (if r < k then Mexact r else 1)) ≤ Mcoarse t

omit [Field F] [Fintype F] [DecidableEq F] [NeZero n] in
open Classical in
/-- Exact failure form for the low top-cardinality mixed choose-profile fit. -/
theorem not_lowMixedChooseProfileTopSumsFit_iff_exists_sum_gt
    (a k : ℕ) (Mexact Mcoarse : ℕ → ℕ) :
    (¬ LowMixedChooseProfileTopSumsFit (n := n) a k Mexact Mcoarse) ↔
      ∃ t : ℕ, t < a ∧ t < k ∧
        Mcoarse t <
          ∑ r ∈ Finset.range a,
            (n - t).choose (r - t) * (if r < k then Mexact r else 1) := by
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro t ht htk
    exact le_of_not_gt (fun hgt => hnone ⟨t, ht, htk, hgt⟩)
  · rintro ⟨t, ht, htk, hgt⟩ hFit
    exact not_lt_of_ge (hFit t ht htk) hgt

omit [Field F] [Fintype F] [DecidableEq F] [NeZero n] in
open Classical in
/-- Exact failure form for the full top-cardinality mixed choose-profile fit. -/
theorem not_fullMixedChooseProfileTopSumsFit_iff_exists_sum_gt
    (a k : ℕ) (Mexact Mcoarse : ℕ → ℕ) :
    (¬ FullMixedChooseProfileTopSumsFit (n := n) a k Mexact Mcoarse) ↔
      ∃ t : ℕ, t < a ∧
        Mcoarse t <
          ∑ r ∈ Finset.range a,
            (n - t).choose (r - t) * (if r < k then Mexact r else 1) := by
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro t ht
    exact le_of_not_gt (fun hgt => hnone ⟨t, ht, hgt⟩)
  · rintro ⟨t, ht, hgt⟩ hFit
    exact not_lt_of_ge (hFit t ht) hgt

omit [Field F] [Fintype F] [DecidableEq F] [NeZero n] in
open Classical in
/-- Every summand of a fitted low top-cardinality mixed profile is below the coarse budget. -/
theorem lowMixedChooseProfileTopSumsFit_term_le
    {a k t r : ℕ} {Mexact Mcoarse : ℕ → ℕ}
    (hFit : LowMixedChooseProfileTopSumsFit (n := n) a k Mexact Mcoarse)
    (ht : t < a) (htk : t < k) (hr : r < a) :
    (n - t).choose (r - t) * (if r < k then Mexact r else 1) ≤ Mcoarse t := by
  have hterm :
      (n - t).choose (r - t) * (if r < k then Mexact r else 1) ≤
        ∑ r ∈ Finset.range a,
          (n - t).choose (r - t) * (if r < k then Mexact r else 1) := by
    exact Finset.single_le_sum
      (f := fun r => (n - t).choose (r - t) * (if r < k then Mexact r else 1))
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hr)
  exact le_trans hterm (hFit t ht htk)

omit [Field F] [Fintype F] [DecidableEq F] [NeZero n] in
open Classical in
/-- Every summand of a fitted full top-cardinality mixed profile is below the coarse budget. -/
theorem fullMixedChooseProfileTopSumsFit_term_le
    {a k t r : ℕ} {Mexact Mcoarse : ℕ → ℕ}
    (hFit : FullMixedChooseProfileTopSumsFit (n := n) a k Mexact Mcoarse)
    (ht : t < a) (hr : r < a) :
    (n - t).choose (r - t) * (if r < k then Mexact r else 1) ≤ Mcoarse t := by
  have hterm :
      (n - t).choose (r - t) * (if r < k then Mexact r else 1) ≤
        ∑ r ∈ Finset.range a,
          (n - t).choose (r - t) * (if r < k then Mexact r else 1) := by
    exact Finset.single_le_sum
      (f := fun r => (n - t).choose (r - t) * (if r < k then Mexact r else 1))
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hr)
  exact le_trans hterm (hFit t ht)

omit [Field F] [Fintype F] [DecidableEq F] [NeZero n] in
open Classical in
/-- The original low exact-profile envelope is necessary for a fitted low top profile. -/
theorem lowMixedChooseProfileTopSumsFit_exact_le
    {a k t : ℕ} {Mexact Mcoarse : ℕ → ℕ}
    (hFit : LowMixedChooseProfileTopSumsFit (n := n) a k Mexact Mcoarse)
    (ht : t < a) (htk : t < k) :
    Mexact t ≤ Mcoarse t := by
  simpa [htk] using
    (lowMixedChooseProfileTopSumsFit_term_le (n := n) (r := t) hFit ht htk ht)

omit [Field F] [Fintype F] [DecidableEq F] [NeZero n] in
open Classical in
/-- One over-budget exact-profile term refutes the low top mixed-profile fit. -/
theorem not_lowMixedChooseProfileTopSumsFit_of_exact_gt
    {a k t : ℕ} {Mexact Mcoarse : ℕ → ℕ}
    (ht : t < a) (htk : t < k) (hgt : Mcoarse t < Mexact t) :
    ¬ LowMixedChooseProfileTopSumsFit (n := n) a k Mexact Mcoarse := by
  intro hFit
  exact not_lt_of_ge
    (lowMixedChooseProfileTopSumsFit_exact_le (n := n) hFit ht htk) hgt

omit [Field F] [Fintype F] [DecidableEq F] [NeZero n] in
open Classical in
/-- High singleton binomial terms are necessary for a fitted low top profile. -/
theorem lowMixedChooseProfileTopSumsFit_high_choose_le
    {a k t r : ℕ} {Mexact Mcoarse : ℕ → ℕ}
    (hFit : LowMixedChooseProfileTopSumsFit (n := n) a k Mexact Mcoarse)
    (ht : t < a) (htk : t < k) (hr : r < a) (hkr : k ≤ r) :
    (n - t).choose (r - t) ≤ Mcoarse t := by
  simpa [not_lt_of_ge hkr] using
    (lowMixedChooseProfileTopSumsFit_term_le (n := n) (r := r) hFit ht htk hr)

omit [Field F] [Fintype F] [DecidableEq F] [NeZero n] in
open Classical in
/-- One over-budget high singleton binomial term refutes the low top fit. -/
theorem not_lowMixedChooseProfileTopSumsFit_of_high_choose_gt
    {a k t r : ℕ} {Mexact Mcoarse : ℕ → ℕ}
    (ht : t < a) (htk : t < k) (hr : r < a) (hkr : k ≤ r)
    (hgt : Mcoarse t < (n - t).choose (r - t)) :
    ¬ LowMixedChooseProfileTopSumsFit (n := n) a k Mexact Mcoarse := by
  intro hFit
  exact not_lt_of_ge
    (lowMixedChooseProfileTopSumsFit_high_choose_le
      (n := n) (r := r) hFit ht htk hr hkr)
    hgt

omit [Field F] [Fintype F] [DecidableEq F] [NeZero n] in
open Classical in
/-- The original low exact-profile envelope is necessary for a fitted full top profile. -/
theorem fullMixedChooseProfileTopSumsFit_exact_le
    {a k t : ℕ} {Mexact Mcoarse : ℕ → ℕ}
    (hFit : FullMixedChooseProfileTopSumsFit (n := n) a k Mexact Mcoarse)
    (ht : t < a) (htk : t < k) :
    Mexact t ≤ Mcoarse t := by
  simpa [htk] using
    (fullMixedChooseProfileTopSumsFit_term_le (n := n) (r := t) hFit ht ht)

omit [Field F] [Fintype F] [DecidableEq F] [NeZero n] in
open Classical in
/-- One over-budget exact-profile term refutes the full top mixed-profile fit. -/
theorem not_fullMixedChooseProfileTopSumsFit_of_exact_gt
    {a k t : ℕ} {Mexact Mcoarse : ℕ → ℕ}
    (ht : t < a) (htk : t < k) (hgt : Mcoarse t < Mexact t) :
    ¬ FullMixedChooseProfileTopSumsFit (n := n) a k Mexact Mcoarse := by
  intro hFit
  exact not_lt_of_ge
    (fullMixedChooseProfileTopSumsFit_exact_le (n := n) hFit ht htk) hgt

omit [Field F] [Fintype F] [DecidableEq F] [NeZero n] in
open Classical in
/-- High singleton binomial terms are necessary for a fitted full top profile. -/
theorem fullMixedChooseProfileTopSumsFit_high_choose_le
    {a k t r : ℕ} {Mexact Mcoarse : ℕ → ℕ}
    (hFit : FullMixedChooseProfileTopSumsFit (n := n) a k Mexact Mcoarse)
    (ht : t < a) (hr : r < a) (hkr : k ≤ r) :
    (n - t).choose (r - t) ≤ Mcoarse t := by
  simpa [not_lt_of_ge hkr] using
    (fullMixedChooseProfileTopSumsFit_term_le (n := n) (r := r) hFit ht hr)

omit [Field F] [Fintype F] [DecidableEq F] [NeZero n] in
open Classical in
/-- One over-budget high singleton binomial term refutes the full top fit. -/
theorem not_fullMixedChooseProfileTopSumsFit_of_high_choose_gt
    {a k t r : ℕ} {Mexact Mcoarse : ℕ → ℕ}
    (ht : t < a) (hr : r < a) (hkr : k ≤ r)
    (hgt : Mcoarse t < (n - t).choose (r - t)) :
    ¬ FullMixedChooseProfileTopSumsFit (n := n) a k Mexact Mcoarse := by
  intro hFit
  exact not_lt_of_ge
    (fullMixedChooseProfileTopSumsFit_high_choose_le
      (n := n) (r := r) hFit ht hr hkr)
    hgt

open Classical in
/-- Named top-fit wrapper for the low mixed route with an arbitrary exact-profile budget. -/
theorem uniformLineBadScalarsBudgeted_of_lowExact_mixedChooseProfileTopSumsFit
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a L B : ℕ)
    (Mexact Mcoarse : ℕ → ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hExactLow :
      UniformLargeZeroSafeLowExactAppearingZeroAgreementFiberBudgeted dom k a Mexact)
    (hProfileTopFit : LowMixedChooseProfileTopSumsFit (n := n) a k Mexact Mcoarse)
    (hHigh : ∀ t : ℕ, t < a → k ≤ t → 1 ≤ Mcoarse t)
    (hFiberFits :
      UniformLargeZeroSafeAppearingCoordinateFiberBudgetFits (F := F) (n := n) a B Mcoarse) :
    UniformLineBadScalarsBudgeted dom k a B :=
  uniformLineBadScalarsBudgeted_of_lowExact_mixedChooseProfileTopSums
    dom hk a L B Mexact Mcoarse hSupport hFits hZeroSafe hExactLow hProfileTopFit
    hHigh hFiberFits

open Classical in
/-- Scanner-facing named top residual for the low mixed route. -/
theorem unsafe_or_not_lowMixedChooseProfileTopSumsFit_of_not_budgeted
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
      ¬ LowMixedChooseProfileTopSumsFit (n := n) a k Mexact Mcoarse := by
  rcases
      (unsafe_or_largeZero_safe_low_mixedChooseProfileTop_gt_of_not_uniformLineBadScalarsBudgeted
        dom hk a L B Mexact Mcoarse hSupport hFits hExactLow hHigh hFiberFits hnot) with
    hUnsafe | hProfile
  · exact Or.inl hUnsafe
  · rcases hProfile with ⟨t, ht, htk, hgt⟩
    exact Or.inr
      ((not_lowMixedChooseProfileTopSumsFit_iff_exists_sum_gt
        (n := n) a k Mexact Mcoarse).mpr ⟨t, ht, htk, hgt⟩)

open Classical in
/-- Named top-fit wrapper for the full mixed route with an arbitrary exact-profile budget. -/
theorem uniformLineBadScalarsBudgeted_of_lowExact_fullMixedChooseProfileTopSumsFit
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a L B : ℕ)
    (Mexact Mcoarse : ℕ → ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hExactLow :
      UniformLargeZeroSafeLowExactAppearingZeroAgreementFiberBudgeted dom k a Mexact)
    (hProfileTopFit : FullMixedChooseProfileTopSumsFit (n := n) a k Mexact Mcoarse)
    (hFiberFits :
      UniformLargeZeroSafeAppearingCoordinateFiberBudgetFits (F := F) (n := n) a B Mcoarse) :
    UniformLineBadScalarsBudgeted dom k a B :=
  uniformLineBadScalarsBudgeted_of_lowExact_fullMixedChooseProfileTopSums
    dom hk a L B Mexact Mcoarse hSupport hFits hZeroSafe hExactLow hProfileTopFit
    hFiberFits

open Classical in
/-- Scanner-facing named top residual for the full mixed route. -/
theorem unsafe_or_not_fullMixedChooseProfileTopSumsFit_of_not_budgeted
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a L B : ℕ)
    (Mexact Mcoarse : ℕ → ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hExactLow :
      UniformLargeZeroSafeLowExactAppearingZeroAgreementFiberBudgeted dom k a Mexact)
    (hFiberFits :
      UniformLargeZeroSafeAppearingCoordinateFiberBudgetFits (F := F) (n := n) a B Mcoarse)
    (hnot : ¬ UniformLineBadScalarsBudgeted dom k a B) :
    (∃ u₀ u₁ c : Fin n → F, c ∈ (rsCode dom k : Submodule F (Fin n → F)) ∧
        a ≤ (directionZeroAgreementSet c u₀ u₁).card) ∨
      ¬ FullMixedChooseProfileTopSumsFit (n := n) a k Mexact Mcoarse := by
  rcases
      (unsafe_or_largeZero_safe_fullMixedChooseProfileTop_gt_of_not_uniformLineBadScalarsBudgeted
        dom hk a L B Mexact Mcoarse hSupport hFits hExactLow hFiberFits hnot) with
    hUnsafe | hProfile
  · exact Or.inl hUnsafe
  · rcases hProfile with ⟨t, ht, hgt⟩
    exact Or.inr
      ((not_fullMixedChooseProfileTopSumsFit_iff_exists_sum_gt
        (n := n) a k Mexact Mcoarse).mpr ⟨t, ht, hgt⟩)

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

omit [Field F] [DecidableEq F] [NeZero n] in
/-- A low top-cardinality field-power fit supplies the corresponding all-cardinality fit. -/
theorem fieldPowMixedProfileCardFit_of_topFit
    {a k : ℕ} {Mcoarse : ℕ → ℕ}
    (hTop : FieldPowMixedProfileTopFit (F := F) (n := n) a k Mcoarse) :
    FieldPowMixedProfileCardFit (F := F) (n := n) a k Mcoarse := by
  intro z t _hzlo hzhi ht htk
  exact le_trans (fieldPowMixedProfileCardSum_le_topCard (F := F) (n := n) a k z t hzhi)
    (hTop t ht htk)

omit [Field F] [DecidableEq F] [NeZero n] in
/-- A full top-cardinality field-power fit supplies the corresponding all-cardinality fit. -/
theorem fieldPowFullMixedProfileCardFit_of_topFit
    {a k : ℕ} {Mcoarse : ℕ → ℕ}
    (hTop : FieldPowFullMixedProfileTopFit (F := F) (n := n) a k Mcoarse) :
    FieldPowFullMixedProfileCardFit (F := F) (n := n) a k Mcoarse := by
  intro z t _hzlo hzhi ht
  exact le_trans (fieldPowMixedProfileCardSum_le_topCard (F := F) (n := n) a k z t hzhi)
    (hTop t ht)

omit [Field F] [DecidableEq F] [NeZero n] in
/-- Any all-cardinality obstruction also refutes the low top-cardinality field-power fit. -/
theorem not_fieldPowMixedProfileTopFit_of_not_cardFit
    {a k : ℕ} {Mcoarse : ℕ → ℕ}
    (hnot : ¬ FieldPowMixedProfileCardFit (F := F) (n := n) a k Mcoarse) :
    ¬ FieldPowMixedProfileTopFit (F := F) (n := n) a k Mcoarse := by
  intro hTop
  exact hnot (fieldPowMixedProfileCardFit_of_topFit (F := F) (n := n) hTop)

omit [Field F] [DecidableEq F] [NeZero n] in
/-- Any all-cardinality obstruction also refutes the full top-cardinality field-power fit. -/
theorem not_fieldPowFullMixedProfileTopFit_of_not_cardFit
    {a k : ℕ} {Mcoarse : ℕ → ℕ}
    (hnot : ¬ FieldPowFullMixedProfileCardFit (F := F) (n := n) a k Mcoarse) :
    ¬ FieldPowFullMixedProfileTopFit (F := F) (n := n) a k Mcoarse := by
  intro hTop
  exact hnot (fieldPowFullMixedProfileCardFit_of_topFit (F := F) (n := n) hTop)

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

omit [Field F] [DecidableEq F] [NeZero n] in
open Classical in
/-- Every summand in a fitted low top-cardinality field-power mixed sum is below the coarse
budget. -/
theorem fieldPowMixedProfileTopFit_term_le
    {a k t r : ℕ} {Mcoarse : ℕ → ℕ}
    (hFit : FieldPowMixedProfileTopFit (F := F) (n := n) a k Mcoarse)
    (ht : t < a) (htk : t < k) (hr : r < a) :
    (n - t).choose (r - t) *
        (if r < k then Fintype.card F * (n.choose (a - r) * Fintype.card F ^ (k - a))
        else 1) ≤ Mcoarse t := by
  have hterm :
      (n - t).choose (r - t) *
          (if r < k then Fintype.card F * (n.choose (a - r) * Fintype.card F ^ (k - a))
          else 1) ≤ fieldPowMixedProfileCardSum (F := F) n a k n t := by
    exact Finset.single_le_sum
      (f := fun r =>
        (n - t).choose (r - t) *
          (if r < k then Fintype.card F * (n.choose (a - r) * Fintype.card F ^ (k - a))
          else 1))
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hr)
  exact le_trans hterm (hFit t ht htk)

omit [Field F] [DecidableEq F] [NeZero n] in
open Classical in
/-- Every summand in a fitted full top-cardinality field-power mixed sum is below the coarse
budget. -/
theorem fieldPowFullMixedProfileTopFit_term_le
    {a k t r : ℕ} {Mcoarse : ℕ → ℕ}
    (hFit : FieldPowFullMixedProfileTopFit (F := F) (n := n) a k Mcoarse)
    (ht : t < a) (hr : r < a) :
    (n - t).choose (r - t) *
        (if r < k then Fintype.card F * (n.choose (a - r) * Fintype.card F ^ (k - a))
        else 1) ≤ Mcoarse t := by
  have hterm :
      (n - t).choose (r - t) *
          (if r < k then Fintype.card F * (n.choose (a - r) * Fintype.card F ^ (k - a))
          else 1) ≤ fieldPowMixedProfileCardSum (F := F) n a k n t := by
    exact Finset.single_le_sum
      (f := fun r =>
        (n - t).choose (r - t) *
          (if r < k then Fintype.card F * (n.choose (a - r) * Fintype.card F ^ (k - a))
          else 1))
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hr)
  exact le_trans hterm (hFit t ht)

omit [Field F] [DecidableEq F] [NeZero n] in
open Classical in
/-- A low top-cardinality field-power fit must dominate its same-profile field-power term. -/
theorem fieldPowMixedProfileTopFit_exact_le
    {a k t : ℕ} {Mcoarse : ℕ → ℕ}
    (hFit : FieldPowMixedProfileTopFit (F := F) (n := n) a k Mcoarse)
    (ht : t < a) (htk : t < k) :
    Fintype.card F * (n.choose (a - t) * Fintype.card F ^ (k - a)) ≤ Mcoarse t := by
  have hterm := fieldPowMixedProfileTopFit_term_le
    (F := F) (n := n) (r := t) hFit ht htk ht
  simpa [htk] using hterm

omit [Field F] [DecidableEq F] [NeZero n] in
open Classical in
/-- Every high singleton binomial term is necessary for a fitted low top-cardinality mixed sum. -/
theorem fieldPowMixedProfileTopFit_high_choose_le
    {a k t r : ℕ} {Mcoarse : ℕ → ℕ}
    (hFit : FieldPowMixedProfileTopFit (F := F) (n := n) a k Mcoarse)
    (ht : t < a) (htk : t < k) (hr : r < a) (hkr : k ≤ r) :
    (n - t).choose (r - t) ≤ Mcoarse t := by
  simpa [not_lt_of_ge hkr] using
    (fieldPowMixedProfileTopFit_term_le
      (F := F) (n := n) (r := r) hFit ht htk hr)

omit [Field F] [DecidableEq F] [NeZero n] in
open Classical in
/-- An over-budget same-profile field-power term refutes the low top-cardinality fit. -/
theorem not_fieldPowMixedProfileTopFit_of_exact_gt
    {a k t : ℕ} {Mcoarse : ℕ → ℕ}
    (ht : t < a) (htk : t < k)
    (hgt :
      Mcoarse t < Fintype.card F * (n.choose (a - t) * Fintype.card F ^ (k - a))) :
    ¬ FieldPowMixedProfileTopFit (F := F) (n := n) a k Mcoarse := by
  intro hFit
  exact not_lt_of_ge
    (fieldPowMixedProfileTopFit_exact_le (F := F) (n := n) hFit ht htk) hgt

omit [Field F] [DecidableEq F] [NeZero n] in
open Classical in
/-- One over-budget high singleton term refutes the low top-cardinality fit. -/
theorem not_fieldPowMixedProfileTopFit_of_high_choose_gt
    {a k t r : ℕ} {Mcoarse : ℕ → ℕ}
    (ht : t < a) (htk : t < k) (hr : r < a) (hkr : k ≤ r)
    (hgt : Mcoarse t < (n - t).choose (r - t)) :
    ¬ FieldPowMixedProfileTopFit (F := F) (n := n) a k Mcoarse := by
  intro hFit
  exact not_lt_of_ge
    (fieldPowMixedProfileTopFit_high_choose_le
      (F := F) (n := n) (r := r) hFit ht htk hr hkr) hgt

omit [Field F] [DecidableEq F] [NeZero n] in
open Classical in
/-- A full top-cardinality field-power fit must dominate its same-profile field-power term. -/
theorem fieldPowFullMixedProfileTopFit_exact_le
    {a k t : ℕ} {Mcoarse : ℕ → ℕ}
    (hFit : FieldPowFullMixedProfileTopFit (F := F) (n := n) a k Mcoarse)
    (ht : t < a) (htk : t < k) :
    Fintype.card F * (n.choose (a - t) * Fintype.card F ^ (k - a)) ≤ Mcoarse t := by
  have hterm := fieldPowFullMixedProfileTopFit_term_le
    (F := F) (n := n) (r := t) hFit ht ht
  simpa [htk] using hterm

omit [Field F] [DecidableEq F] [NeZero n] in
open Classical in
/-- Every high singleton binomial term is necessary for a fitted full top-cardinality mixed sum. -/
theorem fieldPowFullMixedProfileTopFit_high_choose_le
    {a k t r : ℕ} {Mcoarse : ℕ → ℕ}
    (hFit : FieldPowFullMixedProfileTopFit (F := F) (n := n) a k Mcoarse)
    (ht : t < a) (hr : r < a) (hkr : k ≤ r) :
    (n - t).choose (r - t) ≤ Mcoarse t := by
  simpa [not_lt_of_ge hkr] using
    (fieldPowFullMixedProfileTopFit_term_le
      (F := F) (n := n) (r := r) hFit ht hr)

omit [Field F] [DecidableEq F] [NeZero n] in
open Classical in
/-- An over-budget same-profile field-power term refutes the full top-cardinality fit. -/
theorem not_fieldPowFullMixedProfileTopFit_of_exact_gt
    {a k t : ℕ} {Mcoarse : ℕ → ℕ}
    (ht : t < a) (htk : t < k)
    (hgt :
      Mcoarse t < Fintype.card F * (n.choose (a - t) * Fintype.card F ^ (k - a))) :
    ¬ FieldPowFullMixedProfileTopFit (F := F) (n := n) a k Mcoarse := by
  intro hFit
  exact not_lt_of_ge
    (fieldPowFullMixedProfileTopFit_exact_le (F := F) (n := n) hFit ht htk) hgt

omit [Field F] [DecidableEq F] [NeZero n] in
open Classical in
/-- One over-budget high singleton term refutes the full top-cardinality fit. -/
theorem not_fieldPowFullMixedProfileTopFit_of_high_choose_gt
    {a k t r : ℕ} {Mcoarse : ℕ → ℕ}
    (ht : t < a) (hr : r < a) (hkr : k ≤ r)
    (hgt : Mcoarse t < (n - t).choose (r - t)) :
    ¬ FieldPowFullMixedProfileTopFit (F := F) (n := n) a k Mcoarse := by
  intro hFit
  exact not_lt_of_ge
    (fieldPowFullMixedProfileTopFit_high_choose_le
      (F := F) (n := n) (r := r) hFit ht hr hkr) hgt

section SourceAudit

#print axioms
  uniformLargeZeroSafeLowAppearingCoordinateFiberBudgeted_of_lowExact_mixedChooseProfileSumsFit
#print axioms uniformLineBadScalarsBudgeted_of_lowExact_mixedChooseProfileSumsFit
#print axioms not_uniformLowMixedChooseProfileSumsFit_of_not_uniformLineBadScalarsBudgeted
#print axioms unsafe_or_not_uniformLowMixedChooseProfileSumsFit_of_not_budgeted
#print axioms fieldPowMixedProfileCardSum_le_topCard
#print axioms FieldPowMixedProfileTopFit
#print axioms FieldPowFullMixedProfileTopFit
#print axioms LowMixedChooseProfileTopSumsFit
#print axioms FullMixedChooseProfileTopSumsFit
#print axioms not_lowMixedChooseProfileTopSumsFit_iff_exists_sum_gt
#print axioms not_fullMixedChooseProfileTopSumsFit_iff_exists_sum_gt
#print axioms lowMixedChooseProfileTopSumsFit_term_le
#print axioms fullMixedChooseProfileTopSumsFit_term_le
#print axioms lowMixedChooseProfileTopSumsFit_exact_le
#print axioms not_lowMixedChooseProfileTopSumsFit_of_exact_gt
#print axioms lowMixedChooseProfileTopSumsFit_high_choose_le
#print axioms not_lowMixedChooseProfileTopSumsFit_of_high_choose_gt
#print axioms fullMixedChooseProfileTopSumsFit_exact_le
#print axioms not_fullMixedChooseProfileTopSumsFit_of_exact_gt
#print axioms fullMixedChooseProfileTopSumsFit_high_choose_le
#print axioms not_fullMixedChooseProfileTopSumsFit_of_high_choose_gt
#print axioms uniformLineBadScalarsBudgeted_of_lowExact_mixedChooseProfileTopSumsFit
#print axioms unsafe_or_not_lowMixedChooseProfileTopSumsFit_of_not_budgeted
#print axioms uniformLineBadScalarsBudgeted_of_lowExact_fullMixedChooseProfileTopSumsFit
#print axioms unsafe_or_not_fullMixedChooseProfileTopSumsFit_of_not_budgeted
#print axioms not_fieldPowMixedProfileTopFit_iff_exists_sum_gt
#print axioms not_fieldPowFullMixedProfileTopFit_iff_exists_sum_gt
#print axioms fieldPowMixedProfileCardFit_of_topFit
#print axioms fieldPowFullMixedProfileCardFit_of_topFit
#print axioms not_fieldPowMixedProfileTopFit_of_not_cardFit
#print axioms not_fieldPowFullMixedProfileTopFit_of_not_cardFit
#print axioms uniformLineBadScalarsBudgeted_of_fieldPow_mixedProfileTopFit
#print axioms unsafe_or_not_fieldPow_mixedProfileTopFit_of_not_budgeted
#print axioms uniformLineBadScalarsBudgeted_of_fieldPow_fullMixedProfileTopFit
#print axioms unsafe_or_not_fieldPow_fullMixedProfileTopFit_of_not_budgeted
#print axioms fieldPowMixedProfileTopFit_term_le
#print axioms fieldPowFullMixedProfileTopFit_term_le
#print axioms fieldPowMixedProfileTopFit_exact_le
#print axioms fieldPowMixedProfileTopFit_high_choose_le
#print axioms not_fieldPowMixedProfileTopFit_of_exact_gt
#print axioms not_fieldPowMixedProfileTopFit_of_high_choose_gt
#print axioms fieldPowFullMixedProfileTopFit_exact_le
#print axioms fieldPowFullMixedProfileTopFit_high_choose_le
#print axioms not_fieldPowFullMixedProfileTopFit_of_exact_gt
#print axioms not_fieldPowFullMixedProfileTopFit_of_high_choose_gt

end SourceAudit

end ProximityGap.Ownership
