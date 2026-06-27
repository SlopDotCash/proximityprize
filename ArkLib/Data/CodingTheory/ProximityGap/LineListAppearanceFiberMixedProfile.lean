/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LineListSupportRatioFiber

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

/-- Per-line arithmetic fit for the low mixed exact-profile sum.  For each low coarse profile
`t < k`, every coarse zero profile `S` must pay the sum over exact supersets: low exact supersets
cost `Mexact r`, while high exact supersets cost the RS singleton ceiling `1`. -/
def ZeroLowMixedChooseProfileSumsFit
    (a k : ℕ) (u₁ : Fin n → F) (Mexact Mcoarse : ℕ → ℕ) : Prop :=
  ∀ t : ℕ, t < a → t < k →
    ∀ S ∈ (directionZeroSet u₁).powersetCard t,
      (∑ r ∈ Finset.range a,
        ((directionZeroSet u₁).card - t).choose (r - t) *
          (if r < k then Mexact r else 1)) ≤ Mcoarse t

/-- Uniform large-zero-safe version of `ZeroLowMixedChooseProfileSumsFit`. -/
def UniformLargeZeroSafeLowMixedChooseProfileSumsFit
    (dom : Fin n ↪ F) (k a : ℕ) (Mexact Mcoarse : ℕ → ℕ) : Prop :=
  ∀ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
    ZeroDirectionSafeLine dom k a u₀ u₁ →
      ZeroLowMixedChooseProfileSumsFit (F := F) (n := n) a k u₁ Mexact Mcoarse

omit [Fintype F] [NeZero n] in
open Classical in
/-- Exact failure form for one low mixed choose-profile arithmetic fit. -/
theorem not_zeroLowMixedChooseProfileSumsFit_iff_exists_sum_gt
    (a k : ℕ) (u₁ : Fin n → F) (Mexact Mcoarse : ℕ → ℕ) :
    (¬ ZeroLowMixedChooseProfileSumsFit (F := F) (n := n) a k u₁ Mexact Mcoarse) ↔
      ∃ t : ℕ, t < a ∧ t < k ∧ ∃ S : Finset (Fin n),
        S ∈ (directionZeroSet u₁).powersetCard t ∧
        Mcoarse t <
          ∑ r ∈ Finset.range a,
            ((directionZeroSet u₁).card - t).choose (r - t) *
              (if r < k then Mexact r else 1) := by
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro t ht htk S hS
    exact le_of_not_gt
      (fun hgt => hnone ⟨t, ht, htk, S, hS, hgt⟩)
  · rintro ⟨t, ht, htk, S, hS, hgt⟩ hFit
    exact not_lt_of_ge (hFit t ht htk S hS) hgt

open Classical in
omit [Fintype F] [NeZero n] in
/-- Uniform exact failure form for the low mixed choose-profile arithmetic fit. -/
theorem
    not_uniformLargeZeroSafeLowMixedChooseProfileSumsFit_iff_exists_sum_gt
    (dom : Fin n ↪ F) (k a : ℕ) (Mexact Mcoarse : ℕ → ℕ) :
    (¬ UniformLargeZeroSafeLowMixedChooseProfileSumsFit
        (F := F) (n := n) dom k a Mexact Mcoarse) ↔
      ∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
        ZeroDirectionSafeLine dom k a u₀ u₁ ∧
          ∃ t : ℕ, t < a ∧ t < k ∧ ∃ S : Finset (Fin n),
            S ∈ (directionZeroSet u₁).powersetCard t ∧
            Mcoarse t <
              ∑ r ∈ Finset.range a,
                ((directionZeroSet u₁).card - t).choose (r - t) *
                  (if r < k then Mexact r else 1) := by
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro u₀ u₁ hnotEligible hsafe
    by_contra hLine
    rcases
        (not_zeroLowMixedChooseProfileSumsFit_iff_exists_sum_gt
          (F := F) (n := n) a k u₁ Mexact Mcoarse).mp hLine with
      ⟨t, ht, htk, S, hS, hgt⟩
    exact hnone ⟨u₀, u₁, hnotEligible, hsafe, t, ht, htk, S, hS, hgt⟩
  · rintro ⟨u₀, u₁, hnotEligible, hsafe, t, ht, htk, S, hS, hgt⟩ hFit
    exact
      (not_zeroLowMixedChooseProfileSumsFit_iff_exists_sum_gt
        (F := F) (n := n) a k u₁ Mexact Mcoarse).mpr
        ⟨t, ht, htk, S, hS, hgt⟩
        (hFit u₀ u₁ hnotEligible hsafe)

omit [Fintype F] [NeZero n] in
open Classical in
/-- Every summand of a fitted low mixed choose-profile sum is individually below the coarse
budget. -/
theorem lowMixedChooseProfileSumsFit_term_le
    {a k t r : ℕ} {u₁ : Fin n → F} {S : Finset (Fin n)} {Mexact Mcoarse : ℕ → ℕ}
    (hFit : ZeroLowMixedChooseProfileSumsFit (F := F) (n := n) a k u₁ Mexact Mcoarse)
    (ht : t < a) (htk : t < k) (hS : S ∈ (directionZeroSet u₁).powersetCard t)
    (hr : r < a) :
    ((directionZeroSet u₁).card - t).choose (r - t) *
        (if r < k then Mexact r else 1) ≤ Mcoarse t := by
  have hterm :
      ((directionZeroSet u₁).card - t).choose (r - t) *
          (if r < k then Mexact r else 1) ≤
        ∑ r ∈ Finset.range a,
          ((directionZeroSet u₁).card - t).choose (r - t) *
            (if r < k then Mexact r else 1) := by
    exact Finset.single_le_sum
      (f := fun r =>
        ((directionZeroSet u₁).card - t).choose (r - t) *
          (if r < k then Mexact r else 1))
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hr)
  exact le_trans hterm (hFit t ht htk S hS)

omit [Fintype F] [NeZero n] in
open Classical in
/-- A low mixed choose-profile fit must dominate the original low exact-profile envelope at the
same profile. -/
theorem lowMixedChooseProfileSumsFit_exact_le
    {a k t : ℕ} {u₁ : Fin n → F} {S : Finset (Fin n)} {Mexact Mcoarse : ℕ → ℕ}
    (hFit : ZeroLowMixedChooseProfileSumsFit (F := F) (n := n) a k u₁ Mexact Mcoarse)
    (ht : t < a) (htk : t < k) (hS : S ∈ (directionZeroSet u₁).powersetCard t) :
    Mexact t ≤ Mcoarse t := by
  have hterm := lowMixedChooseProfileSumsFit_term_le
    (F := F) (n := n) (r := t) hFit ht htk hS ht
  simpa [htk] using hterm

omit [Fintype F] [NeZero n] in
open Classical in
/-- A high exact-superset singleton contribution is already a necessary arithmetic condition for
the low mixed choose-profile fit. -/
theorem lowMixedChooseProfileSumsFit_high_choose_le
    {a k t r : ℕ} {u₁ : Fin n → F} {S : Finset (Fin n)} {Mexact Mcoarse : ℕ → ℕ}
    (hFit : ZeroLowMixedChooseProfileSumsFit (F := F) (n := n) a k u₁ Mexact Mcoarse)
    (ht : t < a) (htk : t < k) (hS : S ∈ (directionZeroSet u₁).powersetCard t)
    (hr : r < a) (hkr : k ≤ r) :
    ((directionZeroSet u₁).card - t).choose (r - t) ≤ Mcoarse t := by
  have hterm := lowMixedChooseProfileSumsFit_term_le
    (F := F) (n := n) (r := r) hFit ht htk hS hr
  simpa [not_lt_of_ge hkr] using hterm

omit [Fintype F] [NeZero n] in
open Classical in
/-- One over-budget low mixed choose-profile summand refutes the arithmetic fit. -/
theorem not_zeroLowMixedChooseProfileSumsFit_of_exists_term_gt
    {a k t r : ℕ} {u₁ : Fin n → F} {S : Finset (Fin n)} {Mexact Mcoarse : ℕ → ℕ}
    (ht : t < a) (htk : t < k) (hS : S ∈ (directionZeroSet u₁).powersetCard t)
    (hr : r < a)
    (hgt : Mcoarse t <
      ((directionZeroSet u₁).card - t).choose (r - t) *
        (if r < k then Mexact r else 1)) :
    ¬ ZeroLowMixedChooseProfileSumsFit (F := F) (n := n) a k u₁ Mexact Mcoarse := by
  intro hFit
  exact not_lt_of_ge
    (lowMixedChooseProfileSumsFit_term_le
      (F := F) (n := n) (r := r) hFit ht htk hS hr) hgt

omit [Fintype F] [NeZero n] in
open Classical in
/-- One over-budget high singleton exact-superset term refutes the low mixed choose-profile fit. -/
theorem not_zeroLowMixedChooseProfileSumsFit_of_high_choose_gt
    {a k t r : ℕ} {u₁ : Fin n → F} {S : Finset (Fin n)} {Mexact Mcoarse : ℕ → ℕ}
    (ht : t < a) (htk : t < k) (hS : S ∈ (directionZeroSet u₁).powersetCard t)
    (hr : r < a) (hkr : k ≤ r)
    (hgt : Mcoarse t < ((directionZeroSet u₁).card - t).choose (r - t)) :
    ¬ ZeroLowMixedChooseProfileSumsFit (F := F) (n := n) a k u₁ Mexact Mcoarse := by
  intro hFit
  exact not_lt_of_ge
    (lowMixedChooseProfileSumsFit_high_choose_le
      (F := F) (n := n) (r := r) hFit ht htk hS hr hkr) hgt

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
        ∃ t : ℕ, t < a ∧ t < k ∧ ∃ S : Finset (Fin n),
          S ∈ (directionZeroSet u₁).powersetCard t ∧
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
          ∃ t : ℕ, t < a ∧ t < k ∧ ∃ S : Finset (Fin n),
            S ∈ (directionZeroSet u₁).powersetCard t ∧
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
          ∃ t : ℕ, t < a ∧ ∃ S : Finset (Fin n),
            S ∈ (directionZeroSet u₁).powersetCard t ∧
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

open Classical in
/-- Cardinal-profile version of
`uniformLineBadScalarsBudgeted_of_lowExact_mixedChooseProfileSums`.  The mixed profile sum is
independent of the actual subset `S`; it only depends on `#zeroSet(u₁)`.  This wrapper exposes the
remaining low-profile residual as a pure arithmetic statement over cardinalities `z ≤ n`. -/
theorem uniformLineBadScalarsBudgeted_of_lowExact_mixedChooseProfileCardSums
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a L B : ℕ)
    (Mexact Mcoarse : ℕ → ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hExactLow :
      UniformLargeZeroSafeLowExactAppearingZeroAgreementFiberBudgeted dom k a Mexact)
    (hProfileCard :
      ∀ z t : ℕ, a ≤ z → z ≤ n → t < a → t < k →
        (∑ r ∈ Finset.range a,
          (z - t).choose (r - t) * (if r < k then Mexact r else 1)) ≤ Mcoarse t)
    (hHigh : ∀ t : ℕ, t < a → k ≤ t → 1 ≤ Mcoarse t)
    (hFiberFits :
      UniformLargeZeroSafeAppearingCoordinateFiberBudgetFits (F := F) (n := n) a B Mcoarse) :
    UniformLineBadScalarsBudgeted dom k a B :=
  uniformLineBadScalarsBudgeted_of_lowExact_mixedChooseProfileSums
    dom hk a L B Mexact Mcoarse hSupport hFits hZeroSafe hExactLow
    (by
      intro u₀ u₁ hnotEligible _hsafe t ht htk S _hS
      have hzlo : a ≤ (directionZeroSet u₁).card := le_of_not_gt hnotEligible
      have hzhi : (directionZeroSet u₁).card ≤ n := by
        simpa using (Finset.card_le_univ (directionZeroSet u₁))
      simpa using hProfileCard (directionZeroSet u₁).card t hzlo hzhi ht htk)
    hHigh hFiberFits

open Classical in
/-- Scanner-facing cardinal-profile version of the mixed low-exact route.  Once support-side
production, weighted fits, and high-profile singleton ceilings are fixed, failed production
returns either zero-direction saturation or a concrete cardinal pair `(z,t)` whose mixed profile
sum exceeds the proposed coarse budget. -/
theorem unsafe_or_largeZero_safe_low_mixedChooseProfileCard_gt_of_not_uniformLineBadScalarsBudgeted
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
      (∃ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
        a ≤ (directionZeroSet u₁).card ∧ (directionZeroSet u₁).card ≤ n ∧
          ∃ t : ℕ, t < a ∧ t < k ∧
            Mcoarse t <
              ∑ r ∈ Finset.range a,
                ((directionZeroSet u₁).card - t).choose (r - t) *
                  (if r < k then Mexact r else 1)) := by
  rcases
      (unsafe_or_largeZero_safe_low_mixedChooseProfile_gt_of_not_uniformLineBadScalarsBudgeted
        dom hk a L B Mexact Mcoarse hSupport hFits hExactLow hHigh hFiberFits hnot) with
    hUnsafe | hProfile
  · exact Or.inl hUnsafe
  · rcases hProfile with
      ⟨_u₀, u₁, hnotEligible, _hsafe, t, ht, htk, _S, _hS, hgt⟩
    have hzlo : a ≤ (directionZeroSet u₁).card := le_of_not_gt hnotEligible
    have hzhi : (directionZeroSet u₁).card ≤ n := by
      simpa using (Finset.card_le_univ (directionZeroSet u₁))
    exact Or.inr ⟨u₁, hnotEligible, hzlo, hzhi, t, ht, htk, hgt⟩

open Classical in
/-- Cardinal-profile version of the full mixed low-exact/high-singleton choose-profile route. -/
theorem uniformLineBadScalarsBudgeted_of_lowExact_fullMixedChooseProfileCardSums
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a L B : ℕ)
    (Mexact Mcoarse : ℕ → ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hLowExact :
      UniformLargeZeroSafeLowExactAppearingZeroAgreementFiberBudgeted dom k a Mexact)
    (hProfileCard :
      ∀ z t : ℕ, a ≤ z → z ≤ n → t < a →
        (∑ r ∈ Finset.range a,
          (z - t).choose (r - t) * (if r < k then Mexact r else 1)) ≤ Mcoarse t)
    (hFiberFits :
      UniformLargeZeroSafeAppearingCoordinateFiberBudgetFits (F := F) (n := n) a B Mcoarse) :
    UniformLineBadScalarsBudgeted dom k a B :=
  uniformLineBadScalarsBudgeted_of_lowExact_fullMixedChooseProfileSums
    dom hk a L B Mexact Mcoarse hSupport hFits hZeroSafe hLowExact
    (by
      intro u₀ u₁ hnotEligible _hsafe t ht S _hS
      have hzlo : a ≤ (directionZeroSet u₁).card := le_of_not_gt hnotEligible
      have hzhi : (directionZeroSet u₁).card ≤ n := by
        simpa using (Finset.card_le_univ (directionZeroSet u₁))
      simpa using hProfileCard (directionZeroSet u₁).card t hzlo hzhi ht)
    hFiberFits

open Classical in
/-- Scanner-facing cardinal-profile version of the full mixed choose-profile route. -/
theorem
    unsafe_or_largeZero_safe_fullMixedChooseProfileCard_gt_of_not_uniformLineBadScalarsBudgeted
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
      (∃ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
        a ≤ (directionZeroSet u₁).card ∧ (directionZeroSet u₁).card ≤ n ∧
          ∃ t : ℕ, t < a ∧
            Mcoarse t <
              ∑ r ∈ Finset.range a,
                ((directionZeroSet u₁).card - t).choose (r - t) *
                  (if r < k then Mexact r else 1)) := by
  rcases
      (unsafe_or_largeZero_safe_fullMixedChooseProfile_gt_of_not_uniformLineBadScalarsBudgeted
        dom hk a L B Mexact Mcoarse hSupport hFits hLowExact hFiberFits hnot) with
    hUnsafe | hProfile
  · exact Or.inl hUnsafe
  · rcases hProfile with
      ⟨_u₀, u₁, hnotEligible, _hsafe, t, ht, _S, _hS, hgt⟩
    have hzlo : a ≤ (directionZeroSet u₁).card := le_of_not_gt hnotEligible
    have hzhi : (directionZeroSet u₁).card ≤ n := by
      simpa using (Finset.card_le_univ (directionZeroSet u₁))
    exact Or.inr ⟨u₁, hnotEligible, hzlo, hzhi, t, ht, hgt⟩

open Classical in
/-- The all-threshold support-ratio cover envelope supplies the low exact-profile budget needed by
the mixed exact-to-coarse route.  This composes the support-ratio `|F|^(k-a)` interpolation-tail
budget with the low-coarse mixed choose-profile consumer; the remaining non-structural input is
the explicit mixed profile arithmetic over low coarse profiles `t < k`. -/
theorem uniformLineBadScalarsBudgeted_of_lineFiberCoverFieldPow_mixedChooseProfileSums
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a L B : ℕ) (Mcoarse : ℕ → ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hProfile :
      ∀ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
        ZeroDirectionSafeLine dom k a u₀ u₁ →
          ∀ t : ℕ, t < a → t < k →
            ∀ S ∈ (directionZeroSet u₁).powersetCard t,
              (∑ r ∈ Finset.range a,
                ((directionZeroSet u₁).card - t).choose (r - t) *
                  (if r < k then
                    Fintype.card F * (n.choose (a - r) * Fintype.card F ^ (k - a))
                  else 1)) ≤ Mcoarse t)
    (hHigh : ∀ t : ℕ, t < a → k ≤ t → 1 ≤ Mcoarse t)
    (hFiberFits :
      UniformLargeZeroSafeAppearingCoordinateFiberBudgetFits (F := F) (n := n) a B Mcoarse) :
    UniformLineBadScalarsBudgeted dom k a B := by
  let Mexact : ℕ → ℕ :=
    fun r => Fintype.card F * (n.choose (a - r) * Fintype.card F ^ (k - a))
  have hExactLow :
      UniformLargeZeroSafeLowExactAppearingZeroAgreementFiberBudgeted dom k a Mexact := by
    intro u₀ u₁ hnotEligible hsafe t ht htk S hS
    exact uniformExactAppearingZeroAgreementFiberBudgeted_of_lineFiberCoverFieldPow_n
      dom k a u₀ u₁ hnotEligible hsafe t ht S hS
  exact uniformLineBadScalarsBudgeted_of_lowExact_mixedChooseProfileSums
    dom hk a L B Mexact Mcoarse hSupport hFits hZeroSafe hExactLow
    (by
      intro u₀ u₁ hnotEligible hsafe t ht htk S hS
      simpa [Mexact] using hProfile u₀ u₁ hnotEligible hsafe t ht htk S hS)
    hHigh hFiberFits

open Classical in
/-- Scanner-facing version of
`uniformLineBadScalarsBudgeted_of_lineFiberCoverFieldPow_mixedChooseProfileSums`.  Once the
support-side hypotheses and weighted coarse fit are fixed, failed production exposes either
zero-direction saturation or a low coarse profile whose support-ratio-field-power mixed profile
sum is too large. -/
theorem unsafe_or_largeZero_safe_fieldPow_mixedProfile_gt_of_not_budgeted
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a L B : ℕ) (Mcoarse : ℕ → ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
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
                  (if r < k then
                    Fintype.card F * (n.choose (a - r) * Fintype.card F ^ (k - a))
                  else 1)) := by
  let Mexact : ℕ → ℕ :=
    fun r => Fintype.card F * (n.choose (a - r) * Fintype.card F ^ (k - a))
  have hExactLow :
      UniformLargeZeroSafeLowExactAppearingZeroAgreementFiberBudgeted dom k a Mexact := by
    intro u₀ u₁ hnotEligible hsafe t ht htk S hS
    exact uniformExactAppearingZeroAgreementFiberBudgeted_of_lineFiberCoverFieldPow_n
      dom k a u₀ u₁ hnotEligible hsafe t ht S hS
  simpa [Mexact] using
    unsafe_or_largeZero_safe_low_mixedChooseProfile_gt_of_not_uniformLineBadScalarsBudgeted
      dom hk a L B Mexact Mcoarse hSupport hFits hExactLow hHigh hFiberFits hnot

open Classical in
/-- Full-coarse-profile variant of
`uniformLineBadScalarsBudgeted_of_lineFiberCoverFieldPow_mixedChooseProfileSums`: the
support-ratio field-power exact budget feeds the full mixed choose-profile consumer when the mixed
profile inequality is available for every coarse profile `t < a`. -/
theorem uniformLineBadScalarsBudgeted_of_lineFiberCoverFieldPow_fullMixedChooseProfileSums
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a L B : ℕ) (Mcoarse : ℕ → ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hProfile :
      ∀ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
        ZeroDirectionSafeLine dom k a u₀ u₁ →
          ∀ t : ℕ, t < a → ∀ S ∈ (directionZeroSet u₁).powersetCard t,
            (∑ r ∈ Finset.range a,
              ((directionZeroSet u₁).card - t).choose (r - t) *
                (if r < k then
                  Fintype.card F * (n.choose (a - r) * Fintype.card F ^ (k - a))
                else 1)) ≤ Mcoarse t)
    (hFiberFits :
      UniformLargeZeroSafeAppearingCoordinateFiberBudgetFits (F := F) (n := n) a B Mcoarse) :
    UniformLineBadScalarsBudgeted dom k a B := by
  let Mexact : ℕ → ℕ :=
    fun r => Fintype.card F * (n.choose (a - r) * Fintype.card F ^ (k - a))
  have hExactLow :
      UniformLargeZeroSafeLowExactAppearingZeroAgreementFiberBudgeted dom k a Mexact := by
    intro u₀ u₁ hnotEligible hsafe t ht htk S hS
    exact uniformExactAppearingZeroAgreementFiberBudgeted_of_lineFiberCoverFieldPow_n
      dom k a u₀ u₁ hnotEligible hsafe t ht S hS
  exact uniformLineBadScalarsBudgeted_of_lowExact_fullMixedChooseProfileSums
    dom hk a L B Mexact Mcoarse hSupport hFits hZeroSafe hExactLow
    (by
      intro u₀ u₁ hnotEligible hsafe t ht S hS
      simpa [Mexact] using hProfile u₀ u₁ hnotEligible hsafe t ht S hS)
    hFiberFits

open Classical in
/-- Scanner-facing full-coarse-profile variant for the support-ratio-field-power mixed route. -/
theorem unsafe_or_largeZero_safe_fieldPow_fullMixedProfile_gt_of_not_budgeted
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a L B : ℕ) (Mcoarse : ℕ → ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
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
                  (if r < k then
                    Fintype.card F * (n.choose (a - r) * Fintype.card F ^ (k - a))
                  else 1)) := by
  let Mexact : ℕ → ℕ :=
    fun r => Fintype.card F * (n.choose (a - r) * Fintype.card F ^ (k - a))
  have hExactLow :
      UniformLargeZeroSafeLowExactAppearingZeroAgreementFiberBudgeted dom k a Mexact := by
    intro u₀ u₁ hnotEligible hsafe t ht htk S hS
    exact uniformExactAppearingZeroAgreementFiberBudgeted_of_lineFiberCoverFieldPow_n
      dom k a u₀ u₁ hnotEligible hsafe t ht S hS
  simpa [Mexact] using
    unsafe_or_largeZero_safe_fullMixedChooseProfile_gt_of_not_uniformLineBadScalarsBudgeted
      dom hk a L B Mexact Mcoarse hSupport hFits hExactLow hFiberFits hnot

open Classical in
/-- Cardinal-profile version of
`uniformLineBadScalarsBudgeted_of_lineFiberCoverFieldPow_mixedChooseProfileSums`.  The remaining
low-profile arithmetic is a finite `z,t` inequality, where `z` is the zero-set cardinality of a
large-zero direction. -/
theorem uniformLineBadScalarsBudgeted_of_fieldPow_mixedProfileCardSums
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a L B : ℕ) (Mcoarse : ℕ → ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hProfileCard :
      ∀ z t : ℕ, a ≤ z → z ≤ n → t < a → t < k →
        (∑ r ∈ Finset.range a,
          (z - t).choose (r - t) *
            (if r < k then
              Fintype.card F * (n.choose (a - r) * Fintype.card F ^ (k - a))
            else 1)) ≤ Mcoarse t)
    (hHigh : ∀ t : ℕ, t < a → k ≤ t → 1 ≤ Mcoarse t)
    (hFiberFits :
      UniformLargeZeroSafeAppearingCoordinateFiberBudgetFits (F := F) (n := n) a B Mcoarse) :
    UniformLineBadScalarsBudgeted dom k a B := by
  let Mexact : ℕ → ℕ :=
    fun r => Fintype.card F * (n.choose (a - r) * Fintype.card F ^ (k - a))
  have hExactLow :
      UniformLargeZeroSafeLowExactAppearingZeroAgreementFiberBudgeted dom k a Mexact := by
    intro u₀ u₁ hnotEligible hsafe t ht htk S hS
    exact uniformExactAppearingZeroAgreementFiberBudgeted_of_lineFiberCoverFieldPow_n
      dom k a u₀ u₁ hnotEligible hsafe t ht S hS
  exact uniformLineBadScalarsBudgeted_of_lowExact_mixedChooseProfileCardSums
    dom hk a L B Mexact Mcoarse hSupport hFits hZeroSafe hExactLow
    (by
      intro z t hzlo hzhi ht htk
      simpa [Mexact] using hProfileCard z t hzlo hzhi ht htk)
    hHigh hFiberFits

open Classical in
/-- Scanner-facing cardinal-profile version of the support-ratio-field-power mixed route. -/
theorem unsafe_or_largeZero_safe_fieldPow_mixedProfileCard_gt_of_not_budgeted
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a L B : ℕ) (Mcoarse : ℕ → ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
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
                  (if r < k then
                    Fintype.card F * (n.choose (a - r) * Fintype.card F ^ (k - a))
                  else 1)) := by
  let Mexact : ℕ → ℕ :=
    fun r => Fintype.card F * (n.choose (a - r) * Fintype.card F ^ (k - a))
  have hExactLow :
      UniformLargeZeroSafeLowExactAppearingZeroAgreementFiberBudgeted dom k a Mexact := by
    intro u₀ u₁ hnotEligible hsafe t ht htk S hS
    exact uniformExactAppearingZeroAgreementFiberBudgeted_of_lineFiberCoverFieldPow_n
      dom k a u₀ u₁ hnotEligible hsafe t ht S hS
  simpa [Mexact] using
    unsafe_or_largeZero_safe_low_mixedChooseProfileCard_gt_of_not_uniformLineBadScalarsBudgeted
      dom hk a L B Mexact Mcoarse hSupport hFits hExactLow hHigh hFiberFits hnot

open Classical in
/-- Full cardinal-profile version of the support-ratio-field-power mixed route. -/
theorem uniformLineBadScalarsBudgeted_of_fieldPow_fullMixedProfileCardSums
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a L B : ℕ) (Mcoarse : ℕ → ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hProfileCard :
      ∀ z t : ℕ, a ≤ z → z ≤ n → t < a →
        (∑ r ∈ Finset.range a,
          (z - t).choose (r - t) *
            (if r < k then
              Fintype.card F * (n.choose (a - r) * Fintype.card F ^ (k - a))
            else 1)) ≤ Mcoarse t)
    (hFiberFits :
      UniformLargeZeroSafeAppearingCoordinateFiberBudgetFits (F := F) (n := n) a B Mcoarse) :
    UniformLineBadScalarsBudgeted dom k a B := by
  let Mexact : ℕ → ℕ :=
    fun r => Fintype.card F * (n.choose (a - r) * Fintype.card F ^ (k - a))
  have hExactLow :
      UniformLargeZeroSafeLowExactAppearingZeroAgreementFiberBudgeted dom k a Mexact := by
    intro u₀ u₁ hnotEligible hsafe t ht htk S hS
    exact uniformExactAppearingZeroAgreementFiberBudgeted_of_lineFiberCoverFieldPow_n
      dom k a u₀ u₁ hnotEligible hsafe t ht S hS
  exact uniformLineBadScalarsBudgeted_of_lowExact_fullMixedChooseProfileCardSums
    dom hk a L B Mexact Mcoarse hSupport hFits hZeroSafe hExactLow
    (by
      intro z t hzlo hzhi ht
      simpa [Mexact] using hProfileCard z t hzlo hzhi ht)
    hFiberFits

open Classical in
/-- Scanner-facing full cardinal-profile version for the support-ratio-field-power mixed route. -/
theorem unsafe_or_largeZero_safe_fieldPow_fullMixedProfileCard_gt_of_not_budgeted
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a L B : ℕ) (Mcoarse : ℕ → ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
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
                  (if r < k then
                    Fintype.card F * (n.choose (a - r) * Fintype.card F ^ (k - a))
                  else 1)) := by
  let Mexact : ℕ → ℕ :=
    fun r => Fintype.card F * (n.choose (a - r) * Fintype.card F ^ (k - a))
  have hExactLow :
      UniformLargeZeroSafeLowExactAppearingZeroAgreementFiberBudgeted dom k a Mexact := by
    intro u₀ u₁ hnotEligible hsafe t ht htk S hS
    exact uniformExactAppearingZeroAgreementFiberBudgeted_of_lineFiberCoverFieldPow_n
      dom k a u₀ u₁ hnotEligible hsafe t ht S hS
  simpa [Mexact] using
    unsafe_or_largeZero_safe_fullMixedChooseProfileCard_gt_of_not_uniformLineBadScalarsBudgeted
      dom hk a L B Mexact Mcoarse hSupport hFits hExactLow hFiberFits hnot

section SourceAudit

#print axioms ZeroLowMixedChooseProfileSumsFit
#print axioms UniformLargeZeroSafeLowMixedChooseProfileSumsFit
#print axioms not_zeroLowMixedChooseProfileSumsFit_iff_exists_sum_gt
#print axioms not_uniformLargeZeroSafeLowMixedChooseProfileSumsFit_iff_exists_sum_gt
#print axioms lowMixedChooseProfileSumsFit_term_le
#print axioms lowMixedChooseProfileSumsFit_exact_le
#print axioms lowMixedChooseProfileSumsFit_high_choose_le
#print axioms not_zeroLowMixedChooseProfileSumsFit_of_exists_term_gt
#print axioms not_zeroLowMixedChooseProfileSumsFit_of_high_choose_gt
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
#print axioms uniformLineBadScalarsBudgeted_of_lowExact_mixedChooseProfileCardSums
#print axioms
  unsafe_or_largeZero_safe_low_mixedChooseProfileCard_gt_of_not_uniformLineBadScalarsBudgeted
#print axioms uniformLineBadScalarsBudgeted_of_lowExact_fullMixedChooseProfileCardSums
#print axioms
  unsafe_or_largeZero_safe_fullMixedChooseProfileCard_gt_of_not_uniformLineBadScalarsBudgeted
#print axioms uniformLineBadScalarsBudgeted_of_lineFiberCoverFieldPow_mixedChooseProfileSums
#print axioms
  unsafe_or_largeZero_safe_fieldPow_mixedProfile_gt_of_not_budgeted
#print axioms uniformLineBadScalarsBudgeted_of_lineFiberCoverFieldPow_fullMixedChooseProfileSums
#print axioms
  unsafe_or_largeZero_safe_fieldPow_fullMixedProfile_gt_of_not_budgeted
#print axioms uniformLineBadScalarsBudgeted_of_fieldPow_mixedProfileCardSums
#print axioms unsafe_or_largeZero_safe_fieldPow_mixedProfileCard_gt_of_not_budgeted
#print axioms uniformLineBadScalarsBudgeted_of_fieldPow_fullMixedProfileCardSums
#print axioms unsafe_or_largeZero_safe_fieldPow_fullMixedProfileCard_gt_of_not_budgeted

end SourceAudit

end ProximityGap.Ownership
