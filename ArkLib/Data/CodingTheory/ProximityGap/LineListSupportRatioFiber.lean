/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LineListAppearanceFiber

/-!
# Support-ratio fibers for appearance-filtered line lists

The raw coordinate-fiber envelope counts every RS interpolation completion over a zero-direction
set.  `LineListAppearanceFiber.lean` replaces this with codewords that actually appear somewhere
on the affine line.  This file exposes the next structural filter: an appearing codeword must have
a heavy fiber for the support-ratio map

```text
i ↦ (c i - u₀ i) / u₁ i
```

on the nonzero support of the direction.  Thus exact appearance fibers are contained in coordinate
fibers whose support-ratio map has a fiber of size at least `a - t`, where `t` is the exact
zero-direction agreement profile.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- The support-ratio fiber of a codeword along a line direction: moving-support coordinates whose
unique scalar is `γ`. -/
noncomputable def supportRatioFiber (c u₀ u₁ : Fin n → F) (γ : F) : Finset (Fin n) :=
  (directionSupportSet u₁).filter (fun i => (c i - u₀ i) / u₁ i = γ)

omit [Fintype F] in
open Classical in
theorem mem_supportRatioFiber (c u₀ u₁ : Fin n → F) (γ : F) (i : Fin n) :
    i ∈ supportRatioFiber c u₀ u₁ γ ↔
      i ∈ directionSupportSet u₁ ∧ (c i - u₀ i) / u₁ i = γ := by
  rw [supportRatioFiber, Finset.mem_filter]

omit [Fintype F] in
open Classical in
/-- The reusable cardinal form of the punctured support-ratio agreement bound. -/
theorem agreeSet_line_card_le_zeroAgreement_add_supportRatioFiber
    (c u₀ u₁ : Fin n → F) (γ : F) :
    (agreeSet c (fun i => u₀ i + γ • u₁ i)).card
      ≤ (directionZeroAgreementSet c u₀ u₁).card +
        (supportRatioFiber c u₀ u₁ γ).card := by
  simpa [supportRatioFiber] using
    agreeSet_line_card_le_zeroAgreement_add_movingFiber c u₀ u₁ γ

open Classical in
/-- Any appearing codeword has a support-ratio fiber large enough to supply the moving coordinates
not already supplied by zero-direction agreements. -/
theorem exists_supportRatioFiber_card_ge_sub_of_mem_lineAppearingCodewords
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ c : Fin n → F)
    (hc : c ∈ lineAppearingCodewords dom k a u₀ u₁) :
    ∃ γ : F, a - (directionZeroAgreementSet c u₀ u₁).card
      ≤ (supportRatioFiber c u₀ u₁ γ).card := by
  rw [lineAppearingCodewords, Finset.mem_filter] at hc
  rcases hc.2.2 with ⟨γ, hheavy⟩
  refine ⟨γ, ?_⟩
  have hcard := agreeSet_line_card_le_zeroAgreement_add_supportRatioFiber c u₀ u₁ γ
  omega

open Classical in
/-- Exact appearance over a zero-agreement set `S` forces a support-ratio fiber of size
`a - #S`. -/
theorem exists_supportRatioFiber_card_ge_sub_of_mem_exactAppearingZeroAgreementFiber
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ c : Fin n → F) (S : Finset (Fin n))
    (hc : c ∈ exactAppearingZeroAgreementFiber dom k a u₀ u₁ S) :
    ∃ γ : F, a - S.card ≤ (supportRatioFiber c u₀ u₁ γ).card := by
  rw [mem_exactAppearingZeroAgreementFiber] at hc
  rcases exists_supportRatioFiber_card_ge_sub_of_mem_lineAppearingCodewords
      dom k a u₀ u₁ c hc.1 with ⟨γ, hγ⟩
  refine ⟨γ, ?_⟩
  simpa [hc.2] using hγ

open Classical in
/-- Coordinate fiber restricted to codewords whose support-ratio map has a heavy enough fiber.
This is the concrete counting object left after replacing raw interpolation by actual line
appearance. -/
noncomputable def supportRatioHeavyCoordinateFiber
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (S : Finset (Fin n)) :
    Finset (Fin n → F) :=
  (coordinateAgreementFiber dom k u₀ S).filter
    (fun c => ∃ γ : F, a - S.card ≤ (supportRatioFiber c u₀ u₁ γ).card)

open Classical in
theorem mem_supportRatioHeavyCoordinateFiber
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ c : Fin n → F) (S : Finset (Fin n)) :
    c ∈ supportRatioHeavyCoordinateFiber dom k a u₀ u₁ S ↔
      c ∈ coordinateAgreementFiber dom k u₀ S ∧
        ∃ γ : F, a - S.card ≤ (supportRatioFiber c u₀ u₁ γ).card := by
  rw [supportRatioHeavyCoordinateFiber, Finset.mem_filter]

open Classical in
/-- Exact appearance fibers are contained in the corresponding support-ratio-heavy coordinate
fiber.  This isolates the missing positive estimate: count interpolation completions with one
large ratio fiber, not all interpolation completions. -/
theorem exactAppearingZeroAgreementFiber_subset_supportRatioHeavyCoordinateFiber
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (S : Finset (Fin n)) :
    exactAppearingZeroAgreementFiber dom k a u₀ u₁ S ⊆
      supportRatioHeavyCoordinateFiber dom k a u₀ u₁ S := by
  intro c hc
  rw [mem_supportRatioHeavyCoordinateFiber]
  have hcApp :
      c ∈ appearingCoordinateAgreementFiber dom k a u₀ u₁ S :=
    exactAppearingZeroAgreementFiber_subset_appearingCoordinateAgreementFiber
      dom k a u₀ u₁ S hc
  exact ⟨(mem_appearingCoordinateAgreementFiber dom k a u₀ u₁ c S).mp hcApp |>.1,
    exists_supportRatioFiber_card_ge_sub_of_mem_exactAppearingZeroAgreementFiber
      dom k a u₀ u₁ c S hc⟩

open Classical in
/-- Cardinal version of exact-appearance domination by the support-ratio-heavy coordinate fiber. -/
theorem exactAppearingZeroAgreementFiber_card_le_supportRatioHeavyCoordinateFiber_card
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (S : Finset (Fin n)) :
    (exactAppearingZeroAgreementFiber dom k a u₀ u₁ S).card ≤
      (supportRatioHeavyCoordinateFiber dom k a u₀ u₁ S).card :=
  Finset.card_le_card
    (exactAppearingZeroAgreementFiber_subset_supportRatioHeavyCoordinateFiber
      dom k a u₀ u₁ S)

open Classical in
/-- Explicit finite cover of a support-ratio-heavy coordinate fiber.  The cover records the
heavy scalar `γ` and an `(a - #S)`-element subfiber `T` on the moving support, then asks for
ordinary coordinate agreement with the line word `u₀ + γ • u₁` on `S ∪ T`. -/
noncomputable def supportRatioLineFiberCover
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (S : Finset (Fin n)) :
    Finset (Fin n → F) :=
  (Finset.univ : Finset F).biUnion fun γ =>
    ((directionSupportSet u₁).powersetCard (a - S.card)).biUnion fun T =>
      coordinateAgreementFiber dom k (fun i => u₀ i + γ • u₁ i) (S ∪ T)

open Classical in
/-- A support-ratio-heavy coordinate fiber over zero-direction coordinates is covered by
ordinary coordinate fibers on the base zero profile plus a selected moving support-ratio fiber. -/
theorem supportRatioHeavyCoordinateFiber_subset_supportRatioLineFiberCover
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) {S : Finset (Fin n)}
    (hSzero : S ⊆ directionZeroSet u₁) :
    supportRatioHeavyCoordinateFiber dom k a u₀ u₁ S ⊆
      supportRatioLineFiberCover dom k a u₀ u₁ S := by
  intro c hc
  rw [mem_supportRatioHeavyCoordinateFiber] at hc
  rcases hc with ⟨hcCoord, γ, hheavy⟩
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hheavy
  have hTmem : T ∈ (directionSupportSet u₁).powersetCard (a - S.card) := by
    refine Finset.mem_powersetCard.mpr ⟨?_, hTcard⟩
    intro i hi
    exact ((mem_supportRatioFiber c u₀ u₁ γ i).mp (hTsub hi)).1
  have hcLine :
      c ∈ coordinateAgreementFiber dom k (fun i => u₀ i + γ • u₁ i) (S ∪ T) := by
    rw [coordinateAgreementFiber, Finset.mem_filter] at hcCoord ⊢
    refine ⟨Finset.mem_univ _, hcCoord.2.1, ?_⟩
    intro i hi
    rcases Finset.mem_union.mp hi with hiS | hiT
    · have hzero : u₁ i = 0 := by
        simpa [directionZeroSet] using hSzero hiS
      calc
        c i = u₀ i := hcCoord.2.2 i hiS
        _ = u₀ i + γ • u₁ i := by
          rw [hzero]
          simp
    · have hratio := (mem_supportRatioFiber c u₀ u₁ γ i).mp (hTsub hiT)
      have hnonzero : u₁ i ≠ 0 := by
        simpa [directionSupportSet] using hratio.1
      have hdiv : (c i - u₀ i) / u₁ i = γ := hratio.2
      rw [div_eq_iff hnonzero] at hdiv
      rw [smul_eq_mul, ← hdiv]
      ring
  rw [supportRatioLineFiberCover]
  refine Finset.mem_biUnion.mpr ⟨γ, Finset.mem_univ _, ?_⟩
  exact Finset.mem_biUnion.mpr ⟨T, hTmem, hcLine⟩

open Classical in
/-- Cardinal form of the explicit support-ratio line-fiber cover. -/
theorem supportRatioHeavyCoordinateFiber_card_le_supportRatioLineFiberCover_card
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) {S : Finset (Fin n)}
    (hSzero : S ⊆ directionZeroSet u₁) :
    (supportRatioHeavyCoordinateFiber dom k a u₀ u₁ S).card ≤
      (supportRatioLineFiberCover dom k a u₀ u₁ S).card :=
  Finset.card_le_card
    (supportRatioHeavyCoordinateFiber_subset_supportRatioLineFiberCover
      dom k a u₀ u₁ hSzero)

open Classical in
/-- Crude union-bound cardinal estimate for the explicit support-ratio line-fiber cover. -/
theorem supportRatioLineFiberCover_card_le_sum_coordinateAgreementFibers
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (S : Finset (Fin n)) :
    (supportRatioLineFiberCover dom k a u₀ u₁ S).card ≤
      ∑ γ : F, ∑ T ∈ (directionSupportSet u₁).powersetCard (a - S.card),
        (coordinateAgreementFiber dom k (fun i => u₀ i + γ • u₁ i) (S ∪ T)).card := by
  rw [supportRatioLineFiberCover]
  calc
    ((Finset.univ : Finset F).biUnion fun γ =>
        ((directionSupportSet u₁).powersetCard (a - S.card)).biUnion fun T =>
          coordinateAgreementFiber dom k (fun i => u₀ i + γ • u₁ i) (S ∪ T)).card
        ≤ ∑ γ ∈ (Finset.univ : Finset F),
            (((directionSupportSet u₁).powersetCard (a - S.card)).biUnion fun T =>
              coordinateAgreementFiber dom k (fun i => u₀ i + γ • u₁ i) (S ∪ T)).card :=
          Finset.card_biUnion_le
    _ ≤ ∑ γ ∈ (Finset.univ : Finset F),
          ∑ T ∈ (directionSupportSet u₁).powersetCard (a - S.card),
            (coordinateAgreementFiber dom k (fun i => u₀ i + γ • u₁ i) (S ∪ T)).card := by
        exact Finset.sum_le_sum fun γ _ =>
          Finset.card_biUnion_le

open Classical in
/-- Support-ratio-heavy coordinate fibers are still contained in the raw coordinate fiber. -/
theorem supportRatioHeavyCoordinateFiber_subset_coordinateAgreementFiber
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (S : Finset (Fin n)) :
    supportRatioHeavyCoordinateFiber dom k a u₀ u₁ S ⊆
      coordinateAgreementFiber dom k u₀ S := by
  intro c hc
  exact (mem_supportRatioHeavyCoordinateFiber dom k a u₀ u₁ c S).mp hc |>.1

open Classical in
/-- High support-ratio-heavy fibers are singleton-bounded by RS uniqueness, because they are
subsets of raw coordinate fibers over at least `k` prescribed coordinates. -/
theorem supportRatioHeavyCoordinateFiber_card_le_one_of_k_le
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a : ℕ)
    (u₀ u₁ : Fin n → F) {S : Finset (Fin n)} (hS : k ≤ S.card) :
    (supportRatioHeavyCoordinateFiber dom k a u₀ u₁ S).card ≤ 1 :=
  le_trans
    (Finset.card_le_card
      (supportRatioHeavyCoordinateFiber_subset_coordinateAgreementFiber
        dom k a u₀ u₁ S))
    (coordinateAgreementFiber_card_le_one_of_k_le dom hk u₀ hS)

/-- A per-line budget for support-ratio-heavy coordinate fibers. -/
def ZeroSupportRatioHeavyCoordinateFiberBudgeted
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (M : ℕ → ℕ) : Prop :=
  ∀ t : ℕ, t < a → ∀ S ∈ (directionZeroSet u₁).powersetCard t,
    (supportRatioHeavyCoordinateFiber dom k a u₀ u₁ S).card ≤ M t

/-- Uniform support-ratio-heavy coordinate-fiber budget on the large-zero safe branch. -/
def UniformLargeZeroSafeSupportRatioHeavyCoordinateFiberBudgeted
    (dom : Fin n ↪ F) (k a : ℕ) (M : ℕ → ℕ) : Prop :=
  ∀ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
    ZeroDirectionSafeLine dom k a u₀ u₁ →
      ZeroSupportRatioHeavyCoordinateFiberBudgeted dom k a u₀ u₁ M

open Classical in
/-- Support-ratio-heavy coordinate-fiber budgets imply exact appearance-fiber budgets. -/
theorem zeroExactAppearingZeroAgreementFiberBudgeted_of_supportRatioHeavyCoordinateFiberBudgeted
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (M : ℕ → ℕ)
    (hFiber : ZeroSupportRatioHeavyCoordinateFiberBudgeted dom k a u₀ u₁ M) :
    ZeroExactAppearingZeroAgreementFiberBudgeted dom k a u₀ u₁ M := by
  intro t ht S hS
  exact le_trans
    (exactAppearingZeroAgreementFiber_card_le_supportRatioHeavyCoordinateFiber_card
      dom k a u₀ u₁ S)
    (hFiber t ht S hS)

open Classical in
/-- Uniform version of
`zeroExactAppearingZeroAgreementFiberBudgeted_of_supportRatioHeavyCoordinateFiberBudgeted`. -/
theorem uniformExactAppearingZeroAgreementFiberBudgeted_of_supportRatioHeavyCoordinateFiberBudgeted
    (dom : Fin n ↪ F) (k a : ℕ) (M : ℕ → ℕ)
    (hFiber :
      UniformLargeZeroSafeSupportRatioHeavyCoordinateFiberBudgeted dom k a M) :
    UniformLargeZeroSafeExactAppearingZeroAgreementFiberBudgeted dom k a M := by
  intro u₀ u₁ hnotEligible hsafe
  exact zeroExactAppearingZeroAgreementFiberBudgeted_of_supportRatioHeavyCoordinateFiberBudgeted
    dom k a u₀ u₁ M (hFiber u₀ u₁ hnotEligible hsafe)

open Classical in
/-- Scanner-facing converse for the support-ratio-heavy coordinate-fiber route.  Once support-side
production, support arithmetic, zero-safety, and the weighted arithmetic fit are fixed, failed
bad-scalar production exposes a large-zero safe support-ratio-heavy coordinate fiber exceeding the
proposed envelope. -/
theorem
    exists_largeZero_safe_supportRatioHeavyCoordFiber_gt_of_not_uniformLineBadScalarsBudgeted
    (dom : Fin n ↪ F) (k a L B : ℕ) (M : ℕ → ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hFiberFits :
      UniformLargeZeroSafeAppearingCoordinateFiberBudgetFits (F := F) (n := n) a B M)
    (hnot : ¬ UniformLineBadScalarsBudgeted dom k a B) :
    ∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
      ZeroDirectionSafeLine dom k a u₀ u₁ ∧
        ∃ t : ℕ, t < a ∧ ∃ S ∈ (directionZeroSet u₁).powersetCard t,
          M t < (supportRatioHeavyCoordinateFiber dom k a u₀ u₁ S).card := by
  by_contra hnone
  have hFiber :
      UniformLargeZeroSafeSupportRatioHeavyCoordinateFiberBudgeted dom k a M := by
    intro u₀ u₁ hnotEligible hsafe t ht S hS
    exact le_of_not_gt
      (fun hgt => hnone ⟨u₀, u₁, hnotEligible, hsafe, t, ht, S, hS, hgt⟩)
  exact hnot
    (uniformLineBadScalarsBudgeted_of_supportAdjustedBudgetFits_and_exactAppearingFibers
      dom k a L B M hSupport hFits hZeroSafe
      (uniformExactAppearingZeroAgreementFiberBudgeted_of_supportRatioHeavyCoordinateFiberBudgeted
        dom k a M hFiber)
      hFiberFits)

open Classical in
/-- Full failure split for the support-ratio-heavy route.  Without assuming zero-direction safety
up front, failure returns either zero-direction saturation or an overfull support-ratio-heavy
coordinate fiber. -/
theorem
    unsafe_or_largeZero_safe_supportRatioHeavyCoordFiber_gt_of_not_uniformLineBadScalarsBudgeted
    (dom : Fin n ↪ F) (k a L B : ℕ) (M : ℕ → ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hFiberFits :
      UniformLargeZeroSafeAppearingCoordinateFiberBudgetFits (F := F) (n := n) a B M)
    (hnot : ¬ UniformLineBadScalarsBudgeted dom k a B) :
    (∃ u₀ u₁ c : Fin n → F, c ∈ (rsCode dom k : Submodule F (Fin n → F)) ∧
        a ≤ (directionZeroAgreementSet c u₀ u₁).card) ∨
      (∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
        ZeroDirectionSafeLine dom k a u₀ u₁ ∧
          ∃ t : ℕ, t < a ∧ ∃ S ∈ (directionZeroSet u₁).powersetCard t,
            M t < (supportRatioHeavyCoordinateFiber dom k a u₀ u₁ S).card) := by
  by_cases hZeroSafe : UniformZeroDirectionSafe dom k a
  · exact Or.inr
      (exists_largeZero_safe_supportRatioHeavyCoordFiber_gt_of_not_uniformLineBadScalarsBudgeted
          dom k a L B M hSupport hFits hZeroSafe hFiberFits hnot)
  · exact Or.inl
      ((not_uniformZeroDirectionSafe_iff_exists_line_codeword_zeroAgreement_ge
        dom k a).mp hZeroSafe)

open Classical in
/-- If `M` is at least one in every high range `k ≤ t < a`, then any overfull
support-ratio-heavy coordinate fiber must lie in the low interpolation range `t < k`. -/
theorem exists_low_supportRatioHeavyCoordinateFiber_gt_of_exists_fiber_gt_and_high_one
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a : ℕ)
    (u₀ u₁ : Fin n → F) (M : ℕ → ℕ)
    (hHigh : ∀ t : ℕ, t < a → k ≤ t → 1 ≤ M t)
    (hgt : ∃ t : ℕ, t < a ∧ ∃ S ∈ (directionZeroSet u₁).powersetCard t,
      M t < (supportRatioHeavyCoordinateFiber dom k a u₀ u₁ S).card) :
    ∃ t : ℕ, t < a ∧ t < k ∧ ∃ S ∈ (directionZeroSet u₁).powersetCard t,
      M t < (supportRatioHeavyCoordinateFiber dom k a u₀ u₁ S).card := by
  rcases hgt with ⟨t, ht, S, hS, hgt⟩
  by_cases hlow : t < k
  · exact ⟨t, ht, hlow, S, hS, hgt⟩
  · have hkt : k ≤ t := le_of_not_gt hlow
    have hScard : S.card = t := (Finset.mem_powersetCard.mp hS).2
    have hfiber :
        (supportRatioHeavyCoordinateFiber dom k a u₀ u₁ S).card ≤ 1 :=
      supportRatioHeavyCoordinateFiber_card_le_one_of_k_le dom hk a u₀ u₁
        (by rw [hScard]; exact hkt)
    have hle : (supportRatioHeavyCoordinateFiber dom k a u₀ u₁ S).card ≤ M t :=
      le_trans hfiber (hHigh t ht hkt)
    exact False.elim ((not_lt_of_ge hle) hgt)

open Classical in
/-- Scanner-facing full failure split with high support-ratio-heavy coordinate fibers discharged
by RS uniqueness.  Once `M t ≥ 1` for every high `k ≤ t < a`, a failed uniform bad-scalar budget
must expose either zero-direction saturation or a large-zero safe low support-ratio-heavy fiber. -/
theorem
    unsafe_or_largeZero_safe_low_supportRatioHeavyCoordFiber_gt_of_not_uniformLineBadScalarsBudgeted
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a L B : ℕ) (M : ℕ → ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hFiberFits :
      UniformLargeZeroSafeAppearingCoordinateFiberBudgetFits (F := F) (n := n) a B M)
    (hHigh : ∀ t : ℕ, t < a → k ≤ t → 1 ≤ M t)
    (hnot : ¬ UniformLineBadScalarsBudgeted dom k a B) :
    (∃ u₀ u₁ c : Fin n → F, c ∈ (rsCode dom k : Submodule F (Fin n → F)) ∧
        a ≤ (directionZeroAgreementSet c u₀ u₁).card) ∨
      (∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
        ZeroDirectionSafeLine dom k a u₀ u₁ ∧
          ∃ t : ℕ, t < a ∧ t < k ∧ ∃ S ∈ (directionZeroSet u₁).powersetCard t,
            M t < (supportRatioHeavyCoordinateFiber dom k a u₀ u₁ S).card) := by
  rcases
      (unsafe_or_largeZero_safe_supportRatioHeavyCoordFiber_gt_of_not_uniformLineBadScalarsBudgeted
          dom k a L B M hSupport hFits hFiberFits hnot) with hUnsafe | hFiber
  · exact Or.inl hUnsafe
  · rcases hFiber with ⟨u₀, u₁, hnotEligible, hsafe, hgt⟩
    exact Or.inr ⟨u₀, u₁, hnotEligible, hsafe,
      exists_low_supportRatioHeavyCoordinateFiber_gt_of_exists_fiber_gt_and_high_one
        dom hk a u₀ u₁ M hHigh hgt⟩

section SourceAudit

#print axioms supportRatioFiber
#print axioms mem_supportRatioFiber
#print axioms agreeSet_line_card_le_zeroAgreement_add_supportRatioFiber
#print axioms exists_supportRatioFiber_card_ge_sub_of_mem_lineAppearingCodewords
#print axioms exists_supportRatioFiber_card_ge_sub_of_mem_exactAppearingZeroAgreementFiber
#print axioms supportRatioHeavyCoordinateFiber
#print axioms exactAppearingZeroAgreementFiber_subset_supportRatioHeavyCoordinateFiber
#print axioms exactAppearingZeroAgreementFiber_card_le_supportRatioHeavyCoordinateFiber_card
#print axioms supportRatioLineFiberCover
#print axioms supportRatioHeavyCoordinateFiber_subset_supportRatioLineFiberCover
#print axioms supportRatioHeavyCoordinateFiber_card_le_supportRatioLineFiberCover_card
#print axioms supportRatioLineFiberCover_card_le_sum_coordinateAgreementFibers
#print axioms supportRatioHeavyCoordinateFiber_subset_coordinateAgreementFiber
#print axioms supportRatioHeavyCoordinateFiber_card_le_one_of_k_le
#print axioms
  zeroExactAppearingZeroAgreementFiberBudgeted_of_supportRatioHeavyCoordinateFiberBudgeted
#print axioms
  uniformExactAppearingZeroAgreementFiberBudgeted_of_supportRatioHeavyCoordinateFiberBudgeted
#print axioms
  exists_largeZero_safe_supportRatioHeavyCoordFiber_gt_of_not_uniformLineBadScalarsBudgeted
#print axioms
  unsafe_or_largeZero_safe_supportRatioHeavyCoordFiber_gt_of_not_uniformLineBadScalarsBudgeted
#print axioms
  exists_low_supportRatioHeavyCoordinateFiber_gt_of_exists_fiber_gt_and_high_one
#print axioms
  unsafe_or_largeZero_safe_low_supportRatioHeavyCoordFiber_gt_of_not_uniformLineBadScalarsBudgeted

end SourceAudit

end ProximityGap.Ownership
