/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LineListReduction

/-!
# Appearance-filtered coordinate fibers for the line-list route

`LineListReduction.lean` shows that each low zero-agreement stratum is covered by raw affine
coordinate fibers.  `LineListArithmeticObstruction.lean` then shows why the raw field-power
envelope is too large: it counts every interpolation completion, even codewords that never appear
on the affine line.  This file introduces the smaller object that future positive estimates should
target: a coordinate fiber filtered by `lineAppearingCodewords`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longFile 1700

open Finset

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- Coordinate-agreement fiber restricted to codewords that actually appear somewhere on the
line. -/
noncomputable def appearingCoordinateAgreementFiber
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (S : Finset (Fin n)) :
    Finset (Fin n → F) :=
  (coordinateAgreementFiber dom k u₀ S).filter
    (fun c => c ∈ lineAppearingCodewords dom k a u₀ u₁)

open Classical in
theorem mem_appearingCoordinateAgreementFiber
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ c : Fin n → F) (S : Finset (Fin n)) :
    c ∈ appearingCoordinateAgreementFiber dom k a u₀ u₁ S ↔
      c ∈ coordinateAgreementFiber dom k u₀ S ∧
        c ∈ lineAppearingCodewords dom k a u₀ u₁ := by
  rw [appearingCoordinateAgreementFiber, Finset.mem_filter]

open Classical in
/-- Appearance-filtered fibers are bounded by the corresponding raw coordinate fiber. -/
theorem appearingCoordinateAgreementFiber_subset_coordinateAgreementFiber
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (S : Finset (Fin n)) :
    appearingCoordinateAgreementFiber dom k a u₀ u₁ S ⊆
      coordinateAgreementFiber dom k u₀ S := by
  intro c hc
  exact (mem_appearingCoordinateAgreementFiber dom k a u₀ u₁ c S).mp hc |>.1

open Classical in
/-- Cardinal version of the raw-fiber domination. -/
theorem appearingCoordinateAgreementFiber_card_le_coordinateAgreementFiber_card
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (S : Finset (Fin n)) :
    (appearingCoordinateAgreementFiber dom k a u₀ u₁ S).card ≤
      (coordinateAgreementFiber dom k u₀ S).card :=
  Finset.card_le_card
    (appearingCoordinateAgreementFiber_subset_coordinateAgreementFiber dom k a u₀ u₁ S)

open Classical in
/-- Exact appearance fiber over a prescribed zero-agreement set.  Unlike
`appearingCoordinateAgreementFiber`, this requires the actual zero-direction agreement set to be
exactly `S`, so different `S` split a stratum rather than merely covering it. -/
noncomputable def exactAppearingZeroAgreementFiber
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (S : Finset (Fin n)) :
    Finset (Fin n → F) :=
  (lineAppearingCodewords dom k a u₀ u₁).filter
    (fun c => directionZeroAgreementSet c u₀ u₁ = S)

open Classical in
theorem mem_exactAppearingZeroAgreementFiber
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ c : Fin n → F) (S : Finset (Fin n)) :
    c ∈ exactAppearingZeroAgreementFiber dom k a u₀ u₁ S ↔
      c ∈ lineAppearingCodewords dom k a u₀ u₁ ∧
        directionZeroAgreementSet c u₀ u₁ = S := by
  rw [exactAppearingZeroAgreementFiber, Finset.mem_filter]

open Classical in
/-- Exact zero-agreement appearance fibers are contained in the coarser appearance-filtered
coordinate fiber over the same set. -/
theorem exactAppearingZeroAgreementFiber_subset_appearingCoordinateAgreementFiber
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (S : Finset (Fin n)) :
    exactAppearingZeroAgreementFiber dom k a u₀ u₁ S ⊆
      appearingCoordinateAgreementFiber dom k a u₀ u₁ S := by
  intro c hc
  rw [mem_appearingCoordinateAgreementFiber]
  rw [mem_exactAppearingZeroAgreementFiber] at hc
  refine ⟨?_, hc.1⟩
  rw [coordinateAgreementFiber, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  constructor
  · have hcApp := hc.1
    rw [lineAppearingCodewords, Finset.mem_filter] at hcApp
    exact hcApp.2.1
  · intro i hi
    have hiZero : i ∈ directionZeroAgreementSet c u₀ u₁ := by
      rw [hc.2]
      exact hi
    rw [directionZeroAgreementSet, Finset.mem_filter] at hiZero
    exact hiZero.2

open Classical in
/-- Cardinal version of exact-fiber domination by the coarser appearance coordinate fiber. -/
theorem exactAppearingZeroAgreementFiber_card_le_appearingCoordinateAgreementFiber_card
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (S : Finset (Fin n)) :
    (exactAppearingZeroAgreementFiber dom k a u₀ u₁ S).card ≤
      (appearingCoordinateAgreementFiber dom k a u₀ u₁ S).card :=
  Finset.card_le_card
    (exactAppearingZeroAgreementFiber_subset_appearingCoordinateAgreementFiber
      dom k a u₀ u₁ S)

open Classical in
/-- A coarse appearance-coordinate fiber over a zero-coordinate set `S` is covered by exact
zero-agreement fibers over all zero-coordinate supersets of `S`.  This is the reverse comparison
to `exactAppearingZeroAgreementFiber_subset_appearingCoordinateAgreementFiber`, but it pays for
all possible exact profiles extending `S`. -/
theorem appearingCoordinateAgreementFiber_subset_exactAppearingZeroAgreementFiber_superset_biUnion
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) {S : Finset (Fin n)}
    (hSzero : S ⊆ directionZeroSet u₁) :
    appearingCoordinateAgreementFiber dom k a u₀ u₁ S ⊆
      (((directionZeroSet u₁).powerset.filter (fun T => S ⊆ T)).biUnion
        (fun T => exactAppearingZeroAgreementFiber dom k a u₀ u₁ T)) := by
  intro c hc
  have hcApp := (mem_appearingCoordinateAgreementFiber dom k a u₀ u₁ c S).mp hc
  have hcoord := hcApp.1
  rw [coordinateAgreementFiber, Finset.mem_filter] at hcoord
  refine Finset.mem_biUnion.mpr
    ⟨directionZeroAgreementSet c u₀ u₁, ?_, ?_⟩
  · rw [Finset.mem_filter]
    constructor
    · rw [Finset.mem_powerset]
      intro i hi
      rw [directionZeroAgreementSet, Finset.mem_filter] at hi
      exact hi.1
    · intro i hiS
      rw [directionZeroAgreementSet, Finset.mem_filter]
      exact ⟨hSzero hiS, hcoord.2.2 i hiS⟩
  · rw [mem_exactAppearingZeroAgreementFiber]
    exact ⟨hcApp.2, rfl⟩

open Classical in
/-- Cardinal form of the exact-profile superset cover for a coarse appearance-coordinate fiber. -/
theorem appearingCoordinateAgreementFiber_card_le_sum_exactAppearingZeroAgreementFiber_supersets
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) {S : Finset (Fin n)}
    (hSzero : S ⊆ directionZeroSet u₁) :
    (appearingCoordinateAgreementFiber dom k a u₀ u₁ S).card ≤
      ∑ T ∈ (directionZeroSet u₁).powerset.filter (fun T => S ⊆ T),
        (exactAppearingZeroAgreementFiber dom k a u₀ u₁ T).card := by
  calc
    (appearingCoordinateAgreementFiber dom k a u₀ u₁ S).card
        ≤ (((directionZeroSet u₁).powerset.filter (fun T => S ⊆ T)).biUnion
            (fun T => exactAppearingZeroAgreementFiber dom k a u₀ u₁ T)).card :=
      Finset.card_le_card
        (appearingCoordinateAgreementFiber_subset_exactAppearingZeroAgreementFiber_superset_biUnion
          dom k a u₀ u₁ hSzero)
    _ ≤ ∑ T ∈ (directionZeroSet u₁).powerset.filter (fun T => S ⊆ T),
        (exactAppearingZeroAgreementFiber dom k a u₀ u₁ T).card :=
      Finset.card_biUnion_le

open Classical in
/-- In the zero-safe branch, the exact-profile superset cover only needs profiles of size `< a`.
Profiles with `a ≤ #T` cannot contain appearing codewords because every appearing codeword is a
Reed--Solomon codeword and zero-direction safety bounds its zero-agreement count. -/
theorem appearingCoordinateAgreementFiber_subset_safeExactSuperset_biUnion
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) {S : Finset (Fin n)}
    (hsafe : ZeroDirectionSafeLine dom k a u₀ u₁)
    (hSzero : S ⊆ directionZeroSet u₁) :
    appearingCoordinateAgreementFiber dom k a u₀ u₁ S ⊆
      (((directionZeroSet u₁).powerset.filter (fun T => S ⊆ T ∧ T.card < a)).biUnion
        (fun T => exactAppearingZeroAgreementFiber dom k a u₀ u₁ T)) := by
  intro c hc
  have hcApp := (mem_appearingCoordinateAgreementFiber dom k a u₀ u₁ c S).mp hc
  have hcoord := hcApp.1
  rw [coordinateAgreementFiber, Finset.mem_filter] at hcoord
  have hcCode : c ∈ (rsCode dom k : Submodule F (Fin n → F)) := by
    have hcLine := hcApp.2
    rw [lineAppearingCodewords, Finset.mem_filter] at hcLine
    exact hcLine.2.1
  refine Finset.mem_biUnion.mpr
    ⟨directionZeroAgreementSet c u₀ u₁, ?_, ?_⟩
  · rw [Finset.mem_filter]
    constructor
    · rw [Finset.mem_powerset]
      intro i hi
      rw [directionZeroAgreementSet, Finset.mem_filter] at hi
      exact hi.1
    · constructor
      · intro i hiS
        rw [directionZeroAgreementSet, Finset.mem_filter]
        exact ⟨hSzero hiS, hcoord.2.2 i hiS⟩
      · exact hsafe c hcCode
  · rw [mem_exactAppearingZeroAgreementFiber]
    exact ⟨hcApp.2, rfl⟩

open Classical in
/-- Cardinal form of the zero-safe exact-profile superset cover. -/
theorem appearingCoordinateAgreementFiber_card_le_sum_exactAppearingZeroAgreementFiber_safeSupersets
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) {S : Finset (Fin n)}
    (hsafe : ZeroDirectionSafeLine dom k a u₀ u₁)
    (hSzero : S ⊆ directionZeroSet u₁) :
    (appearingCoordinateAgreementFiber dom k a u₀ u₁ S).card ≤
      ∑ T ∈ (directionZeroSet u₁).powerset.filter (fun T => S ⊆ T ∧ T.card < a),
        (exactAppearingZeroAgreementFiber dom k a u₀ u₁ T).card := by
  calc
    (appearingCoordinateAgreementFiber dom k a u₀ u₁ S).card
        ≤ (((directionZeroSet u₁).powerset.filter (fun T => S ⊆ T ∧ T.card < a)).biUnion
            (fun T => exactAppearingZeroAgreementFiber dom k a u₀ u₁ T)).card :=
      Finset.card_le_card
        (appearingCoordinateAgreementFiber_subset_safeExactSuperset_biUnion
          dom k a u₀ u₁ hsafe hSzero)
    _ ≤ ∑ T ∈ (directionZeroSet u₁).powerset.filter (fun T => S ⊆ T ∧ T.card < a),
        (exactAppearingZeroAgreementFiber dom k a u₀ u₁ T).card :=
      Finset.card_biUnion_le

open Classical in
/-- Full exact-profile estimates bound a coarse appearance-coordinate fiber by the zero-safe
restricted sum over exact supersets. -/
theorem appearingCoordinateAgreementFiber_card_le_sum_exactAppearingBudget_safeSupersets
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) {S : Finset (Fin n)}
    (M : ℕ → ℕ)
    (hsafe : ZeroDirectionSafeLine dom k a u₀ u₁)
    (hSzero : S ⊆ directionZeroSet u₁)
    (hExact : ∀ t : ℕ, t < a → ∀ T ∈ (directionZeroSet u₁).powersetCard t,
      (exactAppearingZeroAgreementFiber dom k a u₀ u₁ T).card ≤ M t) :
    (appearingCoordinateAgreementFiber dom k a u₀ u₁ S).card ≤
      ∑ T ∈ (directionZeroSet u₁).powerset.filter (fun T => S ⊆ T ∧ T.card < a),
        M T.card := by
  calc
    (appearingCoordinateAgreementFiber dom k a u₀ u₁ S).card
        ≤ ∑ T ∈ (directionZeroSet u₁).powerset.filter (fun T => S ⊆ T ∧ T.card < a),
          (exactAppearingZeroAgreementFiber dom k a u₀ u₁ T).card :=
      appearingCoordinateAgreementFiber_card_le_sum_exactAppearingZeroAgreementFiber_safeSupersets
        dom k a u₀ u₁ hsafe hSzero
    _ ≤ ∑ T ∈ (directionZeroSet u₁).powerset.filter (fun T => S ⊆ T ∧ T.card < a),
        M T.card := by
      refine Finset.sum_le_sum ?_
      intro T hT
      rcases Finset.mem_filter.mp hT with ⟨hTpow, _hST, hTcard⟩
      exact hExact T.card hTcard T
        (Finset.mem_powersetCard.mpr ⟨Finset.mem_powerset.mp hTpow, rfl⟩)

open Classical in
/-- Fixed-cardinality supersets of `S` inside `Z` inject into subsets of `Z \ S`. -/
theorem powersetCard_superset_card_le_choose_sdiff
    {α : Type} [DecidableEq α] {Z S : Finset α} (r : ℕ) (hSZ : S ⊆ Z) :
    ((Z.powersetCard r).filter (fun T => S ⊆ T)).card ≤
      (Z.card - S.card).choose (r - S.card) := by
  have hle :
      ((Z.powersetCard r).filter (fun T => S ⊆ T)).card ≤
        ((Z \ S).powersetCard (r - S.card)).card := by
    refine Finset.card_le_card_of_injOn (fun T => T \ S) ?_ ?_
    · intro T hT
      obtain ⟨hTpow, hST⟩ := Finset.mem_filter.mp hT
      obtain ⟨hTZ, hTcard⟩ := Finset.mem_powersetCard.mp hTpow
      refine Finset.mem_powersetCard.mpr ⟨?_, ?_⟩
      · intro x hx
        rw [Finset.mem_sdiff] at hx ⊢
        exact ⟨hTZ hx.1, hx.2⟩
      · rw [Finset.card_sdiff_of_subset hST, hTcard]
    · intro A hA B hB hAB
      rw [Finset.mem_coe] at hA hB
      have hSA : S ⊆ A := (Finset.mem_filter.mp hA).2
      have hSB : S ⊆ B := (Finset.mem_filter.mp hB).2
      calc
        A = (A \ S) ∪ S := (Finset.sdiff_union_of_subset hSA).symm
        _ = (B \ S) ∪ S := congrArg (fun U : Finset α => U ∪ S) hAB
        _ = B := Finset.sdiff_union_of_subset hSB
  refine le_trans hle (le_of_eq ?_)
  rw [Finset.card_powersetCard, Finset.card_sdiff_of_subset hSZ]

open Classical in
/-- Cardinality-profile envelope for the zero-safe superset sum.  The exact supersets of a coarse
profile `S` with cardinality `r` cost at most `choose(#Z - #S, r - #S)`. -/
theorem sum_safeSupersets_le_sum_choose_sdiff
    {α : Type} [DecidableEq α] (Z S : Finset α) (a : ℕ) (M : ℕ → ℕ)
    (hSZ : S ⊆ Z) :
    (∑ T ∈ Z.powerset.filter (fun T => S ⊆ T ∧ T.card < a), M T.card) ≤
      ∑ r ∈ Finset.range a, (Z.card - S.card).choose (r - S.card) * M r := by
  set U : Finset (Finset α) := Z.powerset.filter (fun T => S ⊆ T ∧ T.card < a)
    with hU
  have hmaps : (U : Set (Finset α)).MapsTo (fun T => T.card) (Finset.range a) := by
    intro T hT
    rw [Finset.mem_coe, hU, Finset.mem_filter] at hT
    exact Finset.mem_range.mpr hT.2.2
  calc
    (∑ T ∈ Z.powerset.filter (fun T => S ⊆ T ∧ T.card < a), M T.card)
        = ∑ T ∈ U, M T.card := by rw [hU]
    _ = ∑ r ∈ Finset.range a, ∑ T ∈ U.filter (fun T => T.card = r), M T.card := by
      rw [Finset.sum_fiberwise_of_maps_to hmaps]
    _ = ∑ r ∈ Finset.range a, (U.filter (fun T => T.card = r)).card * M r := by
      refine Finset.sum_congr rfl ?_
      intro r _hr
      rw [Finset.sum_const_nat]
      intro T hT
      rw [Finset.mem_filter] at hT
      rw [hT.2]
    _ ≤ ∑ r ∈ Finset.range a, (Z.card - S.card).choose (r - S.card) * M r := by
      refine Finset.sum_le_sum ?_
      intro r _hr
      have hsub :
          U.filter (fun T => T.card = r) ⊆
            (Z.powersetCard r).filter (fun T => S ⊆ T) := by
        intro T hT
        rw [Finset.mem_filter] at hT ⊢
        rw [hU, Finset.mem_filter] at hT
        exact ⟨Finset.mem_powersetCard.mpr ⟨Finset.mem_powerset.mp hT.1.1, hT.2⟩,
          hT.1.2.1⟩
      exact Nat.mul_le_mul_right (M r)
        (le_trans (Finset.card_le_card hsub)
          (powersetCard_superset_card_le_choose_sdiff r hSZ))

/-- A per-line budget for appearance-filtered coordinate fibers. -/
def ZeroAppearingCoordinateFiberBudgeted
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (M : ℕ → ℕ) : Prop :=
  ∀ t : ℕ, t < a → ∀ S ∈ (directionZeroSet u₁).powersetCard t,
    (appearingCoordinateAgreementFiber dom k a u₀ u₁ S).card ≤ M t

/-- A per-line appearance-filtered coordinate-fiber budget restricted to low interpolation
profiles `t < k`.  High profiles can be discharged separately by RS uniqueness. -/
def ZeroLowAppearingCoordinateFiberBudgeted
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (M : ℕ → ℕ) : Prop :=
  ∀ t : ℕ, t < a → t < k → ∀ S ∈ (directionZeroSet u₁).powersetCard t,
    (appearingCoordinateAgreementFiber dom k a u₀ u₁ S).card ≤ M t

/-- A per-line budget for exact zero-agreement appearance fibers. -/
def ZeroExactAppearingZeroAgreementFiberBudgeted
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (M : ℕ → ℕ) : Prop :=
  ∀ t : ℕ, t < a → ∀ S ∈ (directionZeroSet u₁).powersetCard t,
    (exactAppearingZeroAgreementFiber dom k a u₀ u₁ S).card ≤ M t

/-- A per-line exact zero-agreement appearance-fiber budget restricted to low interpolation
profiles `t < k`. -/
def ZeroLowExactAppearingZeroAgreementFiberBudgeted
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (M : ℕ → ℕ) : Prop :=
  ∀ t : ℕ, t < a → t < k → ∀ S ∈ (directionZeroSet u₁).powersetCard t,
    (exactAppearingZeroAgreementFiber dom k a u₀ u₁ S).card ≤ M t

/-- Uniform appearance-filtered coordinate-fiber budget on the large-zero safe branch. -/
def UniformLargeZeroSafeAppearingCoordinateFiberBudgeted
    (dom : Fin n ↪ F) (k a : ℕ) (M : ℕ → ℕ) : Prop :=
  ∀ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
    ZeroDirectionSafeLine dom k a u₀ u₁ →
      ZeroAppearingCoordinateFiberBudgeted dom k a u₀ u₁ M

/-- Uniform low-profile appearance-filtered coordinate-fiber budget on the large-zero safe
branch. -/
def UniformLargeZeroSafeLowAppearingCoordinateFiberBudgeted
    (dom : Fin n ↪ F) (k a : ℕ) (M : ℕ → ℕ) : Prop :=
  ∀ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
    ZeroDirectionSafeLine dom k a u₀ u₁ →
      ZeroLowAppearingCoordinateFiberBudgeted dom k a u₀ u₁ M

/-- Uniform exact zero-agreement appearance-fiber budget on the large-zero safe branch. -/
def UniformLargeZeroSafeExactAppearingZeroAgreementFiberBudgeted
    (dom : Fin n ↪ F) (k a : ℕ) (M : ℕ → ℕ) : Prop :=
  ∀ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
    ZeroDirectionSafeLine dom k a u₀ u₁ →
      ZeroExactAppearingZeroAgreementFiberBudgeted dom k a u₀ u₁ M

/-- Uniform low-profile exact zero-agreement appearance-fiber budget on the large-zero safe
branch. -/
def UniformLargeZeroSafeLowExactAppearingZeroAgreementFiberBudgeted
    (dom : Fin n ↪ F) (k a : ℕ) (M : ℕ → ℕ) : Prop :=
  ∀ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
    ZeroDirectionSafeLine dom k a u₀ u₁ →
      ZeroLowExactAppearingZeroAgreementFiberBudgeted dom k a u₀ u₁ M

open Classical in
/-- Named-budget wrapper for the zero-safe exact-profile superset-sum bound. -/
theorem appearingCoordinateAgreementFiber_card_le_sum_zeroExactAppearingBudget_safeSupersets
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) {S : Finset (Fin n)}
    (M : ℕ → ℕ)
    (hsafe : ZeroDirectionSafeLine dom k a u₀ u₁)
    (hSzero : S ⊆ directionZeroSet u₁)
    (hExact : ZeroExactAppearingZeroAgreementFiberBudgeted dom k a u₀ u₁ M) :
    (appearingCoordinateAgreementFiber dom k a u₀ u₁ S).card ≤
      ∑ T ∈ (directionZeroSet u₁).powerset.filter (fun T => S ⊆ T ∧ T.card < a),
        M T.card :=
  appearingCoordinateAgreementFiber_card_le_sum_exactAppearingBudget_safeSupersets
    dom k a u₀ u₁ M hsafe hSzero hExact

open Classical in
/-- Binomial cardinality-profile envelope for a coarse appearance-coordinate fiber controlled by
an exact zero-agreement appearance budget on a zero-safe line. -/
theorem appearingCoordinateAgreementFiber_card_le_chooseProfile_exactBudget_safeSupersets
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) {S : Finset (Fin n)}
    (M : ℕ → ℕ)
    (hsafe : ZeroDirectionSafeLine dom k a u₀ u₁)
    (hSzero : S ⊆ directionZeroSet u₁)
    (hExact : ZeroExactAppearingZeroAgreementFiberBudgeted dom k a u₀ u₁ M) :
    (appearingCoordinateAgreementFiber dom k a u₀ u₁ S).card ≤
      ∑ r ∈ Finset.range a,
        ((directionZeroSet u₁).card - S.card).choose (r - S.card) * M r := by
  exact le_trans
    (appearingCoordinateAgreementFiber_card_le_sum_zeroExactAppearingBudget_safeSupersets
      dom k a u₀ u₁ M hsafe hSzero hExact)
    (sum_safeSupersets_le_sum_choose_sdiff (directionZeroSet u₁) S a M hSzero)

open Classical in
/-- A full exact-profile budget gives a coarse appearance-coordinate budget once the caller pays
the zero-safe superset sum for every coarse profile. -/
theorem zeroAppearingCoordinateFiberBudgeted_of_exactAppearingBudgeted_and_safeSupersetSums
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (Mexact Mcoarse : ℕ → ℕ)
    (hsafe : ZeroDirectionSafeLine dom k a u₀ u₁)
    (hExact : ZeroExactAppearingZeroAgreementFiberBudgeted dom k a u₀ u₁ Mexact)
    (hSupersets : ∀ t : ℕ, t < a → ∀ S ∈ (directionZeroSet u₁).powersetCard t,
      (∑ T ∈ (directionZeroSet u₁).powerset.filter (fun T => S ⊆ T ∧ T.card < a),
        Mexact T.card) ≤ Mcoarse t) :
    ZeroAppearingCoordinateFiberBudgeted dom k a u₀ u₁ Mcoarse := by
  intro t ht S hS
  exact le_trans
    (appearingCoordinateAgreementFiber_card_le_sum_zeroExactAppearingBudget_safeSupersets
      dom k a u₀ u₁ Mexact hsafe (Finset.mem_powersetCard.mp hS).1 hExact)
    (hSupersets t ht S hS)

open Classical in
/-- Uniform version of
`zeroAppearingCoordinateFiberBudgeted_of_exactAppearingBudgeted_and_safeSupersetSums`. -/
theorem
    uniformLargeZeroSafeAppearingCoordinateFiberBudgeted_of_exactBudgeted_safeSupersetSums
    (dom : Fin n ↪ F) (k a : ℕ) (Mexact Mcoarse : ℕ → ℕ)
    (hExact : UniformLargeZeroSafeExactAppearingZeroAgreementFiberBudgeted dom k a Mexact)
    (hSupersets :
      ∀ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
        ZeroDirectionSafeLine dom k a u₀ u₁ →
          ∀ t : ℕ, t < a → ∀ S ∈ (directionZeroSet u₁).powersetCard t,
            (∑ T ∈ (directionZeroSet u₁).powerset.filter
              (fun T => S ⊆ T ∧ T.card < a), Mexact T.card) ≤ Mcoarse t) :
    UniformLargeZeroSafeAppearingCoordinateFiberBudgeted dom k a Mcoarse := by
  intro u₀ u₁ hnotEligible hsafe
  exact zeroAppearingCoordinateFiberBudgeted_of_exactAppearingBudgeted_and_safeSupersetSums
    dom k a u₀ u₁ Mexact Mcoarse hsafe
    (hExact u₀ u₁ hnotEligible hsafe)
    (hSupersets u₀ u₁ hnotEligible hsafe)

open Classical in
/-- A full exact-profile budget gives a coarse appearance-coordinate budget once the caller pays
the binomial cardinality-profile envelope over safe exact supersets. -/
theorem zeroAppearingCoordinateFiberBudgeted_of_exactAppearingBudgeted_and_chooseProfileSums
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (Mexact Mcoarse : ℕ → ℕ)
    (hsafe : ZeroDirectionSafeLine dom k a u₀ u₁)
    (hExact : ZeroExactAppearingZeroAgreementFiberBudgeted dom k a u₀ u₁ Mexact)
    (hProfile : ∀ t : ℕ, t < a → ∀ S ∈ (directionZeroSet u₁).powersetCard t,
      (∑ r ∈ Finset.range a,
        ((directionZeroSet u₁).card - t).choose (r - t) * Mexact r) ≤ Mcoarse t) :
    ZeroAppearingCoordinateFiberBudgeted dom k a u₀ u₁ Mcoarse := by
  intro t ht S hS
  have hSzero : S ⊆ directionZeroSet u₁ := (Finset.mem_powersetCard.mp hS).1
  have hScard : S.card = t := (Finset.mem_powersetCard.mp hS).2
  exact le_trans
    (appearingCoordinateAgreementFiber_card_le_chooseProfile_exactBudget_safeSupersets
      dom k a u₀ u₁ Mexact hsafe hSzero hExact)
    (by simpa [hScard] using hProfile t ht S hS)

open Classical in
/-- Uniform version of
`zeroAppearingCoordinateFiberBudgeted_of_exactAppearingBudgeted_and_chooseProfileSums`. -/
theorem
    uniformLargeZeroSafeAppearingCoordinateFiberBudgeted_of_exactBudgeted_chooseProfileSums
    (dom : Fin n ↪ F) (k a : ℕ) (Mexact Mcoarse : ℕ → ℕ)
    (hExact : UniformLargeZeroSafeExactAppearingZeroAgreementFiberBudgeted dom k a Mexact)
    (hProfile :
      ∀ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
        ZeroDirectionSafeLine dom k a u₀ u₁ →
          ∀ t : ℕ, t < a → ∀ S ∈ (directionZeroSet u₁).powersetCard t,
            (∑ r ∈ Finset.range a,
              ((directionZeroSet u₁).card - t).choose (r - t) * Mexact r) ≤ Mcoarse t) :
    UniformLargeZeroSafeAppearingCoordinateFiberBudgeted dom k a Mcoarse := by
  intro u₀ u₁ hnotEligible hsafe
  exact zeroAppearingCoordinateFiberBudgeted_of_exactAppearingBudgeted_and_chooseProfileSums
    dom k a u₀ u₁ Mexact Mcoarse hsafe
    (hExact u₀ u₁ hnotEligible hsafe)
    (hProfile u₀ u₁ hnotEligible hsafe)

/-- A raw coordinate-fiber budget immediately gives an appearance-filtered fiber budget. -/
theorem zeroAppearingCoordinateFiberBudgeted_of_coordinateAgreementFiberBudgeted
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (M : ℕ → ℕ)
    (hFiber : ZeroCoordinateAgreementFiberBudgeted dom k a u₀ u₁ M) :
    ZeroAppearingCoordinateFiberBudgeted dom k a u₀ u₁ M := by
  intro t ht S hS
  exact le_trans
    (appearingCoordinateAgreementFiber_card_le_coordinateAgreementFiber_card
      dom k a u₀ u₁ S)
    (hFiber t ht S hS)

/-- Uniform version: the appearance-filtered route strictly generalizes the raw coordinate-fiber
route. -/
theorem uniformLargeZeroSafeAppearingCoordinateFiberBudgeted_of_coordinateAgreementFiberBudgeted
    (dom : Fin n ↪ F) (k a : ℕ) (M : ℕ → ℕ)
    (hFiber : UniformLargeZeroSafeCoordinateAgreementFiberBudgeted dom k a M) :
    UniformLargeZeroSafeAppearingCoordinateFiberBudgeted dom k a M := by
  intro u₀ u₁ hnotEligible hsafe
  exact zeroAppearingCoordinateFiberBudgeted_of_coordinateAgreementFiberBudgeted
    dom k a u₀ u₁ M (hFiber u₀ u₁ hnotEligible hsafe)

open Classical in
/-- An appearance-filtered coordinate-fiber budget immediately gives the sharper exact
zero-agreement appearance-fiber budget. -/
theorem zeroExactAppearingZeroAgreementFiberBudgeted_of_appearingCoordinateFiberBudgeted
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (M : ℕ → ℕ)
    (hFiber : ZeroAppearingCoordinateFiberBudgeted dom k a u₀ u₁ M) :
    ZeroExactAppearingZeroAgreementFiberBudgeted dom k a u₀ u₁ M := by
  intro t ht S hS
  exact le_trans
    (exactAppearingZeroAgreementFiber_card_le_appearingCoordinateAgreementFiber_card
      dom k a u₀ u₁ S)
    (hFiber t ht S hS)

open Classical in
/-- Uniform version: the exact zero-agreement route strictly generalizes the coarser
appearance-coordinate route. -/
theorem
    uniformLargeZeroSafeExactAppearingZeroAgreementFiberBudgeted_of_appearingCoordinateFiberBudgeted
    (dom : Fin n ↪ F) (k a : ℕ) (M : ℕ → ℕ)
    (hFiber : UniformLargeZeroSafeAppearingCoordinateFiberBudgeted dom k a M) :
    UniformLargeZeroSafeExactAppearingZeroAgreementFiberBudgeted dom k a M := by
  intro u₀ u₁ hnotEligible hsafe
  exact zeroExactAppearingZeroAgreementFiberBudgeted_of_appearingCoordinateFiberBudgeted
    dom k a u₀ u₁ M (hFiber u₀ u₁ hnotEligible hsafe)

open Classical in
/-- Low-profile appearance-filtered coordinate-fiber bounds imply the corresponding low-profile
exact zero-agreement appearance-fiber bounds. -/
theorem zeroLowExactAppearingZeroAgreementFiberBudgeted_of_lowAppearingCoordinateFiberBudgeted
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (M : ℕ → ℕ)
    (hFiber : ZeroLowAppearingCoordinateFiberBudgeted dom k a u₀ u₁ M) :
    ZeroLowExactAppearingZeroAgreementFiberBudgeted dom k a u₀ u₁ M := by
  intro t ht htk S hS
  exact le_trans
    (exactAppearingZeroAgreementFiber_card_le_appearingCoordinateAgreementFiber_card
      dom k a u₀ u₁ S)
    (hFiber t ht htk S hS)

open Classical in
/-- Uniform low-profile version: a low appearance-coordinate budget can be consumed directly as a
low exact zero-agreement appearance budget. -/
theorem
    uniformLargeZeroSafeLowExactAppearingZeroAgreementFiberBudgeted_of_lowAppearingBudgeted
    (dom : Fin n ↪ F) (k a : ℕ) (M : ℕ → ℕ)
    (hFiber : UniformLargeZeroSafeLowAppearingCoordinateFiberBudgeted dom k a M) :
    UniformLargeZeroSafeLowExactAppearingZeroAgreementFiberBudgeted dom k a M := by
  intro u₀ u₁ hnotEligible hsafe
  exact zeroLowExactAppearingZeroAgreementFiberBudgeted_of_lowAppearingCoordinateFiberBudgeted
    dom k a u₀ u₁ M (hFiber u₀ u₁ hnotEligible hsafe)

open Classical in
/-- Contrapositive of
`zeroLowExactAppearingZeroAgreementFiberBudgeted_of_lowAppearingCoordinateFiberBudgeted`: if the
low exact appearance budget fails, then the coarser low appearance-coordinate budget already
fails. -/
theorem not_zeroLowAppearingCoordinateFiberBudgeted_of_not_zeroLowExactAppearingBudgeted
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (M : ℕ → ℕ)
    (hnot : ¬ ZeroLowExactAppearingZeroAgreementFiberBudgeted dom k a u₀ u₁ M) :
    ¬ ZeroLowAppearingCoordinateFiberBudgeted dom k a u₀ u₁ M := by
  intro hFiber
  exact hnot
    (zeroLowExactAppearingZeroAgreementFiberBudgeted_of_lowAppearingCoordinateFiberBudgeted
      dom k a u₀ u₁ M hFiber)

open Classical in
/-- Uniform contrapositive: the exact low-profile route has no independent failure mode beyond
the coarser low appearance-coordinate route. -/
theorem not_uniformLowAppearingBudgeted_of_not_uniformLowExactAppearingBudgeted
    (dom : Fin n ↪ F) (k a : ℕ) (M : ℕ → ℕ)
    (hnot : ¬ UniformLargeZeroSafeLowExactAppearingZeroAgreementFiberBudgeted dom k a M) :
    ¬ UniformLargeZeroSafeLowAppearingCoordinateFiberBudgeted dom k a M := by
  intro hFiber
  exact hnot
    (uniformLargeZeroSafeLowExactAppearingZeroAgreementFiberBudgeted_of_lowAppearingBudgeted
      dom k a M hFiber)

open Classical in
/-- A zero-agreement stratum is covered by appearance-filtered coordinate fibers.  This is the
same cover as `zeroAgreementStratum_subset_coordinateAgreementFiber_biUnion`, but it keeps the
line-appearance condition instead of throwing it away. -/
theorem zeroAgreementStratum_subset_appearingCoordinateAgreementFiber_biUnion
    (dom : Fin n ↪ F) (k a : ℕ)
    (u₀ u₁ : Fin n → F) (t : ℕ) :
    zeroAgreementStratum dom k a u₀ u₁ t ⊆
      ((directionZeroSet u₁).powersetCard t).biUnion
        (fun S => appearingCoordinateAgreementFiber dom k a u₀ u₁ S) := by
  intro c hc
  rw [zeroAgreementStratum, Finset.mem_filter] at hc
  let S : Finset (Fin n) := directionZeroAgreementSet c u₀ u₁
  have hSsub : S ⊆ directionZeroSet u₁ := by
    intro i hi
    change i ∈ directionZeroAgreementSet c u₀ u₁ at hi
    rw [directionZeroAgreementSet, Finset.mem_filter] at hi
    exact hi.1
  have hScard : S.card = t := by
    simpa [S] using hc.2
  refine Finset.mem_biUnion.mpr ⟨S, ?_, ?_⟩
  · rw [Finset.mem_powersetCard]
    exact ⟨hSsub, hScard⟩
  · rw [mem_appearingCoordinateAgreementFiber]
    refine ⟨?_, hc.1⟩
    rw [coordinateAgreementFiber, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    constructor
    · have hcApp := hc.1
      rw [lineAppearingCodewords, Finset.mem_filter] at hcApp
      exact hcApp.2.1
    · intro i hi
      change i ∈ directionZeroAgreementSet c u₀ u₁ at hi
      rw [directionZeroAgreementSet, Finset.mem_filter] at hi
      exact hi.2

open Classical in
/-- Cardinal cover by appearance-filtered coordinate fibers. -/
theorem zeroAgreementStratum_card_le_sum_appearingCoordinateAgreementFibers
    (dom : Fin n ↪ F) (k a : ℕ)
    (u₀ u₁ : Fin n → F) (t : ℕ) :
    (zeroAgreementStratum dom k a u₀ u₁ t).card
      ≤ ∑ S ∈ (directionZeroSet u₁).powersetCard t,
        (appearingCoordinateAgreementFiber dom k a u₀ u₁ S).card := by
  calc
    (zeroAgreementStratum dom k a u₀ u₁ t).card
        ≤ (((directionZeroSet u₁).powersetCard t).biUnion
            (fun S => appearingCoordinateAgreementFiber dom k a u₀ u₁ S)).card :=
          Finset.card_le_card
            (zeroAgreementStratum_subset_appearingCoordinateAgreementFiber_biUnion
              dom k a u₀ u₁ t)
    _ ≤ ∑ S ∈ (directionZeroSet u₁).powersetCard t,
          (appearingCoordinateAgreementFiber dom k a u₀ u₁ S).card :=
        Finset.card_biUnion_le

open Classical in
/-- If every appearance-filtered coordinate fiber over a `t`-subset has size at most `M`, then the
whole `t`-stratum has size at most `choose(#zeroSet(u₁), t) * M`. -/
theorem zeroAgreementStratum_card_le_choose_mul_appearingCoordinateFiberBound
    (dom : Fin n ↪ F) (k a : ℕ)
    (u₀ u₁ : Fin n → F) (t M : ℕ)
    (hM : ∀ S ∈ (directionZeroSet u₁).powersetCard t,
      (appearingCoordinateAgreementFiber dom k a u₀ u₁ S).card ≤ M) :
    (zeroAgreementStratum dom k a u₀ u₁ t).card
      ≤ (directionZeroSet u₁).card.choose t * M := by
  calc
    (zeroAgreementStratum dom k a u₀ u₁ t).card
        ≤ ∑ S ∈ (directionZeroSet u₁).powersetCard t,
          (appearingCoordinateAgreementFiber dom k a u₀ u₁ S).card :=
          zeroAgreementStratum_card_le_sum_appearingCoordinateAgreementFibers dom k a u₀ u₁ t
    _ ≤ ∑ _S ∈ (directionZeroSet u₁).powersetCard t, M :=
        Finset.sum_le_sum hM
    _ = ((directionZeroSet u₁).powersetCard t).card * M := by
        rw [Finset.sum_const, smul_eq_mul]
    _ = (directionZeroSet u₁).card.choose t * M := by
        rw [Finset.card_powersetCard]

open Classical in
/-- Exact zero-agreement appearance fibers partition a `t`-stratum by the actual
zero-direction agreement set. -/
theorem zeroAgreementStratum_card_eq_sum_exactAppearingZeroAgreementFibers
    (dom : Fin n ↪ F) (k a : ℕ)
    (u₀ u₁ : Fin n → F) (t : ℕ) :
    (zeroAgreementStratum dom k a u₀ u₁ t).card
      = ∑ S ∈ (directionZeroSet u₁).powersetCard t,
        (exactAppearingZeroAgreementFiber dom k a u₀ u₁ S).card := by
  let strata : Finset (Fin n → F) := zeroAgreementStratum dom k a u₀ u₁ t
  let target : Finset (Finset (Fin n)) := (directionZeroSet u₁).powersetCard t
  have hmaps :
      ∀ c ∈ strata, directionZeroAgreementSet c u₀ u₁ ∈ target := by
    intro c hc
    change c ∈ zeroAgreementStratum dom k a u₀ u₁ t at hc
    rw [zeroAgreementStratum, Finset.mem_filter] at hc
    change directionZeroAgreementSet c u₀ u₁ ∈ (directionZeroSet u₁).powersetCard t
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.filter_subset _ _, hc.2⟩
  have hpart :
      strata.card =
        ∑ S ∈ target,
          (strata.filter fun c => directionZeroAgreementSet c u₀ u₁ = S).card :=
    Finset.card_eq_sum_card_fiberwise hmaps
  rw [show (zeroAgreementStratum dom k a u₀ u₁ t).card = strata.card from rfl, hpart]
  refine Finset.sum_congr rfl ?_
  intro S hS
  congr 1
  ext c
  constructor
  · intro hc
    rw [Finset.mem_filter] at hc
    have hcStratum : c ∈ zeroAgreementStratum dom k a u₀ u₁ t := by
      simpa [strata] using hc.1
    rw [zeroAgreementStratum, Finset.mem_filter] at hcStratum
    rw [exactAppearingZeroAgreementFiber, Finset.mem_filter]
    exact ⟨hcStratum.1, hc.2⟩
  · intro hc
    rw [Finset.mem_filter]
    rw [exactAppearingZeroAgreementFiber, Finset.mem_filter] at hc
    refine ⟨?_, hc.2⟩
    have hcStratum : c ∈ zeroAgreementStratum dom k a u₀ u₁ t := by
      rw [zeroAgreementStratum, Finset.mem_filter]
      refine ⟨hc.1, ?_⟩
      have hScard : S.card = t := (Finset.mem_powersetCard.mp hS).2
      rw [hc.2, hScard]
    simpa [strata] using hcStratum

open Classical in
/-- If every exact zero-agreement appearance fiber over a `t`-subset has size at most `M`, then
the whole `t`-stratum has size at most `choose(#zeroSet(u₁), t) * M`. -/
theorem zeroAgreementStratum_card_le_choose_mul_exactAppearingZeroAgreementFiberBound
    (dom : Fin n ↪ F) (k a : ℕ)
    (u₀ u₁ : Fin n → F) (t M : ℕ)
    (hM : ∀ S ∈ (directionZeroSet u₁).powersetCard t,
      (exactAppearingZeroAgreementFiber dom k a u₀ u₁ S).card ≤ M) :
    (zeroAgreementStratum dom k a u₀ u₁ t).card
      ≤ (directionZeroSet u₁).card.choose t * M := by
  calc
    (zeroAgreementStratum dom k a u₀ u₁ t).card
        = ∑ S ∈ (directionZeroSet u₁).powersetCard t,
          (exactAppearingZeroAgreementFiber dom k a u₀ u₁ S).card :=
          zeroAgreementStratum_card_eq_sum_exactAppearingZeroAgreementFibers dom k a u₀ u₁ t
    _ ≤ ∑ _S ∈ (directionZeroSet u₁).powersetCard t, M :=
        Finset.sum_le_sum hM
    _ = ((directionZeroSet u₁).powersetCard t).card * M := by
        rw [Finset.sum_const, smul_eq_mul]
    _ = (directionZeroSet u₁).card.choose t * M := by
        rw [Finset.card_powersetCard]

/-- Arithmetic fit for an appearance-filtered coordinate-fiber budget.  This deliberately has the
same weighted-binomial shape as `ZeroCoordinateAgreementFiberBudgetFits`, but the budget function
`M` is now allowed to come from the smaller appearance-filtered fibers. -/
def ZeroAppearingCoordinateFiberBudgetFits
    (a B : ℕ) (u₁ : Fin n → F) (M : ℕ → ℕ) : Prop :=
  ∑ t ∈ Finset.range a,
    ((directionZeroSet u₁).card.choose t * M t) *
      ((directionSupportSet u₁).card / (a - t)) ≤ B

/-- Uniform arithmetic fit for appearance-filtered coordinate-fiber budgets on large-zero
directions. -/
def UniformLargeZeroSafeAppearingCoordinateFiberBudgetFits
    (a B : ℕ) (M : ℕ → ℕ) : Prop :=
  ∀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
    ZeroAppearingCoordinateFiberBudgetFits (F := F) (n := n) a B u₁ M

omit [Fintype F] in
/-- Exact failure form for one line's appearance-filtered coordinate-fiber arithmetic fit. -/
theorem not_zeroAppearingCoordinateFiberBudgetFits_iff_sum_gt
    (a B : ℕ) (u₁ : Fin n → F) (M : ℕ → ℕ) :
    (¬ ZeroAppearingCoordinateFiberBudgetFits (F := F) (n := n) a B u₁ M) ↔
      B < ∑ t ∈ Finset.range a,
        ((directionZeroSet u₁).card.choose t * M t) *
          ((directionSupportSet u₁).card / (a - t)) := by
  rw [ZeroAppearingCoordinateFiberBudgetFits]
  exact not_le

omit [Fintype F] in
/-- Exact failure form for the uniform large-zero appearance-filtered arithmetic fit. -/
theorem not_uniformLargeZeroSafeAppearingCoordinateFiberBudgetFits_iff_exists_sum_gt
    (a B : ℕ) (M : ℕ → ℕ) :
    (¬ UniformLargeZeroSafeAppearingCoordinateFiberBudgetFits (F := F) (n := n) a B M) ↔
      ∃ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
        B < ∑ t ∈ Finset.range a,
          ((directionZeroSet u₁).card.choose t * M t) *
            ((directionSupportSet u₁).card / (a - t)) := by
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro u₁ hnotEligible
    exact le_of_not_gt
      (fun hgt => hnone ⟨u₁, hnotEligible, hgt⟩)
  · rintro ⟨u₁, hnotEligible, hgt⟩ hfits
    exact (not_lt_of_ge (hfits u₁ hnotEligible)) hgt

omit [Fintype F] in
/-- The appearance-filtered arithmetic fit contains every individual `t` summand. -/
theorem zeroAppearingCoordinateFiberBudgetFits_term_le
    (a B t : ℕ) (u₁ : Fin n → F) (M : ℕ → ℕ) (ht : t < a)
    (hFits : ZeroAppearingCoordinateFiberBudgetFits (F := F) (n := n) a B u₁ M) :
    ((directionZeroSet u₁).card.choose t * M t) *
        ((directionSupportSet u₁).card / (a - t)) ≤ B := by
  have hmem : t ∈ Finset.range a := Finset.mem_range.mpr ht
  have hterm :
      ((directionZeroSet u₁).card.choose t * M t) *
          ((directionSupportSet u₁).card / (a - t)) ≤
        ∑ t ∈ Finset.range a,
          ((directionZeroSet u₁).card.choose t * M t) *
            ((directionSupportSet u₁).card / (a - t)) := by
    exact Finset.single_le_sum
      (f := fun t =>
        ((directionZeroSet u₁).card.choose t * M t) *
          ((directionSupportSet u₁).card / (a - t)))
      (fun _ _ => Nat.zero_le _) hmem
  exact le_trans hterm hFits

omit [Fintype F] in
/-- One over-budget `t` summand refutes the uniform appearance-filtered arithmetic fit. -/
theorem not_uniformLargeZeroSafeAppearingCoordinateFiberBudgetFits_of_exists_term_gt
    (a B : ℕ) (M : ℕ → ℕ)
    (hgt : ∃ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
      ∃ t : ℕ, t < a ∧
        B < ((directionZeroSet u₁).card.choose t * M t) *
          ((directionSupportSet u₁).card / (a - t))) :
    ¬ UniformLargeZeroSafeAppearingCoordinateFiberBudgetFits (F := F) (n := n) a B M := by
  intro hFits
  rcases hgt with ⟨u₁, hnotEligible, t, ht, hgt⟩
  exact (not_lt_of_ge
    (zeroAppearingCoordinateFiberBudgetFits_term_le
      (F := F) (n := n) a B t u₁ M ht (hFits u₁ hnotEligible))) hgt

set_option linter.unusedFintypeInType false in
/-- The raw coordinate-fiber fit can be consumed as an appearance-filtered fit for the same
numeric envelope. -/
theorem zeroAppearingCoordinateFiberBudgetFits_of_coordinateAgreementFiberBudgetFits
    (a B : ℕ) (u₁ : Fin n → F) (M : ℕ → ℕ)
    (hFits : ZeroCoordinateAgreementFiberBudgetFits (F := F) (n := n) a B u₁ M) :
    ZeroAppearingCoordinateFiberBudgetFits (F := F) (n := n) a B u₁ M := by
  simpa [ZeroAppearingCoordinateFiberBudgetFits, ZeroCoordinateAgreementFiberBudgetFits] using hFits

set_option linter.unusedFintypeInType false in
/-- Uniform version of
`zeroAppearingCoordinateFiberBudgetFits_of_coordinateAgreementFiberBudgetFits`. -/
theorem uniformLargeZeroSafeAppearingCoordinateFiberBudgetFits_of_coordinateAgreementFiberBudgetFits
    (a B : ℕ) (M : ℕ → ℕ)
    (hFits :
      UniformLargeZeroSafeCoordinateAgreementFiberBudgetFits (F := F) (n := n) a B M) :
    UniformLargeZeroSafeAppearingCoordinateFiberBudgetFits (F := F) (n := n) a B M := by
  intro u₁ hnotEligible
  exact zeroAppearingCoordinateFiberBudgetFits_of_coordinateAgreementFiberBudgetFits
    (F := F) (n := n) a B u₁ M (hFits u₁ hnotEligible)

open Classical in
/-- Appearance-filtered coordinate-fiber bounds imply zero-agreement stratum bounds. -/
theorem zeroAgreementStrataCardBudgeted_of_appearingCoordinateFiberBudgeted
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F)
    (M N : ℕ → ℕ)
    (hFiber : ZeroAppearingCoordinateFiberBudgeted dom k a u₀ u₁ M)
    (hN : ∀ t : ℕ, t < a → (directionZeroSet u₁).card.choose t * M t ≤ N t) :
    ZeroAgreementStrataCardBudgeted dom k a u₀ u₁ N := by
  intro t ht
  exact le_trans
    (zeroAgreementStratum_card_le_choose_mul_appearingCoordinateFiberBound
      dom k a u₀ u₁ t (M t) (hFiber t ht))
    (hN t ht)

open Classical in
/-- Exact zero-agreement appearance-fiber bounds imply zero-agreement stratum bounds. -/
theorem zeroAgreementStrataCardBudgeted_of_exactAppearingZeroAgreementFiberBudgeted
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F)
    (M N : ℕ → ℕ)
    (hFiber : ZeroExactAppearingZeroAgreementFiberBudgeted dom k a u₀ u₁ M)
    (hN : ∀ t : ℕ, t < a → (directionZeroSet u₁).card.choose t * M t ≤ N t) :
    ZeroAgreementStrataCardBudgeted dom k a u₀ u₁ N := by
  intro t ht
  exact le_trans
    (zeroAgreementStratum_card_le_choose_mul_exactAppearingZeroAgreementFiberBound
      dom k a u₀ u₁ t (M t) (hFiber t ht))
    (hN t ht)

open Classical in
/-- An appearance-filtered coordinate-fiber budget plus its weighted arithmetic fit gives the
punctured line budget. -/
theorem puncturedZeroStratifiedLineBudgeted_of_appearingCoordinateFiberBudgeted
    (dom : Fin n ↪ F) (k a B : ℕ)
    (u₀ u₁ : Fin n → F) (M : ℕ → ℕ)
    (hsafe : ZeroDirectionSafeLine dom k a u₀ u₁)
    (hFiber : ZeroAppearingCoordinateFiberBudgeted dom k a u₀ u₁ M)
    (hFits : ZeroAppearingCoordinateFiberBudgetFits (F := F) (n := n) a B u₁ M) :
    PuncturedZeroStratifiedLineBudgeted dom k a u₀ u₁ B := by
  refine puncturedZeroStratifiedLineBudgeted_of_zeroAgreementStrataCardBudgeted
    dom k a B u₀ u₁ (fun t => (directionZeroSet u₁).card.choose t * M t)
    hsafe ?_ ?_
  · exact zeroAgreementStrataCardBudgeted_of_appearingCoordinateFiberBudgeted
      dom k a u₀ u₁ M (fun t => (directionZeroSet u₁).card.choose t * M t)
      hFiber (fun _t _ht => le_rfl)
  · simpa [ZeroAppearingCoordinateFiberBudgetFits, ZeroAgreementStrataBudgetFits] using hFits

open Classical in
/-- An exact zero-agreement appearance-fiber budget plus the same weighted arithmetic fit gives
the punctured line budget. -/
theorem puncturedZeroStratifiedLineBudgeted_of_exactAppearingZeroAgreementFiberBudgeted
    (dom : Fin n ↪ F) (k a B : ℕ)
    (u₀ u₁ : Fin n → F) (M : ℕ → ℕ)
    (hsafe : ZeroDirectionSafeLine dom k a u₀ u₁)
    (hFiber : ZeroExactAppearingZeroAgreementFiberBudgeted dom k a u₀ u₁ M)
    (hFits : ZeroAppearingCoordinateFiberBudgetFits (F := F) (n := n) a B u₁ M) :
    PuncturedZeroStratifiedLineBudgeted dom k a u₀ u₁ B := by
  refine puncturedZeroStratifiedLineBudgeted_of_zeroAgreementStrataCardBudgeted
    dom k a B u₀ u₁ (fun t => (directionZeroSet u₁).card.choose t * M t)
    hsafe ?_ ?_
  · exact zeroAgreementStrataCardBudgeted_of_exactAppearingZeroAgreementFiberBudgeted
      dom k a u₀ u₁ M (fun t => (directionZeroSet u₁).card.choose t * M t)
      hFiber (fun _t _ht => le_rfl)
  · simpa [ZeroAppearingCoordinateFiberBudgetFits, ZeroAgreementStrataBudgetFits] using hFits

open Classical in
/-- Uniform appearance-filtered coordinate-fiber bounds plus their arithmetic fit discharge the
punctured large-zero safe budget. -/
theorem uniformPuncturedZeroStratifiedLineBudgeted_of_uniformAppearingCoordinateFiberBudgeted
    (dom : Fin n ↪ F) (k a B : ℕ) (M : ℕ → ℕ)
    (hFiber : UniformLargeZeroSafeAppearingCoordinateFiberBudgeted dom k a M)
    (hFits :
      UniformLargeZeroSafeAppearingCoordinateFiberBudgetFits (F := F) (n := n) a B M) :
    UniformPuncturedZeroStratifiedLineBudgeted dom k a B := by
  intro u₀ u₁ hnotEligible hsafe
  exact puncturedZeroStratifiedLineBudgeted_of_appearingCoordinateFiberBudgeted
    dom k a B u₀ u₁ M hsafe
    (hFiber u₀ u₁ hnotEligible hsafe)
    (hFits u₁ hnotEligible)

/-- Uniform exact zero-agreement appearance-fiber bounds plus the arithmetic fit discharge the
punctured large-zero safe budget. -/
theorem
    uniformPuncturedZeroStratifiedLineBudgeted_of_uniformExactAppearingZeroAgreementFiberBudgeted
    (dom : Fin n ↪ F) (k a B : ℕ) (M : ℕ → ℕ)
    (hFiber : UniformLargeZeroSafeExactAppearingZeroAgreementFiberBudgeted dom k a M)
    (hFits :
      UniformLargeZeroSafeAppearingCoordinateFiberBudgetFits (F := F) (n := n) a B M) :
    UniformPuncturedZeroStratifiedLineBudgeted dom k a B := by
  intro u₀ u₁ hnotEligible hsafe
  exact puncturedZeroStratifiedLineBudgeted_of_exactAppearingZeroAgreementFiberBudgeted
    dom k a B u₀ u₁ M hsafe
    (hFiber u₀ u₁ hnotEligible hsafe)
    (hFits u₁ hnotEligible)

/-- Backwards-compatible consumer: a raw coordinate-fiber budget and raw arithmetic fit discharge
the appearance-filtered route, because raw fibers dominate appearance-filtered fibers. -/
theorem uniformPuncturedLineBudgeted_of_uniformCoordinateFiberBudgeted_viaAppearing
    (dom : Fin n ↪ F) (k a B : ℕ) (M : ℕ → ℕ)
    (hFiber : UniformLargeZeroSafeCoordinateAgreementFiberBudgeted dom k a M)
    (hFits :
      UniformLargeZeroSafeCoordinateAgreementFiberBudgetFits (F := F) (n := n) a B M) :
    UniformPuncturedZeroStratifiedLineBudgeted dom k a B :=
  uniformPuncturedZeroStratifiedLineBudgeted_of_uniformAppearingCoordinateFiberBudgeted
    dom k a B M
    (uniformLargeZeroSafeAppearingCoordinateFiberBudgeted_of_coordinateAgreementFiberBudgeted
      dom k a M hFiber)
    (uniformLargeZeroSafeAppearingCoordinateFiberBudgetFits_of_coordinateAgreementFiberBudgetFits
      (F := F) (n := n) a B M hFits)

/-- Production wrapper using appearance-filtered coordinate-fiber budgets for the large-zero safe
branch. This is the full line-list route with the raw interpolation fiber replaced by the smaller
set of codewords that actually appear somewhere on the affine line. -/
theorem uniformLineBadScalarsBudgeted_of_supportAdjustedBudgetFits_and_appearingCoordinateFibers
    (dom : Fin n ↪ F) (k a L B : ℕ) (M : ℕ → ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hFiber : UniformLargeZeroSafeAppearingCoordinateFiberBudgeted dom k a M)
    (hFiberFits :
      UniformLargeZeroSafeAppearingCoordinateFiberBudgetFits (F := F) (n := n) a B M) :
    UniformLineBadScalarsBudgeted dom k a B :=
  uniformLineBadScalarsBudgeted_of_supportAdjustedBudgetFits_and_puncturedZeroStratified
    dom k a L B hSupport hFits hZeroSafe
    (uniformPuncturedZeroStratifiedLineBudgeted_of_uniformAppearingCoordinateFiberBudgeted
      dom k a B M hFiber hFiberFits)

open Classical in
/-- If the support-eligible line-list route, support arithmetic, zero-direction safety, and
appearance-fiber arithmetic fit are fixed, then any failed uniform bad-scalar budget must exhibit
a large-zero safe appearance-filtered coordinate fiber whose size exceeds the proposed `M t`. -/
theorem exists_largeZero_safe_appearingCoordinateFiber_gt_of_not_uniformLineBadScalarsBudgeted
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
          M t < (appearingCoordinateAgreementFiber dom k a u₀ u₁ S).card := by
  by_contra hnone
  have hFiber : UniformLargeZeroSafeAppearingCoordinateFiberBudgeted dom k a M := by
    intro u₀ u₁ hnotEligible hsafe t ht S hS
    exact le_of_not_gt
      (fun hgt => hnone ⟨u₀, u₁, hnotEligible, hsafe, t, ht, S, hS, hgt⟩)
  exact hnot
    (uniformLineBadScalarsBudgeted_of_supportAdjustedBudgetFits_and_appearingCoordinateFibers
      dom k a L B M hSupport hFits hZeroSafe hFiber hFiberFits)

open Classical in
/-- Scanner-facing full failure split for the appearance-filtered production route. Without
assuming zero-direction safety in advance, a failed uniform bad-scalar budget must expose either a
saturating zero-direction codeword or an overfull appearance-filtered coordinate fiber in the
large-zero safe branch. -/
theorem unsafe_or_largeZero_safe_appearingCoordinateFiber_gt_of_not_uniformLineBadScalarsBudgeted
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
            M t < (appearingCoordinateAgreementFiber dom k a u₀ u₁ S).card) := by
  by_cases hZeroSafe : UniformZeroDirectionSafe dom k a
  · exact Or.inr
      (exists_largeZero_safe_appearingCoordinateFiber_gt_of_not_uniformLineBadScalarsBudgeted
        dom k a L B M hSupport hFits hZeroSafe hFiberFits hnot)
  · exact Or.inl
      ((not_uniformZeroDirectionSafe_iff_exists_line_codeword_zeroAgreement_ge
        dom k a).mp hZeroSafe)

open Classical in
/-- Exact failure form for one line's low-profile appearance-filtered coordinate-fiber budget. -/
theorem not_zeroLowAppearingCoordinateFiberBudgeted_iff_exists_low_fiber_gt
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (M : ℕ → ℕ) :
    (¬ ZeroLowAppearingCoordinateFiberBudgeted dom k a u₀ u₁ M) ↔
      ∃ t : ℕ, t < a ∧ t < k ∧ ∃ S ∈ (directionZeroSet u₁).powersetCard t,
        M t < (appearingCoordinateAgreementFiber dom k a u₀ u₁ S).card := by
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro t ht hlow S hS
    exact le_of_not_gt
      (fun hgt => hnone ⟨t, ht, hlow, S, hS, hgt⟩)
  · rintro ⟨t, ht, hlow, S, hS, hgt⟩ hbudget
    exact (not_lt_of_ge (hbudget t ht hlow S hS)) hgt

open Classical in
/-- Exact failure form for the uniform low-profile appearance-filtered coordinate-fiber budget. -/
theorem not_uniformLargeZeroSafeLowAppearingCoordinateFiberBudgeted_iff_exists_low_fiber_gt
    (dom : Fin n ↪ F) (k a : ℕ) (M : ℕ → ℕ) :
    (¬ UniformLargeZeroSafeLowAppearingCoordinateFiberBudgeted dom k a M) ↔
      ∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
        ZeroDirectionSafeLine dom k a u₀ u₁ ∧
          ∃ t : ℕ, t < a ∧ t < k ∧ ∃ S ∈ (directionZeroSet u₁).powersetCard t,
            M t < (appearingCoordinateAgreementFiber dom k a u₀ u₁ S).card := by
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro u₀ u₁ hnotEligible hsafe t ht hlow S hS
    exact le_of_not_gt
      (fun hgt => hnone ⟨u₀, u₁, hnotEligible, hsafe, t, ht, hlow, S, hS, hgt⟩)
  · rintro ⟨u₀, u₁, hnotEligible, hsafe, t, ht, hlow, S, hS, hgt⟩ hbudget
    exact (not_lt_of_ge (hbudget u₀ u₁ hnotEligible hsafe t ht hlow S hS)) hgt

open Classical in
/-- High appearance-filtered fibers are automatically singleton-bounded. Once the prescribed
zero-coordinate subset has size at least `k`, RS uniqueness bounds the raw fiber by one, and the
appearance-filtered fiber is a subset of it. -/
theorem appearingCoordinateAgreementFiber_card_le_one_of_k_le
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a : ℕ)
    (u₀ u₁ : Fin n → F) {S : Finset (Fin n)} (hS : k ≤ S.card) :
    (appearingCoordinateAgreementFiber dom k a u₀ u₁ S).card ≤ 1 :=
  le_trans
    (appearingCoordinateAgreementFiber_card_le_coordinateAgreementFiber_card dom k a u₀ u₁ S)
    (coordinateAgreementFiber_card_le_one_of_k_le dom hk u₀ hS)

open Classical in
/-- A low-profile appearance-filtered coordinate-fiber budget plus the high-profile singleton
ceiling gives the full per-line appearance-fiber budget. -/
theorem zeroAppearingCoordinateFiberBudgeted_of_low_and_high_one
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a : ℕ)
    (u₀ u₁ : Fin n → F) (M : ℕ → ℕ)
    (hLow : ZeroLowAppearingCoordinateFiberBudgeted dom k a u₀ u₁ M)
    (hHigh : ∀ t : ℕ, t < a → k ≤ t → 1 ≤ M t) :
    ZeroAppearingCoordinateFiberBudgeted dom k a u₀ u₁ M := by
  intro t ht S hS
  by_cases hlow : t < k
  · exact hLow t ht hlow S hS
  · have hkt : k ≤ t := le_of_not_gt hlow
    have hScard : S.card = t := (Finset.mem_powersetCard.mp hS).2
    have hfiber :
        (appearingCoordinateAgreementFiber dom k a u₀ u₁ S).card ≤ 1 :=
      appearingCoordinateAgreementFiber_card_le_one_of_k_le dom hk a u₀ u₁
        (by rw [hScard]; exact hkt)
    exact le_trans hfiber (hHigh t ht hkt)

open Classical in
/-- Uniform version of `zeroAppearingCoordinateFiberBudgeted_of_low_and_high_one`. -/
theorem uniformLargeZeroSafeAppearingCoordinateFiberBudgeted_of_low_and_high_one
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a : ℕ) (M : ℕ → ℕ)
    (hLow : UniformLargeZeroSafeLowAppearingCoordinateFiberBudgeted dom k a M)
    (hHigh : ∀ t : ℕ, t < a → k ≤ t → 1 ≤ M t) :
    UniformLargeZeroSafeAppearingCoordinateFiberBudgeted dom k a M := by
  intro u₀ u₁ hnotEligible hsafe
  exact zeroAppearingCoordinateFiberBudgeted_of_low_and_high_one
    dom hk a u₀ u₁ M (hLow u₀ u₁ hnotEligible hsafe) hHigh

open Classical in
/-- Production wrapper for the low/high split appearance-filtered coordinate-fiber route.  Low
profiles `t < k` are supplied by the caller; high profiles are discharged by RS uniqueness. -/
theorem uniformLineBadScalarsBudgeted_of_lowAppearingCoordinateFibers
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a L B : ℕ) (M : ℕ → ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hLow : UniformLargeZeroSafeLowAppearingCoordinateFiberBudgeted dom k a M)
    (hHigh : ∀ t : ℕ, t < a → k ≤ t → 1 ≤ M t)
    (hFiberFits :
      UniformLargeZeroSafeAppearingCoordinateFiberBudgetFits (F := F) (n := n) a B M) :
    UniformLineBadScalarsBudgeted dom k a B :=
  uniformLineBadScalarsBudgeted_of_supportAdjustedBudgetFits_and_appearingCoordinateFibers
    dom k a L B M hSupport hFits hZeroSafe
    (uniformLargeZeroSafeAppearingCoordinateFiberBudgeted_of_low_and_high_one
      dom hk a M hLow hHigh)
    hFiberFits

open Classical in
/-- If support-side production, zero-direction safety, arithmetic fit, and the high-profile
singleton ceiling are fixed, failed bad-scalar production exposes an overfull low-profile
appearance-coordinate fiber. -/
theorem exists_largeZero_safe_low_appearingCoordinateFiber_gt_of_not_uniformLineBadScalarsBudgeted
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a L B : ℕ) (M : ℕ → ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hFiberFits :
      UniformLargeZeroSafeAppearingCoordinateFiberBudgetFits (F := F) (n := n) a B M)
    (hHigh : ∀ t : ℕ, t < a → k ≤ t → 1 ≤ M t)
    (hnot : ¬ UniformLineBadScalarsBudgeted dom k a B) :
    ∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
      ZeroDirectionSafeLine dom k a u₀ u₁ ∧
        ∃ t : ℕ, t < a ∧ t < k ∧ ∃ S ∈ (directionZeroSet u₁).powersetCard t,
          M t < (appearingCoordinateAgreementFiber dom k a u₀ u₁ S).card := by
  by_contra hnone
  have hLow : UniformLargeZeroSafeLowAppearingCoordinateFiberBudgeted dom k a M := by
    intro u₀ u₁ hnotEligible hsafe t ht hlow S hS
    exact le_of_not_gt
      (fun hgt => hnone ⟨u₀, u₁, hnotEligible, hsafe, t, ht, hlow, S, hS, hgt⟩)
  exact hnot
    (uniformLineBadScalarsBudgeted_of_lowAppearingCoordinateFibers
      dom hk a L B M hSupport hFits hZeroSafe hLow hHigh hFiberFits)

open Classical in
/-- If `M` is at least one in every high range `k ≤ t < a`, then any overfull
appearance-filtered coordinate fiber must lie in the low interpolation range `t < k`. -/
theorem exists_low_appearingCoordinateFiber_gt_of_exists_fiber_gt_and_high_one
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a : ℕ)
    (u₀ u₁ : Fin n → F) (M : ℕ → ℕ)
    (hHigh : ∀ t : ℕ, t < a → k ≤ t → 1 ≤ M t)
    (hgt : ∃ t : ℕ, t < a ∧ ∃ S ∈ (directionZeroSet u₁).powersetCard t,
      M t < (appearingCoordinateAgreementFiber dom k a u₀ u₁ S).card) :
    ∃ t : ℕ, t < a ∧ t < k ∧ ∃ S ∈ (directionZeroSet u₁).powersetCard t,
      M t < (appearingCoordinateAgreementFiber dom k a u₀ u₁ S).card := by
  rcases hgt with ⟨t, ht, S, hS, hgt⟩
  by_cases hlow : t < k
  · exact ⟨t, ht, hlow, S, hS, hgt⟩
  · have hkt : k ≤ t := le_of_not_gt hlow
    have hScard : S.card = t := (Finset.mem_powersetCard.mp hS).2
    have hfiber :
        (appearingCoordinateAgreementFiber dom k a u₀ u₁ S).card ≤ 1 :=
      appearingCoordinateAgreementFiber_card_le_one_of_k_le dom hk a u₀ u₁
        (by rw [hScard]; exact hkt)
    have hle : (appearingCoordinateAgreementFiber dom k a u₀ u₁ S).card ≤ M t :=
      le_trans hfiber (hHigh t ht hkt)
    exact False.elim ((not_lt_of_ge hle) hgt)

open Classical in
/-- Scanner-facing full failure split with high appearance-filtered fibers discharged by RS
uniqueness. Once `M t ≥ 1` for every high `k ≤ t < a`, a failed uniform bad-scalar budget must
expose either zero-direction saturation or a large-zero safe **low** appearance fiber `t < k`. -/
theorem
    unsafe_or_largeZero_safe_low_appearingCoordinateFiber_gt_of_not_uniformLineBadScalarsBudgeted
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
            M t < (appearingCoordinateAgreementFiber dom k a u₀ u₁ S).card) := by
  rcases
      (unsafe_or_largeZero_safe_appearingCoordinateFiber_gt_of_not_uniformLineBadScalarsBudgeted
        dom k a L B M hSupport hFits hFiberFits hnot) with hUnsafe | hFiber
  · exact Or.inl hUnsafe
  · rcases hFiber with ⟨u₀, u₁, hnotEligible, hsafe, hgt⟩
    exact Or.inr ⟨u₀, u₁, hnotEligible, hsafe,
      exists_low_appearingCoordinateFiber_gt_of_exists_fiber_gt_and_high_one
        dom hk a u₀ u₁ M hHigh hgt⟩

open Classical in
/-- Production wrapper using exact zero-agreement appearance-fiber budgets for the large-zero safe
branch.  This is the exact-profile version of
`uniformLineBadScalarsBudgeted_of_supportAdjustedBudgetFits_and_appearingCoordinateFibers`: the
`t`-stratum is split exactly by its zero-agreement set before the arithmetic fit is applied. -/
theorem uniformLineBadScalarsBudgeted_of_supportAdjustedBudgetFits_and_exactAppearingFibers
    (dom : Fin n ↪ F) (k a L B : ℕ) (M : ℕ → ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hFiber : UniformLargeZeroSafeExactAppearingZeroAgreementFiberBudgeted dom k a M)
    (hFiberFits :
      UniformLargeZeroSafeAppearingCoordinateFiberBudgetFits (F := F) (n := n) a B M) :
    UniformLineBadScalarsBudgeted dom k a B :=
  uniformLineBadScalarsBudgeted_of_supportAdjustedBudgetFits_and_puncturedZeroStratified
    dom k a L B hSupport hFits hZeroSafe
    (uniformPuncturedZeroStratifiedLineBudgeted_of_uniformExactAppearingZeroAgreementFiberBudgeted
      dom k a B M hFiber hFiberFits)

open Classical in
/-- If the support-eligible line-list route, support arithmetic, zero-direction safety, and exact
appearance-fiber arithmetic fit are fixed, then any failed uniform bad-scalar budget must exhibit
a large-zero safe exact zero-agreement appearance fiber whose size exceeds the proposed `M t`. -/
theorem exists_largeZero_safe_exactAppearingFiber_gt_of_not_uniformLineBadScalarsBudgeted
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
          M t < (exactAppearingZeroAgreementFiber dom k a u₀ u₁ S).card := by
  by_contra hnone
  have hFiber : UniformLargeZeroSafeExactAppearingZeroAgreementFiberBudgeted dom k a M := by
    intro u₀ u₁ hnotEligible hsafe t ht S hS
    exact le_of_not_gt
      (fun hgt => hnone ⟨u₀, u₁, hnotEligible, hsafe, t, ht, S, hS, hgt⟩)
  exact hnot
    (uniformLineBadScalarsBudgeted_of_supportAdjustedBudgetFits_and_exactAppearingFibers
      dom k a L B M hSupport hFits hZeroSafe hFiber hFiberFits)

open Classical in
/-- Scanner-facing full failure split for the exact appearance-fiber route. Without assuming
zero-direction safety in advance, a failed uniform bad-scalar budget must expose either a
saturating zero-direction codeword or an overfull exact zero-agreement appearance fiber in the
large-zero safe branch. -/
theorem unsafe_or_largeZero_safe_exactAppearingFiber_gt_of_not_uniformLineBadScalarsBudgeted
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
            M t < (exactAppearingZeroAgreementFiber dom k a u₀ u₁ S).card) := by
  by_cases hZeroSafe : UniformZeroDirectionSafe dom k a
  · exact Or.inr
      (exists_largeZero_safe_exactAppearingFiber_gt_of_not_uniformLineBadScalarsBudgeted
        dom k a L B M hSupport hFits hZeroSafe hFiberFits hnot)
  · exact Or.inl
      ((not_uniformZeroDirectionSafe_iff_exists_line_codeword_zeroAgreement_ge
        dom k a).mp hZeroSafe)

open Classical in
/-- Exact failure form for one line's low-profile exact zero-agreement appearance-fiber budget. -/
theorem not_zeroLowExactAppearingZeroAgreementFiberBudgeted_iff_exists_low_fiber_gt
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (M : ℕ → ℕ) :
    (¬ ZeroLowExactAppearingZeroAgreementFiberBudgeted dom k a u₀ u₁ M) ↔
      ∃ t : ℕ, t < a ∧ t < k ∧ ∃ S ∈ (directionZeroSet u₁).powersetCard t,
        M t < (exactAppearingZeroAgreementFiber dom k a u₀ u₁ S).card := by
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro t ht hlow S hS
    exact le_of_not_gt
      (fun hgt => hnone ⟨t, ht, hlow, S, hS, hgt⟩)
  · rintro ⟨t, ht, hlow, S, hS, hgt⟩ hbudget
    exact (not_lt_of_ge (hbudget t ht hlow S hS)) hgt

open Classical in
/-- Exact failure form for the uniform low-profile exact zero-agreement appearance-fiber budget. -/
theorem
    not_uniformLargeZeroSafeLowExactAppearingZeroAgreementFiberBudgeted_iff_exists_low_fiber_gt
    (dom : Fin n ↪ F) (k a : ℕ) (M : ℕ → ℕ) :
    (¬ UniformLargeZeroSafeLowExactAppearingZeroAgreementFiberBudgeted dom k a M) ↔
      ∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
        ZeroDirectionSafeLine dom k a u₀ u₁ ∧
          ∃ t : ℕ, t < a ∧ t < k ∧ ∃ S ∈ (directionZeroSet u₁).powersetCard t,
            M t < (exactAppearingZeroAgreementFiber dom k a u₀ u₁ S).card := by
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro u₀ u₁ hnotEligible hsafe t ht hlow S hS
    exact le_of_not_gt
      (fun hgt => hnone ⟨u₀, u₁, hnotEligible, hsafe, t, ht, hlow, S, hS, hgt⟩)
  · rintro ⟨u₀, u₁, hnotEligible, hsafe, t, ht, hlow, S, hS, hgt⟩ hbudget
    exact (not_lt_of_ge (hbudget u₀ u₁ hnotEligible hsafe t ht hlow S hS)) hgt

open Classical in
/-- A low exact zero-agreement appearance-fiber overrun is also a low overrun for the coarser
appearance-coordinate fiber. -/
theorem exists_low_appearingCoordinateFiber_gt_of_exists_low_exactAppearingFiber_gt
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (M : ℕ → ℕ)
    (hExact :
      ∃ t : ℕ, t < a ∧ t < k ∧ ∃ S ∈ (directionZeroSet u₁).powersetCard t,
        M t < (exactAppearingZeroAgreementFiber dom k a u₀ u₁ S).card) :
      ∃ t : ℕ, t < a ∧ t < k ∧ ∃ S ∈ (directionZeroSet u₁).powersetCard t,
        M t < (appearingCoordinateAgreementFiber dom k a u₀ u₁ S).card := by
  rcases hExact with ⟨t, ht, hlow, S, hS, hgt⟩
  exact ⟨t, ht, hlow, S, hS,
    lt_of_lt_of_le hgt
      (exactAppearingZeroAgreementFiber_card_le_appearingCoordinateAgreementFiber_card
        dom k a u₀ u₁ S)⟩

open Classical in
/-- Uniform low-overrun conversion from exact zero-agreement appearance fibers to the coarser
appearance-coordinate fibers. -/
theorem
    exists_uniformLow_appearingCoordinateFiber_gt_of_exists_uniformLow_exactAppearingFiber_gt
    (dom : Fin n ↪ F) (k a : ℕ) (M : ℕ → ℕ)
    (hExact :
      ∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
        ZeroDirectionSafeLine dom k a u₀ u₁ ∧
          ∃ t : ℕ, t < a ∧ t < k ∧ ∃ S ∈ (directionZeroSet u₁).powersetCard t,
            M t < (exactAppearingZeroAgreementFiber dom k a u₀ u₁ S).card) :
      ∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
        ZeroDirectionSafeLine dom k a u₀ u₁ ∧
          ∃ t : ℕ, t < a ∧ t < k ∧ ∃ S ∈ (directionZeroSet u₁).powersetCard t,
            M t < (appearingCoordinateAgreementFiber dom k a u₀ u₁ S).card := by
  rcases hExact with ⟨u₀, u₁, hnotEligible, hsafe, hlow⟩
  exact ⟨u₀, u₁, hnotEligible, hsafe,
    exists_low_appearingCoordinateFiber_gt_of_exists_low_exactAppearingFiber_gt
      dom k a u₀ u₁ M hlow⟩

open Classical in
/-- Exact appearance fibers are singleton-bounded in high zero-profile levels.  This is the
appearance-filtered version of Reed--Solomon uniqueness: if the prescribed zero set has size at
least `k`, the raw coordinate-agreement fiber has at most one codeword. -/
theorem exactAppearingZeroAgreementFiber_card_le_one_of_k_le
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a : ℕ)
    (u₀ u₁ : Fin n → F) {S : Finset (Fin n)} (hS : k ≤ S.card) :
    (exactAppearingZeroAgreementFiber dom k a u₀ u₁ S).card ≤ 1 :=
  le_trans
    (exactAppearingZeroAgreementFiber_card_le_appearingCoordinateAgreementFiber_card
      dom k a u₀ u₁ S)
    (appearingCoordinateAgreementFiber_card_le_one_of_k_le dom hk a u₀ u₁ hS)

open Classical in
/-- A low-profile exact appearance-fiber budget plus the high-profile singleton ceiling gives the
full per-line exact appearance-fiber budget. -/
theorem zeroExactAppearingZeroAgreementFiberBudgeted_of_low_and_high_one
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a : ℕ)
    (u₀ u₁ : Fin n → F) (M : ℕ → ℕ)
    (hLow : ZeroLowExactAppearingZeroAgreementFiberBudgeted dom k a u₀ u₁ M)
    (hHigh : ∀ t : ℕ, t < a → k ≤ t → 1 ≤ M t) :
    ZeroExactAppearingZeroAgreementFiberBudgeted dom k a u₀ u₁ M := by
  intro t ht S hS
  by_cases hlow : t < k
  · exact hLow t ht hlow S hS
  · have hkt : k ≤ t := le_of_not_gt hlow
    have hScard : S.card = t := (Finset.mem_powersetCard.mp hS).2
    have hfiber :
        (exactAppearingZeroAgreementFiber dom k a u₀ u₁ S).card ≤ 1 :=
      exactAppearingZeroAgreementFiber_card_le_one_of_k_le dom hk a u₀ u₁
        (by rw [hScard]; exact hkt)
    exact le_trans hfiber (hHigh t ht hkt)

open Classical in
/-- Uniform version of `zeroExactAppearingZeroAgreementFiberBudgeted_of_low_and_high_one`. -/
theorem uniformLargeZeroSafeExactAppearingZeroAgreementFiberBudgeted_of_low_and_high_one
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a : ℕ) (M : ℕ → ℕ)
    (hLow : UniformLargeZeroSafeLowExactAppearingZeroAgreementFiberBudgeted dom k a M)
    (hHigh : ∀ t : ℕ, t < a → k ≤ t → 1 ≤ M t) :
    UniformLargeZeroSafeExactAppearingZeroAgreementFiberBudgeted dom k a M := by
  intro u₀ u₁ hnotEligible hsafe
  exact zeroExactAppearingZeroAgreementFiberBudgeted_of_low_and_high_one
    dom hk a u₀ u₁ M (hLow u₀ u₁ hnotEligible hsafe) hHigh

open Classical in
/-- Production wrapper for the low/high split exact appearance-fiber route.  Low profiles `t < k`
are supplied by the caller; high profiles are discharged by RS uniqueness. -/
theorem uniformLineBadScalarsBudgeted_of_lowExactAppearingFibers
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a L B : ℕ) (M : ℕ → ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hLow : UniformLargeZeroSafeLowExactAppearingZeroAgreementFiberBudgeted dom k a M)
    (hHigh : ∀ t : ℕ, t < a → k ≤ t → 1 ≤ M t)
    (hFiberFits :
      UniformLargeZeroSafeAppearingCoordinateFiberBudgetFits (F := F) (n := n) a B M) :
    UniformLineBadScalarsBudgeted dom k a B :=
  uniformLineBadScalarsBudgeted_of_supportAdjustedBudgetFits_and_exactAppearingFibers
    dom k a L B M hSupport hFits hZeroSafe
    (uniformLargeZeroSafeExactAppearingZeroAgreementFiberBudgeted_of_low_and_high_one
      dom hk a M hLow hHigh)
    hFiberFits

open Classical in
/-- If support-side production, zero-direction safety, arithmetic fit, and the high-profile
singleton ceiling are fixed, failed bad-scalar production exposes an overfull low-profile exact
appearance fiber. -/
theorem exists_largeZero_safe_low_exactAppearingFiber_gt_of_not_uniformLineBadScalarsBudgeted
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a L B : ℕ) (M : ℕ → ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hFiberFits :
      UniformLargeZeroSafeAppearingCoordinateFiberBudgetFits (F := F) (n := n) a B M)
    (hHigh : ∀ t : ℕ, t < a → k ≤ t → 1 ≤ M t)
    (hnot : ¬ UniformLineBadScalarsBudgeted dom k a B) :
    ∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
      ZeroDirectionSafeLine dom k a u₀ u₁ ∧
        ∃ t : ℕ, t < a ∧ t < k ∧ ∃ S ∈ (directionZeroSet u₁).powersetCard t,
          M t < (exactAppearingZeroAgreementFiber dom k a u₀ u₁ S).card := by
  by_contra hnone
  have hLow :
      UniformLargeZeroSafeLowExactAppearingZeroAgreementFiberBudgeted dom k a M := by
    intro u₀ u₁ hnotEligible hsafe t ht hlow S hS
    exact le_of_not_gt
      (fun hgt => hnone ⟨u₀, u₁, hnotEligible, hsafe, t, ht, hlow, S, hS, hgt⟩)
  exact hnot
    (uniformLineBadScalarsBudgeted_of_lowExactAppearingFibers
      dom hk a L B M hSupport hFits hZeroSafe hLow hHigh hFiberFits)

open Classical in
/-- If `M` is at least one in every high range `k ≤ t < a`, then any overfull exact
zero-agreement appearance fiber must lie in the low interpolation range `t < k`. -/
theorem exists_low_exactAppearingFiber_gt_of_exists_fiber_gt_and_high_one
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a : ℕ)
    (u₀ u₁ : Fin n → F) (M : ℕ → ℕ)
    (hHigh : ∀ t : ℕ, t < a → k ≤ t → 1 ≤ M t)
    (hgt : ∃ t : ℕ, t < a ∧ ∃ S ∈ (directionZeroSet u₁).powersetCard t,
      M t < (exactAppearingZeroAgreementFiber dom k a u₀ u₁ S).card) :
    ∃ t : ℕ, t < a ∧ t < k ∧ ∃ S ∈ (directionZeroSet u₁).powersetCard t,
      M t < (exactAppearingZeroAgreementFiber dom k a u₀ u₁ S).card := by
  rcases hgt with ⟨t, ht, S, hS, hgt⟩
  by_cases hlow : t < k
  · exact ⟨t, ht, hlow, S, hS, hgt⟩
  · have hkt : k ≤ t := le_of_not_gt hlow
    have hScard : S.card = t := (Finset.mem_powersetCard.mp hS).2
    have hfiber :
        (exactAppearingZeroAgreementFiber dom k a u₀ u₁ S).card ≤ 1 :=
      exactAppearingZeroAgreementFiber_card_le_one_of_k_le dom hk a u₀ u₁
        (by rw [hScard]; exact hkt)
    have hle : (exactAppearingZeroAgreementFiber dom k a u₀ u₁ S).card ≤ M t :=
      le_trans hfiber (hHigh t ht hkt)
    exact False.elim ((not_lt_of_ge hle) hgt)

open Classical in
/-- Scanner-facing full failure split with high exact appearance fibers discharged by RS
uniqueness. Once `M t ≥ 1` for every high `k ≤ t < a`, a failed uniform bad-scalar budget must
expose either zero-direction saturation or a large-zero safe **low** exact appearance fiber
`t < k`. -/
theorem unsafe_or_largeZero_safe_low_exactAppearingFiber_gt_of_not_uniformLineBadScalarsBudgeted
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
            M t < (exactAppearingZeroAgreementFiber dom k a u₀ u₁ S).card) := by
  rcases
      (unsafe_or_largeZero_safe_exactAppearingFiber_gt_of_not_uniformLineBadScalarsBudgeted
        dom k a L B M hSupport hFits hFiberFits hnot) with hUnsafe | hFiber
  · exact Or.inl hUnsafe
  · rcases hFiber with ⟨u₀, u₁, hnotEligible, hsafe, hgt⟩
    exact Or.inr ⟨u₀, u₁, hnotEligible, hsafe,
      exists_low_exactAppearingFiber_gt_of_exists_fiber_gt_and_high_one
        dom hk a u₀ u₁ M hHigh hgt⟩

section SourceAudit

#print axioms appearingCoordinateAgreementFiber
#print axioms appearingCoordinateAgreementFiber_card_le_coordinateAgreementFiber_card
#print axioms exactAppearingZeroAgreementFiber
#print axioms exactAppearingZeroAgreementFiber_card_le_appearingCoordinateAgreementFiber_card
#print axioms
  appearingCoordinateAgreementFiber_subset_exactAppearingZeroAgreementFiber_superset_biUnion
#print axioms
  appearingCoordinateAgreementFiber_card_le_sum_exactAppearingZeroAgreementFiber_supersets
#print axioms
  appearingCoordinateAgreementFiber_subset_safeExactSuperset_biUnion
#print axioms
  appearingCoordinateAgreementFiber_card_le_sum_exactAppearingZeroAgreementFiber_safeSupersets
#print axioms
  appearingCoordinateAgreementFiber_card_le_sum_exactAppearingBudget_safeSupersets
#print axioms powersetCard_superset_card_le_choose_sdiff
#print axioms sum_safeSupersets_le_sum_choose_sdiff
#print axioms ZeroLowAppearingCoordinateFiberBudgeted
#print axioms ZeroLowExactAppearingZeroAgreementFiberBudgeted
#print axioms UniformLargeZeroSafeLowAppearingCoordinateFiberBudgeted
#print axioms UniformLargeZeroSafeLowExactAppearingZeroAgreementFiberBudgeted
#print axioms
  appearingCoordinateAgreementFiber_card_le_sum_zeroExactAppearingBudget_safeSupersets
#print axioms
  appearingCoordinateAgreementFiber_card_le_chooseProfile_exactBudget_safeSupersets
#print axioms
  zeroAppearingCoordinateFiberBudgeted_of_exactAppearingBudgeted_and_safeSupersetSums
#print axioms
  uniformLargeZeroSafeAppearingCoordinateFiberBudgeted_of_exactBudgeted_safeSupersetSums
#print axioms
  zeroAppearingCoordinateFiberBudgeted_of_exactAppearingBudgeted_and_chooseProfileSums
#print axioms
  uniformLargeZeroSafeAppearingCoordinateFiberBudgeted_of_exactBudgeted_chooseProfileSums
#print axioms zeroAppearingCoordinateFiberBudgeted_of_coordinateAgreementFiberBudgeted
#print axioms
  uniformLargeZeroSafeAppearingCoordinateFiberBudgeted_of_coordinateAgreementFiberBudgeted
#print axioms
  zeroExactAppearingZeroAgreementFiberBudgeted_of_appearingCoordinateFiberBudgeted
#print axioms
  uniformLargeZeroSafeExactAppearingZeroAgreementFiberBudgeted_of_appearingCoordinateFiberBudgeted
#print axioms
  zeroLowExactAppearingZeroAgreementFiberBudgeted_of_lowAppearingCoordinateFiberBudgeted
#print axioms
  uniformLargeZeroSafeLowExactAppearingZeroAgreementFiberBudgeted_of_lowAppearingBudgeted
#print axioms
  not_zeroLowAppearingCoordinateFiberBudgeted_of_not_zeroLowExactAppearingBudgeted
#print axioms not_uniformLowAppearingBudgeted_of_not_uniformLowExactAppearingBudgeted
#print axioms zeroAgreementStratum_subset_appearingCoordinateAgreementFiber_biUnion
#print axioms zeroAgreementStratum_card_le_sum_appearingCoordinateAgreementFibers
#print axioms zeroAgreementStratum_card_le_choose_mul_appearingCoordinateFiberBound
#print axioms zeroAgreementStratum_card_eq_sum_exactAppearingZeroAgreementFibers
#print axioms zeroAgreementStratum_card_le_choose_mul_exactAppearingZeroAgreementFiberBound
#print axioms not_zeroAppearingCoordinateFiberBudgetFits_iff_sum_gt
#print axioms not_uniformLargeZeroSafeAppearingCoordinateFiberBudgetFits_iff_exists_sum_gt
#print axioms zeroAppearingCoordinateFiberBudgetFits_term_le
#print axioms not_uniformLargeZeroSafeAppearingCoordinateFiberBudgetFits_of_exists_term_gt
#print axioms zeroAppearingCoordinateFiberBudgetFits_of_coordinateAgreementFiberBudgetFits
#print axioms
  uniformLargeZeroSafeAppearingCoordinateFiberBudgetFits_of_coordinateAgreementFiberBudgetFits
#print axioms zeroAgreementStrataCardBudgeted_of_appearingCoordinateFiberBudgeted
#print axioms zeroAgreementStrataCardBudgeted_of_exactAppearingZeroAgreementFiberBudgeted
#print axioms puncturedZeroStratifiedLineBudgeted_of_appearingCoordinateFiberBudgeted
#print axioms puncturedZeroStratifiedLineBudgeted_of_exactAppearingZeroAgreementFiberBudgeted
#print axioms uniformPuncturedZeroStratifiedLineBudgeted_of_uniformAppearingCoordinateFiberBudgeted
#print axioms
  uniformPuncturedZeroStratifiedLineBudgeted_of_uniformExactAppearingZeroAgreementFiberBudgeted
#print axioms uniformPuncturedLineBudgeted_of_uniformCoordinateFiberBudgeted_viaAppearing
#print axioms
  uniformLineBadScalarsBudgeted_of_supportAdjustedBudgetFits_and_appearingCoordinateFibers
#print axioms
  exists_largeZero_safe_appearingCoordinateFiber_gt_of_not_uniformLineBadScalarsBudgeted
#print axioms
  unsafe_or_largeZero_safe_appearingCoordinateFiber_gt_of_not_uniformLineBadScalarsBudgeted
#print axioms not_zeroLowAppearingCoordinateFiberBudgeted_iff_exists_low_fiber_gt
#print axioms
  not_uniformLargeZeroSafeLowAppearingCoordinateFiberBudgeted_iff_exists_low_fiber_gt
#print axioms appearingCoordinateAgreementFiber_card_le_one_of_k_le
#print axioms zeroAppearingCoordinateFiberBudgeted_of_low_and_high_one
#print axioms uniformLargeZeroSafeAppearingCoordinateFiberBudgeted_of_low_and_high_one
#print axioms uniformLineBadScalarsBudgeted_of_lowAppearingCoordinateFibers
#print axioms
  exists_largeZero_safe_low_appearingCoordinateFiber_gt_of_not_uniformLineBadScalarsBudgeted
#print axioms exists_low_appearingCoordinateFiber_gt_of_exists_fiber_gt_and_high_one
#print axioms
  unsafe_or_largeZero_safe_low_appearingCoordinateFiber_gt_of_not_uniformLineBadScalarsBudgeted
#print axioms
  uniformLineBadScalarsBudgeted_of_supportAdjustedBudgetFits_and_exactAppearingFibers
#print axioms
  exists_largeZero_safe_exactAppearingFiber_gt_of_not_uniformLineBadScalarsBudgeted
#print axioms
  unsafe_or_largeZero_safe_exactAppearingFiber_gt_of_not_uniformLineBadScalarsBudgeted
#print axioms not_zeroLowExactAppearingZeroAgreementFiberBudgeted_iff_exists_low_fiber_gt
#print axioms
  not_uniformLargeZeroSafeLowExactAppearingZeroAgreementFiberBudgeted_iff_exists_low_fiber_gt
#print axioms exists_low_appearingCoordinateFiber_gt_of_exists_low_exactAppearingFiber_gt
#print axioms
  exists_uniformLow_appearingCoordinateFiber_gt_of_exists_uniformLow_exactAppearingFiber_gt
#print axioms exactAppearingZeroAgreementFiber_card_le_one_of_k_le
#print axioms zeroExactAppearingZeroAgreementFiberBudgeted_of_low_and_high_one
#print axioms uniformLargeZeroSafeExactAppearingZeroAgreementFiberBudgeted_of_low_and_high_one
#print axioms uniformLineBadScalarsBudgeted_of_lowExactAppearingFibers
#print axioms
  exists_largeZero_safe_low_exactAppearingFiber_gt_of_not_uniformLineBadScalarsBudgeted
#print axioms exists_low_exactAppearingFiber_gt_of_exists_fiber_gt_and_high_one
#print axioms
  unsafe_or_largeZero_safe_low_exactAppearingFiber_gt_of_not_uniformLineBadScalarsBudgeted

end SourceAudit

end ProximityGap.Ownership
