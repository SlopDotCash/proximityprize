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
/-- Conversely, the explicit support-ratio line-fiber cover contains only support-ratio-heavy
coordinate-fiber codewords when the base profile `S` lies in the zero-direction set. -/
theorem supportRatioLineFiberCover_subset_supportRatioHeavyCoordinateFiber
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) {S : Finset (Fin n)}
    (hSzero : S ⊆ directionZeroSet u₁) :
    supportRatioLineFiberCover dom k a u₀ u₁ S ⊆
      supportRatioHeavyCoordinateFiber dom k a u₀ u₁ S := by
  intro c hc
  rw [supportRatioLineFiberCover] at hc
  rcases Finset.mem_biUnion.mp hc with ⟨γ, _hγ, hcγ⟩
  rcases Finset.mem_biUnion.mp hcγ with ⟨T, hTmem, hcLine⟩
  rw [mem_supportRatioHeavyCoordinateFiber]
  rw [coordinateAgreementFiber, Finset.mem_filter] at hcLine ⊢
  rcases hcLine with ⟨_hmem, hcCode, hagreeLine⟩
  have hTsub : T ⊆ directionSupportSet u₁ := (Finset.mem_powersetCard.mp hTmem).1
  have hTcard : T.card = a - S.card := (Finset.mem_powersetCard.mp hTmem).2
  refine ⟨?_, γ, ?_⟩
  · refine ⟨Finset.mem_univ _, hcCode, ?_⟩
    intro i hiS
    have hzero : u₁ i = 0 := by
      simpa [directionZeroSet] using hSzero hiS
    have hline : c i = u₀ i + γ • u₁ i :=
      hagreeLine i (Finset.mem_union.mpr (Or.inl hiS))
    calc
      c i = u₀ i + γ • u₁ i := hline
      _ = u₀ i := by
        rw [hzero]
        simp
  · rw [← hTcard]
    refine Finset.card_le_card ?_
    intro i hiT
    rw [mem_supportRatioFiber]
    refine ⟨hTsub hiT, ?_⟩
    have hline : c i = u₀ i + γ • u₁ i :=
      hagreeLine i (Finset.mem_union.mpr (Or.inr hiT))
    have hnonzero : u₁ i ≠ 0 := by
      simpa [directionSupportSet] using hTsub hiT
    rw [hline, smul_eq_mul]
    field_simp [hnonzero]
    ring

open Classical in
/-- On zero-direction profiles, the explicit line-fiber cover is exactly the
support-ratio-heavy coordinate fiber. -/
theorem supportRatioLineFiberCover_eq_supportRatioHeavyCoordinateFiber
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) {S : Finset (Fin n)}
    (hSzero : S ⊆ directionZeroSet u₁) :
    supportRatioLineFiberCover dom k a u₀ u₁ S =
      supportRatioHeavyCoordinateFiber dom k a u₀ u₁ S := by
  ext c
  constructor
  · exact fun hc => supportRatioLineFiberCover_subset_supportRatioHeavyCoordinateFiber
      dom k a u₀ u₁ hSzero hc
  · exact fun hc => supportRatioHeavyCoordinateFiber_subset_supportRatioLineFiberCover
      dom k a u₀ u₁ hSzero hc

open Classical in
/-- Cardinal equality form of `supportRatioLineFiberCover_eq_supportRatioHeavyCoordinateFiber`. -/
theorem supportRatioLineFiberCover_card_eq_supportRatioHeavyCoordinateFiber_card
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) {S : Finset (Fin n)}
    (hSzero : S ⊆ directionZeroSet u₁) :
    (supportRatioLineFiberCover dom k a u₀ u₁ S).card =
      (supportRatioHeavyCoordinateFiber dom k a u₀ u₁ S).card := by
  rw [supportRatioLineFiberCover_eq_supportRatioHeavyCoordinateFiber
    dom k a u₀ u₁ hSzero]

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
/-- If the agreement threshold is at least the RS dimension, every coordinate fiber in the
explicit support-ratio cover sum is singleton-bounded by RS uniqueness. -/
theorem supportRatioCoverSum_le_field_card_mul_choose
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) {a : ℕ} (hka : k ≤ a)
    (u₀ u₁ : Fin n → F) {S : Finset (Fin n)}
    (hSzero : S ⊆ directionZeroSet u₁) :
    (∑ γ : F, ∑ T ∈ (directionSupportSet u₁).powersetCard (a - S.card),
      (coordinateAgreementFiber dom k (fun i => u₀ i + γ • u₁ i) (S ∪ T)).card) ≤
      Fintype.card F * (directionSupportSet u₁).card.choose (a - S.card) := by
  calc
    (∑ γ : F, ∑ T ∈ (directionSupportSet u₁).powersetCard (a - S.card),
        (coordinateAgreementFiber dom k (fun i => u₀ i + γ • u₁ i) (S ∪ T)).card)
        ≤ ∑ _γ : F, ∑ _T ∈ (directionSupportSet u₁).powersetCard (a - S.card), 1 := by
        refine Finset.sum_le_sum fun γ _ => ?_
        refine Finset.sum_le_sum fun T hT => ?_
        obtain ⟨hTsub, hTcard⟩ := Finset.mem_powersetCard.mp hT
        have hdisj : Disjoint S T := by
          rw [Finset.disjoint_left]
          intro i hiS hiT
          have hzero : u₁ i = 0 := by
            simpa [directionZeroSet] using hSzero hiS
          have hsupport : u₁ i ≠ 0 := by
            simpa [directionSupportSet] using hTsub hiT
          exact hsupport hzero
        have hcard :
            (S ∪ T).card = S.card + (a - S.card) := by
          rw [Finset.card_union_of_disjoint hdisj, hTcard]
        have hlarge : k ≤ (S ∪ T).card := by
          rw [hcard]
          omega
        exact coordinateAgreementFiber_card_le_one_of_k_le
          dom hk (fun i => u₀ i + γ • u₁ i) hlarge
    _ = ∑ _γ : F, (directionSupportSet u₁).card.choose (a - S.card) := by
        refine Finset.sum_congr rfl fun _γ _ => ?_
        rw [Finset.sum_const, smul_eq_mul, Finset.card_powersetCard, Nat.mul_one]
    _ = Fintype.card F * (directionSupportSet u₁).card.choose (a - S.card) := by
        rw [Finset.sum_const, smul_eq_mul, Finset.card_univ]

open Classical in
/-- High zero profiles have the same scalar-times-support-binomial cover-sum ceiling without
using the exact threshold equality `k ≤ a`.  It is enough that the fixed zero-profile `S` already
has at least `k` coordinates. -/
theorem supportRatioCoverSum_le_field_card_mul_choose_of_k_le_card
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a : ℕ)
    (u₀ u₁ : Fin n → F) {S : Finset (Fin n)} (hSlarge : k ≤ S.card) :
    (∑ γ : F, ∑ T ∈ (directionSupportSet u₁).powersetCard (a - S.card),
      (coordinateAgreementFiber dom k (fun i => u₀ i + γ • u₁ i) (S ∪ T)).card) ≤
      Fintype.card F * (directionSupportSet u₁).card.choose (a - S.card) := by
  calc
    (∑ γ : F, ∑ T ∈ (directionSupportSet u₁).powersetCard (a - S.card),
        (coordinateAgreementFiber dom k (fun i => u₀ i + γ • u₁ i) (S ∪ T)).card)
        ≤ ∑ _γ : F, ∑ _T ∈ (directionSupportSet u₁).powersetCard (a - S.card), 1 := by
        refine Finset.sum_le_sum fun γ _ => ?_
        refine Finset.sum_le_sum fun T _hT => ?_
        have hSsubUnion : S ⊆ S ∪ T := by
          intro i hi
          exact Finset.mem_union_left T hi
        have hlarge : k ≤ (S ∪ T).card :=
          le_trans hSlarge (Finset.card_le_card hSsubUnion)
        exact coordinateAgreementFiber_card_le_one_of_k_le
          dom hk (fun i => u₀ i + γ • u₁ i) hlarge
    _ = ∑ _γ : F, (directionSupportSet u₁).card.choose (a - S.card) := by
        refine Finset.sum_congr rfl fun _γ _ => ?_
        rw [Finset.sum_const, smul_eq_mul, Finset.card_powersetCard, Nat.mul_one]
    _ = Fintype.card F * (directionSupportSet u₁).card.choose (a - S.card) := by
        rw [Finset.sum_const, smul_eq_mul, Finset.card_univ]

open Classical in
/-- If the agreement threshold is at least the RS dimension, each member of the explicit
support-ratio line-fiber cover is singleton-bounded by RS uniqueness.  The cover therefore costs
only one candidate for each scalar and moving-support subfiber. -/
theorem supportRatioLineFiberCover_card_le_field_card_mul_choose
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) {a : ℕ} (hka : k ≤ a)
    (u₀ u₁ : Fin n → F) {S : Finset (Fin n)}
    (hSzero : S ⊆ directionZeroSet u₁) :
    (supportRatioLineFiberCover dom k a u₀ u₁ S).card ≤
      Fintype.card F * (directionSupportSet u₁).card.choose (a - S.card) := by
  exact le_trans
    (supportRatioLineFiberCover_card_le_sum_coordinateAgreementFibers
      dom k a u₀ u₁ S)
    (supportRatioCoverSum_le_field_card_mul_choose dom hk hka u₀ u₁ hSzero)

open Classical in
/-- Support-ratio-heavy coordinate fibers inherit the scalar-times-binomial bound from the
explicit line-fiber cover. -/
theorem supportRatioHeavyCoordinateFiber_card_le_field_card_mul_choose
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) {a : ℕ} (hka : k ≤ a)
    (u₀ u₁ : Fin n → F) {S : Finset (Fin n)}
    (hSzero : S ⊆ directionZeroSet u₁) :
    (supportRatioHeavyCoordinateFiber dom k a u₀ u₁ S).card ≤
      Fintype.card F * (directionSupportSet u₁).card.choose (a - S.card) :=
  le_trans
    (supportRatioHeavyCoordinateFiber_card_le_supportRatioLineFiberCover_card
      dom k a u₀ u₁ hSzero)
    (supportRatioLineFiberCover_card_le_field_card_mul_choose
      dom hk hka u₀ u₁ hSzero)

open Classical in
/-- Uniform-domain version of
`supportRatioHeavyCoordinateFiber_card_le_field_card_mul_choose`, replacing the line support size
by the ambient block length. -/
theorem supportRatioHeavyCoordinateFiber_card_le_field_card_mul_choose_n
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) {a : ℕ} (hka : k ≤ a)
    (u₀ u₁ : Fin n → F) {S : Finset (Fin n)}
    (hSzero : S ⊆ directionZeroSet u₁) :
    (supportRatioHeavyCoordinateFiber dom k a u₀ u₁ S).card ≤
      Fintype.card F * n.choose (a - S.card) := by
  have hsupp : (directionSupportSet u₁).card ≤ n := by
    simpa using (Finset.card_le_univ (directionSupportSet u₁))
  exact le_trans
    (supportRatioHeavyCoordinateFiber_card_le_field_card_mul_choose
      dom hk hka u₀ u₁ hSzero)
    (Nat.mul_le_mul_left (Fintype.card F)
      (Nat.choose_le_choose (a - S.card) hsupp))

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

/-- A per-line support-ratio-heavy coordinate-fiber budget restricted to low interpolation
profiles `t < k`. -/
def ZeroLowSupportRatioHeavyCoordinateFiberBudgeted
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (M : ℕ → ℕ) : Prop :=
  ∀ t : ℕ, t < a → t < k → ∀ S ∈ (directionZeroSet u₁).powersetCard t,
    (supportRatioHeavyCoordinateFiber dom k a u₀ u₁ S).card ≤ M t

open Classical in
/-- The explicit support-ratio line-fiber cover supplies a per-line support-ratio-heavy budget:
one candidate for each scalar and each moving-support subfiber of size `a - t`. -/
theorem zeroSupportRatioHeavyCoordinateFiberBudgeted_of_lineFiberCoverChoose
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) {a : ℕ} (hka : k ≤ a)
    (u₀ u₁ : Fin n → F) :
    ZeroSupportRatioHeavyCoordinateFiberBudgeted dom k a u₀ u₁
      (fun t => Fintype.card F * (directionSupportSet u₁).card.choose (a - t)) := by
  intro t _ht S hS
  obtain ⟨hSsub, hScard⟩ := Finset.mem_powersetCard.mp hS
  simpa [hScard] using
    supportRatioHeavyCoordinateFiber_card_le_field_card_mul_choose
      dom hk hka u₀ u₁ hSsub

open Classical in
/-- Ambient-length variant of
`zeroSupportRatioHeavyCoordinateFiberBudgeted_of_lineFiberCoverChoose`. -/
theorem zeroSupportRatioHeavyCoordinateFiberBudgeted_of_lineFiberCoverChoose_n
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) {a : ℕ} (hka : k ≤ a)
    (u₀ u₁ : Fin n → F) :
    ZeroSupportRatioHeavyCoordinateFiberBudgeted dom k a u₀ u₁
      (fun t => Fintype.card F * n.choose (a - t)) := by
  intro t _ht S hS
  obtain ⟨hSsub, hScard⟩ := Finset.mem_powersetCard.mp hS
  simpa [hScard] using
    supportRatioHeavyCoordinateFiber_card_le_field_card_mul_choose_n
      dom hk hka u₀ u₁ hSsub

/-- A per-line union-bound budget for the explicit support-ratio line-fiber cover. -/
def ZeroSupportRatioCoverSumBudgeted
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (M : ℕ → ℕ) : Prop :=
  ∀ t : ℕ, t < a → ∀ S ∈ (directionZeroSet u₁).powersetCard t,
    (∑ γ : F, ∑ T ∈ (directionSupportSet u₁).powersetCard (a - t),
      (coordinateAgreementFiber dom k (fun i => u₀ i + γ • u₁ i) (S ∪ T)).card) ≤ M t

/-- A per-line explicit support-ratio cover-sum budget restricted to low interpolation profiles
`t < k`. -/
def ZeroLowSupportRatioCoverSumBudgeted
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (M : ℕ → ℕ) : Prop :=
  ∀ t : ℕ, t < a → t < k → ∀ S ∈ (directionZeroSet u₁).powersetCard t,
    (∑ γ : F, ∑ T ∈ (directionSupportSet u₁).powersetCard (a - t),
      (coordinateAgreementFiber dom k (fun i => u₀ i + γ • u₁ i) (S ∪ T)).card) ≤ M t

open Classical in
/-- The explicit cover-sum budget implies the support-ratio-heavy coordinate-fiber budget. -/
theorem zeroSupportRatioHeavyBudgeted_of_coverSumBudgeted
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (M : ℕ → ℕ)
    (hCover : ZeroSupportRatioCoverSumBudgeted dom k a u₀ u₁ M) :
    ZeroSupportRatioHeavyCoordinateFiberBudgeted dom k a u₀ u₁ M := by
  intro t ht S hS
  have hSzero : S ⊆ directionZeroSet u₁ := (Finset.mem_powersetCard.mp hS).1
  have hScard : S.card = t := (Finset.mem_powersetCard.mp hS).2
  calc
    (supportRatioHeavyCoordinateFiber dom k a u₀ u₁ S).card
        ≤ (supportRatioLineFiberCover dom k a u₀ u₁ S).card :=
          supportRatioHeavyCoordinateFiber_card_le_supportRatioLineFiberCover_card
            dom k a u₀ u₁ hSzero
    _ ≤ ∑ γ : F, ∑ T ∈ (directionSupportSet u₁).powersetCard (a - S.card),
          (coordinateAgreementFiber dom k (fun i => u₀ i + γ • u₁ i) (S ∪ T)).card :=
        supportRatioLineFiberCover_card_le_sum_coordinateAgreementFibers dom k a u₀ u₁ S
    _ = ∑ γ : F, ∑ T ∈ (directionSupportSet u₁).powersetCard (a - t),
          (coordinateAgreementFiber dom k (fun i => u₀ i + γ • u₁ i) (S ∪ T)).card := by
        simp [hScard]
    _ ≤ M t := hCover t ht S hS

/-- Uniform support-ratio-heavy coordinate-fiber budget on the large-zero safe branch. -/
def UniformLargeZeroSafeSupportRatioHeavyCoordinateFiberBudgeted
    (dom : Fin n ↪ F) (k a : ℕ) (M : ℕ → ℕ) : Prop :=
  ∀ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
    ZeroDirectionSafeLine dom k a u₀ u₁ →
      ZeroSupportRatioHeavyCoordinateFiberBudgeted dom k a u₀ u₁ M

/-- Uniform low-profile support-ratio-heavy coordinate-fiber budgets on the large-zero safe
branch. -/
def UniformLargeZeroSafeLowSupportRatioHeavyCoordinateFiberBudgeted
    (dom : Fin n ↪ F) (k a : ℕ) (M : ℕ → ℕ) : Prop :=
  ∀ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
    ZeroDirectionSafeLine dom k a u₀ u₁ →
      ZeroLowSupportRatioHeavyCoordinateFiberBudgeted dom k a u₀ u₁ M

/-- Uniform explicit cover-sum budgets on the large-zero safe branch. -/
def UniformLargeZeroSafeSupportRatioCoverSumBudgeted
    (dom : Fin n ↪ F) (k a : ℕ) (M : ℕ → ℕ) : Prop :=
  ∀ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
    ZeroDirectionSafeLine dom k a u₀ u₁ →
      ZeroSupportRatioCoverSumBudgeted dom k a u₀ u₁ M

/-- Uniform low-profile explicit cover-sum budgets on the large-zero safe branch. -/
def UniformLargeZeroSafeLowSupportRatioCoverSumBudgeted
    (dom : Fin n ↪ F) (k a : ℕ) (M : ℕ → ℕ) : Prop :=
  ∀ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
    ZeroDirectionSafeLine dom k a u₀ u₁ →
      ZeroLowSupportRatioCoverSumBudgeted dom k a u₀ u₁ M

open Classical in
/-- The explicit support-ratio cover sum itself satisfies the scalar-times-support-binomial
baseline under RS uniqueness. -/
theorem zeroSupportRatioCoverSumBudgeted_of_lineFiberCoverChoose
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) {a : ℕ} (hka : k ≤ a)
    (u₀ u₁ : Fin n → F) :
    ZeroSupportRatioCoverSumBudgeted dom k a u₀ u₁
      (fun t => Fintype.card F * (directionSupportSet u₁).card.choose (a - t)) := by
  intro _t _ht S hS
  obtain ⟨hSsub, hScard⟩ := Finset.mem_powersetCard.mp hS
  simpa [hScard] using
    supportRatioCoverSum_le_field_card_mul_choose dom hk hka u₀ u₁ hSsub

open Classical in
/-- Ambient-length variant of
`zeroSupportRatioCoverSumBudgeted_of_lineFiberCoverChoose`. -/
theorem zeroSupportRatioCoverSumBudgeted_of_lineFiberCoverChoose_n
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) {a : ℕ} (hka : k ≤ a)
    (u₀ u₁ : Fin n → F) :
    ZeroSupportRatioCoverSumBudgeted dom k a u₀ u₁
      (fun t => Fintype.card F * n.choose (a - t)) := by
  intro t ht S hS
  have hsupp : (directionSupportSet u₁).card ≤ n := by
    simpa using (Finset.card_le_univ (directionSupportSet u₁))
  exact le_trans
    (zeroSupportRatioCoverSumBudgeted_of_lineFiberCoverChoose
      dom hk hka u₀ u₁ t ht S hS)
    (Nat.mul_le_mul_left (Fintype.card F)
      (Nat.choose_le_choose (a - t) hsupp))

open Classical in
/-- Uniform ambient-length support-ratio cover-sum baseline. -/
theorem uniformLargeZeroSafeSupportRatioCoverSumBudgeted_of_lineFiberCoverChoose_n
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) {a : ℕ} (hka : k ≤ a) :
    UniformLargeZeroSafeSupportRatioCoverSumBudgeted dom k a
      (fun t => Fintype.card F * n.choose (a - t)) := by
  intro u₀ u₁ _hnotEligible _hsafe
  exact zeroSupportRatioCoverSumBudgeted_of_lineFiberCoverChoose_n
    dom hk hka u₀ u₁

open Classical in
/-- A low-profile cover-sum budget plus the scalar-times-support-binomial high-profile ceiling
gives the full explicit support-ratio cover-sum budget. -/
theorem zeroSupportRatioCoverSumBudgeted_of_low_and_high_choose
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a : ℕ)
    (u₀ u₁ : Fin n → F) (M : ℕ → ℕ)
    (hLow : ZeroLowSupportRatioCoverSumBudgeted dom k a u₀ u₁ M)
    (hHigh :
      ∀ t : ℕ, t < a → k ≤ t →
        Fintype.card F * (directionSupportSet u₁).card.choose (a - t) ≤ M t) :
    ZeroSupportRatioCoverSumBudgeted dom k a u₀ u₁ M := by
  intro t ht S hS
  by_cases hlow : t < k
  · exact hLow t ht hlow S hS
  · have hkt : k ≤ t := le_of_not_gt hlow
    have hScard : S.card = t := (Finset.mem_powersetCard.mp hS).2
    have hcover :
        (∑ γ : F, ∑ T ∈ (directionSupportSet u₁).powersetCard (a - t),
          (coordinateAgreementFiber dom k (fun i => u₀ i + γ • u₁ i) (S ∪ T)).card) ≤
          Fintype.card F * (directionSupportSet u₁).card.choose (a - t) := by
      have hcoverS :=
        supportRatioCoverSum_le_field_card_mul_choose_of_k_le_card
          dom hk a u₀ u₁ (by rw [hScard]; exact hkt)
      rwa [hScard] at hcoverS
    exact le_trans hcover (hHigh t ht hkt)

open Classical in
/-- Uniform version of `zeroSupportRatioCoverSumBudgeted_of_low_and_high_choose`. -/
theorem uniformLargeZeroSafeSupportRatioCoverSumBudgeted_of_low_and_high_choose
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a : ℕ) (M : ℕ → ℕ)
    (hLow : UniformLargeZeroSafeLowSupportRatioCoverSumBudgeted dom k a M)
    (hHigh :
      ∀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
        ∀ t : ℕ, t < a → k ≤ t →
          Fintype.card F * (directionSupportSet u₁).card.choose (a - t) ≤ M t) :
    UniformLargeZeroSafeSupportRatioCoverSumBudgeted dom k a M := by
  intro u₀ u₁ hnotEligible hsafe
  exact zeroSupportRatioCoverSumBudgeted_of_low_and_high_choose
    dom hk a u₀ u₁ M (hLow u₀ u₁ hnotEligible hsafe)
    (hHigh u₁ hnotEligible)

open Classical in
/-- Exact failure form for one line's explicit support-ratio cover-sum budget. -/
theorem not_zeroSupportRatioCoverSumBudgeted_iff_exists_coverSum_gt
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (M : ℕ → ℕ) :
    (¬ ZeroSupportRatioCoverSumBudgeted dom k a u₀ u₁ M) ↔
      ∃ t : ℕ, t < a ∧ ∃ S ∈ (directionZeroSet u₁).powersetCard t,
        M t < ∑ γ : F, ∑ T ∈ (directionSupportSet u₁).powersetCard (a - t),
          (coordinateAgreementFiber dom k (fun i => u₀ i + γ • u₁ i) (S ∪ T)).card := by
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro t ht S hS
    exact le_of_not_gt
      (fun hgt => hnone ⟨t, ht, S, hS, hgt⟩)
  · rintro ⟨t, ht, S, hS, hgt⟩ hbudget
    exact (not_lt_of_ge (hbudget t ht S hS)) hgt

open Classical in
/-- Exact failure form for the uniform large-zero safe explicit support-ratio cover-sum budget. -/
theorem not_uniformLargeZeroSafeSupportRatioCoverSumBudgeted_iff_exists_coverSum_gt
    (dom : Fin n ↪ F) (k a : ℕ) (M : ℕ → ℕ) :
    (¬ UniformLargeZeroSafeSupportRatioCoverSumBudgeted dom k a M) ↔
      ∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
        ZeroDirectionSafeLine dom k a u₀ u₁ ∧
          ∃ t : ℕ, t < a ∧ ∃ S ∈ (directionZeroSet u₁).powersetCard t,
            M t < ∑ γ : F, ∑ T ∈ (directionSupportSet u₁).powersetCard (a - t),
              (coordinateAgreementFiber dom k
                (fun i => u₀ i + γ • u₁ i) (S ∪ T)).card := by
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro u₀ u₁ hnotEligible hsafe t ht S hS
    exact le_of_not_gt
      (fun hgt => hnone ⟨u₀, u₁, hnotEligible, hsafe, t, ht, S, hS, hgt⟩)
  · rintro ⟨u₀, u₁, hnotEligible, hsafe, t, ht, S, hS, hgt⟩ hbudget
    exact (not_lt_of_ge (hbudget u₀ u₁ hnotEligible hsafe t ht S hS)) hgt

open Classical in
/-- Exact failure form for one line's low-profile explicit support-ratio cover-sum budget. -/
theorem not_zeroLowSupportRatioCoverSumBudgeted_iff_exists_low_coverSum_gt
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (M : ℕ → ℕ) :
    (¬ ZeroLowSupportRatioCoverSumBudgeted dom k a u₀ u₁ M) ↔
      ∃ t : ℕ, t < a ∧ t < k ∧ ∃ S ∈ (directionZeroSet u₁).powersetCard t,
        M t < ∑ γ : F, ∑ T ∈ (directionSupportSet u₁).powersetCard (a - t),
          (coordinateAgreementFiber dom k (fun i => u₀ i + γ • u₁ i) (S ∪ T)).card := by
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
/-- Exact failure form for the uniform low-profile explicit support-ratio cover-sum budget. -/
theorem
    not_uniformLargeZeroSafeLowSupportRatioCoverSumBudgeted_iff_exists_low_coverSum_gt
    (dom : Fin n ↪ F) (k a : ℕ) (M : ℕ → ℕ) :
    (¬ UniformLargeZeroSafeLowSupportRatioCoverSumBudgeted dom k a M) ↔
      ∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
        ZeroDirectionSafeLine dom k a u₀ u₁ ∧
          ∃ t : ℕ, t < a ∧ t < k ∧ ∃ S ∈ (directionZeroSet u₁).powersetCard t,
            M t < ∑ γ : F, ∑ T ∈ (directionSupportSet u₁).powersetCard (a - t),
              (coordinateAgreementFiber dom k
                (fun i => u₀ i + γ • u₁ i) (S ∪ T)).card := by
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
/-- Exact failure form for one line's low-profile support-ratio-heavy coordinate-fiber budget. -/
theorem not_zeroLowSupportRatioHeavyBudgeted_iff_exists_low_fiber_gt
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (M : ℕ → ℕ) :
    (¬ ZeroLowSupportRatioHeavyCoordinateFiberBudgeted dom k a u₀ u₁ M) ↔
      ∃ t : ℕ, t < a ∧ t < k ∧ ∃ S ∈ (directionZeroSet u₁).powersetCard t,
        M t < (supportRatioHeavyCoordinateFiber dom k a u₀ u₁ S).card := by
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
/-- Exact failure form for the uniform low-profile support-ratio-heavy coordinate-fiber budget. -/
theorem not_uniformLargeZeroSafeLowSupportRatioHeavyBudgeted_iff_exists_low_fiber_gt
    (dom : Fin n ↪ F) (k a : ℕ) (M : ℕ → ℕ) :
    (¬ UniformLargeZeroSafeLowSupportRatioHeavyCoordinateFiberBudgeted dom k a M) ↔
      ∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
        ZeroDirectionSafeLine dom k a u₀ u₁ ∧
          ∃ t : ℕ, t < a ∧ t < k ∧ ∃ S ∈ (directionZeroSet u₁).powersetCard t,
            M t < (supportRatioHeavyCoordinateFiber dom k a u₀ u₁ S).card := by
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
/-- Uniform version of `zeroSupportRatioHeavyBudgeted_of_coverSumBudgeted`. -/
theorem uniformSupportRatioHeavyBudgeted_of_coverSumBudgeted
    (dom : Fin n ↪ F) (k a : ℕ) (M : ℕ → ℕ)
    (hCover : UniformLargeZeroSafeSupportRatioCoverSumBudgeted dom k a M) :
    UniformLargeZeroSafeSupportRatioHeavyCoordinateFiberBudgeted dom k a M := by
  intro u₀ u₁ hnotEligible hsafe
  exact zeroSupportRatioHeavyBudgeted_of_coverSumBudgeted
    dom k a u₀ u₁ M (hCover u₀ u₁ hnotEligible hsafe)

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
/-- The scalar-times-ambient-binomial line-cover envelope is a uniform support-ratio-heavy
budget. -/
theorem uniformLargeZeroSafeSupportRatioHeavyCoordinateFiberBudgeted_of_lineFiberCoverChoose_n
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) {a : ℕ} (hka : k ≤ a) :
    UniformLargeZeroSafeSupportRatioHeavyCoordinateFiberBudgeted dom k a
      (fun t => Fintype.card F * n.choose (a - t)) := by
  intro u₀ u₁ _hnotEligible _hsafe
  exact zeroSupportRatioHeavyCoordinateFiberBudgeted_of_lineFiberCoverChoose_n
    dom hk hka u₀ u₁

open Classical in
/-- A low-profile support-ratio-heavy budget plus the high-profile RS uniqueness ceiling gives the
full support-ratio-heavy coordinate-fiber budget. -/
theorem zeroSupportRatioHeavyCoordinateFiberBudgeted_of_low_and_high_one
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a : ℕ)
    (u₀ u₁ : Fin n → F) (M : ℕ → ℕ)
    (hLow : ZeroLowSupportRatioHeavyCoordinateFiberBudgeted dom k a u₀ u₁ M)
    (hHigh : ∀ t : ℕ, t < a → k ≤ t → 1 ≤ M t) :
    ZeroSupportRatioHeavyCoordinateFiberBudgeted dom k a u₀ u₁ M := by
  intro t ht S hS
  by_cases hlow : t < k
  · exact hLow t ht hlow S hS
  · have hkt : k ≤ t := le_of_not_gt hlow
    have hScard : S.card = t := (Finset.mem_powersetCard.mp hS).2
    have hfiber :
        (supportRatioHeavyCoordinateFiber dom k a u₀ u₁ S).card ≤ 1 :=
      supportRatioHeavyCoordinateFiber_card_le_one_of_k_le dom hk a u₀ u₁
        (by rw [hScard]; exact hkt)
    exact le_trans hfiber (hHigh t ht hkt)

open Classical in
/-- Uniform version of `zeroSupportRatioHeavyCoordinateFiberBudgeted_of_low_and_high_one`. -/
theorem uniformLargeZeroSafeSupportRatioHeavyCoordinateFiberBudgeted_of_low_and_high_one
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a : ℕ) (M : ℕ → ℕ)
    (hLow : UniformLargeZeroSafeLowSupportRatioHeavyCoordinateFiberBudgeted dom k a M)
    (hHigh : ∀ t : ℕ, t < a → k ≤ t → 1 ≤ M t) :
    UniformLargeZeroSafeSupportRatioHeavyCoordinateFiberBudgeted dom k a M := by
  intro u₀ u₁ hnotEligible hsafe
  exact zeroSupportRatioHeavyCoordinateFiberBudgeted_of_low_and_high_one
    dom hk a u₀ u₁ M (hLow u₀ u₁ hnotEligible hsafe) hHigh

open Classical in
/-- The ambient-binomial line-cover envelope gives a uniform exact-appearance-fiber budget. -/
theorem uniformExactAppearingZeroAgreementFiberBudgeted_of_lineFiberCoverChoose_n
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) {a : ℕ} (hka : k ≤ a) :
    UniformLargeZeroSafeExactAppearingZeroAgreementFiberBudgeted dom k a
      (fun t => Fintype.card F * n.choose (a - t)) :=
  uniformExactAppearingZeroAgreementFiberBudgeted_of_supportRatioHeavyCoordinateFiberBudgeted
    dom k a (fun t => Fintype.card F * n.choose (a - t))
    (uniformLargeZeroSafeSupportRatioHeavyCoordinateFiberBudgeted_of_lineFiberCoverChoose_n
      dom hk hka)

open Classical in
/-- Direct production wrapper for the ambient-binomial support-ratio line-cover envelope. -/
theorem uniformLineBadScalarsBudgeted_of_supportAdjustedBudgetFits_and_lineFiberCoverChoose_n
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) {a : ℕ} (hka : k ≤ a) (L B : ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hFiberFits : UniformLargeZeroSafeAppearingCoordinateFiberBudgetFits
      (F := F) (n := n) a B (fun t => Fintype.card F * n.choose (a - t))) :
    UniformLineBadScalarsBudgeted dom k a B :=
  uniformLineBadScalarsBudgeted_of_supportAdjustedBudgetFits_and_exactAppearingFibers
    dom k a L B (fun t => Fintype.card F * n.choose (a - t))
    hSupport hFits hZeroSafe
    (uniformExactAppearingZeroAgreementFiberBudgeted_of_lineFiberCoverChoose_n
      dom hk hka)
    hFiberFits

open Classical in
/-- Production wrapper for the low/high split support-ratio-heavy coordinate-fiber route.  Low
profiles `t < k` are supplied by the caller; high profiles are discharged by RS uniqueness. -/
theorem uniformLineBadScalarsBudgeted_of_lowSupportRatioHeavyCoordFibers
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a L B : ℕ) (M : ℕ → ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hLow : UniformLargeZeroSafeLowSupportRatioHeavyCoordinateFiberBudgeted dom k a M)
    (hHigh : ∀ t : ℕ, t < a → k ≤ t → 1 ≤ M t)
    (hFiberFits :
      UniformLargeZeroSafeAppearingCoordinateFiberBudgetFits (F := F) (n := n) a B M) :
    UniformLineBadScalarsBudgeted dom k a B :=
  uniformLineBadScalarsBudgeted_of_supportAdjustedBudgetFits_and_exactAppearingFibers
    dom k a L B M hSupport hFits hZeroSafe
    (uniformExactAppearingZeroAgreementFiberBudgeted_of_supportRatioHeavyCoordinateFiberBudgeted
      dom k a M
      (uniformLargeZeroSafeSupportRatioHeavyCoordinateFiberBudgeted_of_low_and_high_one
        dom hk a M hLow hHigh))
    hFiberFits

open Classical in
/-- If support-side production, zero-direction safety, arithmetic fit, and the high-profile
singleton ceiling are fixed, failed bad-scalar production exposes an overfull low-profile
support-ratio-heavy coordinate fiber. -/
theorem exists_largeZero_safe_low_supportRatioHeavyCoordFiber_gt_of_not_budgeted
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
          M t < (supportRatioHeavyCoordinateFiber dom k a u₀ u₁ S).card := by
  by_contra hnone
  have hLow :
      UniformLargeZeroSafeLowSupportRatioHeavyCoordinateFiberBudgeted dom k a M := by
    intro u₀ u₁ hnotEligible hsafe t ht hlow S hS
    exact le_of_not_gt
      (fun hgt => hnone ⟨u₀, u₁, hnotEligible, hsafe, t, ht, hlow, S, hS, hgt⟩)
  exact hnot
    (uniformLineBadScalarsBudgeted_of_lowSupportRatioHeavyCoordFibers
      dom hk a L B M hSupport hFits hZeroSafe hLow hHigh hFiberFits)

open Classical in
/-- If uniform bad-scalar production fails after the support-side hypotheses, then the
ambient-binomial line-cover arithmetic fit is impossible. -/
theorem
    not_lineFiberCoverChooseBudgetFits_of_not_uniformLineBadScalarsBudgeted
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) {a : ℕ} (hka : k ≤ a) (L B : ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hnot : ¬ UniformLineBadScalarsBudgeted dom k a B) :
    ¬ UniformLargeZeroSafeAppearingCoordinateFiberBudgetFits
      (F := F) (n := n) a B (fun t => Fintype.card F * n.choose (a - t)) := by
  intro hFiberFits
  exact hnot
    (uniformLineBadScalarsBudgeted_of_supportAdjustedBudgetFits_and_lineFiberCoverChoose_n
      dom hk hka L B hSupport hFits hZeroSafe hFiberFits)

/-- Per-summand form of the ambient-binomial support-ratio line-cover arithmetic fit. -/
theorem lineFiberCoverChooseBudgetFits_term_le
    (a B t : ℕ) (u₁ : Fin n → F) (ht : t < a)
    (hFits : ZeroAppearingCoordinateFiberBudgetFits (F := F) (n := n) a B u₁
      (fun t => Fintype.card F * n.choose (a - t))) :
    ((directionZeroSet u₁).card.choose t * (Fintype.card F * n.choose (a - t))) *
        ((directionSupportSet u₁).card / (a - t)) ≤ B := by
  have hmem : t ∈ Finset.range a := Finset.mem_range.mpr ht
  have hterm :
      ((directionZeroSet u₁).card.choose t * (Fintype.card F * n.choose (a - t))) *
          ((directionSupportSet u₁).card / (a - t)) ≤
        ∑ t ∈ Finset.range a,
          ((directionZeroSet u₁).card.choose t *
            (Fintype.card F * n.choose (a - t))) *
            ((directionSupportSet u₁).card / (a - t)) := by
    exact Finset.single_le_sum
      (f := fun t =>
        ((directionZeroSet u₁).card.choose t *
          (Fintype.card F * n.choose (a - t))) *
          ((directionSupportSet u₁).card / (a - t)))
      (fun _ _ => Nat.zero_le _) hmem
  exact le_trans hterm hFits

/-- One over-budget weighted ambient-binomial summand refutes the support-ratio cover fit. -/
theorem not_lineFiberCoverChooseBudgetFits_of_exists_term_gt
    (a B : ℕ)
    (hgt : ∃ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
      ∃ t : ℕ, t < a ∧
        B <
          ((directionZeroSet u₁).card.choose t *
              (Fintype.card F * n.choose (a - t))) *
            ((directionSupportSet u₁).card / (a - t))) :
    ¬ UniformLargeZeroSafeAppearingCoordinateFiberBudgetFits (F := F) (n := n) a B
      (fun t => Fintype.card F * n.choose (a - t)) := by
  intro hFits
  rcases hgt with ⟨u₁, hnotEligible, t, ht, hgt⟩
  exact (not_lt_of_ge
    (lineFiberCoverChooseBudgetFits_term_le
      (F := F) (n := n) a B t u₁ ht (hFits u₁ hnotEligible))) hgt

open Classical in
/-- Failed production under the ambient support-ratio cover envelope exposes an over-budget
weighted binomial sum for some large-zero direction. -/
theorem exists_lineFiberCoverChooseBudgetSum_gt_of_not_uniformLineBadScalarsBudgeted
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) {a : ℕ} (hka : k ≤ a) (L B : ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hnot : ¬ UniformLineBadScalarsBudgeted dom k a B) :
    ∃ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
      B < ∑ t ∈ Finset.range a,
        ((directionZeroSet u₁).card.choose t *
            (Fintype.card F * n.choose (a - t))) *
          ((directionSupportSet u₁).card / (a - t)) := by
  have hnotFits :=
    not_lineFiberCoverChooseBudgetFits_of_not_uniformLineBadScalarsBudgeted
      dom hk hka L B hSupport hFits hZeroSafe hnot
  by_contra hnone
  apply hnotFits
  intro u₁ hnotEligible
  exact le_of_not_gt
    (fun hgt => hnone ⟨u₁, hnotEligible, hgt⟩)

open Classical in
/-- Production wrapper for the explicit support-ratio cover-sum route. -/
theorem uniformLineBadScalarsBudgeted_of_supportRatioCoverSums
    (dom : Fin n ↪ F) (k a L B : ℕ) (M : ℕ → ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hCover : UniformLargeZeroSafeSupportRatioCoverSumBudgeted dom k a M)
    (hFiberFits :
      UniformLargeZeroSafeAppearingCoordinateFiberBudgetFits (F := F) (n := n) a B M) :
    UniformLineBadScalarsBudgeted dom k a B :=
  uniformLineBadScalarsBudgeted_of_supportAdjustedBudgetFits_and_exactAppearingFibers
    dom k a L B M hSupport hFits hZeroSafe
    (uniformExactAppearingZeroAgreementFiberBudgeted_of_supportRatioHeavyCoordinateFiberBudgeted
      dom k a M
      (uniformSupportRatioHeavyBudgeted_of_coverSumBudgeted dom k a M hCover))
    hFiberFits

open Classical in
/-- Production wrapper for the low/high split support-ratio cover-sum route.  Low profiles
`t < k` are supplied by the caller; high profiles are discharged by the
scalar-times-support-binomial ceiling. -/
theorem uniformLineBadScalarsBudgeted_of_lowSupportRatioCoverSums
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a L B : ℕ) (M : ℕ → ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hLow : UniformLargeZeroSafeLowSupportRatioCoverSumBudgeted dom k a M)
    (hHigh :
      ∀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
        ∀ t : ℕ, t < a → k ≤ t →
          Fintype.card F * (directionSupportSet u₁).card.choose (a - t) ≤ M t)
    (hFiberFits :
      UniformLargeZeroSafeAppearingCoordinateFiberBudgetFits (F := F) (n := n) a B M) :
    UniformLineBadScalarsBudgeted dom k a B :=
  uniformLineBadScalarsBudgeted_of_supportRatioCoverSums
    dom k a L B M hSupport hFits hZeroSafe
    (uniformLargeZeroSafeSupportRatioCoverSumBudgeted_of_low_and_high_choose
      dom hk a M hLow hHigh)
    hFiberFits

open Classical in
/-- If support-side production, zero-direction safety, arithmetic fit, and the high-profile
cover-sum ceiling are fixed, failed bad-scalar production exposes an overfull low-profile
support-ratio cover sum. -/
theorem exists_largeZero_safe_low_supportRatioCoverSum_gt_of_not_uniformLineBadScalarsBudgeted
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a L B : ℕ) (M : ℕ → ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hFiberFits :
      UniformLargeZeroSafeAppearingCoordinateFiberBudgetFits (F := F) (n := n) a B M)
    (hHigh :
      ∀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
        ∀ t : ℕ, t < a → k ≤ t →
          Fintype.card F * (directionSupportSet u₁).card.choose (a - t) ≤ M t)
    (hnot : ¬ UniformLineBadScalarsBudgeted dom k a B) :
    ∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
      ZeroDirectionSafeLine dom k a u₀ u₁ ∧
        ∃ t : ℕ, t < a ∧ t < k ∧ ∃ S ∈ (directionZeroSet u₁).powersetCard t,
          M t < ∑ γ : F, ∑ T ∈ (directionSupportSet u₁).powersetCard (a - t),
            (coordinateAgreementFiber dom k
              (fun i => u₀ i + γ • u₁ i) (S ∪ T)).card := by
  by_contra hnone
  have hLow : UniformLargeZeroSafeLowSupportRatioCoverSumBudgeted dom k a M := by
    intro u₀ u₁ hnotEligible hsafe t ht hlow S hS
    exact le_of_not_gt
      (fun hgt => hnone ⟨u₀, u₁, hnotEligible, hsafe, t, ht, hlow, S, hS, hgt⟩)
  exact hnot
    (uniformLineBadScalarsBudgeted_of_lowSupportRatioCoverSums
      dom hk a L B M hSupport hFits hZeroSafe hLow hHigh hFiberFits)

open Classical in
/-- Direct production wrapper through the explicit cover-sum interface using the ambient
scalar-times-binomial baseline. -/
theorem
    uniformLineBadScalarsBudgeted_of_supportAdjustedBudgetFits_and_coverSum_lineFiberCoverChoose_n
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) {a : ℕ} (hka : k ≤ a) (L B : ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hFiberFits : UniformLargeZeroSafeAppearingCoordinateFiberBudgetFits
      (F := F) (n := n) a B (fun t => Fintype.card F * n.choose (a - t))) :
    UniformLineBadScalarsBudgeted dom k a B :=
  uniformLineBadScalarsBudgeted_of_supportRatioCoverSums
    dom k a L B (fun t => Fintype.card F * n.choose (a - t))
    hSupport hFits hZeroSafe
    (uniformLargeZeroSafeSupportRatioCoverSumBudgeted_of_lineFiberCoverChoose_n
      dom hk hka)
    hFiberFits

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
/-- Scanner-facing converse for the explicit support-ratio cover-sum route.  Failed bad-scalar
production exposes a large-zero safe zero-profile whose finite `(γ, T)` cover sum exceeds the
proposed envelope. -/
theorem
    exists_largeZero_safe_supportRatioCoverSum_gt_of_not_uniformLineBadScalarsBudgeted
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
          M t < ∑ γ : F, ∑ T ∈ (directionSupportSet u₁).powersetCard (a - t),
            (coordinateAgreementFiber dom k (fun i => u₀ i + γ • u₁ i) (S ∪ T)).card := by
  rcases
      (exists_largeZero_safe_supportRatioHeavyCoordFiber_gt_of_not_uniformLineBadScalarsBudgeted
          dom k a L B M hSupport hFits hZeroSafe hFiberFits hnot) with
    ⟨u₀, u₁, hnotEligible, hsafe, t, ht, S, hS, hgt⟩
  refine ⟨u₀, u₁, hnotEligible, hsafe, t, ht, S, hS, ?_⟩
  have hSzero : S ⊆ directionZeroSet u₁ := (Finset.mem_powersetCard.mp hS).1
  have hScard : S.card = t := (Finset.mem_powersetCard.mp hS).2
  have hle :
      (supportRatioHeavyCoordinateFiber dom k a u₀ u₁ S).card
        ≤ ∑ γ : F, ∑ T ∈ (directionSupportSet u₁).powersetCard (a - t),
            (coordinateAgreementFiber dom k (fun i => u₀ i + γ • u₁ i) (S ∪ T)).card := by
    calc
      (supportRatioHeavyCoordinateFiber dom k a u₀ u₁ S).card
          ≤ (supportRatioLineFiberCover dom k a u₀ u₁ S).card :=
            supportRatioHeavyCoordinateFiber_card_le_supportRatioLineFiberCover_card
              dom k a u₀ u₁ hSzero
      _ ≤ ∑ γ : F, ∑ T ∈ (directionSupportSet u₁).powersetCard (a - S.card),
            (coordinateAgreementFiber dom k (fun i => u₀ i + γ • u₁ i) (S ∪ T)).card :=
          supportRatioLineFiberCover_card_le_sum_coordinateAgreementFibers dom k a u₀ u₁ S
      _ = ∑ γ : F, ∑ T ∈ (directionSupportSet u₁).powersetCard (a - t),
            (coordinateAgreementFiber dom k (fun i => u₀ i + γ • u₁ i) (S ∪ T)).card := by
          simp [hScard]
  exact lt_of_lt_of_le hgt hle

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
/-- Full failure split for the explicit support-ratio cover-sum route.  Without assuming
zero-direction safety up front, failure returns either zero-direction saturation or an overfull
finite `(γ, T)` cover sum. -/
theorem
    unsafe_or_largeZero_safe_supportRatioCoverSum_gt_of_not_uniformLineBadScalarsBudgeted
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
            M t < ∑ γ : F, ∑ T ∈ (directionSupportSet u₁).powersetCard (a - t),
              (coordinateAgreementFiber dom k
                (fun i => u₀ i + γ • u₁ i) (S ∪ T)).card) := by
  by_cases hZeroSafe : UniformZeroDirectionSafe dom k a
  · exact Or.inr
      (exists_largeZero_safe_supportRatioCoverSum_gt_of_not_uniformLineBadScalarsBudgeted
        dom k a L B M hSupport hFits hZeroSafe hFiberFits hnot)
  · exact Or.inl
      ((not_uniformZeroDirectionSafe_iff_exists_line_codeword_zeroAgreement_ge
        dom k a).mp hZeroSafe)

open Classical in
/-- If `M` dominates the scalar-times-support-binomial cover-sum ceiling in every high range
`k ≤ t < a`, then any overfull explicit cover-sum witness must lie in the low interpolation range
`t < k`. -/
theorem exists_low_supportRatioCoverSum_gt_of_exists_coverSum_gt_and_high_choose
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a : ℕ)
    (u₀ u₁ : Fin n → F) (M : ℕ → ℕ)
    (hHigh :
      ∀ t : ℕ, t < a → k ≤ t →
        Fintype.card F * (directionSupportSet u₁).card.choose (a - t) ≤ M t)
    (hgt : ∃ t : ℕ, t < a ∧ ∃ S ∈ (directionZeroSet u₁).powersetCard t,
      M t < ∑ γ : F, ∑ T ∈ (directionSupportSet u₁).powersetCard (a - t),
        (coordinateAgreementFiber dom k (fun i => u₀ i + γ • u₁ i) (S ∪ T)).card) :
    ∃ t : ℕ, t < a ∧ t < k ∧ ∃ S ∈ (directionZeroSet u₁).powersetCard t,
      M t < ∑ γ : F, ∑ T ∈ (directionSupportSet u₁).powersetCard (a - t),
        (coordinateAgreementFiber dom k (fun i => u₀ i + γ • u₁ i) (S ∪ T)).card := by
  rcases hgt with ⟨t, ht, S, hS, hgt⟩
  by_cases hlow : t < k
  · exact ⟨t, ht, hlow, S, hS, hgt⟩
  · have hkt : k ≤ t := le_of_not_gt hlow
    have hScard : S.card = t := (Finset.mem_powersetCard.mp hS).2
    have hcover :
        (∑ γ : F, ∑ T ∈ (directionSupportSet u₁).powersetCard (a - t),
          (coordinateAgreementFiber dom k (fun i => u₀ i + γ • u₁ i) (S ∪ T)).card) ≤
          Fintype.card F * (directionSupportSet u₁).card.choose (a - t) := by
      have hcoverS :=
        supportRatioCoverSum_le_field_card_mul_choose_of_k_le_card
          dom hk a u₀ u₁ (by rw [hScard]; exact hkt)
      rwa [hScard] at hcoverS
    have hle :
        (∑ γ : F, ∑ T ∈ (directionSupportSet u₁).powersetCard (a - t),
          (coordinateAgreementFiber dom k (fun i => u₀ i + γ • u₁ i) (S ∪ T)).card) ≤
          M t :=
      le_trans hcover (hHigh t ht hkt)
    exact False.elim ((not_lt_of_ge hle) hgt)

open Classical in
/-- Scanner-facing full failure split with high explicit support-ratio cover sums discharged by
the scalar-times-support-binomial ceiling.  Failed uniform production must expose either
zero-direction saturation or a large-zero safe low cover-sum witness. -/
theorem
    unsafe_or_largeZero_safe_low_supportRatioCoverSum_gt_of_not_uniformLineBadScalarsBudgeted
    (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (a L B : ℕ) (M : ℕ → ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hFiberFits :
      UniformLargeZeroSafeAppearingCoordinateFiberBudgetFits (F := F) (n := n) a B M)
    (hHigh :
      ∀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
        ∀ t : ℕ, t < a → k ≤ t →
          Fintype.card F * (directionSupportSet u₁).card.choose (a - t) ≤ M t)
    (hnot : ¬ UniformLineBadScalarsBudgeted dom k a B) :
    (∃ u₀ u₁ c : Fin n → F, c ∈ (rsCode dom k : Submodule F (Fin n → F)) ∧
        a ≤ (directionZeroAgreementSet c u₀ u₁).card) ∨
      (∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
        ZeroDirectionSafeLine dom k a u₀ u₁ ∧
          ∃ t : ℕ, t < a ∧ t < k ∧ ∃ S ∈ (directionZeroSet u₁).powersetCard t,
            M t < ∑ γ : F, ∑ T ∈ (directionSupportSet u₁).powersetCard (a - t),
              (coordinateAgreementFiber dom k
                (fun i => u₀ i + γ • u₁ i) (S ∪ T)).card) := by
  rcases
      (unsafe_or_largeZero_safe_supportRatioCoverSum_gt_of_not_uniformLineBadScalarsBudgeted
        dom k a L B M hSupport hFits hFiberFits hnot) with hUnsafe | hCover
  · exact Or.inl hUnsafe
  · rcases hCover with ⟨u₀, u₁, hnotEligible, hsafe, hgt⟩
    exact Or.inr ⟨u₀, u₁, hnotEligible, hsafe,
      exists_low_supportRatioCoverSum_gt_of_exists_coverSum_gt_and_high_choose
        dom hk a u₀ u₁ M (hHigh u₁ hnotEligible) hgt⟩

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
#print axioms supportRatioLineFiberCover_subset_supportRatioHeavyCoordinateFiber
#print axioms supportRatioLineFiberCover_eq_supportRatioHeavyCoordinateFiber
#print axioms supportRatioLineFiberCover_card_eq_supportRatioHeavyCoordinateFiber_card
#print axioms supportRatioLineFiberCover_card_le_sum_coordinateAgreementFibers
#print axioms supportRatioCoverSum_le_field_card_mul_choose
#print axioms supportRatioCoverSum_le_field_card_mul_choose_of_k_le_card
#print axioms supportRatioLineFiberCover_card_le_field_card_mul_choose
#print axioms supportRatioHeavyCoordinateFiber_card_le_field_card_mul_choose
#print axioms supportRatioHeavyCoordinateFiber_card_le_field_card_mul_choose_n
#print axioms supportRatioHeavyCoordinateFiber_subset_coordinateAgreementFiber
#print axioms supportRatioHeavyCoordinateFiber_card_le_one_of_k_le
#print axioms ZeroLowSupportRatioHeavyCoordinateFiberBudgeted
#print axioms zeroSupportRatioHeavyCoordinateFiberBudgeted_of_lineFiberCoverChoose
#print axioms zeroSupportRatioHeavyCoordinateFiberBudgeted_of_lineFiberCoverChoose_n
#print axioms ZeroSupportRatioCoverSumBudgeted
#print axioms ZeroLowSupportRatioCoverSumBudgeted
#print axioms zeroSupportRatioHeavyBudgeted_of_coverSumBudgeted
#print axioms UniformLargeZeroSafeSupportRatioCoverSumBudgeted
#print axioms UniformLargeZeroSafeLowSupportRatioHeavyCoordinateFiberBudgeted
#print axioms UniformLargeZeroSafeLowSupportRatioCoverSumBudgeted
#print axioms zeroSupportRatioCoverSumBudgeted_of_lineFiberCoverChoose
#print axioms zeroSupportRatioCoverSumBudgeted_of_lineFiberCoverChoose_n
#print axioms uniformLargeZeroSafeSupportRatioCoverSumBudgeted_of_lineFiberCoverChoose_n
#print axioms zeroSupportRatioHeavyCoordinateFiberBudgeted_of_low_and_high_one
#print axioms
  uniformLargeZeroSafeSupportRatioHeavyCoordinateFiberBudgeted_of_low_and_high_one
#print axioms zeroSupportRatioCoverSumBudgeted_of_low_and_high_choose
#print axioms
  uniformLargeZeroSafeSupportRatioCoverSumBudgeted_of_low_and_high_choose
#print axioms not_zeroSupportRatioCoverSumBudgeted_iff_exists_coverSum_gt
#print axioms
  not_uniformLargeZeroSafeSupportRatioCoverSumBudgeted_iff_exists_coverSum_gt
#print axioms not_zeroLowSupportRatioCoverSumBudgeted_iff_exists_low_coverSum_gt
#print axioms
  not_uniformLargeZeroSafeLowSupportRatioCoverSumBudgeted_iff_exists_low_coverSum_gt
#print axioms not_zeroLowSupportRatioHeavyBudgeted_iff_exists_low_fiber_gt
#print axioms
  not_uniformLargeZeroSafeLowSupportRatioHeavyBudgeted_iff_exists_low_fiber_gt
#print axioms uniformSupportRatioHeavyBudgeted_of_coverSumBudgeted
#print axioms
  zeroExactAppearingZeroAgreementFiberBudgeted_of_supportRatioHeavyCoordinateFiberBudgeted
#print axioms
  uniformExactAppearingZeroAgreementFiberBudgeted_of_supportRatioHeavyCoordinateFiberBudgeted
#print axioms
  uniformLargeZeroSafeSupportRatioHeavyCoordinateFiberBudgeted_of_lineFiberCoverChoose_n
#print axioms uniformExactAppearingZeroAgreementFiberBudgeted_of_lineFiberCoverChoose_n
#print axioms
  uniformLineBadScalarsBudgeted_of_supportAdjustedBudgetFits_and_lineFiberCoverChoose_n
#print axioms uniformLineBadScalarsBudgeted_of_lowSupportRatioHeavyCoordFibers
#print axioms exists_largeZero_safe_low_supportRatioHeavyCoordFiber_gt_of_not_budgeted
#print axioms not_lineFiberCoverChooseBudgetFits_of_not_uniformLineBadScalarsBudgeted
#print axioms lineFiberCoverChooseBudgetFits_term_le
#print axioms not_lineFiberCoverChooseBudgetFits_of_exists_term_gt
#print axioms
  exists_lineFiberCoverChooseBudgetSum_gt_of_not_uniformLineBadScalarsBudgeted
#print axioms uniformLineBadScalarsBudgeted_of_supportRatioCoverSums
#print axioms uniformLineBadScalarsBudgeted_of_lowSupportRatioCoverSums
#print axioms
  exists_largeZero_safe_low_supportRatioCoverSum_gt_of_not_uniformLineBadScalarsBudgeted
#print axioms
  uniformLineBadScalarsBudgeted_of_supportAdjustedBudgetFits_and_coverSum_lineFiberCoverChoose_n
#print axioms
  exists_largeZero_safe_supportRatioHeavyCoordFiber_gt_of_not_uniformLineBadScalarsBudgeted
#print axioms
  exists_largeZero_safe_supportRatioCoverSum_gt_of_not_uniformLineBadScalarsBudgeted
#print axioms
  unsafe_or_largeZero_safe_supportRatioHeavyCoordFiber_gt_of_not_uniformLineBadScalarsBudgeted
#print axioms
  unsafe_or_largeZero_safe_supportRatioCoverSum_gt_of_not_uniformLineBadScalarsBudgeted
#print axioms
  exists_low_supportRatioCoverSum_gt_of_exists_coverSum_gt_and_high_choose
#print axioms
  unsafe_or_largeZero_safe_low_supportRatioCoverSum_gt_of_not_uniformLineBadScalarsBudgeted
#print axioms
  exists_low_supportRatioHeavyCoordinateFiber_gt_of_exists_fiber_gt_and_high_one
#print axioms
  unsafe_or_largeZero_safe_low_supportRatioHeavyCoordFiber_gt_of_not_uniformLineBadScalarsBudgeted

end SourceAudit

end ProximityGap.Ownership
