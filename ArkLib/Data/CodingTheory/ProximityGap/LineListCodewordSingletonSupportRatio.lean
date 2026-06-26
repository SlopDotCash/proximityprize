/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LineListSingletonDefectGeometry

/-!
# Codeword-indexed support-ratio covers for singleton witnesses

`LineListIncidenceMultiplicity.lean` isolates singleton bad scalars by their unique witnessing
codeword.  This file attaches the support-ratio geometry to one fixed codeword: every singleton
scalar has a large support-ratio fiber, hence admits finite subfibers of size
`a - #zeroAgreement(c)`.

The point is not yet a floor proof.  It creates the exact finite object needed by the next
overlap-multiplicity attempt: pairs `(γ, T)` where `γ` is uniquely witnessed by `c` and `T` is a
large moving-support subfiber for that same scalar.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- For one codeword `c`, the finite support-ratio subfiber cover of its singleton-witness
scalars.  A point is a scalar `γ` uniquely witnessed by `c` together with an
`(a - #zeroAgreement(c))`-subset of the moving coordinates whose support-ratio value is `γ`. -/
noncomputable def codewordSingletonSupportRatioCover
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ c : Fin n → F) :
    Finset (F × Finset (Fin n)) :=
  (Finset.univ : Finset (F × Finset (Fin n))).filter
    (fun e => e.1 ∈ codewordSingletonWitnessScalars dom k a u₀ u₁ c ∧
      e.2 ∈ (supportRatioFiber c u₀ u₁ e.1).powersetCard
        (a - (directionZeroAgreementSet c u₀ u₁).card))

open Classical in
theorem mem_codewordSingletonSupportRatioCover
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ c : Fin n → F)
    (e : F × Finset (Fin n)) :
    e ∈ codewordSingletonSupportRatioCover dom k a u₀ u₁ c ↔
      e.1 ∈ codewordSingletonWitnessScalars dom k a u₀ u₁ c ∧
        e.2 ∈ (supportRatioFiber c u₀ u₁ e.1).powersetCard
          (a - (directionZeroAgreementSet c u₀ u₁).card) := by
  rw [codewordSingletonSupportRatioCover, Finset.mem_filter]
  simp

open Classical in
/-- A singleton-witness scalar has enough support-ratio mass to choose the required moving
subfiber. -/
theorem supportRatioFiber_card_ge_sub_of_mem_codewordSingletonWitnessScalars
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ c : Fin n → F) {γ : F}
    (hγ : γ ∈ codewordSingletonWitnessScalars dom k a u₀ u₁ c) :
    a - (directionZeroAgreementSet c u₀ u₁).card
      ≤ (supportRatioFiber c u₀ u₁ γ).card := by
  have hheavy :
      γ ∈ codewordHeavyScalars (F := F) (n := n) a c u₀ u₁ :=
    codewordSingletonWitnessScalars_subset_codewordHeavyScalars dom k a u₀ u₁ c hγ
  rw [mem_codewordHeavyScalars] at hheavy
  have hcard := agreeSet_line_card_le_zeroAgreement_add_supportRatioFiber c u₀ u₁ γ
  omega

open Classical in
/-- Every singleton-witness scalar has at least one point in the codeword-indexed support-ratio
cover. -/
theorem exists_mem_codewordSingletonSupportRatioCover_of_mem_singletonWitness
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ c : Fin n → F) {γ : F}
    (hγ : γ ∈ codewordSingletonWitnessScalars dom k a u₀ u₁ c) :
    ∃ T : Finset (Fin n),
      T ∈ (supportRatioFiber c u₀ u₁ γ).powersetCard
        (a - (directionZeroAgreementSet c u₀ u₁).card) ∧
        (γ, T) ∈ codewordSingletonSupportRatioCover dom k a u₀ u₁ c := by
  obtain ⟨T, hTsub, hTcard⟩ :=
    Finset.exists_subset_card_eq
      (supportRatioFiber_card_ge_sub_of_mem_codewordSingletonWitnessScalars
        dom k a u₀ u₁ c hγ)
  have hTmem :
      T ∈ (supportRatioFiber c u₀ u₁ γ).powersetCard
        (a - (directionZeroAgreementSet c u₀ u₁).card) :=
    Finset.mem_powersetCard.mpr ⟨hTsub, hTcard⟩
  refine ⟨T, hTmem, ?_⟩
  rw [mem_codewordSingletonSupportRatioCover]
  exact ⟨hγ, hTmem⟩

open Classical in
/-- The first projection of the codeword-indexed support-ratio cover is exactly the singleton
scalar fiber of that codeword. -/
theorem codewordSingletonWitnessScalars_eq_image_fst_supportRatioCover
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ c : Fin n → F) :
    codewordSingletonWitnessScalars dom k a u₀ u₁ c =
      (codewordSingletonSupportRatioCover dom k a u₀ u₁ c).image Prod.fst := by
  ext γ
  constructor
  · intro hγ
    rcases exists_mem_codewordSingletonSupportRatioCover_of_mem_singletonWitness
        dom k a u₀ u₁ c hγ with
      ⟨T, _hT, hpair⟩
    exact Finset.mem_image.mpr ⟨(γ, T), hpair, rfl⟩
  · intro hγ
    rcases Finset.mem_image.mp hγ with ⟨⟨γ', T⟩, hpair, hfst⟩
    dsimp at hfst
    subst γ'
    exact (mem_codewordSingletonSupportRatioCover dom k a u₀ u₁ c (γ, T)).mp hpair |>.1

open Classical in
/-- The codeword-indexed support-ratio cover cardinally dominates the singleton scalar fiber. -/
theorem codewordSingletonWitnessScalars_card_le_supportRatioCover_card
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ c : Fin n → F) :
    (codewordSingletonWitnessScalars dom k a u₀ u₁ c).card
      ≤ (codewordSingletonSupportRatioCover dom k a u₀ u₁ c).card := by
  rw [codewordSingletonWitnessScalars_eq_image_fst_supportRatioCover]
  exact Finset.card_image_le

open Classical in
/-- The fiber of the support-ratio cover over a singleton scalar is exactly the collection of
eligible support-ratio subfibers for that scalar. -/
theorem codewordSingletonSupportRatioCover_fst_fiber_eq
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ c : Fin n → F) {γ : F}
    (hγ : γ ∈ codewordSingletonWitnessScalars dom k a u₀ u₁ c) :
    (codewordSingletonSupportRatioCover dom k a u₀ u₁ c).filter (fun e => e.1 = γ) =
      ((supportRatioFiber c u₀ u₁ γ).powersetCard
        (a - (directionZeroAgreementSet c u₀ u₁).card)).image (fun T => (γ, T)) := by
  ext e
  rcases e with ⟨γ', T⟩
  constructor
  · intro he
    rw [Finset.mem_filter] at he
    have hγ' : γ' = γ := he.2
    subst γ'
    have hcover :=
      (mem_codewordSingletonSupportRatioCover dom k a u₀ u₁ c (γ, T)).mp he.1
    exact Finset.mem_image.mpr ⟨T, hcover.2, rfl⟩
  · intro he
    rcases Finset.mem_image.mp he with ⟨T', hT', hpair⟩
    cases hpair
    rw [Finset.mem_filter]
    refine ⟨?_, rfl⟩
    rw [mem_codewordSingletonSupportRatioCover]
    exact ⟨hγ, hT'⟩

open Classical in
/-- Cardinality of one scalar fiber of the codeword-indexed support-ratio cover. -/
theorem codewordSingletonSupportRatioCover_fst_fiber_card_eq_choose
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ c : Fin n → F) {γ : F}
    (hγ : γ ∈ codewordSingletonWitnessScalars dom k a u₀ u₁ c) :
    ((codewordSingletonSupportRatioCover dom k a u₀ u₁ c).filter (fun e => e.1 = γ)).card =
      (supportRatioFiber c u₀ u₁ γ).card.choose
        (a - (directionZeroAgreementSet c u₀ u₁).card) := by
  calc
    ((codewordSingletonSupportRatioCover dom k a u₀ u₁ c).filter
        (fun e => e.1 = γ)).card
        = (((supportRatioFiber c u₀ u₁ γ).powersetCard
            (a - (directionZeroAgreementSet c u₀ u₁).card)).image
              (fun T => (γ, T))).card := by
          rw [codewordSingletonSupportRatioCover_fst_fiber_eq dom k a u₀ u₁ c hγ]
    _ = ((supportRatioFiber c u₀ u₁ γ).powersetCard
            (a - (directionZeroAgreementSet c u₀ u₁).card)).card := by
          exact Finset.card_image_of_injOn
            (fun _T _hT _T' _hT' h => by simpa using congrArg Prod.snd h)
    _ = (supportRatioFiber c u₀ u₁ γ).card.choose
          (a - (directionZeroAgreementSet c u₀ u₁).card) := by
          rw [Finset.card_powersetCard]

open Classical in
/-- Exact decomposition of the codeword-indexed support-ratio cover by singleton scalar. -/
theorem codewordSingletonSupportRatioCover_card_eq_sum_choose
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ c : Fin n → F) :
    (codewordSingletonSupportRatioCover dom k a u₀ u₁ c).card =
      ∑ γ ∈ codewordSingletonWitnessScalars dom k a u₀ u₁ c,
        (supportRatioFiber c u₀ u₁ γ).card.choose
          (a - (directionZeroAgreementSet c u₀ u₁).card) := by
  let C := codewordSingletonSupportRatioCover dom k a u₀ u₁ c
  let S := codewordSingletonWitnessScalars dom k a u₀ u₁ c
  have hmaps : ∀ e ∈ C, e.1 ∈ S := by
    intro e he
    change e ∈ codewordSingletonSupportRatioCover dom k a u₀ u₁ c at he
    exact (mem_codewordSingletonSupportRatioCover dom k a u₀ u₁ c e).mp he |>.1
  calc
    C.card = ∑ γ ∈ S, (C.filter fun e => e.1 = γ).card :=
      Finset.card_eq_sum_card_fiberwise hmaps
    _ = ∑ γ ∈ codewordSingletonWitnessScalars dom k a u₀ u₁ c,
          (supportRatioFiber c u₀ u₁ γ).card.choose
            (a - (directionZeroAgreementSet c u₀ u₁).card) := by
        refine Finset.sum_congr rfl ?_
        intro γ hγ
        exact codewordSingletonSupportRatioCover_fst_fiber_card_eq_choose
          dom k a u₀ u₁ c (by simpa [S] using hγ)

/-- Uniform cap on the codeword-indexed support-ratio cover attached to every appearing codeword
on every large-zero safe line. -/
def UniformLargeZeroSafeCodewordSingletonSupportRatioCoverBudgeted
    (dom : Fin n ↪ F) (k a S : ℕ) : Prop :=
  ∀ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
    ZeroDirectionSafeLine dom k a u₀ u₁ →
      ∀ c ∈ lineAppearingCodewords dom k a u₀ u₁,
        (codewordSingletonSupportRatioCover dom k a u₀ u₁ c).card ≤ S

/-- A support-ratio cover cap implies the direct singleton-witness scalar cap for each appearing
codeword. -/
theorem uniformLargeZeroSafeCodewordSingletonBudgeted_of_supportRatioCoverBudgeted
    (dom : Fin n ↪ F) (k a S : ℕ)
    (hcover :
      UniformLargeZeroSafeCodewordSingletonSupportRatioCoverBudgeted dom k a S) :
    UniformLargeZeroSafeCodewordSingletonBudgeted dom k a S := by
  intro u₀ u₁ hnotEligible hsafe c hc
  exact le_trans
    (codewordSingletonWitnessScalars_card_le_supportRatioCover_card dom k a u₀ u₁ c)
    (hcover u₀ u₁ hnotEligible hsafe c hc)

open Classical in
/-- Exact failure form for the codeword-indexed support-ratio cover cap. -/
theorem not_uniformLargeZeroSafeCodewordSingletonSupportRatioCoverBudgeted_iff_exists_cover_gt
    (dom : Fin n ↪ F) (k a S : ℕ) :
    (¬ UniformLargeZeroSafeCodewordSingletonSupportRatioCoverBudgeted dom k a S) ↔
      ∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
        ZeroDirectionSafeLine dom k a u₀ u₁ ∧
          ∃ c ∈ lineAppearingCodewords dom k a u₀ u₁,
            S < (codewordSingletonSupportRatioCover dom k a u₀ u₁ c).card := by
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro u₀ u₁ hnotEligible hsafe c hc
    exact le_of_not_gt
      (fun hgt => hnone ⟨u₀, u₁, hnotEligible, hsafe, c, hc, hgt⟩)
  · rintro ⟨u₀, u₁, hnotEligible, hsafe, c, hc, hgt⟩ hbudget
    exact (not_lt_of_ge (hbudget u₀ u₁ hnotEligible hsafe c hc)) hgt

open Classical in
/-- If the direct singleton cap fails, then the codeword-indexed support-ratio cover is already
overfull for a concrete appearing codeword. -/
theorem
    exists_largeZero_safe_codewordSupportRatioCover_gt_of_not_codewordSingletonBudgeted
    (dom : Fin n ↪ F) (k a S : ℕ)
    (hnot : ¬ UniformLargeZeroSafeCodewordSingletonBudgeted dom k a S) :
    ∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
      ZeroDirectionSafeLine dom k a u₀ u₁ ∧
        ∃ c ∈ lineAppearingCodewords dom k a u₀ u₁,
          S < (codewordSingletonSupportRatioCover dom k a u₀ u₁ c).card := by
  rcases
      (not_uniformLargeZeroSafeCodewordSingletonBudgeted_iff_exists_card_gt
        dom k a S).mp hnot with
    ⟨u₀, u₁, hnotEligible, hsafe, c, hc, hgt⟩
  exact ⟨u₀, u₁, hnotEligible, hsafe, c, hc,
    lt_of_lt_of_le hgt
      (codewordSingletonWitnessScalars_card_le_supportRatioCover_card
        dom k a u₀ u₁ c)⟩

/-- The codeword-indexed support-ratio cover cap can be consumed by the direct per-codeword
singleton production route. -/
theorem largeZeroSafeLineBadScalarsBudgeted_of_codewordSingletonSupportRatioCoverBudget
    (dom : Fin n ↪ F) (k a S B : ℕ)
    (hcover :
      UniformLargeZeroSafeCodewordSingletonSupportRatioCoverBudgeted dom k a S)
    (hbudget : UniformLargeZeroSafeWeightPlusCodewordSingletonBudgeted dom k a B S) :
    LargeZeroSafeLineBadScalarsBudgeted dom k a B :=
  largeZeroSafeLineBadScalarsBudgeted_of_codewordSingletonBudget dom k a S B
    (uniformLargeZeroSafeCodewordSingletonBudgeted_of_supportRatioCoverBudgeted
      dom k a S hcover)
    hbudget

/-- Production wrapper for the support-ratio cover route to per-codeword singleton caps. -/
theorem
    uniformLineBadScalarsBudgeted_of_supportAdjusted_and_codewordSupportRatioCoverBudget
    (dom : Fin n ↪ F) (k a L S B : ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hcover :
      UniformLargeZeroSafeCodewordSingletonSupportRatioCoverBudgeted dom k a S)
    (hbudget : UniformLargeZeroSafeWeightPlusCodewordSingletonBudgeted dom k a B S) :
    UniformLineBadScalarsBudgeted dom k a B :=
  uniformLineBadScalarsBudgeted_of_supportAdjusted_and_codewordSingletonBudget
    dom k a L S B hSupport hFits hZeroSafe
    (uniformLargeZeroSafeCodewordSingletonBudgeted_of_supportRatioCoverBudgeted
      dom k a S hcover)
    hbudget

open Classical in
/-- Scanner for the support-ratio cover route.  Once support-side hypotheses are fixed, failed
production forces either the usual appearing-codeword arithmetic failure or an overfull
codeword-indexed support-ratio cover for a concrete appearing codeword. -/
theorem
    exists_largeZero_safe_codewordSupportRatioCoverRouteFailure_of_not_budgeted
    (dom : Fin n ↪ F) (k a L S B : ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hnot : ¬ UniformLineBadScalarsBudgeted dom k a B) :
    ∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
      ZeroDirectionSafeLine dom k a u₀ u₁ ∧
        (¬ puncturedZeroStratifiedLineWeight dom k a u₀ u₁
            + (lineAppearingCodewords dom k a u₀ u₁).card * S ≤ 2 * B ∨
          ∃ c ∈ lineAppearingCodewords dom k a u₀ u₁,
            S < (codewordSingletonSupportRatioCover dom k a u₀ u₁ c).card) := by
  by_cases hcover :
      UniformLargeZeroSafeCodewordSingletonSupportRatioCoverBudgeted dom k a S
  · have hperCode :
        UniformLargeZeroSafeCodewordSingletonBudgeted dom k a S :=
      uniformLargeZeroSafeCodewordSingletonBudgeted_of_supportRatioCoverBudgeted
        dom k a S hcover
    rcases
      exists_largeZero_safe_codewordSingletonBudgetFailure_of_not_uniformLineBadScalarsBudgeted
        dom k a L S B hSupport hFits hZeroSafe hperCode hnot with
      ⟨u₀, u₁, hnotEligible, hsafe, hfail⟩
    exact ⟨u₀, u₁, hnotEligible, hsafe, Or.inl hfail⟩
  · rcases
      (not_uniformLargeZeroSafeCodewordSingletonSupportRatioCoverBudgeted_iff_exists_cover_gt
        dom k a S).mp hcover with
      ⟨u₀, u₁, hnotEligible, hsafe, c, hc, hgt⟩
    exact ⟨u₀, u₁, hnotEligible, hsafe, Or.inr ⟨c, hc, hgt⟩⟩

section SourceAudit

#print axioms codewordSingletonSupportRatioCover
#print axioms mem_codewordSingletonSupportRatioCover
#print axioms supportRatioFiber_card_ge_sub_of_mem_codewordSingletonWitnessScalars
#print axioms exists_mem_codewordSingletonSupportRatioCover_of_mem_singletonWitness
#print axioms codewordSingletonWitnessScalars_eq_image_fst_supportRatioCover
#print axioms codewordSingletonWitnessScalars_card_le_supportRatioCover_card
#print axioms codewordSingletonSupportRatioCover_fst_fiber_eq
#print axioms codewordSingletonSupportRatioCover_fst_fiber_card_eq_choose
#print axioms codewordSingletonSupportRatioCover_card_eq_sum_choose
#print axioms UniformLargeZeroSafeCodewordSingletonSupportRatioCoverBudgeted
#print axioms uniformLargeZeroSafeCodewordSingletonBudgeted_of_supportRatioCoverBudgeted
#print axioms
  not_uniformLargeZeroSafeCodewordSingletonSupportRatioCoverBudgeted_iff_exists_cover_gt
#print axioms
  exists_largeZero_safe_codewordSupportRatioCover_gt_of_not_codewordSingletonBudgeted
#print axioms largeZeroSafeLineBadScalarsBudgeted_of_codewordSingletonSupportRatioCoverBudget
#print axioms
  uniformLineBadScalarsBudgeted_of_supportAdjusted_and_codewordSupportRatioCoverBudget
#print axioms
  exists_largeZero_safe_codewordSupportRatioCoverRouteFailure_of_not_budgeted

end SourceAudit

end ProximityGap.Ownership
