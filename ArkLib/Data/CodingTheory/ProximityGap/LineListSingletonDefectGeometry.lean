/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LineListIncidenceMultiplicity
import ArkLib.Data.CodingTheory.ProximityGap.LineListAppearanceFiber

/-!
# Geometry of singleton witness defects

`LineListIncidenceMultiplicity.lean` isolates the additive obstruction to a factor-two
multiplicity discount: bad scalars with a singleton witness-codeword fiber.  This file turns that
defect into a filtered incidence graph and localizes it by exact zero-direction agreement sets.

The main local inequality says that singleton incidences whose unique witness lies in a fixed
exact zero-agreement fiber are bounded by that exact fiber size times the usual per-codeword
heavy-scalar denominator.  This is not a floor proof; it is the bridge needed to attack the
singleton defect by exact-fiber or ownership-profile estimates.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Finset

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- Incidences whose scalar lies in the singleton bad-scalar defect. -/
noncomputable def singletonBadScalarIncidences
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) :
    Finset (F × (Fin n → F)) :=
  (lineHeavyIncidences dom k a u₀ u₁).filter
    (fun e => e.1 ∈ singletonBadScalars dom k a u₀ u₁)

theorem mem_singletonBadScalarIncidences
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F)
    (e : F × (Fin n → F)) :
    e ∈ singletonBadScalarIncidences dom k a u₀ u₁ ↔
      e ∈ lineHeavyIncidences dom k a u₀ u₁ ∧
        e.1 ∈ singletonBadScalars dom k a u₀ u₁ := by
  classical
  rw [singletonBadScalarIncidences, Finset.mem_filter]

theorem singletonBadScalarIncidences_subset_lineHeavyIncidences
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) :
    singletonBadScalarIncidences dom k a u₀ u₁ ⊆
      lineHeavyIncidences dom k a u₀ u₁ := by
  intro e he
  exact ((mem_singletonBadScalarIncidences dom k a u₀ u₁ e).mp he).1

open Classical in
/-- The singleton-defect incidence graph has exactly one incidence over each singleton bad
scalar. -/
theorem singletonBadScalarIncidences_card_eq_singletonBadScalarDefect
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) :
    (singletonBadScalarIncidences dom k a u₀ u₁).card =
      singletonBadScalarDefect dom k a u₀ u₁ := by
  let I := singletonBadScalarIncidences dom k a u₀ u₁
  let S := singletonBadScalars dom k a u₀ u₁
  have hmaps : ∀ e ∈ I, e.1 ∈ S := by
    intro e he
    have he' := (mem_singletonBadScalarIncidences dom k a u₀ u₁ e).mp he
    simpa [S] using he'.2
  calc
    I.card = ∑ γ ∈ S, (I.filter fun e => e.1 = γ).card :=
      Finset.card_eq_sum_card_fiberwise hmaps
    _ = ∑ γ ∈ S, (badScalarWitnessCodewords dom k a u₀ u₁ γ).card := by
        refine Finset.sum_congr rfl ?_
        intro γ hγ
        have hfiber :
            I.filter (fun e => e.1 = γ) =
              (lineHeavyIncidences dom k a u₀ u₁).filter (fun e => e.1 = γ) := by
          ext e
          constructor
          · intro he
            rw [Finset.mem_filter] at he
            rw [Finset.mem_filter]
            exact ⟨((mem_singletonBadScalarIncidences dom k a u₀ u₁ e).mp he.1).1, he.2⟩
          · intro he
            rw [Finset.mem_filter] at he
            rw [Finset.mem_filter]
            refine ⟨?_, he.2⟩
            rw [mem_singletonBadScalarIncidences]
            refine ⟨he.1, ?_⟩
            simpa [he.2, S] using hγ
        rw [hfiber]
        exact lineHeavyIncidences_fst_fiber_card_eq_badScalarWitnessCodewords_card
          dom k a u₀ u₁ γ
    _ = ∑ _γ ∈ S, 1 := by
        refine Finset.sum_congr rfl ?_
        intro γ hγ
        exact ((mem_singletonBadScalars dom k a u₀ u₁ γ).mp (by simpa [S] using hγ)).2
    _ = singletonBadScalarDefect dom k a u₀ u₁ := by
        rw [singletonBadScalarDefect]
        simp [S]

open Classical in
/-- The singleton defect is bounded by the full incidence count. -/
theorem singletonBadScalarDefect_le_lineHeavyIncidences_card
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) :
    singletonBadScalarDefect dom k a u₀ u₁
      ≤ (lineHeavyIncidences dom k a u₀ u₁).card := by
  rw [← singletonBadScalarIncidences_card_eq_singletonBadScalarDefect]
  exact Finset.card_le_card
    (singletonBadScalarIncidences_subset_lineHeavyIncidences dom k a u₀ u₁)

open Classical in
/-- Safe lines bound the singleton defect by the punctured zero-stratified line weight. -/
theorem singletonBadScalarDefect_le_puncturedZeroStratifiedLineWeight
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F)
    (hsafe : ZeroDirectionSafeLine dom k a u₀ u₁) :
    singletonBadScalarDefect dom k a u₀ u₁
      ≤ puncturedZeroStratifiedLineWeight dom k a u₀ u₁ :=
  le_trans
    (singletonBadScalarDefect_le_lineHeavyIncidences_card dom k a u₀ u₁)
    (lineHeavyIncidences_card_le_puncturedZeroStratifiedLineWeight
      dom k a u₀ u₁ hsafe)

open Classical in
/-- Singleton-defect incidences whose witness codeword has exact zero-direction agreement set
`S`. -/
noncomputable def singletonBadScalarIncidencesInExactZeroAgreementFiber
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (S : Finset (Fin n)) :
    Finset (F × (Fin n → F)) :=
  (singletonBadScalarIncidences dom k a u₀ u₁).filter
    (fun e => directionZeroAgreementSet e.2 u₀ u₁ = S)

theorem mem_singletonBadScalarIncidencesInExactZeroAgreementFiber
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (S : Finset (Fin n))
    (e : F × (Fin n → F)) :
    e ∈ singletonBadScalarIncidencesInExactZeroAgreementFiber dom k a u₀ u₁ S ↔
      e ∈ singletonBadScalarIncidences dom k a u₀ u₁ ∧
        directionZeroAgreementSet e.2 u₀ u₁ = S := by
  classical
  rw [singletonBadScalarIncidencesInExactZeroAgreementFiber, Finset.mem_filter]

open Classical in
/-- Distinct exact zero-agreement profiles have disjoint singleton-defect incidence slices. -/
theorem disjoint_singletonBadScalarIncidencesInExactZeroAgreementFiber_of_ne
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F)
    {S T : Finset (Fin n)} (hne : S ≠ T) :
    Disjoint
      (singletonBadScalarIncidencesInExactZeroAgreementFiber dom k a u₀ u₁ S)
      (singletonBadScalarIncidencesInExactZeroAgreementFiber dom k a u₀ u₁ T) := by
  rw [Finset.disjoint_left]
  intro e heS heT
  have hS :=
    (mem_singletonBadScalarIncidencesInExactZeroAgreementFiber dom k a u₀ u₁ S e).mp heS
  have hT :=
    (mem_singletonBadScalarIncidencesInExactZeroAgreementFiber dom k a u₀ u₁ T e).mp heT
  exact hne (hS.2.symm.trans hT.2)

open Classical in
/-- Projecting an exact singleton-defect incidence to its codeword lands in the exact appearance
fiber over the same zero-direction agreement set. -/
theorem snd_mem_exactAppearingZeroAgreementFiber_of_mem_singletonBadScalarIncidencesInExact
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (S : Finset (Fin n))
    {e : F × (Fin n → F)}
    (he : e ∈ singletonBadScalarIncidencesInExactZeroAgreementFiber dom k a u₀ u₁ S) :
    e.2 ∈ exactAppearingZeroAgreementFiber dom k a u₀ u₁ S := by
  rw [mem_exactAppearingZeroAgreementFiber]
  have heExact :=
    (mem_singletonBadScalarIncidencesInExactZeroAgreementFiber dom k a u₀ u₁ S e).mp he
  have heSingleton :=
    (mem_singletonBadScalarIncidences dom k a u₀ u₁ e).mp heExact.1
  have hLine : e ∈ lineHeavyIncidences dom k a u₀ u₁ := heSingleton.1
  rw [lineHeavyIncidences, Finset.mem_filter] at hLine
  refine ⟨?_, heExact.2⟩
  rw [lineAppearingCodewords, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, hLine.2.1, e.1, hLine.2.2⟩

open Classical in
/-- Fixed-profile singleton-defect incidences are bounded by the corresponding exact appearance
fiber times the usual per-codeword heavy-scalar denominator. -/
theorem singletonBadScalarIncidencesInExact_card_le_exactFiber_card_mul_support_div
    (dom : Fin n ↪ F) (k a : ℕ)
    (u₀ u₁ : Fin n → F) {S : Finset (Fin n)} {t : ℕ}
    (hsafe : ZeroDirectionSafeLine dom k a u₀ u₁)
    (hS : S ∈ (directionZeroSet u₁).powersetCard t) :
    (singletonBadScalarIncidencesInExactZeroAgreementFiber dom k a u₀ u₁ S).card
      ≤ (exactAppearingZeroAgreementFiber dom k a u₀ u₁ S).card *
        ((directionSupportSet u₁).card / (a - t)) := by
  let I := singletonBadScalarIncidencesInExactZeroAgreementFiber dom k a u₀ u₁ S
  let E := exactAppearingZeroAgreementFiber dom k a u₀ u₁ S
  have hmaps : ∀ e ∈ I, e.2 ∈ E := by
    intro e he
    exact snd_mem_exactAppearingZeroAgreementFiber_of_mem_singletonBadScalarIncidencesInExact
      dom k a u₀ u₁ S (by simpa [I] using he)
  calc
    I.card = ∑ c ∈ E, (I.filter fun e => e.2 = c).card :=
      Finset.card_eq_sum_card_fiberwise hmaps
    _ ≤ ∑ _c ∈ E, ((directionSupportSet u₁).card / (a - t)) := by
        refine Finset.sum_le_sum ?_
        intro c hcE
        have hcExact : c ∈ exactAppearingZeroAgreementFiber dom k a u₀ u₁ S := by
          simpa [E] using hcE
        have hcApp := (mem_exactAppearingZeroAgreementFiber dom k a u₀ u₁ c S).mp hcExact
        have hcCode : c ∈ (rsCode dom k : Submodule F (Fin n → F)) := by
          rw [lineAppearingCodewords, Finset.mem_filter] at hcApp
          exact hcApp.1.2.1
        have hlineFiber :
            (I.filter fun e => e.2 = c).card
              ≤ ((lineHeavyIncidences dom k a u₀ u₁).filter fun e => e.2 = c).card := by
          exact Finset.card_le_card (by
            intro e he
            rw [Finset.mem_filter] at he
            rw [Finset.mem_filter]
            refine ⟨?_, he.2⟩
            have heI : e ∈ singletonBadScalarIncidencesInExactZeroAgreementFiber
                dom k a u₀ u₁ S := by
              simpa [I] using he.1
            have heSingleton :=
              (mem_singletonBadScalarIncidencesInExactZeroAgreementFiber
                dom k a u₀ u₁ S e).mp heI |>.1
            exact (mem_singletonBadScalarIncidences dom k a u₀ u₁ e).mp heSingleton |>.1)
        have hheavy :
            ((lineHeavyIncidences dom k a u₀ u₁).filter fun e => e.2 = c).card
              = (codewordHeavyScalars (F := F) (n := n) a c u₀ u₁).card :=
          lineHeavyIncidences_snd_fiber_card_eq_codewordHeavyScalars_card
            dom k a u₀ u₁ c hcCode
        have hden :
            (directionSupportSet u₁).card /
                (a - (directionZeroAgreementSet c u₀ u₁).card)
              = (directionSupportSet u₁).card / (a - t) := by
          have hScard : S.card = t := (Finset.mem_powersetCard.mp hS).2
          rw [hcApp.2, hScard]
        exact le_trans hlineFiber
          (by
            rw [hheavy]
            exact le_trans
              (codeword_heavy_scalar_card_le_support_div_sub_zeroAgreement
                (F := F) (n := n) a c u₀ u₁ (hsafe c hcCode))
              (le_of_eq hden))
    _ = E.card * ((directionSupportSet u₁).card / (a - t)) := by
        rw [Finset.sum_const, smul_eq_mul]

/-- Per-line profile budget for singleton-defect exact zero-agreement slices.  `D t` bounds the
number of singleton-defect incidences whose unique witness has exact zero-direction agreement set
of size `t`. -/
def ZeroExactSingletonDefectProfileBudgeted
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (D : ℕ → ℕ) : Prop :=
  ∀ t : ℕ, t < a → ∀ S ∈ (directionZeroSet u₁).powersetCard t,
    (singletonBadScalarIncidencesInExactZeroAgreementFiber dom k a u₀ u₁ S).card ≤ D t

/-- Arithmetic fit for a singleton-defect exact-profile budget. -/
def ZeroExactSingletonDefectProfileBudgetFits
    (a B : ℕ) (u₁ : Fin n → F) (D : ℕ → ℕ) : Prop :=
  ∑ t ∈ Finset.range a, (directionZeroSet u₁).card.choose t * D t ≤ B

/-- Uniform singleton-defect exact-profile budget on the large-zero safe branch. -/
def UniformLargeZeroSafeExactSingletonDefectProfileBudgeted
    (dom : Fin n ↪ F) (k a : ℕ) (D : ℕ → ℕ) : Prop :=
  ∀ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
    ZeroDirectionSafeLine dom k a u₀ u₁ →
      ZeroExactSingletonDefectProfileBudgeted dom k a u₀ u₁ D

/-- Uniform combined arithmetic budget for punctured weight plus a singleton-defect exact-profile
envelope on the large-zero safe branch. -/
def UniformLargeZeroSafeWeightPlusExactSingletonProfileBudgeted
    (dom : Fin n ↪ F) (k a B : ℕ) (D : ℕ → ℕ) : Prop :=
  ∀ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
    ZeroDirectionSafeLine dom k a u₀ u₁ →
      puncturedZeroStratifiedLineWeight dom k a u₀ u₁
        + ∑ t ∈ Finset.range a, (directionZeroSet u₁).card.choose t * D t ≤ 2 * B

/-- Per-line exact-appearance-fiber budget strong enough for singleton-defect slices.  For each
exact zero-agreement profile of size `t`, the exact appearance fiber times the usual
moving-support denominator is bounded by `D t`. -/
def ZeroExactAppearanceFiberSingletonBudgeted
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (D : ℕ → ℕ) : Prop :=
  ∀ t : ℕ, t < a → ∀ S ∈ (directionZeroSet u₁).powersetCard t,
    (exactAppearingZeroAgreementFiber dom k a u₀ u₁ S).card *
      ((directionSupportSet u₁).card / (a - t)) ≤ D t

/-- Uniform exact-appearance-fiber budget for singleton-defect slices on the large-zero safe
branch. -/
def UniformLargeZeroSafeExactAppearanceFiberSingletonBudgeted
    (dom : Fin n ↪ F) (k a : ℕ) (D : ℕ → ℕ) : Prop :=
  ∀ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
    ZeroDirectionSafeLine dom k a u₀ u₁ →
      ZeroExactAppearanceFiberSingletonBudgeted dom k a u₀ u₁ D

open Classical in
/-- An exact appearance-fiber budget, after multiplying by the support denominator, gives the
singleton-defect profile budget. -/
theorem zeroExactSingletonDefectProfileBudgeted_of_exactAppearanceFiberSingletonBudgeted
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (D : ℕ → ℕ)
    (hsafe : ZeroDirectionSafeLine dom k a u₀ u₁)
    (hAppearance : ZeroExactAppearanceFiberSingletonBudgeted dom k a u₀ u₁ D) :
    ZeroExactSingletonDefectProfileBudgeted dom k a u₀ u₁ D := by
  intro t ht S hS
  exact le_trans
    (singletonBadScalarIncidencesInExact_card_le_exactFiber_card_mul_support_div
      dom k a u₀ u₁ hsafe hS)
    (hAppearance t ht S hS)

open Classical in
/-- Uniform version of the exact-appearance-fiber to singleton-profile bridge. -/
theorem uniformExactSingletonProfileBudgeted_of_exactAppearanceFiberSingletonBudgeted
    (dom : Fin n ↪ F) (k a : ℕ) (D : ℕ → ℕ)
    (hAppearance : UniformLargeZeroSafeExactAppearanceFiberSingletonBudgeted dom k a D) :
    UniformLargeZeroSafeExactSingletonDefectProfileBudgeted dom k a D := by
  intro u₀ u₁ hnotEligible hsafe
  exact zeroExactSingletonDefectProfileBudgeted_of_exactAppearanceFiberSingletonBudgeted
    dom k a u₀ u₁ D hsafe (hAppearance u₀ u₁ hnotEligible hsafe)

open Classical in
/-- Existing exact appearance-fiber caps imply the singleton-fiber cap once their moving-support
denominator arithmetic fits inside `D`. -/
theorem zeroExactAppearanceFiberSingletonBudgeted_of_exactAppearingZeroAgreementFiberBudgeted
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (M D : ℕ → ℕ)
    (hFiber : ZeroExactAppearingZeroAgreementFiberBudgeted dom k a u₀ u₁ M)
    (hMul : ∀ t : ℕ, t < a →
      M t * ((directionSupportSet u₁).card / (a - t)) ≤ D t) :
    ZeroExactAppearanceFiberSingletonBudgeted dom k a u₀ u₁ D := by
  intro t ht S hS
  exact le_trans
    (Nat.mul_le_mul_right ((directionSupportSet u₁).card / (a - t))
      (hFiber t ht S hS))
    (hMul t ht)

open Classical in
/-- Uniform exact appearance-fiber caps imply the singleton-fiber cap once their moving-support
denominator arithmetic fits uniformly. -/
theorem uniformExactAppearanceFiberSingletonBudgeted_of_exactAppearingFiberBudgeted
    (dom : Fin n ↪ F) (k a : ℕ) (M D : ℕ → ℕ)
    (hFiber : UniformLargeZeroSafeExactAppearingZeroAgreementFiberBudgeted dom k a M)
    (hMul : ∀ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
      ZeroDirectionSafeLine dom k a u₀ u₁ →
        ∀ t : ℕ, t < a →
          M t * ((directionSupportSet u₁).card / (a - t)) ≤ D t) :
    UniformLargeZeroSafeExactAppearanceFiberSingletonBudgeted dom k a D := by
  intro u₀ u₁ hnotEligible hsafe
  exact zeroExactAppearanceFiberSingletonBudgeted_of_exactAppearingZeroAgreementFiberBudgeted
    dom k a u₀ u₁ M D (hFiber u₀ u₁ hnotEligible hsafe)
    (hMul u₀ u₁ hnotEligible hsafe)

open Classical in
/-- On a zero-safe line, singleton-defect incidences are covered by their exact zero-agreement
profiles of size `t < a`. -/
theorem singletonBadScalarIncidences_subset_biUnion_exactProfiles
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F)
    (hsafe : ZeroDirectionSafeLine dom k a u₀ u₁) :
    singletonBadScalarIncidences dom k a u₀ u₁ ⊆
      (Finset.range a).biUnion
        (fun t => ((directionZeroSet u₁).powersetCard t).biUnion
          (fun S => singletonBadScalarIncidencesInExactZeroAgreementFiber
            dom k a u₀ u₁ S)) := by
  intro e he
  have hLine := ((mem_singletonBadScalarIncidences dom k a u₀ u₁ e).mp he).1
  rw [lineHeavyIncidences, Finset.mem_filter] at hLine
  let S : Finset (Fin n) := directionZeroAgreementSet e.2 u₀ u₁
  let t : ℕ := S.card
  have ht : t ∈ Finset.range a := by
    exact Finset.mem_range.mpr (by
      simpa [S, t] using hsafe e.2 hLine.2.1)
  have hSsub : S ⊆ directionZeroSet u₁ := by
    intro i hi
    change i ∈ directionZeroAgreementSet e.2 u₀ u₁ at hi
    rw [directionZeroAgreementSet, Finset.mem_filter] at hi
    exact hi.1
  have hS : S ∈ (directionZeroSet u₁).powersetCard t := by
    rw [Finset.mem_powersetCard]
    exact ⟨hSsub, rfl⟩
  refine Finset.mem_biUnion.mpr ⟨t, ht, ?_⟩
  refine Finset.mem_biUnion.mpr ⟨S, hS, ?_⟩
  rw [mem_singletonBadScalarIncidencesInExactZeroAgreementFiber]
  exact ⟨he, rfl⟩

open Classical in
/-- Singleton defect as bounded by the sum of exact-profile singleton-defect slices. -/
theorem singletonBadScalarDefect_le_sum_exactSingletonProfiles
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F)
    (hsafe : ZeroDirectionSafeLine dom k a u₀ u₁) :
    singletonBadScalarDefect dom k a u₀ u₁
      ≤ ∑ t ∈ Finset.range a,
        ∑ S ∈ (directionZeroSet u₁).powersetCard t,
          (singletonBadScalarIncidencesInExactZeroAgreementFiber dom k a u₀ u₁ S).card := by
  rw [← singletonBadScalarIncidences_card_eq_singletonBadScalarDefect]
  calc
    (singletonBadScalarIncidences dom k a u₀ u₁).card
        ≤ ((Finset.range a).biUnion
          (fun t => ((directionZeroSet u₁).powersetCard t).biUnion
            (fun S => singletonBadScalarIncidencesInExactZeroAgreementFiber
              dom k a u₀ u₁ S))).card :=
          Finset.card_le_card
            (singletonBadScalarIncidences_subset_biUnion_exactProfiles
              dom k a u₀ u₁ hsafe)
    _ ≤ ∑ t ∈ Finset.range a,
          (((directionZeroSet u₁).powersetCard t).biUnion
            (fun S => singletonBadScalarIncidencesInExactZeroAgreementFiber
              dom k a u₀ u₁ S)).card :=
          Finset.card_biUnion_le
    _ ≤ ∑ t ∈ Finset.range a,
          ∑ S ∈ (directionZeroSet u₁).powersetCard t,
            (singletonBadScalarIncidencesInExactZeroAgreementFiber dom k a u₀ u₁ S).card := by
        refine Finset.sum_le_sum ?_
        intro t _ht
        exact Finset.card_biUnion_le

open Classical in
/-- A profile-wise singleton-defect budget implies the summed binomial singleton-defect cap. -/
theorem singletonBadScalarDefect_le_of_exactSingletonProfileBudgeted
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (D : ℕ → ℕ)
    (hsafe : ZeroDirectionSafeLine dom k a u₀ u₁)
    (hProfile : ZeroExactSingletonDefectProfileBudgeted dom k a u₀ u₁ D) :
    singletonBadScalarDefect dom k a u₀ u₁
      ≤ ∑ t ∈ Finset.range a, (directionZeroSet u₁).card.choose t * D t := by
  calc
    singletonBadScalarDefect dom k a u₀ u₁
        ≤ ∑ t ∈ Finset.range a,
          ∑ S ∈ (directionZeroSet u₁).powersetCard t,
            (singletonBadScalarIncidencesInExactZeroAgreementFiber dom k a u₀ u₁ S).card :=
          singletonBadScalarDefect_le_sum_exactSingletonProfiles dom k a u₀ u₁ hsafe
    _ ≤ ∑ t ∈ Finset.range a,
          ∑ _S ∈ (directionZeroSet u₁).powersetCard t, D t := by
        refine Finset.sum_le_sum ?_
        intro t ht
        exact Finset.sum_le_sum fun S hS => hProfile t (Finset.mem_range.mp ht) S hS
    _ = ∑ t ∈ Finset.range a, (directionZeroSet u₁).card.choose t * D t := by
        refine Finset.sum_congr rfl ?_
        intro t _ht
        rw [Finset.sum_const, smul_eq_mul, Finset.card_powersetCard]

open Classical in
/-- A profile-wise singleton-defect budget plus its arithmetic fit bounds the singleton defect. -/
theorem singletonBadScalarDefect_le_of_exactSingletonProfileBudgeted_and_fits
    (dom : Fin n ↪ F) (k a B : ℕ) (u₀ u₁ : Fin n → F) (D : ℕ → ℕ)
    (hsafe : ZeroDirectionSafeLine dom k a u₀ u₁)
    (hProfile : ZeroExactSingletonDefectProfileBudgeted dom k a u₀ u₁ D)
    (hFits : ZeroExactSingletonDefectProfileBudgetFits (F := F) (n := n) a B u₁ D) :
    singletonBadScalarDefect dom k a u₀ u₁ ≤ B :=
  le_trans
    (singletonBadScalarDefect_le_of_exactSingletonProfileBudgeted
      dom k a u₀ u₁ D hsafe hProfile)
    hFits

open Classical in
/-- Exact singleton-profile budgets imply the older combined singleton-defect arithmetic budget. -/
theorem uniformLargeZeroSafeWeightPlusSingletonDefectBudgeted_of_exactSingletonProfileBudget
    (dom : Fin n ↪ F) (k a B : ℕ) (D : ℕ → ℕ)
    (hProfile : UniformLargeZeroSafeExactSingletonDefectProfileBudgeted dom k a D)
    (hbudget : UniformLargeZeroSafeWeightPlusExactSingletonProfileBudgeted dom k a B D) :
    UniformLargeZeroSafeWeightPlusSingletonDefectBudgeted dom k a B := by
  intro u₀ u₁ hnotEligible hsafe
  exact le_trans
    (Nat.add_le_add_left
      (singletonBadScalarDefect_le_of_exactSingletonProfileBudgeted
        dom k a u₀ u₁ D hsafe (hProfile u₀ u₁ hnotEligible hsafe))
      (puncturedZeroStratifiedLineWeight dom k a u₀ u₁))
    (hbudget u₀ u₁ hnotEligible hsafe)

open Classical in
/-- Exact appearance-fiber singleton budgets imply the older combined singleton-defect arithmetic
budget. -/
theorem uniformLargeZeroSafeWeightPlusSingletonDefectBudgeted_of_exactAppearanceFiberSingletonBudget
    (dom : Fin n ↪ F) (k a B : ℕ) (D : ℕ → ℕ)
    (hAppearance : UniformLargeZeroSafeExactAppearanceFiberSingletonBudgeted dom k a D)
    (hbudget : UniformLargeZeroSafeWeightPlusExactSingletonProfileBudgeted dom k a B D) :
    UniformLargeZeroSafeWeightPlusSingletonDefectBudgeted dom k a B :=
  uniformLargeZeroSafeWeightPlusSingletonDefectBudgeted_of_exactSingletonProfileBudget
    dom k a B D
    (uniformExactSingletonProfileBudgeted_of_exactAppearanceFiberSingletonBudgeted
      dom k a D hAppearance)
    hbudget

open Classical in
/-- Bad-scalar budget from exact singleton-defect profile budgets and combined arithmetic. -/
theorem lineBadScalars_card_le_of_weight_add_exactSingletonProfileBudget_le_two_mul
    (dom : Fin n ↪ F) (k a B : ℕ) (u₀ u₁ : Fin n → F) (D : ℕ → ℕ)
    (hsafe : ZeroDirectionSafeLine dom k a u₀ u₁)
    (hProfile : ZeroExactSingletonDefectProfileBudgeted dom k a u₀ u₁ D)
    (hbudget : puncturedZeroStratifiedLineWeight dom k a u₀ u₁
        + ∑ t ∈ Finset.range a, (directionZeroSet u₁).card.choose t * D t ≤ 2 * B) :
    (lineBadScalars dom k a u₀ u₁).card ≤ B :=
  lineBadScalars_card_le_of_weight_add_singletonDefect_le_two_mul
    dom k a B u₀ u₁ hsafe
    (le_trans
      (Nat.add_le_add_left
        (singletonBadScalarDefect_le_of_exactSingletonProfileBudgeted
          dom k a u₀ u₁ D hsafe hProfile)
        (puncturedZeroStratifiedLineWeight dom k a u₀ u₁))
      hbudget)

open Classical in
/-- Uniform large-zero safe consumer for exact singleton-defect profile budgets. -/
theorem largeZeroSafeLineBadScalarsBudgeted_of_exactSingletonProfileBudget
    (dom : Fin n ↪ F) (k a B : ℕ) (D : ℕ → ℕ)
    (hProfile : UniformLargeZeroSafeExactSingletonDefectProfileBudgeted dom k a D)
    (hbudget : UniformLargeZeroSafeWeightPlusExactSingletonProfileBudgeted dom k a B D) :
    LargeZeroSafeLineBadScalarsBudgeted dom k a B := by
  intro u₀ u₁ hnotEligible hsafe
  exact lineBadScalars_card_le_of_weight_add_exactSingletonProfileBudget_le_two_mul
    dom k a B u₀ u₁ D hsafe
    (hProfile u₀ u₁ hnotEligible hsafe)
    (hbudget u₀ u₁ hnotEligible hsafe)

open Classical in
/-- Production wrapper for the exact singleton-defect profile route. -/
theorem uniformLineBadScalarsBudgeted_of_supportAdjusted_and_exactSingletonProfileBudget
    (dom : Fin n ↪ F) (k a L B : ℕ) (D : ℕ → ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hProfile : UniformLargeZeroSafeExactSingletonDefectProfileBudgeted dom k a D)
    (hbudget : UniformLargeZeroSafeWeightPlusExactSingletonProfileBudgeted dom k a B D) :
    UniformLineBadScalarsBudgeted dom k a B :=
  uniformLineBadScalarsBudgeted_of_supportAdjustedBudgetFits_and_largeZeroSafe
    dom k a L B hSupport hFits hZeroSafe
    (largeZeroSafeLineBadScalarsBudgeted_of_exactSingletonProfileBudget
      dom k a B D hProfile hbudget)

open Classical in
/-- Uniform production wrapper from exact appearance-fiber singleton budgets. -/
theorem uniformLineBadScalarsBudgeted_of_exactAppearanceFiberSingletonBudget
    (dom : Fin n ↪ F) (k a L B : ℕ) (D : ℕ → ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hAppearance : UniformLargeZeroSafeExactAppearanceFiberSingletonBudgeted dom k a D)
    (hbudget : UniformLargeZeroSafeWeightPlusExactSingletonProfileBudgeted dom k a B D) :
    UniformLineBadScalarsBudgeted dom k a B :=
  uniformLineBadScalarsBudgeted_of_supportAdjusted_and_exactSingletonProfileBudget
    dom k a L B D hSupport hFits hZeroSafe
    (uniformExactSingletonProfileBudgeted_of_exactAppearanceFiberSingletonBudgeted
      dom k a D hAppearance)
    hbudget

open Classical in
/-- Converse scanner for the exact singleton-defect profile route.  Once support, zero-safety,
profile budgets, and support arithmetic are fixed, any failed uniform bad-scalar budget violates
the combined punctured-weight plus profile-defect arithmetic on a large-zero safe line. -/
theorem exists_largeZero_safe_exactSingletonProfileBudgetFailure_of_not_budgeted
    (dom : Fin n ↪ F) (k a L B : ℕ) (D : ℕ → ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hProfile : UniformLargeZeroSafeExactSingletonDefectProfileBudgeted dom k a D)
    (hnot : ¬ UniformLineBadScalarsBudgeted dom k a B) :
    ∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
      ZeroDirectionSafeLine dom k a u₀ u₁ ∧
        ¬ puncturedZeroStratifiedLineWeight dom k a u₀ u₁
          + ∑ t ∈ Finset.range a, (directionZeroSet u₁).card.choose t * D t ≤ 2 * B := by
  by_contra hnone
  have hbudget : UniformLargeZeroSafeWeightPlusExactSingletonProfileBudgeted dom k a B D := by
    intro u₀ u₁ hnotEligible hsafe
    by_contra hfail
    exact hnone ⟨u₀, u₁, hnotEligible, hsafe, hfail⟩
  exact hnot
    (uniformLineBadScalarsBudgeted_of_supportAdjusted_and_exactSingletonProfileBudget
      dom k a L B D hSupport hFits hZeroSafe hProfile hbudget)

open Classical in
/-- Converse scanner for the exact appearance-fiber singleton route.  Once support arithmetic,
zero-safety, and exact appearance-fiber singleton bounds are fixed, any failed uniform bad-scalar
budget violates the combined punctured-weight plus profile arithmetic on a large-zero safe line. -/
theorem exists_largeZero_safe_exactAppearanceFiberSingletonBudgetFailure_of_not_budgeted
    (dom : Fin n ↪ F) (k a L B : ℕ) (D : ℕ → ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hAppearance : UniformLargeZeroSafeExactAppearanceFiberSingletonBudgeted dom k a D)
    (hnot : ¬ UniformLineBadScalarsBudgeted dom k a B) :
    ∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
      ZeroDirectionSafeLine dom k a u₀ u₁ ∧
        ¬ puncturedZeroStratifiedLineWeight dom k a u₀ u₁
          + ∑ t ∈ Finset.range a, (directionZeroSet u₁).card.choose t * D t ≤ 2 * B :=
  exists_largeZero_safe_exactSingletonProfileBudgetFailure_of_not_budgeted
    dom k a L B D hSupport hFits hZeroSafe
    (uniformExactSingletonProfileBudgeted_of_exactAppearanceFiberSingletonBudgeted
      dom k a D hAppearance)
    hnot

open Classical in
/-- Converse scanner for the profile envelope itself.  Once support, zero-safety, support
arithmetic, and the combined weight-plus-profile arithmetic are fixed, any failed uniform
bad-scalar budget exposes an overfull exact singleton-defect profile. -/
theorem exists_largeZero_safe_exactSingletonProfile_gt_of_not_uniformLineBadScalarsBudgeted
    (dom : Fin n ↪ F) (k a L B : ℕ) (D : ℕ → ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hbudget : UniformLargeZeroSafeWeightPlusExactSingletonProfileBudgeted dom k a B D)
    (hnot : ¬ UniformLineBadScalarsBudgeted dom k a B) :
    ∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
      ZeroDirectionSafeLine dom k a u₀ u₁ ∧
        ∃ t : ℕ, t < a ∧ ∃ S ∈ (directionZeroSet u₁).powersetCard t,
          D t < (singletonBadScalarIncidencesInExactZeroAgreementFiber
            dom k a u₀ u₁ S).card := by
  by_contra hnone
  have hProfile : UniformLargeZeroSafeExactSingletonDefectProfileBudgeted dom k a D := by
    intro u₀ u₁ hnotEligible hsafe t ht S hS
    exact le_of_not_gt
      (fun hgt => hnone ⟨u₀, u₁, hnotEligible, hsafe, t, ht, S, hS, hgt⟩)
  exact hnot
    (uniformLineBadScalarsBudgeted_of_supportAdjusted_and_exactSingletonProfileBudget
      dom k a L B D hSupport hFits hZeroSafe hProfile hbudget)

open Classical in
/-- Converse scanner for the exact appearance-fiber singleton envelope.  Once support,
zero-safety, support arithmetic, and the combined profile arithmetic are fixed, any failed uniform
bad-scalar budget exposes an exact appearance profile whose support-denominator weighted size
exceeds the proposed singleton cap. -/
theorem exists_largeZero_safe_exactAppearanceFiberSingleton_gt_of_not_uniformLineBadScalarsBudgeted
    (dom : Fin n ↪ F) (k a L B : ℕ) (D : ℕ → ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hbudget : UniformLargeZeroSafeWeightPlusExactSingletonProfileBudgeted dom k a B D)
    (hnot : ¬ UniformLineBadScalarsBudgeted dom k a B) :
    ∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
      ZeroDirectionSafeLine dom k a u₀ u₁ ∧
        ∃ t : ℕ, t < a ∧ ∃ S ∈ (directionZeroSet u₁).powersetCard t,
          D t <
            (exactAppearingZeroAgreementFiber dom k a u₀ u₁ S).card *
              ((directionSupportSet u₁).card / (a - t)) := by
  by_contra hnone
  have hAppearance : UniformLargeZeroSafeExactAppearanceFiberSingletonBudgeted dom k a D := by
    intro u₀ u₁ hnotEligible hsafe t ht S hS
    exact le_of_not_gt
      (fun hgt => hnone ⟨u₀, u₁, hnotEligible, hsafe, t, ht, S, hS, hgt⟩)
  exact hnot
    (uniformLineBadScalarsBudgeted_of_exactAppearanceFiberSingletonBudget
      dom k a L B D hSupport hFits hZeroSafe hAppearance hbudget)

section SourceAudit

#print axioms singletonBadScalarIncidences
#print axioms mem_singletonBadScalarIncidences
#print axioms singletonBadScalarIncidences_card_eq_singletonBadScalarDefect
#print axioms singletonBadScalarDefect_le_lineHeavyIncidences_card
#print axioms singletonBadScalarDefect_le_puncturedZeroStratifiedLineWeight
#print axioms singletonBadScalarIncidencesInExactZeroAgreementFiber
#print axioms mem_singletonBadScalarIncidencesInExactZeroAgreementFiber
#print axioms disjoint_singletonBadScalarIncidencesInExactZeroAgreementFiber_of_ne
#print axioms snd_mem_exactAppearingZeroAgreementFiber_of_mem_singletonBadScalarIncidencesInExact
#print axioms singletonBadScalarIncidencesInExact_card_le_exactFiber_card_mul_support_div
#print axioms ZeroExactSingletonDefectProfileBudgeted
#print axioms ZeroExactSingletonDefectProfileBudgetFits
#print axioms UniformLargeZeroSafeExactSingletonDefectProfileBudgeted
#print axioms UniformLargeZeroSafeWeightPlusExactSingletonProfileBudgeted
#print axioms ZeroExactAppearanceFiberSingletonBudgeted
#print axioms UniformLargeZeroSafeExactAppearanceFiberSingletonBudgeted
#print axioms zeroExactSingletonDefectProfileBudgeted_of_exactAppearanceFiberSingletonBudgeted
#print axioms
  uniformExactSingletonProfileBudgeted_of_exactAppearanceFiberSingletonBudgeted
#print axioms zeroExactAppearanceFiberSingletonBudgeted_of_exactAppearingZeroAgreementFiberBudgeted
#print axioms
  uniformExactAppearanceFiberSingletonBudgeted_of_exactAppearingFiberBudgeted
#print axioms uniformLargeZeroSafeWeightPlusSingletonDefectBudgeted_of_exactSingletonProfileBudget
#print axioms
  uniformLargeZeroSafeWeightPlusSingletonDefectBudgeted_of_exactAppearanceFiberSingletonBudget
#print axioms singletonBadScalarIncidences_subset_biUnion_exactProfiles
#print axioms singletonBadScalarDefect_le_sum_exactSingletonProfiles
#print axioms singletonBadScalarDefect_le_of_exactSingletonProfileBudgeted
#print axioms singletonBadScalarDefect_le_of_exactSingletonProfileBudgeted_and_fits
#print axioms lineBadScalars_card_le_of_weight_add_exactSingletonProfileBudget_le_two_mul
#print axioms largeZeroSafeLineBadScalarsBudgeted_of_exactSingletonProfileBudget
#print axioms uniformLineBadScalarsBudgeted_of_supportAdjusted_and_exactSingletonProfileBudget
#print axioms uniformLineBadScalarsBudgeted_of_exactAppearanceFiberSingletonBudget
#print axioms
  exists_largeZero_safe_exactSingletonProfileBudgetFailure_of_not_budgeted
#print axioms
  exists_largeZero_safe_exactAppearanceFiberSingletonBudgetFailure_of_not_budgeted
#print axioms
  exists_largeZero_safe_exactSingletonProfile_gt_of_not_uniformLineBadScalarsBudgeted
#print axioms
  exists_largeZero_safe_exactAppearanceFiberSingleton_gt_of_not_uniformLineBadScalarsBudgeted

end SourceAudit

end ProximityGap.Ownership
