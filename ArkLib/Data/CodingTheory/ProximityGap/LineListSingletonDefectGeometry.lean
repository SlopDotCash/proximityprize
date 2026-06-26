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

section SourceAudit

#print axioms singletonBadScalarIncidences
#print axioms mem_singletonBadScalarIncidences
#print axioms singletonBadScalarIncidences_card_eq_singletonBadScalarDefect
#print axioms singletonBadScalarDefect_le_lineHeavyIncidences_card
#print axioms singletonBadScalarDefect_le_puncturedZeroStratifiedLineWeight
#print axioms singletonBadScalarIncidencesInExactZeroAgreementFiber
#print axioms mem_singletonBadScalarIncidencesInExactZeroAgreementFiber
#print axioms snd_mem_exactAppearingZeroAgreementFiber_of_mem_singletonBadScalarIncidencesInExact
#print axioms singletonBadScalarIncidencesInExact_card_le_exactFiber_card_mul_support_div

end SourceAudit

end ProximityGap.Ownership
