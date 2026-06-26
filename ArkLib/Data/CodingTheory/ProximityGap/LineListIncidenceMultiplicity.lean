/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LineListReduction

/-!
# Incidence multiplicity for the line-list route

`LineListReduction.lean` bounds a line's bad scalars by union-bounding over appearing codewords.
This file records the exact incidence graph behind that step.  The useful new interface is a
conditional multiplicity discount: if every bad scalar has at least `R` codeword witnesses, then
the punctured zero-stratified weight bounds `R * #badScalars`.

This does not prove such a multiplicity floor.  It isolates it as a strictly different residual
from the existing appearance-fiber and line-list-size budgets.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- Codewords witnessing that a fixed scalar is bad on the affine line. -/
noncomputable def badScalarWitnessCodewords
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (γ : F) :
    Finset (Fin n → F) :=
  (Finset.univ : Finset (Fin n → F)).filter
    (fun c => c ∈ (rsCode dom k : Submodule F (Fin n → F)) ∧
      a ≤ (agreeSet c (fun i => u₀ i + γ • u₁ i)).card)

open Classical in
/-- Scalars for which a fixed word is heavy along the affine line. -/
noncomputable def codewordHeavyScalars
    (a : ℕ) (c u₀ u₁ : Fin n → F) : Finset F :=
  (Finset.univ : Finset F).filter
    (fun γ => a ≤ (agreeSet c (fun i => u₀ i + γ • u₁ i)).card)

open Classical in
/-- The bipartite incidence graph between bad scalars and their witnessing codewords. -/
noncomputable def lineHeavyIncidences
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) :
    Finset (F × (Fin n → F)) :=
  (Finset.univ : Finset (F × (Fin n → F))).filter
    (fun e => e.2 ∈ (rsCode dom k : Submodule F (Fin n → F)) ∧
      a ≤ (agreeSet e.2 (fun i => u₀ i + e.1 • u₁ i)).card)

theorem mem_badScalarWitnessCodewords
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (γ : F)
    (c : Fin n → F) :
    c ∈ badScalarWitnessCodewords dom k a u₀ u₁ γ ↔
      c ∈ (rsCode dom k : Submodule F (Fin n → F)) ∧
        a ≤ (agreeSet c (fun i => u₀ i + γ • u₁ i)).card := by
  classical
  rw [badScalarWitnessCodewords, Finset.mem_filter]
  simp

theorem mem_codewordHeavyScalars
    (a : ℕ) (c u₀ u₁ : Fin n → F) (γ : F) :
    γ ∈ codewordHeavyScalars (F := F) (n := n) a c u₀ u₁ ↔
      a ≤ (agreeSet c (fun i => u₀ i + γ • u₁ i)).card := by
  classical
  rw [codewordHeavyScalars, Finset.mem_filter]
  simp

theorem mem_lineHeavyIncidences
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F)
    (e : F × (Fin n → F)) :
    e ∈ lineHeavyIncidences dom k a u₀ u₁ ↔
      e.2 ∈ (rsCode dom k : Submodule F (Fin n → F)) ∧
        a ≤ (agreeSet e.2 (fun i => u₀ i + e.1 • u₁ i)).card := by
  classical
  rw [lineHeavyIncidences, Finset.mem_filter]
  simp

open Classical in
/-- Bad scalars are exactly the first projection of the incidence graph. -/
theorem lineBadScalars_eq_image_fst_lineHeavyIncidences
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) :
    lineBadScalars dom k a u₀ u₁ =
      (lineHeavyIncidences dom k a u₀ u₁).image Prod.fst := by
  ext γ
  constructor
  · intro hγ
    rw [lineBadScalars, Finset.mem_filter] at hγ
    rcases hγ with ⟨_, c, hc, hheavy⟩
    refine Finset.mem_image.mpr ⟨(γ, c), ?_, rfl⟩
    rw [mem_lineHeavyIncidences]
    exact ⟨hc, hheavy⟩
  · intro hγ
    rcases Finset.mem_image.mp hγ with ⟨⟨γ', c⟩, hinc, hfst⟩
    dsimp at hfst
    subst γ'
    rw [mem_lineHeavyIncidences] at hinc
    rw [lineBadScalars, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, c, hinc.1, hinc.2⟩

open Classical in
/-- Appearing codewords are exactly the second projection of the incidence graph. -/
theorem lineAppearingCodewords_eq_image_snd_lineHeavyIncidences
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) :
    lineAppearingCodewords dom k a u₀ u₁ =
      (lineHeavyIncidences dom k a u₀ u₁).image Prod.snd := by
  ext c
  constructor
  · intro hc
    rw [lineAppearingCodewords, Finset.mem_filter] at hc
    rcases hc with ⟨_, hcode, γ, hheavy⟩
    refine Finset.mem_image.mpr ⟨(γ, c), ?_, rfl⟩
    rw [mem_lineHeavyIncidences]
    exact ⟨hcode, hheavy⟩
  · intro hc
    rcases Finset.mem_image.mp hc with ⟨⟨γ, c'⟩, hinc, hsnd⟩
    dsimp at hsnd
    subst c'
    rw [mem_lineHeavyIncidences] at hinc
    rw [lineAppearingCodewords, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hinc.1, γ, hinc.2⟩

open Classical in
/-- Projection from incidences to bad scalars gives the old union-bound starting point. -/
theorem lineBadScalars_card_le_lineHeavyIncidences_card
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) :
    (lineBadScalars dom k a u₀ u₁).card
      ≤ (lineHeavyIncidences dom k a u₀ u₁).card := by
  rw [lineBadScalars_eq_image_fst_lineHeavyIncidences]
  exact Finset.card_image_le

open Classical in
/-- Projection from incidences to appearing codewords. -/
theorem lineAppearingCodewords_card_le_lineHeavyIncidences_card
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) :
    (lineAppearingCodewords dom k a u₀ u₁).card
      ≤ (lineHeavyIncidences dom k a u₀ u₁).card := by
  rw [lineAppearingCodewords_eq_image_snd_lineHeavyIncidences]
  exact Finset.card_image_le

open Classical in
/-- The fiber of the incidence graph over a scalar is exactly its witnessing-codeword set. -/
theorem lineHeavyIncidences_fst_fiber_card_eq_badScalarWitnessCodewords_card
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (γ : F) :
    ((lineHeavyIncidences dom k a u₀ u₁).filter (fun e => e.1 = γ)).card =
      (badScalarWitnessCodewords dom k a u₀ u₁ γ).card := by
  let toIncidence : (Fin n → F) → F × (Fin n → F) := fun c => (γ, c)
  have hfiber :
      (lineHeavyIncidences dom k a u₀ u₁).filter (fun e => e.1 = γ) =
        (badScalarWitnessCodewords dom k a u₀ u₁ γ).image toIncidence := by
    ext e
    rcases e with ⟨γ', c⟩
    constructor
    · intro he
      rw [Finset.mem_filter] at he
      dsimp at he
      have hγ' : γ' = γ := he.2
      subst γ'
      rw [mem_lineHeavyIncidences] at he
      refine Finset.mem_image.mpr ⟨c, ?_, rfl⟩
      rw [mem_badScalarWitnessCodewords]
      exact he.1
    · intro he
      rcases Finset.mem_image.mp he with ⟨c', hc', hpair⟩
      cases hpair
      rw [Finset.mem_filter]
      refine ⟨?_, rfl⟩
      rw [mem_lineHeavyIncidences]
      rw [mem_badScalarWitnessCodewords] at hc'
      exact hc'
  rw [hfiber]
  exact Finset.card_image_of_injOn
    (fun _ _ _ _ h => by simpa [toIncidence] using congrArg Prod.snd h)

open Classical in
/-- The incidence count decomposes as the sum of bad-scalar witness multiplicities. -/
theorem lineHeavyIncidences_card_eq_sum_badScalarWitnessCodewords
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) :
    (lineHeavyIncidences dom k a u₀ u₁).card =
      ∑ γ ∈ lineBadScalars dom k a u₀ u₁,
        (badScalarWitnessCodewords dom k a u₀ u₁ γ).card := by
  classical
  let I := lineHeavyIncidences dom k a u₀ u₁
  let B := lineBadScalars dom k a u₀ u₁
  have hmaps : ∀ e ∈ I, e.1 ∈ B := by
    intro e he
    have himage : e.1 ∈ I.image Prod.fst := Finset.mem_image.mpr ⟨e, he, rfl⟩
    simpa [B, I, lineBadScalars_eq_image_fst_lineHeavyIncidences]
      using himage
  calc
    I.card = ∑ γ ∈ B, (I.filter (fun e => e.1 = γ)).card :=
      Finset.card_eq_sum_card_fiberwise hmaps
    _ = ∑ γ ∈ B, (badScalarWitnessCodewords dom k a u₀ u₁ γ).card := by
      refine Finset.sum_congr rfl ?_
      intro γ _hγ
      exact lineHeavyIncidences_fst_fiber_card_eq_badScalarWitnessCodewords_card
        dom k a u₀ u₁ γ

open Classical in
/-- The fiber of the incidence graph over a codeword is exactly its heavy-scalar set. -/
theorem lineHeavyIncidences_snd_fiber_card_eq_codewordHeavyScalars_card
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ c : Fin n → F)
    (hc : c ∈ (rsCode dom k : Submodule F (Fin n → F))) :
    ((lineHeavyIncidences dom k a u₀ u₁).filter (fun e => e.2 = c)).card =
      (codewordHeavyScalars (F := F) (n := n) a c u₀ u₁).card := by
  let toIncidence : F → F × (Fin n → F) := fun γ => (γ, c)
  have hfiber :
      (lineHeavyIncidences dom k a u₀ u₁).filter (fun e => e.2 = c) =
        (codewordHeavyScalars (F := F) (n := n) a c u₀ u₁).image toIncidence := by
    ext e
    rcases e with ⟨γ, c'⟩
    constructor
    · intro he
      rw [Finset.mem_filter] at he
      dsimp at he
      have hc' : c' = c := he.2
      subst c'
      rw [mem_lineHeavyIncidences] at he
      refine Finset.mem_image.mpr ⟨γ, ?_, rfl⟩
      rw [mem_codewordHeavyScalars]
      exact he.1.2
    · intro he
      rcases Finset.mem_image.mp he with ⟨γ', hγ', hpair⟩
      cases hpair
      rw [Finset.mem_filter]
      refine ⟨?_, rfl⟩
      rw [mem_lineHeavyIncidences]
      rw [mem_codewordHeavyScalars] at hγ'
      exact ⟨hc, hγ'⟩
  rw [hfiber]
  exact Finset.card_image_of_injOn
    (fun _ _ _ _ h => by simpa [toIncidence] using congrArg Prod.fst h)

open Classical in
/-- The incidence count also decomposes over appearing codewords and their heavy scalars. -/
theorem lineHeavyIncidences_card_eq_sum_codewordHeavyScalars
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) :
    (lineHeavyIncidences dom k a u₀ u₁).card =
      ∑ c ∈ lineAppearingCodewords dom k a u₀ u₁,
        (codewordHeavyScalars (F := F) (n := n) a c u₀ u₁).card := by
  classical
  let I := lineHeavyIncidences dom k a u₀ u₁
  let App := lineAppearingCodewords dom k a u₀ u₁
  have hmaps : ∀ e ∈ I, e.2 ∈ App := by
    intro e he
    have himage : e.2 ∈ I.image Prod.snd := Finset.mem_image.mpr ⟨e, he, rfl⟩
    simpa [App, I, lineAppearingCodewords_eq_image_snd_lineHeavyIncidences]
      using himage
  calc
    I.card = ∑ c ∈ App, (I.filter (fun e => e.2 = c)).card :=
      Finset.card_eq_sum_card_fiberwise hmaps
    _ = ∑ c ∈ App, (codewordHeavyScalars (F := F) (n := n) a c u₀ u₁).card := by
      refine Finset.sum_congr rfl ?_
      intro c hcApp
      have hcCode : c ∈ (rsCode dom k : Submodule F (Fin n → F)) := by
        have hcApp' : c ∈ lineAppearingCodewords dom k a u₀ u₁ := by
          simpa [App] using hcApp
        rw [lineAppearingCodewords, Finset.mem_filter] at hcApp'
        exact hcApp'.2.1
      exact lineHeavyIncidences_snd_fiber_card_eq_codewordHeavyScalars_card
        dom k a u₀ u₁ c hcCode

open Classical in
/-- The punctured zero-stratified weight bounds the full incidence count, not just its scalar
projection. -/
theorem lineHeavyIncidences_card_le_puncturedZeroStratifiedLineWeight
    (dom : Fin n ↪ F) (k a : ℕ)
    (u₀ u₁ : Fin n → F) (hsafe : ZeroDirectionSafeLine dom k a u₀ u₁) :
    (lineHeavyIncidences dom k a u₀ u₁).card
      ≤ puncturedZeroStratifiedLineWeight dom k a u₀ u₁ := by
  rw [lineHeavyIncidences_card_eq_sum_codewordHeavyScalars,
    puncturedZeroStratifiedLineWeight]
  refine Finset.sum_le_sum ?_
  intro c hcApp
  have hcCode : c ∈ (rsCode dom k : Submodule F (Fin n → F)) := by
    rw [lineAppearingCodewords, Finset.mem_filter] at hcApp
    exact hcApp.2.1
  simpa [codewordHeavyScalars] using
    codeword_heavy_scalar_card_le_support_div_sub_zeroAgreement
      (F := F) (n := n) a c u₀ u₁ (hsafe c hcCode)

/-- A bad-scalar multiplicity floor: every bad scalar has at least `R` witnessing codewords. -/
def LineBadScalarMultiplicityFloor
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (R : ℕ) : Prop :=
  ∀ γ ∈ lineBadScalars dom k a u₀ u₁,
    R ≤ (badScalarWitnessCodewords dom k a u₀ u₁ γ).card

open Classical in
/-- Multiplicity converts the incidence identity into `#badScalars * R ≤ #incidences`. -/
theorem lineBadScalars_card_mul_le_lineHeavyIncidences_card_of_multiplicityFloor
    (dom : Fin n ↪ F) (k a R : ℕ) (u₀ u₁ : Fin n → F)
    (hmult : LineBadScalarMultiplicityFloor dom k a u₀ u₁ R) :
    (lineBadScalars dom k a u₀ u₁).card * R
      ≤ (lineHeavyIncidences dom k a u₀ u₁).card := by
  rw [lineHeavyIncidences_card_eq_sum_badScalarWitnessCodewords]
  calc
    (lineBadScalars dom k a u₀ u₁).card * R
        = ∑ _γ ∈ lineBadScalars dom k a u₀ u₁, R := by
          rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ γ ∈ lineBadScalars dom k a u₀ u₁,
          (badScalarWitnessCodewords dom k a u₀ u₁ γ).card :=
        Finset.sum_le_sum hmult

open Classical in
/-- Multiplicity discount against the punctured line weight.  When every bad scalar has at least
`R` codeword witnesses, the punctured weight pays for `R` copies of each bad scalar. -/
theorem lineBadScalars_card_mul_le_puncturedZeroStratifiedLineWeight_of_multiplicityFloor
    (dom : Fin n ↪ F) (k a R : ℕ) (u₀ u₁ : Fin n → F)
    (hsafe : ZeroDirectionSafeLine dom k a u₀ u₁)
    (hmult : LineBadScalarMultiplicityFloor dom k a u₀ u₁ R) :
    (lineBadScalars dom k a u₀ u₁).card * R
      ≤ puncturedZeroStratifiedLineWeight dom k a u₀ u₁ :=
  le_trans
    (lineBadScalars_card_mul_le_lineHeavyIncidences_card_of_multiplicityFloor
      dom k a R u₀ u₁ hmult)
    (lineHeavyIncidences_card_le_puncturedZeroStratifiedLineWeight
      dom k a u₀ u₁ hsafe)

open Classical in
/-- Division form of the multiplicity discount. -/
theorem lineBadScalars_card_le_puncturedZeroStratifiedLineWeight_div_of_multiplicityFloor
    (dom : Fin n ↪ F) (k a R : ℕ) (u₀ u₁ : Fin n → F)
    (hR : 1 ≤ R)
    (hsafe : ZeroDirectionSafeLine dom k a u₀ u₁)
    (hmult : LineBadScalarMultiplicityFloor dom k a u₀ u₁ R) :
    (lineBadScalars dom k a u₀ u₁).card
      ≤ puncturedZeroStratifiedLineWeight dom k a u₀ u₁ / R :=
  (Nat.le_div_iff_mul_le hR).mpr
    (lineBadScalars_card_mul_le_puncturedZeroStratifiedLineWeight_of_multiplicityFloor
      dom k a R u₀ u₁ hsafe hmult)

open Classical in
/-- Budget consumer for the multiplicity-discounted punctured weight. -/
theorem lineBadScalars_card_le_of_multiplicityFloor_and_weight_div_le
    (dom : Fin n ↪ F) (k a R B : ℕ) (u₀ u₁ : Fin n → F)
    (hR : 1 ≤ R)
    (hsafe : ZeroDirectionSafeLine dom k a u₀ u₁)
    (hmult : LineBadScalarMultiplicityFloor dom k a u₀ u₁ R)
    (hbudget : puncturedZeroStratifiedLineWeight dom k a u₀ u₁ / R ≤ B) :
    (lineBadScalars dom k a u₀ u₁).card ≤ B :=
  le_trans
    (lineBadScalars_card_le_puncturedZeroStratifiedLineWeight_div_of_multiplicityFloor
      dom k a R u₀ u₁ hR hsafe hmult)
    hbudget

section SourceAudit

#print axioms badScalarWitnessCodewords
#print axioms codewordHeavyScalars
#print axioms lineHeavyIncidences
#print axioms lineBadScalars_eq_image_fst_lineHeavyIncidences
#print axioms lineAppearingCodewords_eq_image_snd_lineHeavyIncidences
#print axioms lineHeavyIncidences_card_eq_sum_badScalarWitnessCodewords
#print axioms lineHeavyIncidences_card_eq_sum_codewordHeavyScalars
#print axioms lineHeavyIncidences_card_le_puncturedZeroStratifiedLineWeight
#print axioms LineBadScalarMultiplicityFloor
#print axioms lineBadScalars_card_mul_le_puncturedZeroStratifiedLineWeight_of_multiplicityFloor
#print axioms lineBadScalars_card_le_puncturedZeroStratifiedLineWeight_div_of_multiplicityFloor
#print axioms lineBadScalars_card_le_of_multiplicityFloor_and_weight_div_le

end SourceAudit

end ProximityGap.Ownership
