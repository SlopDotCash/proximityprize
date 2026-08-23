/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LineListReduction
import ArkLib.Data.CodingTheory.ProximityGap.JohnsonListBound
import ArkLib.Data.CodingTheory.ProximityGap.OpenCoreConditionalPin

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
set_option linter.style.longFile 2100

open Finset
open scoped NNReal ENNReal

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

local instance instNonemptyFinOfNeZero : Nonempty (Fin n) :=
  ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩⟩

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

open Classical in
/-- Any witnessing codeword makes the scalar bad. -/
theorem lineBadScalars_mem_of_mem_badScalarWitnessCodewords
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) {γ : F} {c : Fin n → F}
    (hc : c ∈ badScalarWitnessCodewords dom k a u₀ u₁ γ) :
    γ ∈ lineBadScalars dom k a u₀ u₁ := by
  rw [mem_badScalarWitnessCodewords] at hc
  rw [lineBadScalars, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, c, hc.1, hc.2⟩

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
/-- Failure of a multiplicity floor is exactly a bad scalar with too few witnessing codewords. -/
theorem not_lineBadScalarMultiplicityFloor_iff_exists_badScalarWitnessCodewords_card_lt
    (dom : Fin n ↪ F) (k a R : ℕ) (u₀ u₁ : Fin n → F) :
    ¬ LineBadScalarMultiplicityFloor dom k a u₀ u₁ R ↔
      ∃ γ ∈ lineBadScalars dom k a u₀ u₁,
        (badScalarWitnessCodewords dom k a u₀ u₁ γ).card < R := by
  constructor
  · intro h
    by_contra hnone
    apply h
    intro γ hγ
    exact le_of_not_gt (fun hlt => hnone ⟨γ, hγ, hlt⟩)
  · rintro ⟨γ, hγ, hlt⟩ hmult
    exact (not_lt_of_ge (hmult γ hγ)) hlt

open Classical in
/-- Every bad scalar has at least one witnessing codeword. -/
theorem badScalarWitnessCodewords_card_pos_of_mem_lineBadScalars
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) {γ : F}
    (hγ : γ ∈ lineBadScalars dom k a u₀ u₁) :
    0 < (badScalarWitnessCodewords dom k a u₀ u₁ γ).card := by
  rw [lineBadScalars, Finset.mem_filter] at hγ
  rcases hγ with ⟨_, c, hcCode, hheavy⟩
  exact Finset.card_pos.mpr ⟨c, (mem_badScalarWitnessCodewords dom k a u₀ u₁ γ c).mpr
    ⟨hcCode, hheavy⟩⟩

open Classical in
/-- The `R = 1` multiplicity floor is automatic and gives no genuine discount. -/
theorem lineBadScalarMultiplicityFloor_one
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) :
    LineBadScalarMultiplicityFloor dom k a u₀ u₁ 1 := by
  intro γ hγ
  exact badScalarWitnessCodewords_card_pos_of_mem_lineBadScalars dom k a u₀ u₁ hγ

open Classical in
/-- Failure of the first nontrivial multiplicity floor (`R = 2`) is exactly a bad scalar with a
unique witnessing codeword. -/
theorem not_lineBadScalarMultiplicityFloor_two_iff_exists_unique_badScalarWitness
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) :
    ¬ LineBadScalarMultiplicityFloor dom k a u₀ u₁ 2 ↔
      ∃ γ ∈ lineBadScalars dom k a u₀ u₁,
        (badScalarWitnessCodewords dom k a u₀ u₁ γ).card = 1 := by
  constructor
  · intro hnot
    rcases (not_lineBadScalarMultiplicityFloor_iff_exists_badScalarWitnessCodewords_card_lt
      dom k a 2 u₀ u₁).mp hnot with ⟨γ, hγ, hlt⟩
    refine ⟨γ, hγ, ?_⟩
    have hpos := badScalarWitnessCodewords_card_pos_of_mem_lineBadScalars
      dom k a u₀ u₁ hγ
    omega
  · rintro ⟨γ, hγ, hcard⟩
    apply (not_lineBadScalarMultiplicityFloor_iff_exists_badScalarWitnessCodewords_card_lt
      dom k a 2 u₀ u₁).mpr
    refine ⟨γ, hγ, ?_⟩
    omega

/-- No bad scalar has a unique witnessing codeword.  This is the exact first nontrivial
multiplicity-discount condition. -/
def NoUniqueBadScalarWitness
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) : Prop :=
  ∀ γ ∈ lineBadScalars dom k a u₀ u₁,
    (badScalarWitnessCodewords dom k a u₀ u₁ γ).card ≠ 1

/-- A codeword is the unique witness for a fixed bad scalar. -/
def IsUniqueBadScalarWitnessCodeword
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (γ : F)
    (c : Fin n → F) : Prop :=
  c ∈ badScalarWitnessCodewords dom k a u₀ u₁ γ ∧
    ∀ c' ∈ badScalarWitnessCodewords dom k a u₀ u₁ γ, c' = c

open Classical in
/-- A singleton witness-codeword fiber is the same as an explicitly unique witness codeword. -/
theorem badScalarWitnessCodewords_card_eq_one_iff_exists_isUniqueBadScalarWitnessCodeword
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (γ : F) :
    (badScalarWitnessCodewords dom k a u₀ u₁ γ).card = 1 ↔
      ∃ c : Fin n → F, IsUniqueBadScalarWitnessCodeword dom k a u₀ u₁ γ c := by
  constructor
  · intro hcard
    rcases Finset.card_eq_one.mp hcard with ⟨c, hfiber⟩
    refine ⟨c, ?_⟩
    constructor
    · rw [hfiber]
      exact Finset.mem_singleton_self c
    · intro c' hc'
      rw [hfiber] at hc'
      exact Finset.mem_singleton.mp hc'
  · rintro ⟨c, hc, huniq⟩
    apply Finset.card_eq_one.mpr
    refine ⟨c, ?_⟩
    ext c'
    constructor
    · intro hc'
      rw [Finset.mem_singleton]
      exact huniq c' hc'
    · intro hc'
      rw [Finset.mem_singleton] at hc'
      subst c'
      exact hc

/-- Every witness to a bad scalar has a distinct second witness.  This is the positive form of the
no-unique-witness condition. -/
def BadScalarSecondWitnessProperty
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) : Prop :=
  ∀ γ ∈ lineBadScalars dom k a u₀ u₁,
    ∀ c ∈ badScalarWitnessCodewords dom k a u₀ u₁ γ,
      ∃ c' ∈ badScalarWitnessCodewords dom k a u₀ u₁ γ, c' ≠ c

open Classical in
/-- The no-unique-witness condition is exactly the constructive second-witness condition. -/
theorem noUniqueBadScalarWitness_iff_secondWitnessProperty
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) :
    NoUniqueBadScalarWitness dom k a u₀ u₁ ↔
      BadScalarSecondWitnessProperty dom k a u₀ u₁ := by
  constructor
  · intro hno γ hγ c hc
    by_contra hnone
    have hsubset :
        badScalarWitnessCodewords dom k a u₀ u₁ γ ⊆ ({c} : Finset (Fin n → F)) := by
      intro c' hc'
      rw [Finset.mem_singleton]
      by_contra hne
      exact hnone ⟨c', hc', hne⟩
    have hfiber : badScalarWitnessCodewords dom k a u₀ u₁ γ = {c} := by
      apply Finset.Subset.antisymm hsubset
      intro c' hc'
      rw [Finset.mem_singleton] at hc'
      subst c'
      exact hc
    have hcard : (badScalarWitnessCodewords dom k a u₀ u₁ γ).card = 1 := by
      rw [hfiber, Finset.card_singleton]
    exact hno γ hγ hcard
  · intro hsecond γ hγ hcard
    rcases (badScalarWitnessCodewords_card_eq_one_iff_exists_isUniqueBadScalarWitnessCodeword
      dom k a u₀ u₁ γ).mp hcard with ⟨c, hc, huniq⟩
    rcases hsecond γ hγ c hc with ⟨c', hc', hne⟩
    exact hne (huniq c' hc')

open Classical in
/-- In the strict unique-decoding regime, every nonempty per-scalar witness fiber is a singleton. -/
theorem badScalarWitnessCodewords_card_eq_one_of_uniqueDecoding
    (dom : Fin n ↪ F) (k a d : ℕ) (u₀ u₁ : Fin n → F) (γ : F)
    (hγ : γ ∈ lineBadScalars dom k a u₀ u₁)
    (hdist : ∀ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
      ∀ c' ∈ (rsCode dom k : Submodule F (Fin n → F)), c ≠ c' →
        d ≤ hammingDist c c')
    (h2a : Fintype.card (Fin n) + (Fintype.card (Fin n) - d) < 2 * a) :
    (badScalarWitnessCodewords dom k a u₀ u₁ γ).card = 1 := by
  have hfiberNonempty :
      (badScalarWitnessCodewords dom k a u₀ u₁ γ).Nonempty := by
    rw [lineBadScalars, Finset.mem_filter] at hγ
    rcases hγ with ⟨_, c, hc, hheavy⟩
    refine ⟨c, ?_⟩
    rw [mem_badScalarWitnessCodewords]
    exact ⟨hc, hheavy⟩
  refine ArkLib.JohnsonList.johnson_unique_decoding_eq_one
    (f := fun i : Fin n => u₀ i + γ • u₁ i)
    (L := badScalarWitnessCodewords dom k a u₀ u₁ γ)
    (a := a) (b := Fintype.card (Fin n) - d) hfiberNonempty ?_ ?_ h2a
  · intro c hc
    exact ((mem_badScalarWitnessCodewords dom k a u₀ u₁ γ c).mp hc).2
  · intro c hc c' hc' hne
    have hcCode := ((mem_badScalarWitnessCodewords dom k a u₀ u₁ γ c).mp hc).1
    have hc'Code := ((mem_badScalarWitnessCodewords dom k a u₀ u₁ γ c').mp hc').1
    exact ArkLib.JohnsonList.agree_card_le_card_sub_of_hammingDist_ge
      (hdist c hcCode c' hc'Code hne)

open Classical in
/-- A bad scalar in the strict unique-decoding regime gives an explicit unique witness codeword. -/
theorem exists_uniqueWitnessCodeword_of_mem_lineBadScalars_uniqueDecoding
    (dom : Fin n ↪ F) (k a d : ℕ) (u₀ u₁ : Fin n → F) {γ : F}
    (hγ : γ ∈ lineBadScalars dom k a u₀ u₁)
    (hdist : ∀ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
      ∀ c' ∈ (rsCode dom k : Submodule F (Fin n → F)), c ≠ c' →
        d ≤ hammingDist c c')
    (h2a : Fintype.card (Fin n) + (Fintype.card (Fin n) - d) < 2 * a) :
    ∃ c : Fin n → F, IsUniqueBadScalarWitnessCodeword dom k a u₀ u₁ γ c :=
  (badScalarWitnessCodewords_card_eq_one_iff_exists_isUniqueBadScalarWitnessCodeword
    dom k a u₀ u₁ γ).mp
    (badScalarWitnessCodewords_card_eq_one_of_uniqueDecoding
      dom k a d u₀ u₁ γ hγ hdist h2a)

open Classical in
/-- Any nonempty bad-scalar set in the strict unique-decoding regime refutes the no-unique route. -/
theorem not_noUniqueBadScalarWitness_of_nonempty_uniqueDecoding
    (dom : Fin n ↪ F) (k a d : ℕ) (u₀ u₁ : Fin n → F)
    (hbad : (lineBadScalars dom k a u₀ u₁).Nonempty)
    (hdist : ∀ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
      ∀ c' ∈ (rsCode dom k : Submodule F (Fin n → F)), c ≠ c' →
        d ≤ hammingDist c c')
    (h2a : Fintype.card (Fin n) + (Fintype.card (Fin n) - d) < 2 * a) :
    ¬ NoUniqueBadScalarWitness dom k a u₀ u₁ := by
  rcases hbad with ⟨γ, hγ⟩
  intro hno
  exact hno γ hγ
    (badScalarWitnessCodewords_card_eq_one_of_uniqueDecoding
      dom k a d u₀ u₁ γ hγ hdist h2a)

open Classical in
/-- The constructive second-witness route is impossible in a nonempty strict unique-decoding
regime. -/
theorem not_secondWitnessProperty_of_nonempty_uniqueDecoding
    (dom : Fin n ↪ F) (k a d : ℕ) (u₀ u₁ : Fin n → F)
    (hbad : (lineBadScalars dom k a u₀ u₁).Nonempty)
    (hdist : ∀ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
      ∀ c' ∈ (rsCode dom k : Submodule F (Fin n → F)), c ≠ c' →
        d ≤ hammingDist c c')
    (h2a : Fintype.card (Fin n) + (Fintype.card (Fin n) - d) < 2 * a) :
    ¬ BadScalarSecondWitnessProperty dom k a u₀ u₁ := by
  intro hsecond
  exact not_noUniqueBadScalarWitness_of_nonempty_uniqueDecoding
    dom k a d u₀ u₁ hbad hdist h2a
    ((noUniqueBadScalarWitness_iff_secondWitnessProperty dom k a u₀ u₁).mpr hsecond)

open Classical in
/-- Failure of the factor-two floor is equivalently an explicitly unique witness codeword. -/
theorem not_lineBadScalarMultiplicityFloor_two_iff_exists_uniqueWitnessCodeword
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) :
    ¬ LineBadScalarMultiplicityFloor dom k a u₀ u₁ 2 ↔
      ∃ γ ∈ lineBadScalars dom k a u₀ u₁,
        ∃ c : Fin n → F, IsUniqueBadScalarWitnessCodeword dom k a u₀ u₁ γ c := by
  constructor
  · intro hnot
    rcases (not_lineBadScalarMultiplicityFloor_two_iff_exists_unique_badScalarWitness
      dom k a u₀ u₁).mp hnot with ⟨γ, hγ, hcard⟩
    rcases (badScalarWitnessCodewords_card_eq_one_iff_exists_isUniqueBadScalarWitnessCodeword
      dom k a u₀ u₁ γ).mp hcard with ⟨c, hc⟩
    exact ⟨γ, hγ, c, hc⟩
  · rintro ⟨γ, hγ, c, hc⟩
    apply (not_lineBadScalarMultiplicityFloor_two_iff_exists_unique_badScalarWitness
      dom k a u₀ u₁).mpr
    refine ⟨γ, hγ, ?_⟩
    exact (badScalarWitnessCodewords_card_eq_one_iff_exists_isUniqueBadScalarWitnessCodeword
      dom k a u₀ u₁ γ).mpr ⟨c, hc⟩

open Classical in
/-- Negating `NoUniqueBadScalarWitness` produces an explicitly unique witness codeword. -/
theorem not_noUniqueBadScalarWitness_iff_exists_uniqueWitnessCodeword
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) :
    ¬ NoUniqueBadScalarWitness dom k a u₀ u₁ ↔
      ∃ γ ∈ lineBadScalars dom k a u₀ u₁,
        ∃ c : Fin n → F, IsUniqueBadScalarWitnessCodeword dom k a u₀ u₁ γ c := by
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro γ hγ hcard
    apply hnone
    rcases (badScalarWitnessCodewords_card_eq_one_iff_exists_isUniqueBadScalarWitnessCodeword
      dom k a u₀ u₁ γ).mp hcard with ⟨c, hc⟩
    exact ⟨γ, hγ, c, hc⟩
  · rintro ⟨γ, hγ, c, hc⟩ hno
    exact hno γ hγ
      ((badScalarWitnessCodewords_card_eq_one_iff_exists_isUniqueBadScalarWitnessCodeword
        dom k a u₀ u₁ γ).mpr ⟨c, hc⟩)

open Classical in
/-- Having no unique-witness bad scalar is exactly the `R = 2` multiplicity floor. -/
theorem lineBadScalarMultiplicityFloor_two_iff_noUniqueBadScalarWitness
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) :
    LineBadScalarMultiplicityFloor dom k a u₀ u₁ 2 ↔
      NoUniqueBadScalarWitness dom k a u₀ u₁ := by
  constructor
  · intro hfloor γ hγ hcard
    have hge := hfloor γ hγ
    omega
  · intro hno
    by_contra hnot
    rcases (not_lineBadScalarMultiplicityFloor_two_iff_exists_unique_badScalarWitness
      dom k a u₀ u₁).mp hnot with ⟨γ, hγ, hcard⟩
    exact hno γ hγ hcard

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
/-- Factor-two incidence discount from the no-unique-witness condition. -/
theorem
    lineBadScalars_card_le_puncturedZeroStratifiedLineWeight_div_two_of_noUniqueBadScalarWitness
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F)
    (hsafe : ZeroDirectionSafeLine dom k a u₀ u₁)
    (hno : NoUniqueBadScalarWitness dom k a u₀ u₁) :
    (lineBadScalars dom k a u₀ u₁).card
      ≤ puncturedZeroStratifiedLineWeight dom k a u₀ u₁ / 2 :=
  lineBadScalars_card_le_puncturedZeroStratifiedLineWeight_div_of_multiplicityFloor
    dom k a 2 u₀ u₁ (by omega) hsafe
    ((lineBadScalarMultiplicityFloor_two_iff_noUniqueBadScalarWitness
      dom k a u₀ u₁).mpr hno)

open Classical in
/-- Budget consumer for the factor-two no-unique-witness route. -/
theorem lineBadScalars_card_le_of_noUniqueBadScalarWitness_and_weight_div_two_le
    (dom : Fin n ↪ F) (k a B : ℕ) (u₀ u₁ : Fin n → F)
    (hsafe : ZeroDirectionSafeLine dom k a u₀ u₁)
    (hno : NoUniqueBadScalarWitness dom k a u₀ u₁)
    (hbudget : puncturedZeroStratifiedLineWeight dom k a u₀ u₁ / 2 ≤ B) :
    (lineBadScalars dom k a u₀ u₁).card ≤ B :=
  le_trans
    (lineBadScalars_card_le_puncturedZeroStratifiedLineWeight_div_two_of_noUniqueBadScalarWitness
      dom k a u₀ u₁ hsafe hno)
    hbudget

open Classical in
/-- Factor-two incidence discount from the constructive second-witness condition. -/
theorem lineBadScalars_card_le_weightDivTwo_of_secondWitness
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F)
    (hsafe : ZeroDirectionSafeLine dom k a u₀ u₁)
    (hsecond : BadScalarSecondWitnessProperty dom k a u₀ u₁) :
    (lineBadScalars dom k a u₀ u₁).card
      ≤ puncturedZeroStratifiedLineWeight dom k a u₀ u₁ / 2 :=
  lineBadScalars_card_le_puncturedZeroStratifiedLineWeight_div_two_of_noUniqueBadScalarWitness
    dom k a u₀ u₁ hsafe
    ((noUniqueBadScalarWitness_iff_secondWitnessProperty dom k a u₀ u₁).mpr hsecond)

open Classical in
/-- Budget consumer for the constructive second-witness route. -/
theorem lineBadScalars_card_le_of_secondWitness_and_weightDivTwo_le
    (dom : Fin n ↪ F) (k a B : ℕ) (u₀ u₁ : Fin n → F)
    (hsafe : ZeroDirectionSafeLine dom k a u₀ u₁)
    (hsecond : BadScalarSecondWitnessProperty dom k a u₀ u₁)
    (hbudget : puncturedZeroStratifiedLineWeight dom k a u₀ u₁ / 2 ≤ B) :
    (lineBadScalars dom k a u₀ u₁).card ≤ B :=
  le_trans
    (lineBadScalars_card_le_weightDivTwo_of_secondWitness
      dom k a u₀ u₁ hsafe hsecond)
    hbudget

open Classical in
/-- Bad scalars whose witness-codeword fiber is a singleton.  These are exactly the obstruction to
the factor-two incidence floor. -/
noncomputable def singletonBadScalars
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) : Finset F :=
  (lineBadScalars dom k a u₀ u₁).filter
    (fun γ => (badScalarWitnessCodewords dom k a u₀ u₁ γ).card = 1)

theorem mem_singletonBadScalars
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (γ : F) :
    γ ∈ singletonBadScalars dom k a u₀ u₁ ↔
      γ ∈ lineBadScalars dom k a u₀ u₁ ∧
        (badScalarWitnessCodewords dom k a u₀ u₁ γ).card = 1 := by
  classical
  rw [singletonBadScalars, Finset.mem_filter]

theorem singletonBadScalars_subset_lineBadScalars
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) :
    singletonBadScalars dom k a u₀ u₁ ⊆ lineBadScalars dom k a u₀ u₁ := by
  intro γ hγ
  exact ((mem_singletonBadScalars dom k a u₀ u₁ γ).mp hγ).1

open Classical in
/-- Singleton bad scalars are exactly the bad scalars with an explicitly unique witness codeword. -/
theorem mem_singletonBadScalars_iff_exists_uniqueWitnessCodeword
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (γ : F) :
    γ ∈ singletonBadScalars dom k a u₀ u₁ ↔
      γ ∈ lineBadScalars dom k a u₀ u₁ ∧
        ∃ c : Fin n → F, IsUniqueBadScalarWitnessCodeword dom k a u₀ u₁ γ c := by
  rw [mem_singletonBadScalars,
    badScalarWitnessCodewords_card_eq_one_iff_exists_isUniqueBadScalarWitnessCodeword]

/-- The number of singleton bad-scalar fibers.  This is the exact additive defect in the weakened
factor-two incidence bound. -/
noncomputable def singletonBadScalarDefect
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) : ℕ :=
  (singletonBadScalars dom k a u₀ u₁).card

open Classical in
/-- The singleton defect as an indicator sum over the bad scalars. -/
theorem singletonBadScalarDefect_eq_sum_indicator
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) :
    singletonBadScalarDefect dom k a u₀ u₁ =
      ∑ γ ∈ lineBadScalars dom k a u₀ u₁,
        if (badScalarWitnessCodewords dom k a u₀ u₁ γ).card = 1 then 1 else 0 := by
  rw [singletonBadScalarDefect, singletonBadScalars, Finset.card_filter]

/-- The singleton defect is bounded by the total number of bad scalars. -/
theorem singletonBadScalarDefect_le_lineBadScalars_card
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) :
    singletonBadScalarDefect dom k a u₀ u₁
      ≤ (lineBadScalars dom k a u₀ u₁).card := by
  classical
  rw [singletonBadScalarDefect, singletonBadScalars]
  exact Finset.card_filter_le _ _

open Classical in
/-- Zero singleton defect is exactly the no-unique-witness condition. -/
theorem singletonBadScalarDefect_eq_zero_iff_noUniqueBadScalarWitness
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) :
    singletonBadScalarDefect dom k a u₀ u₁ = 0 ↔
      NoUniqueBadScalarWitness dom k a u₀ u₁ := by
  constructor
  · intro hzero γ hγ hcard
    have hmem : γ ∈ singletonBadScalars dom k a u₀ u₁ :=
      (mem_singletonBadScalars dom k a u₀ u₁ γ).mpr ⟨hγ, hcard⟩
    have hpos : 0 < singletonBadScalarDefect dom k a u₀ u₁ := by
      rw [singletonBadScalarDefect]
      exact Finset.card_pos.mpr ⟨γ, hmem⟩
    omega
  · intro hno
    rw [singletonBadScalarDefect, Finset.card_eq_zero]
    ext γ
    constructor
    · intro hγ
      rcases (mem_singletonBadScalars dom k a u₀ u₁ γ).mp hγ with ⟨hbad, hcard⟩
      exact False.elim (hno γ hbad hcard)
    · intro hγ
      simp at hγ

open Classical in
/-- Zero singleton defect is equivalently the constructive second-witness condition. -/
theorem singletonBadScalarDefect_eq_zero_iff_secondWitnessProperty
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) :
    singletonBadScalarDefect dom k a u₀ u₁ = 0 ↔
      BadScalarSecondWitnessProperty dom k a u₀ u₁ := by
  rw [singletonBadScalarDefect_eq_zero_iff_noUniqueBadScalarWitness,
    noUniqueBadScalarWitness_iff_secondWitnessProperty]

open Classical in
/-- Positive singleton defect is exactly failure of the no-unique-witness condition. -/
theorem singletonBadScalarDefect_pos_iff_not_noUniqueBadScalarWitness
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) :
    0 < singletonBadScalarDefect dom k a u₀ u₁ ↔
      ¬ NoUniqueBadScalarWitness dom k a u₀ u₁ := by
  constructor
  · intro hpos hno
    have hzero :=
      (singletonBadScalarDefect_eq_zero_iff_noUniqueBadScalarWitness
        dom k a u₀ u₁).mpr hno
    omega
  · intro hnot
    by_contra hnotpos
    have hzero : singletonBadScalarDefect dom k a u₀ u₁ = 0 := by
      omega
    exact hnot
      ((singletonBadScalarDefect_eq_zero_iff_noUniqueBadScalarWitness
        dom k a u₀ u₁).mp hzero)

open Classical in
/-- Positive singleton defect is exactly a bad scalar with an explicitly unique witness codeword. -/
theorem singletonBadScalarDefect_pos_iff_exists_uniqueWitnessCodeword
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) :
    0 < singletonBadScalarDefect dom k a u₀ u₁ ↔
      ∃ γ ∈ lineBadScalars dom k a u₀ u₁,
        ∃ c : Fin n → F, IsUniqueBadScalarWitnessCodeword dom k a u₀ u₁ γ c := by
  rw [singletonBadScalarDefect_pos_iff_not_noUniqueBadScalarWitness,
    not_noUniqueBadScalarWitness_iff_exists_uniqueWitnessCodeword]

open Classical in
/-- In the strict unique-decoding regime, every bad scalar is a singleton bad scalar. -/
theorem singletonBadScalars_eq_lineBadScalars_of_uniqueDecoding
    (dom : Fin n ↪ F) (k a d : ℕ) (u₀ u₁ : Fin n → F)
    (hdist : ∀ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
      ∀ c' ∈ (rsCode dom k : Submodule F (Fin n → F)), c ≠ c' →
        d ≤ hammingDist c c')
    (h2a : Fintype.card (Fin n) + (Fintype.card (Fin n) - d) < 2 * a) :
    singletonBadScalars dom k a u₀ u₁ = lineBadScalars dom k a u₀ u₁ := by
  ext γ
  constructor
  · intro hγ
    exact singletonBadScalars_subset_lineBadScalars dom k a u₀ u₁ hγ
  · intro hγ
    exact (mem_singletonBadScalars dom k a u₀ u₁ γ).mpr
      ⟨hγ,
        badScalarWitnessCodewords_card_eq_one_of_uniqueDecoding
          dom k a d u₀ u₁ γ hγ hdist h2a⟩

open Classical in
/-- In the strict unique-decoding regime, the singleton defect is maximal: it is the whole
bad-scalar count. -/
theorem singletonBadScalarDefect_eq_lineBadScalars_card_of_uniqueDecoding
    (dom : Fin n ↪ F) (k a d : ℕ) (u₀ u₁ : Fin n → F)
    (hdist : ∀ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
      ∀ c' ∈ (rsCode dom k : Submodule F (Fin n → F)), c ≠ c' →
        d ≤ hammingDist c c')
    (h2a : Fintype.card (Fin n) + (Fintype.card (Fin n) - d) < 2 * a) :
    singletonBadScalarDefect dom k a u₀ u₁ =
      (lineBadScalars dom k a u₀ u₁).card := by
  rw [singletonBadScalarDefect,
    singletonBadScalars_eq_lineBadScalars_of_uniqueDecoding
      dom k a d u₀ u₁ hdist h2a]

open Classical in
/-- Scalars for which a fixed codeword is the unique witness to a singleton bad-scalar fiber. -/
noncomputable def codewordSingletonWitnessScalars
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (c : Fin n → F) : Finset F :=
  (lineBadScalars dom k a u₀ u₁).filter
    (fun γ => IsUniqueBadScalarWitnessCodeword dom k a u₀ u₁ γ c)

theorem mem_codewordSingletonWitnessScalars
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (c : Fin n → F) (γ : F) :
    γ ∈ codewordSingletonWitnessScalars dom k a u₀ u₁ c ↔
      γ ∈ lineBadScalars dom k a u₀ u₁ ∧
        IsUniqueBadScalarWitnessCodeword dom k a u₀ u₁ γ c := by
  classical
  rw [codewordSingletonWitnessScalars, Finset.mem_filter]

theorem codewordSingletonWitnessScalars_subset_lineBadScalars
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (c : Fin n → F) :
    codewordSingletonWitnessScalars dom k a u₀ u₁ c ⊆
      lineBadScalars dom k a u₀ u₁ := by
  intro γ hγ
  exact ((mem_codewordSingletonWitnessScalars dom k a u₀ u₁ c γ).mp hγ).1

open Classical in
/-- A codeword-singleton scalar is heavy for that codeword. -/
theorem codewordSingletonWitnessScalars_subset_codewordHeavyScalars
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (c : Fin n → F) :
    codewordSingletonWitnessScalars dom k a u₀ u₁ c ⊆
      codewordHeavyScalars (F := F) (n := n) a c u₀ u₁ := by
  intro γ hγ
  rcases (mem_codewordSingletonWitnessScalars dom k a u₀ u₁ c γ).mp hγ with
    ⟨_hbad, hcUnique⟩
  rw [mem_codewordHeavyScalars]
  exact ((mem_badScalarWitnessCodewords dom k a u₀ u₁ γ c).mp hcUnique.1).2

open Classical in
/-- Per-codeword singleton-witness scalars inherit the same support-denominator bound as all
heavy scalars for that codeword. -/
theorem codewordSingletonWitnessScalars_card_le_support_div_sub_zeroAgreement
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (c : Fin n → F)
    (hz : (directionZeroAgreementSet c u₀ u₁).card < a) :
    (codewordSingletonWitnessScalars dom k a u₀ u₁ c).card
      ≤ (directionSupportSet u₁).card /
        (a - (directionZeroAgreementSet c u₀ u₁).card) := by
  exact le_trans
    (Finset.card_le_card
      (codewordSingletonWitnessScalars_subset_codewordHeavyScalars
        dom k a u₀ u₁ c))
    (by
      simpa [codewordHeavyScalars] using
        (codeword_heavy_scalar_card_le_support_div_sub_zeroAgreement
          (F := F) (n := n) a c u₀ u₁ hz))

open Classical in
/-- Zero-safe line form of
`codewordSingletonWitnessScalars_card_le_support_div_sub_zeroAgreement`. -/
theorem codewordSingletonWitnessScalars_card_le_support_div_of_zeroSafe
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (c : Fin n → F)
    (hsafe : ZeroDirectionSafeLine dom k a u₀ u₁)
    (hc : c ∈ (rsCode dom k : Submodule F (Fin n → F))) :
    (codewordSingletonWitnessScalars dom k a u₀ u₁ c).card
      ≤ (directionSupportSet u₁).card /
        (a - (directionZeroAgreementSet c u₀ u₁).card) :=
  codewordSingletonWitnessScalars_card_le_support_div_sub_zeroAgreement
    dom k a u₀ u₁ c (hsafe c hc)

open Classical in
/-- A codeword-singleton scalar is a singleton bad scalar. -/
theorem codewordSingletonWitnessScalars_subset_singletonBadScalars
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) (c : Fin n → F) :
    codewordSingletonWitnessScalars dom k a u₀ u₁ c ⊆
      singletonBadScalars dom k a u₀ u₁ := by
  intro γ hγ
  rcases (mem_codewordSingletonWitnessScalars dom k a u₀ u₁ c γ).mp hγ with
    ⟨hbad, hcUnique⟩
  exact (mem_singletonBadScalars_iff_exists_uniqueWitnessCodeword
    dom k a u₀ u₁ γ).mpr ⟨hbad, c, hcUnique⟩

open Classical in
/-- If a codeword uniquely witnesses a scalar, then it appears somewhere on the line. -/
theorem lineAppearingCodewords_mem_of_isUniqueBadScalarWitnessCodeword
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) {γ : F} {c : Fin n → F}
    (hcUnique : IsUniqueBadScalarWitnessCodeword dom k a u₀ u₁ γ c) :
    c ∈ lineAppearingCodewords dom k a u₀ u₁ := by
  have hmem := (mem_badScalarWitnessCodewords dom k a u₀ u₁ γ c).mp hcUnique.1
  rw [lineAppearingCodewords, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, hmem.1, γ, hmem.2⟩

open Classical in
/-- Different codewords have disjoint singleton-witness scalar fibers. -/
theorem disjoint_codewordSingletonWitnessScalars_of_ne
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) {c c' : Fin n → F}
    (hne : c ≠ c') :
    Disjoint (codewordSingletonWitnessScalars dom k a u₀ u₁ c)
      (codewordSingletonWitnessScalars dom k a u₀ u₁ c') := by
  rw [Finset.disjoint_left]
  intro γ hγ hγ'
  rcases (mem_codewordSingletonWitnessScalars dom k a u₀ u₁ c γ).mp hγ with
    ⟨_hbad, hcUnique⟩
  rcases (mem_codewordSingletonWitnessScalars dom k a u₀ u₁ c' γ).mp hγ' with
    ⟨_hbad', hc'Unique⟩
  exact hne ((hcUnique.2 c' hc'Unique.1).symm)

open Classical in
/-- The per-codeword singleton-witness scalar fibers are pairwise disjoint. -/
theorem pairwiseDisjoint_codewordSingletonWitnessScalars
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) :
    (lineAppearingCodewords dom k a u₀ u₁ : Set (Fin n → F)).PairwiseDisjoint
      (fun c => codewordSingletonWitnessScalars dom k a u₀ u₁ c) := by
  intro c _hc c' _hc' hne
  exact disjoint_codewordSingletonWitnessScalars_of_ne dom k a u₀ u₁ hne

open Classical in
/-- Singleton bad scalars are covered by the per-codeword singleton-witness scalar fibers. -/
theorem singletonBadScalars_subset_biUnion_codewordSingletonWitnessScalars
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) :
    singletonBadScalars dom k a u₀ u₁ ⊆
      (lineAppearingCodewords dom k a u₀ u₁).biUnion
        (fun c => codewordSingletonWitnessScalars dom k a u₀ u₁ c) := by
  intro γ hγ
  rcases (mem_singletonBadScalars_iff_exists_uniqueWitnessCodeword
    dom k a u₀ u₁ γ).mp hγ with ⟨hbad, c, hcUnique⟩
  exact Finset.mem_biUnion.mpr
    ⟨c, lineAppearingCodewords_mem_of_isUniqueBadScalarWitnessCodeword
        dom k a u₀ u₁ hcUnique,
      (mem_codewordSingletonWitnessScalars dom k a u₀ u₁ c γ).mpr ⟨hbad, hcUnique⟩⟩

open Classical in
/-- The per-codeword singleton-witness scalar fibers exactly partition singleton bad scalars. -/
theorem biUnion_codewordSingletonWitnessScalars_eq_singletonBadScalars
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) :
    (lineAppearingCodewords dom k a u₀ u₁).biUnion
        (fun c => codewordSingletonWitnessScalars dom k a u₀ u₁ c) =
      singletonBadScalars dom k a u₀ u₁ := by
  ext γ
  constructor
  · intro hγ
    rcases Finset.mem_biUnion.mp hγ with ⟨c, _hcApp, hγc⟩
    exact codewordSingletonWitnessScalars_subset_singletonBadScalars
      dom k a u₀ u₁ c hγc
  · intro hγ
    exact singletonBadScalars_subset_biUnion_codewordSingletonWitnessScalars
      dom k a u₀ u₁ hγ

open Classical in
/-- Exact codeword-indexed decomposition of the singleton defect. -/
theorem singletonBadScalarDefect_eq_sum_codewordSingletonWitnessScalars
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) :
    singletonBadScalarDefect dom k a u₀ u₁ =
      ∑ c ∈ lineAppearingCodewords dom k a u₀ u₁,
        (codewordSingletonWitnessScalars dom k a u₀ u₁ c).card := by
  rw [singletonBadScalarDefect]
  rw [← biUnion_codewordSingletonWitnessScalars_eq_singletonBadScalars]
  exact Finset.card_biUnion (pairwiseDisjoint_codewordSingletonWitnessScalars dom k a u₀ u₁)

open Classical in
/-- Union-bound form of the singleton-defect problem, indexed by the unique witnessing codeword. -/
theorem singletonBadScalarDefect_le_sum_codewordSingletonWitnessScalars
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) :
    singletonBadScalarDefect dom k a u₀ u₁
      ≤ ∑ c ∈ lineAppearingCodewords dom k a u₀ u₁,
        (codewordSingletonWitnessScalars dom k a u₀ u₁ c).card :=
  le_of_eq (singletonBadScalarDefect_eq_sum_codewordSingletonWitnessScalars dom k a u₀ u₁)

open Classical in
/-- Singleton-defect bound from per-codeword singleton-witness scalar budgets. -/
theorem singletonBadScalarDefect_le_of_codewordSingletonWitnessScalars
    (dom : Fin n ↪ F) (k a B : ℕ) (u₀ u₁ : Fin n → F)
    (hbudget : ∀ c ∈ lineAppearingCodewords dom k a u₀ u₁,
      (codewordSingletonWitnessScalars dom k a u₀ u₁ c).card ≤ B) :
    singletonBadScalarDefect dom k a u₀ u₁
      ≤ (lineAppearingCodewords dom k a u₀ u₁).card * B := by
  refine le_trans
    (singletonBadScalarDefect_le_sum_codewordSingletonWitnessScalars dom k a u₀ u₁) ?_
  calc
    ∑ c ∈ lineAppearingCodewords dom k a u₀ u₁,
        (codewordSingletonWitnessScalars dom k a u₀ u₁ c).card
        ≤ ∑ _c ∈ lineAppearingCodewords dom k a u₀ u₁, B :=
          Finset.sum_le_sum hbudget
    _ = (lineAppearingCodewords dom k a u₀ u₁).card * B := by
      rw [Finset.sum_const, smul_eq_mul]

open Classical in
/-- Defect cap from a line-list cap and a uniform per-codeword singleton-scalar cap. -/
theorem singletonBadScalarDefect_le_of_lineListBudgeted_and_codewordSingletonWitnessScalars
    (dom : Fin n ↪ F) (k a L S : ℕ) (u₀ u₁ : Fin n → F)
    (hlist : LineListBudgeted dom k a u₀ u₁ L)
    (hperCode : ∀ c ∈ lineAppearingCodewords dom k a u₀ u₁,
      (codewordSingletonWitnessScalars dom k a u₀ u₁ c).card ≤ S) :
    singletonBadScalarDefect dom k a u₀ u₁ ≤ L * S :=
  le_trans
    (singletonBadScalarDefect_le_of_codewordSingletonWitnessScalars
      dom k a S u₀ u₁ hperCode)
    (Nat.mul_le_mul_right S hlist)

open Classical in
/-- Defect version of the factor-two incidence count.  Non-singleton bad scalars pay for two
incidences; singleton bad scalars pay for one incidence and one defect unit. -/
theorem lineBadScalars_card_mul_two_le_lineHeavyIncidences_card_add_singletonDefect
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) :
    (lineBadScalars dom k a u₀ u₁).card * 2
      ≤ (lineHeavyIncidences dom k a u₀ u₁).card
        + singletonBadScalarDefect dom k a u₀ u₁ := by
  rw [lineHeavyIncidences_card_eq_sum_badScalarWitnessCodewords,
    singletonBadScalarDefect_eq_sum_indicator]
  calc
    (lineBadScalars dom k a u₀ u₁).card * 2
        = ∑ _γ ∈ lineBadScalars dom k a u₀ u₁, 2 := by
          rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ γ ∈ lineBadScalars dom k a u₀ u₁,
          ((badScalarWitnessCodewords dom k a u₀ u₁ γ).card +
            (if (badScalarWitnessCodewords dom k a u₀ u₁ γ).card = 1 then 1 else 0)) := by
        refine Finset.sum_le_sum ?_
        intro γ hγ
        have hpos := badScalarWitnessCodewords_card_pos_of_mem_lineBadScalars
          dom k a u₀ u₁ hγ
        by_cases hcard : (badScalarWitnessCodewords dom k a u₀ u₁ γ).card = 1
        · simp [hcard]
        · have htwo : 2 ≤ (badScalarWitnessCodewords dom k a u₀ u₁ γ).card := by
            omega
          simpa [hcard] using htwo
    _ = (∑ γ ∈ lineBadScalars dom k a u₀ u₁,
          (badScalarWitnessCodewords dom k a u₀ u₁ γ).card) +
        ∑ γ ∈ lineBadScalars dom k a u₀ u₁,
          if (badScalarWitnessCodewords dom k a u₀ u₁ γ).card = 1 then 1 else 0 := by
        rw [Finset.sum_add_distrib]

open Classical in
/-- Defect version of the factor-two punctured-weight bound on safe lines. -/
theorem lineBadScalars_card_mul_two_le_puncturedWeight_add_singletonDefect
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F)
    (hsafe : ZeroDirectionSafeLine dom k a u₀ u₁) :
    (lineBadScalars dom k a u₀ u₁).card * 2
      ≤ puncturedZeroStratifiedLineWeight dom k a u₀ u₁
        + singletonBadScalarDefect dom k a u₀ u₁ :=
  le_trans
    (lineBadScalars_card_mul_two_le_lineHeavyIncidences_card_add_singletonDefect
      dom k a u₀ u₁)
    (Nat.add_le_add_right
      (lineHeavyIncidences_card_le_puncturedZeroStratifiedLineWeight
        dom k a u₀ u₁ hsafe)
      (singletonBadScalarDefect dom k a u₀ u₁))

open Classical in
/-- Division form of the singleton-defect incidence discount. -/
theorem lineBadScalars_card_le_puncturedWeight_add_singletonDefect_div_two
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F)
    (hsafe : ZeroDirectionSafeLine dom k a u₀ u₁) :
    (lineBadScalars dom k a u₀ u₁).card
      ≤ (puncturedZeroStratifiedLineWeight dom k a u₀ u₁
          + singletonBadScalarDefect dom k a u₀ u₁) / 2 :=
  (Nat.le_div_iff_mul_le (by omega : 1 ≤ 2)).mpr
    (lineBadScalars_card_mul_two_le_puncturedWeight_add_singletonDefect
      dom k a u₀ u₁ hsafe)

open Classical in
/-- Budget consumer for the singleton-defect route. -/
theorem lineBadScalars_card_le_of_weight_add_singletonDefect_le_two_mul
    (dom : Fin n ↪ F) (k a B : ℕ) (u₀ u₁ : Fin n → F)
    (hsafe : ZeroDirectionSafeLine dom k a u₀ u₁)
    (hbudget : puncturedZeroStratifiedLineWeight dom k a u₀ u₁
        + singletonBadScalarDefect dom k a u₀ u₁ ≤ 2 * B) :
    (lineBadScalars dom k a u₀ u₁).card ≤ B := by
  have htwice :
      (lineBadScalars dom k a u₀ u₁).card * 2 ≤ 2 * B :=
    le_trans
      (lineBadScalars_card_mul_two_le_puncturedWeight_add_singletonDefect
        dom k a u₀ u₁ hsafe)
      hbudget
  omega

open Classical in
/-- Bad-scalar budget from a per-codeword singleton-scalar cap and combined arithmetic. -/
theorem lineBadScalars_card_le_of_weight_add_codewordSingletonBudget_le_two_mul
    (dom : Fin n ↪ F) (k a S B : ℕ) (u₀ u₁ : Fin n → F)
    (hsafe : ZeroDirectionSafeLine dom k a u₀ u₁)
    (hperCode : ∀ c ∈ lineAppearingCodewords dom k a u₀ u₁,
      (codewordSingletonWitnessScalars dom k a u₀ u₁ c).card ≤ S)
    (hbudget : puncturedZeroStratifiedLineWeight dom k a u₀ u₁
        + (lineAppearingCodewords dom k a u₀ u₁).card * S ≤ 2 * B) :
    (lineBadScalars dom k a u₀ u₁).card ≤ B :=
  lineBadScalars_card_le_of_weight_add_singletonDefect_le_two_mul
    dom k a B u₀ u₁ hsafe
    (le_trans
      (Nat.add_le_add_left
        (singletonBadScalarDefect_le_of_codewordSingletonWitnessScalars
          dom k a S u₀ u₁ hperCode)
        (puncturedZeroStratifiedLineWeight dom k a u₀ u₁))
      hbudget)

open Classical in
/-- Bad-scalar budget from a line-list cap, per-codeword singleton-scalar cap, and combined
arithmetic. -/
theorem lineBadScalars_card_le_of_weight_add_lineListSingletonBudget_le_two_mul
    (dom : Fin n ↪ F) (k a L S B : ℕ) (u₀ u₁ : Fin n → F)
    (hsafe : ZeroDirectionSafeLine dom k a u₀ u₁)
    (hlist : LineListBudgeted dom k a u₀ u₁ L)
    (hperCode : ∀ c ∈ lineAppearingCodewords dom k a u₀ u₁,
      (codewordSingletonWitnessScalars dom k a u₀ u₁ c).card ≤ S)
    (hbudget : puncturedZeroStratifiedLineWeight dom k a u₀ u₁ + L * S ≤ 2 * B) :
    (lineBadScalars dom k a u₀ u₁).card ≤ B :=
  lineBadScalars_card_le_of_weight_add_singletonDefect_le_two_mul
    dom k a B u₀ u₁ hsafe
    (le_trans
      (Nat.add_le_add_left
        (singletonBadScalarDefect_le_of_lineListBudgeted_and_codewordSingletonWitnessScalars
          dom k a L S u₀ u₁ hlist hperCode)
        (puncturedZeroStratifiedLineWeight dom k a u₀ u₁))
      hbudget)

open Classical in
/-- Failure of the named no-unique-witness condition is exactly a bad scalar with one witnessing
codeword. -/
theorem not_noUniqueBadScalarWitness_iff_exists_unique_badScalarWitness
    (dom : Fin n ↪ F) (k a : ℕ) (u₀ u₁ : Fin n → F) :
    ¬ NoUniqueBadScalarWitness dom k a u₀ u₁ ↔
      ∃ γ ∈ lineBadScalars dom k a u₀ u₁,
        (badScalarWitnessCodewords dom k a u₀ u₁ γ).card = 1 := by
  rw [← lineBadScalarMultiplicityFloor_two_iff_noUniqueBadScalarWitness]
  exact not_lineBadScalarMultiplicityFloor_two_iff_exists_unique_badScalarWitness
    dom k a u₀ u₁

open Classical in
/-- Scanner form for the factor-two route.  If the line is safe and the half-weight budget fits,
then any failure of the bad-scalar budget forces a unique-witness bad scalar. -/
theorem exists_unique_badScalarWitness_of_not_lineBadScalars_card_le
    (dom : Fin n ↪ F) (k a B : ℕ) (u₀ u₁ : Fin n → F)
    (hsafe : ZeroDirectionSafeLine dom k a u₀ u₁)
    (hbudget : puncturedZeroStratifiedLineWeight dom k a u₀ u₁ / 2 ≤ B)
    (hnot : ¬ (lineBadScalars dom k a u₀ u₁).card ≤ B) :
    ∃ γ ∈ lineBadScalars dom k a u₀ u₁,
      (badScalarWitnessCodewords dom k a u₀ u₁ γ).card = 1 := by
  by_contra hnone
  apply hnot
  have hno : NoUniqueBadScalarWitness dom k a u₀ u₁ := by
    intro γ hγ hcard
    exact hnone ⟨γ, hγ, hcard⟩
  exact lineBadScalars_card_le_of_noUniqueBadScalarWitness_and_weight_div_two_le
    dom k a B u₀ u₁ hsafe hno hbudget

open Classical in
/-- Stronger scanner form for the factor-two route, returning the actual unique witness codeword. -/
theorem exists_uniqueWitnessCodeword_of_not_lineBadScalars_card_le
    (dom : Fin n ↪ F) (k a B : ℕ) (u₀ u₁ : Fin n → F)
    (hsafe : ZeroDirectionSafeLine dom k a u₀ u₁)
    (hbudget : puncturedZeroStratifiedLineWeight dom k a u₀ u₁ / 2 ≤ B)
    (hnot : ¬ (lineBadScalars dom k a u₀ u₁).card ≤ B) :
    ∃ γ ∈ lineBadScalars dom k a u₀ u₁,
      ∃ c : Fin n → F, IsUniqueBadScalarWitnessCodeword dom k a u₀ u₁ γ c := by
  rcases exists_unique_badScalarWitness_of_not_lineBadScalars_card_le
    dom k a B u₀ u₁ hsafe hbudget hnot with ⟨γ, hγ, hcard⟩
  rcases (badScalarWitnessCodewords_card_eq_one_iff_exists_isUniqueBadScalarWitnessCodeword
    dom k a u₀ u₁ γ).mp hcard with ⟨c, hc⟩
  exact ⟨γ, hγ, c, hc⟩

/-- Uniform no-unique-witness condition on the large-zero safe residual branch. -/
def UniformLargeZeroSafeNoUniqueBadScalarWitness
    (dom : Fin n ↪ F) (k a : ℕ) : Prop :=
  ∀ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
    ZeroDirectionSafeLine dom k a u₀ u₁ →
      NoUniqueBadScalarWitness dom k a u₀ u₁

/-- Uniform constructive second-witness condition on the large-zero safe residual branch. -/
def UniformLargeZeroSafeSecondWitnessProperty
    (dom : Fin n ↪ F) (k a : ℕ) : Prop :=
  ∀ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
    ZeroDirectionSafeLine dom k a u₀ u₁ →
      BadScalarSecondWitnessProperty dom k a u₀ u₁

open Classical in
/-- The uniform no-unique-witness branch is exactly the uniform constructive second-witness
branch. -/
theorem uniformLargeZeroSafeNoUnique_iff_secondWitnessProperty
    (dom : Fin n ↪ F) (k a : ℕ) :
    UniformLargeZeroSafeNoUniqueBadScalarWitness dom k a ↔
      UniformLargeZeroSafeSecondWitnessProperty dom k a := by
  constructor
  · intro hno u₀ u₁ hnotEligible hsafe
    exact (noUniqueBadScalarWitness_iff_secondWitnessProperty
      dom k a u₀ u₁).mp (hno u₀ u₁ hnotEligible hsafe)
  · intro hsecond u₀ u₁ hnotEligible hsafe
    exact (noUniqueBadScalarWitness_iff_secondWitnessProperty
      dom k a u₀ u₁).mpr (hsecond u₀ u₁ hnotEligible hsafe)

/-- Uniform zero singleton-defect condition on the large-zero safe residual branch. -/
def UniformLargeZeroSafeSingletonDefectZero
    (dom : Fin n ↪ F) (k a : ℕ) : Prop :=
  ∀ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
    ZeroDirectionSafeLine dom k a u₀ u₁ →
      singletonBadScalarDefect dom k a u₀ u₁ = 0

open Classical in
/-- The uniform no-unique-witness branch is exactly zero singleton defect on every large-zero safe
line. -/
theorem uniformLargeZeroSafeNoUnique_iff_singletonDefectZero
    (dom : Fin n ↪ F) (k a : ℕ) :
    UniformLargeZeroSafeNoUniqueBadScalarWitness dom k a ↔
      UniformLargeZeroSafeSingletonDefectZero dom k a := by
  constructor
  · intro hno u₀ u₁ hnotEligible hsafe
    exact (singletonBadScalarDefect_eq_zero_iff_noUniqueBadScalarWitness
      dom k a u₀ u₁).mpr (hno u₀ u₁ hnotEligible hsafe)
  · intro hzero u₀ u₁ hnotEligible hsafe
    exact (singletonBadScalarDefect_eq_zero_iff_noUniqueBadScalarWitness
      dom k a u₀ u₁).mp (hzero u₀ u₁ hnotEligible hsafe)

open Classical in
/-- The uniform constructive second-witness branch is exactly zero singleton defect on every
large-zero safe line. -/
theorem uniformLargeZeroSafeSecondWitness_iff_singletonDefectZero
    (dom : Fin n ↪ F) (k a : ℕ) :
    UniformLargeZeroSafeSecondWitnessProperty dom k a ↔
      UniformLargeZeroSafeSingletonDefectZero dom k a := by
  rw [← uniformLargeZeroSafeNoUnique_iff_secondWitnessProperty,
    uniformLargeZeroSafeNoUnique_iff_singletonDefectZero]

/-- Uniform half-weight arithmetic budget for the factor-two multiplicity route on the large-zero
safe residual branch. -/
def UniformLargeZeroSafePuncturedWeightDivTwoBudgeted
    (dom : Fin n ↪ F) (k a B : ℕ) : Prop :=
  ∀ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
    ZeroDirectionSafeLine dom k a u₀ u₁ →
      puncturedZeroStratifiedLineWeight dom k a u₀ u₁ / 2 ≤ B

/-- Uniform combined arithmetic budget for the singleton-defect route on the large-zero safe
residual branch. -/
def UniformLargeZeroSafeWeightPlusSingletonDefectBudgeted
    (dom : Fin n ↪ F) (k a B : ℕ) : Prop :=
  ∀ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
    ZeroDirectionSafeLine dom k a u₀ u₁ →
      puncturedZeroStratifiedLineWeight dom k a u₀ u₁
        + singletonBadScalarDefect dom k a u₀ u₁ ≤ 2 * B

/-- Uniform cap on singleton bad scalars uniquely witnessed by any one appearing codeword on the
large-zero safe branch. -/
def UniformLargeZeroSafeCodewordSingletonBudgeted
    (dom : Fin n ↪ F) (k a S : ℕ) : Prop :=
  ∀ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
    ZeroDirectionSafeLine dom k a u₀ u₁ →
      ∀ c ∈ lineAppearingCodewords dom k a u₀ u₁,
        (codewordSingletonWitnessScalars dom k a u₀ u₁ c).card ≤ S

/-- Combined arithmetic budget using the actual number of appearing codewords and a uniform
per-codeword singleton cap. -/
def UniformLargeZeroSafeWeightPlusCodewordSingletonBudgeted
    (dom : Fin n ↪ F) (k a B S : ℕ) : Prop :=
  ∀ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
    ZeroDirectionSafeLine dom k a u₀ u₁ →
      puncturedZeroStratifiedLineWeight dom k a u₀ u₁
        + (lineAppearingCodewords dom k a u₀ u₁).card * S ≤ 2 * B

/-- Uniform line-list cap on the large-zero safe branch.  This is separate from
`UniformSupportLineListBudgeted`, which only controls support-eligible directions. -/
def UniformLargeZeroSafeLineListBudgeted
    (dom : Fin n ↪ F) (k a L : ℕ) : Prop :=
  ∀ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
    ZeroDirectionSafeLine dom k a u₀ u₁ →
      LineListBudgeted dom k a u₀ u₁ L

/-- Combined arithmetic budget using a large-zero-safe line-list cap and a per-codeword singleton
cap. -/
def UniformLargeZeroSafeWeightPlusLineListSingletonBudgeted
    (dom : Fin n ↪ F) (k a L S B : ℕ) : Prop :=
  ∀ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ →
    ZeroDirectionSafeLine dom k a u₀ u₁ →
      puncturedZeroStratifiedLineWeight dom k a u₀ u₁ + L * S ≤ 2 * B

open Classical in
/-- Exact failure form for the uniform per-codeword singleton cap on the large-zero safe branch. -/
theorem not_uniformLargeZeroSafeCodewordSingletonBudgeted_iff_exists_card_gt
    (dom : Fin n ↪ F) (k a S : ℕ) :
    (¬ UniformLargeZeroSafeCodewordSingletonBudgeted dom k a S) ↔
      ∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
        ZeroDirectionSafeLine dom k a u₀ u₁ ∧
          ∃ c ∈ lineAppearingCodewords dom k a u₀ u₁,
            S < (codewordSingletonWitnessScalars dom k a u₀ u₁ c).card := by
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
/-- Exact failure form for the large-zero-safe line-list cap. -/
theorem not_uniformLargeZeroSafeLineListBudgeted_iff_exists_lineAppearing_gt
    (dom : Fin n ↪ F) (k a L : ℕ) :
    (¬ UniformLargeZeroSafeLineListBudgeted dom k a L) ↔
      ∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
        ZeroDirectionSafeLine dom k a u₀ u₁ ∧
          L < (lineAppearingCodewords dom k a u₀ u₁).card := by
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro u₀ u₁ hnotEligible hsafe
    unfold LineListBudgeted
    by_contra hle
    exact hnone ⟨u₀, u₁, hnotEligible, hsafe, Nat.lt_of_not_ge hle⟩
  · rintro ⟨u₀, u₁, hnotEligible, hsafe, hgt⟩ hbudget
    exact (not_lt_of_ge (hbudget u₀ u₁ hnotEligible hsafe)) hgt

open Classical in
/-- If a uniform per-codeword singleton cap fails, then the usual support-denominator bound is
already above that cap for a concrete appearing codeword. -/
theorem
    exists_largeZero_safe_codewordSingletonSupportDiv_gt_of_not_uniformSingletonBudgeted
    (dom : Fin n ↪ F) (k a S : ℕ)
    (hnot : ¬ UniformLargeZeroSafeCodewordSingletonBudgeted dom k a S) :
    ∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
      ZeroDirectionSafeLine dom k a u₀ u₁ ∧
        ∃ c ∈ lineAppearingCodewords dom k a u₀ u₁,
          S < (directionSupportSet u₁).card /
            (a - (directionZeroAgreementSet c u₀ u₁).card) := by
  rcases
      (not_uniformLargeZeroSafeCodewordSingletonBudgeted_iff_exists_card_gt
        dom k a S).mp hnot with
    ⟨u₀, u₁, hnotEligible, hsafe, c, hc, hgt⟩
  refine ⟨u₀, u₁, hnotEligible, hsafe, c, hc, ?_⟩
  have hcCode : c ∈ (rsCode dom k : Submodule F (Fin n → F)) := by
    rw [lineAppearingCodewords, Finset.mem_filter] at hc
    exact hc.2.1
  exact lt_of_lt_of_le hgt
    (codewordSingletonWitnessScalars_card_le_support_div_of_zeroSafe
      dom k a u₀ u₁ c hsafe hcCode)

open Classical in
/-- The no-unique-witness condition plus the half punctured-weight budget discharges the large-zero
safe residual. -/
theorem
    largeZeroSafeLineBadScalarsBudgeted_of_noUnique_and_weightDivTwo
    (dom : Fin n ↪ F) (k a B : ℕ)
    (hno : UniformLargeZeroSafeNoUniqueBadScalarWitness dom k a)
    (hbudget : UniformLargeZeroSafePuncturedWeightDivTwoBudgeted dom k a B) :
    LargeZeroSafeLineBadScalarsBudgeted dom k a B := by
  intro u₀ u₁ hnotEligible hsafe
  exact lineBadScalars_card_le_of_noUniqueBadScalarWitness_and_weight_div_two_le
    dom k a B u₀ u₁ hsafe
    (hno u₀ u₁ hnotEligible hsafe)
    (hbudget u₀ u₁ hnotEligible hsafe)

open Classical in
/-- The constructive second-witness condition plus the half punctured-weight budget discharges the
large-zero safe residual. -/
theorem
    largeZeroSafeLineBadScalarsBudgeted_of_secondWitness_and_weightDivTwo
    (dom : Fin n ↪ F) (k a B : ℕ)
    (hsecond : UniformLargeZeroSafeSecondWitnessProperty dom k a)
    (hbudget : UniformLargeZeroSafePuncturedWeightDivTwoBudgeted dom k a B) :
    LargeZeroSafeLineBadScalarsBudgeted dom k a B :=
  largeZeroSafeLineBadScalarsBudgeted_of_noUnique_and_weightDivTwo
    dom k a B
    ((uniformLargeZeroSafeNoUnique_iff_secondWitnessProperty dom k a).mpr hsecond)
    hbudget

/-- Production wrapper for the factor-two no-unique-witness route.  The support-eligible branch is
handled by the existing support-adjusted line-list budget; the large-zero safe branch uses
no-unique witnesses plus the half punctured-weight arithmetic budget. -/
theorem
    uniformLineBadScalarsBudgeted_of_supportAdjusted_and_noUniqueWeightDivTwo
    (dom : Fin n ↪ F) (k a L B : ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hno : UniformLargeZeroSafeNoUniqueBadScalarWitness dom k a)
    (hbudget : UniformLargeZeroSafePuncturedWeightDivTwoBudgeted dom k a B) :
    UniformLineBadScalarsBudgeted dom k a B :=
  uniformLineBadScalarsBudgeted_of_supportAdjustedBudgetFits_and_largeZeroSafe
    dom k a L B hSupport hFits hZeroSafe
    (largeZeroSafeLineBadScalarsBudgeted_of_noUnique_and_weightDivTwo
      dom k a B hno hbudget)

open Classical in
/-- Production wrapper for the constructive second-witness route. -/
theorem
    uniformLineBadScalarsBudgeted_of_supportAdjusted_and_secondWitnessWeightDivTwo
    (dom : Fin n ↪ F) (k a L B : ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hsecond : UniformLargeZeroSafeSecondWitnessProperty dom k a)
    (hbudget : UniformLargeZeroSafePuncturedWeightDivTwoBudgeted dom k a B) :
    UniformLineBadScalarsBudgeted dom k a B :=
  uniformLineBadScalarsBudgeted_of_supportAdjusted_and_noUniqueWeightDivTwo
    dom k a L B hSupport hFits hZeroSafe
    ((uniformLargeZeroSafeNoUnique_iff_secondWitnessProperty dom k a).mpr hsecond)
    hbudget

open Classical in
/-- The combined punctured-weight plus singleton-defect budget discharges the large-zero safe
residual. -/
theorem largeZeroSafeLineBadScalarsBudgeted_of_singletonDefectBudget
    (dom : Fin n ↪ F) (k a B : ℕ)
    (hbudget : UniformLargeZeroSafeWeightPlusSingletonDefectBudgeted dom k a B) :
    LargeZeroSafeLineBadScalarsBudgeted dom k a B := by
  intro u₀ u₁ hnotEligible hsafe
  exact lineBadScalars_card_le_of_weight_add_singletonDefect_le_two_mul
    dom k a B u₀ u₁ hsafe (hbudget u₀ u₁ hnotEligible hsafe)

/-- Production wrapper for the singleton-defect route.  Instead of proving all singleton fibers
absent, it is enough to bound their total defect together with the punctured line weight. -/
theorem uniformLineBadScalarsBudgeted_of_supportAdjusted_and_singletonDefectBudget
    (dom : Fin n ↪ F) (k a L B : ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hbudget : UniformLargeZeroSafeWeightPlusSingletonDefectBudgeted dom k a B) :
    UniformLineBadScalarsBudgeted dom k a B :=
  uniformLineBadScalarsBudgeted_of_supportAdjustedBudgetFits_and_largeZeroSafe
    dom k a L B hSupport hFits hZeroSafe
    (largeZeroSafeLineBadScalarsBudgeted_of_singletonDefectBudget
      dom k a B hbudget)

open Classical in
/-- A per-codeword singleton cap plus the direct appearing-codeword arithmetic budget discharges
the large-zero safe residual. -/
theorem largeZeroSafeLineBadScalarsBudgeted_of_codewordSingletonBudget
    (dom : Fin n ↪ F) (k a S B : ℕ)
    (hperCode : UniformLargeZeroSafeCodewordSingletonBudgeted dom k a S)
    (hbudget : UniformLargeZeroSafeWeightPlusCodewordSingletonBudgeted dom k a B S) :
    LargeZeroSafeLineBadScalarsBudgeted dom k a B := by
  intro u₀ u₁ hnotEligible hsafe
  exact lineBadScalars_card_le_of_weight_add_codewordSingletonBudget_le_two_mul
    dom k a S B u₀ u₁ hsafe
    (hperCode u₀ u₁ hnotEligible hsafe)
    (hbudget u₀ u₁ hnotEligible hsafe)

/-- Production wrapper for the direct per-codeword singleton-cap route. -/
theorem uniformLineBadScalarsBudgeted_of_supportAdjusted_and_codewordSingletonBudget
    (dom : Fin n ↪ F) (k a L S B : ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hperCode : UniformLargeZeroSafeCodewordSingletonBudgeted dom k a S)
    (hbudget : UniformLargeZeroSafeWeightPlusCodewordSingletonBudgeted dom k a B S) :
    UniformLineBadScalarsBudgeted dom k a B :=
  uniformLineBadScalarsBudgeted_of_supportAdjustedBudgetFits_and_largeZeroSafe
    dom k a L B hSupport hFits hZeroSafe
    (largeZeroSafeLineBadScalarsBudgeted_of_codewordSingletonBudget
      dom k a S B hperCode hbudget)

open Classical in
/-- A large-zero-safe line-list cap, a per-codeword singleton cap, and the combined arithmetic
budget discharge the large-zero safe residual. -/
theorem largeZeroSafeLineBadScalarsBudgeted_of_lineListSingletonBudget
    (dom : Fin n ↪ F) (k a L S B : ℕ)
    (hlist : UniformLargeZeroSafeLineListBudgeted dom k a L)
    (hperCode : UniformLargeZeroSafeCodewordSingletonBudgeted dom k a S)
    (hbudget : UniformLargeZeroSafeWeightPlusLineListSingletonBudgeted dom k a L S B) :
    LargeZeroSafeLineBadScalarsBudgeted dom k a B := by
  intro u₀ u₁ hnotEligible hsafe
  exact lineBadScalars_card_le_of_weight_add_lineListSingletonBudget_le_two_mul
    dom k a L S B u₀ u₁ hsafe
    (hlist u₀ u₁ hnotEligible hsafe)
    (hperCode u₀ u₁ hnotEligible hsafe)
    (hbudget u₀ u₁ hnotEligible hsafe)

/-- Production wrapper for the line-list plus per-codeword singleton-cap route. -/
theorem uniformLineBadScalarsBudgeted_of_supportAdjusted_and_lineListSingletonBudget
    (dom : Fin n ↪ F) (k a L Lzero S B : ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hlist : UniformLargeZeroSafeLineListBudgeted dom k a Lzero)
    (hperCode : UniformLargeZeroSafeCodewordSingletonBudgeted dom k a S)
    (hbudget :
      UniformLargeZeroSafeWeightPlusLineListSingletonBudgeted dom k a Lzero S B) :
    UniformLineBadScalarsBudgeted dom k a B :=
  uniformLineBadScalarsBudgeted_of_supportAdjustedBudgetFits_and_largeZeroSafe
    dom k a L B hSupport hFits hZeroSafe
    (largeZeroSafeLineBadScalarsBudgeted_of_lineListSingletonBudget
      dom k a Lzero S B hlist hperCode hbudget)

open Classical in
/-- Converse scanner for the singleton-defect route.  If support, zero-safety, and support
arithmetic are fixed, any failed uniform bad-scalar budget must violate the combined
punctured-weight plus singleton-defect budget on a large-zero safe line. -/
theorem
    exists_largeZero_safe_singletonDefectBudgetFailure_of_not_uniformLineBadScalarsBudgeted
    (dom : Fin n ↪ F) (k a L B : ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hnot : ¬ UniformLineBadScalarsBudgeted dom k a B) :
    ∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
      ZeroDirectionSafeLine dom k a u₀ u₁ ∧
        ¬ puncturedZeroStratifiedLineWeight dom k a u₀ u₁
          + singletonBadScalarDefect dom k a u₀ u₁ ≤ 2 * B := by
  by_contra hnone
  have hbudget : UniformLargeZeroSafeWeightPlusSingletonDefectBudgeted dom k a B := by
    intro u₀ u₁ hnotEligible hsafe
    by_contra hfail
    exact hnone ⟨u₀, u₁, hnotEligible, hsafe, hfail⟩
  exact hnot
    (uniformLineBadScalarsBudgeted_of_supportAdjusted_and_singletonDefectBudget
      dom k a L B hSupport hFits hZeroSafe hbudget)

open Classical in
/-- Scanner for the direct per-codeword singleton-cap route.  If the per-codeword cap is fixed,
failed production exposes failure of the direct appearing-codeword arithmetic budget. -/
theorem exists_largeZero_safe_codewordSingletonBudgetFailure_of_not_uniformLineBadScalarsBudgeted
    (dom : Fin n ↪ F) (k a L S B : ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hperCode : UniformLargeZeroSafeCodewordSingletonBudgeted dom k a S)
    (hnot : ¬ UniformLineBadScalarsBudgeted dom k a B) :
    ∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
      ZeroDirectionSafeLine dom k a u₀ u₁ ∧
        ¬ puncturedZeroStratifiedLineWeight dom k a u₀ u₁
          + (lineAppearingCodewords dom k a u₀ u₁).card * S ≤ 2 * B := by
  by_contra hnone
  have hbudget : UniformLargeZeroSafeWeightPlusCodewordSingletonBudgeted dom k a B S := by
    intro u₀ u₁ hnotEligible hsafe
    by_contra hfail
    exact hnone ⟨u₀, u₁, hnotEligible, hsafe, hfail⟩
  exact hnot
    (uniformLineBadScalarsBudgeted_of_supportAdjusted_and_codewordSingletonBudget
      dom k a L S B hSupport hFits hZeroSafe hperCode hbudget)

open Classical in
/-- Complementary scanner for the direct per-codeword singleton-cap route.  If the direct
appearing-codeword arithmetic budget is fixed, failed production exposes a concrete appearing
codeword whose singleton-witness scalar fiber exceeds the proposed cap. -/
theorem exists_largeZero_safe_codewordSingletonCap_gt_of_not_uniformLineBadScalarsBudgeted
    (dom : Fin n ↪ F) (k a L S B : ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hbudget : UniformLargeZeroSafeWeightPlusCodewordSingletonBudgeted dom k a B S)
    (hnot : ¬ UniformLineBadScalarsBudgeted dom k a B) :
    ∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
      ZeroDirectionSafeLine dom k a u₀ u₁ ∧
        ∃ c ∈ lineAppearingCodewords dom k a u₀ u₁,
          S < (codewordSingletonWitnessScalars dom k a u₀ u₁ c).card := by
  by_contra hnone
  have hperCode : UniformLargeZeroSafeCodewordSingletonBudgeted dom k a S := by
    intro u₀ u₁ hnotEligible hsafe c hc
    exact le_of_not_gt
      (fun hgt => hnone ⟨u₀, u₁, hnotEligible, hsafe, c, hc, hgt⟩)
  exact hnot
    (uniformLineBadScalarsBudgeted_of_supportAdjusted_and_codewordSingletonBudget
      dom k a L S B hSupport hFits hZeroSafe hperCode hbudget)

open Classical in
/-- Combined scanner for the direct per-codeword singleton route.  Once the support branch,
support arithmetic, and zero-direction safety are fixed, failed production forces either combined
appearing-codeword arithmetic failure or a concrete appearing codeword exceeding the proposed
singleton-witness cap. -/
theorem exists_largeZero_safe_codewordSingletonRouteFailure_of_not_uniformLineBadScalarsBudgeted
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
            S < (codewordSingletonWitnessScalars dom k a u₀ u₁ c).card) := by
  by_cases hperCode : UniformLargeZeroSafeCodewordSingletonBudgeted dom k a S
  · rcases
      exists_largeZero_safe_codewordSingletonBudgetFailure_of_not_uniformLineBadScalarsBudgeted
        dom k a L S B hSupport hFits hZeroSafe hperCode hnot with
      ⟨u₀, u₁, hnotEligible, hsafe, hfail⟩
    exact ⟨u₀, u₁, hnotEligible, hsafe, Or.inl hfail⟩
  · rcases
      (not_uniformLargeZeroSafeCodewordSingletonBudgeted_iff_exists_card_gt
        dom k a S).mp hperCode with
      ⟨u₀, u₁, hnotEligible, hsafe, c, hc, hgt⟩
    exact ⟨u₀, u₁, hnotEligible, hsafe, Or.inr ⟨c, hc, hgt⟩⟩

open Classical in
/-- Support-denominator form of the direct per-codeword singleton-route scanner.  If the
per-codeword route fails and the combined arithmetic side is not the reason, then some appearing
codeword has support-denominator capacity above the proposed singleton cap. -/
theorem
    exists_largeZero_safe_codewordSingletonRouteSupportDivFailure
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
            S < (directionSupportSet u₁).card /
              (a - (directionZeroAgreementSet c u₀ u₁).card)) := by
  by_cases hperCode : UniformLargeZeroSafeCodewordSingletonBudgeted dom k a S
  · rcases
      exists_largeZero_safe_codewordSingletonBudgetFailure_of_not_uniformLineBadScalarsBudgeted
        dom k a L S B hSupport hFits hZeroSafe hperCode hnot with
      ⟨u₀, u₁, hnotEligible, hsafe, hfail⟩
    exact ⟨u₀, u₁, hnotEligible, hsafe, Or.inl hfail⟩
  · rcases
      exists_largeZero_safe_codewordSingletonSupportDiv_gt_of_not_uniformSingletonBudgeted
        dom k a S hperCode with
      ⟨u₀, u₁, hnotEligible, hsafe, c, hc, hgt⟩
    exact ⟨u₀, u₁, hnotEligible, hsafe, Or.inr ⟨c, hc, hgt⟩⟩

open Classical in
/-- Scanner for the line-list singleton route.  With the large-zero-safe line-list and per-codeword
caps fixed, failed production exposes failure of the `puncturedWeight + Lzero * S` arithmetic. -/
theorem exists_largeZero_safe_lineListSingletonBudgetFailure_of_not_uniformLineBadScalarsBudgeted
    (dom : Fin n ↪ F) (k a L Lzero S B : ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hlist : UniformLargeZeroSafeLineListBudgeted dom k a Lzero)
    (hperCode : UniformLargeZeroSafeCodewordSingletonBudgeted dom k a S)
    (hnot : ¬ UniformLineBadScalarsBudgeted dom k a B) :
    ∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
      ZeroDirectionSafeLine dom k a u₀ u₁ ∧
        ¬ puncturedZeroStratifiedLineWeight dom k a u₀ u₁ + Lzero * S ≤ 2 * B := by
  by_contra hnone
  have hbudget :
      UniformLargeZeroSafeWeightPlusLineListSingletonBudgeted dom k a Lzero S B := by
    intro u₀ u₁ hnotEligible hsafe
    by_contra hfail
    exact hnone ⟨u₀, u₁, hnotEligible, hsafe, hfail⟩
  exact hnot
    (uniformLineBadScalarsBudgeted_of_supportAdjusted_and_lineListSingletonBudget
      dom k a L Lzero S B hSupport hFits hZeroSafe hlist hperCode hbudget)

open Classical in
/-- Complementary scanner for the line-list singleton route.  With line-list and arithmetic fixed,
failed production exposes a codeword whose singleton-witness scalar fiber exceeds the cap. -/
theorem exists_largeZero_safe_lineListSingletonCap_gt_of_not_uniformLineBadScalarsBudgeted
    (dom : Fin n ↪ F) (k a L Lzero S B : ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hlist : UniformLargeZeroSafeLineListBudgeted dom k a Lzero)
    (hbudget :
      UniformLargeZeroSafeWeightPlusLineListSingletonBudgeted dom k a Lzero S B)
    (hnot : ¬ UniformLineBadScalarsBudgeted dom k a B) :
    ∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
      ZeroDirectionSafeLine dom k a u₀ u₁ ∧
        ∃ c ∈ lineAppearingCodewords dom k a u₀ u₁,
          S < (codewordSingletonWitnessScalars dom k a u₀ u₁ c).card := by
  by_contra hnone
  have hperCode : UniformLargeZeroSafeCodewordSingletonBudgeted dom k a S := by
    intro u₀ u₁ hnotEligible hsafe c hc
    exact le_of_not_gt
      (fun hgt => hnone ⟨u₀, u₁, hnotEligible, hsafe, c, hc, hgt⟩)
  exact hnot
    (uniformLineBadScalarsBudgeted_of_supportAdjusted_and_lineListSingletonBudget
      dom k a L Lzero S B hSupport hFits hZeroSafe hlist hperCode hbudget)

open Classical in
/-- Combined scanner for the line-list singleton route.  Failed production forces one of the
three remaining obligations: the large-zero-safe line-list cap fails, the per-codeword singleton
cap fails on a concrete appearing codeword, or the combined arithmetic
`puncturedWeight + Lzero * S <= 2B` fails. -/
theorem exists_largeZero_safe_lineListSingletonRouteFailure_of_not_uniformLineBadScalarsBudgeted
    (dom : Fin n ↪ F) (k a L Lzero S B : ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hnot : ¬ UniformLineBadScalarsBudgeted dom k a B) :
    ∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
      ZeroDirectionSafeLine dom k a u₀ u₁ ∧
        (Lzero < (lineAppearingCodewords dom k a u₀ u₁).card ∨
          (∃ c ∈ lineAppearingCodewords dom k a u₀ u₁,
            S < (codewordSingletonWitnessScalars dom k a u₀ u₁ c).card) ∨
          ¬ puncturedZeroStratifiedLineWeight dom k a u₀ u₁ + Lzero * S ≤ 2 * B) := by
  by_cases hlist : UniformLargeZeroSafeLineListBudgeted dom k a Lzero
  · by_cases hperCode : UniformLargeZeroSafeCodewordSingletonBudgeted dom k a S
    · rcases
        exists_largeZero_safe_lineListSingletonBudgetFailure_of_not_uniformLineBadScalarsBudgeted
          dom k a L Lzero S B hSupport hFits hZeroSafe hlist hperCode hnot with
        ⟨u₀, u₁, hnotEligible, hsafe, hfail⟩
      exact ⟨u₀, u₁, hnotEligible, hsafe, Or.inr (Or.inr hfail)⟩
    · rcases
        (not_uniformLargeZeroSafeCodewordSingletonBudgeted_iff_exists_card_gt
          dom k a S).mp hperCode with
        ⟨u₀, u₁, hnotEligible, hsafe, c, hc, hgt⟩
      exact ⟨u₀, u₁, hnotEligible, hsafe, Or.inr (Or.inl ⟨c, hc, hgt⟩)⟩
  · rcases
      (not_uniformLargeZeroSafeLineListBudgeted_iff_exists_lineAppearing_gt
        dom k a Lzero).mp hlist with
      ⟨u₀, u₁, hnotEligible, hsafe, hgt⟩
    exact ⟨u₀, u₁, hnotEligible, hsafe, Or.inl hgt⟩

open Classical in
/-- Failure of the uniform constructive second-witness branch is exactly a large-zero safe line
with a bad scalar witness that has no distinct second witness. -/
theorem
    not_uniformLargeZeroSafeSecondWitnessProperty_iff_exists_witness_without_second
    (dom : Fin n ↪ F) (k a : ℕ) :
    ¬ UniformLargeZeroSafeSecondWitnessProperty dom k a ↔
      ∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
        ZeroDirectionSafeLine dom k a u₀ u₁ ∧
          ∃ γ ∈ lineBadScalars dom k a u₀ u₁,
            ∃ c ∈ badScalarWitnessCodewords dom k a u₀ u₁ γ,
              ∀ c' ∈ badScalarWitnessCodewords dom k a u₀ u₁ γ, c' = c := by
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro u₀ u₁ hnotEligible hsafe γ hγ c hc
    by_contra hnotSecond
    apply hnone
    exact ⟨u₀, u₁, hnotEligible, hsafe, γ, hγ, c, hc,
      fun c' hc' => by
        by_contra hne
        exact hnotSecond ⟨c', hc', hne⟩⟩
  · rintro ⟨u₀, u₁, hnotEligible, hsafe, γ, hγ, c, hc, huniq⟩ hsecond
    rcases hsecond u₀ u₁ hnotEligible hsafe γ hγ c hc with ⟨c', hc', hne⟩
    exact hne (huniq c' hc')

open Classical in
/-- Uniform scanner for the factor-two route.  Once the support branch, support arithmetic,
zero-direction safety, and half punctured-weight arithmetic are fixed, any failed uniform
bad-scalar budget must be a large-zero safe line with an explicitly unique witness codeword. -/
theorem exists_largeZero_safe_uniqueWitnessCodeword_of_not_uniformLineBadScalarsBudgeted
    (dom : Fin n ↪ F) (k a L B : ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hbudget : UniformLargeZeroSafePuncturedWeightDivTwoBudgeted dom k a B)
    (hnot : ¬ UniformLineBadScalarsBudgeted dom k a B) :
    ∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
      ZeroDirectionSafeLine dom k a u₀ u₁ ∧
        ∃ γ ∈ lineBadScalars dom k a u₀ u₁,
          ∃ c : Fin n → F, IsUniqueBadScalarWitnessCodeword dom k a u₀ u₁ γ c := by
  by_contra hnone
  have hno : UniformLargeZeroSafeNoUniqueBadScalarWitness dom k a := by
    intro u₀ u₁ hnotEligible hsafe γ hγ hcard
    rcases (badScalarWitnessCodewords_card_eq_one_iff_exists_isUniqueBadScalarWitnessCodeword
      dom k a u₀ u₁ γ).mp hcard with ⟨c, hc⟩
    exact hnone ⟨u₀, u₁, hnotEligible, hsafe, γ, hγ, c, hc⟩
  exact hnot
    (uniformLineBadScalarsBudgeted_of_supportAdjusted_and_noUniqueWeightDivTwo
      dom k a L B hSupport hFits hZeroSafe hno hbudget)

open Classical in
/-- Constructive scanner for the factor-two route.  Once the support branch, support arithmetic,
zero-direction safety, and half punctured-weight arithmetic are fixed, any failed uniform
bad-scalar budget yields a concrete witness codeword with no distinct second witness. -/
theorem exists_largeZero_safe_witness_without_second_of_not_uniformLineBadScalarsBudgeted
    (dom : Fin n ↪ F) (k a L B : ℕ)
    (hSupport : UniformSupportLineListBudgeted dom k a L)
    (hFits : SupportAdjustedBudgetFits (F := F) (n := n) a L B)
    (hZeroSafe : UniformZeroDirectionSafe dom k a)
    (hbudget : UniformLargeZeroSafePuncturedWeightDivTwoBudgeted dom k a B)
    (hnot : ¬ UniformLineBadScalarsBudgeted dom k a B) :
    ∃ u₀ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
      ZeroDirectionSafeLine dom k a u₀ u₁ ∧
        ∃ γ ∈ lineBadScalars dom k a u₀ u₁,
          ∃ c ∈ badScalarWitnessCodewords dom k a u₀ u₁ γ,
            ∀ c' ∈ badScalarWitnessCodewords dom k a u₀ u₁ γ, c' = c := by
  by_contra hnone
  have hsecond : UniformLargeZeroSafeSecondWitnessProperty dom k a := by
    intro u₀ u₁ hnotEligible hsafe γ hγ c hc
    by_contra hnotSecond
    apply hnone
    exact ⟨u₀, u₁, hnotEligible, hsafe, γ, hγ, c, hc,
      fun c' hc' => by
        by_contra hne
        exact hnotSecond ⟨c', hc', hne⟩⟩
  exact hnot
    (uniformLineBadScalarsBudgeted_of_supportAdjusted_and_secondWitnessWeightDivTwo
      dom k a L B hSupport hFits hZeroSafe hsecond hbudget)

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

open Classical in
/-- Every MCA-bad scalar lies in the line-list bad-scalar set once the real radius has crossed the
integer agreement threshold `a`.  The `mcaEvent` no-joint clause is discarded here; only the
existence of a codeword agreeing on a witness set is used. -/
theorem mcaEvent_badScalars_subset_lineBadScalars
    (dom : Fin n ↪ F) (k a : ℕ) {δ : ℝ≥0}
    (hlo : ((a - 1 : ℕ) : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    (u₀ u₁ : Fin n → F) :
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ))
      ⊆ lineBadScalars dom k a u₀ u₁ := by
  intro γ hγ
  rw [Finset.mem_filter] at hγ
  rcases hγ with ⟨_, S, hS, hline, _hnoJoint⟩
  rcases hline with ⟨c, hc, hagree⟩
  have haS : a ≤ S.card := by
    have hlt : ((a - 1 : ℕ) : ℝ≥0) < (S.card : ℝ≥0) :=
      lt_of_lt_of_le hlo hS
    have hltNat : a - 1 < S.card := by exact_mod_cast hlt
    omega
  have hSsub : S ⊆ agreeSet c (fun i => u₀ i + γ • u₁ i) := by
    intro i hi
    rw [agreeSet, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hagree i hi⟩
  rw [lineBadScalars, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, c, hc, le_trans haS (Finset.card_le_card hSsub)⟩

open Classical in
/-- Cardinal form of `mcaEvent_badScalars_subset_lineBadScalars`. -/
theorem mcaEvent_badScalars_card_le_lineBadScalars
    (dom : Fin n ↪ F) (k a : ℕ) {δ : ℝ≥0}
    (hlo : ((a - 1 : ℕ) : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    (u₀ u₁ : Fin n → F) :
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)).card
      ≤ (lineBadScalars dom k a u₀ u₁).card :=
  Finset.card_le_card
    (mcaEvent_badScalars_subset_lineBadScalars dom k a hlo u₀ u₁)

open Classical in
/-- A uniform line-list bad-scalar budget supplies the open-core incidence bound consumed by the
`δ*` lower pin. -/
theorem worstCaseIncidenceBounded_of_uniformLineBadScalarsBudgeted
    (dom : Fin n ↪ F) (k a B : ℕ) {δ : ℝ≥0}
    (hlo : ((a - 1 : ℕ) : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    (hB : UniformLineBadScalarsBudgeted dom k a B) :
    OpenCoreConditionalPin.WorstCaseIncidenceBounded (F := F) (A := F)
      (((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F))) δ B := by
  intro u
  exact le_trans
    (mcaEvent_badScalars_card_le_lineBadScalars dom k a hlo (u 0) (u 1))
    (hB (u 0) (u 1))

open Classical in
/-- Direct `δ*` floor from a uniform line-list bad-scalar budget.  The remaining inputs are exactly
the radius-in-window inequality and the normalized budget fit. -/
theorem mcaDeltaStar_floor_of_uniformLineBadScalarsBudgeted
    (dom : Fin n ↪ F) (k a B : ℕ) (εstar : ℝ≥0∞) {δ : ℝ≥0}
    (hδ : δ ≤ 1)
    (hlo : ((a - 1 : ℕ) : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    (hB : UniformLineBadScalarsBudgeted dom k a B)
    (hbudget : (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ MCAThresholdLedger.mcaDeltaStar (F := F) (A := F)
      (((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F))) εstar :=
  OpenCoreConditionalPin.worstCaseIncidence_pin (F := F) (A := F)
    (((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F))) εstar hδ
    (worstCaseIncidenceBounded_of_uniformLineBadScalarsBudgeted dom k a B hlo hB)
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
#print axioms not_lineBadScalarMultiplicityFloor_iff_exists_badScalarWitnessCodewords_card_lt
#print axioms lineBadScalars_mem_of_mem_badScalarWitnessCodewords
#print axioms badScalarWitnessCodewords_card_pos_of_mem_lineBadScalars
#print axioms lineBadScalarMultiplicityFloor_one
#print axioms not_lineBadScalarMultiplicityFloor_two_iff_exists_unique_badScalarWitness
#print axioms NoUniqueBadScalarWitness
#print axioms IsUniqueBadScalarWitnessCodeword
#print axioms badScalarWitnessCodewords_card_eq_one_iff_exists_isUniqueBadScalarWitnessCodeword
#print axioms BadScalarSecondWitnessProperty
#print axioms noUniqueBadScalarWitness_iff_secondWitnessProperty
#print axioms badScalarWitnessCodewords_card_eq_one_of_uniqueDecoding
#print axioms exists_uniqueWitnessCodeword_of_mem_lineBadScalars_uniqueDecoding
#print axioms not_noUniqueBadScalarWitness_of_nonempty_uniqueDecoding
#print axioms not_secondWitnessProperty_of_nonempty_uniqueDecoding
#print axioms not_lineBadScalarMultiplicityFloor_two_iff_exists_uniqueWitnessCodeword
#print axioms not_noUniqueBadScalarWitness_iff_exists_uniqueWitnessCodeword
#print axioms lineBadScalarMultiplicityFloor_two_iff_noUniqueBadScalarWitness
#print axioms
  lineBadScalars_card_le_puncturedZeroStratifiedLineWeight_div_two_of_noUniqueBadScalarWitness
#print axioms lineBadScalars_card_le_of_noUniqueBadScalarWitness_and_weight_div_two_le
#print axioms lineBadScalars_card_le_weightDivTwo_of_secondWitness
#print axioms lineBadScalars_card_le_of_secondWitness_and_weightDivTwo_le
#print axioms singletonBadScalars
#print axioms mem_singletonBadScalars
#print axioms singletonBadScalars_subset_lineBadScalars
#print axioms mem_singletonBadScalars_iff_exists_uniqueWitnessCodeword
#print axioms singletonBadScalarDefect
#print axioms singletonBadScalarDefect_eq_sum_indicator
#print axioms singletonBadScalarDefect_le_lineBadScalars_card
#print axioms singletonBadScalarDefect_eq_zero_iff_noUniqueBadScalarWitness
#print axioms singletonBadScalarDefect_eq_zero_iff_secondWitnessProperty
#print axioms singletonBadScalarDefect_pos_iff_not_noUniqueBadScalarWitness
#print axioms singletonBadScalarDefect_pos_iff_exists_uniqueWitnessCodeword
#print axioms singletonBadScalars_eq_lineBadScalars_of_uniqueDecoding
#print axioms singletonBadScalarDefect_eq_lineBadScalars_card_of_uniqueDecoding
#print axioms codewordSingletonWitnessScalars
#print axioms mem_codewordSingletonWitnessScalars
#print axioms codewordSingletonWitnessScalars_subset_lineBadScalars
#print axioms codewordSingletonWitnessScalars_subset_codewordHeavyScalars
#print axioms codewordSingletonWitnessScalars_card_le_support_div_sub_zeroAgreement
#print axioms codewordSingletonWitnessScalars_card_le_support_div_of_zeroSafe
#print axioms codewordSingletonWitnessScalars_subset_singletonBadScalars
#print axioms lineAppearingCodewords_mem_of_isUniqueBadScalarWitnessCodeword
#print axioms disjoint_codewordSingletonWitnessScalars_of_ne
#print axioms pairwiseDisjoint_codewordSingletonWitnessScalars
#print axioms singletonBadScalars_subset_biUnion_codewordSingletonWitnessScalars
#print axioms biUnion_codewordSingletonWitnessScalars_eq_singletonBadScalars
#print axioms singletonBadScalarDefect_eq_sum_codewordSingletonWitnessScalars
#print axioms singletonBadScalarDefect_le_sum_codewordSingletonWitnessScalars
#print axioms singletonBadScalarDefect_le_of_codewordSingletonWitnessScalars
#print axioms singletonBadScalarDefect_le_of_lineListBudgeted_and_codewordSingletonWitnessScalars
#print axioms lineBadScalars_card_mul_two_le_lineHeavyIncidences_card_add_singletonDefect
#print axioms lineBadScalars_card_mul_two_le_puncturedWeight_add_singletonDefect
#print axioms lineBadScalars_card_le_puncturedWeight_add_singletonDefect_div_two
#print axioms lineBadScalars_card_le_of_weight_add_singletonDefect_le_two_mul
#print axioms lineBadScalars_card_le_of_weight_add_codewordSingletonBudget_le_two_mul
#print axioms lineBadScalars_card_le_of_weight_add_lineListSingletonBudget_le_two_mul
#print axioms not_noUniqueBadScalarWitness_iff_exists_unique_badScalarWitness
#print axioms exists_unique_badScalarWitness_of_not_lineBadScalars_card_le
#print axioms exists_uniqueWitnessCodeword_of_not_lineBadScalars_card_le
#print axioms UniformLargeZeroSafeNoUniqueBadScalarWitness
#print axioms UniformLargeZeroSafeSecondWitnessProperty
#print axioms uniformLargeZeroSafeNoUnique_iff_secondWitnessProperty
#print axioms UniformLargeZeroSafeSingletonDefectZero
#print axioms uniformLargeZeroSafeNoUnique_iff_singletonDefectZero
#print axioms uniformLargeZeroSafeSecondWitness_iff_singletonDefectZero
#print axioms UniformLargeZeroSafePuncturedWeightDivTwoBudgeted
#print axioms UniformLargeZeroSafeWeightPlusSingletonDefectBudgeted
#print axioms UniformLargeZeroSafeCodewordSingletonBudgeted
#print axioms UniformLargeZeroSafeWeightPlusCodewordSingletonBudgeted
#print axioms UniformLargeZeroSafeLineListBudgeted
#print axioms UniformLargeZeroSafeWeightPlusLineListSingletonBudgeted
#print axioms not_uniformLargeZeroSafeCodewordSingletonBudgeted_iff_exists_card_gt
#print axioms not_uniformLargeZeroSafeLineListBudgeted_iff_exists_lineAppearing_gt
#print axioms
  exists_largeZero_safe_codewordSingletonSupportDiv_gt_of_not_uniformSingletonBudgeted
#print axioms largeZeroSafeLineBadScalarsBudgeted_of_noUnique_and_weightDivTwo
#print axioms largeZeroSafeLineBadScalarsBudgeted_of_secondWitness_and_weightDivTwo
#print axioms uniformLineBadScalarsBudgeted_of_supportAdjusted_and_noUniqueWeightDivTwo
#print axioms uniformLineBadScalarsBudgeted_of_supportAdjusted_and_secondWitnessWeightDivTwo
#print axioms largeZeroSafeLineBadScalarsBudgeted_of_singletonDefectBudget
#print axioms uniformLineBadScalarsBudgeted_of_supportAdjusted_and_singletonDefectBudget
#print axioms largeZeroSafeLineBadScalarsBudgeted_of_codewordSingletonBudget
#print axioms uniformLineBadScalarsBudgeted_of_supportAdjusted_and_codewordSingletonBudget
#print axioms largeZeroSafeLineBadScalarsBudgeted_of_lineListSingletonBudget
#print axioms uniformLineBadScalarsBudgeted_of_supportAdjusted_and_lineListSingletonBudget
#print axioms
  exists_largeZero_safe_singletonDefectBudgetFailure_of_not_uniformLineBadScalarsBudgeted
#print axioms
  exists_largeZero_safe_codewordSingletonBudgetFailure_of_not_uniformLineBadScalarsBudgeted
#print axioms
  exists_largeZero_safe_codewordSingletonCap_gt_of_not_uniformLineBadScalarsBudgeted
#print axioms
  exists_largeZero_safe_codewordSingletonRouteFailure_of_not_uniformLineBadScalarsBudgeted
#print axioms
  exists_largeZero_safe_codewordSingletonRouteSupportDivFailure
#print axioms
  exists_largeZero_safe_lineListSingletonBudgetFailure_of_not_uniformLineBadScalarsBudgeted
#print axioms
  exists_largeZero_safe_lineListSingletonCap_gt_of_not_uniformLineBadScalarsBudgeted
#print axioms
  exists_largeZero_safe_lineListSingletonRouteFailure_of_not_uniformLineBadScalarsBudgeted
#print axioms not_uniformLargeZeroSafeSecondWitnessProperty_iff_exists_witness_without_second
#print axioms exists_largeZero_safe_uniqueWitnessCodeword_of_not_uniformLineBadScalarsBudgeted
#print axioms
  exists_largeZero_safe_witness_without_second_of_not_uniformLineBadScalarsBudgeted
#print axioms lineBadScalars_card_mul_le_puncturedZeroStratifiedLineWeight_of_multiplicityFloor
#print axioms lineBadScalars_card_le_puncturedZeroStratifiedLineWeight_div_of_multiplicityFloor
#print axioms lineBadScalars_card_le_of_multiplicityFloor_and_weight_div_le
#print axioms mcaEvent_badScalars_subset_lineBadScalars
#print axioms mcaEvent_badScalars_card_le_lineBadScalars
#print axioms worstCaseIncidenceBounded_of_uniformLineBadScalarsBudgeted
#print axioms mcaDeltaStar_floor_of_uniformLineBadScalarsBudgeted

end SourceAudit

end ProximityGap.Ownership
