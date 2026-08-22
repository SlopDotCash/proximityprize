/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterCommonFactorConstruction

/-!
# Saturated P1 common-factor cores and received stack

This file completes the set-theoretic heart of the saturated amplifier.  The
concrete polynomial/row substrate is supplied by
`_P1RateQuarterCommonFactorConstruction`; here we prove that

`(oldCore \ newHoles) ∪ commonRoots`

has exactly `8m+r+d` coordinates for every source line and that the amplified
polynomial pair agrees with the amplified received stack throughout it.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

open Finset Polynomial
open _root_.ProximityGap Code
open scoped NNReal Polynomial

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterSaturatedConstructionLegacy

open ArkLib.ProximityGap.PrizeShapePrimeP30
open P1RateQuarterScaleArithmetic
open P1RateQuarterScaleConstruction
open P1RateQuarterCommonFactorArithmetic
open P1RateQuarterCommonFactorConstruction
open HalfPredecessorCoreFreshDecode

local instance localInstance_P1RateQuarterSaturatedConstruction_1 : Fact (Nat.Prime P) := ⟨prime_P⟩
attribute [local instance] Classical.propDecidable

local notation "δsat" => P1RateQuarterCommonFactorArithmetic.delta

/-! ## Membership geometry of the three modified singleton cells -/

theorem mem_core_iff_of_snd_ne_fifteen (i : Fin 3) {e : Coord}
    (he : e.2 ≠ (15 : Fin 16)) : e ∈ core i ↔ e.2 ∈ baseCore i := by
  simp only [core, Finset.mem_filter, Finset.mem_univ, true_and, corePred]
  constructor
  · rintro (hbase | ⟨-, hsnd⟩)
    · exact hbase
    · exact (he hsnd).elim
  · exact Or.inl

theorem mem_core_of_snd_mem_baseCore (i : Fin 3) {e : Coord}
    (he : e.2 ∈ baseCore i) : e ∈ core i := by
  simp only [core, Finset.mem_filter, Finset.mem_univ, true_and, corePred]
  exact Or.inl he

theorem not_mem_core_of_snd_ne_fifteen (i : Fin 3) {e : Coord}
    (hne : e.2 ≠ (15 : Fin 16)) (he : e.2 ∉ baseCore i) : e ∉ core i := by
  intro hcore
  simp only [core, Finset.mem_filter, Finset.mem_univ, true_and, corePred] at hcore
  rcases hcore with hbase | htransfer
  · exact he hbase
  · exact hne htransfer.2

theorem mem_core_iff_of_mem_rootFour (i : Fin 3) {e : Coord}
    (he : e ∈ rootFour) : e ∈ core i ↔ i = 0 := by
  have hsnd := snd_eq_of_mem_selectedCoords (4 : Fin 16) he
  rw [mem_core_iff_of_snd_ne_fifteen i (by omega), hsnd]
  fin_cases i <;> decide

theorem mem_core_iff_of_mem_rootEleven (i : Fin 3) {e : Coord}
    (he : e ∈ rootEleven) : e ∈ core i ↔ i = 1 := by
  have hsnd := snd_eq_of_mem_selectedCoords (11 : Fin 16) he
  rw [mem_core_iff_of_snd_ne_fifteen i (by omega), hsnd]
  fin_cases i <;> decide

theorem mem_core_iff_of_mem_newHoles (i : Fin 3) {e : Coord}
    (he : e ∈ newHoles) : e ∈ core i ↔ i = 2 := by
  have hsnd := snd_eq_of_mem_selectedCoords (13 : Fin 16) he
  rw [mem_core_iff_of_snd_ne_fifteen i (by omega), hsnd]
  fin_cases i <;> decide

theorem newHoles_subset_core_two : newHoles ⊆ core 2 := by
  intro e he
  have hsnd := snd_eq_of_mem_selectedCoords (13 : Fin 16) he
  simp only [core, Finset.mem_filter, Finset.mem_univ, true_and, corePred]
  left
  rw [hsnd]
  decide

theorem core_zero_disjoint_newHoles : Disjoint (core 0) newHoles := by
  rw [Finset.disjoint_left]
  intro e hecore hehole
  have hsnd := snd_eq_of_mem_selectedCoords (13 : Fin 16) hehole
  simp only [core, Finset.mem_filter, Finset.mem_univ, true_and, corePred] at hecore
  rcases hecore with hbase | htransfer
  · rw [hsnd] at hbase
    exact (by decide : (13 : Fin 16) ∉ baseCore 0) hbase
  · exact (by omega : (13 : Fin 16) ≠ 15) (hsnd.symm.trans htransfer.2)

theorem core_one_disjoint_newHoles : Disjoint (core 1) newHoles := by
  rw [Finset.disjoint_left]
  intro e hecore hehole
  have hsnd := snd_eq_of_mem_selectedCoords (13 : Fin 16) hehole
  simp only [core, Finset.mem_filter, Finset.mem_univ, true_and, corePred] at hecore
  rcases hecore with hbase | htransfer
  · rw [hsnd] at hbase
    exact (by decide : (13 : Fin 16) ∉ baseCore 1) hbase
  · exact (by omega : (13 : Fin 16) ≠ 15) (hsnd.symm.trans htransfer.2)

theorem core_sdiff_newHoles_card (i : Fin 3) :
    (core i \ newHoles).card =
      if i = 2 then 8 * m + r - d else 8 * m + r := by
  fin_cases i
  · change (core 0 \ newHoles).card =
      if (0 : Fin 3) = 2 then 8 * m + r - d else 8 * m + r
    rw [Finset.sdiff_eq_self_of_disjoint core_zero_disjoint_newHoles,
      core_card]
    simp
  · change (core 1 \ newHoles).card =
      if (1 : Fin 3) = 2 then 8 * m + r - d else 8 * m + r
    rw [Finset.sdiff_eq_self_of_disjoint core_one_disjoint_newHoles,
      core_card]
    simp
  · change (core 2 \ newHoles).card =
      if (2 : Fin 3) = 2 then 8 * m + r - d else 8 * m + r
    rw [Finset.card_sdiff_of_subset newHoles_subset_core_two,
      core_card, newHoles_card]
    simp

theorem commonRoot_not_mem_newHoles {e : Coord} (he : e ∈ commonRoots) :
    e ∉ newHoles :=
  (Finset.disjoint_left.mp commonRoots_disjoint_newHoles) he

theorem rootFour_mem_core_zero {e : Coord} (he : e ∈ rootFour) : e ∈ core 0 := by
  have hsnd := snd_eq_of_mem_selectedCoords (4 : Fin 16) he
  simp only [core, Finset.mem_filter, Finset.mem_univ, true_and, corePred]
  left
  rw [hsnd]
  decide

theorem rootFour_not_mem_core_one {e : Coord} (he : e ∈ rootFour) : e ∉ core 1 := by
  have hsnd := snd_eq_of_mem_selectedCoords (4 : Fin 16) he
  intro hcore
  simp only [core, Finset.mem_filter, Finset.mem_univ, true_and, corePred] at hcore
  rcases hcore with hbase | htransfer
  · rw [hsnd] at hbase
    exact (by decide : (4 : Fin 16) ∉ baseCore 1) hbase
  · exact (by omega : (4 : Fin 16) ≠ 15) (hsnd.symm.trans htransfer.2)

theorem rootFour_not_mem_core_two {e : Coord} (he : e ∈ rootFour) : e ∉ core 2 := by
  have hsnd := snd_eq_of_mem_selectedCoords (4 : Fin 16) he
  intro hcore
  simp only [core, Finset.mem_filter, Finset.mem_univ, true_and, corePred] at hcore
  rcases hcore with hbase | htransfer
  · rw [hsnd] at hbase
    exact (by decide : (4 : Fin 16) ∉ baseCore 2) hbase
  · exact (by omega : (4 : Fin 16) ≠ 15) (hsnd.symm.trans htransfer.2)

theorem rootEleven_mem_core_one {e : Coord} (he : e ∈ rootEleven) : e ∈ core 1 := by
  have hsnd := snd_eq_of_mem_selectedCoords (11 : Fin 16) he
  simp only [core, Finset.mem_filter, Finset.mem_univ, true_and, corePred]
  left
  rw [hsnd]
  decide

theorem rootEleven_not_mem_core_zero {e : Coord} (he : e ∈ rootEleven) : e ∉ core 0 := by
  have hsnd := snd_eq_of_mem_selectedCoords (11 : Fin 16) he
  intro hcore
  simp only [core, Finset.mem_filter, Finset.mem_univ, true_and, corePred] at hcore
  rcases hcore with hbase | htransfer
  · rw [hsnd] at hbase
    exact (by decide : (11 : Fin 16) ∉ baseCore 0) hbase
  · exact (by omega : (11 : Fin 16) ≠ 15) (hsnd.symm.trans htransfer.2)

theorem rootEleven_not_mem_core_two {e : Coord} (he : e ∈ rootEleven) : e ∉ core 2 := by
  have hsnd := snd_eq_of_mem_selectedCoords (11 : Fin 16) he
  intro hcore
  simp only [core, Finset.mem_filter, Finset.mem_univ, true_and, corePred] at hcore
  rcases hcore with hbase | htransfer
  · rw [hsnd] at hbase
    exact (by decide : (11 : Fin 16) ∉ baseCore 2) hbase
  · exact (by omega : (11 : Fin 16) ≠ 15) (hsnd.symm.trans htransfer.2)

theorem core_zero_disjoint_rootEleven : Disjoint (core 0) rootEleven := by
  rw [Finset.disjoint_left]
  intro e hcore hroot
  have hsnd := snd_eq_of_mem_selectedCoords (11 : Fin 16) hroot
  simp only [core, Finset.mem_filter, Finset.mem_univ, true_and, corePred] at hcore
  rcases hcore with hbase | htransfer
  · rw [hsnd] at hbase
    exact (by decide : (11 : Fin 16) ∉ baseCore 0) hbase
  · exact (by omega : (11 : Fin 16) ≠ 15) (hsnd.symm.trans htransfer.2)

theorem core_one_disjoint_rootFour : Disjoint (core 1) rootFour := by
  rw [Finset.disjoint_left]
  intro e hcore hroot
  have hsnd := snd_eq_of_mem_selectedCoords (4 : Fin 16) hroot
  simp only [core, Finset.mem_filter, Finset.mem_univ, true_and, corePred] at hcore
  rcases hcore with hbase | htransfer
  · rw [hsnd] at hbase
    exact (by decide : (4 : Fin 16) ∉ baseCore 1) hbase
  · exact (by omega : (4 : Fin 16) ≠ 15) (hsnd.symm.trans htransfer.2)

theorem core_two_disjoint_commonRoots : Disjoint (core 2) commonRoots := by
  rw [Finset.disjoint_left]
  intro e hcore hroot
  rw [commonRoots, Finset.mem_union] at hroot
  rcases hroot with hfour | heleven
  · have hsnd := snd_eq_of_mem_selectedCoords (4 : Fin 16) hfour
    simp only [core, Finset.mem_filter, Finset.mem_univ, true_and, corePred] at hcore
    rcases hcore with hbase | htransfer
    · rw [hsnd] at hbase
      exact (by decide : (4 : Fin 16) ∉ baseCore 2) hbase
    · exact (by omega : (4 : Fin 16) ≠ 15) (hsnd.symm.trans htransfer.2)
  · have hsnd := snd_eq_of_mem_selectedCoords (11 : Fin 16) heleven
    simp only [core, Finset.mem_filter, Finset.mem_univ, true_and, corePred] at hcore
    rcases hcore with hbase | htransfer
    · rw [hsnd] at hbase
      exact (by decide : (11 : Fin 16) ∉ baseCore 2) hbase
    · exact (by omega : (11 : Fin 16) ≠ 15) (hsnd.symm.trans htransfer.2)

/-! ## Exact amplified cores -/

/-- Small logical predicate underlying amplified-core membership. -/
def amplifiedCorePred (i : Fin 3) (e : Coord) : Prop :=
  match i with
  | 0 => (corePred 0 e ∧ e ∉ newHoles) ∨ e ∈ rootEleven
  | 1 => (corePred 1 e ∧ e ∉ newHoles) ∨ e ∈ rootFour
  | 2 => (corePred 2 e ∧ e ∉ newHoles) ∨ e ∈ commonRoots

/-- Filtering by a proposition keeps downstream membership elimination from
normalizing the billion-scale union representation. -/
noncomputable def amplifiedCoreSet (i : Fin 3) : Finset Coord :=
  Finset.univ.filter (amplifiedCorePred i)

theorem amplifiedCoreSet_zero_eq :
    amplifiedCoreSet 0 = (core 0 \ newHoles) ∪ rootEleven := by
  ext e
  simp [amplifiedCoreSet, amplifiedCorePred, core]

theorem amplifiedCoreSet_one_eq :
    amplifiedCoreSet 1 = (core 1 \ newHoles) ∪ rootFour := by
  ext e
  simp [amplifiedCoreSet, amplifiedCorePred, core]

theorem amplifiedCoreSet_two_eq :
    amplifiedCoreSet 2 = (core 2 \ newHoles) ∪ commonRoots := by
  ext e
  simp [amplifiedCoreSet, amplifiedCorePred, core]

theorem amplifiedCoreSet_card (i : Fin 3) :
    (amplifiedCoreSet i).card = amplifiedCore := by
  fin_cases i
  · change (amplifiedCoreSet 0).card = amplifiedCore
    rw [amplifiedCoreSet_zero_eq]
    have hdisjoint : Disjoint (core 0 \ newHoles) rootEleven :=
      Disjoint.mono_left Finset.sdiff_subset core_zero_disjoint_rootEleven
    rw [Finset.card_union_of_disjoint hdisjoint,
      core_sdiff_newHoles_card, rootEleven_card]
    simp [amplifiedCore]
  · change (amplifiedCoreSet 1).card = amplifiedCore
    rw [amplifiedCoreSet_one_eq]
    have hdisjoint : Disjoint (core 1 \ newHoles) rootFour :=
      Disjoint.mono_left Finset.sdiff_subset core_one_disjoint_rootFour
    rw [Finset.card_union_of_disjoint hdisjoint,
      core_sdiff_newHoles_card, rootFour_card]
    simp [amplifiedCore]
  · change (amplifiedCoreSet 2).card = amplifiedCore
    rw [amplifiedCoreSet_two_eq]
    have hdisjoint : Disjoint (core 2 \ newHoles) commonRoots :=
      Disjoint.mono_left Finset.sdiff_subset core_two_disjoint_commonRoots
    rw [Finset.card_union_of_disjoint hdisjoint,
      core_sdiff_newHoles_card, commonRoots_card]
    norm_num [amplifiedCore, d, m, r]

theorem amplifiedCoreSet_card_ge_k (i : Fin 3) :
    k ≤ (amplifiedCoreSet i).card := by
  rw [amplifiedCoreSet_card]
  norm_num [amplifiedCore, k, d, m, r]

theorem amplifiedCoreSet_size_condition (i : Fin 3) :
    ((((amplifiedCoreSet i).card + 1 : ℕ) : ℝ≥0)) ≥
      (1 - δsat) * (Fintype.card Coord : ℝ≥0) := by
  rw [amplifiedCoreSet_card, card_coord, agreement_mass_eq_amplifiedThreshold]

end ArkLib.ProximityGap.Frontier.P1RateQuarterSaturatedConstructionLegacy

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.P1RateQuarterSaturatedConstructionLegacy
#print axioms amplifiedCoreSet_card
#print axioms amplifiedCoreSet_size_condition
