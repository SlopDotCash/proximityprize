/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterCommonFactorConstruction

/-!
# Saturated P1 common-factor cores

This module proves the exact cardinality and polynomial-pair agreement properties
of the amplified common-factor cores. Safe and unsafe event certificates are split
into separate modules to keep elaboration memory bounded.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false
set_option maxRecDepth 250000

open Finset Polynomial
open _root_.ProximityGap Code
open scoped NNReal Polynomial

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterSaturatedConstruction

open ArkLib.ProximityGap.PrizeShapePrimeP30
open P1RateQuarterScaleArithmetic
open P1RateQuarterScaleConstruction
open P1RateQuarterCommonFactorArithmetic
open P1RateQuarterCommonFactorConstruction
open HalfPredecessorCoreFreshDecode

local instance : Fact (Nat.Prime P) := ⟨prime_P⟩
attribute [local instance] Classical.propDecidable

local notation "δsat" => P1RateQuarterCommonFactorArithmetic.delta

/-! ## Membership geometry of the three modified singleton cells -/

theorem mem_core_iff_of_residue
    (i : Fin 3) {a : Fin 16} (ha : a ≠ 15) {e : Coord}
    (hsnd : e.2 = a) : e ∈ core i ↔ a ∈ baseCore i := by
  simp only [core, Finset.mem_filter, Finset.mem_univ, true_and, corePred]
  constructor
  · intro h
    rcases h with hbase | htransfer
    · rwa [hsnd] at hbase
    · exact (ha (hsnd.symm.trans htransfer.2)).elim
  · intro hbase
    left
    rwa [hsnd]

theorem mem_core_iff_of_mem_rootFour (i : Fin 3) {e : Coord}
    (he : e ∈ rootFour) : e ∈ core i ↔ i = 0 := by
  rw [mem_core_iff_of_residue i (by decide)
    (snd_eq_of_mem_selectedCoords (4 : Fin 16) he)]
  fin_cases i <;> decide

theorem mem_core_iff_of_mem_rootEleven (i : Fin 3) {e : Coord}
    (he : e ∈ rootEleven) : e ∈ core i ↔ i = 1 := by
  rw [mem_core_iff_of_residue i (by decide)
    (snd_eq_of_mem_selectedCoords (11 : Fin 16) he)]
  fin_cases i <;> decide

theorem mem_core_iff_of_mem_newHoles (i : Fin 3) {e : Coord}
    (he : e ∈ newHoles) : e ∈ core i ↔ i = 2 := by
  rw [mem_core_iff_of_residue i (by decide)
    (snd_eq_of_mem_selectedCoords (13 : Fin 16) he)]
  fin_cases i <;> decide

theorem newHoles_subset_core_two : newHoles ⊆ core 2 := by
  intro e he
  rw [mem_core_iff_of_residue 2 (by decide)
    (snd_eq_of_mem_selectedCoords (13 : Fin 16) he)]
  decide

theorem core_zero_disjoint_newHoles : Disjoint (core 0) newHoles := by
  rw [Finset.disjoint_left]
  intro e hecore hehole
  rw [mem_core_iff_of_residue 0 (by decide)
    (snd_eq_of_mem_selectedCoords (13 : Fin 16) hehole)] at hecore
  exact (by decide : (13 : Fin 16) ∉ baseCore 0) hecore

theorem core_one_disjoint_newHoles : Disjoint (core 1) newHoles := by
  rw [Finset.disjoint_left]
  intro e hecore hehole
  rw [mem_core_iff_of_residue 1 (by decide)
    (snd_eq_of_mem_selectedCoords (13 : Fin 16) hehole)] at hecore
  exact (by decide : (13 : Fin 16) ∉ baseCore 1) hecore

theorem rootFour_mem_core_zero {e : Coord} (he : e ∈ rootFour) :
    e ∈ core 0 := by
  rw [mem_core_iff_of_residue 0 (by decide)
    (snd_eq_of_mem_selectedCoords (4 : Fin 16) he)]
  decide

theorem rootFour_not_mem_core_one {e : Coord} (he : e ∈ rootFour) :
    e ∉ core 1 := by
  rw [mem_core_iff_of_residue 1 (by decide)
    (snd_eq_of_mem_selectedCoords (4 : Fin 16) he)]
  decide

theorem rootFour_not_mem_core_two {e : Coord} (he : e ∈ rootFour) :
    e ∉ core 2 := by
  rw [mem_core_iff_of_residue 2 (by decide)
    (snd_eq_of_mem_selectedCoords (4 : Fin 16) he)]
  decide

theorem rootEleven_not_mem_core_zero {e : Coord} (he : e ∈ rootEleven) :
    e ∉ core 0 := by
  rw [mem_core_iff_of_residue 0 (by decide)
    (snd_eq_of_mem_selectedCoords (11 : Fin 16) he)]
  decide

theorem rootEleven_mem_core_one {e : Coord} (he : e ∈ rootEleven) :
    e ∈ core 1 := by
  rw [mem_core_iff_of_residue 1 (by decide)
    (snd_eq_of_mem_selectedCoords (11 : Fin 16) he)]
  decide

theorem rootEleven_not_mem_core_two {e : Coord} (he : e ∈ rootEleven) :
    e ∉ core 2 := by
  rw [mem_core_iff_of_residue 2 (by decide)
    (snd_eq_of_mem_selectedCoords (11 : Fin 16) he)]
  decide

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

theorem core_zero_sdiff_inter_commonRoots :
    (core 0 \ newHoles) ∩ commonRoots = rootFour := by
  ext e
  rw [Finset.mem_inter, Finset.mem_sdiff]
  constructor
  · rintro ⟨⟨hcore, -⟩, hroot⟩
    rw [commonRoots, Finset.mem_union] at hroot
    rcases hroot with hfour | heleven
    · exact hfour
    · exact (rootEleven_not_mem_core_zero heleven hcore).elim
  · intro hfour
    have hcommon : e ∈ commonRoots :=
      Finset.mem_union_left rootEleven hfour
    exact ⟨⟨rootFour_mem_core_zero hfour,
      commonRoot_not_mem_newHoles hcommon⟩, hcommon⟩

theorem core_one_sdiff_inter_commonRoots :
    (core 1 \ newHoles) ∩ commonRoots = rootEleven := by
  ext e
  rw [Finset.mem_inter, Finset.mem_sdiff]
  constructor
  · rintro ⟨⟨hcore, -⟩, hroot⟩
    rw [commonRoots, Finset.mem_union] at hroot
    rcases hroot with hfour | heleven
    · exact (rootFour_not_mem_core_one hfour hcore).elim
    · exact heleven
  · intro heleven
    have hcommon : e ∈ commonRoots :=
      Finset.mem_union_right rootFour heleven
    exact ⟨⟨rootEleven_mem_core_one heleven,
      commonRoot_not_mem_newHoles hcommon⟩, hcommon⟩

theorem core_two_sdiff_inter_commonRoots :
    (core 2 \ newHoles) ∩ commonRoots = ∅ := by
  ext e
  rw [Finset.mem_inter, Finset.mem_sdiff]
  constructor
  · rintro ⟨⟨hcore, -⟩, hroot⟩
    rw [commonRoots, Finset.mem_union] at hroot
    rcases hroot with hfour | heleven
    · exact (rootFour_not_mem_core_two hfour hcore).elim
    · exact (rootEleven_not_mem_core_two heleven hcore).elim
  · intro hempty
    simp only [Finset.not_mem_empty] at hempty

theorem core_sdiff_inter_commonRoots (i : Fin 3) :
    (core i \ newHoles) ∩ commonRoots =
      if i = 0 then rootFour else if i = 1 then rootEleven else ∅ := by
  fin_cases i
  · simpa using core_zero_sdiff_inter_commonRoots
  · simpa using core_one_sdiff_inter_commonRoots
  · simpa using core_two_sdiff_inter_commonRoots

theorem core_sdiff_inter_commonRoots_card (i : Fin 3) :
    ((core i \ newHoles) ∩ commonRoots).card =
      if i = 2 then 0 else d := by
  rw [core_sdiff_inter_commonRoots]
  fin_cases i <;> simp [rootFour_card, rootEleven_card]

/-! ## Exact amplified cores -/

/-- Remove the new holes and promote all common roots into every core. -/
noncomputable def amplifiedCoreSet (i : Fin 3) : Finset Coord :=
  (core i \ newHoles) ∪ commonRoots

theorem amplifiedCoreSet_card (i : Fin 3) :
    (amplifiedCoreSet i).card = amplifiedCore := by
  have hbook := Finset.card_union_add_card_inter
    (core i \ newHoles) commonRoots
  rw [← amplifiedCoreSet, core_sdiff_newHoles_card, commonRoots_card,
    core_sdiff_inter_commonRoots_card] at hbook
  fin_cases i <;> simp at hbook <;>
    norm_num [amplifiedCore, d, m, r] at hbook ⊢ <;> omega

theorem amplifiedCoreSet_card_ge_k (i : Fin 3) :
    k ≤ (amplifiedCoreSet i).card := by
  rw [amplifiedCoreSet_card]
  norm_num [amplifiedCore, k, d, m, r]

theorem amplifiedCoreSet_size_condition (i : Fin 3) :
    ((((amplifiedCoreSet i).card + 1 : ℕ) : ℝ≥0)) ≥
      (1 - δsat) * (Fintype.card Coord : ℝ≥0) := by
  rw [amplifiedCoreSet_card, card_coord, agreement_mass_eq_amplifiedThreshold]

/-! ## Agreement of the amplified stack on every amplified core -/

@[simp] theorem amplifiedU_zero (L : CommonLocatorData) :
    amplifiedU L 0 = amplifiedU0 L := rfl

@[simp] theorem amplifiedU_one (L : CommonLocatorData) :
    amplifiedU L 1 = amplifiedU1 L := rfl

theorem amplified_core_pair_agreement
    (L : CommonLocatorData) (i : Fin 3) (e : Coord)
    (he : e ∈ amplifiedCoreSet i) :
    (amplifiedIntercept L i).eval (domain e) = amplifiedU0 L e ∧
      (amplifiedDirection L i).eval (domain e) = amplifiedU1 L e := by
  rw [amplifiedCoreSet, Finset.mem_union] at he
  rcases he with hold | hroot
  · have hcore : e ∈ core i := (Finset.mem_sdiff.mp hold).1
    have hnotHole : e ∉ newHoles := (Finset.mem_sdiff.mp hold).2
    have holdAgree := core_pair_agreement i e hcore
    have hrows := amplifiedU_rows_of_not_mem_newHoles L hnotHole
    rw [amplifiedIntercept_eval, amplifiedDirection_eval, hrows.1, hrows.2,
      holdAgree.1, holdAgree.2]
    constructor <;> ring
  · have hzero := L.eval_zero hroot
    have hnotHole : e ∉ newHoles := commonRoot_not_mem_newHoles hroot
    have hrows := amplifiedU_rows_of_not_mem_newHoles L hnotHole
    rw [amplifiedIntercept_eval, amplifiedDirection_eval, hrows.1, hrows.2,
      hzero]
    simp

theorem amplified_core_pair_agreement_stack
    (L : CommonLocatorData) (i : Fin 3) (e : Coord)
    (he : e ∈ amplifiedCoreSet i) :
    (amplifiedIntercept L i).eval (domain e) = amplifiedU L 0 e ∧
      (amplifiedDirection L i).eval (domain e) = amplifiedU L 1 e := by
  rw [amplifiedU_zero, amplifiedU_one]
  exact amplified_core_pair_agreement L i e he

end ArkLib.ProximityGap.Frontier.P1RateQuarterSaturatedConstruction
