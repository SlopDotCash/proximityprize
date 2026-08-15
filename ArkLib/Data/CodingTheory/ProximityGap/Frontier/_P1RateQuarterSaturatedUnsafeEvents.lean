/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterSaturatedCore

/-!
# Unsafe events for the saturated P1 common-factor construction
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

local instance localInstance_P1RateQuarterSaturatedUnsafeEvents_1 : Fact (Nat.Prime P) := ⟨prime_P⟩
attribute [local instance] Classical.propDecidable

local notation "δsat" => P1RateQuarterCommonFactorArithmetic.delta

/-! ## The `d+1` saturated hole coordinates -/

/-- The `d` selected residue-thirteen holes followed by the old singleton
residue-fifteen hole. -/
abbrev SaturatedHoleIndex := SelectedFibreIndex ⊕ Fin 1

def saturatedHoleCoord : SaturatedHoleIndex → Coord
  | Sum.inl q => selectedCoordEmbedding 13 q
  | Sum.inr _ => hole

def saturatedHoleKind : SaturatedHoleIndex → Fin 2
  | Sum.inl _ => 0
  | Sum.inr _ => 1

theorem saturatedHoleCoord_injective : Function.Injective saturatedHoleCoord := by
  intro a b h
  rcases a with q | a <;> rcases b with q' | b
  · apply congrArg Sum.inl
    exact (selectedCoordEmbedding 13).injective h
  · exfalso
    have hsnd : (13 : Fin 16) = 15 := by
      simpa only [saturatedHoleCoord, selectedCoordEmbedding, hole] using
        congrArg Prod.snd h
    exact (by decide : (13 : Fin 16) ≠ 15) hsnd
  · exfalso
    have hsnd : (15 : Fin 16) = 13 := by
      simpa only [saturatedHoleCoord, selectedCoordEmbedding, hole] using
        congrArg Prod.snd h
    exact (by decide : (15 : Fin 16) ≠ 13) hsnd
  · exact congrArg Sum.inr (Subsingleton.elim a b)

theorem saturatedHoleCoord_mem_newHoles (q : SelectedFibreIndex) :
    saturatedHoleCoord (Sum.inl q) ∈ newHoles := by
  exact (mem_selectedCoords_iff 13 _).2 ⟨q, rfl⟩

theorem saturatedHoleCoord_old (a : Fin 1) :
    saturatedHoleCoord (Sum.inr a) = hole := rfl

theorem saturatedHoleCoord_not_mem_commonRoots (h : SaturatedHoleIndex) :
    saturatedHoleCoord h ∉ commonRoots := by
  rcases h with q | a
  · intro hroot
    exact (Finset.disjoint_left.mp commonRoots_disjoint_newHoles) hroot
      (saturatedHoleCoord_mem_newHoles q)
  · exact hole_not_mem_commonRoots

theorem saturatedHole_locator_ne_zero (L : CommonLocatorData)
    (h : SaturatedHoleIndex) :
    L.polynomial.eval (domain (saturatedHoleCoord h)) ≠ 0 :=
  L.eval_ne_zero (saturatedHoleCoord_not_mem_commonRoots h)

theorem saturatedHoleCoord_not_mem_amplifiedCore
    (i : Fin 3) (h : SaturatedHoleIndex) :
    saturatedHoleCoord h ∉ amplifiedCoreSet i := by
  intro hmem
  rw [amplifiedCoreSet, Finset.mem_union] at hmem
  rcases hmem with hold | hroot
  · rw [Finset.mem_sdiff] at hold
    rcases hold with ⟨hcore, hnotNew⟩
    rcases h with q | a
    · apply hnotNew
      exact (mem_selectedCoords_iff 13 _).2 ⟨q, rfl⟩
    ·
      simp only [core, corePred, Finset.mem_filter, Finset.mem_univ,
        true_and] at hcore
      rcases hcore with hbase | htransfer
      · apply fifteen_not_mem_baseCore i
        simpa only [saturatedHoleCoord, hole] using hbase
      · obtain ⟨⟨q, hq⟩, -⟩ := htransfer
        have himpossible :
            (Sum.inr (0 : Fin 1) : FibreIndex) = Sum.inl (i, q) := by
          simpa only [saturatedHoleCoord, hole] using hq
        cases himpossible
  · exact saturatedHoleCoord_not_mem_commonRoots h hroot

theorem saturatedHole_domain_pow_m (h : SaturatedHoleIndex) :
    domain (saturatedHoleCoord h) ^ m =
      holeFibreValue (saturatedHoleKind h) := by
  rcases h with q | a
  · rw [domain_pow_m]
    simp [saturatedHoleCoord, saturatedHoleKind, holeFibreValue,
      selectedCoordEmbedding]
  · rw [domain_pow_m]
    simp [saturatedHoleCoord, saturatedHoleKind, holeFibreValue, hole]

/-- Direction values on the two kinds of saturated holes. -/
def saturatedHoleValue : Fin 2 → Fin 3 → F := ![
  newHoleValue,
  holeValue]

theorem saturatedHoleValue_ne_two (a : Fin 2) (i : Fin 3) :
    saturatedHoleValue a i ≠ (2 : F) := by
  fin_cases a
  · exact newHoleValue_ne_two i
  · exact holeValue_ne_two i

theorem direction_eval_saturatedHole (i : Fin 3) (h : SaturatedHoleIndex) :
    (direction i).eval (domain (saturatedHoleCoord h)) =
      saturatedHoleValue (saturatedHoleKind h) i := by
  rcases h with q | a
  · have hdir :
        (direction i).eval (domain (saturatedHoleCoord (Sum.inl q))) =
          newHoleValue i := by
      apply direction_eval_newHole i
      exact (mem_selectedCoords_iff 13 _).2 ⟨q, rfl⟩
    simpa only [saturatedHoleKind, saturatedHoleValue] using hdir
  · simpa only [saturatedHoleCoord, saturatedHoleKind, saturatedHoleValue,
      hole] using direction_eval_hole_fibre i (Sum.inr 0)

theorem saturatedHoleConstant_cross (a : Fin 2) (i : Fin 3) :
    holeConstant a i * (2 - saturatedHoleValue a i) =
      saturatedHoleValue a i - 1 := by
  fin_cases a
  · simpa [holeConstant, saturatedHoleValue] using
      (eq_div_iff (sub_ne_zero.mpr (newHoleValue_ne_two i).symm)).mp
        (newUnsafeConstant_formula i)
  · simpa [holeConstant, saturatedHoleValue] using
      (eq_div_iff (sub_ne_zero.mpr (holeValue_ne_two i).symm)).mp
        (unsafeConstant_formula i)

theorem saturatedHole_fold_identity (a : Fin 2) (i : Fin 3) :
    saturatedHoleValue a i * (1 + holeConstant a i) =
      1 + 2 * holeConstant a i := by
  have hc := saturatedHoleConstant_cross a i
  linear_combination -hc

theorem amplifiedU_rows_saturatedHole
    (L : CommonLocatorData) (h : SaturatedHoleIndex) :
    amplifiedU0 L (saturatedHoleCoord h) =
        L.polynomial.eval (domain (saturatedHoleCoord h)) *
          domain (saturatedHoleCoord h) ∧
      amplifiedU1 L (saturatedHoleCoord h) =
        L.polynomial.eval (domain (saturatedHoleCoord h)) * 2 := by
  rcases h with q | a
  · apply amplifiedU_rows_of_mem_newHoles L
    exact (mem_selectedCoords_iff 13 _).2 ⟨q, rfl⟩
  · have hrows := amplifiedU_rows_of_not_mem_newHoles L
        (show hole ∉ newHoles from hole_not_mem_newHoles)
    simpa only [saturatedHoleCoord, hole_rows.1, hole_rows.2] using hrows

noncomputable def saturatedUnsafeGamma
    (h : SaturatedHoleIndex) (i : Fin 3) : F :=
  holeConstant (saturatedHoleKind h) i * domain (saturatedHoleCoord h)

theorem saturated_unsafe_fresh_agreement
    (L : CommonLocatorData) (h : SaturatedHoleIndex) (i : Fin 3) :
    (amplifiedIntercept L i + C (saturatedUnsafeGamma h i) *
      amplifiedDirection L i).eval (domain (saturatedHoleCoord h)) =
      amplifiedU0 L (saturatedHoleCoord h) + saturatedUnsafeGamma h i *
        amplifiedU1 L (saturatedHoleCoord h) := by
  let x := domain (saturatedHoleCoord h)
  let ell := L.polynomial.eval x
  let a := saturatedHoleKind h
  let t := saturatedHoleValue a i
  let c := holeConstant a i
  have ht := direction_eval_saturatedHole i h
  have hrows := amplifiedU_rows_saturatedHole L h
  have hfold := saturatedHole_fold_identity a i
  simp only [eval_add, eval_mul, eval_C, amplifiedIntercept_eval,
    amplifiedDirection_eval]
  rw [ht, hrows.1, hrows.2]
  change x * (ell * t) + (c * x) * (ell * t) =
    ell * x + (c * x) * (ell * 2)
  calc
    x * (ell * t) + (c * x) * (ell * t) =
        ell * x * (t * (1 + c)) := by ring
    _ = ell * x * (1 + 2 * c) := by rw [hfold]
    _ = ell * x + (c * x) * (ell * 2) := by ring

theorem saturated_unsafe_pair_mismatch
    (L : CommonLocatorData) (h : SaturatedHoleIndex) (i : Fin 3) :
    ((amplifiedIntercept L i).eval (domain (saturatedHoleCoord h)),
      (amplifiedDirection L i).eval (domain (saturatedHoleCoord h))) ≠
      (amplifiedU0 L (saturatedHoleCoord h),
        amplifiedU1 L (saturatedHoleCoord h)) := by
  intro hpairs
  have hsecond := congrArg Prod.snd hpairs
  rw [amplifiedDirection_eval, direction_eval_saturatedHole,
    (amplifiedU_rows_saturatedHole L h).2] at hsecond
  have ht : saturatedHoleValue (saturatedHoleKind h) i = (2 : F) :=
    mul_left_cancel₀ (saturatedHole_locator_ne_zero L h) hsecond
  exact saturatedHoleValue_ne_two (saturatedHoleKind h) i ht

theorem saturated_unsafe_mcaEvent
    (L : CommonLocatorData) (h : SaturatedHoleIndex) (i : Fin 3) :
    mcaEvent
      ((ReedSolomon.code domain k : Submodule F (Coord → F)) :
        Set (Coord → F))
      δsat (amplifiedU L 0) (amplifiedU L 1)
        (saturatedUnsafeGamma h i) := by
  apply mcaEvent_of_affine_core_fresh domain k δsat (amplifiedU L)
    (saturatedUnsafeGamma h i) (amplifiedCoreSet i)
    (saturatedHoleCoord h) (amplifiedIntercept L i) (amplifiedDirection L i)
  · exact saturatedHoleCoord_not_mem_amplifiedCore i h
  · exact amplifiedIntercept_degree_lt_k L i
  · exact amplifiedDirection_degree_lt_k L i
  · exact amplifiedAffine_degree_lt_k L i (saturatedUnsafeGamma h i)
  · exact amplifiedCoreSet_card_ge_k i
  · exact amplifiedCoreSet_size_condition i
  · exact amplified_core_pair_agreement_stack L i
  · simpa only [amplifiedU_zero, amplifiedU_one] using
      saturated_unsafe_fresh_agreement L h i
  · simpa only [amplifiedU_zero, amplifiedU_one] using
      saturated_unsafe_pair_mismatch L h i

end ArkLib.ProximityGap.Frontier.P1RateQuarterSaturatedConstruction
