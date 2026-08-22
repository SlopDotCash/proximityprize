/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterSaturatedCore

/-!
# Safe events for the saturated P1 common-factor construction
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

local instance localInstance_P1RateQuarterSaturatedSafeEvents_1 : Fact (Nat.Prime P) := ⟨prime_P⟩
attribute [local instance] Classical.propDecidable

local notation "δsat" => P1RateQuarterCommonFactorArithmetic.delta

/-! ## Safe one-fresh-coordinate certificates -/

theorem old_received_rows_on_line (e : Coord) (he : e ≠ hole) :
    u0 e = domain e * u1 e := by
  have hcovered : lineAt e ≠ none := by
    intro hnone
    rcases e with ⟨j, a⟩
    simp only [lineAt] at hnone
    split at hnone
    · rename_i ha
      subst a
      rcases j with iq | hlast
      · simp at hnone
      · apply he
        exact Prod.ext (congrArg Sum.inr (Subsingleton.elim hlast 0)) rfl
    · simp at hnone
  rcases hline : lineAt e with _ | owner
  · exact (hcovered hline).elim
  · simp only [u0, u1, hline]

noncomputable def saturatedSafeSource (e : Coord) (he : e ≠ hole) : Fin 3 :=
  P1RateQuarterScaleBadCount.safeSource e he

theorem saturatedSafeSource_not_mem_oldCore (e : Coord) (he : e ≠ hole) :
    e ∉ core (saturatedSafeSource e he) :=
  P1RateQuarterScaleBadCount.safeSource_not_mem e he

private theorem saturatedSafeSource_not_corePred
    (e : Coord) (he : e ≠ hole) :
    ¬corePred (saturatedSafeSource e he) e := by
  intro hpred
  apply saturatedSafeSource_not_mem_oldCore e he
  simpa only [core, Finset.mem_filter, Finset.mem_univ, true_and] using hpred

theorem saturatedSafeSource_old_mismatch (e : Coord) (he : e ≠ hole) :
    (direction (saturatedSafeSource e he)).eval (domain e) ≠ u1 e :=
  P1RateQuarterScaleBadCount.safeSource_mismatch e he

theorem saturatedSafeSource_not_mem_amplifiedCore
    (e : Coord) (he : e ≠ hole) (hroot : e ∉ commonRoots) :
    e ∉ amplifiedCoreSet (saturatedSafeSource e he) := by
  intro hmem
  rw [amplifiedCoreSet, Finset.mem_union] at hmem
  rcases hmem with hold | hcommon
  · rw [Finset.mem_sdiff] at hold
    rcases hold with ⟨hcore, -⟩
    simp only [core, Finset.mem_filter, Finset.mem_univ, true_and] at hcore
    exact saturatedSafeSource_not_corePred e he hcore
  · exact hroot hcommon

theorem saturated_safe_direction_mismatch
    (L : CommonLocatorData) (e : Coord) (he : e ≠ hole)
    (hnew : e ∉ newHoles) (hroot : e ∉ commonRoots) :
    (amplifiedDirection L (saturatedSafeSource e he)).eval (domain e) ≠
      amplifiedU1 L e := by
  rw [amplifiedDirection_eval,
    (amplifiedU_rows_of_not_mem_newHoles L hnew).2]
  intro hscaled
  apply saturatedSafeSource_old_mismatch e he
  exact mul_left_cancel₀ (L.eval_ne_zero hroot) hscaled

theorem saturated_safe_fresh_agreement
    (L : CommonLocatorData) (e : Coord) (he : e ≠ hole)
    (hnew : e ∉ newHoles) :
    (amplifiedIntercept L (saturatedSafeSource e he) +
      C (-domain e) * amplifiedDirection L (saturatedSafeSource e he)).eval
        (domain e) =
      amplifiedU0 L e + (-domain e) * amplifiedU1 L e := by
  let i := saturatedSafeSource e he
  have hrows := amplifiedU_rows_of_not_mem_newHoles L hnew
  have hold := old_received_rows_on_line e he
  simp only [eval_add, eval_mul, eval_C, amplifiedIntercept_eval]
  rw [hrows.1, hrows.2, hold]
  ring

theorem saturated_safe_mcaEvent
    (L : CommonLocatorData) (e : Coord) (he : e ≠ hole)
    (hnew : e ∉ newHoles) (hroot : e ∉ commonRoots) :
    mcaEvent
      ((ReedSolomon.code domain k : Submodule F (Coord → F)) :
        Set (Coord → F))
      δsat (amplifiedU L 0) (amplifiedU L 1) (-domain e) := by
  let i := saturatedSafeSource e he
  apply mcaEvent_of_affine_core_fresh domain k δsat (amplifiedU L)
    (-domain e) (amplifiedCoreSet i) e
    (amplifiedIntercept L i) (amplifiedDirection L i)
  · exact saturatedSafeSource_not_mem_amplifiedCore e he hroot
  · exact amplifiedIntercept_degree_lt_k L i
  · exact amplifiedDirection_degree_lt_k L i
  · exact amplifiedAffine_degree_lt_k L i (-domain e)
  · exact amplifiedCoreSet_card_ge_k i
  · exact amplifiedCoreSet_size_condition i
  · exact amplified_core_pair_agreement_stack L i
  · have hfresh := saturated_safe_fresh_agreement L e he hnew
    simpa only [i, amplifiedU_zero, amplifiedU_one] using hfresh
  · intro hpairs
    apply saturated_safe_direction_mismatch L e he hnew hroot
    have hsecond := congrArg (fun p : F × F => p.2) hpairs
    simpa only [i, amplifiedU_one] using hsecond

end ArkLib.ProximityGap.Frontier.P1RateQuarterSaturatedConstruction
