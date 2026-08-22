/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterSaturatedConstruction

/-!
# _P1RateQuarterSaturatedPairAgreement

Module docstring for `_P1RateQuarterSaturatedPairAgreement.lean`.
-/


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false
set_option maxHeartbeats 500000
set_option maxRecDepth 500000

open Finset Polynomial
open _root_.ProximityGap Code
open scoped NNReal Polynomial

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterSaturatedConstructionLegacy

open ArkLib.ProximityGap.PrizeShapePrimeP30
open P1RateQuarterScaleArithmetic
open P1RateQuarterScaleConstruction
open P1RateQuarterCommonFactorConstruction
open RateQuarterCommonFactorOwnershipAmplifier

local instance localInstance_P1RateQuarterSaturatedPairAgreement_1 : Fact (Nat.Prime P) := ⟨prime_P⟩
attribute [local instance] Classical.propDecidable

theorem amplified_pair_agreement_of_old_values
    (L : CommonLocatorData) (f : F[X]) (e : Coord)
    (hu0 : domain e * f.eval (domain e) = u0 e)
    (hu1 : f.eval (domain e) = u1 e) (hnew : e ∉ newHoles) :
    ((Polynomial.X : F[X]) * (L.polynomial * f)).eval (domain e) =
        amplifiedU0 L e ∧
      (L.polynomial * f).eval (domain e) = amplifiedU1 L e := by
  have hrows := amplifiedU_rows_of_not_mem_newHoles (L := L) (e := e) hnew
  rw [eval_mul, eval_X, eval_mul, hrows.1, hrows.2]
  constructor
  · calc
      domain e * (L.polynomial.eval (domain e) * f.eval (domain e)) =
          L.polynomial.eval (domain e) *
            (domain e * f.eval (domain e)) := by ring
      _ = L.polynomial.eval (domain e) * u0 e := by rw [hu0]
  · rw [hu1]

theorem amplified_pair_agreement_of_old_core
    (L : CommonLocatorData) (i : Fin 3) (e : Coord)
    (hcore : corePred i e) (hnew : e ∉ newHoles) :
    (amplifiedIntercept L i).eval (domain e) = amplifiedU0 L e ∧
      (amplifiedDirection L i).eval (domain e) = amplifiedU1 L e := by
  have holdAgree :
      (intercept i).eval (domain e) = u0 e ∧
        (direction i).eval (domain e) = u1 e := by
    rcases hcore with hbase | heTransfer
    · have hne15 : e.2 ≠ (15 : Fin 16) := by
        intro h
        rw [h] at hbase
        exact fifteen_not_mem_baseCore i hbase
      have hcompat := ordinaryLine_compatible i e.2 hbase
      have hline : lineAt e = some (ordinaryLine e.2) := by
        simp [lineAt, hne15]
      have hu0 : u0 e = domain e *
          (direction (ordinaryLine e.2)).eval (domain e) := by
        simp only [u0, hline]
      have hu1 : u1 e =
          (direction (ordinaryLine e.2)).eval (domain e) := by
        simp only [u1, hline]
      constructor
      · rw [intercept, eval_mul, eval_X, hu0, direction_eval,
          direction_eval, hcompat]
      · rw [hu1, direction_eval, direction_eval, hcompat]
    · obtain ⟨⟨q, heq1⟩, heq2⟩ := heTransfer
      have heq : e = (Sum.inl (i, q), (15 : Fin 16)) := Prod.ext heq1 heq2
      subst e
      constructor
      · simp only [intercept, eval_mul, eval_X, u0, lineAt_transfer]
      · simp only [u1, lineAt_transfer]
  have hu0 : domain e * (direction i).eval (domain e) = u0 e := by
    simpa only [intercept, eval_mul, eval_X] using holdAgree.1
  simpa only [amplifiedIntercept, amplifiedDirection, amplifiedFactor] using
    amplified_pair_agreement_of_old_values L (direction i) e hu0
      holdAgree.2 hnew

theorem amplified_pair_agreement_of_common_root
    (L : CommonLocatorData) (i : Fin 3) (e : Coord)
    (hroot : e ∈ commonRoots) :
    (amplifiedIntercept L i).eval (domain e) = amplifiedU0 L e ∧
      (amplifiedDirection L i).eval (domain e) = amplifiedU1 L e := by
  have hzero := L.eval_zero hroot
  have hnotHole : e ∉ newHoles := commonRoot_not_mem_newHoles hroot
  have hrows := amplifiedU_rows_of_not_mem_newHoles (L := L) (e := e) hnotHole
  rw [amplifiedIntercept_eval, amplifiedDirection_eval, hrows.1, hrows.2,
    hzero]
  simp

end ArkLib.ProximityGap.Frontier.P1RateQuarterSaturatedConstructionLegacy

open ArkLib.ProximityGap.Frontier.P1RateQuarterSaturatedConstructionLegacy
#print axioms amplified_pair_agreement_of_old_values
#print axioms amplified_pair_agreement_of_old_core
#print axioms amplified_pair_agreement_of_common_root
