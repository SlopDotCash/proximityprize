/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterSaturatedConstruction

/-!
# _P1RateQuarterSaturatedOldAgreement

Module docstring for `_P1RateQuarterSaturatedOldAgreement.lean`.
-/


set_option autoImplicit false
set_option linter.constructorNameAsVariable false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 500000
set_option maxRecDepth 100000

open Finset Polynomial
open _root_.ProximityGap Code
open scoped NNReal Polynomial

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterSaturatedConstructionLegacy

open ArkLib.ProximityGap.PrizeShapePrimeP30
open P1RateQuarterScaleArithmetic
open P1RateQuarterScaleConstruction

local instance localInstance_P1RateQuarterSaturatedOldAgreement_1 : Fact (Nat.Prime P) := ⟨prime_P⟩
attribute [local instance] Classical.propDecidable

/-- Kernel-cheap reconstruction of old-core agreement, isolated from the
billion-scale selected-coordinate definitions. -/
theorem old_core_pair_agreement_fast (i : Fin 3) (e : Coord)
    (he : e ∈ core i) :
    (intercept i).eval (domain e) = u0 e ∧
      (direction i).eval (domain e) = u1 e := by
  simp only [core, corePred, Finset.mem_filter, Finset.mem_univ, true_and] at he
  rcases he with hbase | heTransfer
  · have hne15 : e.2 ≠ (15 : Fin 16) := by
      intro h
      rw [h] at hbase
      exact fifteen_not_mem_baseCore i hbase
    have hcompat := ordinaryLine_compatible i e.2 hbase
    have hline : lineAt e = some (ordinaryLine e.2) := by simp [lineAt, hne15]
    have hu0 : u0 e = domain e *
        (direction (ordinaryLine e.2)).eval (domain e) := by
      simp only [u0, hline]
    have hu1 : u1 e = (direction (ordinaryLine e.2)).eval (domain e) := by
      simp only [u1, hline]
    constructor
    · rw [intercept, eval_mul, eval_X, hu0, direction_eval, direction_eval,
        hcompat]
    · rw [hu1, direction_eval, direction_eval, hcompat]
  · obtain ⟨⟨q, heq1⟩, heq2⟩ := heTransfer
    have heq : e = (Sum.inl (i, q), (15 : Fin 16)) := Prod.ext heq1 heq2
    subst e
    constructor
    · simp only [intercept, eval_mul, eval_X, u0, lineAt_transfer]
    · simp only [u1, lineAt_transfer]

end ArkLib.ProximityGap.Frontier.P1RateQuarterSaturatedConstructionLegacy

open ArkLib.ProximityGap.Frontier.P1RateQuarterSaturatedConstructionLegacy
#print axioms old_core_pair_agreement_fast
