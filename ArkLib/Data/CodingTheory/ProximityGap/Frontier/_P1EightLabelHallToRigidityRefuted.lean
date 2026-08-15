/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterSmallSubsetRankLocalization
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._GaugedTensorSpanConcreteRefutedF7
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SupportDividedDifferenceUnrestrictedKernelRefuted

/-!
# The eight-label Hall kernel does not by itself imply divided-difference rigidity

The P1 localization theorem proves that deleting at most eight labels makes every remaining
subset projected-Hall-safe.  A tempting next step is to treat the deleted labels as gauge anchors
and infer degree-restricted kernel rigidity from the complement Hall inequalities.

This file refutes that implication in the exact operator vocabulary.  The existing `F_7`
five-label tensor certificate has anchors `0,1`; every subset disjoint from those anchors obeys
the full degree-two projected Hall budget, yet a nonzero degree-one polynomial family is in the
divided-difference kernel and vanishes at both anchors.

Consequently, constant-width localization is useful only together with genuinely algebraic
maximal-recoverability input.  No Hall-only local-to-global theorem can finish the exact P1 pin.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.P1EightLabelHallToRigidityRefuted

open SupportDividedDifferenceUnrestrictedKernelRefuted
open P1RateQuarterSmallSubsetRankLocalization
open GaugedTensorSpanConcreteRefutedF7

local instance localInstance_P1EightLabelHallToRigidityRefuted_1 : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- The two anchors form an exceptional set outside which every subset satisfies the exact
`projectedBudget` inequality used by the P1 localization lane. -/
theorem fullHall_outside_two_anchors :
    ∀ U : Finset Label, Disjoint U ({0, 1} : Finset Label) →
      U.card * 2 ≤
        P1RateQuarterSmallSubsetRankLocalization.projectedBudget support U := by
  intro U hdisjoint
  have hsub : U ⊆ nonAnchors := by
    intro j hj
    have hj0 : j ≠ 0 := by
      intro h
      subst j
      exact (Finset.disjoint_left.mp hdisjoint) hj (by simp)
    have hj1 : j ≠ 1 := by
      intro h
      subst j
      exact (Finset.disjoint_left.mp hdisjoint) hj (by simp)
    fin_cases j <;> simp_all [nonAnchors]
  simpa [P1RateQuarterSmallSubsetRankLocalization.projectedBudget,
    GaugedTensorSpanConcreteRefutedF7.projectedBudget, Nat.mul_comm] using
      projectedHall_safe U hsub

/-- The same Hall-safe complement nevertheless has a nonzero degree-restricted gauged kernel. -/
theorem degreeAnchoredKernelRigid_refuted :
    ¬ DegreeAnchoredKernelRigid domain support label 2 0 1 := by
  intro hrigid
  apply q_ne_zero
  exact hrigid q q_degreeLT_two q_mem_kernel q_anchor_zero.1 q_anchor_zero.2

/-- **Hall-to-rigidity refutation.**  Even an exceptional set of cardinality two can have every
complement subset Hall-safe while the corresponding two-anchor kernel is nontrivial. -/
theorem hall_complement_does_not_force_rigidity :
    (({0, 1} : Finset Label).card ≤ 8 ∧
      (∀ U : Finset Label, Disjoint U ({0, 1} : Finset Label) →
        U.card * 2 ≤
          P1RateQuarterSmallSubsetRankLocalization.projectedBudget support U)) ∧
      ¬ DegreeAnchoredKernelRigid domain support label 2 0 1 := by
  refine ⟨⟨by decide, fullHall_outside_two_anchors⟩,
    degreeAnchoredKernelRigid_refuted⟩

end ArkLib.ProximityGap.Frontier.P1EightLabelHallToRigidityRefuted

open ArkLib.ProximityGap.Frontier.P1EightLabelHallToRigidityRefuted

#print axioms fullHall_outside_two_anchors
#print axioms degreeAnchoredKernelRigid_refuted
#print axioms hall_complement_does_not_force_rigidity
