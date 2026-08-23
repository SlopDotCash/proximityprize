/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Spartan.TightComposedFull
import ArkLib.ProofSystem.Spartan.TightFinalTrivial

/-!
# The tight composed chain at the pure terminal check (issue #329, B7 apex pairing)

The canonical tight chain for the **paired** apex (KS *and* completeness on one protocol):
`composedPIOPTightPure_Rc` — the eight-phase tight composition ending at `finalCheckPure`
(the trivial-predicate terminal check, whose binding currency is the semantic relation
`tightFinalRelOut`). The rbr-KS apex re-instantiates the FC-generic fold of
`TightComposedFull.lean` at `FC := finalCheckPure` with the proven pure h₈ leaf — same
relations, same tight error vector. The completeness side (`finalCheckPure_perfectCompleteness`
+ the enriched/strengthened sum-check legs) consumes the same chain.
-/

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace Spartan.Spec.Bricks

set_option linter.unusedSectionVars false

noncomputable section

variable {R : Type 0} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] [Inhabited R]
  [SampleableType R] (pp : PublicParams)

variable {ι : Type} (oSpec : OracleSpec ι)

/-- Universe-pinned alias of the pure terminal check (the fold's `FC` slot). -/
abbrev finalCheckPureKS :
    OracleReduction.{0, 0} oSpec
      (Statement.AfterSecondSumcheckWithTarget R pp)
      (OracleStatement.AfterLinearCombination R pp) Unit
      (Statement.AfterSecondSumcheckWithTarget R pp)
      (OracleStatement.AfterLinearCombination R pp) Unit !p[] :=
  finalCheckPure pp oSpec

/-- **The tight composed Spartan PIOP at the pure terminal check** — the canonical chain
carrying both the tight rbr-KS and perfect completeness. -/
noncomputable def composedPIOPTightPure_Rc :
    OracleReduction oSpec
      (Statement R pp) (OracleStatement R pp) (Witness R pp)
      (Statement.AfterSecondSumcheckWithTarget R pp)
      (OracleStatement.AfterLinearCombination R pp) Unit
      (composedPSpec (R := R) pp) :=
  (oracleReduction.firstMessage R pp oSpec).append <|
  (oracleReduction.firstChallenge R pp oSpec).append <|
    (firstSumcheckReductionWithTarget pp oSpec).append <|
    (sendEvalClaimWithTarget pp oSpec).append <|
    (linearCombinationWithTarget pp oSpec).append <|
    (prependRLCTargetWithTarget pp oSpec).append <|
    (secondSumcheckReductionWithTarget pp oSpec).append <|
    (finalCheckPureKS pp oSpec)

section Apex

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

set_option linter.unusedFintypeInType false in
set_option maxHeartbeats 1000000 in
/-- **THE TIGHT rbr KNOWLEDGE SOUNDNESS at the pure terminal check** (issue #329): identical
relations and error vector as `composedTightFull_rbrKnowledgeSoundness`, on the chain that also
carries the perfect completeness. -/
theorem composedTightPure_rbrKnowledgeSoundness [Subsingleton σ]
    (hm : 0 < pp.ℓ_m) (hn : 0 < pp.ℓ_n)
    [Inhabited (Statement.AfterSecondSumcheckWithTarget R pp ×
      ∀ i, OracleStatement.AfterLinearCombination R pp i)]
    [Inhabited (Statement.AfterFirstSumcheckWithTarget R pp ×
      ∀ i, OracleStatement.AfterFirstSumcheck R pp i)]
    (hInit : ∃ s, s ∈ support init) (hInitNF : Pr[⊥ | init] = 0)
    (hNE_B : Nonempty (Statement.AfterFirstMessage R pp ×
      ∀ i, OracleStatement.AfterFirstMessage R pp i))
    (hNE_C : Nonempty (Statement.AfterFirstChallenge R pp ×
      ∀ i, OracleStatement.AfterFirstChallenge R pp i))
    (hNE_E : Nonempty (Statement.AfterSendEvalClaimWithTarget R pp ×
      ∀ i, OracleStatement.AfterSendEvalClaim R pp i))
    (hNE_F : Nonempty (Statement.AfterLinearCombinationWithTarget R pp ×
      ∀ i, OracleStatement.AfterLinearCombination R pp i))
    (hNE_G : Nonempty ((R × Statement.AfterLinearCombinationWithTarget R pp) ×
      ∀ i, OracleStatement.AfterLinearCombination R pp i)) :
    (composedPIOPTightPure_Rc (R := R) pp oSpec).verifier.rbrKnowledgeSoundness init impl
      (spartanRelIn R pp) (tightFinalRelOut (R := R) pp)
      (composedRbrError pp
        (0 : (⟨!v[.P_to_V], !v[Witness R pp]⟩ : ProtocolSpec 1).ChallengeIdx → ℝ≥0)
        (fun _ => (pp.ℓ_m : ℝ≥0) / (Fintype.card R : ℝ≥0))
        (fun _ => (3 : ℝ≥0) / (Fintype.card R))
        (0 : (⟨!v[.P_to_V], !v[∀ i, EvalClaim R i]⟩ : ProtocolSpec 1).ChallengeIdx → ℝ≥0)
        (fun _ => (1 : ℝ≥0) / (Fintype.card R : ℝ≥0))
        (0 : (!p[] : ProtocolSpec 0).ChallengeIdx → ℝ≥0)
        (fun _ => (2 : ℝ≥0) / (Fintype.card R))
        (0 : (!p[] : ProtocolSpec 0).ChallengeIdx → ℝ≥0)) := by
  obtain ⟨verify₁, hV₁⟩ := firstMessage_toVerifier_pure (R := R) pp oSpec
  obtain ⟨verify₃?, hV₃⟩ := firstSumcheckWithTarget_toVerifier_isFailingDet (R := R) pp oSpec
  obtain ⟨verify₇?, hV₇⟩ := secondSumcheckWithTarget_toVerifier_isFailingDet (R := R) pp oSpec
  have h₂ : (oracleReduction.firstChallenge.{0} R pp oSpec).verifier.rbrKnowledgeSoundness
      init impl
      (firstMessageRbrRelB (R := R) pp)
      (firstSumcheckWithTargetRbrRelIn (R := R) pp oSpec)
      (fun _ => (pp.ℓ_m : ℝ≥0) / (Fintype.card R : ℝ≥0)) := by
    rw [firstSumcheckWithTargetRbrRelIn_eq_relIn]
    exact firstChallenge_rbrKnowledgeSoundness_schwartzZippel pp oSpec hm
  exact composedPIOPTightFull_rbrKnowledgeSoundness_of_leaves.{0, 0, 0, 0} pp oSpec
    (finalCheckPureKS pp oSpec) hm hn
    verify₁ hV₁
    (fun p tr => ((fun p (c : FirstChallenge R pp) => ((c, p.1), p.2)) p
      (tr.challenges ⟨0, rfl⟩)))
    (firstChallenge_toVerifier_closed pp oSpec)
    verify₃? hV₃
    (fun p tr => sendEvalClaimWithTargetRouteMap (R := R) pp p (tr.messages ⟨0, rfl⟩))
    (sendEvalClaimWithTarget_toVerifier_closed pp oSpec)
    (fun p tr => ((fun p (c : LinearCombinationChallenge R) => ((c, p.1), p.2)) p
      (tr.challenges ⟨0, rfl⟩)))
    (linearCombinationWithTarget_toVerifier_closed pp oSpec)
    (fun p _tr => ((∑ idx, p.1.1 idx * p.2 (.inl 0) idx, p.1), p.2))
    (prependRLCTargetWithTarget_toVerifier_pure pp oSpec)
    verify₇? hV₇
    (firstMessage_rbrKnowledgeSoundness_spartanRelIn pp oSpec)
    h₂
    (firstSumcheckWithTarget_rbrKnowledgeSoundness_honest_full pp oSpec hInit hInitNF)
    (sendEvalClaimWithTarget_rbrKnowledgeSoundness_leaf pp oSpec)
    (linearCombinationWithTarget_rbrKnowledgeSoundness_leaf.{0} pp oSpec)
    (prependRLCTargetWithTarget_rbrKnowledgeSoundness_leaf' pp oSpec)
    (secondSumcheckWithTarget_conjoined_rbrKnowledgeSoundness pp oSpec hInit hInitNF)
    (finalCheckPure_rbrKnowledgeSoundness pp oSpec)
    hInit hInitNF hNE_B hNE_C hNE_E hNE_F hNE_G

end Apex

end

end Spartan.Spec.Bricks

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms Spartan.Spec.Bricks.composedPIOPTightPure_Rc
#print axioms Spartan.Spec.Bricks.composedTightPure_rbrKnowledgeSoundness
