/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Spartan.ComposedRbrKnowledgeSoundness
import ArkLib.ProofSystem.Spartan.FinalCheckRbrKnowledgeLeaf
import ArkLib.ProofSystem.Spartan.PrependRLCDeterminism
import ArkLib.ProofSystem.Spartan.SumcheckDeterminismWitnesses
import ArkLib.ProofSystem.Spartan.SumcheckKnowledgeLeaves

/-!
# Spartan composed RBR-KS wiring progress (#114)

This module plugs the proven generic sum-check RBR-KS leaves and the verifier determinism witnesses
into the seven-seam composed Spartan RBR-KS fold.  The resulting theorem leaves only the genuine
non-sum-check relation leaves exposed.
-/

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace Spartan.Spec.Bricks

set_option linter.unusedSectionVars false

noncomputable section

variable {R : Type 0} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] [Inhabited R]
  [SampleableType R] (pp : PublicParams)

variable {ι : Type} (oSpec : OracleSpec ι)
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {relB : Set ((Statement.AfterFirstMessage R pp ×
    ∀ i, OracleStatement.AfterFirstMessage R pp i) × Unit)}
  {relE : Set ((Statement.AfterSendEvalClaim R pp ×
    ∀ i, OracleStatement.AfterSendEvalClaim R pp i) × Unit)}
  {relF : Set ((Statement.AfterLinearCombination R pp ×
    ∀ i, OracleStatement.AfterLinearCombination R pp i) × Unit)}

/-- Local mirror of `ComposedRbrKnowledgeSoundness`'s private universe-pinned adapter. -/
private abbrev prependRLCTargetKSWiring {ι : Type} (oSpec : OracleSpec ι) :
    OracleReduction.{0, 0} oSpec
      (Statement.AfterLinearCombination R pp) (OracleStatement.AfterLinearCombination R pp) Unit
      (R × Statement.AfterLinearCombination R pp)
      (OracleStatement.AfterLinearCombination R pp) Unit !p[] :=
  prependRLCTarget pp oSpec

/-- The composed Spartan RBR-KS residual after plugging in:

* all verifier determinism witnesses (`hV₁`-`hV₇`);
* the full first/second sum-check RBR-KS leaves, with errors `3 / |R|` and `2 / |R|`.

The remaining hypotheses are precisely the non-sum-check relation leaves, including the terminal
`finalCheck` leaf against the chosen relation chain. -/
theorem composedRbrKnowledgeSoundnessStatement_of_nonsumcheck_leaves [Subsingleton σ]
    (hm : 0 < pp.ℓ_m) (hn : 0 < pp.ℓ_n)
    [Inhabited (FinalStatement R pp × ∀ i, FinalOracleStatement R pp i)]
    [Inhabited (Statement.AfterFirstSumcheck R pp ×
      ∀ i, OracleStatement.AfterFirstSumcheck R pp i)]
    {err₁ : (⟨!v[.P_to_V], !v[Witness R pp]⟩ : ProtocolSpec 1).ChallengeIdx → ℝ≥0}
    {err₂ : (⟨!v[.V_to_P], !v[FirstChallenge R pp]⟩ : ProtocolSpec 1).ChallengeIdx → ℝ≥0}
    {err₄ : (⟨!v[.P_to_V], !v[∀ i, EvalClaim R i]⟩ : ProtocolSpec 1).ChallengeIdx → ℝ≥0}
    {err₅ : (⟨!v[.V_to_P], !v[LinearCombinationChallenge R]⟩ :
      ProtocolSpec 1).ChallengeIdx → ℝ≥0}
    {err₆ : (!p[] : ProtocolSpec 0).ChallengeIdx → ℝ≥0}
    {err₈ : (!p[] : ProtocolSpec 0).ChallengeIdx → ℝ≥0}
    (h₁ : (oracleReduction.firstMessage R pp oSpec).verifier.rbrKnowledgeSoundness init impl
      (spartanRelIn R pp) relB err₁)
    (h₂ : (oracleReduction.firstChallenge.{0} R pp oSpec).verifier.rbrKnowledgeSoundness init impl
      relB (firstSumcheckRbrRelIn (R := R) pp oSpec) err₂)
    (h₄ : (oracleReduction.sendEvalClaim R pp oSpec).verifier.rbrKnowledgeSoundness init impl
      (firstSumcheckRbrRelOut (R := R) pp oSpec) relE err₄)
    (h₅ : (oracleReduction.linearCombination.{0} R pp oSpec).verifier.rbrKnowledgeSoundness
      init impl relE relF err₅)
    (h₆ : (prependRLCTargetKSWiring (R := R) pp oSpec).verifier.rbrKnowledgeSoundness init impl
      relF (secondSumcheckRbrRelIn (R := R) pp oSpec) err₆)
    (h₈ : (finalCheck R pp oSpec).verifier.rbrKnowledgeSoundness init impl
      (secondSumcheckRbrRelOut (R := R) pp oSpec) (finalCheckRelOut R pp) err₈)
    (hInit : ∃ s, s ∈ support init) (hInitNF : Pr[⊥ | init] = 0)
    (hNE_B : Nonempty (Statement.AfterFirstMessage R pp ×
      ∀ i, OracleStatement.AfterFirstMessage R pp i))
    (hNE_C : Nonempty (Statement.AfterFirstChallenge R pp ×
      ∀ i, OracleStatement.AfterFirstChallenge R pp i))
    (hNE_E : Nonempty (Statement.AfterSendEvalClaim R pp ×
      ∀ i, OracleStatement.AfterSendEvalClaim R pp i))
    (hNE_F : Nonempty (Statement.AfterLinearCombination R pp ×
      ∀ i, OracleStatement.AfterLinearCombination R pp i))
    (hNE_G : Nonempty ((R × Statement.AfterLinearCombination R pp) ×
      ∀ i, OracleStatement.AfterLinearCombination R pp i)) :
    composedRbrKnowledgeSoundnessStatement R pp oSpec (composedPIOP_Rc pp oSpec) init impl
      (composedRbrError pp err₁ err₂ (fun _ => (3 : ℝ≥0) / (Fintype.card R))
        err₄ err₅ err₆ (fun _ => (2 : ℝ≥0) / (Fintype.card R)) err₈) := by
  obtain ⟨verify₁, hV₁⟩ := firstMessage_toVerifier_pure (R := R) pp oSpec
  obtain ⟨verify₂, hV₂⟩ := firstChallenge_toVerifier_pure.{0} (R := R) pp oSpec
  obtain ⟨verify₃?, hV₃⟩ :=
    Spartan.Spec.firstSumcheck_toVerifier_isFailingDet (R := R) pp oSpec
  obtain ⟨verify₄, hV₄⟩ := sendEvalClaim_toVerifier_pure (R := R) pp oSpec
  obtain ⟨verify₅, hV₅⟩ := linearCombination_toVerifier_pure.{0} (R := R) pp oSpec
  let verify₆ : (Statement.AfterLinearCombination R pp ×
        ∀ i, OracleStatement.AfterLinearCombination R pp i) →
      (!p[] : ProtocolSpec 0).FullTranscript →
      ((R × Statement.AfterLinearCombination R pp) ×
        ∀ i, OracleStatement.AfterLinearCombination R pp i) :=
    fun p _tr => ((∑ idx, p.1.1 idx * p.2 (.inl 0) idx, p.1), p.2)
  have hV₆ : (prependRLCTargetKSWiring (R := R) pp oSpec).verifier.toVerifier
      = ⟨fun p tr => pure (verify₆ p tr)⟩ := by
    simpa [prependRLCTargetKSWiring, verify₆]
      using prependRLCTarget_toVerifier_pure (R := R) pp oSpec
  obtain ⟨verify₇?, hV₇⟩ :=
    Spartan.Spec.secondSumcheck_toVerifier_isFailingDet (R := R) pp oSpec
  have h₃ := firstSumcheck_rbrKnowledgeSoundness_honest_full
    (R := R) pp oSpec (init := init) (impl := impl) hInit hInitNF
  have h₇ := secondSumcheck_rbrKnowledgeSoundness_honest_full
    (R := R) pp oSpec (init := init) (impl := impl) hInit hInitNF
  exact composedRbrKnowledgeSoundnessStatement_of_leaves pp oSpec hm hn
    verify₁ hV₁ verify₂ hV₂ verify₃? hV₃ verify₄ hV₄ verify₅ hV₅ verify₆ hV₆
    verify₇? hV₇ h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ hInit hInitNF hNE_B hNE_C hNE_E
    hNE_F hNE_G

#print axioms Spartan.Spec.Bricks.composedRbrKnowledgeSoundnessStatement_of_nonsumcheck_leaves

/-- Relation-preserving composed Spartan RBR-KS progress after plugging in:

* all verifier determinism witnesses;
* both full sum-check RBR-KS leaves;
* the zero-round identity-style `finalCheck` RBR-KS leaf.

This theorem intentionally ends at `secondSumcheckRbrRelOut`, not at the broad
`finalCheckRelOut = Set.univ`, because the current `finalCheck` verifier forwards its input and
does not enforce a nontrivial terminal predicate. -/
theorem composedRbrKnowledgeSoundnessPreserving_of_nonsumcheck_leaves [Subsingleton σ]
    (hm : 0 < pp.ℓ_m) (hn : 0 < pp.ℓ_n)
    [Inhabited (FinalStatement R pp × ∀ i, FinalOracleStatement R pp i)]
    [Inhabited (Statement.AfterFirstSumcheck R pp ×
      ∀ i, OracleStatement.AfterFirstSumcheck R pp i)]
    {err₁ : (⟨!v[.P_to_V], !v[Witness R pp]⟩ : ProtocolSpec 1).ChallengeIdx → ℝ≥0}
    {err₂ : (⟨!v[.V_to_P], !v[FirstChallenge R pp]⟩ : ProtocolSpec 1).ChallengeIdx → ℝ≥0}
    {err₄ : (⟨!v[.P_to_V], !v[∀ i, EvalClaim R i]⟩ : ProtocolSpec 1).ChallengeIdx → ℝ≥0}
    {err₅ : (⟨!v[.V_to_P], !v[LinearCombinationChallenge R]⟩ :
      ProtocolSpec 1).ChallengeIdx → ℝ≥0}
    {err₆ : (!p[] : ProtocolSpec 0).ChallengeIdx → ℝ≥0}
    (h₁ : (oracleReduction.firstMessage R pp oSpec).verifier.rbrKnowledgeSoundness init impl
      (spartanRelIn R pp) relB err₁)
    (h₂ : (oracleReduction.firstChallenge.{0} R pp oSpec).verifier.rbrKnowledgeSoundness init impl
      relB (firstSumcheckRbrRelIn (R := R) pp oSpec) err₂)
    (h₄ : (oracleReduction.sendEvalClaim R pp oSpec).verifier.rbrKnowledgeSoundness init impl
      (firstSumcheckRbrRelOut (R := R) pp oSpec) relE err₄)
    (h₅ : (oracleReduction.linearCombination.{0} R pp oSpec).verifier.rbrKnowledgeSoundness
      init impl relE relF err₅)
    (h₆ : (prependRLCTargetKSWiring (R := R) pp oSpec).verifier.rbrKnowledgeSoundness init impl
      relF (secondSumcheckRbrRelIn (R := R) pp oSpec) err₆)
    (hInit : ∃ s, s ∈ support init) (hInitNF : Pr[⊥ | init] = 0)
    (hNE_B : Nonempty (Statement.AfterFirstMessage R pp ×
      ∀ i, OracleStatement.AfterFirstMessage R pp i))
    (hNE_C : Nonempty (Statement.AfterFirstChallenge R pp ×
      ∀ i, OracleStatement.AfterFirstChallenge R pp i))
    (hNE_E : Nonempty (Statement.AfterSendEvalClaim R pp ×
      ∀ i, OracleStatement.AfterSendEvalClaim R pp i))
    (hNE_F : Nonempty (Statement.AfterLinearCombination R pp ×
      ∀ i, OracleStatement.AfterLinearCombination R pp i))
    (hNE_G : Nonempty ((R × Statement.AfterLinearCombination R pp) ×
      ∀ i, OracleStatement.AfterLinearCombination R pp i)) :
    (composedPIOP_Rc (R := R) pp oSpec).verifier.rbrKnowledgeSoundness init impl
      (spartanRelIn R pp) (secondSumcheckRbrRelOut (R := R) pp oSpec)
      (composedRbrError pp err₁ err₂ (fun _ => (3 : ℝ≥0) / (Fintype.card R))
        err₄ err₅ err₆ (fun _ => (2 : ℝ≥0) / (Fintype.card R))
        (0 : (!p[] : ProtocolSpec 0).ChallengeIdx → ℝ≥0)) := by
  obtain ⟨verify₁, hV₁⟩ := firstMessage_toVerifier_pure (R := R) pp oSpec
  obtain ⟨verify₂, hV₂⟩ := firstChallenge_toVerifier_pure.{0} (R := R) pp oSpec
  obtain ⟨verify₃?, hV₃⟩ :=
    Spartan.Spec.firstSumcheck_toVerifier_isFailingDet (R := R) pp oSpec
  obtain ⟨verify₄, hV₄⟩ := sendEvalClaim_toVerifier_pure (R := R) pp oSpec
  obtain ⟨verify₅, hV₅⟩ := linearCombination_toVerifier_pure.{0} (R := R) pp oSpec
  let verify₆ : (Statement.AfterLinearCombination R pp ×
        ∀ i, OracleStatement.AfterLinearCombination R pp i) →
      (!p[] : ProtocolSpec 0).FullTranscript →
      ((R × Statement.AfterLinearCombination R pp) ×
        ∀ i, OracleStatement.AfterLinearCombination R pp i) :=
    fun p _tr => ((∑ idx, p.1.1 idx * p.2 (.inl 0) idx, p.1), p.2)
  have hV₆ : (prependRLCTargetKSWiring (R := R) pp oSpec).verifier.toVerifier
      = ⟨fun p tr => pure (verify₆ p tr)⟩ := by
    simpa [prependRLCTargetKSWiring, verify₆]
      using prependRLCTarget_toVerifier_pure (R := R) pp oSpec
  obtain ⟨verify₇?, hV₇⟩ :=
    Spartan.Spec.secondSumcheck_toVerifier_isFailingDet (R := R) pp oSpec
  have h₃ := firstSumcheck_rbrKnowledgeSoundness_honest_full
    (R := R) pp oSpec (init := init) (impl := impl) hInit hInitNF
  have h₇ := secondSumcheck_rbrKnowledgeSoundness_honest_full
    (R := R) pp oSpec (init := init) (impl := impl) hInit hInitNF
  have h₈ := finalCheck_rbrKnowledgeSoundness_secondSumcheckRbrRelOut.{0}
    (R := R) pp oSpec (init := init) (impl := impl)
  exact composedPIOP_Rc_rbrKnowledgeSoundness_of_leaves pp oSpec hm hn
    verify₁ hV₁ verify₂ hV₂ verify₃? hV₃ verify₄ hV₄ verify₅ hV₅ verify₆ hV₆
    verify₇? hV₇ h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ hInit hInitNF hNE_B hNE_C hNE_E
    hNE_F hNE_G

#print axioms Spartan.Spec.Bricks.composedRbrKnowledgeSoundnessPreserving_of_nonsumcheck_leaves

end

end Spartan.Spec.Bricks
