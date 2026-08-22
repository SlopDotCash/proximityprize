/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.Security.RbrKnowledgeTruncate
import ArkLib.ProofSystem.Spartan.ShortPhaseRbrKnowledgeLeaves

/-!
# Composed Spartan RBR knowledge soundness — the named residual, discharged (issue #114)

This file discharges `Bricks.composedRbrKnowledgeSoundnessStatement` (the broad-terminal
composed RBR-KS obligation, with output relation `finalCheckRelOut = Set.univ`) at the
assembled `composedPIOP_Rc`, with the error vector of the unconditional relation-preserving
apex `composedRbrKnowledgeSoundnessPreserving_unconditional`:

  `0 / ℓ_m·|R|⁻¹ / 3·|R|⁻¹ (per round) / 0 / 1 / 0 / 2·|R|⁻¹ (per round) / 0`.

**Read the error vector before citing this.** The `linearCombination` round pays per-round
error `1` — proven-forced on the no-claim relation chain (see the module docstring of
`ShortPhaseRbrKnowledgeLeaves.lean`: a prover sending the true evaluation claims flips that
round with probability `1`). Because a round of error `1` is present, the truncation
combinator `OracleVerifier.rbrKnowledgeSoundness_relOut_any_of_one_le_error` converts the
relation-preserving apex (terminal relation `secondSumcheckRbrRelOut`) into the same statement
against the broad `finalCheckRelOut = Set.univ` — the knowledge content of the discharged
residual is exactly the rbr-KS of the protocol prefix up to `linearCombination` (R1CS witness
extraction from the first message, Schwartz–Zippel at `firstChallenge`, the full first
sum-check at `3/|R|` per round).

The **stronger** headline fact remains the relation-preserving apex
`composedRbrKnowledgeSoundnessPreserving_unconditional`, which keeps the nontrivial
second-sum-check terminal relation. The *tight* end-to-end statement (error `O(1/|R|)` at
every round against a checking terminal) requires the target-carrying (`WithClaim`) protocol
line — tracked as issue #329.
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

/-- The `linearCombination` challenge round, as a challenge index of the full composed
protocol spec (four `inr` steps past `firstMessage`/`firstChallenge`/`firstSumcheck`/
`sendEvalClaim`, then the unique challenge of the 1-round `linearCombination` phase). -/
def linearCombinationChallengeIdx : (composedPSpec (R := R) pp).ChallengeIdx :=
  ChallengeIdx.sumEquiv (.inr <|
    ChallengeIdx.sumEquiv (.inr <|
      ChallengeIdx.sumEquiv (.inr <|
        ChallengeIdx.sumEquiv (.inr <|
          ChallengeIdx.sumEquiv (.inl (default :
            (⟨!v[.V_to_P], !v[LinearCombinationChallenge R]⟩ :
              ProtocolSpec 1).ChallengeIdx))))))

/-- The composed error vector of the unconditional apex evaluates to `err₅ = 1` at the
`linearCombination` challenge round. -/
theorem composedRbrError_linearCombinationChallengeIdx
    (err₁ : (⟨!v[.P_to_V], !v[Witness R pp]⟩ : ProtocolSpec 1).ChallengeIdx → ℝ≥0)
    (err₂ : (⟨!v[.V_to_P], !v[FirstChallenge R pp]⟩ : ProtocolSpec 1).ChallengeIdx → ℝ≥0)
    (err₃ : (Sumcheck.Spec.pSpec R 3 pp.ℓ_m).ChallengeIdx → ℝ≥0)
    (err₄ : (⟨!v[.P_to_V], !v[∀ i, EvalClaim R i]⟩ : ProtocolSpec 1).ChallengeIdx → ℝ≥0)
    (err₅ : (⟨!v[.V_to_P], !v[LinearCombinationChallenge R]⟩ :
      ProtocolSpec 1).ChallengeIdx → ℝ≥0)
    (err₆ : (!p[] : ProtocolSpec 0).ChallengeIdx → ℝ≥0)
    (err₇ : (Sumcheck.Spec.pSpec R 2 pp.ℓ_n).ChallengeIdx → ℝ≥0)
    (err₈ : (!p[] : ProtocolSpec 0).ChallengeIdx → ℝ≥0) :
    composedRbrError pp err₁ err₂ err₃ err₄ err₅ err₆ err₇ err₈
        (linearCombinationChallengeIdx (R := R) pp)
      = err₅ default := by
  simp only [linearCombinationChallengeIdx, composedRbrError, Function.comp_apply,
    Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr]

/-- **The named composed Spartan RBR knowledge-soundness residual, discharged (issue #114).**

`composedRbrKnowledgeSoundnessStatement` at `Rc := composedPIOP_Rc`, with the apex error
vector. Obtained from the unconditional relation-preserving apex by truncating the knowledge
state function at the (error-`1`) `linearCombination` round — see the module docstring for
what this does and does not claim. -/
theorem composedRbrKnowledgeSoundnessStatement_proven [Subsingleton σ]
    (hm : 0 < pp.ℓ_m) (hn : 0 < pp.ℓ_n)
    [Inhabited (FinalStatement R pp × ∀ i, FinalOracleStatement R pp i)]
    [Inhabited (Statement.AfterFirstSumcheck R pp ×
      ∀ i, OracleStatement.AfterFirstSumcheck R pp i)]
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
    composedRbrKnowledgeSoundnessStatement R pp oSpec (composedPIOP_Rc (R := R) pp oSpec)
      init impl
      (composedRbrError pp
        (0 : (⟨!v[.P_to_V], !v[Witness R pp]⟩ : ProtocolSpec 1).ChallengeIdx → ℝ≥0)
        (fun _ => (pp.ℓ_m : ℝ≥0) / (Fintype.card R : ℝ≥0))
        (fun _ => (3 : ℝ≥0) / (Fintype.card R))
        (0 : (⟨!v[.P_to_V], !v[∀ i, EvalClaim R i]⟩ : ProtocolSpec 1).ChallengeIdx → ℝ≥0)
        (fun _ => 1)
        (0 : (!p[] : ProtocolSpec 0).ChallengeIdx → ℝ≥0)
        (fun _ => (2 : ℝ≥0) / (Fintype.card R))
        (0 : (!p[] : ProtocolSpec 0).ChallengeIdx → ℝ≥0)) := by
  have h := composedRbrKnowledgeSoundnessPreserving_unconditional (R := R) pp oSpec
    (init := init) (impl := impl) hm hn hInit hInitNF hNE_B hNE_C hNE_E hNE_F hNE_G
  unfold composedRbrKnowledgeSoundnessStatement
  refine OracleVerifier.rbrKnowledgeSoundness_relOut_any_of_one_le_error h
    (linearCombinationChallengeIdx (R := R) pp) ?_ _
  rw [composedRbrError_linearCombinationChallengeIdx]

end

end Spartan.Spec.Bricks

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms Spartan.Spec.Bricks.composedRbrError_linearCombinationChallengeIdx
#print axioms Spartan.Spec.Bricks.composedRbrKnowledgeSoundnessStatement_proven
