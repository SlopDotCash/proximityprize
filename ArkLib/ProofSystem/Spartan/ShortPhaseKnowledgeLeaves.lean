/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ProximityPrize.Compatibility.SpartanSendEvalClaim
import ProximityPrize.Compatibility.SpartanLinearCombination
import ProximityPrize.Compatibility.SpartanFirstChallenge
import ProximityPrize.Compatibility.SumcheckKnowledge
import ArkLib.ProofSystem.Spartan.ComposedRbrKnowledgeSoundness
import ArkLib.ProofSystem.Spartan.SumcheckKnowledgeLeaves
import ArkLib.ProofSystem.Spartan.PrependRLCDeterminism
import ArkLib.ProofSystem.Spartan.SumcheckDeterminismWitnesses
import ArkLib.ProofSystem.Spartan.FinalCheckRbrKnowledgeLeaf

import ProximityPrize.Compatibility.PureKnowledge

/-!

Canonical-message integration: the degree-2/degree-3 round knowledge bounds remain explicit
hypotheses of the `_of_sumcheck_rounds` constructions below. Former unconditional zero-flip
completion claims are retired; exact names, commands and added obligations are recorded in
`scripts/integration/sumcheck-message-semantics-retirements.json`.

# Spartan short-phase RBR-KS leaves + the one-seam composed assembly (#114)

This module discharges the five remaining short-phase round-by-round knowledge-soundness leaves
of `composedPIOP_Rc_rbrKnowledgeSoundness_of_leaves` (`firstMessage`, `firstChallenge`,
`sendEvalClaim`, `linearCombination`, `prependRLCTarget`; the two sum-check leaves live in
`SumcheckKnowledgeLeaves.lean` and the terminal `finalCheck` leaf in
`FinalCheckRbrKnowledgeLeaf.lean`), and folds everything into
`composedPIOP_Rc_rbrKnowledgeSoundness_of_rlcSeamBridge_of_sumcheck_rounds`: the **full composed Spartan rbr
knowledge soundness with explicit canonical round bounds and a named seam hypothesis**.

## The generic engine

All five phases compile (`toVerifier`) to **pure deterministic** verifiers (the determinism
witnesses of `ComposedRbrKnowledgeSoundness.lean` / `PrependRLCDeterminism.lean`). For such a
verifier the two generic theorems

* `Verifier.rbrKnowledgeSoundness_of_pure_oneRound`
* `Verifier.rbrKnowledgeSoundness_of_pure_zeroRound`

give rbr knowledge soundness **with error `0`** for any relation pair `(relIn, relOut)`
satisfying the extraction implication `(verify stmt tr, wOut) ∈ relOut → (stmt, ext …) ∈ relIn`
— uniformly in the direction of the round (for a `P_to_V` round there are no challenge indices;
for a `V_to_P` round the state-flip event is pointwise empty under the implication). Two
canonical relation transformers instantiate the implication by construction:

* `Verifier.pureKSPushforward verify relOut` — "some full transcript reaches `relOut`"
  (the *smallest* valid input relation for a given output relation);
* `Verifier.pureKSCarry verify relIn` — "every `verify`-preimage satisfies `relIn`"
  (the *largest* valid output relation for a given input relation).

## The relation chain

With the sum-check endpoints pinned by the proven honest sum-check leaves
(`relC = firstSumcheckRbrRelIn`, `relD = firstSumcheckRbrRelOut`,
`relG = secondSumcheckRbrRelIn`, `relH = relI = secondSumcheckRbrRelOut`), the chain is

`firstMessageKSRelIn →h₁→ firstChallengeKSRelIn →h₂→ relC →h₃→ relD →h₄→
sendEvalClaimKSRelOut →h₅→ prependRLCKSRelIn →h₆→ relG →h₇→ relH →h₈→ relH`

where `h₁, h₂, h₆` are pushforward leaves into the pinned right endpoints, and `h₄` is the carry
leaf out of the pinned left endpoint `relD`. All are proven here with error `0`.

## The honest seam (`hSeam`, the `h₅` slot) — why it is irreducible

The `linearCombination` leaf `h₅` must connect `sendEvalClaimKSRelOut` (the carry of the
first-sumcheck terminal relation through the eval-claim message) to `prependRLCKSRelIn` (the
preimage of the second-sumcheck input claim under the RLC-target map). This is the genuine
random-linear-combination *batching* step binding the prover's freshly-sent eval claims across
the two sum-checks, and **no choice of intermediate relations can dissolve it**: the `h₆`
obligations force `relF ⊇ prependRLCKSRelIn`, and the `h₄` obligations force
`relE ⊆ sendEvalClaimKSRelOut`-style carries of `relD`, so the gap between the forced minimal
and maximal relations at the `h₅` seam is exactly the batching implication. It is therefore
taken as the named hypothesis `hSeam` with its own error `err₅`. Note that `hSeam` is *trivially
provable at `err₅ = 1`* (any probability is `≤ 1`, with a constantly-true round-1 state) — such
an instantiation is intentionally **not** provided here, since it makes the composed error bound
vacuous at that round; the meaningful target is `err₅ = O(1/|R|)`, which requires relating the
claimed evaluations to the actual matrix MLE sums (content adjacent to the currently
tautological `finalPredicate` of `finalCheck`).

All declarations are axiom-clean (`[propext, Classical.choice, Quot.sound]`, no `sorryAx`),
audited by the `#print axioms` commands at the bottom of this file.
-/

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

/-! Generic pure-verifier transport is shared by `Compatibility.PureKnowledge`. -/



/-! ### Spartan leaves -/

namespace Spartan.Spec.Bricks

set_option linter.unusedSectionVars false

noncomputable section

variable {R : Type 0} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] [Inhabited R]
  [SampleableType R] (pp : PublicParams)

variable {ι : Type} (oSpec : OracleSpec ι)
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- The pure map computed by the compiled `firstMessage` verifier (canonical choice from the
proven determinism witness). -/
noncomputable def firstMessageVerify :=
  (firstMessage_toVerifier_pure (R := R) pp oSpec).choose

theorem firstMessageVerify_spec :
    (oracleReduction.firstMessage R pp oSpec).verifier.toVerifier
      = ⟨fun p tr => pure (firstMessageVerify pp oSpec p tr)⟩ :=
  (firstMessage_toVerifier_pure (R := R) pp oSpec).choose_spec

/-- The pure map computed by the compiled `firstChallenge` verifier. -/
noncomputable def firstChallengeVerify :=
  (firstChallenge_toVerifier_pure (R := R) pp oSpec).choose

theorem firstChallengeVerify_spec :
    (oracleReduction.completedFirstChallenge R pp oSpec).verifier.toVerifier
      = ⟨fun p tr => pure (firstChallengeVerify pp oSpec p tr)⟩ :=
  (firstChallenge_toVerifier_pure (R := R) pp oSpec).choose_spec

/-- The pure map computed by the compiled `sendEvalClaim` verifier. -/
noncomputable def sendEvalClaimVerify :=
  (sendEvalClaim_toVerifier_pure (R := R) pp oSpec).choose

theorem sendEvalClaimVerify_spec :
    (oracleReduction.completedSendEvalClaim R pp oSpec).verifier.toVerifier
      = ⟨fun p tr => pure (sendEvalClaimVerify pp oSpec p tr)⟩ :=
  (sendEvalClaim_toVerifier_pure (R := R) pp oSpec).choose_spec

/-- The pure map computed by the compiled `linearCombination` verifier. -/
noncomputable def linearCombinationVerify :=
  (linearCombination_toVerifier_pure (R := R) pp oSpec).choose

theorem linearCombinationVerify_spec :
    (oracleReduction.completedLinearCombination R pp oSpec).verifier.toVerifier
      = ⟨fun p tr => pure (linearCombinationVerify pp oSpec p tr)⟩ :=
  (linearCombination_toVerifier_pure (R := R) pp oSpec).choose_spec

/-- The pure map computed by the compiled `prependRLCTarget` verifier (concrete form). -/
def prependRLCVerify :
    (Statement.AfterLinearCombination R pp ×
      ∀ i, OracleStatement.AfterLinearCombination R pp i) →
    (!p[] : ProtocolSpec 0).FullTranscript →
    ((R × Statement.AfterLinearCombination R pp) ×
      ∀ i, OracleStatement.AfterLinearCombination R pp i) :=
  fun p _tr => ((∑ idx, p.1.1 idx * (show R from p.2 (.inl idx)), p.1), p.2)

theorem prependRLCVerify_spec :
    (prependRLCTarget (R := R) pp oSpec).verifier.toVerifier
      = ⟨fun p tr => pure (prependRLCVerify pp p tr)⟩ := by
  simpa only [prependRLCVerify] using
    (prependRLCTarget_toVerifier_pure (R := R) pp oSpec)


/-! ### Chain relations -/

/-- `relC`-pushforward: the honest rbr-KS input relation of the `firstChallenge` phase — the
input statements from which **some** challenge `τ` reaches the pinned first-sumcheck honest
input relation (`firstSumcheckRbrRelIn`). Serves as `relB` of the composed chain. -/
def firstChallengeKSRelIn : Set ((Statement.AfterFirstMessage R pp ×
    ∀ i, OracleStatement.AfterFirstMessage R pp i) × Unit) :=
  Verifier.pureKSPushforward (firstChallengeVerify pp oSpec)
    (firstSumcheckRbrRelIn (R := R) pp oSpec)

/-- `relB`-pushforward: the honest rbr-KS input relation of the `firstMessage` phase. Serves as
`relA` of the composed chain. -/
def firstMessageKSRelIn : Set ((Statement R pp ×
    ∀ i, OracleStatement R pp i) × Witness R pp) :=
  Verifier.pureKSPushforward (firstMessageVerify pp oSpec) (firstChallengeKSRelIn pp oSpec)

/-- `relG`-preimage: the honest rbr-KS input relation of the zero-round `prependRLCTarget`
phase — the preimage of the pinned second-sumcheck honest input relation
(`secondSumcheckRbrRelIn`) under the pure RLC-target map. Serves as `relF`. -/
def prependRLCKSRelIn : Set ((Statement.AfterLinearCombination R pp ×
    ∀ i, OracleStatement.AfterLinearCombination R pp i) × Unit) :=
  Verifier.pureKSPushforward (prependRLCVerify pp) (secondSumcheckRbrRelIn (R := R) pp oSpec)

/-- `relF`-pushforward: the honest rbr-KS input relation of the `linearCombination` phase.
Serves as `relE`. -/
def linearCombinationKSRelIn : Set ((Statement.AfterSendEvalClaim R pp ×
    ∀ i, OracleStatement.AfterSendEvalClaim R pp i) × Unit) :=
  Verifier.pureKSPushforward (linearCombinationVerify pp oSpec) (prependRLCKSRelIn pp oSpec)

/-- `relE`-pushforward: the honest rbr-KS input relation of the `sendEvalClaim` phase. -/
def sendEvalClaimKSRelIn : Set ((Statement.AfterFirstSumcheck R pp ×
    ∀ i, OracleStatement.AfterFirstSumcheck R pp i) × Unit) :=
  Verifier.pureKSPushforward (sendEvalClaimVerify pp oSpec) (linearCombinationKSRelIn pp oSpec)

/-- `relD`-carry: the largest output relation of `sendEvalClaim` for which the extraction
implication into the pinned `firstSumcheckRbrRelOut` holds. -/
def sendEvalClaimKSRelOut : Set ((Statement.AfterSendEvalClaim R pp ×
    ∀ i, OracleStatement.AfterSendEvalClaim R pp i) × Unit) :=
  Verifier.pureKSCarry (sendEvalClaimVerify pp oSpec) (firstSumcheckRbrRelOut (R := R) pp oSpec)

/-- Carry of `sendEvalClaimKSRelOut` through `linearCombination`. -/
def linearCombinationKSRelOut : Set ((Statement.AfterLinearCombination R pp ×
    ∀ i, OracleStatement.AfterLinearCombination R pp i) × Unit) :=
  Verifier.pureKSCarry (linearCombinationVerify pp oSpec) (sendEvalClaimKSRelOut pp oSpec)

/-! ### The leaves: generic variants -/

variable (init) (impl)

/-- `firstMessage` rbr-KS, pushforward form: any output relation, error `0`. -/
theorem firstMessage_rbrKnowledgeSoundness_pushforward
    (relOut : Set ((Statement.AfterFirstMessage R pp ×
      ∀ i, OracleStatement.AfterFirstMessage R pp i) × Unit)) :
    (oracleReduction.firstMessage R pp oSpec).verifier.rbrKnowledgeSoundness init impl
      (Verifier.pureKSPushforward (firstMessageVerify pp oSpec) relOut :
        Set ((Statement R pp × ∀ i, OracleStatement R pp i) × Witness R pp))
      relOut 0 := by
  unfold OracleVerifier.rbrKnowledgeSoundness
  rw [firstMessageVerify_spec (R := R) pp oSpec]
  exact Verifier.rbrKnowledgeSoundness_of_pure_oneRound init impl _ (fun _ tr _ => tr 0) _ _
    (fun stmt tr wOut h => ⟨tr, wOut, h⟩)

/-- `firstChallenge` rbr-KS, pushforward form: any output relation, error `0`. -/
theorem firstChallenge_rbrKnowledgeSoundness_pushforward
    (relOut : Set ((Statement.AfterFirstChallenge R pp ×
      ∀ i, OracleStatement.AfterFirstChallenge R pp i) × Unit)) :
    (oracleReduction.completedFirstChallenge R pp oSpec).verifier.rbrKnowledgeSoundness init impl
      (Verifier.pureKSPushforward (firstChallengeVerify pp oSpec) relOut :
        Set ((Statement.AfterFirstMessage R pp ×
          ∀ i, OracleStatement.AfterFirstMessage R pp i) × Unit))
      relOut 0 := by
  unfold OracleVerifier.rbrKnowledgeSoundness
  rw [firstChallengeVerify_spec (R := R) pp oSpec]
  exact Verifier.rbrKnowledgeSoundness_of_pure_oneRound init impl _ (fun _ _ _ => ()) _ _
    (fun stmt tr wOut h => ⟨tr, wOut, h⟩)

/-- `sendEvalClaim` rbr-KS, pushforward form: any output relation, error `0`. -/
theorem sendEvalClaim_rbrKnowledgeSoundness_pushforward
    (relOut : Set ((Statement.AfterSendEvalClaim R pp ×
      ∀ i, OracleStatement.AfterSendEvalClaim R pp i) × Unit)) :
    (oracleReduction.completedSendEvalClaim R pp oSpec).verifier.rbrKnowledgeSoundness init impl
      (Verifier.pureKSPushforward (sendEvalClaimVerify pp oSpec) relOut :
        Set ((Statement.AfterFirstSumcheck R pp ×
          ∀ i, OracleStatement.AfterFirstSumcheck R pp i) × Unit))
      relOut 0 := by
  unfold OracleVerifier.rbrKnowledgeSoundness
  rw [sendEvalClaimVerify_spec (R := R) pp oSpec]
  exact Verifier.rbrKnowledgeSoundness_of_pure_oneRound init impl _ (fun _ _ _ => ()) _ _
    (fun stmt tr wOut h => ⟨tr, wOut, h⟩)

/-- `sendEvalClaim` rbr-KS, carry form: any **input** relation (in particular the pinned
`firstSumcheckRbrRelOut`), error `0`. -/
theorem sendEvalClaim_rbrKnowledgeSoundness_carry
    (relIn : Set ((Statement.AfterFirstSumcheck R pp ×
      ∀ i, OracleStatement.AfterFirstSumcheck R pp i) × Unit)) :
    (oracleReduction.completedSendEvalClaim R pp oSpec).verifier.rbrKnowledgeSoundness init impl
      relIn
      (Verifier.pureKSCarry (sendEvalClaimVerify pp oSpec) relIn :
        Set ((Statement.AfterSendEvalClaim R pp ×
          ∀ i, OracleStatement.AfterSendEvalClaim R pp i) × Unit))
      0 := by
  unfold OracleVerifier.rbrKnowledgeSoundness
  rw [sendEvalClaimVerify_spec (R := R) pp oSpec]
  exact Verifier.rbrKnowledgeSoundness_of_pure_oneRound init impl _ (fun _ _ _ => ()) _ _
    (fun stmt tr wOut h => by
      rcases h stmt tr rfl () with h
      exact h)

/-- `linearCombination` rbr-KS, pushforward form: any output relation, error `0`. -/
theorem linearCombination_rbrKnowledgeSoundness_pushforward
    (relOut : Set ((Statement.AfterLinearCombination R pp ×
      ∀ i, OracleStatement.AfterLinearCombination R pp i) × Unit)) :
    (oracleReduction.completedLinearCombination R pp oSpec).verifier.rbrKnowledgeSoundness init impl
      (Verifier.pureKSPushforward (linearCombinationVerify pp oSpec) relOut :
        Set ((Statement.AfterSendEvalClaim R pp ×
          ∀ i, OracleStatement.AfterSendEvalClaim R pp i) × Unit))
      relOut 0 := by
  unfold OracleVerifier.rbrKnowledgeSoundness
  rw [linearCombinationVerify_spec (R := R) pp oSpec]
  exact Verifier.rbrKnowledgeSoundness_of_pure_oneRound init impl _ (fun _ _ _ => ()) _ _
    (fun stmt tr wOut h => ⟨tr, wOut, h⟩)

/-- `linearCombination` rbr-KS, carry form: any input relation, error `0`. -/
theorem linearCombination_rbrKnowledgeSoundness_carry
    (relIn : Set ((Statement.AfterSendEvalClaim R pp ×
      ∀ i, OracleStatement.AfterSendEvalClaim R pp i) × Unit)) :
    (oracleReduction.completedLinearCombination R pp oSpec).verifier.rbrKnowledgeSoundness init impl
      relIn
      (Verifier.pureKSCarry (linearCombinationVerify pp oSpec) relIn :
        Set ((Statement.AfterLinearCombination R pp ×
          ∀ i, OracleStatement.AfterLinearCombination R pp i) × Unit))
      0 := by
  unfold OracleVerifier.rbrKnowledgeSoundness
  rw [linearCombinationVerify_spec (R := R) pp oSpec]
  exact Verifier.rbrKnowledgeSoundness_of_pure_oneRound init impl _ (fun _ _ _ => ()) _ _
    (fun stmt tr wOut h => h stmt tr rfl ())

/-- `prependRLCTarget` rbr-KS, pushforward (= preimage) form: any output relation, error `0`. -/
theorem prependRLCTarget_rbrKnowledgeSoundness_pushforward
    (relOut : Set (((R × Statement.AfterLinearCombination R pp) ×
      ∀ i, OracleStatement.AfterLinearCombination R pp i) × Unit)) :
    (prependRLCTarget (R := R) pp oSpec).verifier.rbrKnowledgeSoundness init impl
      (Verifier.pureKSPushforward (prependRLCVerify pp) relOut :
        Set ((Statement.AfterLinearCombination R pp ×
          ∀ i, OracleStatement.AfterLinearCombination R pp i) × Unit))
      relOut 0 := by
  unfold OracleVerifier.rbrKnowledgeSoundness
  rw [prependRLCVerify_spec (R := R) pp oSpec]
  exact Verifier.rbrKnowledgeSoundness_of_pure_zeroRound init impl _ (fun _ _ _ => ()) _ _
    (fun stmt tr wOut h => ⟨tr, wOut, h⟩)

/-! ### The leaves: pinned-chain corollaries -/

/-- **Leaf `h₁`** (`firstMessage`): pushforward chain instance. -/
theorem firstMessage_rbrKnowledgeSoundness_leaf :
    (oracleReduction.firstMessage R pp oSpec).verifier.rbrKnowledgeSoundness init impl
      (firstMessageKSRelIn pp oSpec) (firstChallengeKSRelIn pp oSpec) 0 :=
  firstMessage_rbrKnowledgeSoundness_pushforward pp oSpec init impl _

/-- **Leaf `h₂`** (`firstChallenge`): ends exactly at the pinned `firstSumcheckRbrRelIn`. -/
theorem firstChallenge_rbrKnowledgeSoundness_leaf :
    (oracleReduction.completedFirstChallenge R pp oSpec).verifier.rbrKnowledgeSoundness init impl
      (firstChallengeKSRelIn pp oSpec) (firstSumcheckRbrRelIn (R := R) pp oSpec) 0 :=
  firstChallenge_rbrKnowledgeSoundness_pushforward pp oSpec init impl _

/-- **Leaf `h₄`, carry form** (`sendEvalClaim`): starts exactly at the pinned
`firstSumcheckRbrRelOut`. -/
theorem sendEvalClaim_rbrKnowledgeSoundness_leaf_carry :
    (oracleReduction.completedSendEvalClaim R pp oSpec).verifier.rbrKnowledgeSoundness init impl
      (firstSumcheckRbrRelOut (R := R) pp oSpec) (sendEvalClaimKSRelOut pp oSpec) 0 :=
  sendEvalClaim_rbrKnowledgeSoundness_carry pp oSpec init impl _

/-- **Leaf `h₄`, pushforward form** (`sendEvalClaim`): ends exactly at
`linearCombinationKSRelIn`. -/
theorem sendEvalClaim_rbrKnowledgeSoundness_leaf_pushforward :
    (oracleReduction.completedSendEvalClaim R pp oSpec).verifier.rbrKnowledgeSoundness init impl
      (sendEvalClaimKSRelIn pp oSpec) (linearCombinationKSRelIn pp oSpec) 0 :=
  sendEvalClaim_rbrKnowledgeSoundness_pushforward pp oSpec init impl _

/-- **Leaf `h₅`, pushforward form** (`linearCombination`). -/
theorem linearCombination_rbrKnowledgeSoundness_leaf_pushforward :
    (oracleReduction.completedLinearCombination R pp oSpec).verifier.rbrKnowledgeSoundness init impl
      (linearCombinationKSRelIn pp oSpec) (prependRLCKSRelIn pp oSpec) 0 :=
  linearCombination_rbrKnowledgeSoundness_pushforward pp oSpec init impl _

/-- **Leaf `h₅`, carry form** (`linearCombination`): continues the carry chain from
`sendEvalClaimKSRelOut`. -/
theorem linearCombination_rbrKnowledgeSoundness_leaf_carry :
    (oracleReduction.completedLinearCombination R pp oSpec).verifier.rbrKnowledgeSoundness init impl
      (sendEvalClaimKSRelOut pp oSpec) (linearCombinationKSRelOut pp oSpec) 0 :=
  linearCombination_rbrKnowledgeSoundness_carry pp oSpec init impl _

/-- **Leaf `h₆`** (`prependRLCTarget`): ends exactly at the pinned
`secondSumcheckRbrRelIn`. -/
theorem prependRLCTarget_rbrKnowledgeSoundness_leaf :
    (prependRLCTarget (R := R) pp oSpec).verifier.rbrKnowledgeSoundness init impl
      (prependRLCKSRelIn pp oSpec) (secondSumcheckRbrRelIn (R := R) pp oSpec) 0 :=
  prependRLCTarget_rbrKnowledgeSoundness_pushforward pp oSpec init impl _


/-! ### The composed assembly, reduced to the single RLC seam bridge -/

/-- The completed Spartan composition construction, conditional on the actual canonical
sumcheck degree-2, degree-3 per-round knowledge bounds. The former unconditional zero-flip
completion is retired; exact source and the added obligations are recorded in the migration audit. -/
theorem composedPIOP_Rc_rbrKnowledgeSoundness_of_rlcSeamBridge_of_sumcheck_rounds [Subsingleton σ]
    (hm : 0 < pp.ℓ_m) (hn : 0 < pp.ℓ_n)
    [Inhabited (FinalStatement R pp × ∀ i, FinalOracleStatement R pp i)]
    [Inhabited (Statement.AfterFirstSumcheck R pp ×
      ∀ i, OracleStatement.AfterFirstSumcheck R pp i)]
    {err₅ : (⟨!v[.V_to_P], !v[LinearCombinationChallenge R]⟩ :
      ProtocolSpec 1).ChallengeIdx → ℝ≥0}
    (hSeam : (oracleReduction.completedLinearCombination R pp oSpec).verifier.rbrKnowledgeSoundness
      init impl (sendEvalClaimKSRelOut pp oSpec) (prependRLCKSRelIn pp oSpec) err₅)
    (hInit : ∃ s, s ∈ support init) (hInitNF : prFail (init) = 0)
    (hNE_B : Nonempty (Statement.AfterFirstMessage R pp ×
      ∀ i, OracleStatement.AfterFirstMessage R pp i))
    (hNE_C : Nonempty (Statement.AfterFirstChallenge R pp ×
      ∀ i, OracleStatement.AfterFirstChallenge R pp i))
    (hNE_E : Nonempty (Statement.AfterSendEvalClaim R pp ×
      ∀ i, OracleStatement.AfterSendEvalClaim R pp i))
    (hNE_F : Nonempty (Statement.AfterLinearCombination R pp ×
      ∀ i, OracleStatement.AfterLinearCombination R pp i))
    (hNE_G : Nonempty ((R × Statement.AfterLinearCombination R pp) ×
      ∀ i, OracleStatement.AfterLinearCombination R pp i))
    (hRound2 : Sumcheck.Spec.RoundKnowledge R 2 (boolEmbedding R) pp.ℓ_n oSpec init impl)
    (hRound3 : Sumcheck.Spec.RoundKnowledge R 3 (boolEmbedding R) pp.ℓ_m oSpec init impl)
    :
    (composedPIOP_Rc (R := R) pp oSpec).verifier.rbrKnowledgeSoundness init impl
      (firstMessageKSRelIn pp oSpec) (secondSumcheckRbrRelOut (R := R) pp oSpec)
      (composedRbrError pp 0 0 (fun _ => (3 : ℝ≥0) / (Fintype.card R)) 0 err₅ 0
        (fun _ => (2 : ℝ≥0) / (Fintype.card R)) 0) := by
  obtain ⟨verify₁, hV₁⟩ := firstMessage_toVerifier_pure (R := R) pp oSpec
  obtain ⟨verify₂, hV₂⟩ := firstChallenge_toVerifier_pure (R := R) pp oSpec
  obtain ⟨verify₃?, hV₃⟩ :=
    Spartan.Spec.firstSumcheck_toVerifier_isFailingDet (R := R) pp oSpec
  obtain ⟨verify₄, hV₄⟩ := sendEvalClaim_toVerifier_pure (R := R) pp oSpec
  obtain ⟨verify₅, hV₅⟩ := linearCombination_toVerifier_pure (R := R) pp oSpec
  obtain ⟨verify₇?, hV₇⟩ :=
    Spartan.Spec.secondSumcheck_toVerifier_isFailingDet (R := R) pp oSpec
  have h₁ := firstMessage_rbrKnowledgeSoundness_leaf (R := R) pp oSpec init impl
  have h₂ := firstChallenge_rbrKnowledgeSoundness_leaf (R := R) pp oSpec init impl
  have h₃ := firstSumcheck_rbrKnowledgeSoundness_honest_full_of_sumcheck_rounds (hRound3 := hRound3)
    (R := R) pp oSpec (init := init) (impl := impl) hInit hInitNF
  have h₄ := sendEvalClaim_rbrKnowledgeSoundness_leaf_carry (R := R) pp oSpec init impl
  have h₆ := prependRLCTarget_rbrKnowledgeSoundness_leaf (R := R) pp oSpec init impl
  have h₇ := secondSumcheck_rbrKnowledgeSoundness_honest_full_of_sumcheck_rounds (hRound2 :=
    hRound2)
    (R := R) pp oSpec (init := init) (impl := impl) hInit hInitNF
  have h₈ := finalCheck_rbrKnowledgeSoundness_secondSumcheckRbrRelOut
    (R := R) pp oSpec (init := init) (impl := impl)
  exact composedPIOP_Rc_rbrKnowledgeSoundness_of_leaves pp oSpec hm hn
    verify₁ hV₁ verify₂ hV₂ verify₃? hV₃ verify₄ hV₄ verify₅ hV₅
    (fun p _tr => prependRLCVerify pp p _tr)
    (prependRLCVerify_spec (R := R) pp oSpec)
    verify₇? hV₇ h₁ h₂ h₃ h₄ hSeam h₆ h₇ h₈ hInit hInitNF hNE_B hNE_C hNE_E
    hNE_F hNE_G

end

end Spartan.Spec.Bricks

#print axioms Verifier.rbrKnowledgeSoundness_of_pure_oneRound
#print axioms Verifier.rbrKnowledgeSoundness_of_pure_zeroRound
#print axioms Spartan.Spec.Bricks.firstMessage_rbrKnowledgeSoundness_leaf
#print axioms Spartan.Spec.Bricks.firstChallenge_rbrKnowledgeSoundness_leaf
#print axioms Spartan.Spec.Bricks.sendEvalClaim_rbrKnowledgeSoundness_leaf_carry
#print axioms Spartan.Spec.Bricks.sendEvalClaim_rbrKnowledgeSoundness_leaf_pushforward
#print axioms Spartan.Spec.Bricks.linearCombination_rbrKnowledgeSoundness_leaf_pushforward
#print axioms Spartan.Spec.Bricks.linearCombination_rbrKnowledgeSoundness_leaf_carry
#print axioms Spartan.Spec.Bricks.prependRLCTarget_rbrKnowledgeSoundness_leaf
#print axioms
  Spartan.Spec.Bricks.composedPIOP_Rc_rbrKnowledgeSoundness_of_rlcSeamBridge_of_sumcheck_rounds
