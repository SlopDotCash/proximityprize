/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ProximityPrize.Compatibility.SpartanLinearCombination
import ArkLib.ProofSystem.Spartan.Composition
import ArkLib.ProofSystem.Spartan.ComposedCompletenessLeaves
import ArkLib.ProofSystem.Spartan.FirstSumcheckBridgeFree

/-!
# `linearCombination` phase perfect completeness, parametric in the input relation (#114)

`ComposedCompletenessLeaves.linearCombination_perfectCompleteness` proves the Spartan RLC
challenge phase perfectly complete for the *pinned* R1CS pass-through relations
(`linearCombinationRelIn` → `linearCombinationRelOut`). The composed-PC fold
(`composedCompletenessStatement_of_five_leaves`, `ComposedCompleteness.lean`) however pins the
phase's **input** relation to whatever the upstream `sendEvalClaim` leaf emits —
`sendEvalClaimRelOut … (firstSumcheckRelOutBF …)`, which carries the bundled eval-claim *honesty*
conjunct that the pinned relations drop (and which the downstream honest RLC-target adapter
`prependRLCTarget` needs).

Since `linearCombination` is a pure V→P challenge round — statement and oracles pass through
unchanged, the sampled challenge is merely recorded — it is perfectly complete from **any** input
relation `rel` to the challenge-stripped pushforward `linearCombinationRelOutOf rel`. This module
proves exactly that:

* `linearCombinationRelOutOf` — the pushforward output relation (strip the recorded challenge,
  require the underlying pair in `rel`);
* `linearCombination_perfectCompleteness_of` — the parametric leaf perfect completeness. The
  five-leaves consumer's `h₅` is the instance `rel := relE` for whatever `relE` the `sendEvalClaim`
  leaf provides, with `relF := linearCombinationRelOutOf relE`;
* `linearCombinationRelOutOf_sendEvalClaimBF_subset_prependRLCTargetRelIn` — the seam weld: on the
  canonical chain (`relE := sendEvalClaimRelOut … (firstSumcheckRelOutBF …)`, exactly what the
  proven `sendEvalClaim_perfectCompleteness` emits from the consumer-pinned `relD`), the natural
  pushforward `relF` refines `prependRLCTargetRelIn` — the input relation of the proven
  downstream `prependRLCTarget_perfectCompleteness_secondSumcheckRelInBF`;
* `linearCombination_perfectCompleteness_sendEvalClaimBF` — the consumer-endpoint `h₅` instance:
  perfectly complete from `sendEvalClaimRelOut … (firstSumcheckRelOutBF …)` into
  `prependRLCTargetRelIn`, so `h₄`/`h₅`/`h₆` of `composedCompletenessStatement_of_five_leaves` now
  chain with `relE := sendEvalClaimRelOut … (firstSumcheckRelOutBF …)` and
  `relF := prependRLCTargetRelIn`.
-/

open MvPolynomial OracleComp OracleSpec OracleQuery OracleInterface ProtocolSpec

namespace Spartan.Spec

variable {R : Type} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] [SampleableType R]
  (pp : Spartan.PublicParams) {ι : Type} (oSpec : OracleSpec ι)

omit [IsDomain R] [Fintype R] [DecidableEq R] [SampleableType R] in
/-- The `linearCombination` phase records the sampled RLC challenge and passes statement and
oracles through unchanged, so its honest output relation from an arbitrary input relation `rel` is
the challenge-stripped pushforward: drop the recorded challenge `x.1.1.1` and require the
underlying (statement, oracles, witness) tuple to lie in `rel`. -/
def linearCombinationRelOutOf
    (rel : Set ((Statement.AfterSendEvalClaim R pp ×
        (∀ i, OracleStatement.AfterSendEvalClaim R pp i)) × Unit)) :
    Set ((Statement.AfterLinearCombination R pp ×
        (∀ i, OracleStatement.AfterLinearCombination R pp i)) × Unit) :=
  { x | ((x.1.1.2, x.1.2), ()) ∈ rel }

/-- `VerifierOnly` instance for the `linearCombination` protocol shape. Kept `local`: the exported
instance lives in `ComposedCompletenessLeaves` (`instLinearCombinationVerifierOnly`), which this
module deliberately does not import. -/
local instance :
    VerifierOnly (⟨!v[.V_to_P], !v[LinearCombinationChallenge R]⟩ : ProtocolSpec 1) where
  verifier_first' := by simp

set_option linter.unusedSimpArgs false in
omit [DecidableEq R] [SampleableType R] in
/-- **The `linearCombination` phase is perfectly complete from any input relation** to its
challenge-stripped pushforward `linearCombinationRelOutOf rel`: the phase samples the RLC
challenge, records it, and passes statement/oracles/witness through unchanged. This is the
parametric form of the leaf hypothesis `h₅` of `composedCompletenessStatement_of_five_leaves`
(instantiate `rel` with the output relation of the `sendEvalClaim` leaf). -/
theorem linearCombination_perfectCompleteness_of
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    (rel : Set ((Statement.AfterSendEvalClaim R pp ×
        (∀ i, OracleStatement.AfterSendEvalClaim R pp i)) × Unit)) :
    (oracleReduction.completedLinearCombination R pp oSpec).perfectCompleteness init impl
      rel (linearCombinationRelOutOf (R := R) pp rel) := by
  exact completedLinearCombination_perfectCompleteness_of pp oSpec rel

/-! ## The h₅ seam weld for the canonical chain -/

omit [IsDomain R] [Fintype R] [DecidableEq R] [SampleableType R] in
/-- **Seam weld (h₅ → h₆).** On the canonical relation chain of
`composedCompletenessStatement_of_five_leaves` — with
`relE := sendEvalClaimRelOut … (firstSumcheckRelOutBF …)`,
the output the proven `sendEvalClaim_perfectCompleteness` emits from the consumer-pinned
`firstSumcheckRelOutBF` — the natural pushforward output relation of the `linearCombination`
phase refines `prependRLCTargetRelIn`, the input relation of the proven honest RLC-target
adapter completeness. The R1CS conjunct transports verbatim (the phase passes statement and
oracles through); the recorded function-level eval-claim honesty gives the pointwise form by
`congrFun`. -/
theorem linearCombinationRelOutOf_sendEvalClaimBF_subset_prependRLCTargetRelIn :
    linearCombinationRelOutOf (R := R) pp
        (sendEvalClaimRelOut R pp (firstSumcheckRelOutBF (R := R) pp))
      ⊆ Bricks.prependRLCTargetRelIn (R := R) pp := by
  rintro x ⟨hR1CS, hHonest⟩
  exact ⟨hR1CS, fun idx => congrFun hHonest idx⟩

omit [DecidableEq R] [SampleableType R] in
/-- **Consumer-endpoint form of the `linearCombination` leaf completeness** (`h₅` of
`composedCompletenessStatement_of_five_leaves`): perfectly complete from
`sendEvalClaimRelOut … (firstSumcheckRelOutBF …)` (the proven `sendEvalClaim` leaf output at the
consumer-pinned `relD`) into `prependRLCTargetRelIn` (the proven input of
`prependRLCTarget_perfectCompleteness_secondSumcheckRelInBF`). With this, hypotheses `h₄`, `h₅`,
`h₆` of the five-leaves consumer chain at
`relE := sendEvalClaimRelOut … (firstSumcheckRelOutBF …)`, `relF := prependRLCTargetRelIn`. -/
theorem linearCombination_perfectCompleteness_sendEvalClaimBF
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)} :
    (oracleReduction.completedLinearCombination R pp oSpec).perfectCompleteness init impl
      (sendEvalClaimRelOut R pp (firstSumcheckRelOutBF (R := R) pp))
      (Bricks.prependRLCTargetRelIn (R := R) pp) := by
  have h := linearCombination_perfectCompleteness_of pp oSpec
    (σ := σ) (init := init) (impl := impl)
    (sendEvalClaimRelOut R pp (firstSumcheckRelOutBF (R := R) pp))
  unfold OracleReduction.perfectCompleteness Reduction.perfectCompleteness at h ⊢
  exact Reduction.completeness_relOut_mono init impl
    (linearCombinationRelOutOf_sendEvalClaimBF_subset_prependRLCTargetRelIn pp) h

end Spartan.Spec

-- Axiom checks
#print axioms Spartan.Spec.linearCombination_perfectCompleteness_of
#print axioms Spartan.Spec.linearCombinationRelOutOf_sendEvalClaimBF_subset_prependRLCTargetRelIn
#print axioms Spartan.Spec.linearCombination_perfectCompleteness_sendEvalClaimBF
