/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Spartan.TightRLCKernel

/-!
# The tight `linearCombination` rbr knowledge-soundness leaf at `1/|R|` (issue #329, Brick A)

The existing leaf `linearCombination_rbrKnowledgeSoundness_leaf`
(`ShortPhaseRbrKnowledgeLeaves.lean`) is honest but trivial: on the no-claim relation chain
`relE := sendEvalClaimRbrRelE → relF := prependRLCTargetRbrRelF` the per-round error is forced
to `1`, because a prover that sends the **true** evaluation claims makes the RLC target
genuinely equal the second sum-check's cube sum for *every* challenge, so the doom of the first
sum-check cannot propagate.

This module repairs the relation chain by **pinning the sent claims to their true values**,
abstractly over a pinning function
`trueV : StmtIn → (R1CS.MatrixIdx → R)` (the honest claim values; the concrete instantiation
`trueV = fun (stmt, oStmt) idx => (M_idx 𝕫) ⸨r_x⸩`-style evaluation is follow-up work):

* `linearCombinationRelE_pinned trueV` — the input relation: the base `sendEvalClaimRbrRelE`
  **and** the bundled claim oracle (the `.inl 0` component of
  `OracleStatement.AfterSendEvalClaim`) equals `trueV` of the input statement;
* `linearCombinationRelF_pinned trueV` — the output relation: the base
  `prependRLCTargetRbrRelF` content, the base `relE` content transported along the underlying
  statement `(y.1.1.2, y.1.2)` (the `linearCombination` verifier only prepends the sampled
  challenge, so the input statement is recoverable from the output), **and** the RLC pin
  `∑ idx, r idx * claims idx = ∑ idx, r idx * trueV idx` — the carried RLC target (which the
  verifier computes from the *sent* claims) agrees with the RLC of the *true* values at the
  sampled challenge.

With these relations the false-to-true case split is clean. For a doomed input
(`∉ relE_pinned`) either:

* **(a)** the claims are true but the base `relE` fails: the transported `relE` conjunct of
  `relF_pinned` is challenge-independent and false, so the flip probability is `0`; or
* **(b)** the claims differ from `trueV`: membership in `relF_pinned` forces the RLC pin, which
  is exactly the affine kernel event of `TightRLCKernel`, so by
  `probEvent_linearForm_eq_le` the flip probability is at most `1/|R|`.

The main theorem `linearCombination_rbrKnowledgeSoundness_tight` plugs this case split into the
generic combinator `Verifier.rbrKnowledgeSoundness_singleChallenge_pure` via the closed form
`linearCombination_toVerifier_closed`, giving per-round error `1/|R|` instead of `1`.

`linearCombination_tight_error_exact` is the matching-attack certificate (the A3 tightness
side): for an attacker whose claims differ from `trueV` while the remaining `relF_pinned`
content holds whenever the RLC pin does, the flip probability is **exactly** `1/|R|`
(`TightRLCKernel.probEvent_linearForm_eq`), so no per-round error below `1/|R|` is achievable
at these relations.
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

/-! ### The claim-pinned relation chain -/

/-- The claim-pinned input relation for the `linearCombination` round: the base
`sendEvalClaimRbrRelE` together with the pin that the bundled evaluation-claim oracle
(the `.inl 0` component) carries exactly the true values `trueV` of the input statement. -/
@[reducible]
def linearCombinationRelE_pinned
    (trueV : Statement.AfterSendEvalClaim R pp ×
      (∀ i, OracleStatement.AfterSendEvalClaim R pp i) → R1CS.MatrixIdx → R) :
    Set ((Statement.AfterSendEvalClaim R pp ×
      ∀ i, OracleStatement.AfterSendEvalClaim R pp i) × Unit) :=
  { x | x ∈ sendEvalClaimRbrRelE (R := R) pp oSpec ∧ x.1.2 (.inl 0) = trueV x.1 }

/-- The claim-pinned output relation for the `linearCombination` round: the base
`prependRLCTargetRbrRelF` content, the base `relE` content transported along the underlying
input statement `(y.1.1.2, y.1.2)`, and the **RLC pin**: the random linear combination of the
*sent* claims (the carried RLC target, by the verifier's construction) equals the random linear
combination of the *true* values at the sampled challenge `y.1.1.1`. -/
@[reducible]
def linearCombinationRelF_pinned
    (trueV : Statement.AfterSendEvalClaim R pp ×
      (∀ i, OracleStatement.AfterSendEvalClaim R pp i) → R1CS.MatrixIdx → R) :
    Set ((Statement.AfterLinearCombination R pp ×
      ∀ i, OracleStatement.AfterLinearCombination R pp i) × Unit) :=
  { y | y ∈ prependRLCTargetRbrRelF (R := R) pp oSpec ∧
        ((y.1.1.2, y.1.2), ()) ∈ sendEvalClaimRbrRelE (R := R) pp oSpec ∧
        (∑ idx, y.1.1.1 idx * y.1.2 (.inl 0) idx)
          = ∑ idx, y.1.1.1 idx * trueV (y.1.1.2, y.1.2) idx }

/-! ### The tight leaf -/

/-- **The tight `linearCombination` leaf (issue #329, Brick A).** On the claim-pinned relation
chain `linearCombinationRelE_pinned trueV → linearCombinationRelF_pinned trueV`, the
`linearCombination` phase is rbr knowledge-sound with per-round error `1/|R|` (instead of the
error `1` forced on the no-claim chain): a doomed prover either fails the challenge-independent
transported content (flip probability `0`), or carries claims `≠ trueV` and must hit the RLC
kernel event, which `TightRLCKernel.probEvent_linearForm_eq_le` bounds by `1/|R|`. -/
theorem linearCombination_rbrKnowledgeSoundness_tight
    (trueV : Statement.AfterSendEvalClaim R pp ×
      (∀ i, OracleStatement.AfterSendEvalClaim R pp i) → R1CS.MatrixIdx → R) :
    (oracleReduction.linearCombination R pp oSpec).verifier.rbrKnowledgeSoundness init impl
      (linearCombinationRelE_pinned (R := R) pp oSpec trueV)
      (linearCombinationRelF_pinned (R := R) pp oSpec trueV)
      (fun _ => (1 : ℝ≥0) / (Fintype.card R : ℝ≥0)) := by
  unfold OracleVerifier.rbrKnowledgeSoundness
  rw [linearCombination_toVerifier_closed]
  refine Verifier.rbrKnowledgeSoundness_singleChallenge_pure
    (C := LinearCombinationChallenge R)
    init impl
    (fun (p : Statement.AfterSendEvalClaim R pp ×
        ∀ i, OracleStatement.AfterSendEvalClaim R pp i) c => ((c, p.1), p.2))
    (linearCombinationRelE_pinned (R := R) pp oSpec trueV)
    (linearCombinationRelF_pinned (R := R) pp oSpec trueV) _ ?_
  intro stmtIn hbad
  by_cases hclaims : stmtIn.2 (.inl 0) = trueV stmtIn
  · -- Case (a): claims are true but the base `relE` fails — the transported `relE` conjunct of
    -- the output relation is challenge-independent and false, so the flip probability is `0`.
    have hrelE : (stmtIn, ()) ∉ sendEvalClaimRbrRelE (R := R) pp oSpec :=
      fun h => hbad ⟨h, hclaims⟩
    refine le_trans (le_of_eq (probEvent_eq_zero_iff.mpr ?_)) (zero_le _)
    intro c _ hc
    obtain ⟨-, h2, -⟩ := hc
    exact hrelE h2
  · -- Case (b): claims differ from `trueV` — membership forces the RLC kernel event, bounded
    -- by `1/|R|` via the TightRLCKernel affine corollary.
    refine le_trans (probEvent_mono ?_)
      (probEvent_linearForm_eq_le (stmtIn.2 (.inl 0)) (trueV stmtIn) hclaims)
    intro c _ hc
    obtain ⟨-, -, h3⟩ := hc
    exact h3

/-! ### The matching-attack certificate (A3 tightness at these relations) -/

/-- **Exact tightness of the `1/|R|` leaf error at the claim-pinned relations.** Consider an
attacker at a doomed input whose claims differ from the true values (`hclaims`) but whose
remaining data is otherwise consistent: whenever the sampled challenge hits the RLC kernel
event, the rest of the `relF_pinned` content holds (`hcompat` — e.g. the prover sent the honest
matrices/witness so the base relations are genuinely satisfied, only the claims are off). Then
the false-to-true flip probability is **exactly** `1/|R|`
(`TightRLCKernel.probEvent_linearForm_eq`): the per-round error of
`linearCombination_rbrKnowledgeSoundness_tight` cannot be improved at these relations. -/
theorem linearCombination_tight_error_exact
    (trueV : Statement.AfterSendEvalClaim R pp ×
      (∀ i, OracleStatement.AfterSendEvalClaim R pp i) → R1CS.MatrixIdx → R)
    (stmtIn : Statement.AfterSendEvalClaim R pp ×
      ∀ i, OracleStatement.AfterSendEvalClaim R pp i)
    (hclaims : stmtIn.2 (.inl 0) ≠ trueV stmtIn)
    (hcompat : ∀ c : LinearCombinationChallenge R,
      (∑ idx, c idx * stmtIn.2 (.inl 0) idx) = (∑ idx, c idx * trueV stmtIn idx) →
      ((((c, stmtIn.1), stmtIn.2)), ()) ∈
        linearCombinationRelF_pinned (R := R) pp oSpec trueV) :
    Pr[fun c : LinearCombinationChallenge R =>
        ((((c, stmtIn.1), stmtIn.2)), ()) ∈
          linearCombinationRelF_pinned (R := R) pp oSpec trueV
      | $ᵗ (LinearCombinationChallenge R)]
      = 1 / (Fintype.card R : ENNReal) := by
  have hev : (fun c : LinearCombinationChallenge R =>
        ((((c, stmtIn.1), stmtIn.2)), ()) ∈
          linearCombinationRelF_pinned (R := R) pp oSpec trueV)
      = (fun c : LinearCombinationChallenge R =>
          (∑ idx, c idx * stmtIn.2 (.inl 0) idx) = ∑ idx, c idx * trueV stmtIn idx) := by
    funext c
    apply propext
    constructor
    · rintro ⟨-, -, h3⟩
      exact h3
    · exact hcompat c
  rw [hev]
  exact probEvent_linearForm_eq (stmtIn.2 (.inl 0)) (trueV stmtIn) hclaims

end

end Spartan.Spec.Bricks

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms Spartan.Spec.Bricks.linearCombination_rbrKnowledgeSoundness_tight
#print axioms Spartan.Spec.Bricks.linearCombination_tight_error_exact
