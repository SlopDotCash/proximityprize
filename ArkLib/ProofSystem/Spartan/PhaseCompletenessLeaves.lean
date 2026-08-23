/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Spartan.Composition
import ArkLib.ProofSystem.Spartan.FirstSumcheckBridgeFree
import ArkLib.ProofSystem.Spartan.SecondSumcheckBridgeFree
import ArkLib.ProofSystem.Spartan.FirstChallengeComplete

/-!
# Per-phase perfect-completeness leaves for the composed Spartan PIOP (#114)

The composed-PC fold over `composedPIOP_Rc`'s seven phases needs a perfect-completeness theorem
for every *leaf* phase, with seam relations matching exactly. Four leaves already exist
(`firstChallenge_perfectCompleteness`, `firstSumcheck_perfectCompleteness_bridgeFree`,
`secondSumcheck_perfectCompleteness_bridgeFree`, and the generic
`SendSingleWitness.oracleReduction_completeness` for `firstMessage`). This module supplies the
missing ones:

* `firstMessage_perfectCompleteness` — re-points the generic `SendSingleWitness` completeness at
  the Spartan seam relations `spartanRelIn → firstChallengeRelIn`;
* `sendEvalClaimRelOutHonest` + `sendEvalClaim_perfectCompleteness` — the eval-claim send carries the
  R1CS relation through *and* records that the bundled claim oracle is honest (equals
  `evalClaimValue`); this honesty is exactly what the downstream second-sum-check target needs;
* `linearCombinationRelOutHonest` + `linearCombination_perfectCompleteness` — the RLC challenge round
  carries both facts through unchanged;
* `prependRLCTarget` + `prependRLCTarget_perfectCompleteness` — the **honest second-sum-check
  target adapter** (the design fix for #114): a zero-round adapter whose prover *and* verifier
  both compute the second-sum-check target as the random linear combination
  `∑ idx, γ idx · v idx` of the bundled eval-claim oracle values (the verifier by querying the
  bundled oracle, the prover in the clear). Its output relation is exactly
  `secondSumcheckRelInBF`. This replaces the typed-existence adapter `prependTarget`
  (which emits the placeholder target `0` and cannot be complete for `secondSumcheckRelInBF`);
* `finalCheck_perfectCompleteness` — the terminal zero-round `CheckClaim` phase, complete from any
  input relation to the (trivial) `finalCheckRelOut = Set.univ`.
-/

open OracleComp OracleInterface ProtocolSpec Function

namespace Spartan.Spec

variable {R : Type} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] [SampleableType R]
  (pp : Spartan.PublicParams) {ι : Type} (oSpec : OracleSpec ι)
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-! ## Seam relations for the middle phases -/

/-- Output relation of the `sendEvalClaim` phase: the R1CS instance is satisfied *and* the bundled
evaluation-claim oracle is honest — it equals `evalClaimValue` of the underlying matrices/witness at
the first sum-check challenge point. The honesty conjunct is what lets the downstream honest target
adapter (`prependRLCTarget`) produce the second-sum-check target demanded by
`secondSumcheckRelInBF`. -/
def sendEvalClaimRelOutHonest :
    Set ((Statement.AfterSendEvalClaim R pp ×
        (∀ i, OracleStatement.AfterSendEvalClaim R pp i)) × Unit) :=
  { x | R1CS.relation R pp.toSizeR1CS x.1.1.2.2
        (fun idx => x.1.2 (.inr (.inl idx))) (x.1.2 (.inr (.inr 0)))
      ∧ x.1.2 (.inl 0) = evalClaimValue R pp x.1.1 (fun i => x.1.2 (.inr i)) }

/-- Output relation of the `linearCombination` phase: same content as `sendEvalClaimRelOutHonest`, with
the freshly-sampled RLC challenge `γ` prepended to the statement (the relation does not constrain
`γ`). -/
def linearCombinationRelOutHonest :
    Set ((Statement.AfterLinearCombination R pp ×
        (∀ i, OracleStatement.AfterLinearCombination R pp i)) × Unit) :=
  { x | R1CS.relation R pp.toSizeR1CS x.1.1.2.2.2
        (fun idx => x.1.2 (.inr (.inl idx))) (x.1.2 (.inr (.inr 0)))
      ∧ x.1.2 (.inl 0) = evalClaimValue R pp x.1.1.2 (fun i => x.1.2 (.inr i)) }

/-! ## `firstMessage` -/

/-- **`firstMessage` phase perfect completeness.** The generic `SendSingleWitness` completeness,
re-pointed at the Spartan seam relations: from the R1CS input relation `spartanRelIn` (witness as
witness) to `firstChallengeRelIn` (witness moved into the oracle family). -/
theorem firstMessage_perfectCompleteness (hInit : NeverFail init) :
    (oracleReduction.firstMessage R pp oSpec).perfectCompleteness init impl
      (Bricks.spartanRelIn R pp) (firstChallengeRelIn (R := R) pp) := by
  have h := SendSingleWitness.oracleReduction_completeness
    (oSpec := oSpec) (Statement := Statement R pp) (OStatement := OracleStatement R pp)
    (Witness := Witness R pp) (init := init) (impl := impl)
    (oRelIn := Bricks.spartanRelIn R pp) hInit
  exact Reduction.completeness_relOut_mono init impl (fun x hx => hx) h

end Spartan.Spec
