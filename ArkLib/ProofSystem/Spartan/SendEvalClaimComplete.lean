/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ProximityPrize.Compatibility.SpartanSendEvalClaim
import ProximityPrize.Extensions.ProofSystem.Spartan.Basic
import ArkLib.ProofSystem.Spartan.FirstSumcheckBridgeFree

/-!
# `sendEvalClaim` leaf perfect completeness, pinned to the bridge-free chain (#114)

Discharges the `h₄` hypothesis of
`Spartan.Spec.Bricks.composedCompletenessStatement_of_five_leaves`
(`ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean`): the 1-message `P_to_V` phase
`oracleReduction.completedSendEvalClaim` is perfectly complete from the pinned input relation
`firstSumcheckRelOutBF` into the pinned output relation `sendEvalClaimRelOutBF`
(instantiate the residual's free `relE := sendEvalClaimRelOutBF R pp`).

* `sendEvalClaimRelOutBF` — the input relation carried through (`firstSumcheckRelOutBF` on the
  recovered input pair, i.e. R1CS satisfiability) **and** the canonical scalar claim family `.inl idx`
  is honest (equals `evalClaimValue`). This is the canonical honest choice of `relE`: it preserves
  the full input relation and adds exactly the honesty fact that the downstream honest-RLC-target
  adapter (`prependRLCTarget`) consumes.
* `sendEvalClaim_perfectCompleteness_BF` — the leaf perfect-completeness theorem itself
  (deterministic 1-message forwarding phase; the verifier performs no check).
* `sendEvalClaimRelOutBF_eq_concrete` — definitional unfolding into the concrete
  `R1CS.relation ∧ honesty` form (the shape the `linearCombination` leaf consumes downstream).

This module is deliberately self-contained over the stable chain (`Spartan.Basic` +
`FirstSumcheckBridgeFree`): it does not import `ComposedCompletenessLeaves` (whose parametric
`sendEvalClaim_perfectCompleteness` yields the same fact but whose module carries the in-flight
`prependRLCTarget` completeness section).
-/

open OracleComp OracleSpec ProtocolSpec OracleInterface Function

namespace Spartan.Spec

variable (R : Type) [CommRing R] [Fintype R] (pp : PublicParams)
variable {ι : Type} (oSpec : OracleSpec ι)
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- Output relation of the `sendEvalClaim` phase, pinned to the bridge-free chain: the recovered
input pair (dropping the freshly sent scalar claim family) still satisfies
`firstSumcheckRelOutBF` (R1CS satisfiability), and the scalar evaluation-claim family is honest — it
equals `evalClaimValue` of the carried statement and the forwarded input oracles. -/
def sendEvalClaimRelOutBF :
    Set ((Statement.AfterSendEvalClaim R pp ×
        (∀ i, OracleStatement.AfterSendEvalClaim R pp i)) × Unit) :=
  { x | ((x.1.1, fun j => x.1.2 (.inr j)), ()) ∈ firstSumcheckRelOutBF (R := R) pp ∧
        (fun idx => x.1.2 (.inl idx)) = evalClaimValue R pp x.1.1 (fun j => x.1.2 (.inr j)) }

omit [Fintype R] in
/-- `sendEvalClaimRelOutBF`, unfolded to the concrete `R1CS.relation ∧ honesty` form (the shape
the downstream `linearCombination` leaf and the honest-RLC-target adapter consume). -/
theorem sendEvalClaimRelOutBF_eq_concrete :
    sendEvalClaimRelOutBF R pp =
      { x | R1CS.relation R pp.toSizeR1CS x.1.1.2.2
            (fun idx => x.1.2 (.inr (.inl idx))) (x.1.2 (.inr (.inr 0)))
          ∧ (fun idx => x.1.2 (.inl idx)) = evalClaimValue R pp x.1.1 (fun j => x.1.2 (.inr j)) } := rfl

/-- **The `sendEvalClaim` leaf is perfectly complete (pinned, #114).** From the bridge-free first
sum-check output relation `firstSumcheckRelOutBF`, the 1-message `P_to_V` phase
`oracleReduction.completedSendEvalClaim` lands in `sendEvalClaimRelOutBF`: the honest prover forwards the
input oracles and sends the bundled eval-claim `evalClaimValue`; the verifier performs no check,
so both the relation pass-through and the eval-claim honesty are deterministic.

This is exactly the `h₄` obligation of `composedCompletenessStatement_of_five_leaves` with
`relE := sendEvalClaimRelOutBF R pp`. -/
theorem sendEvalClaim_perfectCompleteness_BF :
    (oracleReduction.completedSendEvalClaim R pp oSpec).perfectCompleteness init impl
      (firstSumcheckRelOutBF (R := R) pp) (sendEvalClaimRelOutBF R pp) := by
  change ((oracleReduction.completedSendEvalClaim R pp oSpec).toReduction).perfectCompleteness
    init impl (firstSumcheckRelOutBF (R := R) pp) (sendEvalClaimRelOutBF R pp)
  apply Reduction.perfectCompleteness_of_run_support
  rintro ⟨stmt, oStmt⟩ ⟨⟩ hIn z hz
  have : ProverOnly (⟨!v[.P_to_V], !v[∀ i, EvalClaim R i]⟩ : ProtocolSpec 1) :=
    { prover_first' := by simp }
  simp only [OracleReduction.toReduction, oracleReduction.completedSendEvalClaim] at hz
  rw [Reduction.run_of_prover_first] at hz
  simp only [sendEvalClaimProver, sendEvalClaimVerifier, liftM_pure, pure_bind,
    bind_pure_comp, OracleVerifier.toVerifier] at hz
  simp only [OptionT.run_mk, OptionT.run_pure, simulateQ_pure, pure_bind, map_pure, liftM_pure,
    Option.getM_some, Option.map_some] at hz
  simp_all [sendEvalClaimRelOutBF, OracleVerifier.materializeOutput,
    OracleVerifier.materializeOutputOracle]
  exact ⟨rfl, rfl⟩

end Spartan.Spec

-- Axiom check
#print axioms Spartan.Spec.sendEvalClaim_perfectCompleteness_BF
