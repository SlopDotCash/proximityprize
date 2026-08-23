/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Spartan.Basic
import ArkLib.ProofSystem.Spartan.FirstSumcheckBridgeFree

/-!
# `sendEvalClaim` leaf perfect completeness, pinned to the bridge-free chain (#114)

Discharges the `h₄` hypothesis of
`Spartan.Spec.Bricks.composedCompletenessStatement_of_five_leaves`
(`ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean`): the 1-message `P_to_V` phase
`oracleReduction.sendEvalClaim` is perfectly complete from the pinned input relation
`firstSumcheckRelOutBF` into the pinned output relation `sendEvalClaimRelOutBF`
(instantiate the residual's free `relE := sendEvalClaimRelOutBF R pp`).

* `sendEvalClaimRelOutBF` — the input relation carried through (`firstSumcheckRelOutBF` on the
  recovered input pair, i.e. R1CS satisfiability) **and** the bundled eval-claim oracle `.inl 0`
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

variable (R : Type) [CommRing R] (pp : PublicParams)
variable {ι : Type} (oSpec : OracleSpec ι)
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- Output relation of the `sendEvalClaim` phase, pinned to the bridge-free chain: the recovered
input pair (dropping the freshly-bundled claim oracle `.inl 0`) still satisfies
`firstSumcheckRelOutBF` (R1CS satisfiability), and the bundled eval-claim oracle is honest — it
equals `evalClaimValue` of the carried statement and the forwarded input oracles. -/
def sendEvalClaimRelOutBF :
    Set ((Statement.AfterSendEvalClaim R pp ×
        (∀ i, OracleStatement.AfterSendEvalClaim R pp i)) × Unit) :=
  { x | ((x.1.1, fun j => x.1.2 (.inr j)), ()) ∈ firstSumcheckRelOutBF (R := R) pp ∧
        x.1.2 (.inl 0) = evalClaimValue R pp x.1.1 (fun j => x.1.2 (.inr j)) }

/-- `sendEvalClaimRelOutBF`, unfolded to the concrete `R1CS.relation ∧ honesty` form (the shape
the downstream `linearCombination` leaf and the honest-RLC-target adapter consume). -/
theorem sendEvalClaimRelOutBF_eq_concrete :
    sendEvalClaimRelOutBF R pp =
      { x | R1CS.relation R pp.toSizeR1CS x.1.1.2.2
            (fun idx => x.1.2 (.inr (.inl idx))) (x.1.2 (.inr (.inr 0)))
          ∧ x.1.2 (.inl 0) = evalClaimValue R pp x.1.1 (fun j => x.1.2 (.inr j)) } := rfl

/-- **The `sendEvalClaim` leaf is perfectly complete (pinned, #114).** From the bridge-free first
sum-check output relation `firstSumcheckRelOutBF`, the 1-message `P_to_V` phase
`oracleReduction.sendEvalClaim` lands in `sendEvalClaimRelOutBF`: the honest prover forwards the
input oracles and sends the bundled eval-claim `evalClaimValue`; the verifier performs no check,
so both the relation pass-through and the eval-claim honesty are deterministic.

This is exactly the `h₄` obligation of `composedCompletenessStatement_of_five_leaves` with
`relE := sendEvalClaimRelOutBF R pp`. -/
theorem sendEvalClaim_perfectCompleteness_BF :
    (oracleReduction.sendEvalClaim R pp oSpec).perfectCompleteness init impl
      (firstSumcheckRelOutBF (R := R) pp) (sendEvalClaimRelOutBF R pp) := by
  simp only [OracleReduction.perfectCompleteness, Reduction.perfectCompleteness,
    Reduction.completeness, Reduction.completenessFromRun, ENNReal.coe_zero, tsub_zero]
  intro ⟨stmt, oStmt⟩ wit hIn
  have _inst : ProverOnly (⟨!v[.P_to_V], !v[∀ i, EvalClaim R i]⟩ : ProtocolSpec 1) :=
    { prover_first' := by simp }
  simp only [OracleReduction.toReduction, oracleReduction.sendEvalClaim]
  rw [Reduction.run_of_prover_first]
  simp only [sendEvalClaimProver, sendEvalClaimVerifier, liftM_pure, pure_bind,
    bind_pure_comp, OracleVerifier.toVerifier]
  erw [simulateQ_pure]
  simp only [map_pure, StateT.run'_eq, StateT.run_pure]
  rw [ge_iff_le, one_le_probEvent_iff, probEvent_eq_one_iff]
  refine ⟨?_, ?_⟩
  · -- `probFailure = 0`: a `ProbComp` (`OracleComp unifSpec`) cannot fail and the appended
    -- `pure (some ·)` is total, so the failure probability is structurally zero.
    rw [OptionT.probFailure_eq, OptionT.run_mk]
    simp
  · intro x hx
    rw [OptionT.mem_support_iff, OptionT.run_mk] at hx
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hx
    obtain ⟨s, _, hx⟩ := hx
    cases hx
    refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · -- relation pass-through: input pair recovered from `.inr` part lands in the input relation
        convert hIn using 2
      · -- eval-claim honesty: `.inl 0` slot equals the honest `evalClaimValue`
        rfl
    · -- prover output statement equals verifier output statement
      refine Prod.ext rfl ?_
      funext i
      rcases i with j | j <;> rfl

end Spartan.Spec

-- Axiom check
#print axioms Spartan.Spec.sendEvalClaim_perfectCompleteness_BF
