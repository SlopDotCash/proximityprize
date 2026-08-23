/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Sumcheck.Spec.Completeness

/-!
# Full multi-round sum-check perfect completeness (**oracle** level)

`Sumcheck.Spec.reduction_perfectCompleteness` (in `Completeness.lean`) proves the multi-round
sum-check perfect completeness at the *plain* `Reduction` level. This file lifts that to the
**oracle** reduction `Sumcheck.Spec.oracleReduction`.

`OracleReduction.perfectCompleteness relIn relOut oR` is *definitionally*
`Reduction.perfectCompleteness relIn relOut oR.toReduction` (`Security/Basic.lean:472`). The
provers of `oracleReduction.toReduction` and `reduction` are definitionally equal (both are the
`Prover.seqCompose` of the per-round provers). The *only* remaining content is the verifier-side
fusion:

  `oracleVerifier.toVerifier = verifier`,

i.e. that the `seqCompose`d oracle-verifier's routed `simulateQ`s factor as the `seqCompose`d
plain verifier. At the general `seqCompose` level this is the still-open named residual
`OracleReduction.appendToReductionResidual` / `OracleVerifier.seqCompose_toVerifier` (the
verifier analogue of `Prover.append_run`); see
`OracleReduction/Composition/Sequential/AppendPerfectCompletenessOracle.lean` and
`AppendVerifierFusion.lean`, where only the per-router intermediate lemmas are discharged so far.

Accordingly, we take that single equation as the explicit, clearly-named hypothesis `hBridge` of
the main theorem and discharge everything else honestly via the proven
`reduction_perfectCompleteness`. A later brick that closes the seqCompose verifier-fusion residual
supplies `hBridge` on the nose. We additionally record the *unconditional* corollary
`oracleReduction_perfectCompleteness_of_toReduction_eq`, phrased directly against the bridge
equation, so that any consumer who has the fusion lemma in hand gets the oracle-level completeness
with no further obligation.
-/

open ProtocolSpec OracleComp OracleSpec
open scoped NNReal

namespace Sumcheck.Spec

variable {R : Type} [CommSemiring R] [SampleableType R] [DecidableEq R] [Fintype R] [Inhabited R]
  {n : ℕ} {deg : ℕ} {m : ℕ} {D : Fin m ↪ R}
  {ι : Type} {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- **The single residual** isolating the verifier-side fusion for the full multi-round sum-check
oracle reduction: the `Verifier` image of the `seqCompose`d oracle reduction equals the `Reduction`
obtained from `seqCompose`ing the plain reductions. The provers are definitionally equal, so this is
the *entire* remaining content of the oracle-level completeness — the verifier analogue of
`Prover.append_run`, lifted along `seqCompose`.

**SUPERSEDED + SUSPECTED FALSE AS STATED (audit 2026-06-10).**  The per-round reduction of this
bridge (`SingleRoundBridge.lean`) bottoms out in the single-round equation
`(Simple.oracleReduction).toReduction = Simple.reduction`, which is the documented suspected-false
`oracleReduction_eq_reduction` (the two verifiers check different objects, so the syntactic
equality is not expected to hold).  The live, bridge-FREE apex is
`oracleReduction_perfectCompleteness_unconditional`
(`OracleCompletenessUncondCorrect.lean`), proven via the CubeFiber coherence instance with no
bridge anywhere; Spartan consumers are routed around this Prop by `FirstSumcheckBridgeFree` /
`SecondSumcheckBridgeFree`.  Remaining consumers of this Prop form a legacy conditional chain
(`OracleCompletenessUncond`, `SingleRoundBridge`, `SpartanSumcheckUnconditional`, Logup's
`BridgeAndAppendResiduals`); do not build new work on it.

Ledger status (#351): legacy surface, superseded; the live apex is bridge-free (#114).
Kept only for the conditional chain above; build nothing new on it. -/
abbrev oracleReductionToReductionResidual (R : Type) [CommSemiring R] [SampleableType R]
    [DecidableEq R] (deg : ℕ) {m : ℕ} (D : Fin m ↪ R) (n : ℕ) {ι : Type} (oSpec : OracleSpec ι) :
    Prop :=
  (oracleReduction R deg D n oSpec).toReduction = reduction R deg D n oSpec

/-- **Full multi-round sum-check perfect completeness (oracle level), modulo the verifier bridge.**

`OracleReduction.perfectCompleteness` unfolds to `Reduction.perfectCompleteness` of
`oracleReduction.toReduction`; the named bridge `hBridge` rewrites that to `reduction`, and the
proven `reduction_perfectCompleteness` closes the goal. The `hInit`/`hImplSupp` hypotheses are
exactly those of `reduction_perfectCompleteness`. -/
theorem oracleReduction_perfectCompleteness_of_bridge
    (hBridge : oracleReductionToReductionResidual R deg D n oSpec)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β)) :
    (oracleReduction R deg D n oSpec).perfectCompleteness init impl
      (relationRound R n deg D 0) (relationRound R n deg D (Fin.last n)) := by
  -- `OracleReduction.perfectCompleteness ... oracleReduction`
  --   `= Reduction.perfectCompleteness ... oracleReduction.toReduction` (definitional).
  change Reduction.perfectCompleteness init impl
    (relationRound R n deg D 0) (relationRound R n deg D (Fin.last n))
    (oracleReduction R deg D n oSpec).toReduction
  -- Bridge the oracle reduction's `toReduction` to the plain `reduction`.
  rw [hBridge]
  -- Discharge with the already-proven reduction-level completeness.
  exact reduction_perfectCompleteness hInit hImplSupp

/-- Restatement of `oracleReduction_perfectCompleteness_of_bridge` directly against the bare bridge
equation `oracleReduction.toReduction = reduction`, so a consumer holding the seqCompose
verifier-fusion lemma can apply it with no `abbrev` indirection. -/
theorem oracleReduction_perfectCompleteness_of_toReduction_eq
    (hBridge : (oracleReduction R deg D n oSpec).toReduction = reduction R deg D n oSpec)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β)) :
    (oracleReduction R deg D n oSpec).perfectCompleteness init impl
      (relationRound R n deg D 0) (relationRound R n deg D (Fin.last n)) :=
  oracleReduction_perfectCompleteness_of_bridge hBridge hInit hImplSupp

end Sumcheck.Spec

#print axioms Sumcheck.Spec.oracleReduction_perfectCompleteness_of_bridge
#print axioms Sumcheck.Spec.oracleReduction_perfectCompleteness_of_toReduction_eq
