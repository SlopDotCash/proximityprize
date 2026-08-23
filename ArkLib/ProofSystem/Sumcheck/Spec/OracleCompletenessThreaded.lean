/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Sumcheck.Spec.Completeness
import ArkLib.OracleReduction.Composition.Sequential.SeqComposeOracleCompleteness

/-!
# Full multi-round sum-check perfect completeness (**oracle** level), via the proven
verifier-fusion threading keystone — without the false `toReduction = reduction` bridge

`OracleCompleteness.lean` proves `Sumcheck.Spec.oracleReduction_perfectCompleteness_of_bridge`
only *modulo* the documented-**false** bridge

  `oracleReductionToReductionResidual R deg D n oSpec`
      i.e. `(oracleReduction R deg D n oSpec).toReduction = reduction R deg D n oSpec`.

That equation is genuinely false for sum-check: the oracle verifier checks the *input-oracle*
polynomial's `D`-sum, while the plain `reduction`'s verifier checks the *message* polynomial's
`D`-sum; they diverge off honest transcripts (the documented-false `oracleReduction_eq_reduction`).
`OracleCompletenessUncond.lean` discharges that bridge from a per-round `toReduction = reduction`
fact `hPerRound`, but each such per-round equation is *itself* the same kind of false bridge.

This file gives the oracle-level completeness through the **correct** route, which never asserts that
false equation. The chain is:

* `OracleReduction.perfectCompleteness oR` is, definitionally, `Reduction.perfectCompleteness
  oR.toReduction`.
* The proven, **unconditional** n-ary keystone
  `OracleReduction.seqCompose_perfectCompleteness_threaded`
  (in `SeqComposeOracleCompleteness.lean`) — itself built from the proven binary verifier-fusion
  `OracleReduction.appendToReductionResidual_proof`
  (`(R₁.append R₂).toReduction = R₁.toReduction.append R₂.toReduction`) threaded along the
  `seqCompose` induction — assembles the oracle-level `seqCompose` perfect completeness from the
  per-round **oracle** completenesses. It rewrites the oracle `seqCompose`'s `toReduction` to the
  `Reduction`-level `seqCompose` of the per-round `toReduction`s, *not* to the plain `reduction`, so
  no false equation is used.

The single remaining input is the **per-round oracle completeness**
`(SingleRound.oracleReduction i).perfectCompleteness`. This is the tight, honest residual; unlike
`hPerRound`, it is a *true* statement (the honest sum-check round is complete). It is obtained from
the proven `Simple.oracleReduction_perfectCompleteness` via
`OracleReduction.liftContext_perfectCompleteness`, the *only* genuine side condition being the
single-round oracle-routing lens coherence `OracleVerifier.LiftContextCoherent sumcheckOracleLens
(Simple.oracleReduction …).verifier` — the virtual-oracle summation faithfulness `hfaith`, the same
mathematical content as the per-round `proj_complete`/`sumcheck_round_split` already proven in
`oCtxLens_complete`. We carry that coherence as the named instance hypothesis `[coh]`, which any
concrete instantiation discharging its lens' `LiftContextCoherent` side condition supplies (exactly
as the LogUp / Spartan lenses do via `liftContextCoherent_of`).

Everything else — the seqCompose verifier fusion (`appendToReductionResidual_proof`), the threading,
and the `Reduction`-level probabilistic engine — is fully proven and axiom-clean on `main`.
-/

open ProtocolSpec OracleComp OracleSpec
open scoped NNReal

namespace Sumcheck.Spec

namespace SingleRound

variable {R : Type} [CommSemiring R] [SampleableType R] [DecidableEq R] [Fintype R] [Inhabited R]
  {n : ℕ} {deg : ℕ} {m : ℕ} {D : Fin m ↪ R}
  {ι : Type} {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

set_option linter.unusedFintypeInType false in
/-- **Per-round oracle perfect completeness.**

The `i`-th-round oracle reduction `SingleRound.oracleReduction i =
(Simple.oracleReduction).liftContext (oCtxLens i) (sumcheckOracleLens i)` is perfectly complete,
lifted from the proven `Simple.oracleReduction_perfectCompleteness` through
`OracleReduction.liftContext_perfectCompleteness`. The value-level completeness side condition is
the already-proven `oCtxLens_complete` (`proj_complete` is the round-split `sumcheck_round_split`,
`lift_complete` the round-update `sumcheck_round_eval_snoc`); `hStmt` holds by `rfl`
(`sumcheckOracleLens.toLens = oStmtLens = oCtxLens.stmt`). The sole genuine residual is the
oracle-routing coherence `[coh]` of the sum-check lens — the virtual `|D|^(n-1)`-fold summation
faithfulness — supplied on the nose by any concrete instantiation's `LiftContextCoherent`. -/
theorem oracleReduction_perfectCompleteness (i : Fin n)
    [coh : OracleVerifier.LiftContextCoherent (sumcheckOracleLens R n deg D oSpec i)
      (Simple.oracleReduction R deg D oSpec).verifier] :
    (oracleReduction R n deg D oSpec i).perfectCompleteness init impl
      (relationRound R n deg D i.castSucc) (relationRound R n deg D i.succ) :=
  OracleReduction.liftContext_perfectCompleteness
    (lens := oCtxLens R n deg D i)
    (stmtLens := sumcheckOracleLens R n deg D oSpec i)
    (R := Simple.oracleReduction R deg D oSpec)
    (hStmt := rfl)
    (Simple.oracleReduction_perfectCompleteness R deg D oSpec)

end SingleRound

variable {R : Type} [CommSemiring R] [SampleableType R] [DecidableEq R] [Fintype R] [Inhabited R]
  {n : ℕ} {deg : ℕ} {m : ℕ} {D : Fin m ↪ R}
  {ι : Type} {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

-- The `@`-applied keystone elaborates a large dependent `seqCompose` `toReduction` bridge through
-- the `change`/`rw`, so we raise the heartbeat limit.
set_option maxHeartbeats 1000000 in
set_option linter.unusedFintypeInType false in
/-- **Full multi-round sum-check perfect completeness (oracle level) — without the false bridge.**

Assembled honestly through the proven, unconditional n-ary verifier-fusion threading keystone
`OracleReduction.seqCompose_perfectCompleteness_threaded` (which discharges every append seam via
the proven binary fusion `appendToReductionResidual_proof`, never asserting the false
`toReduction = reduction`) from the per-round **oracle** completeness
`SingleRound.oracleReduction_perfectCompleteness`. The latter is a *true* statement, supplied from
the proven `Simple.oracleReduction_perfectCompleteness` via `liftContext_perfectCompleteness`.

The only hypotheses are the honest data facts already required by the proven
`reduction_perfectCompleteness` (`hInit`, `hImplSupp`) together with the per-round oracle-routing
lens coherence `[coh]` (the single genuine residual — the virtual-oracle summation faithfulness of
`sumcheckOracleLens`). No `appendToReductionResidual` / verifier-fusion `hBridge` obligation remains,
and no false `toReduction = reduction` equation is used anywhere in the chain. -/
theorem oracleReduction_perfectCompleteness
    [coh : ∀ i, OracleVerifier.LiftContextCoherent (SingleRound.sumcheckOracleLens R n deg D oSpec i)
      (SingleRound.Simple.oracleReduction R deg D oSpec).verifier]
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β)) :
    (oracleReduction R deg D n oSpec).perfectCompleteness init impl
      (relationRound R n deg D 0) (relationRound R n deg D (Fin.last n)) := by
  -- The per-round challenge `Fintype`/`Inhabited` (each challenge is a field element) are not
  -- available as instances; supply them explicitly from `chalFintype`/`chalInhab` (built explicitly
  -- from `[Fintype R]`/`[Inhabited R]`) via `@`-application of the keystone.
  exact @OracleReduction.seqCompose_perfectCompleteness_threaded
    ι oSpec _ _ σ init impl n (StatementRound R n) _ (fun _ => OracleStatement R n deg) _
    (fun _ => Unit) _ _ _ _
    (fun _ => SingleRound.chalFintype) (fun _ => SingleRound.chalInhab)
    (SingleRound.oracleReduction R n deg D oSpec) _
    (fun i => relationRound R n deg D i)
    (fun _ => ⟨by omega, SingleRound.pSpec_dir_zero⟩)
    hInit hImplSupp
    (fun i => SingleRound.oracleReduction_perfectCompleteness (coh := coh i) i)

end Sumcheck.Spec

#print axioms Sumcheck.Spec.SingleRound.oracleReduction_perfectCompleteness
#print axioms Sumcheck.Spec.oracleReduction_perfectCompleteness
