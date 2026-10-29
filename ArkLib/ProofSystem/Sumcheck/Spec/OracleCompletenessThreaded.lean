/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Sumcheck.Spec.Completeness
import ProximityPrize.Extensions.ProofSystem.Sumcheck.Spec.SingleRound
import ArkLib.OracleReduction.Composition.Sequential.SeqComposeOracleCompleteness

/-!
# Oracle-level multi-round sum-check perfect completeness

The canonical round verifier checks the prover's message polynomial. Its completed perfect
completeness theorem supplies each round; the completed n-ary verifier-fusion engine assembles
these rounds without relying on a separate equality of reduction representations.

The historical lens-coherence binders remain available on these compatibility wrappers. The
canonical executable-lens completeness proof discharges the required projection and output
conditions directly.
-/

open ProtocolSpec OracleComp OracleSpec
open scoped NNReal

namespace Sumcheck.Spec

namespace SingleRound

variable {R : Type} [CommSemiring R] [SampleableType R] [DecidableEq R] [Fintype R] [Inhabited R]
  {n : ℕ} {deg : ℕ} {m : ℕ} {D : Fin m ↪ R}
  {ι : Type} {oSpec : OracleSpec ι} [∀ q, Fintype (oSpec.Range q)] [∀ q, Inhabited (oSpec.Range q)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

omit [Fintype R] [Inhabited R] [(q : ι) → Fintype (oSpec.Range q)]
    [(q : ι) → Inhabited (oSpec.Range q)] in
set_option linter.unusedFintypeInType false in
/-- Compatibility spelling for canonical completed round completeness, with the historical
lens-coherence parameter retained for existing callers. -/
theorem oracleReduction_perfectCompleteness_of_liftContextCoherent (i : Fin n)
    [_coh : OracleVerifier.LiftContextCoherent (sumcheckOracleLens R n deg D oSpec i)
      (Simple.oracleReduction R deg D oSpec).verifier] :
    (oracleReduction R n deg D oSpec i).perfectCompleteness init impl
      (relationRound R n deg D i.castSucc) (relationRound R n deg D i.succ) :=
  oracleReduction_perfectCompleteness (R := R) (n := n) (deg := deg) (D := D)
    (oSpec := oSpec) i

end SingleRound

variable {R : Type} [CommSemiring R] [SampleableType R] [DecidableEq R] [Fintype R] [Inhabited R]
  {n : ℕ} {deg : ℕ} {m : ℕ} {D : Fin m ↪ R}
  {ι : Type} {oSpec : OracleSpec ι} [∀ q, Fintype (oSpec.Range q)] [∀ q, Inhabited (oSpec.Range q)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

-- The `@`-applied keystone elaborates a large dependent `seqCompose` `toReduction` bridge through
-- the `change`/`rw`, so we raise the heartbeat limit.
set_option maxHeartbeats 1000000 in
set_option linter.unusedFintypeInType false in
/-- Completed n-ary oracle completeness assembled from the canonical round theorem. The
historical coherence family is retained for existing callers. -/
theorem oracleReduction_perfectCompleteness
    [coh : ∀ i, OracleVerifier.LiftContextCoherent (SingleRound.sumcheckOracleLens R n deg D oSpec i)
      (SingleRound.Simple.oracleReduction R deg D oSpec).verifier]
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β)) :
    (oracleReduction R deg D n oSpec).perfectCompleteness init impl
      (relationRound R n deg D 0) (relationRound R n deg D (Fin.last n)) := by
  exact OracleReduction.seqCompose_pc_oracle_msg'
    (init := init) (impl := impl)
    (StatementRound R n) (fun _ => OracleStatement R n deg) (fun _ => Unit)
    (SingleRound.oracleReduction R n deg D oSpec)
    (fun i => relationRound R n deg D i)
    (fun _ => inferInstance) (fun _ => SingleRound.chalFintype)
    (fun _ => SingleRound.chalInhab)
    (fun _ => ⟨by omega, SingleRound.pSpec_dir_zero⟩)
    hInit hImplSupp
    (fun i => SingleRound.oracleReduction_perfectCompleteness_of_liftContextCoherent
      (_coh := coh i) i)

end Sumcheck.Spec

#print axioms Sumcheck.Spec.SingleRound.oracleReduction_perfectCompleteness_of_liftContextCoherent
#print axioms Sumcheck.Spec.oracleReduction_perfectCompleteness
