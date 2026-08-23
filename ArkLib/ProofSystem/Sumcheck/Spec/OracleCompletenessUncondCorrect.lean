/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Sumcheck.Spec.OracleCompletenessThreaded
import ArkLib.ProofSystem.Sumcheck.Spec.SingleRoundCohWired

/-! # Multi-round sum-check oracle perfect completeness — UNCONDITIONAL (issue #13)

`Sumcheck.Spec.oracleReduction_perfectCompleteness` (`OracleCompletenessThreaded.lean`) proves the
multi-round oracle-level perfect completeness via the genuine, bridge-FREE `seqCompose` threaded
keystone (no false `toReduction = reduction` equation), conditional only on the per-round
oracle-routing lens coherence `[coh : ∀ i, LiftContextCoherent (sumcheckOracleLens i) Simple.verifier]`
plus the standard data facts `hInit`/`hImplSupp`.

That `coh` is now a THEOREM: `coh_proven_inst` (`SingleRoundCohWired.lean`) supplies it from the
proven `CubeFiber` (`SingleRoundFaithful.coh_proven`). Feeding it discharges the last residual, so
the multi-round sum-check oracle perfect completeness is unconditional modulo only the honest data
facts. This is the correct replacement for the false-bridge `oracleReduction_perfectCompleteness_uncond`. -/

open OracleComp OracleSpec ProtocolSpec
namespace Sumcheck.Spec
noncomputable section
variable {R : Type} [CommSemiring R] [DecidableEq R] [SampleableType R] [Fintype R] [Inhabited R]
  {n : ℕ} {deg : ℕ} {m : ℕ} {D : Fin m ↪ R} {ι : Type} {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- **Multi-round sum-check ORACLE perfect completeness, UNCONDITIONAL.** The per-round lens
coherence `coh` of `oracleReduction_perfectCompleteness` is discharged by the proven `CubeFiber`
(`SingleRound.coh_proven_inst`). No verifier-fusion / `toReduction = reduction` bridge anywhere —
the completeness is assembled by the genuine `seqCompose` threaded keystone. -/
theorem oracleReduction_perfectCompleteness_unconditional
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β)) :
    (oracleReduction R deg D n oSpec).perfectCompleteness init impl
      (relationRound R n deg D 0) (relationRound R n deg D (Fin.last n)) :=
  oracleReduction_perfectCompleteness
    (coh := fun i => SingleRound.coh_proven_inst i) hInit hImplSupp

end
end Sumcheck.Spec
