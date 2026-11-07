/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Sumcheck.Spec.OracleCompletenessThreaded
import ArkLib.ProofSystem.Sumcheck.Spec.SingleRoundCohWired

/-! # Compatibility for multi-round oracle sum-check completeness

`Sumcheck.Spec.oracleReduction_perfectCompleteness` in `SingleRound.lean` proves perfect
completeness for the full oracle protocol. This wrapper keeps the initialization and support
parameters used by existing downstream calls. -/

open OracleComp OracleSpec ProtocolSpec
namespace Sumcheck.Spec
noncomputable section
variable {R : Type} [CommSemiring R] [DecidableEq R] [SampleableType R] [Fintype R] [Inhabited R]
  {n : ℕ} {deg : ℕ} {m : ℕ} {D : Fin m ↪ R} {ι : Type} {oSpec : OracleSpec ι} [∀ q, Fintype (oSpec.Range q)] [∀ q, Inhabited (oSpec.Range q)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- Oracle sum-check completeness with the historical data parameters. -/
theorem oracleReduction_perfectCompleteness_unconditional
    (_hInit : NeverFail init)
    (_hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β)) :
    (oracleReduction R deg D n oSpec).perfectCompleteness init impl
      (relationRound R n deg D 0) (relationRound R n deg D (Fin.last n)) :=
  Sumcheck.Spec.oracleReduction_perfectCompleteness R deg D n oSpec

end
end Sumcheck.Spec
