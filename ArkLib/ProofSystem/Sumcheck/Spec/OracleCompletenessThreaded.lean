/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Sumcheck.Spec.Completeness
import ArkLib.Extensions.ProofSystem.Sumcheck.Spec.SingleRound

/-!
# Single-round sum-check completeness compatibility

The canonical round verifier checks the prover's message polynomial. Its completed perfect
completeness theorem discharges the lens conditions directly. The wrapper retains the
historical coherence parameter for callers that supply it.
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

end Sumcheck.Spec

#print axioms Sumcheck.Spec.SingleRound.oracleReduction_perfectCompleteness_of_liftContextCoherent
