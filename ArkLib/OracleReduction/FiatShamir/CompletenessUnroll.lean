/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.FiatShamir.Basic

/-!
# Fiat-Shamir completeness-unroll from the run-equality residual (issue #116)

fiatShamir_completeness_of_runEq derives R.fiatShamir.completeness from the single run-equality
residual (honest FS transcript = interactive honest transcript), routed through the in-tree-proven
associativity-aware run-collapse. Soundness/ZK legs remain gated on RO-programming infra.
-/

open ProtocolSpec OracleComp OracleSpec
open scoped BigOperators NNReal

namespace Issue116

noncomputable section

variable {n : ℕ}
variable {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type}

open Reduction

-- ===========================================================================================
-- (1) GENUINE STRUCTURAL LEMMA — run-equality ⇒ run-collapse.
--     Derived from the in-tree-proven
--     `Reduction.fiatShamir_runCollapseResidual_of_run_eq_honestExecution`.
-- ===========================================================================================

/-- The basic Fiat-Shamir run-collapse residual follows from the run-equality residual.

`R.fiatShamir.run` lives over the right-associated oracle sum
`oSpec + (fsChallengeOracle StmtIn pSpec + [FiatShamirProtocolSpec.Challenge]ₒ)`, where the outer
Fiat-Shamir challenge oracle is over an `IsEmpty` challenge index (the transformed spec is
prover-only) and is therefore never queried.  Given the run-equality residual, the combined
implementation `addLift impl challengeQueryImpl` interpreted over the re-associated lifted
computation discards the empty right summand.  The genuine collapse (through
`simulateQ_add_liftComp_add_assoc_left`) is the in-tree theorem
`fiatShamir_runCollapseResidual_of_run_eq_honestExecution`. -/
theorem fiatShamir_runCollapse_of_runEq
    (impl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn)
    (hRunEq : fiatShamir_run_eq_honestExecution R stmtIn witIn) :
    fiatShamir_runCollapseResidual impl R stmtIn witIn :=
  Reduction.fiatShamir_runCollapseResidual_of_run_eq_honestExecution impl R stmtIn witIn hRunEq

-- ===========================================================================================
-- (2) FULL COMPLETENESS-UNROLL FROM THE SINGLE RUN-EQUALITY RESIDUAL.
--     Composes (1) with the already-proven `fiatShamir_completeness_unroll_of_runCollapse`.
-- ===========================================================================================

/-- Completeness of the transformed one-message basic Fiat-Shamir reduction is equivalent to the
explicit honest-execution experiment, given only the per-input run-equality residual
`fiatShamir_run_eq_honestExecution`. -/
theorem fiatShamir_completeness_unroll_of_runEq
    (init : ProbComp σ)
    (impl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    (relIn : Set (StmtIn × WitIn))
    (relOut : Set (StmtOut × WitOut))
    (completenessError : ℝ≥0)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hRunEq : ∀ stmtIn witIn, fiatShamir_run_eq_honestExecution R stmtIn witIn) :
    fiatShamir_completeness_unroll init impl relIn relOut completenessError R :=
  Reduction.fiatShamir_completeness_unroll_of_runCollapse init impl relIn relOut completenessError R
    (fun stmtIn witIn => fiatShamir_runCollapse_of_runEq impl R stmtIn witIn (hRunEq stmtIn witIn))

/-- Forward direction packaged for downstream users: basic FS completeness from the run-equality
residual plus honest-execution completeness. -/
theorem fiatShamir_completeness_of_runEq
    (init : ProbComp σ)
    (impl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    (relIn : Set (StmtIn × WitIn))
    (relOut : Set (StmtOut × WitOut))
    (completenessError : ℝ≥0)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hRunEq : ∀ stmtIn witIn, fiatShamir_run_eq_honestExecution R stmtIn witIn)
    (hHonest : Reduction.completenessFromRun init impl relIn relOut
      (R.fiatShamirHonestExecution) completenessError) :
    R.fiatShamir.completeness init impl relIn relOut completenessError :=
  (fiatShamir_completeness_unroll_of_runEq init impl relIn relOut completenessError R hRunEq).2
    hHonest

#print axioms fiatShamir_runCollapse_of_runEq
#print axioms fiatShamir_completeness_unroll_of_runEq
#print axioms fiatShamir_completeness_of_runEq

end

end Issue116
