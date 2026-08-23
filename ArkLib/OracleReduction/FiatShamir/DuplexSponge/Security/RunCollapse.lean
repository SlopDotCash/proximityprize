/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Completeness
import ArkLib.OracleReduction.FiatShamir.BasicCompleteness

/-!
  # Discharging the Duplex-Sponge Fiat-Shamir Run-Collapse Residuals

  This file discharges the duplex-sponge Fiat-Shamir (DSFS) run-collapse residuals
  `Reduction.duplexSpongeFiatShamir_runCollapseResidual` and
  `Reduction.duplexSpongeFiatShamirSalted_runCollapseResidual` left open in
  `FiatShamir/DuplexSponge/Security/Completeness.lean`, and feeds them into the existing bridges
  `Reduction.duplexSpongeFiatShamir_completeness_unroll_of_runCollapse` (and the salted analogue)
  to obtain `Reduction.duplexSpongeFiatShamir_completeness_unroll` **unconditionally**.

  The proof mirrors the basic Fiat-Shamir run-collapse `Reduction.fiatShamir_runCollapse`
  (`FiatShamir/BasicCompleteness.lean`): the transformed reduction is prover-only (a single
  `P_to_V` message), so the appended `[Challenge]ₒ` oracle of the transformed run is vacuous. We
  unfold the run via `Reduction.run_of_prover_first`, reconcile the `OptionT`-level structure
  (the two-step associativity-routed lift chosen by `run` versus the direct lift consumed by the
  collapse lemmas) using the generic bridge toolkit `ArkLib.FiatShamir.CompletenessAux`, then push
  `simulateQ` through the binds, collapsing the empty appended challenge oracle per piece via
  `simulateQ_addLift_liftM`.
-/

open ProtocolSpec OracleComp OracleSpec ArkLib.FiatShamir.CompletenessAux
open scoped NNReal

noncomputable section

namespace Reduction

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [∀ i, SampleableType (pSpec.Challenge i)]
  {U : Type} [SpongeUnit U] [SpongeSize]
  [HasMessageSize pSpec] [∀ i, Serialize (pSpec.Message i) (Vector U (messageSize i))]
  [HasChallengeSize pSpec] [∀ i, Deserialize (pSpec.Challenge i) (Vector U (challengeSize i))]

attribute [local instance] Reduction.dsfsProverOnly Reduction.dsfsSaltedProverOnly

omit [∀ i, SampleableType (pSpec.Challenge i)] in
set_option maxHeartbeats 1000000 in
-- The two-stage `simp` normalization over the unrolled `OptionT`/`simulateQ` execution is large
-- (many lift/`getM`/`Option.elim` rewrites), so the default heartbeat budget is raised.
/-- **The unsalted DSFS run-collapse residual holds.** Interpreting the transformed reduction's
run against the appended (prover-only, hence empty) challenge oracle equals interpreting the
explicit honest execution. This discharges
`Reduction.duplexSpongeFiatShamir_runCollapseResidual`. -/
theorem duplexSpongeFiatShamir_runCollapse
    {σ : Type}
    (impl : QueryImpl (oSpec + duplexSpongeChallengeOracle StmtIn U) (StateT σ ProbComp))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn) :
    Reduction.duplexSpongeFiatShamir_runCollapseResidual (U := U) impl R stmtIn witIn := by
  unfold Reduction.duplexSpongeFiatShamir_runCollapseResidual
  rw [Reduction.run_of_prover_first]
  unfold Reduction.duplexSpongeFiatShamirHonestExecution
    Reduction.duplexSpongeFiatShamirHonestRun
  -- Stage 1: reconcile OptionT-level structure (pair projection, verifier collapse).
  simp only [Reduction.duplexSpongeFiatShamir, Prover.duplexSpongeFiatShamir, Verifier.run,
    liftComp_eq_liftM, bind_assoc, monadLift_bind,
    bind_pure_comp, liftM_map, liftM_optionT_combined, bind_map_left,
    monadLift_optionT_lift_run_map_getM]
  -- Stage 2: push `.run`, distribute `simulateQ` through binds and `Option.elim`, collapse the
  -- empty appended challenge oracle per piece.
  simp only [QueryImpl.addLift_def, QueryImpl.liftTarget_self, liftM_eq_monadLift,
    OptionT.run_bind, OptionT.run_map, OptionT.run_monadLift, OptionT.run_mk,
    optionT_monadLift_run,
    simulateQ_bind, simulateQ_map, simulateQ_pure, simulateQ_addLift_liftM,
    Option.elimM, simulateQ_option_elim]
  simp [simulateQ_bind, simulateQ_pure, simulateQ_option_elim, liftM_eq_monadLift,
    OptionT.run_bind, OptionT.run_mk,
    Option.elimM, bind_assoc, map_bind]
  rfl

omit [∀ i, SampleableType (pSpec.Challenge i)] in
set_option maxHeartbeats 1600000 in
-- The salted normalization repeats the unsalted two-stage `simp` with the extra salt-sampling
-- leg, so the heartbeat budget is raised further.
/-- **The salted DSFS run-collapse residual holds.** Salted analogue of
`Reduction.duplexSpongeFiatShamir_runCollapse`; the extra salt-sampling leg lifts through the
same `OptionT` bridge. This discharges
`Reduction.duplexSpongeFiatShamirSalted_runCollapseResidual`. -/
theorem duplexSpongeFiatShamirSalted_runCollapse {δ : Nat}
    {σ : Type}
    (impl : QueryImpl (oSpec + duplexSpongeChallengeOracle StmtIn U) (StateT σ ProbComp))
    (sampleSalt : OracleComp oSpec (Vector U δ))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn) :
    Reduction.duplexSpongeFiatShamirSalted_runCollapseResidual (U := U)
      impl sampleSalt R stmtIn witIn := by
  unfold Reduction.duplexSpongeFiatShamirSalted_runCollapseResidual
  rw [Reduction.run_of_prover_first]
  unfold Reduction.duplexSpongeFiatShamirSaltedHonestExecution
    Reduction.duplexSpongeFiatShamirSaltedHonestRun
  -- Stage 1: reconcile OptionT-level structure (pair projection, verifier collapse).
  simp only [Reduction.duplexSpongeFiatShamirSalted, Prover.duplexSpongeFiatShamirSalted,
    Verifier.run, liftComp_eq_liftM, bind_assoc, monadLift_bind,
    bind_pure_comp, liftM_map, liftM_optionT_combined, bind_map_left,
    monadLift_optionT_lift_run_map_getM]
  -- Stage 2: push `.run`, distribute `simulateQ` through binds and `Option.elim`, collapse the
  -- empty appended challenge oracle per piece.
  simp only [QueryImpl.addLift_def, QueryImpl.liftTarget_self, liftM_eq_monadLift,
    OptionT.run_bind, OptionT.run_map, OptionT.run_monadLift, OptionT.run_mk,
    optionT_monadLift_run,
    simulateQ_bind, simulateQ_map, simulateQ_pure, simulateQ_addLift_liftM,
    Option.elimM, simulateQ_option_elim]
  simp [simulateQ_bind, simulateQ_pure, simulateQ_option_elim, liftM_eq_monadLift,
    OptionT.run_bind, OptionT.run_mk,
    Option.elimM, bind_assoc, map_bind]
  rfl

/-- **Completeness of the unsalted DSFS transform is unconditionally equivalent to its explicit
honest execution.** Feeds the now-proven `duplexSpongeFiatShamir_runCollapse` into the bridge
`Reduction.duplexSpongeFiatShamir_completeness_unroll_of_runCollapse`. -/
theorem duplexSpongeFiatShamir_completeness_unroll_discharged
    {σ : Type}
    (init : ProbComp σ)
    (impl : QueryImpl (oSpec + duplexSpongeChallengeOracle StmtIn U) (StateT σ ProbComp))
    (relIn : Set (StmtIn × WitIn))
    (relOut : Set (StmtOut × WitOut))
    (completenessError : ℝ≥0)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) :
    duplexSpongeFiatShamir_completeness_unroll (U := U)
      init impl relIn relOut completenessError R :=
  duplexSpongeFiatShamir_completeness_unroll_of_runCollapse init impl relIn relOut
    completenessError R
    (fun stmtIn witIn => duplexSpongeFiatShamir_runCollapse impl R stmtIn witIn)

/-- **Completeness of the salted DSFS transform is unconditionally equivalent to its explicit
honest execution.** Feeds the now-proven `duplexSpongeFiatShamirSalted_runCollapse` into the
bridge `Reduction.duplexSpongeFiatShamirSalted_completeness_unroll_of_runCollapse`. -/
theorem duplexSpongeFiatShamirSalted_completeness_unroll_discharged {δ : Nat}
    {σ : Type}
    (init : ProbComp σ)
    (impl : QueryImpl (oSpec + duplexSpongeChallengeOracle StmtIn U) (StateT σ ProbComp))
    (sampleSalt : OracleComp oSpec (Vector U δ))
    (relIn : Set (StmtIn × WitIn))
    (relOut : Set (StmtOut × WitOut))
    (completenessError : ℝ≥0)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) :
    duplexSpongeFiatShamirSalted_completeness_unroll (U := U)
      init impl sampleSalt relIn relOut completenessError R :=
  duplexSpongeFiatShamirSalted_completeness_unroll_of_runCollapse init impl sampleSalt relIn
    relOut completenessError R
    (fun stmtIn witIn => duplexSpongeFiatShamirSalted_runCollapse impl sampleSalt R stmtIn witIn)

#print axioms Reduction.duplexSpongeFiatShamir_runCollapse
#print axioms Reduction.duplexSpongeFiatShamirSalted_runCollapse
#print axioms Reduction.duplexSpongeFiatShamir_completeness_unroll_discharged
#print axioms Reduction.duplexSpongeFiatShamirSalted_completeness_unroll_discharged

end Reduction

end
