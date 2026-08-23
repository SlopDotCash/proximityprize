/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.FiatShamir.Basic
import ArkLib.OracleReduction.LiftContext.Reduction

/-!
  # Discharging Basic Fiat-Shamir Completeness (#116)

  This file discharges the basic (non-duplex-sponge) Fiat-Shamir completeness residual
  `Reduction.fiatShamir_runCollapseResidual` left open in `FiatShamir/Basic.lean`, and uses the
  existing bridge `Reduction.fiatShamir_completeness_unroll_of_runCollapse` to prove
  `Reduction.fiatShamir_completeness_unroll` **unconditionally**.

  The core obstacle was a lift-coherence/oracle-spec-associativity wall: relating the transformed
  reduction's run `R.fiatShamir.run` (over `(oSpec + fsChallengeOracle) + [Challenge]ₒ`) to the
  explicit honest execution `R.fiatShamirHonestExecution` (over `oSpec + fsChallengeOracle`). We
  resolve it by proving the residual *directly at the `simulateQ` level*: unfold the prover-first run
  via `Reduction.run_of_prover_first`, reconcile the `OptionT`-level structure (pair projection and
  the verifier `getM`/`run` collapse), then push `simulateQ` through the binds and `Option.elim`,
  collapsing the empty (prover-only) `[FiatShamirProtocolSpec.Challenge]ₒ` oracle per piece via
  `simulateQ_addLift_liftM`.
-/

open ProtocolSpec OracleComp OracleSpec
open scoped NNReal

noncomputable section

namespace ArkLib.FiatShamir.CompletenessAux

variable {M : Type → Type} {α β : Type}

theorem liftM_eq_monadLift {m n : Type → Type} [MonadLiftT m n] (x : m α) :
    (liftM x : n α) = monadLift x := rfl

theorem optionT_lift_run_bind_getM [Monad M] [LawfulMonad M] (X : OptionT M α) :
    ((liftM X.run : OptionT M (Option α)) >>= fun o => (o.getM : OptionT M α)) = X := by
  apply OptionT.ext
  simp only [OptionT.run_bind, OptionT.run_monadLift, Option.elimM, bind_assoc,
    map_eq_pure_bind, pure_bind]
  conv_rhs => rw [← bind_pure X.run]
  congr 1
  funext o
  cases o <;> rfl

theorem optionT_lift_run_map_getM [Monad M] [LawfulMonad M]
    (X : OptionT M β) (f : β → α) :
    ((liftM X.run : OptionT M (Option β)) >>=
        fun o => f <$> (o.getM : OptionT M β)) =
      (f <$> X : OptionT M α) := by
  simp only [← bind_pure_comp, ← bind_assoc, optionT_lift_run_bind_getM]

variable {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}

theorem monadLift_optionT_lift_run_getM (X : OptionT (OracleComp spec₁) α) :
    ((monadLift (liftM X.run : OptionT (OracleComp spec₁) (Option α)) :
          OptionT (OracleComp (spec₁ + spec₂)) (Option α)) >>=
        fun o => (o.getM : OptionT (OracleComp (spec₁ + spec₂)) α)) =
      (monadLift X : OptionT (OracleComp (spec₁ + spec₂)) α) := by
  conv_rhs => rw [← optionT_lift_run_bind_getM X]
  rw [monadLift_bind]
  congr 1
  funext o
  cases o <;> rfl

theorem monadLift_optionT_lift_run_map_getM (X : OptionT (OracleComp spec₁) β) (f : β → α) :
    ((monadLift (liftM X.run : OptionT (OracleComp spec₁) (Option β)) :
          OptionT (OracleComp (spec₁ + spec₂)) (Option β)) >>=
        fun o => f <$> (o.getM : OptionT (OracleComp (spec₁ + spec₂)) β)) =
      (f <$> (monadLift X : OptionT (OracleComp (spec₁ + spec₂)) β) :
        OptionT (OracleComp (spec₁ + spec₂)) α) := by
  simp only [← bind_pure_comp, ← bind_assoc, monadLift_optionT_lift_run_getM]

theorem liftM_optionT_combined (m : OracleComp spec₁ α) :
    (liftM m : OptionT (OracleComp (spec₁ + spec₂)) α) =
      (monadLift (liftM m : OptionT (OracleComp spec₁) α) :
        OptionT (OracleComp (spec₁ + spec₂)) α) := rfl

@[simp] theorem optionT_monadLift_run (x : OptionT (OracleComp spec₁) α) :
    ((monadLift x : OptionT (OracleComp (spec₁ + spec₂)) α)).run = monadLift x.run := rfl

theorem simulateQ_map_monadLift_getM_run {σ' : Type}
    (impl : QueryImpl (spec₁ + spec₂) (StateT σ' ProbComp)) (o : Option α) (f : α → β) :
    simulateQ impl
      ((f <$> (monadLift (o.getM : OptionT (OracleComp spec₁) α) :
          OptionT (OracleComp (spec₁ + spec₂)) α)).run) = pure (Option.map f o) := by
  have h : ((f <$> (monadLift (o.getM : OptionT (OracleComp spec₁) α) :
      OptionT (OracleComp (spec₁ + spec₂)) α)).run) = pure (Option.map f o) := by
    cases o <;> rfl
  rw [h, simulateQ_pure]

theorem optionT_run_simulateQ_liftquery (X : OptionT (OracleComp spec₁) α) :
    OptionT.run (simulateQ (fun t => (monadLift (OracleSpec.query t) :
        OracleComp (spec₁ + spec₂) _)) X) =
      (monadLift X.run : OracleComp (spec₁ + spec₂) (Option α)) := rfl

#print axioms liftM_eq_monadLift
#print axioms optionT_lift_run_bind_getM
#print axioms optionT_lift_run_map_getM
#print axioms monadLift_optionT_lift_run_getM
#print axioms monadLift_optionT_lift_run_map_getM
#print axioms liftM_optionT_combined
#print axioms optionT_monadLift_run
#print axioms simulateQ_map_monadLift_getM_run
#print axioms optionT_run_simulateQ_liftquery

end ArkLib.FiatShamir.CompletenessAux

open ArkLib.FiatShamir.CompletenessAux

variable {n : ℕ}
variable {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [∀ i, SampleableType (pSpec.Challenge i)]

namespace Reduction

attribute [local instance] Reduction.fiatShamirProverOnly
attribute [local instance] Reduction.fiatShamirChallengeOracleInterface

/-- The basic Fiat-Shamir protocol spec has no challenge rounds (it is prover-only), so its challenge
oracle is empty; this provides the (vacuous) sampleability instance. -/
local instance (priority := 10) fiatShamirSampleable :
    ∀ i : (FiatShamirProtocolSpec (pSpec := pSpec)).ChallengeIdx,
      SampleableType ((FiatShamirProtocolSpec (pSpec := pSpec)).Challenge i) := by
  intro i
  rcases i with ⟨i, hi⟩
  exact False.elim (by
    rcases i with ⟨k, hk⟩
    have hk0 : k = 0 := by omega
    subst k
    simp at hi)

set_option maxHeartbeats 1000000 in
-- The two-stage `simp` normalization over the unrolled `OptionT`/`simulateQ` execution is large
-- (many lift/`getM`/`Option.elim` rewrites), so the default heartbeat budget is raised.
/-- **The basic Fiat-Shamir run-collapse residual holds.** Interpreting the transformed reduction's
run against the appended (prover-only, hence empty) Fiat-Shamir challenge oracle equals interpreting
the explicit honest execution. This discharges `Reduction.fiatShamir_runCollapseResidual`. -/
theorem fiatShamir_runCollapse
    {σ : Type}
    (impl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn) :
    Reduction.fiatShamir_runCollapseResidual impl R stmtIn witIn := by
  unfold Reduction.fiatShamir_runCollapseResidual
  rw [Reduction.run_of_prover_first]
  unfold Reduction.fiatShamirHonestExecution
  -- Stage 1: reconcile OptionT-level structure (pair projection, verifier collapse).
  simp only [Reduction.fiatShamir, Prover.fiatShamir, Verifier.fiatShamir, Verifier.run,
    liftComp_eq_liftM, bind_assoc, pure_bind, monadLift_bind, monadLift_pure, map_bind,
    bind_pure_comp, liftM_map, liftM_optionT_combined, bind_map_left,
    monadLift_optionT_lift_run_map_getM]
  -- Stage 2: push `.run`, distribute `simulateQ` through binds and `Option.elim`, collapse the
  -- empty appended challenge oracle per piece.
  simp only [QueryImpl.addLift_def, QueryImpl.liftTarget_self, liftM_eq_monadLift,
    OptionT.run_bind, OptionT.run_monadLift, OptionT.run_mk, optionT_monadLift_run,
    simulateQ_bind, simulateQ_map, simulateQ_pure, simulateQ_addLift_liftM,
    OptionT.simulateQ_addLift_liftM, Option.getM_map_run, Option.elimM,
    simulateQ_option_elim, bind_assoc, pure_bind, map_bind,
    simulateQ_getM_run_some, OptionT.simulateQ_getM_some, StateT.run_simulateQ_optiont_map,
    StateT.run_pure_some_bind_map, Option.map_comp_lambda, simulateQ_map_monadLift_getM_run,
    optionT_run_simulateQ_liftquery, OptionT.run_monadLift]
  simp [simulateQ_bind, simulateQ_map, simulateQ_pure, simulateQ_addLift_liftM,
    OptionT.simulateQ_addLift_liftM, simulateQ_option_elim, simulateQ_getM_run_some,
    OptionT.simulateQ_getM_some, StateT.run_simulateQ_optiont_map, StateT.run_pure_some_bind_map,
    Option.getM_map_run, Option.map_comp_lambda, optionT_monadLift_run, liftM_eq_monadLift,
    OptionT.run_bind, OptionT.run_monadLift, OptionT.run_mk, monadLift_bind, monadLift_pure,
    Option.elimM, bind_assoc, pure_bind, map_bind]
  rfl

/-- **Completeness of the basic Fiat-Shamir transform is unconditionally equivalent to its explicit
honest execution.** This discharges `Reduction.fiatShamir_completeness_unroll` (issue #116,
completeness leg) by feeding the now-proven `fiatShamir_runCollapse` into the bridge
`Reduction.fiatShamir_completeness_unroll_of_runCollapse`. -/
theorem fiatShamir_completeness_unroll_discharged
    {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (completenessError : ℝ≥0)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) :
    Reduction.fiatShamir_completeness_unroll init impl relIn relOut completenessError R :=
  Reduction.fiatShamir_completeness_unroll_of_runCollapse init impl relIn relOut completenessError R
    (fun stmtIn witIn => fiatShamir_runCollapse impl R stmtIn witIn)

/-- Basic Fiat-Shamir completeness follows from completeness of the explicit honest execution,
without requiring callers to pass the already-proved run-collapse residual. -/
theorem fiatShamir_completeness_of_honestExecution_discharged
    {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (completenessError : ℝ≥0)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hHonest : Reduction.completenessFromRun init impl relIn relOut
      R.fiatShamirHonestExecution completenessError) :
    R.fiatShamir.completeness init impl relIn relOut completenessError :=
  (fiatShamir_completeness_unroll_discharged init impl relIn relOut completenessError R).2
    hHonest

/-- Transformed basic Fiat-Shamir completeness projects back to completeness of the explicit honest
execution, without requiring callers to pass the already-proved run-collapse residual. -/
theorem fiatShamir_honestExecution_completeness_of_completeness_discharged
    {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (completenessError : ℝ≥0)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hFS : R.fiatShamir.completeness init impl relIn relOut completenessError) :
    Reduction.completenessFromRun init impl relIn relOut
      R.fiatShamirHonestExecution completenessError :=
  (fiatShamir_completeness_unroll_discharged init impl relIn relOut completenessError R).1 hFS

/-- Perfect completeness of the basic Fiat-Shamir transform is unconditionally equivalent to perfect
completeness of its explicit honest execution. -/
theorem fiatShamir_perfectCompleteness_unroll_discharged
    {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) :
    Reduction.fiatShamir_perfectCompleteness_unroll init impl relIn relOut R :=
  Reduction.fiatShamir_perfectCompleteness_unroll_of_runCollapse init impl relIn relOut R
    (fun stmtIn witIn => fiatShamir_runCollapse impl R stmtIn witIn)

/-- Basic Fiat-Shamir perfect completeness follows from perfect completeness of the explicit honest
execution, using the discharged run-collapse theorem. -/
theorem fiatShamir_perfectCompleteness_of_honestExecution_discharged
    {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hHonest : Reduction.perfectCompletenessFromRun init impl relIn relOut
      R.fiatShamirHonestExecution) :
    R.fiatShamir.perfectCompleteness init impl relIn relOut :=
  (fiatShamir_perfectCompleteness_unroll_discharged init impl relIn relOut R).2 hHonest

/-- Transformed basic Fiat-Shamir perfect completeness projects back to perfect completeness of the
explicit honest execution, using the discharged run-collapse theorem. -/
theorem fiatShamir_honestExecution_perfectCompleteness_of_perfectCompleteness_discharged
    {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hFS : R.fiatShamir.perfectCompleteness init impl relIn relOut) :
    Reduction.perfectCompletenessFromRun init impl relIn relOut
      R.fiatShamirHonestExecution :=
  (fiatShamir_perfectCompleteness_unroll_discharged init impl relIn relOut R).1 hFS

/-- Basic Fiat-Shamir completeness at any target error follows from perfect completeness of the
explicit honest execution, using the discharged run-collapse theorem. -/
theorem fiatShamir_completeness_of_perfect_honestExecution_discharged
    {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (completenessError : ℝ≥0)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hHonest : Reduction.perfectCompletenessFromRun init impl relIn relOut
      R.fiatShamirHonestExecution) :
    R.fiatShamir.completeness init impl relIn relOut completenessError := by
  unfold Reduction.perfectCompletenessFromRun at hHonest
  exact Reduction.completeness_error_mono init impl (zero_le completenessError)
    (fiatShamir_completeness_of_honestExecution_discharged init impl relIn relOut
      0 R hHonest)

/-- Discharged error-monotone completeness consumer for basic Fiat-Shamir. -/
theorem fiatShamir_completeness_of_honestExecution_mono_error_discharged
    {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    {completenessError₁ completenessError₂ : ℝ≥0}
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hHonest : Reduction.completenessFromRun init impl relIn relOut
      R.fiatShamirHonestExecution completenessError₁)
    (hle : completenessError₁ ≤ completenessError₂) :
    R.fiatShamir.completeness init impl relIn relOut completenessError₂ :=
  Reduction.completeness_error_mono init impl hle
    (fiatShamir_completeness_of_honestExecution_discharged init impl relIn relOut
      completenessError₁ R hHonest)

/-- Discharged relation-transport completeness consumer for basic Fiat-Shamir. -/
theorem fiatShamir_completeness_of_honestExecution_mono_relations_discharged
    {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    {relIn relIn' : Set (StmtIn × WitIn)}
    {relOut relOut' : Set (StmtOut × WitOut)}
    (completenessError : ℝ≥0)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hHonest : Reduction.completenessFromRun init impl relIn relOut
      R.fiatShamirHonestExecution completenessError)
    (hIn : relIn' ⊆ relIn) (hOut : relOut ⊆ relOut') :
    R.fiatShamir.completeness init impl relIn' relOut' completenessError :=
  Reduction.completeness_relOut_mono init impl hOut <|
    Reduction.completeness_relIn_mono init impl hIn <|
      fiatShamir_completeness_of_honestExecution_discharged init impl relIn relOut
        completenessError R hHonest

/-- Discharged relation-and-error transport completeness consumer for basic Fiat-Shamir. -/
theorem fiatShamir_completeness_of_honestExecution_mono_relations_error_discharged
    {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    {relIn relIn' : Set (StmtIn × WitIn)}
    {relOut relOut' : Set (StmtOut × WitOut)}
    {completenessError₁ completenessError₂ : ℝ≥0}
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hHonest : Reduction.completenessFromRun init impl relIn relOut
      R.fiatShamirHonestExecution completenessError₁)
    (hIn : relIn' ⊆ relIn) (hOut : relOut ⊆ relOut')
    (hle : completenessError₁ ≤ completenessError₂) :
    R.fiatShamir.completeness init impl relIn' relOut' completenessError₂ :=
  Reduction.completeness_error_mono init impl hle
    (fiatShamir_completeness_of_honestExecution_mono_relations_discharged init impl
      (relIn := relIn) (relIn' := relIn') (relOut := relOut) (relOut' := relOut')
      completenessError₁ R hHonest hIn hOut)

/-- Discharged relation-transport perfect-completeness consumer for basic Fiat-Shamir. -/
theorem fiatShamir_perfectCompleteness_of_honestExecution_mono_relations_discharged
    {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    {relIn relIn' : Set (StmtIn × WitIn)}
    {relOut relOut' : Set (StmtOut × WitOut)}
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hHonest : Reduction.perfectCompletenessFromRun init impl relIn relOut
      R.fiatShamirHonestExecution)
    (hIn : relIn' ⊆ relIn) (hOut : relOut ⊆ relOut') :
    R.fiatShamir.perfectCompleteness init impl relIn' relOut' := by
  unfold Reduction.perfectCompleteness Reduction.perfectCompletenessFromRun at *
  exact fiatShamir_completeness_of_honestExecution_mono_relations_discharged init impl
    (relIn := relIn) (relIn' := relIn') (relOut := relOut) (relOut' := relOut')
    0 R hHonest hIn hOut

/-- Discharged relation-and-error completeness consumer from perfect honest execution. -/
theorem fiatShamir_completeness_of_perfect_honestExecution_mono_relations_error_discharged
    {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT σ ProbComp))
    {relIn relIn' : Set (StmtIn × WitIn)}
    {relOut relOut' : Set (StmtOut × WitOut)}
    (completenessError : ℝ≥0)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hHonest : Reduction.perfectCompletenessFromRun init impl relIn relOut
      R.fiatShamirHonestExecution)
    (hIn : relIn' ⊆ relIn) (hOut : relOut ⊆ relOut') :
    R.fiatShamir.completeness init impl relIn' relOut' completenessError := by
  unfold Reduction.perfectCompletenessFromRun at hHonest
  exact fiatShamir_completeness_of_honestExecution_mono_relations_error_discharged init impl
    (relIn := relIn) (relIn' := relIn') (relOut := relOut) (relOut' := relOut')
    (completenessError₁ := 0) (completenessError₂ := completenessError)
    R hHonest hIn hOut (zero_le completenessError)

#print axioms fiatShamir_runCollapse
#print axioms fiatShamir_completeness_unroll_discharged
#print axioms fiatShamir_completeness_of_honestExecution_discharged
#print axioms fiatShamir_honestExecution_completeness_of_completeness_discharged
#print axioms fiatShamir_perfectCompleteness_unroll_discharged
#print axioms fiatShamir_perfectCompleteness_of_honestExecution_discharged
#print axioms fiatShamir_honestExecution_perfectCompleteness_of_perfectCompleteness_discharged
#print axioms fiatShamir_completeness_of_perfect_honestExecution_discharged
#print axioms fiatShamir_completeness_of_honestExecution_mono_error_discharged
#print axioms fiatShamir_completeness_of_honestExecution_mono_relations_discharged
#print axioms fiatShamir_completeness_of_honestExecution_mono_relations_error_discharged
#print axioms fiatShamir_perfectCompleteness_of_honestExecution_mono_relations_discharged
#print axioms fiatShamir_completeness_of_perfect_honestExecution_mono_relations_error_discharged

end Reduction

end
