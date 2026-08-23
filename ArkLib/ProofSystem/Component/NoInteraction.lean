/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.Security.RoundByRound

/-!
  # A classification of all (oracle) reductions with no interaction between the prover and verifier

  This file contains the general form of all (oracle) reductions with no interaction between the
  prover and verifier. In this setting, there are many specializations, and we can use these to
  derive simpler conditions for completeness & soundness.
-/

open OracleComp OracleInterface ProtocolSpec Function NNReal ENNReal

namespace NoInteraction

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)]
  {WitIn : Type}
  {StmtOut : Type} {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type} [Oₛₒ : ∀ i, OracleInterface (OStmtOut i)]
  {WitOut : Type}

section Reduction

variable (mapStmt : StmtIn → OracleComp oSpec StmtOut)
  (mapWit : StmtIn → WitIn → OracleComp oSpec WitOut)

/-- Collect the functions `mapStmt` and `mapWit` into a single function `mapCtx` -/
@[reducible]
def combineMap : StmtIn × WitIn → OracleComp oSpec (StmtOut × WitOut) :=
  fun ⟨stmt, wit⟩ => do return (← mapStmt stmt, ← mapWit stmt wit)

/-- The prover in a no-interaction reduction can be specified by a tuple of functions:
- `mapStmt : StmtIn → OracleComp oSpec StmtOut` maps the input statement to an output statement
- `mapWit : StmtIn → WitIn → OracleComp oSpec WitOut` maps the input witness to an output witness,
  depending on the input statement
-/
@[reducible]
def prover : Prover oSpec StmtIn WitIn StmtOut WitOut !p[] where
  PrvState | 0 => StmtIn × WitIn
  input := id
  sendMessage := fun i => nomatch i
  receiveChallenge := fun i => nomatch i
  output := combineMap mapStmt mapWit

/-- The verifier in a no-interaction reduction takes an empty transcript, and hence reduce to a
  function `mapStmt : StmtIn → OracleComp oSpec StmtOut` -/
@[reducible]
def verifier : Verifier oSpec StmtIn StmtOut !p[] where
  verify := fun stmt _ => mapStmt stmt

/-- The no-interaction reduction can be specified by a tuple of functions:
- `mapStmt : StmtIn → OracleComp oSpec StmtOut` maps the input statement to an output statement
- `mapWit : StmtIn → WitIn → OracleComp oSpec WitOut` maps the input witness to an output witness,
  depending on the input statement
-/
@[reducible]
def reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut !p[] where
  prover := prover mapStmt mapWit
  verifier := verifier mapStmt

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}

/-- A `some`-valued `ProbComp` under `OptionT.mk` is `OptionT.lift` of the underlying computation:
  the no-interaction run never fails (the prover and verifier only `liftM` total `OracleComp oSpec`
  maps, never `failure`), so its `Reduction.run` distribution is the `OptionT.lift` of a plain
  `ProbComp`. Used to peel the `OptionT` wrapper in `reduction_completeness`. -/
private theorem optionT_mk_some_map_eq_lift {α : Type} (x : ProbComp α) :
    (OptionT.mk (some <$> x) : OptionT ProbComp α) = OptionT.lift x := by
  rw [OptionT.lift, bind_pure_comp]

/-- Completeness of a no-interaction reduction.

  **Faithfulness of the hypothesis `hRel`.** `Reduction.run` (`Execution.lean`) runs the prover
  and the verifier as two *independent* sub-computations: the prover evaluates
  `combineMap mapStmt mapWit` (one call each to `mapStmt` and `mapWit`), while the verifier
  *separately* evaluates `mapStmt` again on the same input statement. The completeness event
  (`Reduction.completeness`, `Security/Basic.lean`) then demands not only
  `(stmtOut, witOut) ∈ relOut` but also that the prover's and the verifier's output statements
  *agree* (`prvStmtOut = stmtOut`).
  When `mapStmt` is randomized (queries `oSpec`), the two independent evaluations may disagree, so a
  hypothesis about a *single* evaluation of `combineMap` is too weak to imply completeness — it
  cannot constrain the verifier's separate `mapStmt` call. Accordingly `hRel` is stated over the
  *genuine* run distribution: the prover's `combineMap`, the verifier's separate `mapStmt`, and the
  success event including the agreement constraint, all threaded through the *same* state via
  `simulateQ impl`. There is no challenge oracle to lift (the protocol `!p[]` has no rounds), so
  this is the faithful image of `Reduction.run` for the no-interaction reduction. -/
theorem reduction_completeness {ε : ℝ≥0} [DecidablePred (· ∈ relOut)]
    [DecidableEq StmtOut]
    (hRel : ∀ stmtIn witIn, (stmtIn, witIn) ∈ relIn →
      Pr[fun ⟨⟨pStmtOut, witOut⟩, vStmtOut⟩ =>
          (vStmtOut, witOut) ∈ relOut ∧ pStmtOut = vStmtOut | do
        (simulateQ impl <| do
            let ctxOut ← combineMap mapStmt mapWit ⟨stmtIn, witIn⟩
            let vStmtOut ← mapStmt stmtIn
            pure (ctxOut, vStmtOut)).run' (← init)] ≥ 1 - ε) :
    Reduction.completeness init impl relIn relOut (reduction mapStmt mapWit) ε := by
  simp only [Reduction.completeness, Reduction.run, Verifier.run, prover, Prover.run,
    Prover.runToRound_zero_of_prover_first, Fin.last, Fin.zero_eta, id_eq, QueryImpl.addLift_def]
  intro stmtIn witIn hStmtIn
  refine ge_trans (le_of_eq ?_) (hRel stmtIn witIn hStmtIn)
  simp only [combineMap, OptionT.run_bind,
    OptionT.run_monadLift, monadLift_eq_self,
    simulateQ_bind, simulateQ_map,
    ← liftComp_eq_liftM, OracleComp.liftComp_bind, OracleComp.liftComp_map,
    QueryImpl.simulateQ_add_liftComp_left, QueryImpl.liftTarget_self,
    Option.elimM, Option.elim, Option.getM,
    StateT.run'_eq, StateT.run_bind, StateT.run_map, liftM_map, OptionT.run_map,
    bind_pure_comp, map_bind, bind_assoc, map_pure, pure_bind,
    bind_map_left, Functor.map_map]
  conv_rhs =>
    pattern (OptionT.run (liftM _))
    change OracleComp.liftComp (some <$> mapStmt stmtIn) _
  conv_rhs =>
    pattern (simulateQ _ (OracleComp.liftComp _ _))
    rw [QueryImpl.simulateQ_add_liftComp_left, simulateQ_map]
  conv_rhs =>
    arg 1; arg 1
    simp only [StateT.run_map, map_bind, Functor.map_map, Function.comp, Option.map_some,
      bind_assoc, bind_pure_comp, map_pure]
    -- split the innermost `(some ∘ proj) <$> X` into `some <$> (proj <$> X)`
    enter [2, __do_lift]
    enter [2, a]
    enter [2, a_1]
    rw [← Functor.map_map]
  -- factor `some` outward, innermost bind first
  conv_rhs =>
    arg 1; arg 1
    enter [2, __do_lift]
    enter [2, a]
    rw [← map_bind]
  conv_rhs =>
    arg 1; arg 1
    enter [2, __do_lift]
    rw [← map_bind]
  conv_rhs =>
    arg 1; arg 1
    rw [← map_bind]
  rw [optionT_mk_some_map_eq_lift, OptionT.probEvent_lift]
  simp only [probEvent_bind_eq_tsum, probEvent_map, Function.comp_def]

end Reduction

section OracleReduction



end OracleReduction

end NoInteraction
