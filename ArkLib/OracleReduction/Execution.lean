/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.Basic
import ArkLib.Data.Fin.Basic
import ArkLib.ToVCVio.OracleComp.EvalDist

/-!
  # Execution Semantics of Interactive Oracle Reductions

  We define what it means to execute an interactive oracle reduction, and prove some basic
  properties.
-/

open OracleComp OracleSpec SubSpec ProtocolSpec

universe u v



section Execution

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)]
 {WitIn : Type}
  {StmtOut : Type} {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type} {WitOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n}

namespace Prover

/--
Prover's function for processing the next round, given the current result of the previous round, and
a function for getting the challenge.
-/
@[inline, specialize]
def processRound (j : Fin n)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (currentResult : OracleComp (oSpec + [pSpec.Challenge]ₒ)
      (pSpec.Transcript j.castSucc × prover.PrvState j.castSucc)) :
      OracleComp (oSpec + [pSpec.Challenge]ₒ)
        (pSpec.Transcript j.succ × prover.PrvState j.succ) := do
  let ⟨transcript, state⟩ ← currentResult
  match hDir : pSpec.dir j with
  | .V_to_P => do
    let challenge ← pSpec.getChallenge ⟨j, hDir⟩
    letI newState := (← prover.receiveChallenge ⟨j, hDir⟩ state) challenge
    return ⟨transcript.concat challenge, newState⟩
  | .P_to_V => do
    let ⟨msg, newState⟩ ← prover.sendMessage ⟨j, hDir⟩ state
    return ⟨transcript.concat msg, newState⟩

/-- Run the prover in an interactive reduction up to round index `i`, via first inputting the
  statement and witness, and then processing each round up to round `i`. Returns the transcript up
  to round `i`, and the prover's state after round `i`.
-/
@[inline, specialize]
def runToRound (i : Fin (n + 1))
    (stmt : StmtIn) (wit : WitIn) (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) :
      OracleComp (oSpec + [pSpec.Challenge]ₒ) (pSpec.Transcript i × prover.PrvState i) :=
  Fin.induction
    (pure ⟨default, prover.input (stmt, wit)⟩)
    (prover.processRound)
    i

/-- Run the prover in an interactive reduction up to round `i`, logging all the queries made by the
  prover. Returns the transcript up to that round, the prover's state after that round, and the
  log of the prover's oracle queries. This basically just wraps `runToRound` with a logging
  oracle.
-/
@[inline, specialize]
def runWithLogToRound (i : Fin (n + 1))
    (stmt : StmtIn) (wit : WitIn) (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) :
      OracleComp (oSpec + [pSpec.Challenge]ₒ)
        ((pSpec.Transcript i × prover.PrvState i) × QueryLog (oSpec + [pSpec.Challenge]ₒ)) :=
  WriterT.run (simulateQ loggingOracle (prover.runToRound i stmt wit))

private lemma fst_map_simulateQ_loggingOracle_run {ι : Type} {spec : OracleSpec ι} {α : Type}
    (oa : OracleComp spec α) :
    Prod.fst <$> WriterT.run (simulateQ loggingOracle oa) = oa := by
  exact loggingOracle.fst_map_run_simulateQ oa

@[simp]
lemma runWithLogToRound_discard_log_eq_runToRound (i : Fin (n + 1))
    (stmt : StmtIn) (wit : WitIn) (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) :
      Prod.fst <$> prover.runWithLogToRound i stmt wit =
        prover.runToRound i stmt wit := by
  simp [runWithLogToRound, runToRound]

/-- Run the prover in an interactive reduction. Returns the output statement and witness, and the
  transcript. See `runWithLog` for a version that additionally returns the log of the
  prover's oracle queries.
-/
@[inline, specialize]
def run (stmt : StmtIn) (wit : WitIn)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) :
      OracleComp (oSpec + [pSpec.Challenge]ₒ) (FullTranscript pSpec × StmtOut × WitOut) := do
  let ⟨transcript, state⟩ ← prover.runToRound (Fin.last n) stmt wit
  return ⟨transcript, ← prover.output state⟩

/-- Run the prover in an interactive reduction, logging all the queries made by the prover. Returns
  the transcript, the output statement and witness, and the log of the prover's oracle queries.

Note: this is just a wrapper around `run` that logs the queries made by the prover.
-/
@[inline, specialize]
def runWithLog (stmt : StmtIn) (wit : WitIn)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) :
      OracleComp (oSpec + [pSpec.Challenge]ₒ)
        ((FullTranscript pSpec × StmtOut × WitOut) × QueryLog (oSpec + [pSpec.Challenge]ₒ)) :=
  (simulateQ loggingOracle (prover.run stmt wit)).run

@[simp]
lemma runWithLog_discard_log_eq_run (stmt : StmtIn) (wit : WitIn)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) :
      Prod.fst <$> prover.runWithLog stmt wit = prover.run stmt wit := by
  simp [runWithLog]

end Prover

private lemma fst_map_liftComp_simulateQ_loggingOracle_run {ι τ : Type}
    {spec : OracleSpec ι} {superSpec : OracleSpec τ} {α : Type}
    [MonadLiftT (OracleQuery spec) (OracleQuery superSpec)]
    (oa : OracleComp spec α) :
    Prod.fst <$> (WriterT.run (simulateQ loggingOracle oa)).liftComp superSpec =
      oa.liftComp superSpec := by
  rw [← OracleComp.liftComp_map]
  exact congrArg (fun x => x.liftComp superSpec)
    (loggingOracle.fst_map_run_simulateQ oa)

/-- Run the (non-oracle) verifier in an interactive reduction. It takes in the input statement and
  the transcript, and return the output statement.
-/
@[inline, specialize, reducible]
def Verifier.run (stmt : StmtIn) (transcript : FullTranscript pSpec)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec) : OptionT (OracleComp oSpec) StmtOut :=
  verifier.verify stmt transcript

/-- Run the oracle verifier in the interactive protocol. Returns the verifier's output, including
    both the output statement and oracle statements, and the log of queries made by the verifier.
-/
@[inline, specialize]
def OracleVerifier.run [Oₘ : ∀ i, OracleInterface (pSpec.Message i)]
    (stmt : StmtIn) (oStmtIn : ∀ i, OStmtIn i) (transcript : FullTranscript pSpec)
    (verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec) :
      OptionT (OracleComp oSpec) (StmtOut × (∀ i, OStmtOut i)) := do
  let f := OracleInterface.simOracle2 oSpec oStmtIn transcript.messages
  let stmtOut ← simulateQ f (verifier.verify stmt transcript.challenges)
  let oStmtOut : ∀ i, OStmtOut i := fun i => match h : verifier.embed i with
    | .inl j => (verifier.hEq i ▸ h ▸ oStmtIn j : OStmtOut i)
    | .inr j => (verifier.hEq i ▸ h ▸ transcript.messages j : OStmtOut i)
  return ⟨stmtOut, oStmtOut⟩

/-- Running an oracle verifier then is equal to running its non-oracle counterpart -/
@[simp]
theorem OracleVerifier.run_eq_run_verifier [Oₘ : ∀ i, OracleInterface (pSpec.Message i)]
    {stmt : StmtIn} {oStmt : ∀ i, OStmtIn i} {transcript : FullTranscript pSpec}
    {verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec} :
      verifier.run stmt oStmt transcript =
        verifier.toVerifier.run ⟨stmt, oStmt⟩ transcript := by
  simp only [OracleVerifier.run, OracleVerifier.toVerifier, Verifier.run]
  rfl

/-- An execution of an interactive reduction on a given initial statement and witness. Consists of
  first running the prover, and then the verifier. Returns the full transcript, the output statement
  and witness from the prover, and the output statement from the verifier.

  See `Reduction.runWithLog` for a version that additionally returns the logs of the prover's and
  the verifier's oracle queries.
-/
@[inline, specialize]
def Reduction.run (stmt : StmtIn) (wit : WitIn)
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) :
      OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ))
        ((FullTranscript pSpec × StmtOut × WitOut) × StmtOut) := do
  -- `ctxOut` contains both the output statement and witness after running the prover
  let proverResult ← reduction.prover.run stmt wit
  let stmtOut ← liftM (reduction.verifier.run stmt proverResult.1).run
  return ⟨proverResult, ← stmtOut.getM⟩

/-- Run a reduction and return only the verifier's output statement, discarding the full transcript
  and prover witness. Useful when only the final verdict matters (e.g. for `Proof`s). -/
def Reduction.verdict (stmt : StmtIn) (wit : WitIn)
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) :
      OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ)) StmtOut := do
  let ⟨_, stmtOut⟩ ← reduction.run stmt wit
  return stmtOut

/-- Running `Reduction.verdict` is running the reduction and projecting the verdict. -/
lemma Reduction.verdict_run_eq_map_run
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn) :
    (reduction.verdict stmt wit).run =
      Option.map (fun result : (FullTranscript pSpec × StmtOut × WitOut) × StmtOut =>
        result.2) <$> (reduction.run stmt wit).run := by
  simp [Reduction.verdict, OptionT.run_map]

/-- Run a reduction on `L` instances (given by indexed statements and witnesses), and sequence the
  full successful run results. Returns `none` if any instance fails, otherwise returns a function
  from indices to the full run data. -/
def Reduction.allRuns {L : ℕ}
    (stmts : Fin L → StmtIn) (wits : Fin L → WitIn)
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) :
      OracleComp (oSpec + [pSpec.Challenge]ₒ)
        (Option (Fin L → ((FullTranscript pSpec × StmtOut × WitOut) × StmtOut))) := do
  let results ← (Vector.ofFn id).mapM fun i => (reduction.run (stmts i) (wits i)).run
  return (results.mapM id).map fun v => fun i => v[i]

/-- Run a reduction on `L` instances and project each successful full run result through `extract`.
  Returns `none` if any instance fails, otherwise returns the indexed extracted outputs. -/
def Reduction.allOutputs {L : ℕ} {α : Type}
    (extract : ((FullTranscript pSpec × StmtOut × WitOut) × StmtOut) → α)
    (stmts : Fin L → StmtIn) (wits : Fin L → WitIn)
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) :
      OracleComp (oSpec + [pSpec.Challenge]ₒ) (Option (Fin L → α)) := do
  let results ← reduction.allRuns stmts wits
  return results.map fun resultOf => fun i => extract (resultOf i)

/-- Run a reduction on `L` instances (given by indexed statements and witnesses), and sequence the
  results. Returns `none` if any instance fails, otherwise returns a function from indices to
  the verifier's output statements. -/
def Reduction.allVerdicts {L : ℕ}
    (stmts : Fin L → StmtIn) (wits : Fin L → WitIn)
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) :
      OracleComp (oSpec + [pSpec.Challenge]ₒ) (Option (Fin L → StmtOut)) := do
  let results ← (Vector.ofFn id).mapM fun i => (reduction.verdict (stmts i) (wits i)).run
  return (results.mapM id).map fun v => fun i => v[i]

/-- `allVerdicts` has the same distribution as `allOutputs` with a projection retaining the
  verifier output as the first component; it differs only by a pure post-map. -/
lemma Reduction.allVerdicts_eq_map_allOutputs_fst {L : ℕ} {β : Type}
    (extract : ((FullTranscript pSpec × StmtOut × WitOut) × StmtOut) → β)
    (stmts : Fin L → StmtIn) (wits : Fin L → WitIn)
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) :
    reduction.allVerdicts stmts wits =
      (Option.map (fun resultOf => fun i => (resultOf i).1)) <$>
        reduction.allOutputs (fun result => (result.2, extract result)) stmts wits := by
  unfold Reduction.allVerdicts Reduction.allOutputs Reduction.allRuns
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
  rw [Vector.mapM_bind_map_eq
    (v := Vector.ofFn (id : Fin L → Fin L))
    (f₁ := fun i => (reduction.verdict (stmts i) (wits i)).run)
    (f₂ := fun i => (reduction.run (stmts i) (wits i)).run)
    (g := Option.map (fun result : (FullTranscript pSpec × StmtOut × WitOut) × StmtOut =>
      result.2))
    (post₁ := fun results =>
      pure ((results.mapM id).map fun v => fun i => v[i]))
    (post₂ := fun results =>
      pure (Option.map (fun resultOf => fun i => (resultOf i).1)
        (Option.map (fun resultOf => fun i => ((resultOf i).2, extract (resultOf i)))
          (Option.map (fun v => fun i => v[i]) (results.mapM id)))))]
  · intro i
    exact Reduction.verdict_run_eq_map_run reduction (stmts i) (wits i)
  · intro results
    congr 1
    rw [Vector.mapM_id_option_map_comm]
    cases h : results.mapM id with
    | none => simp
    | some v =>
        simp only [Option.map_some, Option.some.injEq]
        funext i
        simp

lemma Reduction.support_allOutputs_index
    {StmtIn WitIn StmtOut WitOut α : Type} {n : ℕ} {pSpec : ProtocolSpec n} {L : ℕ}
    (extract : ((FullTranscript pSpec × StmtOut × WitOut) × StmtOut) → α)
    (stmts : Fin L → StmtIn) (wits : Fin L → WitIn)
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    {y : Option (Fin L → α)}
    (hy : y ∈ support (reduction.allOutputs extract stmts wits))
    {resultOf : Fin L → α} (hy_eq : y = some resultOf) (i : Fin L) :
      ∃ result, some result ∈ support (reduction.run (stmts i) (wits i)).run ∧
        extract result = resultOf i := by
  unfold Reduction.allOutputs at hy
  rw [mem_support_bind_iff] at hy
  obtain ⟨runsOpt, hrunsOpt, hy_mem⟩ := hy
  rw [mem_support_pure_iff] at hy_mem
  rw [hy_eq] at hy_mem
  cases hruns : runsOpt with
  | none => simp [hruns] at hy_mem
  | some runOf =>
      simp only [hruns, Option.map_some, Option.some.injEq] at hy_mem
      unfold Reduction.allRuns at hrunsOpt
      rw [mem_support_bind_iff] at hrunsOpt
      obtain ⟨results, hresults, hrunsOpt⟩ := hrunsOpt
      rw [mem_support_pure_iff] at hrunsOpt
      cases hseq : results.mapM id with
      | none => simp [hseq, hruns] at hrunsOpt
      | some results' =>
          simp only [hseq, Option.map_some] at hrunsOpt
          rw [hruns] at hrunsOpt
          simp only [Option.some.injEq] at hrunsOpt
          have hidx : results[i] = some results'[i] :=
            Vector.mapM_id_some_index hseq i
          refine ⟨results'[i], ?_, ?_⟩
          · simpa [hidx] using
              OracleComp.support_ofFn_mapM_index
                (fun i => (reduction.run (stmts i) (wits i)).run) hresults i
          · have hrunOf_i := congrFun hrunsOpt i
            have hresult_i := congrFun hy_mem i
            rw [hresult_i, hrunOf_i]

/-- If a reduction's verifier is a pure function `f` of the input statement and full transcript,
    then the verifier output of any complete result in the support of `Reduction.run` equals
    `f stmt td` applied to the input statement and the produced transcript. -/
lemma Reduction.support_run_pure_verifier
    {StmtIn WitIn StmtOut WitOut : Type}
    {n : ℕ} {pSpec : ProtocolSpec n}
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (f : StmtIn → FullTranscript pSpec → StmtOut)
    (hf : ∀ stmt td,
      reduction.verifier.verify stmt td =
        (pure (f stmt td) : OptionT (OracleComp oSpec) StmtOut))
    (stmt : StmtIn) (wit : WitIn)
    {y : Option ((FullTranscript pSpec × StmtOut × WitOut) × StmtOut)}
    (hy : y ∈ support (reduction.run stmt wit).run)
    {td : FullTranscript pSpec} {prv : StmtOut × WitOut} {vOut : StmtOut}
    (heq : y = some ((td, prv), vOut)) : vOut = f stmt td := by
  rw [heq] at hy
  unfold Reduction.run at hy
  simp only [OptionT.run_bind, Option.elimM] at hy
  rw [mem_support_bind_iff] at hy
  obtain ⟨proverResultOpt, _hprover, hy⟩ := hy
  cases proverResultOpt with
  | none =>
      exfalso
      simp at hy
  | some proverResult =>
      simp only [Option.elim_some] at hy
      rw [mem_support_bind_iff] at hy
      obtain ⟨stmtOutOpt, hstmtOutOpt, hy⟩ := hy
      simp only [ChallengeIdx, Challenge, Verifier.run, hf, OptionT.run_pure, liftM_pure,
        support_pure, Set.mem_singleton_iff] at hstmtOutOpt
      subst stmtOutOpt
      simp only [Option.elim_some, Option.getM_some, OptionT.run_pure] at hy
      injection hy with hpair
      have htd : td = proverResult.1 := congrArg Prod.fst (congrArg Prod.fst hpair)
      have hvOut : vOut = f stmt proverResult.1 := congrArg Prod.snd hpair
      rw [htd]
      exact hvOut

/-- An execution of an interactive reduction on a given initial statement and witness. Consists of
  first running the prover, and then the verifier. Returns the full transcript, the output statement
  and witness from the prover, and the output statement from the verifier, along with the logs of
  the prover's and the verifier's oracle queries.
-/
@[inline, specialize]
def Reduction.runWithLog (stmt : StmtIn) (wit : WitIn)
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) :
      OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ))
        (((FullTranscript pSpec × StmtOut × WitOut) × StmtOut) ×
          QueryLog (oSpec + [pSpec.Challenge]ₒ) × QueryLog oSpec) := do
  -- `ctxOut` contains both the output statement and witness after running the prover
  let ⟨proverResult, proveQueryLog⟩ ← reduction.prover.runWithLog stmt wit
  let ⟨stmtOut, verifyQueryLog⟩ ←
    liftM (simulateQ loggingOracle (reduction.verifier.run stmt proverResult.1)).run
  return ⟨⟨proverResult, ← stmtOut.getM⟩, proveQueryLog, verifyQueryLog⟩

/-- Note: figure out a better name for this -/
private lemma Monad.map_of_prod_fst_eq_prod_fst {m : Type u → Type v} [Monad m] [LawfulMonad m]
    {α β γ : Type u} (ma : m (α × β)) (c : γ) :
    (fun a => (c, a.1)) <$> ma = Prod.mk c <$> Prod.fst <$> ma := by
  simp only [Functor.map_map]

/-- In OptionT, lifting a pair-valued computation and projecting the first component
in the continuation equals lifting the map and binding directly. -/
private lemma OptionT_liftM_bind_fst {m : Type → Type} [Monad m] [LawfulMonad m]
    {α β γ : Type} (x : m (α × β)) (f : α → OptionT m γ) :
    ((liftM x : OptionT m _) >>= fun p => f p.1) =
    (liftM (Prod.fst <$> x) : OptionT m _) >>= f := by
  rw [← bind_map_left]
  show (Prod.fst <$> monadLift x) >>= f = monadLift (Prod.fst <$> x) >>= f
  congr 1
  simp [liftM, MonadLift.monadLift, OptionT.lift, OptionT.mk,
    Functor.map_map, Function.comp]

/-- Logging the queries made by both parties do not change the output of the reduction -/
@[simp]
theorem Reduction.runWithLog_discard_logs_eq_run
    {stmt : StmtIn} {wit : WitIn}
    {reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec} :
      Prod.fst <$>
        reduction.runWithLog stmt wit = reduction.run stmt wit := by
  simp only [Reduction.runWithLog, Reduction.run, map_bind, map_pure, Functor.map_map,
    Function.comp]
  have h1 := OptionT_liftM_bind_fst (m := OracleComp (oSpec + [pSpec.Challenge]ₒ))
    (Prover.runWithLog stmt wit reduction.prover)
    (fun proverResult =>
      liftM (simulateQ loggingOracle (Verifier.run stmt proverResult.1 reduction.verifier)).run
        >>= fun a_1 => (fun a_2 => (proverResult, a_2)) <$> a_1.1.getM)
  -- Prover logging elimination: use OptionT_liftM_bind_fst + Prover.runWithLog_discard_log_eq_run
  exact h1 ▸ by
    rw [Prover.runWithLog_discard_log_eq_run]
    congr 1; ext proverResult
    -- Verifier logging elimination by induction on the verifier computation
    generalize Verifier.run stmt proverResult.1 reduction.verifier = vc
    induction vc using OracleComp.induction with
    | pure a => simp [simulateQ_pure, WriterT.run_pure]; rfl
    | query_bind t oa ih =>
      simp only [run_simulateQ_loggingOracle_query_bind]
      simp [bind_map_left, ih, OptionT.run_bind, Option.elimM, bind_assoc, OptionT.run_map]
      -- Remaining: OptionT.run distributing through liftM + bind on RHS
      -- The RHS has OptionT.run (liftM (query t) >>= oa) which should equal
      -- query t >>= fun u => OptionT.run (oa u). This is monadLift_bind for OptionT SubSpec.
      rfl
  -- calc
  -- _ = (do
  --   let a ← (simulateQ loggingOracle proverRun).run
  --   (fun aFst : (pSpec.FullTranscript × StmtOut × WitOut) => (fun b => (aFst, Prod.fst b)) <$>
  --       (simulateQ loggingOracle (Verifier.run stmt aFst.1 reduction.verifier)).run.liftComp
  --         (oSpec + [pSpec.Challenge]ₒ)) a.1) := rfl
  -- _ = _ := by
    -- rw [loggingOracle.simulateQ_bind_fst_comp proverRun
    --   (fun a => (fun b => (a, Prod.fst b)) <$>
    --     (simulateQ loggingOracle (Verifier.run stmt a.1 reduction.verifier)).run.liftComp
    --       (oSpec + [pSpec.Challenge]ₒ))]
    -- congr
    -- ext proverResult
    -- rw [← Functor.map_map]
    -- simp


/-- Run an interactive oracle reduction. Returns the full transcript, the output statement and
  witness, the log of all prover's oracle queries, and the log of all verifier's oracle queries to
  the prover's messages and to the shared oracle.
-/
@[inline, specialize]
def OracleReduction.run [∀ i, OracleInterface (pSpec.Message i)]
    (stmt : StmtIn) (oStmt : ∀ i, OStmtIn i) (wit : WitIn)
    (reduction : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec) :
      OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ))
        ((FullTranscript pSpec × (StmtOut × ∀ i, OStmtOut i) × WitOut) ×
          (StmtOut × ∀ i, OStmtOut i)) := do
  let proverResult ← reduction.prover.run ⟨stmt, oStmt⟩ wit
  let stmtOut ← liftM (reduction.verifier.run stmt oStmt proverResult.1).run
  return ⟨proverResult, ← stmtOut.getM⟩

/-- Run an interactive oracle reduction. Returns the full transcript, the output statement and
  witness, the log of all prover's oracle queries, and the log of all verifier's oracle queries to
  the prover's messages and to the shared oracle.
-/
@[inline, specialize]
def OracleReduction.runWithLog [∀ i, OracleInterface (pSpec.Message i)]
    (stmt : StmtIn) (oStmt : ∀ i, OStmtIn i) (wit : WitIn)
    (reduction : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec) :
      OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ))
        ((FullTranscript pSpec × (StmtOut × ∀ i, OStmtOut i) × WitOut) ×
          (StmtOut × ∀ i, OStmtOut i) ×
            QueryLog (oSpec + [pSpec.Challenge]ₒ) × QueryLog oSpec) := do
  let ⟨proverResult, proveQueryLog⟩ ←
    (simulateQ loggingOracle (reduction.prover.run ⟨stmt, oStmt⟩ wit)).run
  let ⟨stmtOut, verifyQueryLog⟩ ←
    liftM (simulateQ loggingOracle (reduction.verifier.run stmt oStmt proverResult.1)).run
  return ⟨proverResult, ← stmtOut.getM, proveQueryLog, verifyQueryLog⟩

/-- Running an oracle reduction is equal to running its non-oracle counterpart -/
@[simp]
theorem OracleReduction.run_eq_run_reduction [∀ i, OracleInterface (pSpec.Message i)]
    {stmt : StmtIn} {oStmt : ∀ i, OStmtIn i} {wit : WitIn}
    {oracleReduction : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec} :
      oracleReduction.run stmt oStmt wit =
        oracleReduction.toReduction.run ⟨stmt, oStmt⟩ wit := by
  simp only [OracleReduction.run, Reduction.run, OracleVerifier.run_eq_run_verifier,
    OracleReduction.toReduction]

/-- Running an oracle reduction with logging of queries to the shared oracle is equal to running its
  non-oracle counterpart with logging of queries to the shared oracle -/
@[simp]
theorem OracleReduction.runWithLog_eq_runWithLog_reduction [∀ i, OracleInterface (pSpec.Message i)]
    {stmt : StmtIn} {oStmt : ∀ i, OStmtIn i} {wit : WitIn}
    {oracleReduction : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec} :
      oracleReduction.run stmt oStmt wit =
        oracleReduction.toReduction.run ⟨stmt, oStmt⟩ wit := by
  simp only [OracleReduction.run, Reduction.run, OracleVerifier.run_eq_run_verifier,
    OracleReduction.toReduction]

@[simp]
theorem Prover.runToRound_zero_of_prover_first
    (stmt : StmtIn) (wit : WitIn) (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) :
      prover.runToRound 0 stmt wit = (pure (default, prover.input (stmt, wit))) := by
  simp [Prover.runToRound]

namespace Prover

/-! ### Prefix / round-range decomposition of `runToRound`

These additive lemmas relate the prover's full run to its per-round partial runs.  The keystone is
`runToRound_eq_bind_continueFromTo`: for any earlier round `k ≤ j`, the run up to round `j` factors
as the run up to `k` followed by a continuation `continueFromTo` that folds `processRound` over the
remaining rounds `k .. j-1`.  This is a plain `OracleComp` *equality* (the continuation only
`processRound`s further rounds), which is the structural connective consumed by both the
`rbrSoundness → soundness` probability bridge and the sequential-composition `append_run`
characterization. -/

/-- **Single-round unfolding of `runToRound`.**  Running the prover up to round `j.succ` is the same
  as running it up to round `j.castSucc` and then processing round `j`. -/
theorem runToRound_succ (j : Fin n)
    (stmt : StmtIn) (wit : WitIn) (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) :
    prover.runToRound j.succ stmt wit
      = prover.processRound j (prover.runToRound j.castSucc stmt wit) := by
  unfold runToRound
  rw [Fin.induction_succ]

/-- **`processRound` at a challenge (V_to_P) round.**  Specialization of `processRound` to a round
  `i` that is a challenge round (so `pSpec.dir i = .V_to_P`). -/
theorem processRound_challenge (i : pSpec.ChallengeIdx)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (currentResult : OracleComp (oSpec + [pSpec.Challenge]ₒ)
      (pSpec.Transcript i.1.castSucc × prover.PrvState i.1.castSucc)) :
    prover.processRound i.1 currentResult = (do
      let ⟨transcript, state⟩ ← currentResult
      let challenge ← pSpec.getChallenge i
      let newState := (← prover.receiveChallenge i state) challenge
      return ⟨transcript.concat challenge, newState⟩) := by
  unfold processRound
  obtain ⟨j, hj⟩ := i
  simp only
  congr 1
  funext x
  split <;> rename_i hDir
  · rfl
  · rw [hj] at hDir; exact absurd hDir (by decide)

/-- **Kleisli continuation folding `processRound` over rounds `k .. j-1`.**  Transforms a round-`k`
partial result `(transcript, state)` into the round-`j` partial run, by folding `processRound`.
Defined by `Fin.induction` on the *target* index `j`: when the running index reaches `k` exactly it
returns the supplied start `rk` (`pure`), and each subsequent `succ` step applies one more
`processRound`.  (The `j < k` branches are never used; for those the dependent-`Fin` base is filled
with the `runToRound 0` seed value, kept only to make the fold total.) -/
noncomputable def continueFromTo (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn) (k : Fin (n + 1)) :
    (j : Fin (n + 1)) →
      (pSpec.Transcript k × prover.PrvState k) →
        OracleComp (oSpec + [pSpec.Challenge]ₒ) (pSpec.Transcript j × prover.PrvState j) :=
  Fin.induction
    (motive := fun j => (pSpec.Transcript k × prover.PrvState k) →
        OracleComp (oSpec + [pSpec.Challenge]ₒ) (pSpec.Transcript j × prover.PrvState j))
    (fun rk => if h : (k : Fin (n + 1)) = 0 then h ▸ pure rk
               else pure (default, prover.input (stmt, wit)))
    (fun m prev rk =>
      if h : (k : Fin (n + 1)) = m.succ then h ▸ pure rk
      else prover.processRound m (prev rk))

/-- **`continueFromTo` step at a `succ` target that has not yet reached the start.**  When the target
`m.succ` is *strictly past* the start index `k` (`k ≠ m.succ`), the continuation applies one more
`processRound m` on top of the round-`m.castSucc` continuation. -/
theorem continueFromTo_succ_of_ne (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn) (k : Fin (n + 1)) (m : Fin n)
    (hne : (k : Fin (n + 1)) ≠ m.succ)
    (rk : pSpec.Transcript k × prover.PrvState k) :
    continueFromTo prover stmt wit k m.succ rk
      = prover.processRound m (continueFromTo prover stmt wit k m.castSucc rk) := by
  unfold continueFromTo
  rw [Fin.induction_succ]
  simp only [hne, ↓reduceDIte]

/-- **`continueFromTo` at the diagonal is the identity (`pure`).**  Continuing from round `k` to
round `k` returns the start result unchanged. -/
theorem continueFromTo_self (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn)
    (k : Fin (n + 1)) (rk : pSpec.Transcript k × prover.PrvState k) :
    continueFromTo prover stmt wit k k rk = pure rk := by
  unfold continueFromTo
  induction k using Fin.induction with
  | zero => simp [Fin.induction_zero]
  | succ m _ => simp [Fin.induction_succ]

/-- **`processRound` factors as a bind on its input.**  Since `processRound j cur` first runs `cur`
and then performs a round-`j` step depending only on `cur`'s output, it equals
`cur >>= (round-j step on a `pure`d result)`. -/
theorem processRound_eq_bind (j : Fin n) (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (cur : OracleComp (oSpec + [pSpec.Challenge]ₒ)
      (pSpec.Transcript j.castSucc × prover.PrvState j.castSucc)) :
    prover.processRound j cur = cur >>= (fun r => prover.processRound j (pure r)) := by
  unfold processRound
  simp only [pure_bind]

/-- **Round-range decomposition of `runToRound` (THE keystone).**  For any earlier round `k ≤ j`, the
prover run up to round `j` equals the run up to round `k` followed by the continuation
`continueFromTo` that folds `processRound` over rounds `k .. j-1`.  A plain `OracleComp` equality,
proved by `Fin.induction` on `j` (with `k` fixed) via `runToRound_succ`, `processRound_eq_bind`, and
monad associativity. -/
theorem runToRound_eq_bind_continueFromTo
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn) (k j : Fin (n + 1)) (hkj : k ≤ j) :
    prover.runToRound j stmt wit
      = prover.runToRound k stmt wit >>= continueFromTo prover stmt wit k j := by
  induction j using Fin.induction with
  | zero =>
    have hk0 : k = 0 := le_antisymm hkj (Fin.zero_le _)
    subst hk0
    conv_rhs => rw [show (continueFromTo prover stmt wit 0 0)
                      = (fun rk => pure rk) from funext (continueFromTo_self prover stmt wit 0)]
    rw [bind_pure]
  | succ m ih =>
    rcases eq_or_lt_of_le hkj with heq | hlt
    · subst heq
      conv_rhs => rw [show (continueFromTo prover stmt wit (m.succ) (m.succ))
                        = (fun rk => pure rk)
                          from funext (continueFromTo_self prover stmt wit _)]
      rw [bind_pure]
    · have hkm : k ≤ m.castSucc := by rw [Fin.le_castSucc_iff]; exact hlt
      have hne : (k : Fin (n + 1)) ≠ m.succ := ne_of_lt hlt
      rw [runToRound_succ, ih hkm]
      have hcont : continueFromTo prover stmt wit k m.succ
          = fun rk => prover.processRound m (continueFromTo prover stmt wit k m.castSucc rk) :=
        funext (fun rk => continueFromTo_succ_of_ne prover stmt wit k m hne rk)
      rw [hcont, processRound_eq_bind m prover
            (runToRound k stmt wit prover >>= continueFromTo prover stmt wit k m.castSucc),
          bind_assoc]
      refine bind_congr (fun rk => ?_)
      rw [← processRound_eq_bind]

/-- **Transitivity / range-split of `continueFromTo`.**  For `k ≤ k' ≤ j`, continuing the prover's
run from round `k` to round `j` equals continuing `k → k'` and then `k' → j`.  Proved by
`Fin.induction` on `j` via `continueFromTo_succ_of_ne`, `processRound_eq_bind`, and `bind_assoc`
(the `continueFromTo`-prefix analogue of `runToRound_eq_bind_continueFromTo`).  This is the split a
sequential-composition right-block run characterization needs to peel the seam round off the interior
rounds. -/
theorem continueFromTo_trans (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn) (k k' j : Fin (n + 1)) (hkk' : k ≤ k') (hk'j : k' ≤ j)
    (rk : pSpec.Transcript k × prover.PrvState k) :
    continueFromTo prover stmt wit k j rk
      = continueFromTo prover stmt wit k k' rk >>= continueFromTo prover stmt wit k' j := by
  induction j using Fin.induction with
  | zero =>
    have hk'0 : k' = 0 := le_antisymm hk'j (Fin.zero_le _)
    have hk0 : k = 0 := le_antisymm (hkk'.trans hk'j) (Fin.zero_le _)
    subst hk'0; subst hk0
    simp only [continueFromTo_self, pure_bind]
  | succ m ih =>
    rcases eq_or_lt_of_le hk'j with heq | hlt
    · subst heq
      conv_rhs => rw [show (continueFromTo prover stmt wit (m.succ) (m.succ))
                        = (fun rk => pure rk)
                          from funext (continueFromTo_self prover stmt wit _)]
      rw [bind_pure]
    · have hk'm : k' ≤ m.castSucc := by rw [Fin.le_castSucc_iff]; exact hlt
      have hne : (k : Fin (n + 1)) ≠ m.succ := ne_of_lt (lt_of_le_of_lt hkk' hlt)
      have hne' : (k' : Fin (n + 1)) ≠ m.succ := ne_of_lt hlt
      rw [continueFromTo_succ_of_ne prover stmt wit k m hne rk, ih hk'm]
      have hcont : continueFromTo prover stmt wit k' m.succ
          = fun rk => prover.processRound m (continueFromTo prover stmt wit k' m.castSucc rk) :=
        funext (fun rk => continueFromTo_succ_of_ne prover stmt wit k' m hne' rk)
      rw [hcont, processRound_eq_bind m prover
            (continueFromTo prover stmt wit k k' rk >>= continueFromTo prover stmt wit k' m.castSucc),
          bind_assoc]
      refine bind_congr (fun rk => ?_)
      rw [← processRound_eq_bind]

/-- **Seam→`runToRound` bridge.**  `processRound 0` applied to the (pure) round-0 default state is
exactly `runToRound 1` (i.e. `runToRound (⟨0,hn⟩.succ)`).  Glue for the sequential-composition
right-block assembly: it turns the seam round's `processRound 0 (pure(default, input))` shape (from
the `append_continueFromTo_seam_start_*` lemmas) into `runToRound 1`, so `runToRound_eq_bind_continueFromTo`
can fold it with the interior `continueFromTo` into a single `runToRound`.  By `runToRound_succ` and the
definitional `runToRound 0 = pure(default, input)`. -/
theorem processRound_zero_pure_eq_runToRound {n : ℕ} {pSpec : ProtocolSpec n} (hn : 0 < n)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) (s : StmtIn) (w : WitIn) :
    prover.processRound (⟨0, hn⟩ : Fin n)
        (pure ((default : pSpec.Transcript (⟨0, by omega⟩ : Fin (n + 1))), prover.input (s, w)))
      = prover.runToRound (⟨0, hn⟩ : Fin n).succ s w := by
  rw [runToRound_succ]
  congr 1

/-- **P₂-side right-block assembly.**  The seam round's `processRound 0 (pure(default, input))` bound
with the interior continuation `continueFromTo 1 → last` is exactly `runToRound (Fin.last n)` — i.e.
the appended right block, projected to `P₂`, reconstructs `P₂`'s full run-to-round.  Combines
`processRound_zero_pure_eq_runToRound` (seam → `runToRound 1`) with `runToRound_eq_bind_continueFromTo`
(`runToRound 1 >>= continueFromTo 1 last = runToRound last`). -/
theorem processRound_zero_continueFromTo_eq_runToRound_last {n : ℕ} {pSpec : ProtocolSpec n}
    (hn : 0 < n) (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (s : StmtIn) (w : WitIn) :
    (prover.processRound (⟨0, hn⟩ : Fin n)
        (pure ((default : pSpec.Transcript (⟨0, by omega⟩ : Fin (n + 1))), prover.input (s, w)))
      >>= prover.continueFromTo s w (⟨0, hn⟩ : Fin n).succ (Fin.last n))
      = prover.runToRound (Fin.last n) s w := by
  rw [processRound_zero_pure_eq_runToRound hn]
  exact (runToRound_eq_bind_continueFromTo prover s w (⟨0, hn⟩ : Fin n).succ (Fin.last n)
    (by rw [Fin.le_def, Fin.val_succ, Fin.val_last]; omega)).symm

/-- **`continueFromTo` target-index transport.**  Continuing to two propositionally-equal target
rounds is heterogeneously equal.  The non-`rw`-able bridge (the result type depends on the target, so
in-place rewriting hits a non-type-correct motive) for aligning `Fin.last`-shaped targets with the
`⟨k₀ + j⟩`-shaped targets produced by the right-block interior induction (`1 + (n-1) = n` is not
definitional).  Proved by `subst`. -/
theorem continueFromTo_heq_target {n : ℕ} {pSpec : ProtocolSpec n} {k j₁ j₂ : Fin (n + 1)}
    (h : j₁ = j₂) (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn) (rk : pSpec.Transcript k × prover.PrvState k) :
    HEq (prover.continueFromTo stmt wit k j₁ rk) (prover.continueFromTo stmt wit k j₂ rk) := by
  subst h; rfl

/-- **`liftComp ∘ continueFromTo` target-index transport.**  The `liftComp`-lifted analogue of
`continueFromTo_heq_target`: continuing to two propositionally-equal target rounds and lifting along a
`SubSpec` is heterogeneously equal.  Used in the sequential-composition right-block assembly to align
the `liftComp`-of-`continueFromTo` produced by the interior induction (target `⟨k₀ + j⟩`) with the
`Fin.last` target of the run characterization.  Proved by `subst`. -/
theorem liftComp_continueFromTo_heq_target {n : ℕ} {pSpec : ProtocolSpec n} {k j₁ j₂ : Fin (n + 1)}
    (h : j₁ = j₂) {τ : Type} {superSpec : OracleSpec τ}
    [MonadLiftT (OracleQuery (oSpec + [pSpec.Challenge]ₒ)) (OracleQuery superSpec)]
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn) (rk : pSpec.Transcript k × prover.PrvState k) :
    HEq ((prover.continueFromTo stmt wit k j₁ rk).liftComp superSpec)
      ((prover.continueFromTo stmt wit k j₂ rk).liftComp superSpec) := by
  subst h; rfl

/-! ### Direction-resolved single-round peels

The two lemmas below resolve the `processRound` direction match into the two honest round shapes,
so a fixed-`n` honest run can be peeled one round at a time without unfolding the `match` by hand.
They sit on top of `runToRound_succ` (the one-round unfolding) and `processRound`'s definition. -/

/-- Unfold `processRound` into its `do`-block: take the previous round's `(transcript, state)`,
then branch on the round direction.  A rewrite handle; once the direction of the round is known use
the direction-resolved `runToRound_succ_challenge`/`runToRound_succ_message`. -/
theorem processRound_def (j : Fin n)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (currentResult : OracleComp (oSpec + [pSpec.Challenge]ₒ)
      (pSpec.Transcript j.castSucc × prover.PrvState j.castSucc)) :
      prover.processRound j currentResult = (do
        let ⟨transcript, state⟩ ← currentResult
        match hDir : pSpec.dir j with
        | .V_to_P => do
          let challenge ← pSpec.getChallenge ⟨j, hDir⟩
          letI newState := (← prover.receiveChallenge ⟨j, hDir⟩ state) challenge
          return ⟨transcript.concat challenge, newState⟩
        | .P_to_V => do
          let ⟨msg, newState⟩ ← prover.sendMessage ⟨j, hDir⟩ state
          return ⟨transcript.concat msg, newState⟩) := rfl

/-- **Message-round peel.** When round `j` is a `P_to_V` (prover-message) round, peeling one round
binds over the previous result and then runs `sendMessage`, appending the message to the
transcript. -/
theorem runToRound_succ_message (j : Fin n)
    (stmt : StmtIn) (wit : WitIn) (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hDir : pSpec.dir j = .P_to_V) :
      prover.runToRound j.succ stmt wit = (do
        let ⟨transcript, state⟩ ← prover.runToRound j.castSucc stmt wit
        let ⟨msg, newState⟩ ← prover.sendMessage ⟨j, hDir⟩ state
        return ⟨transcript.concat msg, newState⟩) := by
  rw [runToRound_succ, processRound_def]
  apply bind_congr
  rintro ⟨transcript, state⟩
  -- Collapse the tuple match, then resolve the direction match: the `V_to_P` branch is impossible
  -- by `hDir`, the `P_to_V` branch is the honest message shape (proof-irrelevant in `hDir`).
  dsimp only
  split <;> rename_i hDir'
  · exact absurd (hDir.symm.trans hDir') (by decide)
  · rfl

/-- **Challenge-round peel.** When round `j` is a `V_to_P` (verifier-challenge) round, peeling one
round binds over the previous result, samples the challenge, runs `receiveChallenge`, and appends
the challenge to the transcript. -/
theorem runToRound_succ_challenge (j : Fin n)
    (stmt : StmtIn) (wit : WitIn) (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hDir : pSpec.dir j = .V_to_P) :
      prover.runToRound j.succ stmt wit = (do
        let ⟨transcript, state⟩ ← prover.runToRound j.castSucc stmt wit
        let challenge ← pSpec.getChallenge ⟨j, hDir⟩
        letI newState := (← prover.receiveChallenge ⟨j, hDir⟩ state) challenge
        return ⟨transcript.concat challenge, newState⟩) := by
  rw [runToRound_succ, processRound_def]
  apply bind_congr
  rintro ⟨transcript, state⟩
  -- Collapse the tuple match, then resolve the direction match: the `V_to_P` branch is the honest
  -- challenge shape, the `P_to_V` branch is impossible by `hDir`.
  dsimp only
  split <;> rename_i hDir'
  · rfl
  · exact absurd (hDir.symm.trans hDir') (by decide)

/-- **Full-run peel.** `Prover.run` is `runToRound (Fin.last n)` followed by `output`. This exposes
the head so that the run can be peeled round-by-round (via `runToRound_succ` and friends) down to
the `output` step. -/
theorem run_eq_runToRound_last
    (stmt : StmtIn) (wit : WitIn) (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) :
      prover.run stmt wit = (do
        let ⟨transcript, state⟩ ← prover.runToRound (Fin.last n) stmt wit
        return ⟨transcript, ← prover.output state⟩) := rfl

end Prover

end Execution

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)]
  {WitIn : Type}
  {StmtOut : Type} {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type} [Oₛₒ : ∀ i, OracleInterface (OStmtOut i)]
  {WitOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n} [Oₘ : ∀ i, OracleInterface (pSpec.Message i)]

section Trivial

/-- Running the identity or trivial reduction results in the same input statement and witness, and
  empty transcript. -/
@[simp]
theorem Reduction.id_run (stmt : StmtIn) (wit : WitIn) :
    (Reduction.id : Reduction oSpec StmtIn WitIn _ _ _).run stmt wit =
      pure ⟨⟨default, stmt, wit⟩, stmt⟩ := by
  simp [Reduction.run, Reduction.id, Prover.run, Verifier.run, Prover.id, Verifier.id]
  rfl

/-- Running the identity or trivial reduction, with logging of queries to the shared oracle,
  results in the same input statement and witness, empty transcript, and empty query logs. -/
@[simp]
theorem Reduction.id_runWithLog (stmt : StmtIn) (wit : WitIn) :
    (Reduction.id : Reduction oSpec StmtIn WitIn _ _ _).runWithLog stmt wit =
      pure ⟨⟨⟨default, stmt, wit⟩, stmt⟩, [], []⟩ := by
  simp_all only [ChallengeIdx, Challenge]
  rfl

/-- Running the identity or trivial oracle reduction results in the same input statement, oracle
  statement, and witness. -/
@[simp]
theorem OracleReduction.id_run (stmt : StmtIn) (oStmt : ∀ i, OStmtIn i) (wit : WitIn) :
    (OracleReduction.id : OracleReduction oSpec StmtIn OStmtIn WitIn _ _ _ _).run stmt oStmt wit =
      pure ⟨⟨default, ⟨stmt, oStmt⟩, wit⟩, ⟨stmt, oStmt⟩⟩ := by
  simp_all only [ChallengeIdx, Challenge, run_eq_run_reduction, id_toReduction, Reduction.id_run]

/-- Running the identity or trivial oracle reduction results in the same input statement, oracle
  statement, and witness. -/
@[simp]
theorem OracleReduction.id_runWithLog (stmt : StmtIn) (oStmt : ∀ i, OStmtIn i) (wit : WitIn) :
    (OracleReduction.id : OracleReduction oSpec StmtIn OStmtIn WitIn _ _ _ _).runWithLog
      stmt oStmt wit = pure ⟨⟨default, ⟨stmt, oStmt⟩, wit⟩, ⟨stmt, oStmt⟩, [], []⟩ := by
  simp only [OracleReduction.runWithLog, OracleVerifier.run, Prover.run, OracleReduction.id,
    OracleProver.id, OracleVerifier.id, Prover.id,
    Prover.runToRound,
    monadLift_pure, pure_bind, Option.getM]
  rfl

end Trivial

section OptionTLifts

variable {α : Type} {pSpec : ProtocolSpec 1}

/-- Coercing an `OracleComp` into `OptionT` agrees with the explicit `OptionT.lift`. -/
lemma oracleComp_toOptionT_eq_lift (mx : OracleComp oSpec α) :
    ((mx : OptionT (OracleComp oSpec) α)) = OptionT.lift mx := by
  rw [OptionT.ext_iff]
  rw [show OptionT.lift mx = OptionT.mk (some <$> mx) by rfl]
  rw [show ((mx : OptionT (OracleComp oSpec) α)).run =
      some <$> (monadLift mx : OracleComp oSpec α) by
        change (monadLift mx : OptionT (OracleComp oSpec) α).run = _
        exact OptionT.run_monadLift (m := OracleComp oSpec) (n := OracleComp oSpec) mx]
  rw [monadLift_eq_self]
  rfl

/-- Lifting `OptionT.lift mx` across an oracle-spec extension is the same as first lifting `mx`
to the larger oracle spec and then lifting into `OptionT`. -/
lemma liftM_optionT_lift_eq_monadLift_liftM (mx : OracleComp oSpec α) :
    (liftM (OptionT.lift mx : OptionT (OracleComp oSpec) α) :
      OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ)) α) =
      (monadLift (liftM mx : OracleComp (oSpec + [pSpec.Challenge]ₒ) α) :
        OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ)) α) := by
  rw [liftM_OptionT_eq]
  change
    (simulateQ (fun t => (liftM (OracleSpec.query t) :
        OracleComp (oSpec + [pSpec.Challenge]ₒ) _)) (OptionT.lift mx).run) =
      (monadLift (liftM mx : OracleComp (oSpec + [pSpec.Challenge]ₒ) α) :
        OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ)) α).run
  rw [show OptionT.lift mx = OptionT.mk (some <$> mx) by rfl]
  rw [show (monadLift (liftM mx : OracleComp (oSpec + [pSpec.Challenge]ₒ) α) :
      OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ)) α).run =
      some <$> (monadLift (liftM mx : OracleComp (oSpec + [pSpec.Challenge]ₒ) α) :
        OracleComp (oSpec + [pSpec.Challenge]ₒ) α) by
        exact OptionT.run_monadLift (m := OracleComp (oSpec + [pSpec.Challenge]ₒ))
          (n := OracleComp (oSpec + [pSpec.Challenge]ₒ))
          (liftM mx : OracleComp (oSpec + [pSpec.Challenge]ₒ) α)]
  rw [monadLift_eq_self]
  change simulateQ (fun t => (liftM (OracleSpec.query t) :
      OracleComp (oSpec + [pSpec.Challenge]ₒ) _))
    (some <$> mx) = some <$> (liftM mx : OracleComp (oSpec + [pSpec.Challenge]ₒ) α)
  rw [simulateQ_map]
  rw [show simulateQ (fun t => (liftM (OracleSpec.query t) :
        OracleComp (oSpec + [pSpec.Challenge]ₒ) _))
      mx = liftComp mx (oSpec + [pSpec.Challenge]ₒ) by rfl]
  rw [liftComp_eq_liftM]

/-- Directly lifting an `OracleComp` into `OptionT` over an extended oracle spec agrees with
first lifting the computation into the larger oracle spec and then into `OptionT`. -/
lemma liftM_oracleComp_eq_monadLift_liftM (mx : OracleComp oSpec α) :
    (liftM mx : OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ)) α) =
      (monadLift (liftM mx : OracleComp (oSpec + [pSpec.Challenge]ₒ) α) :
        OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ)) α) := by
  change (liftM ((mx : OptionT (OracleComp oSpec) α)) :
      OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ)) α) = _
  rw [oracleComp_toOptionT_eq_lift]
  exact liftM_optionT_lift_eq_monadLift_liftM (pSpec := pSpec) mx

/-- Interpreting a lifted `OptionT` computation against an appended oracle implementation ignores
the right-hand implementation when the lifted computation never queries it. -/
lemma simulateQ_add_run_liftM_left
    {ι₂ : Type} {spec₂ : OracleSpec ι₂} {σ : Type}
    (impl₁ : QueryImpl oSpec (StateT σ ProbComp))
    (impl₂ : QueryImpl spec₂ (StateT σ ProbComp))
    (oa : OptionT (OracleComp oSpec) α) :
    simulateQ (impl₁ + impl₂) (OptionT.run (liftM oa)) = simulateQ impl₁ oa.run := by
  rw [liftM_OptionT_eq]
  change simulateQ (impl₁ + impl₂) (liftM oa.run : OracleComp (oSpec + spec₂) (Option α)) = _
  rw [show (liftM oa.run : OracleComp (oSpec + spec₂) (Option α)) =
      liftComp oa.run (oSpec + spec₂) by rw [liftComp_eq_liftM]]
  rw [QueryImpl.simulateQ_add_liftComp_left]

omit pSpec in
/-- Interpreting a computation lifted through `spec₁ + (spec₂ + spec₃)` and then across the
add-association `SubSpec` against an implementation on `(spec₁ + spec₂) + spec₃` ignores the
right-hand implementation when the source computation only queries `spec₁ + spec₂`. -/
lemma simulateQ_add_liftComp_add_assoc_left
    {ι₁ ι₂ ι₃ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {spec₃ : OracleSpec ι₃} {σ : Type}
    (impl₁₂ : QueryImpl (spec₁ + spec₂) (StateT σ ProbComp))
    (impl₃ : QueryImpl spec₃ (StateT σ ProbComp))
    (oa : OracleComp (spec₁ + spec₂) α) :
    simulateQ (impl₁₂ + impl₃)
        (OracleComp.liftComp
          (OracleComp.liftComp oa (spec₁ + (spec₂ + spec₃)))
          ((spec₁ + spec₂) + spec₃)) =
      simulateQ impl₁₂ oa := by
  induction oa using OracleComp.inductionOn with
  | pure _ => rfl
  | query_bind t oa ih =>
      rcases t with t | t
      · simp only [OracleComp.liftComp_bind, OracleComp.liftComp_query, simulateQ_bind,
          simulateQ_query]
        refine bind_congr ?_
        intro x
        exact ih x
      · simp only [OracleComp.liftComp_bind, OracleComp.liftComp_query, simulateQ_bind,
          simulateQ_query]
        refine bind_congr ?_
        intro x
        exact ih x

#print axioms simulateQ_add_liftComp_add_assoc_left

end OptionTLifts

section SingleMessage

/-! Simplification lemmas for protocols with a single message -/

variable {pSpec : ProtocolSpec 1}

@[simp]
theorem Prover.runToRound_one_of_prover_first [ProverOnly pSpec] (stmt : StmtIn) (wit : WitIn)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) :
      prover.runToRound 1 stmt wit = (do
        let state := prover.input (stmt, wit)
        let ⟨msg, state⟩ ← liftComp (prover.sendMessage ⟨0, by simp⟩ state) _
        return (fun i => match i with | ⟨0, _⟩ => msg, state)) := by
  simp [Prover.runToRound, Prover.processRound]
  have : pSpec.dir 0 = .P_to_V := by simp
  split <;> rename_i hDir
  · have : Direction.P_to_V = .V_to_P := by rw [← this, hDir]
    contradiction
  · congr; funext a; congr; simp [default, Transcript.concat]; funext i
    have : i = 0 := by aesop
    rw [this]; simp [Fin.snoc]

@[simp]
theorem Prover.runToRound_one_of_verifier_first [VerifierOnly pSpec] (stmt : StmtIn) (wit : WitIn)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) :
      prover.runToRound 1 stmt wit = (do
        let state := prover.input (stmt, wit)
        let challenge ← liftComp (pSpec.getChallenge ⟨0, by simp⟩) _
        letI newState := (← liftComp (prover.receiveChallenge ⟨0, by simp⟩ state) _) challenge
        return (fun i => match i with | ⟨0, _⟩ => challenge, newState)) := by
  simp [Prover.runToRound, Prover.processRound]
  have : pSpec.dir 0 = .V_to_P := by simp
  split <;> rename_i hDir
  · -- V_to_P case: this is what we want
    congr 1
    funext challenge
    congr 1
    funext f
    simp only [default, Transcript.concat, Prod.mk.injEq]
    constructor
    · funext ⟨i, hi⟩
      have h : i = 0 := by omega
      subst h
      simp [Fin.snoc]
    · trivial
  · -- P_to_V case: contradiction
    have : Direction.V_to_P = .P_to_V := by rw [← this, hDir]
    contradiction

@[simp]
theorem Prover.run_of_verifier_first [VerifierOnly pSpec] (stmt : StmtIn) (wit : WitIn)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) :
      prover.run stmt wit = (do
        let state := prover.input (stmt, wit)
        let challenge ← liftComp (pSpec.getChallenge ⟨0, by simp⟩) _
        let f ← liftComp (prover.receiveChallenge ⟨0, by simp⟩ state) _
        let ctxOut ← prover.output (f challenge)
        return ((fun i => match i with | ⟨0, _⟩ => challenge), ctxOut)) := by
  simp [Prover.run]; rfl

@[simp]
theorem Prover.run_of_prover_first [ProverOnly pSpec] (stmt : StmtIn) (wit : WitIn)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) :
      prover.run stmt wit = (do
        let state := prover.input (stmt, wit)
        let ⟨msg, state⟩ ← liftComp (prover.sendMessage ⟨0, by simp⟩ state) _
        let ctxOut ← prover.output state
        return ((fun i => match i with | ⟨0, _⟩ => msg), ctxOut)) := by
  simp [Prover.run]; rfl

-- @[simp]
theorem Reduction.run_of_prover_first [ProverOnly pSpec] (stmt : StmtIn) (wit : WitIn)
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) :
      reduction.run stmt wit = (do
        let state := reduction.prover.input (stmt, wit)
        let ⟨msg, state⟩ ← (reduction.prover.sendMessage ⟨0, by simp⟩ state)
        let ctxOut ← reduction.prover.output state
        let transcript : pSpec.FullTranscript := fun i => match i with | ⟨0, _⟩ => msg
        let stmtOut ← (reduction.verifier.verify stmt transcript).run
        return (⟨transcript, ctxOut⟩, ← stmtOut.getM)) := by
  simp only [Reduction.run, Verifier.run]
  rw [Prover.run_of_prover_first]
  rw [OptionT.ext_iff]
  simp only [liftComp_eq_liftM, bind_assoc, pure_bind, monadLift_bind, monadLift_pure]
  rw [liftM_oracleComp_eq_monadLift_liftM (pSpec := pSpec)
    (mx := reduction.prover.sendMessage ⟨0, by simp⟩ (reduction.prover.input (stmt, wit)))]
  refine bind_congr ?_
  intro x
  rw [liftM_oracleComp_eq_monadLift_liftM (pSpec := pSpec) (mx := reduction.prover.output x.2)]
  -- conv =>
  --   enter [1, 2, a, 1]
  --   rw [map_eq_pure_bind]
  --   rw [loggingOracle.simulateQ_bind_fst
  --     (reduction.verifier.verify stmt _) (fun a_1_1 => pure (a_1_1, _))]
  -- simp

end SingleMessage

section Classes

variable {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn WitIn StmtOut WitOut : Type}
    {pSpec : ProtocolSpec 2}

end Classes
