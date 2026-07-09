/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.Security.RoundByRound
import ArkLib.OracleReduction.Security.OracleZeroKnowledge

open OracleComp ProtocolSpec

/-!
  # Simple (Oracle) Reduction: Locally / non-interactively reduce a claim

  This is a zero-round (oracle) reduction.

  1. Reduction version: there are mappings between `StmtIn → StmtOut` and `StmtIn → WitIn → WitOut`.
     Note the second mapping between witnesses may depend on the input statement as well. The prover
     and verifier applies these mappings to the input statement and witness, and returns the output
     statement and witness.

  This reduction is secure via pull-backs on relations. What this means is as follows:
  - Completeness holds if for the outputs of the reduction satisfies some relation `relOut` whenever
    the inputs satisfy the relation `relIn := relOut (mapStmt ·) (mapWit ·)`
  - (Round-by-round) knowledge soundness holds if there exists an inverse mapping
    `StmtIn → WitOut → WitIn` on witnesses (for extraction) such that
    `(mapStmt stmtIn, witOut) ∈ relOut → (stmtIn, mapWitInv stmtIn witOut) ∈ relIn`.

  2. Oracle reduction version: same as above, but with the extra mapping `OStmtIn → OStmtOut`,
     defined as an oracle simulation / embedding.

  This oracle reduction is secure via pull-backs on relations, similar to the reduction version,
  except that `mapStmt` is replaced by `mapStmt ⊗ mapOStmt`.
-/

namespace ReduceClaim

variable {ι : Type} (oSpec : OracleSpec ι)
  {StmtIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} {WitIn : Type}
  {StmtOut : Type} {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type} {WitOut : Type}
  [∀ i, OracleInterface (OStmtIn i)]
  (mapStmt : StmtIn → StmtOut) (mapWit : StmtIn → WitIn → WitOut)

section Reduction

/-- The prover for the `ReduceClaim` reduction. -/
def prover : Prover oSpec StmtIn WitIn StmtOut WitOut !p[] where
  PrvState | 0 => StmtIn × WitIn
  input := id
  sendMessage := fun i => nomatch i
  receiveChallenge := fun i => nomatch i
  output := fun ⟨stmt, wit⟩ => pure (mapStmt stmt, mapWit stmt wit)

/-- The verifier for the `ReduceClaim` reduction. -/
def verifier : Verifier oSpec StmtIn StmtOut !p[] where
  verify := fun stmt _ => pure (mapStmt stmt)

/-- The reduction for the `ReduceClaim` reduction. -/
def reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut !p[] where
  prover := prover oSpec mapStmt mapWit
  verifier := verifier oSpec mapStmt

variable {oSpec} {mapStmt} {mapWit}
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))

/-- The `ReduceClaim` reduction satisfies perfect completeness for any relation. -/
@[simp]
theorem reduction_completeness --(h : init.neverFails)
    (hRel : ∀ stmtIn witIn, (stmtIn, witIn) ∈ relIn ↔
      (mapStmt stmtIn, mapWit stmtIn witIn) ∈ relOut) :
    (reduction oSpec mapStmt mapWit).perfectCompleteness init impl relIn relOut := by
  simp only [Reduction.perfectCompleteness, Reduction.completeness, Reduction.completenessFromRun,
    ENNReal.coe_zero, tsub_zero]
  intro stmtIn witIn hIn
  have hrun : (reduction oSpec mapStmt mapWit).run stmtIn witIn =
      (pure ((default, (mapStmt stmtIn, mapWit stmtIn witIn)), mapStmt stmtIn) :
        OptionT (OracleComp _) _) := by
    simp [reduction, Reduction.run, prover, verifier, Prover.run, Verifier.run, Prover.runToRound]
    rfl
  simp only [hrun]
  rw [ge_iff_le, one_le_probEvent_iff, probEvent_eq_one_iff]
  refine ⟨?_, ?_⟩
  · rw [OptionT.probFailure_eq, OptionT.run_mk]
    simp only [probFailure_eq_zero, zero_add]
    apply probOutput_eq_zero_of_not_mem_support
    simp only [support_bind, Set.mem_iUnion, not_exists]
    intro s _ hmem
    change none ∈ support
      (StateT.run' (simulateQ _ (pure (some ((default, (mapStmt stmtIn, mapWit stmtIn witIn)),
        mapStmt stmtIn)) : OracleComp _ _)) s) at hmem
    rw [simulateQ_pure] at hmem
    change none ∈ support
      (Prod.fst <$> (pure (some ((default, (mapStmt stmtIn, mapWit stmtIn witIn)),
        mapStmt stmtIn)) : StateT σ ProbComp _).run s) at hmem
    rw [StateT.run_pure] at hmem
    simp [map_pure] at hmem
  · intro x hx
    rw [OptionT.mem_support_iff] at hx
    simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hx
    obtain ⟨s, _, hx⟩ := hx
    change some x ∈ support
      (StateT.run' (simulateQ _ (pure (some ((default, (mapStmt stmtIn, mapWit stmtIn witIn)),
        mapStmt stmtIn)) : OracleComp _ _)) s) at hx
    rw [simulateQ_pure] at hx
    change some x ∈ support
      (Prod.fst <$> (pure (some ((default, (mapStmt stmtIn, mapWit stmtIn witIn)),
        mapStmt stmtIn)) : StateT σ ProbComp _).run s) at hx
    rw [StateT.run_pure] at hx
    simp only [map_pure, support_pure, Set.mem_singleton_iff, Option.some.injEq] at hx
    cases hx
    exact ⟨(hRel stmtIn witIn).mp hIn, rfl⟩

/-- The honest transcript distribution for `ReduceClaim` is the deterministic empty transcript.
The mapped witness appears only in the output data, never in the zero-round transcript. -/
theorem honestTranscriptDist_reduction_evalDist
    (stmtIn : StmtIn) (witIn : WitIn) :
    evalDist (Reduction.honestTranscriptDist init impl
        (reduction oSpec mapStmt mapWit) stmtIn witIn) =
      evalDist (pure default : OptionT ProbComp (FullTranscript !p[])) := by
  apply evalDist_ext
  intro transcript
  classical
  unfold Reduction.honestTranscriptDist
  have hrun : (reduction oSpec mapStmt mapWit).run stmtIn witIn =
      (pure ((default, (mapStmt stmtIn, mapWit stmtIn witIn)), mapStmt stmtIn) :
        OptionT (OracleComp _) _) := by
    simp [reduction, Reduction.run, prover, verifier, Prover.run, Verifier.run,
      Prover.runToRound]
    rfl
  simp only [hrun, map_pure, OptionT.run_pure, simulateQ_pure, StateT.run'_eq,
    StateT.run_pure, bind_pure_comp]
  rw [OptionT.probOutput_eq, OptionT.probOutput_eq]
  simp [probOutput_map_const, HasEvalPMF.probFailure_eq_zero]

/-- `ReduceClaim` is perfectly HVZK for any input relation: it has no messages or challenges, so
the identity empty-transcript simulator matches every honest transcript distribution. -/
theorem reduction_perfectHVZK (relIn : Set (StmtIn × WitIn)) :
    Reduction.perfectHVZK init impl relIn
      (reduction oSpec mapStmt mapWit) Reduction.idTranscriptSimulator := by
  intro stmtIn witIn _
  exact (honestTranscriptDist_reduction_evalDist (oSpec := oSpec)
    (mapStmt := mapStmt) (mapWit := mapWit) stmtIn witIn).symm

/-- Perfect HVZK implies statistical HVZK for `ReduceClaim` at every error budget. -/
theorem reduction_statisticalHVZK (relIn : Set (StmtIn × WitIn)) (ε : NNReal) :
    Reduction.statisticalHVZK init impl relIn
      (reduction oSpec mapStmt mapWit) Reduction.idTranscriptSimulator ε :=
  (reduction_perfectHVZK (oSpec := oSpec) (mapStmt := mapStmt)
    (mapWit := mapWit) (init := init) (impl := impl) relIn).statisticalHVZK ε

/-- `ReduceClaim` has an explicit perfect-HVZK simulator for any input relation. -/
theorem reduction_isHVZK (relIn : Set (StmtIn × WitIn)) :
    Reduction.isHVZK init impl relIn (reduction oSpec mapStmt mapWit) :=
  ⟨Reduction.idTranscriptSimulator, reduction_perfectHVZK (oSpec := oSpec)
    (mapStmt := mapStmt) (mapWit := mapWit) (init := init) (impl := impl) relIn⟩

/-- `ReduceClaim` has statistical HVZK for any input relation and error budget. -/
theorem reduction_isStatHVZK (relIn : Set (StmtIn × WitIn)) (ε : NNReal) :
    Reduction.isStatHVZK init impl relIn (reduction oSpec mapStmt mapWit) ε :=
  (reduction_isHVZK (oSpec := oSpec) (mapStmt := mapStmt)
    (mapWit := mapWit) (init := init) (impl := impl) relIn).isStatHVZK ε

/-- The round-by-round extractor for the `ReduceClaim` (oracle) reduction. Requires a mapping
  `mapWitInv` from the output witness to the input witness. -/
def extractor (mapWitInv : StmtIn → WitOut → WitIn) :
    Extractor.RoundByRound oSpec StmtIn WitIn WitOut !p[] (fun _ => WitIn) where
  eqIn := rfl
  extractMid := fun i => Fin.elim0 i
  extractOut := fun stmtIn _ witOut => mapWitInv stmtIn witOut

variable {mapWitInv : StmtIn → WitOut → WitIn}


@[simp]
lemma support_liftM (m : Type _ → Type _) [Monad m] [HasEvalSet m]
    {α} (mx : m α) : support (liftM mx : OptionT m α) = support mx :=
  OptionT.support_liftM mx

@[simp]
lemma support_mk (m : Type _ → Type _) [Monad m] [HasEvalSet m]
    {α} (mx : m (Option α)) :
    support (OptionT.mk mx) = {x | some x ∈ support mx} := by
  -- `OptionT.mk` packages an `m (Option α)` into `OptionT m α`; the standalone instance gives
  -- `support (OptionT.mk mx) = some ⁻¹' support (OptionT.run (OptionT.mk mx))
  --   = some ⁻¹' support mx`,
  -- which is exactly the set described by the RHS.
  rw [OptionT.support_def]
  ext x; simp

/-- The knowledge state function for the `ReduceClaim` reduction. -/
def knowledgeStateFunction (hRel : ∀ stmtIn witOut,
    (mapStmt stmtIn, witOut) ∈ relOut → (stmtIn, mapWitInv stmtIn witOut) ∈ relIn) :
    (verifier oSpec mapStmt).KnowledgeStateFunction
      init impl relIn relOut (extractor mapWitInv) where
  toFun | ⟨0, _⟩ => fun stmtIn _ witIn => ⟨stmtIn, witIn⟩ ∈ relIn
  toFun_empty := fun stmtIn witIn => by simp
  toFun_next := fun m => Fin.elim0 m
  toFun_full := fun stmtIn _ witOut h => by
    -- Verifier deterministically returns `mapStmt stmtIn`; from positive probability we extract
    -- `(mapStmt stmtIn, witOut) ∈ relOut`, then invoke `hRel` to land in `relIn`.
    simp only [Verifier.run, verifier] at h
    rw [gt_iff_lt, probEvent_pos_iff] at h
    obtain ⟨x, hx, hrel⟩ := h
    rw [OptionT.mem_support_iff] at hx
    simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hx
    obtain ⟨s, _, hx⟩ := hx
    have key : (simulateQ impl (pure (mapStmt stmtIn) : OptionT (OracleComp oSpec) StmtOut)).run' s =
        pure (some (mapStmt stmtIn)) := by
      change (simulateQ impl
        (pure (some (mapStmt stmtIn)) : OracleComp oSpec (Option StmtOut))).run' s = _
      rw [simulateQ_pure]
      change Prod.fst <$> (pure (some (mapStmt stmtIn)) : StateT σ ProbComp _).run s = _
      rw [StateT.run_pure]; simp [map_pure]
    rw [key] at hx
    simp only [support_pure, Set.mem_singleton_iff] at hx
    cases (Option.some.inj hx)
    exact hRel stmtIn witOut hrel

/-- The `ReduceClaim` oracle reduction satisfies perfect round-by-round knowledge soundness.

Note that since there is no challenge round, all the work is done in the definition of the
knowledge state function. -/
@[simp]
theorem verifier_rbrKnowledgeSoundness (hRel : ∀ stmtIn witOut,
    (mapStmt stmtIn, witOut) ∈ relOut → (stmtIn, mapWitInv stmtIn witOut) ∈ relIn) :
    (verifier oSpec mapStmt).rbrKnowledgeSoundness init impl relIn relOut 0 := by
  refine ⟨_, _, knowledgeStateFunction relIn relOut hRel, ?_⟩
  simp only [ProtocolSpec.ChallengeIdx]
  exact fun _ _ _ i => Fin.elim0 i.1

#print axioms ReduceClaim.honestTranscriptDist_reduction_evalDist
#print axioms ReduceClaim.reduction_perfectHVZK
#print axioms ReduceClaim.reduction_statisticalHVZK
#print axioms ReduceClaim.reduction_isHVZK
#print axioms ReduceClaim.reduction_isStatHVZK

end Reduction

section OracleReduction

variable
  -- Require map on indices to go the other way
  (embedIdx : ιₛₒ ↪ ιₛᵢ) (hEq : ∀ i, OStmtIn (embedIdx i) = OStmtOut i)

@[reducible, simp]
def mapOStmt (oStmtIn : ∀ i, OStmtIn i) : ∀ i, OStmtOut i := fun i => (hEq i) ▸ oStmtIn (embedIdx i)

/-- The oracle prover for the `ReduceClaim` oracle reduction. -/
def oracleProver : OracleProver oSpec
    StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut !p[] where
  PrvState := fun _ => (StmtIn × (∀ i, OStmtIn i)) × WitIn
  input := id
  sendMessage := fun i => nomatch i
  receiveChallenge := fun i => nomatch i
  output := fun ⟨⟨stmt, oStmt⟩, wit⟩ =>
    pure ((mapStmt stmt, mapOStmt embedIdx hEq oStmt), mapWit stmt wit)

/-- The oracle verifier for the `ReduceClaim` oracle reduction. -/
def oracleVerifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut !p[] where
  verify := fun stmt _ => pure (mapStmt stmt)
  embed := .trans embedIdx .inl
  hEq := by intro i; simp [hEq]

/-- Running the (oracle) verifier of the `ReduceClaim` oracle reduction deterministically returns
  the mapped statement and oracle statements. -/
theorem oracleVerifier_toVerifier_run (stmtIn : StmtIn) (oStmtIn : ∀ i, OStmtIn i)
    (tr : (!p[] : ProtocolSpec 0).FullTranscript) :
    (oracleVerifier oSpec mapStmt embedIdx hEq).toVerifier.run ⟨stmtIn, oStmtIn⟩ tr =
      (pure (mapStmt stmtIn, mapOStmt embedIdx hEq oStmtIn) : OptionT (OracleComp oSpec) _) := by
  simp only [Verifier.run, OracleVerifier.toVerifier, oracleVerifier]
  erw [simulateQ_pure]
  simp only [Function.Embedding.trans_apply, Function.Embedding.inl_apply]
  rfl

/-- The oracle reduction for the `ReduceClaim` oracle reduction. -/
def oracleReduction : OracleReduction oSpec
    StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut !p[] where
  prover := oracleProver oSpec mapStmt mapWit embedIdx hEq
  verifier := oracleVerifier oSpec mapStmt embedIdx hEq

variable {oSpec} {mapStmt} {mapWit} {embedIdx} {hEq}
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  (relIn : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn))
  (relOut : Set ((StmtOut × (∀ i, OStmtOut i)) × WitOut))

/-- The `ReduceClaim` oracle reduction satisfies perfect completeness for any relation.

  Proof strategy mirrors the non-oracle `reduction_completeness`: the prover deterministically
  returns the mapped output, the verifier deterministically computes `mapStmt`, and the
  positive-probability output is exactly the mapped element which lies in `relOut` by `hRel`. -/
@[simp]
theorem oracleReduction_completeness
    (hRel : ∀ stmtIn oStmtIn witIn,
      ((stmtIn, oStmtIn), witIn) ∈ relIn →
      ((mapStmt stmtIn, mapOStmt embedIdx hEq oStmtIn), mapWit stmtIn witIn) ∈ relOut) :
    (oracleReduction oSpec mapStmt mapWit embedIdx hEq).perfectCompleteness init impl
      relIn relOut := by
  simp only [OracleReduction.perfectCompleteness, Reduction.perfectCompleteness,
    Reduction.completeness, Reduction.completenessFromRun, ENNReal.coe_zero, tsub_zero]
  intro ⟨stmtIn, oStmtIn⟩ witIn hIn
  -- Reduce the run to a deterministic `pure` of the expected output.
  have hrun : (oracleReduction oSpec mapStmt mapWit embedIdx hEq).toReduction.run
      ⟨stmtIn, oStmtIn⟩ witIn =
      (pure ((default,
          ((mapStmt stmtIn, mapOStmt embedIdx hEq oStmtIn), mapWit stmtIn witIn)),
          (mapStmt stmtIn, mapOStmt embedIdx hEq oStmtIn)) :
        OptionT (OracleComp _) _) := by
    simp only [oracleReduction, OracleReduction.toReduction, Reduction.run, oracleProver,
      oracleVerifier, OracleVerifier.toVerifier, Prover.run, Verifier.run, Prover.runToRound]
    rfl
  rw [hrun]
  rw [ge_iff_le, one_le_probEvent_iff, probEvent_eq_one_iff]
  refine ⟨?_, ?_⟩
  · rw [OptionT.probFailure_eq, OptionT.run_mk]
    simp only [probFailure_eq_zero, zero_add]
    apply probOutput_eq_zero_of_not_mem_support
    simp only [support_bind, Set.mem_iUnion, not_exists]
    intro s _ hmem
    change none ∈ support
      (StateT.run' (simulateQ _ (pure (some ((default,
        ((mapStmt stmtIn, mapOStmt embedIdx hEq oStmtIn), mapWit stmtIn witIn)),
        (mapStmt stmtIn, mapOStmt embedIdx hEq oStmtIn))) : OracleComp _ _)) s) at hmem
    rw [simulateQ_pure] at hmem
    change none ∈ support
      (Prod.fst <$> (pure (some ((default,
        ((mapStmt stmtIn, mapOStmt embedIdx hEq oStmtIn), mapWit stmtIn witIn)),
        (mapStmt stmtIn, mapOStmt embedIdx hEq oStmtIn))) :
          StateT σ ProbComp _).run s) at hmem
    rw [StateT.run_pure] at hmem
    simp [map_pure] at hmem
  · intro x hx
    rw [OptionT.mem_support_iff] at hx
    simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hx
    obtain ⟨s, _, hx⟩ := hx
    change some x ∈ support
      (StateT.run' (simulateQ _ (pure (some ((default,
        ((mapStmt stmtIn, mapOStmt embedIdx hEq oStmtIn), mapWit stmtIn witIn)),
        (mapStmt stmtIn, mapOStmt embedIdx hEq oStmtIn))) : OracleComp _ _)) s) at hx
    rw [simulateQ_pure] at hx
    change some x ∈ support
      (Prod.fst <$> (pure (some ((default,
        ((mapStmt stmtIn, mapOStmt embedIdx hEq oStmtIn), mapWit stmtIn witIn)),
        (mapStmt stmtIn, mapOStmt embedIdx hEq oStmtIn))) :
          StateT σ ProbComp _).run s) at hx
    rw [StateT.run_pure] at hx
    simp only [map_pure, support_pure, Set.mem_singleton_iff, Option.some.injEq] at hx
    cases hx
    exact ⟨hRel stmtIn oStmtIn witIn hIn, rfl⟩
  -- -- Future work: clean up this proof
  -- simp only [OracleReduction.perfectCompleteness, oracleReduction, OracleReduction.toReduction,
  --   OracleVerifier.toVerifier,
  --   Reduction.perfectCompleteness_eq_prob_one, ProtocolSpec.ChallengeIdx, StateT.run'_eq,
  --   OracleComp.probEvent_eq_one_iff, OracleComp.probFailure_eq_zero_iff,
  --   OracleComp.neverFails_bind_iff, h, OracleComp.neverFails_map_iff, true_and,
  --   OracleComp.support_bind, OracleComp.support_map, Set.mem_iUnion, Set.mem_image, Prod.exists,
  --   exists_and_right, exists_eq_right, exists_prop, forall_exists_index, and_imp, Prod.forall,
  --   Fin.forall_fin_zero_pi, Prod.mk.injEq]
  -- simp only [Reduction.run, Prover.run, Verifier.run, oracleProver, oracleVerifier]
  -- simp only [ProtocolSpec.ChallengeIdx, Fin.reduceLast, Nat.reduceAdd, ProtocolSpec.MessageIdx,
  --   ProtocolSpec.Message, ProtocolSpec.Challenge, Prover.runToRound_zero_of_prover_first,
  --   Fin.isValue, id_eq, bind_pure_comp, map_pure, OracleComp.simulateQ_pure,
  --   Function.Embedding.trans_apply, Function.Embedding.inl_apply, eq_mpr_eq_cast,
  --   OracleComp.liftM_eq_liftComp, OracleComp.liftComp_pure, StateT.run_pure,
  --   OracleComp.neverFails_pure, implies_true, OracleComp.support_pure, Set.mem_singleton_iff,
  --   Prod.mk.injEq, and_imp, true_and]
  -- aesop

/-- The honest transcript distribution for the plain `ReduceClaim` oracle reduction is the
deterministic empty transcript. The mapped output oracle statement and witness appear only in the
output data, never in the zero-round transcript. -/
theorem honestTranscriptDist_oracleReduction_evalDist
    (stmtIn : StmtIn) (oStmtIn : ∀ i, OStmtIn i) (witIn : WitIn) :
    evalDist (Reduction.honestTranscriptDist init impl
        (oracleReduction oSpec mapStmt mapWit embedIdx hEq).toReduction
        ⟨stmtIn, oStmtIn⟩ witIn) =
      evalDist (pure default : OptionT ProbComp (FullTranscript !p[])) := by
  apply evalDist_ext
  intro transcript
  classical
  unfold Reduction.honestTranscriptDist
  have hrun : (oracleReduction oSpec mapStmt mapWit embedIdx hEq).toReduction.run
      ⟨stmtIn, oStmtIn⟩ witIn =
      (pure ((default,
          ((mapStmt stmtIn, mapOStmt embedIdx hEq oStmtIn), mapWit stmtIn witIn)),
          (mapStmt stmtIn, mapOStmt embedIdx hEq oStmtIn)) :
        OptionT (OracleComp _) _) := by
    simp only [oracleReduction, OracleReduction.toReduction, Reduction.run, oracleProver,
      oracleVerifier, OracleVerifier.toVerifier, Prover.run, Verifier.run, Prover.runToRound]
    rfl
  rw [hrun]
  simp only [map_pure, OptionT.run_pure, simulateQ_pure, StateT.run'_eq, StateT.run_pure,
    bind_pure_comp]
  rw [OptionT.probOutput_eq, OptionT.probOutput_eq]
  simp [probOutput_map_const, HasEvalPMF.probFailure_eq_zero]

/-- The plain `ReduceClaim` oracle reduction is perfectly HVZK for any input relation: it has no
messages or challenges, so the identity empty-transcript simulator matches every honest transcript
distribution. -/
theorem oracleReduction_perfectHVZK
    (relIn : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)) :
    OracleReduction.perfectHVZK init impl relIn
      (oracleReduction oSpec mapStmt mapWit embedIdx hEq)
      Reduction.idTranscriptSimulator := by
  intro stmtIn witIn _
  exact (honestTranscriptDist_oracleReduction_evalDist (oSpec := oSpec)
    (mapStmt := mapStmt) (mapWit := mapWit) (embedIdx := embedIdx) (hEq := hEq)
    stmtIn.1 stmtIn.2 witIn).symm

/-- Perfect HVZK implies statistical HVZK for the plain `ReduceClaim` oracle reduction at every
error budget. -/
theorem oracleReduction_statisticalHVZK
    (relIn : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)) (ε : NNReal) :
    OracleReduction.statisticalHVZK init impl relIn
      (oracleReduction oSpec mapStmt mapWit embedIdx hEq)
      Reduction.idTranscriptSimulator ε :=
  (oracleReduction_perfectHVZK (oSpec := oSpec) (mapStmt := mapStmt)
    (mapWit := mapWit) (embedIdx := embedIdx) (hEq := hEq)
    (init := init) (impl := impl) relIn).statisticalHVZK ε

/-- The plain `ReduceClaim` oracle reduction has an explicit perfect-HVZK simulator for any input
relation. -/
theorem oracleReduction_isHVZK
    (relIn : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)) :
    OracleReduction.isHVZK init impl relIn
      (oracleReduction oSpec mapStmt mapWit embedIdx hEq) :=
  ⟨Reduction.idTranscriptSimulator,
    oracleReduction_perfectHVZK (oSpec := oSpec) (mapStmt := mapStmt)
      (mapWit := mapWit) (embedIdx := embedIdx) (hEq := hEq)
      (init := init) (impl := impl) relIn⟩

/-- The plain `ReduceClaim` oracle reduction has statistical HVZK for any input relation and error
budget. -/
theorem oracleReduction_isStatHVZK
    (relIn : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)) (ε : NNReal) :
    OracleReduction.isStatHVZK init impl relIn
      (oracleReduction oSpec mapStmt mapWit embedIdx hEq) ε :=
  (oracleReduction_isHVZK (oSpec := oSpec) (mapStmt := mapStmt)
    (mapWit := mapWit) (embedIdx := embedIdx) (hEq := hEq)
    (init := init) (impl := impl) relIn).isStatHVZK ε

#print axioms ReduceClaim.honestTranscriptDist_oracleReduction_evalDist
#print axioms ReduceClaim.oracleReduction_perfectHVZK
#print axioms ReduceClaim.oracleReduction_statisticalHVZK
#print axioms ReduceClaim.oracleReduction_isHVZK
#print axioms ReduceClaim.oracleReduction_isStatHVZK

variable {mapWitInv : (StmtIn × (∀ i, OStmtIn i)) → WitOut → WitIn}

/-- The knowledge state function for the `ReduceClaim` oracle reduction. -/
def oracleKnowledgeStateFunction (hRel : ∀ stmtIn oStmtIn witOut,
    ((mapStmt stmtIn, mapOStmt embedIdx hEq oStmtIn), witOut) ∈ relOut →
      ((stmtIn, oStmtIn), mapWitInv (stmtIn, oStmtIn) witOut) ∈ relIn) :
    (oracleVerifier oSpec mapStmt embedIdx hEq).KnowledgeStateFunction
      init impl relIn relOut (extractor mapWitInv) where
  toFun | ⟨0, _⟩ => fun ⟨stmtIn, oStmtIn⟩ _ witIn => ⟨⟨stmtIn, oStmtIn⟩, witIn⟩ ∈ relIn
  toFun_empty := fun stmtIn witIn => by simp
  toFun_next := fun m => Fin.elim0 m
  toFun_full := fun ⟨stmtIn, oStmtIn⟩ tr witOut => by
    -- Bind `h` via `intro` (not as a lambda parameter) to avoid an expensive `isDefEq` check
    -- against the heavy `verifier.run` field type.
    intro h
    simp only [Verifier.run, oracleVerifier, OracleVerifier.toVerifier] at h
    change ((stmtIn, oStmtIn), mapWitInv (stmtIn, oStmtIn) witOut) ∈ relIn
    rw [gt_iff_lt, probEvent_pos_iff] at h
    obtain ⟨x, hx, hrel⟩ := h
    rw [OptionT.mem_support_iff] at hx
    simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hx
    obtain ⟨s, _, hx⟩ := hx
    -- The oracle verifier deterministically returns the pair
    -- `(mapStmt stmtIn, mapOStmt embedIdx hEq oStmtIn)`, so the simulated run is definitionally
    -- `pure (some ...)` and positive probability forces `x` to equal that pair.
    have hxc : some x ∈ support ((simulateQ impl
        (pure (some (mapStmt stmtIn, mapOStmt embedIdx hEq oStmtIn)) :
          OracleComp oSpec (Option (StmtOut × (∀ i, OStmtOut i))))).run' s) := hx
    rw [simulateQ_pure] at hxc
    change some x ∈ support (Prod.fst <$> (pure
      (some (mapStmt stmtIn, mapOStmt embedIdx hEq oStmtIn)) : StateT σ ProbComp _).run s) at hxc
    rw [StateT.run_pure] at hxc
    simp only [map_pure, support_pure, Set.mem_singleton_iff] at hxc
    cases (Option.some.inj hxc)
    exact hRel stmtIn oStmtIn witOut hrel

/-- The `ReduceClaim` oracle reduction satisfies perfect round-by-round knowledge soundness.

Note that since there is no challenge round, all the work is done in the definition of the
knowledge state function. -/
@[simp]
theorem oracleVerifier_rbrKnowledgeSoundness (hRel : ∀ stmtIn oStmtIn witOut,
    ((mapStmt stmtIn, mapOStmt embedIdx hEq oStmtIn), witOut) ∈ relOut →
      ((stmtIn, oStmtIn), mapWitInv (stmtIn, oStmtIn) witOut) ∈ relIn) :
    (oracleVerifier oSpec mapStmt embedIdx hEq).rbrKnowledgeSoundness init impl relIn relOut 0 := by
  refine ⟨_, _, oracleKnowledgeStateFunction relIn relOut hRel, ?_⟩
  intro stmtIn witIn prover i
  exact Fin.elim0 i.1

end OracleReduction

section OracleReductionO

/-!
### Oracle-aware variant: `ReduceClaim` whose output statement may depend on the oracles

DEFINITION ADDED (2026-06-04): The plain `ReduceClaim.oracleReduction` above transforms the output
statement by a **pure** map `mapStmt : StmtIn → StmtOut` with no oracle access. Some consumers (e.g.
a single round of sum-check, where the new target `b := q.eval r` is the evaluation of an *oracle*
polynomial `q`) need the output statement to be computed by
**querying the input oracle statements**.

This variant adds an *oracle-aware* statement map. An oracle reduction's verifier is allowed oracle
access (its `verify` returns an `OracleComp` over `oSpec + ([OStmtIn]ₒ + [pSpec.Message]ₒ)`), so we
let the verifier compute the output statement by an oracle computation `mapStmtO`. The (honest)
prover holds the concrete oracle data, so it computes the same output via the *pure* specification
`mapStmt : StmtIn → (∀ i, OStmtIn i) → StmtOut`; consistency of the two is the coherence hypothesis
`hMap` (simulating `mapStmtO` against the concrete oracle data yields `mapStmt`). Mirrors the
output-oracle routing (`embed`/`hEq`) and the security-lemma shape of the plain variant verbatim, so
existing `ReduceClaim` consumers stay intact (the plain `oracleReduction` is untouched).

We specialize the protocol spec to `!p[]` (zero rounds, no messages), matching the plain variant. -/

variable
  (mapStmtO : StmtIn →
    OracleComp (oSpec + ([OStmtIn]ₒ + [(!p[] : ProtocolSpec 0).Message]ₒ)) StmtOut)
  (mapStmtO_spec : StmtIn → (∀ i, OStmtIn i) → StmtOut)
  (embedIdx : ιₛₒ ↪ ιₛᵢ) (hEq : ∀ i, OStmtIn (embedIdx i) = OStmtOut i)

/-- The oracle prover for the oracle-aware `ReduceClaim` variant. The honest prover holds the
  concrete oracle data, so it applies the *pure* specification `mapStmtO_spec` (which coheres with
  the verifier's oracle map `mapStmtO` via `hMap`). -/
def oracleProverO : OracleProver oSpec
    StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut !p[] where
  PrvState := fun _ => (StmtIn × (∀ i, OStmtIn i)) × WitIn
  input := id
  sendMessage := fun i => nomatch i
  receiveChallenge := fun i => nomatch i
  output := fun ⟨⟨stmt, oStmt⟩, wit⟩ =>
    pure ((mapStmtO_spec stmt oStmt, mapOStmt embedIdx hEq oStmt), mapWit stmt wit)

/-- The oracle verifier for the oracle-aware `ReduceClaim` variant. Its `verify` computes the output
  statement by the oracle computation `mapStmtO stmt`, querying the input oracle statements. -/
def oracleVerifierO : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut !p[] where
  verify := fun stmt _ => OptionT.lift (mapStmtO stmt)
  embed := .trans embedIdx .inl
  hEq := by intro i; simp [hEq]

/-- The oracle-aware `ReduceClaim` variant as an oracle reduction. -/
def oracleReductionO : OracleReduction oSpec
    StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut !p[] where
  prover := oracleProverO (oSpec := oSpec) (mapStmtO_spec := mapStmtO_spec) (mapWit := mapWit)
    (embedIdx := embedIdx) (hEq := hEq)
  verifier := oracleVerifierO (oSpec := oSpec) (mapStmtO := mapStmtO) (embedIdx := embedIdx)
    (hEq := hEq)

variable {oSpec} {mapStmtO} {mapStmtO_spec} {mapWit} {embedIdx} {hEq}
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- The coherence hypothesis bundling the verifier's oracle map `mapStmtO` with the prover's pure
  specification `mapStmtO_spec`: simulating `mapStmtO stmt` against the concrete oracle data `oStmt`
  (and prover messages, of which there are none for `!p[]`) returns `mapStmtO_spec stmt oStmt`.

  This is stated as a plain `∀` (not a bundled `abbrev`) so that the security proofs can `rw`/`simp`
  with it directly. -/
@[reducible]
def MapCoherent
    (mapStmtO : StmtIn →
      OracleComp (oSpec + ([OStmtIn]ₒ + [(!p[] : ProtocolSpec 0).Message]ₒ)) StmtOut)
    (mapStmtO_spec : StmtIn → (∀ i, OStmtIn i) → StmtOut) : Prop :=
  ∀ stmt oStmt (msgs : ∀ i, (!p[] : ProtocolSpec 0).Message i),
    simulateQ (OracleInterface.simOracle2 oSpec oStmt msgs) (mapStmtO stmt)
      = pure (mapStmtO_spec stmt oStmt)

/-- Running the (oracle) verifier of the oracle-aware `ReduceClaim` variant deterministically
  returns the mapped statement and oracle statements (using the coherence `hMap`). -/
theorem oracleVerifierO_toVerifier_run (hMap : MapCoherent mapStmtO mapStmtO_spec)
    (stmtIn : StmtIn) (oStmtIn : ∀ i, OStmtIn i)
    (tr : (!p[] : ProtocolSpec 0).FullTranscript) :
    (oracleVerifierO (oSpec := oSpec) (mapStmtO := mapStmtO) (embedIdx := embedIdx)
        (hEq := hEq)).toVerifier.run ⟨stmtIn, oStmtIn⟩ tr =
      (pure (mapStmtO_spec stmtIn oStmtIn, mapOStmt embedIdx hEq oStmtIn) :
        OptionT (OracleComp oSpec) _) := by
  simp only [Verifier.run, OracleVerifier.toVerifier, oracleVerifierO]
  rw [simulateQ_optionT_lift, hMap]
  rw [show (OptionT.lift (pure (mapStmtO_spec stmtIn oStmtIn)) :
      OptionT (OracleComp oSpec) StmtOut) = pure (mapStmtO_spec stmtIn oStmtIn) from rfl]
  rw [pure_bind]
  simp only [Function.Embedding.trans_apply, Function.Embedding.inl_apply]

/-- Running the oracle-aware `ReduceClaim` variant deterministically returns the mapped statement,
  oracle statements and witness. -/
theorem oracleReductionO_run (hMap : MapCoherent mapStmtO mapStmtO_spec)
    (stmtIn : StmtIn) (oStmtIn : ∀ i, OStmtIn i) (witIn : WitIn) :
    (oracleReductionO (oSpec := oSpec) (mapStmtO := mapStmtO) (mapStmtO_spec := mapStmtO_spec)
        (mapWit := mapWit) (embedIdx := embedIdx) (hEq := hEq)).toReduction.run
        ⟨stmtIn, oStmtIn⟩ witIn =
      (pure ((default,
        ((mapStmtO_spec stmtIn oStmtIn, mapOStmt embedIdx hEq oStmtIn), mapWit stmtIn witIn)),
        (mapStmtO_spec stmtIn oStmtIn, mapOStmt embedIdx hEq oStmtIn)) :
          OptionT (OracleComp _) _) := by
  simp only [OracleReduction.toReduction, oracleReductionO, Reduction.run,
    oracleProverO, oracleVerifierO, OracleVerifier.toVerifier, Prover.run, Verifier.run,
    Prover.runToRound]
  simp only [simulateQ_optionT_lift, hMap]
  simp only [OptionT.lift, OptionT.mk, OptionT.run, bind_pure_comp, map_pure,
    Option.getM, monadLift_pure]
  rfl

variable (relIn : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn))
  (relOut : Set ((StmtOut × (∀ i, OStmtOut i)) × WitOut))

/-- The oracle-aware `ReduceClaim` variant satisfies perfect completeness for any relation whose
  pull-back along the (pure) statement specification holds. -/
theorem oracleReductionO_completeness (hMap : MapCoherent mapStmtO mapStmtO_spec)
    (hRel : ∀ stmtIn oStmtIn witIn,
      ((stmtIn, oStmtIn), witIn) ∈ relIn →
      ((mapStmtO_spec stmtIn oStmtIn, mapOStmt embedIdx hEq oStmtIn), mapWit stmtIn witIn) ∈
        relOut) :
    (oracleReductionO (oSpec := oSpec) (mapStmtO := mapStmtO) (mapStmtO_spec := mapStmtO_spec)
        (mapWit := mapWit) (embedIdx := embedIdx) (hEq := hEq)).perfectCompleteness
      init impl relIn relOut := by
  simp only [OracleReduction.perfectCompleteness, Reduction.perfectCompleteness,
    Reduction.completeness, Reduction.completenessFromRun, ENNReal.coe_zero, tsub_zero]
  intro ⟨stmtIn, oStmtIn⟩ witIn hIn
  simp only [oracleReductionO_run hMap]
  rw [ge_iff_le, one_le_probEvent_iff, probEvent_eq_one_iff]
  refine ⟨?_, ?_⟩
  · rw [OptionT.probFailure_eq, OptionT.run_mk]
    simp only [probFailure_eq_zero, zero_add]
    apply probOutput_eq_zero_of_not_mem_support
    simp only [support_bind, Set.mem_iUnion, not_exists]
    intro s _ hmem
    change none ∈ _root_.support
      (StateT.run' (simulateQ _ (pure (some ((default,
        ((mapStmtO_spec stmtIn oStmtIn, mapOStmt embedIdx hEq oStmtIn), mapWit stmtIn witIn)),
        (mapStmtO_spec stmtIn oStmtIn, mapOStmt embedIdx hEq oStmtIn))) :
          OracleComp _ _)) s) at hmem
    rw [simulateQ_pure] at hmem
    change none ∈ _root_.support
      (Prod.fst <$> (pure (some ((default,
        ((mapStmtO_spec stmtIn oStmtIn, mapOStmt embedIdx hEq oStmtIn), mapWit stmtIn witIn)),
        (mapStmtO_spec stmtIn oStmtIn, mapOStmt embedIdx hEq oStmtIn))) :
          StateT σ ProbComp _).run s) at hmem
    rw [StateT.run_pure] at hmem
    simp [map_pure] at hmem
  · intro x hx
    rw [OptionT.mem_support_iff] at hx
    simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hx
    obtain ⟨s, _, hx⟩ := hx
    change some x ∈ _root_.support
      (StateT.run' (simulateQ _ (pure (some ((default,
        ((mapStmtO_spec stmtIn oStmtIn, mapOStmt embedIdx hEq oStmtIn), mapWit stmtIn witIn)),
        (mapStmtO_spec stmtIn oStmtIn, mapOStmt embedIdx hEq oStmtIn))) :
          OracleComp _ _)) s) at hx
    rw [simulateQ_pure] at hx
    change some x ∈ _root_.support
      (Prod.fst <$> (pure (some ((default,
        ((mapStmtO_spec stmtIn oStmtIn, mapOStmt embedIdx hEq oStmtIn), mapWit stmtIn witIn)),
        (mapStmtO_spec stmtIn oStmtIn, mapOStmt embedIdx hEq oStmtIn))) :
          StateT σ ProbComp _).run s) at hx
    rw [StateT.run_pure] at hx
    simp only [map_pure, support_pure, Set.mem_singleton_iff, Option.some.injEq] at hx
    cases hx
    exact ⟨hRel stmtIn oStmtIn witIn hIn, rfl⟩

/-- The honest transcript distribution for the oracle-aware `ReduceClaim` variant is the
deterministic empty transcript. The oracle-aware statement map and witness map appear only in the
output data, never in the zero-round transcript. -/
theorem honestTranscriptDist_oracleReductionO_evalDist
    (hMap : MapCoherent mapStmtO mapStmtO_spec)
    (stmtIn : StmtIn) (oStmtIn : ∀ i, OStmtIn i) (witIn : WitIn) :
    evalDist (Reduction.honestTranscriptDist init impl
        (oracleReductionO (oSpec := oSpec) (mapStmtO := mapStmtO)
          (mapStmtO_spec := mapStmtO_spec) (mapWit := mapWit)
          (embedIdx := embedIdx) (hEq := hEq)).toReduction
        ⟨stmtIn, oStmtIn⟩ witIn) =
      evalDist (pure default : OptionT ProbComp (FullTranscript !p[])) := by
  apply evalDist_ext
  intro transcript
  classical
  unfold Reduction.honestTranscriptDist
  rw [oracleReductionO_run hMap]
  simp only [map_pure, OptionT.run_pure, simulateQ_pure, StateT.run'_eq, StateT.run_pure,
    bind_pure_comp]
  rw [OptionT.probOutput_eq, OptionT.probOutput_eq]
  simp [probOutput_map_const, HasEvalPMF.probFailure_eq_zero]

/-- The oracle-aware `ReduceClaim` variant is perfectly HVZK for any input relation under
`MapCoherent`: it has no messages or challenges, so the identity empty-transcript simulator matches
every honest transcript distribution. -/
theorem oracleReductionO_perfectHVZK (hMap : MapCoherent mapStmtO mapStmtO_spec)
    (relIn : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)) :
    OracleReduction.perfectHVZK init impl relIn
      (oracleReductionO (oSpec := oSpec) (mapStmtO := mapStmtO)
        (mapStmtO_spec := mapStmtO_spec) (mapWit := mapWit)
        (embedIdx := embedIdx) (hEq := hEq))
      Reduction.idTranscriptSimulator := by
  intro stmtIn witIn _
  exact (honestTranscriptDist_oracleReductionO_evalDist (oSpec := oSpec)
    (mapStmtO := mapStmtO) (mapStmtO_spec := mapStmtO_spec) (mapWit := mapWit)
    (embedIdx := embedIdx) (hEq := hEq) (init := init) (impl := impl) hMap
    stmtIn.1 stmtIn.2 witIn).symm

/-- Perfect HVZK implies statistical HVZK for the oracle-aware `ReduceClaim` variant at every
error budget. -/
theorem oracleReductionO_statisticalHVZK (hMap : MapCoherent mapStmtO mapStmtO_spec)
    (relIn : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)) (ε : NNReal) :
    OracleReduction.statisticalHVZK init impl relIn
      (oracleReductionO (oSpec := oSpec) (mapStmtO := mapStmtO)
        (mapStmtO_spec := mapStmtO_spec) (mapWit := mapWit)
        (embedIdx := embedIdx) (hEq := hEq))
      Reduction.idTranscriptSimulator ε :=
  (oracleReductionO_perfectHVZK (oSpec := oSpec) (mapStmtO := mapStmtO)
    (mapStmtO_spec := mapStmtO_spec) (mapWit := mapWit) (embedIdx := embedIdx)
    (hEq := hEq) (init := init) (impl := impl) hMap relIn).statisticalHVZK ε

/-- The oracle-aware `ReduceClaim` variant has an explicit perfect-HVZK simulator for any input
relation under `MapCoherent`. -/
theorem oracleReductionO_isHVZK (hMap : MapCoherent mapStmtO mapStmtO_spec)
    (relIn : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)) :
    OracleReduction.isHVZK init impl relIn
      (oracleReductionO (oSpec := oSpec) (mapStmtO := mapStmtO)
        (mapStmtO_spec := mapStmtO_spec) (mapWit := mapWit)
        (embedIdx := embedIdx) (hEq := hEq)) :=
  ⟨Reduction.idTranscriptSimulator,
    oracleReductionO_perfectHVZK (oSpec := oSpec) (mapStmtO := mapStmtO)
      (mapStmtO_spec := mapStmtO_spec) (mapWit := mapWit) (embedIdx := embedIdx)
      (hEq := hEq) (init := init) (impl := impl) hMap relIn⟩

/-- The oracle-aware `ReduceClaim` variant has statistical HVZK for any input relation and error
budget under `MapCoherent`. -/
theorem oracleReductionO_isStatHVZK (hMap : MapCoherent mapStmtO mapStmtO_spec)
    (relIn : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)) (ε : NNReal) :
    OracleReduction.isStatHVZK init impl relIn
      (oracleReductionO (oSpec := oSpec) (mapStmtO := mapStmtO)
        (mapStmtO_spec := mapStmtO_spec) (mapWit := mapWit)
        (embedIdx := embedIdx) (hEq := hEq)) ε :=
  (oracleReductionO_isHVZK (oSpec := oSpec) (mapStmtO := mapStmtO)
    (mapStmtO_spec := mapStmtO_spec) (mapWit := mapWit) (embedIdx := embedIdx)
    (hEq := hEq) (init := init) (impl := impl) hMap relIn).isStatHVZK ε

/-- The underlying non-oracle reduction of the oracle-aware `ReduceClaim` variant is perfectly HVZK
for any input relation under `MapCoherent`. -/
theorem oracleReductionO_toReduction_perfectHVZK
    (hMap : MapCoherent mapStmtO mapStmtO_spec)
    (relIn : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)) :
    Reduction.perfectHVZK init impl relIn
      (oracleReductionO (oSpec := oSpec) (mapStmtO := mapStmtO)
        (mapStmtO_spec := mapStmtO_spec) (mapWit := mapWit)
        (embedIdx := embedIdx) (hEq := hEq)).toReduction
      Reduction.idTranscriptSimulator :=
  oracleReductionO_perfectHVZK (oSpec := oSpec) (mapStmtO := mapStmtO)
    (mapStmtO_spec := mapStmtO_spec) (mapWit := mapWit) (embedIdx := embedIdx)
    (hEq := hEq) (init := init) (impl := impl) hMap relIn

/-- The underlying non-oracle reduction of the oracle-aware `ReduceClaim` variant is statistically
HVZK for any input relation and error budget under `MapCoherent`. -/
theorem oracleReductionO_toReduction_statisticalHVZK
    (hMap : MapCoherent mapStmtO mapStmtO_spec)
    (relIn : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)) (ε : NNReal) :
    Reduction.statisticalHVZK init impl relIn
      (oracleReductionO (oSpec := oSpec) (mapStmtO := mapStmtO)
        (mapStmtO_spec := mapStmtO_spec) (mapWit := mapWit)
        (embedIdx := embedIdx) (hEq := hEq)).toReduction
      Reduction.idTranscriptSimulator ε :=
  oracleReductionO_statisticalHVZK (oSpec := oSpec) (mapStmtO := mapStmtO)
    (mapStmtO_spec := mapStmtO_spec) (mapWit := mapWit) (embedIdx := embedIdx)
    (hEq := hEq) (init := init) (impl := impl) hMap relIn ε

/-- The underlying non-oracle reduction of the oracle-aware `ReduceClaim` variant has an explicit
perfect-HVZK simulator for any input relation under `MapCoherent`. -/
theorem oracleReductionO_toReduction_isHVZK
    (hMap : MapCoherent mapStmtO mapStmtO_spec)
    (relIn : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)) :
    Reduction.isHVZK init impl relIn
      (oracleReductionO (oSpec := oSpec) (mapStmtO := mapStmtO)
        (mapStmtO_spec := mapStmtO_spec) (mapWit := mapWit)
        (embedIdx := embedIdx) (hEq := hEq)).toReduction :=
  ⟨Reduction.idTranscriptSimulator,
    oracleReductionO_toReduction_perfectHVZK (oSpec := oSpec) (mapStmtO := mapStmtO)
      (mapStmtO_spec := mapStmtO_spec) (mapWit := mapWit) (embedIdx := embedIdx)
      (hEq := hEq) (init := init) (impl := impl) hMap relIn⟩

/-- The underlying non-oracle reduction of the oracle-aware `ReduceClaim` variant has statistical
HVZK for any input relation and error budget under `MapCoherent`. -/
theorem oracleReductionO_toReduction_isStatHVZK
    (hMap : MapCoherent mapStmtO mapStmtO_spec)
    (relIn : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn)) (ε : NNReal) :
    Reduction.isStatHVZK init impl relIn
      (oracleReductionO (oSpec := oSpec) (mapStmtO := mapStmtO)
        (mapStmtO_spec := mapStmtO_spec) (mapWit := mapWit)
        (embedIdx := embedIdx) (hEq := hEq)).toReduction ε :=
  ⟨Reduction.idTranscriptSimulator,
    oracleReductionO_toReduction_statisticalHVZK (oSpec := oSpec) (mapStmtO := mapStmtO)
      (mapStmtO_spec := mapStmtO_spec) (mapWit := mapWit) (embedIdx := embedIdx)
      (hEq := hEq) (init := init) (impl := impl) hMap relIn ε⟩

#print axioms ReduceClaim.honestTranscriptDist_oracleReductionO_evalDist
#print axioms ReduceClaim.oracleReductionO_perfectHVZK
#print axioms ReduceClaim.oracleReductionO_statisticalHVZK
#print axioms ReduceClaim.oracleReductionO_isHVZK
#print axioms ReduceClaim.oracleReductionO_isStatHVZK
#print axioms ReduceClaim.oracleReductionO_toReduction_perfectHVZK
#print axioms ReduceClaim.oracleReductionO_toReduction_statisticalHVZK
#print axioms ReduceClaim.oracleReductionO_toReduction_isHVZK
#print axioms ReduceClaim.oracleReductionO_toReduction_isStatHVZK

variable {mapWitInv : (StmtIn × (∀ i, OStmtIn i)) → WitOut → WitIn}

/-- The knowledge state function for the oracle-aware `ReduceClaim` variant. Mirrors
  `oracleKnowledgeStateFunction` but routes the verifier through
  `oracleVerifierO_toVerifier_run`. -/
def oracleKnowledgeStateFunctionO (hMap : MapCoherent mapStmtO mapStmtO_spec)
    (hRel : ∀ stmtIn oStmtIn witOut,
      ((mapStmtO_spec stmtIn oStmtIn, mapOStmt embedIdx hEq oStmtIn), witOut) ∈ relOut →
      ((stmtIn, oStmtIn), mapWitInv (stmtIn, oStmtIn) witOut) ∈ relIn) :
    (oracleVerifierO (oSpec := oSpec) (mapStmtO := mapStmtO) (embedIdx := embedIdx)
        (hEq := hEq)).KnowledgeStateFunction
      init impl relIn relOut (extractor mapWitInv) where
  toFun | ⟨0, _⟩ => fun ⟨stmtIn, oStmtIn⟩ _ witIn => ⟨⟨stmtIn, oStmtIn⟩, witIn⟩ ∈ relIn
  toFun_empty := fun stmtIn witIn => by simp
  toFun_next := fun m => Fin.elim0 m
  toFun_full := fun ⟨stmtIn, oStmtIn⟩ tr witOut => by
    intro h
    rw [oracleVerifierO_toVerifier_run hMap] at h
    rw [gt_iff_lt, probEvent_pos_iff] at h
    obtain ⟨x, hx, hrel⟩ := h
    rw [OptionT.mem_support_iff] at hx
    simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hx
    obtain ⟨s, _, hx⟩ := hx
    have key : (simulateQ impl
        (pure (mapStmtO_spec stmtIn oStmtIn, mapOStmt embedIdx hEq oStmtIn) :
          OptionT (OracleComp oSpec) (StmtOut × (∀ i, OStmtOut i)))).run' s =
        pure (some (mapStmtO_spec stmtIn oStmtIn, mapOStmt embedIdx hEq oStmtIn)) := by
      change (simulateQ impl
        (pure (some (mapStmtO_spec stmtIn oStmtIn, mapOStmt embedIdx hEq oStmtIn)) :
          OracleComp oSpec (Option (StmtOut × (∀ i, OStmtOut i))))).run' s = _
      rw [simulateQ_pure]
      change Prod.fst <$>
        (pure (some (mapStmtO_spec stmtIn oStmtIn, mapOStmt embedIdx hEq oStmtIn)) :
          StateT σ ProbComp _).run s = _
      rw [StateT.run_pure]; simp [map_pure]
    rw [key] at hx
    simp only [support_pure, Set.mem_singleton_iff] at hx
    cases (Option.some.inj hx)
    exact hRel stmtIn oStmtIn witOut hrel

/-- The oracle-aware `ReduceClaim` variant satisfies perfect round-by-round knowledge soundness.

Note that since there is no challenge round, all the work is done in the definition of the
knowledge state function. -/
theorem oracleVerifierO_rbrKnowledgeSoundness (hMap : MapCoherent mapStmtO mapStmtO_spec)
    (hRel : ∀ stmtIn oStmtIn witOut,
      ((mapStmtO_spec stmtIn oStmtIn, mapOStmt embedIdx hEq oStmtIn), witOut) ∈ relOut →
      ((stmtIn, oStmtIn), mapWitInv (stmtIn, oStmtIn) witOut) ∈ relIn) :
    (oracleVerifierO (oSpec := oSpec) (mapStmtO := mapStmtO) (embedIdx := embedIdx)
        (hEq := hEq)).rbrKnowledgeSoundness init impl
      relIn relOut 0 := by
  refine ⟨_, _, oracleKnowledgeStateFunctionO relIn relOut hMap hRel, ?_⟩
  simp only [ProtocolSpec.ChallengeIdx]
  exact fun _ _ _ i => Fin.elim0 i.1

end OracleReductionO

end ReduceClaim
