/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.Security.RoundByRound
import ArkLib.OracleReduction.Security.ZeroKnowledge

/-!
  # Simple (Oracle) Reduction: Check if a predicate / claim on a statement is satisfied

  This is a zero-round (oracle) reduction. There is no witness.

  1. Reduction version: the input relation becomes a predicate on the statement. Verifier checks
     this predicate, and returns the same statement if successful.

  2. Oracle reduction version: the input relation becomes an oracle computation having as oracles
     the oracle statements, and taking in the (non-oracle) statement as an input (i.e. via
     `ReaderT`), and returning a `Prop`. Verifier performs this oracle computation, and returns the
     same statement & oracle statement if successful.

  In both cases, the output relation is trivial (since the input relation has been checked by the
  verifier).

  Note: after the refactor (to disallow failure in `OracleComp`), this may become a special case
  of `ReduceClaim`.
-/

open OracleComp OracleInterface ProtocolSpec Function

namespace CheckClaim

variable {ι : Type} (oSpec : OracleSpec ι) (Statement : Type)

section Reduction

/-- The prover for the `CheckClaim` reduction. -/
@[inline, specialize]
def prover : Prover oSpec Statement Unit Statement Unit !p[] where
  PrvState := fun _ => Statement
  input := Prod.fst
  sendMessage := fun i => nomatch i
  receiveChallenge := fun i => nomatch i
  output := fun stmt => pure (stmt, ())

variable (pred : Statement → Prop) [DecidablePred pred]

/-- The verifier for the `CheckClaim` reduction. -/
@[inline, specialize]
def verifier : Verifier oSpec Statement Statement !p[] where
  verify := fun stmt _ => do guard (pred stmt); return stmt

/-- The reduction for the `CheckClaim` reduction. -/
@[inline, specialize]
def reduction : Reduction oSpec Statement Unit Statement Unit !p[] where
  prover := prover oSpec Statement
  verifier := verifier oSpec Statement pred

@[reducible, simp]
def relIn : Set (Statement × Unit) := { ⟨stmt, _⟩ | pred stmt }

@[reducible, simp]
def relOut : Set (Statement × Unit) := Set.univ

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- The `CheckClaim` reduction satisfies perfect completeness with respect to the predicate as the
  input relation, and the output relation being always true. -/
@[simp]
theorem reduction_completeness [Nonempty σ] [DecidableEq Statement] :
    (reduction oSpec Statement pred).perfectCompleteness init impl
    (relIn Statement pred) (relOut Statement) := by
  simp only [Reduction.perfectCompleteness, Reduction.completeness, Reduction.completenessFromRun, ENNReal.coe_zero, tsub_zero]
  intro stmt () valid
  simp only [relIn, Set.mem_setOf_eq] at valid
  -- valid : pred stmt
  -- First simplify the reduction run
  have hrun : (reduction oSpec Statement pred).run stmt () =
      (pure ((default, stmt, ()), stmt) :
        OptionT (OracleComp _) _) := by
    simp [reduction, Reduction.run, prover, verifier, Prover.run, Verifier.run,
          Prover.runToRound, guard, if_pos valid]; rfl
  simp only [hrun]
  -- Now identical to id_perfectCompleteness pattern
  rw [ge_iff_le, one_le_probEvent_iff, probEvent_eq_one_iff]
  refine ⟨?_, ?_⟩
  · rw [OptionT.probFailure_eq, OptionT.run_mk]
    simp only [probFailure_eq_zero, zero_add]
    apply probOutput_eq_zero_of_not_mem_support
    simp only [support_bind, Set.mem_iUnion, not_exists]
    intro s _ hmem
    -- Unfold OptionT.run on pure, then simulateQ_pure, then StateT
    change none ∈ _root_.support
      (StateT.run' (simulateQ _ (pure (some ((default, stmt, ()), stmt)) :
        OracleComp _ _)) s) at hmem
    rw [simulateQ_pure] at hmem
    change none ∈ _root_.support
      (Prod.fst <$> (pure (some ((default, stmt, ()), stmt)) :
        StateT σ ProbComp _).run s) at hmem
    rw [StateT.run_pure] at hmem
    simp [map_pure] at hmem
  · intro x hx
    rw [OptionT.mem_support_iff] at hx
    simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hx
    obtain ⟨s, _, hx⟩ := hx
    change some x ∈ _root_.support
      (StateT.run' (simulateQ _ (pure (some ((default, stmt, ()), stmt)) :
        OracleComp _ _)) s) at hx
    rw [simulateQ_pure] at hx
    change some x ∈ _root_.support
      (Prod.fst <$> (pure (some ((default, stmt, ()), stmt)) :
        StateT σ ProbComp _).run s) at hx
    rw [StateT.run_pure] at hx
    simp [map_pure, support_pure] at hx
    cases hx
    simp [relOut]

/-- The honest transcript distribution for a valid `CheckClaim` statement is the deterministic
empty transcript. This is the concrete zero-round core used by the HVZK wrappers below. -/
theorem honestTranscriptDist_reduction_evalDist
    (stmt : Statement) (hpred : pred stmt) :
    evalDist (Reduction.honestTranscriptDist init impl
        (reduction oSpec Statement pred) stmt ()) =
      evalDist (pure default : OptionT ProbComp (FullTranscript !p[])) := by
  apply evalDist_ext
  intro transcript
  classical
  unfold Reduction.honestTranscriptDist
  have hrun : (reduction oSpec Statement pred).run stmt () =
      (pure ((default, stmt, ()), stmt) : OptionT (OracleComp _) _) := by
    simp [reduction, Reduction.run, prover, verifier, Prover.run, Verifier.run,
          Prover.runToRound, guard, if_pos hpred]
    rfl
  simp only [hrun, map_pure, OptionT.run_pure, simulateQ_pure, StateT.run'_eq,
    StateT.run_pure, bind_pure_comp]
  rw [OptionT.probOutput_eq, OptionT.probOutput_eq]
  simp [probOutput_map_const, HasEvalPMF.probFailure_eq_zero]

/-- `CheckClaim` is perfectly HVZK for the predicate relation. The simulator is the identity
transcript simulator, since the real protocol has no messages or challenges. -/
theorem reduction_perfectHVZK :
    Reduction.perfectHVZK init impl (relIn Statement pred)
      (reduction oSpec Statement pred) Reduction.idTranscriptSimulator := by
  intro stmt wit hrel
  cases wit
  exact (honestTranscriptDist_reduction_evalDist oSpec Statement pred stmt hrel).symm

/-- Perfect HVZK implies statistical HVZK at every error budget. -/
theorem reduction_statisticalHVZK (ε : NNReal) :
    Reduction.statisticalHVZK init impl (relIn Statement pred)
      (reduction oSpec Statement pred) Reduction.idTranscriptSimulator ε :=
  (reduction_perfectHVZK oSpec Statement pred).statisticalHVZK ε

/-- `CheckClaim` has an explicit perfect-HVZK simulator. -/
theorem reduction_isHVZK :
    Reduction.isHVZK init impl (relIn Statement pred) (reduction oSpec Statement pred) :=
  ⟨Reduction.idTranscriptSimulator, reduction_perfectHVZK oSpec Statement pred⟩

/-- `CheckClaim` has statistical HVZK at every error budget. -/
theorem reduction_isStatHVZK (ε : NNReal) :
    Reduction.isStatHVZK init impl (relIn Statement pred) (reduction oSpec Statement pred) ε :=
  (reduction_isHVZK oSpec Statement pred).isStatHVZK ε

/-- The round-by-round extractor for the `CheckClaim` reduction. Trivial since the witness is
  `Unit`. -/
def extractor : Extractor.RoundByRound oSpec Statement Unit Unit !p[] (fun _ => Unit) where
  eqIn := rfl
  extractMid := fun i => Fin.elim0 i
  extractOut := fun _ _ witOut => witOut

/-- The knowledge state function for the `CheckClaim` reduction. Since there is no challenge round,
  the state function simply records whether the predicate holds on the statement. -/
def knowledgeStateFunction :
    (verifier oSpec Statement pred).KnowledgeStateFunction
      init impl (relIn Statement pred) (relOut Statement) (extractor oSpec Statement) where
  toFun | ⟨0, _⟩ => fun stmtIn _ _ => pred stmtIn
  toFun_empty := fun stmtIn witIn => by simp [relIn]
  toFun_next := fun m => Fin.elim0 m
  toFun_full := fun stmtIn tr witOut => by
    -- Bind `h` via `intro` (not as a lambda parameter) to avoid an expensive `isDefEq` check
    -- against the heavy `verifier.run` field type.
    intro h
    -- Goal: `pred stmtIn`. The verifier runs `do guard (pred stmtIn); return stmtIn`. The output is
    -- in the (trivial) output relation with positive probability only if the guard passes.
    show pred stmtIn
    by_contra hpred
    rw [gt_iff_lt, probEvent_pos_iff] at h
    obtain ⟨x, hx, _⟩ := h
    rw [OptionT.mem_support_iff] at hx
    simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hx
    obtain ⟨s, _, hx⟩ := hx
    -- `verifier.run stmtIn tr = do guard (pred stmtIn); return stmtIn`; with `¬ pred stmtIn` the
    -- guard fails, so the underlying option computation has support `{none}`, contradicting
    -- `some x ∈ support`.
    have hrun : (verifier oSpec Statement pred).run stmtIn tr =
        (OptionT.mk (pure none) : OptionT (OracleComp oSpec) Statement) := by
      simp only [verifier, Verifier.run, guard, if_neg hpred]
      rfl
    have key : (simulateQ impl
        ((verifier oSpec Statement pred).run stmtIn tr)).run' s =
        pure none := by
      rw [hrun]
      change (simulateQ impl (pure none : OracleComp oSpec (Option Statement))).run' s = _
      rw [simulateQ_pure]
      change Prod.fst <$> (pure (none : Option Statement) : StateT σ ProbComp _).run s = _
      rw [StateT.run_pure]; simp [map_pure]
    rw [key] at hx
    simp only [support_pure, Set.mem_singleton_iff] at hx
    exact absurd hx (by simp)

/-- The `CheckClaim` reduction satisfies perfect round-by-round knowledge soundness.

Note that since there is no challenge round, all the work is done in the definition of the
knowledge state function. -/
theorem verifier_rbr_knowledge_soundness :
    (verifier oSpec Statement pred).rbrKnowledgeSoundness init impl
      (relIn Statement pred) (relOut Statement) 0 := by
  refine ⟨_, _, knowledgeStateFunction oSpec Statement pred, ?_⟩
  simp only [ProtocolSpec.ChallengeIdx]
  exact fun _ _ _ i => Fin.elim0 i.1

#print axioms CheckClaim.honestTranscriptDist_reduction_evalDist
#print axioms CheckClaim.reduction_perfectHVZK
#print axioms CheckClaim.reduction_statisticalHVZK
#print axioms CheckClaim.reduction_isHVZK
#print axioms CheckClaim.reduction_isStatHVZK

end Reduction

section OracleReduction

variable {ιₛ : Type} (OStatement : ιₛ → Type) [∀ i, OracleInterface (OStatement i)]

/-- The oracle prover for the `CheckClaim` oracle reduction. -/
@[inline, specialize]
def oracleProver : OracleProver oSpec
    Statement OStatement Unit Statement OStatement Unit !p[] where
  PrvState := fun _ => Statement × (∀ i, OStatement i)
  input := Prod.fst
  sendMessage := fun i => nomatch i
  receiveChallenge := fun i => nomatch i
  output := fun stmt => pure (stmt, ())

variable (pred : ReaderT Statement (OracleComp [OStatement]ₒ) Prop)
  -- (hPred : ∀ stmt, NeverFail (pred stmt))

/-- The oracle verifier for the `CheckClaim` oracle reduction. -/
@[inline, specialize]
def oracleVerifier : OracleVerifier oSpec
    Statement OStatement Statement OStatement !p[] where
  verify := fun stmt _ => do let _ ← pred stmt; return stmt
  embed := Embedding.inl
  hEq := by intro i; simp

/-- The oracle reduction for the `CheckClaim` oracle reduction. -/
@[inline, specialize]
def oracleReduction : OracleReduction oSpec
    Statement OStatement Unit Statement OStatement Unit !p[] where
  prover := oracleProver oSpec Statement OStatement
  verifier := oracleVerifier oSpec Statement OStatement pred

variable {Statement} {OStatement}

-- @[reducible, simp]
-- def toRelInput : Set ((Statement × (∀ i, OStatement i)) × Unit) :=
--   { ⟨⟨stmt, oStmt⟩, _⟩ | simulateQ' (toOracleImpl OStatement oStmt) (pred stmt) (hPred stmt) }

-- -- theorem oracleProver_run

-- variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

-- /-- The `CheckClaim` reduction satisfies perfect completeness. -/
-- @[simp]
-- theorem oracleReduction_completeness (h : init.neverFails) :
--     (oracleReduction oSpec Statement OStatement pred).perfectCompleteness init impl
--     (toRelInput pred hPred) Set.univ := by
--   simp only [OracleReduction.perfectCompleteness, toRelInput, OracleReduction.toReduction,
--     oracleReduction, oracleProver, Nat.reduceAdd, Fin.isValue, MessageIdx, Message, ChallengeIdx,
--     Challenge, Fin.reduceLast, oracleVerifier, bind_pure_comp, OracleVerifier.toVerifier,
--     simulateQ_map, Embedding.inl_apply, eq_mpr_eq_cast, cast_eq, Functor.map_map,
--     Reduction.perfectCompleteness_eq_prob_one, Set.mem_setOf_eq, StateT.run'_eq, Set.mem_univ,
--     true_and, probEvent_eq_one_iff, probFailure_eq_zero_iff, neverFails_bind_iff, h,
--     neverFails_map_iff, support_bind, support_map, Set.mem_iUnion, Set.mem_image, Prod.exists,
--     exists_and_right, exists_eq_right, exists_prop, forall_exists_index, and_imp, Prod.forall,
--     Fin.forall_fin_zero_pi, Prod.mk.injEq]
--   simp only [Reduction.run, Prover.run, Verifier.run, toOracleImpl, simulateQ']
--   simp only [ChallengeIdx, Fin.reduceLast, Prover.runToRound_zero_of_prover_first, Fin.isValue,
--     bind_pure_comp, liftM_eq_liftComp, liftComp_map, Functor.map_map, pure_bind]

end OracleReduction

end CheckClaim
