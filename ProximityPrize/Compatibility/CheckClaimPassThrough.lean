/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.ProofSystem.Component.CheckClaim
import ArkLib.ToVCVio.Lemmas

/-!
# Compatibility laws for the canonical pure `CheckClaim` oracle reduction

The historical predicate argument labels the caller's relational condition. The canonical
oracle verifier forwards its input unchanged and does not execute that predicate.
-/

open OracleComp OracleSpec OracleInterface ProtocolSpec

namespace CheckClaim

variable {ι : Type} {oSpec : OracleSpec ι} {Statement : Type}
  {ιₛ : Type} {OStatement : ιₛ → Type} [∀ i, OracleInterface (OStatement i)]

omit [∀ i, OracleInterface (OStatement i)] in
/-- The canonical oracle prover forwards its input with the empty transcript. -/
lemma oracleProver_run (stmt : Statement) (oStmt : ∀ i, OStatement i) :
    (oracleProver oSpec Statement OStatement).run (stmt, oStmt) () =
      pure ((default : (!p[] : ProtocolSpec 0).FullTranscript), (stmt, oStmt), ()) := rfl

/-- The complete pure run forwards both copies of the input pair. -/
theorem oracleReduction_run_run (stmt : Statement) (oStmt : ∀ i, OStatement i) :
    ((oracleReduction oSpec Statement OStatement).toReduction.run (stmt, oStmt) ()).run =
      (pure (some ((default, (stmt, oStmt), ()), (stmt, oStmt))) : OracleComp _ _) := by
  simp only [oracleReduction, OracleReduction.toReduction, Reduction.run, oracleProver,
    oracleVerifier, OracleVerifier.toVerifier, Prover.run, Verifier.run, Prover.runToRound]
  rfl

/-- The compiled verifier has exactly its unchanged input as its possible result. -/
theorem support_toVerifier_run
    (_pred : ReaderT Statement (OracleComp [OStatement]ₒ) Prop)
    (stmt : Statement) (oStmt : ∀ i, OStatement i)
    (tr : (!p[] : ProtocolSpec 0).FullTranscript) :
    ∀ x ∈ support (((oracleVerifier oSpec Statement OStatement).toVerifier.run
        (stmt, oStmt) tr).run), x = some (stmt, oStmt) := by
  rw [oracleVerifier_toVerifier_run]
  simp

/-- The complete run has only the unchanged prover and verifier outputs in its support. -/
theorem support_oracleReduction_run
    (_pred : ReaderT Statement (OracleComp [OStatement]ₒ) Prop)
    (stmt : Statement) (oStmt : ∀ i, OStatement i) :
    ∀ x ∈ support ((((oracleReduction oSpec Statement OStatement).toReduction.run
        (stmt, oStmt) ()).run)),
      x = some ((default, (stmt, oStmt), ()), (stmt, oStmt)) := by
  rw [oracleReduction_run_run]
  simp

/-- Every relation is preserved by the canonical pass-through. -/
theorem oracleReduction_perfectCompleteness_any
    (_pred : ReaderT Statement (OracleComp [OStatement]ₒ) Prop)
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    (rel : Set ((Statement × (∀ i, OStatement i)) × Unit)) :
    (oracleReduction oSpec Statement OStatement).perfectCompleteness init impl rel rel := by
  simpa only [oracleRelOut, Set.ofPred_true, Set.inter_univ] using
    oracleReduction_completeness (oSpec := oSpec) init impl (fun _ _ => True) rel
      (fun _ _ _ => True.intro)

/-- A pass-through may weaken its output relation. The initialization premise is retained
for callers of the historical compatibility theorem. -/
theorem oracleReduction_perfectCompleteness_passthrough
    (pred : ReaderT Statement (OracleComp [OStatement]ₒ) Prop)
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {relIn relOut : Set ((Statement × (∀ i, OStatement i)) × Unit)}
    (_hInit : NeverFail init)
    (h : ∀ p, (p, ()) ∈ relIn → (p, ()) ∈ relOut) :
    (oracleReduction oSpec Statement OStatement).perfectCompleteness init impl relIn relOut := by
  apply Reduction.perfectCompleteness_of_run_support
  intro ⟨stmt, oStmt⟩ witIn hIn x hx
  cases witIn
  rw [oracleReduction_run_run, support_pure, Set.mem_singleton_iff] at hx
  subst x
  exact ⟨_, rfl, h _ hIn, rfl⟩

/-- The pass-through introduces no optional failure, even after shared-oracle simulation. -/
theorem oracleReduction_neverFails
    (_pred : ReaderT Statement (OracleComp [OStatement]ₒ) Prop)
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    (stmt : Statement) (oStmt : ∀ i, OStatement i) :
    prFail (OptionT.mk (do StateT.run' (simulateQ (QueryImpl.addLift impl challengeQueryImpl)
        (((oracleReduction oSpec Statement OStatement).toReduction.run
          (stmt, oStmt) ()).run)) (← init))) = 0 := by
  rw [oracleReduction_run_run]
  simp only [simulateQ_pure, StateT.run'_pure_lib]
  rw [OptionT.probFailure_mk_bind_eq_zero_iff]
  refine ⟨OracleComp.prFail_eq_zero init, ?_⟩
  intro _ _
  exact prFail_pure ((default, (stmt, oStmt), ()), (stmt, oStmt))

end CheckClaim

#print axioms CheckClaim.oracleReduction_run_run
#print axioms CheckClaim.oracleReduction_perfectCompleteness_any
#print axioms CheckClaim.oracleReduction_perfectCompleteness_passthrough
#print axioms CheckClaim.oracleReduction_neverFails
