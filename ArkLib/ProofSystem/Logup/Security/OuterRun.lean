/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Protocol
import ArkLib.ProofSystem.Logup.Sumcheck.SumcheckPolynomial

/-!
# Closed form of the compiled outer LogUp verifier (issue #13)

This file characterizes the outer LogUp verifier's compiled run: simulating
`outerVerifier.verify` against concrete oracle statements and prover messages (via
`OracleInterface.simOracle2`) collapses every table query of the pole-scan loop to a pure
Lagrange evaluation, leaving the query-free `OptionT` computation

  `if (∀ u, x + t(u) ≠ 0) then pure stmtOut else failure`.

This is the load-bearing verifier-side lemma for outer-phase completeness: composed with the
honest prover's run, the only failure mode of the outer phase is the pole event bounded by
`probEvent_pole_le` in `Security/Completeness.lean`.

## Transport lemmas

The `simulateQ`-over-`OptionT` transport lemmas (`pure`/`failure`/`guard`/`forIn` and the
`forIn`-of-guards collapse) are re-derived here. Canonical copies exist in
`ToyProblem/Spec/General.lean`, but that module is currently unbuildable (issue #35), and the
`Binius/BinaryBasefold/QueryPhase.lean` precedent likewise re-derives them locally for
self-containment.
-/

open scoped NNReal ENNReal
open OracleComp ProtocolSpec

namespace Logup

/-! ## `simulateQ` transport lemmas over `OptionT (OracleComp _)` -/

section SimulateQTransport
variable {ι' : Type} {spec : OracleSpec ι'} {m : Type → Type} [Monad m] [LawfulMonad m]
variable {α β : Type}

/-- `simulateQ` commutes with `OptionT.pure`. -/
theorem simulateQ_optionT_pure' (impl : QueryImpl spec m) (b : β) :
    simulateQ impl (pure b : OptionT (OracleComp spec) β) = (pure b : OptionT m β) := by
  rw [show (pure b : OptionT (OracleComp spec) β) = OptionT.lift (pure b)
        from (OptionT.lift_pure b).symm]
  rw [simulateQ_optionT_lift, simulateQ_pure, OptionT.lift_pure]

omit [LawfulMonad m] in
/-- `simulateQ` commutes with `OptionT` `failure`. -/
theorem simulateQ_optionT_failure' (impl : QueryImpl spec m) :
    simulateQ impl (failure : OptionT (OracleComp spec) β) = (failure : OptionT m β) := by
  rw [OracleComp.failure_def]
  apply OptionT.ext
  simp only [OptionT.fail]
  rfl

/-- `simulateQ` of a query-free `guard` is the (target-monad) `if`. -/
theorem simulateQ_optionT_guard' (impl : QueryImpl spec m) (P : Prop) [Decidable P] :
    simulateQ impl (guard P : OptionT (OracleComp spec) PUnit)
      = (if P then pure PUnit.unit else failure : OptionT m PUnit) := by
  rw [guard_eq]
  by_cases hP : P
  · rw [if_pos hP, if_pos hP, simulateQ_optionT_pure']
  · rw [if_neg hP, if_neg hP, simulateQ_optionT_failure']

/-- `simulateQ` commutes with `forIn` over a list in `OptionT (OracleComp …)`. -/
theorem simulateQ_optionT_forIn' (impl : QueryImpl spec m)
    (l : List α) (f : α → β → OptionT (OracleComp spec) (ForInStep β))
    (g : α → β → OptionT m (ForInStep β))
    (hg : ∀ a b, g a b = simulateQ impl (f a b)) :
    ∀ init : β,
      simulateQ impl (forIn l init f : OptionT (OracleComp spec) β)
        = (forIn l init g : OptionT m β) := by
  induction l with
  | nil =>
    intro init
    rw [List.forIn_nil, List.forIn_nil, simulateQ_optionT_pure']
  | cons a l ih =>
    intro init
    rw [List.forIn_cons, List.forIn_cons, simulateQ_optionT_bind, hg]
    refine bind_congr ?_
    intro step
    cases step with
    | done b => exact simulateQ_optionT_pure' impl b
    | yield b => exact ih b

omit [LawfulMonad m] in
/-- A `forIn` over a list whose body is `guard (Q a)` then `yield ()` collapses to
`if (∀ a ∈ l, Q a) then pure () else failure`: the pole-scan loop accepts iff every
per-element guard passes. -/
theorem forIn_guard_eq' (l : List α) (Q : α → Prop) [∀ a, Decidable (Q a)]
    (body : α → PUnit → OptionT (OracleComp spec) (ForInStep PUnit))
    (hbody : ∀ a u, body a u = (guard (Q a) >>= fun _ => pure (ForInStep.yield PUnit.unit))) :
    (forIn l PUnit.unit body : OptionT (OracleComp spec) PUnit)
      = (if (∀ a ∈ l, Q a) then pure PUnit.unit else failure) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.forIn_cons, hbody]
    by_cases hQa : Q a
    · rw [guard_eq, if_pos hQa]
      simp only [pure_bind]
      rw [ih]
      by_cases hrest : (∀ b ∈ l, Q b)
      · rw [if_pos hrest, if_pos]
        intro b hb
        rcases List.mem_cons.mp hb with h | h
        · exact h ▸ hQa
        · exact hrest b h
      · rw [if_neg hrest, if_neg (fun hall =>
          hrest (fun b hb => hall b (List.mem_cons_of_mem a hb)))]
    · rw [guard_eq, if_neg hQa,
        if_neg (fun hall => hQa (hall a (List.mem_cons_self)))]
      simp [failure_bind]

end SimulateQTransport

/-! ## `simOracle2` query collapse, LEFT (oracle-statement) family -/

section SimOracle2Query
open OracleInterface
variable {ιₒ : Type} {oSpec : OracleSpec ιₒ}
  {ι₁ : Type} {T₁ : ι₁ → Type} [∀ i, OracleInterface (T₁ i)]
  {ι₂ : Type} {T₂ : ι₂ → Type} [∀ i, OracleInterface (T₂ i)]

/-- `simOracle2` oracle-statement-query collapse (`OracleComp` form), LEFT (oracle) family. -/
lemma simulateQ_simOracle2_leftQuery_oc' (t₁ : ∀ i, T₁ i) (t₂ : ∀ i, T₂ i)
    (qm : ([T₁]ₒ).Domain) :
    simulateQ (OracleInterface.simOracle2 oSpec t₁ t₂)
      (liftM (([T₁]ₒ).query qm) : OracleComp (oSpec + ([T₁]ₒ + [T₂]ₒ)) _)
      = (pure (OracleInterface.answer (t₁ qm.1) qm.2) : OracleComp oSpec _) := by
  change simulateQ (OracleInterface.simOracle2 oSpec t₁ t₂)
      (liftM ((oSpec + ([T₁]ₒ + [T₂]ₒ)).query (Sum.inr (Sum.inl qm)))) = _
  rw [simulateQ_spec_query]
  simp only [OracleInterface.simOracle2, QueryImpl.addLift_def, QueryImpl.add_apply_inr,
    QueryImpl.liftTarget_apply]
  change liftM (OracleInterface.simOracle0 T₁ t₁ qm) = _
  simp only [OracleInterface.simOracle0]
  rfl

/-- Verify-body oracle-statement-query collapse (LEFT family), `OptionT` form. -/
lemma simulateQ_simOracle2_leftQuery_optionT' (t₁ : ∀ i, T₁ i) (t₂ : ∀ i, T₂ i)
    (qm : ([T₁]ₒ).Domain) :
    (simulateQ (OracleInterface.simOracle2 oSpec t₁ t₂)
      (OptionT.lift (OracleComp.liftComp (OracleComp.lift (OracleSpec.query qm))
        (oSpec + ([T₁]ₒ + [T₂]ₒ))))
      : OptionT (OracleComp oSpec) _)
      = (pure (OracleInterface.answer (t₁ qm.1) qm.2) : OptionT (OracleComp oSpec) _) := by
  erw [simulateQ_optionT_lift]
  rw [OracleComp.liftComp_query]
  simp only [OracleQuery.input_query, OracleQuery.cont_query, id_map]
  rw [simulateQ_simOracle2_leftQuery_oc']
  rfl

end SimOracle2Query

/-! ## Outer LogUp verifier closed form -/

section OuterRun

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)]
variable (n M : ℕ)
variable (params : ProtocolParams M)

/-- The outer `x` challenge, read off a challenge assignment (definitional repackaging). -/
def chalX (chal : ∀ i, (outerPSpec F n params).Challenge i) : F := chal ⟨1, rfl⟩

/-- The outer batching challenge, read off a challenge assignment. -/
def chalBatch (chal : ∀ i, (outerPSpec F n params).Challenge i) :
    BatchingChallenge F n params.numGroups := chal ⟨3, rfl⟩

/-- Querying a Lagrange-form multilinear oracle at a hypercube sign point returns the row value
(the Lagrange kernel is a delta on the hypercube, `lagrangeKernel_signPoint`). -/
theorem answer_signPoint (t : MultilinearOracle F n) (u : Hypercube n) :
    OracleInterface.answer t (signPoint F u) = evalOnHypercube t u := by
  classical
  have hSigns : (-1 : F) ≠ 1 := Fact.out
  change (∑ v : Hypercube n, t v * lagrangeKernel F v (signPoint F u)) = t u
  rw [Finset.sum_eq_single u]
  · simp [lagrangeKernel_signPoint F n hSigns]
  · intro v _ hv
    simp [lagrangeKernel_signPoint F n hSigns, hv]
  · intro h
    exact False.elim (h (Finset.mem_univ u))

set_option maxHeartbeats 2000000 in
/-- **Closed form of the compiled outer LogUp verifier.** Simulating
`outerVerifier.verify` against the honest oracle statements and prover messages collapses the
pole-scan loop's table queries, leaving `if (no pole hit) then pure stmtOut else failure`. -/
theorem simulateQ_outerVerify_eq (stmt : StmtIn F n M) (oStmt : ∀ i, OStmtIn F n M i)
    (chal : ∀ i, (outerPSpec F n params).Challenge i)
    (msgs : ∀ i, (outerPSpec F n params).Message i) :
    simulateQ (OracleInterface.simOracle2 oSpec oStmt msgs)
      ((outerVerifier oSpec F n M params).verify stmt chal)
      = (if ∀ u : Hypercube n,
            chalX F n M params chal + evalOnHypercube (tableOracle oStmt) u ≠ 0
          then (pure { xChallenge := chalX F n M params chal,
                       zChallenge := (chalBatch F n M params chal).1,
                       batchingScalars := (chalBatch F n M params chal).2 }
                : OptionT (OracleComp oSpec) (StmtAfterOuter F n M params))
          else failure) := by
  unfold outerVerifier
  dsimp only
  rw [simulateQ_optionT_bind]
  rw [simulateQ_optionT_forIn' (impl := OracleInterface.simOracle2 oSpec oStmt msgs)
    (g := fun (u : Hypercube n) (_ : PUnit) =>
      (guard (chalX F n M params chal + evalOnHypercube (tableOracle oStmt) u ≠ 0) >>=
        fun _ => pure (ForInStep.yield PUnit.unit)))]
  swap
  · -- forIn body collapse: the table query collapses to `pure (answer …)`.
    intro u _
    symm
    rw [simulateQ_optionT_bind]
    erw [simulateQ_simOracle2_leftQuery_optionT' (T₁ := OStmtIn F n M)
      (T₂ := (outerPSpec F n params).Message) (oSpec := oSpec) oStmt msgs
      (⟨InputOracleIdx.table, signPoint F u⟩ : [OStmtIn F n M]ₒ.Domain)]
    dsimp only [Sigma.fst, Sigma.snd]
    erw [pure_bind]
    rw [simulateQ_optionT_bind, simulateQ_optionT_guard', simulateQ_optionT_pure']
    rw [answer_signPoint]
    rfl
  rw [forIn_guard_eq' (l := Finset.univ.toList)
      (Q := fun u : Hypercube n =>
        chalX F n M params chal + evalOnHypercube (tableOracle oStmt) u ≠ 0)]
  swap
  · intro a u
    rfl
  have hall : (∀ u ∈ (Finset.univ : Finset (Hypercube n)).toList,
        chalX F n M params chal + evalOnHypercube (tableOracle oStmt) u ≠ 0)
      ↔ (∀ u : Hypercube n,
        chalX F n M params chal + evalOnHypercube (tableOracle oStmt) u ≠ 0) :=
    ⟨fun h u => h u (Finset.mem_toList.mpr (Finset.mem_univ u)), fun h u _ => h u⟩
  by_cases hP : ∀ u : Hypercube n,
      chalX F n M params chal + evalOnHypercube (tableOracle oStmt) u ≠ 0
  · rw [if_pos (hall.mpr hP), if_pos hP, pure_bind, simulateQ_optionT_pure']
    rfl
  · rw [if_neg (fun h => hP (hall.mp h)), if_neg hP, failure_bind]

end OuterRun

end Logup

/- Axiom audit for the compiled outer LogUp verifier closed form. -/
#print axioms Logup.answer_signPoint
#print axioms Logup.forIn_guard_eq'
#print axioms Logup.simulateQ_optionT_forIn'
#print axioms Logup.simulateQ_outerVerify_eq
