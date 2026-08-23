/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Spartan.TightFinalLeaf
import ArkLib.ToVCVio.OracleComp.SimSemantics.SimulateQ

/-!
# The `finalCheckTight` completeness leaf (#329, B7 step 4)

Completeness of the tight chain's terminal `CheckClaim` phase: the oracle `CheckClaim`
**never rejects** (its predicate's `Prop` is discarded by `let _ ←` at the oracle level) and
passes the statement/oracle-statement pair through unchanged, so the honest relation is
preserved verbatim.

Unlike the binding-free `finalCheck` leaf (`FinalCheckLeafComplete.lean`), the tight terminal
predicate `tightFinalPredicate` makes *symbolically many* oracle queries
(`finalExpectedClaimFromOracles` folds over `2 ^ pp.ℓ_n` cube points), so the honest run does
**not** collapse to a literal `pure` by `rfl`. Instead this module proves **pred-generic
support collapses** for any `CheckClaim` oracle reduction:

* `CheckClaim.support_toVerifier_run` — every output of the compiled verifier run is
  `some (stmt, oStmt)`: the lifted predicate enters the run through (a composite of)
  `OptionT.lift`, so it is always `some`-wrapped and its value is discarded; the only
  `OptionT` failure entry points (`guard`/`failure`) are absent.
* `CheckClaim.support_oracleReduction_run` — the same collapse for the full honest
  reduction run (deterministic prover, default transcript).
* `CheckClaim.oracleReduction_perfectCompleteness_any` — pred-generic perfect completeness
  from **any** input relation back to itself.

The instance-path obstruction that killed the run-*equation* route (the do-notation `liftM`
elaborates through a composite `MonadLiftT` chain of `simulateQ`-based `OptionT` hops that no
`rw`/`simp` pattern matches) is dissolved by working at the **support** level: the chain is
exposed once with `dsimp only [liftM, MonadLiftT.monadLift, MonadLift.monadLift]`, and the
resulting `simulateQ` heads are discharged by *applying* semantic lemmas
(`support_simulateQ_subset'`, defeq unification) rather than rewriting.

These are instantiated at the tight terminal check as `finalCheckTight_run_support`,
`finalCheckTight_neverFails`, `finalCheckTight_perfectCompleteness_any`, and
`finalCheckTight_perfectCompleteness` (at `relIn = relOut = tightFinalRelOut`), the
completeness leaf for the tight composition of `TightComposedFull.lean`.

**Honesty note.** As with all `CheckClaim` phases in this chain, the verifier *discards* the
predicate's truth value, so the completeness content here is totality (no failure) plus
prover/verifier output agreement; the algebraic content of the terminal identities lives in
the relation chain (`tightFinalRelOut`), which this leaf carries through unchanged.
-/

open OracleComp OracleSpec OracleInterface ProtocolSpec

universe u v

namespace CheckClaim

/-! ## Generic support transport lemmas

These are applied (not rewritten), so they unify up to definitional unfolding of
`OptionT.run`/`OptionT.mk` and the monad-lift instance chains. -/

/-- Outputs of a simulated computation (into another `OracleComp`) are outputs of the original
computation. `OracleComp`-target analogue of `support_simulateQ_run'_subset`. -/
private lemma support_simulateQ_subset' {ι₁ : Type u} {ι₂ : Type v}
    {spec : OracleSpec ι₁} {spec' : OracleSpec ι₂}
    (impl : QueryImpl spec (OracleComp spec')) {α : Type} (oa : OracleComp spec α) :
    support (simulateQ impl oa) ⊆ support oa := by
  intro y hy
  induction oa using OracleComp.inductionOn generalizing y with
  | pure x => simpa [simulateQ_pure] using hy
  | query_bind t oa ih =>
      simp only [simulateQ_bind, simulateQ_query, support_bind, Set.mem_iUnion] at hy ⊢
      aesop

/-- A simulated `some`-wrapped computation only outputs `some`. -/
private lemma head_some {ι₁ : Type u} {ι₂ : Type v}
    {spec : OracleSpec ι₁} {spec' : OracleSpec ι₂}
    (impl : QueryImpl spec (OracleComp spec')) {γ : Type} (Y : OracleComp spec γ)
    {o : Option γ}
    (h : o ∈ support (simulateQ impl (Y >>= fun x => pure (some x)))) :
    ∃ y, o = some y := by
  have h' := support_simulateQ_subset' impl _ h
  simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at h'
  obtain ⟨y, -, rfl⟩ := h'
  exact ⟨y, rfl⟩

/-- A simulated `pure (some b)` only outputs `some b`. -/
private lemma mem_support_pure_optionT {ι₁ : Type u} {ι₂ : Type v}
    {spec : OracleSpec ι₁} {spec' : OracleSpec ι₂}
    (impl : QueryImpl spec (OracleComp spec')) {γ : Type} (b : γ) {o : Option γ}
    (h : o ∈ support (simulateQ impl (pure (some b) : OracleComp spec (Option γ)))) :
    o = some b := by
  rw [simulateQ_pure] at h
  simpa using h

/-- Membership in the support of a `pure` pins the value. Applied (defeq-unified) against
computations that reduce to `pure` definitionally (e.g. `Fin.induction` at round `0`). -/
private lemma mem_support_pure_eq {ι₁ : Type u} {spec : OracleSpec ι₁}
    {α : Type} {b c : α} (h : c ∈ support (pure b : OracleComp spec α)) : c = b := by
  simpa using h

/-- `OptionT`-level probability-one bridge with sampled initial state: if every output of the
underlying computation is a `some` satisfying `P`, the simulated experiment satisfies `P` with
probability one. Init-sampling version of `OptionT.probEvent_eq_one_of_simulateQ_support`. -/
private lemma probEvent_eq_one_of_support_init
    {ι₁ σ α : Type} {spec : OracleSpec ι₁}
    (impl : QueryImpl spec (StateT σ ProbComp)) (init : ProbComp σ)
    (oa : OracleComp spec (Option α)) (P : α → Prop)
    (h : ∀ x ∈ support oa, ∃ a, x = some a ∧ P a) :
    Pr[P | OptionT.mk (do (simulateQ impl oa).run' (← init))] = 1 := by
  letI := Classical.decPred P
  rw [probEvent_eq_one_iff]
  constructor
  · rw [OptionT.probFailure_eq, OptionT.run_mk]
    have hfail : Pr[⊥ | (do (simulateQ impl oa).run' (← init) : ProbComp _)] = 0 :=
      HasEvalPMF.probFailure_eq_zero _
    rw [hfail, _root_.zero_add]
    refine probOutput_eq_zero_of_not_mem_support fun hnone => ?_
    simp only [support_bind, Set.mem_iUnion] at hnone
    obtain ⟨s, -, hnone⟩ := hnone
    have hmem := _root_.support_simulateQ_run'_subset impl oa s hnone
    obtain ⟨a, ha, -⟩ := h none hmem
    cases ha
  · intro y hy
    rw [OptionT.mem_support_iff] at hy
    simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hy
    obtain ⟨s, -, hy⟩ := hy
    obtain ⟨a, ha, hP⟩ := h (some y) (_root_.support_simulateQ_run'_subset impl oa s hy)
    cases ha
    exact hP

/-- `probFailure` version of the bridge: if every output of the underlying computation is a
`some`, the simulated experiment never fails. -/
private lemma probFailure_eq_zero_of_support_init
    {ι₁ σ α : Type} {spec : OracleSpec ι₁}
    (impl : QueryImpl spec (StateT σ ProbComp)) (init : ProbComp σ)
    (oa : OracleComp spec (Option α))
    (h : ∀ x ∈ support oa, ∃ a, x = some a) :
    Pr[⊥ | OptionT.mk (do (simulateQ impl oa).run' (← init))] = 0 := by
  rw [OptionT.probFailure_eq, OptionT.run_mk]
  have hfail : Pr[⊥ | (do (simulateQ impl oa).run' (← init) : ProbComp _)] = 0 :=
    HasEvalPMF.probFailure_eq_zero _
  rw [hfail, _root_.zero_add]
  refine probOutput_eq_zero_of_not_mem_support fun hnone => ?_
  simp only [support_bind, Set.mem_iUnion] at hnone
  obtain ⟨s, -, hnone⟩ := hnone
  have hmem := _root_.support_simulateQ_run'_subset impl oa s hnone
  obtain ⟨a, ha⟩ := h none hmem
  cases ha

variable {ι : Type} {oSpec : OracleSpec ι} {Statement : Type}
  {ιₛ : Type} {OStatement : ιₛ → Type} [∀ i, OracleInterface (OStatement i)]
  (pred : ReaderT Statement (OracleComp [OStatement]ₒ) Prop)

/-! ## The pred-generic run collapses -/

/-- **The pred-generic support collapse for the compiled `CheckClaim` oracle verifier**: the
run only ever outputs `some (stmt, oStmt)` — there is no failure entry point, and the
predicate's (simulated, `some`-wrapped) value is discarded. -/
theorem support_toVerifier_run (stmt : Statement) (oStmt : ∀ i, OStatement i)
    (tr : (!p[] : ProtocolSpec 0).FullTranscript) :
    ∀ x ∈ support (((oracleVerifier oSpec Statement OStatement pred).toVerifier.run
        (stmt, oStmt) tr).run), x = some (stmt, oStmt) := by
  intro x hx
  simp only [Verifier.run, OracleVerifier.toVerifier, oracleVerifier] at hx
  rw [OptionT.run_bind] at hx
  dsimp only [liftM, MonadLiftT.monadLift, MonadLift.monadLift] at hx
  simp only [OptionT.run_mk, OptionT.run_lift, simulateQ_bind, simulateQ_pure,
    Option.elimM, support_bind, Set.mem_iUnion] at hx
  rw [simulateQ_optionT_bind] at hx
  simp only [OptionT.run_bind, Option.elimM, support_bind, Set.mem_iUnion] at hx
  obtain ⟨i, ⟨i1, hi1, hi⟩, hxm⟩ := hx
  obtain ⟨y, rfl⟩ := head_some _ _ hi1
  rw [Option.elim_some] at hi
  have hstmt := mem_support_pure_optionT _ _ hi
  subst hstmt
  rw [Option.elim_some] at hxm
  rw [OptionT.run_pure] at hxm
  simp only [support_pure, Set.mem_singleton_iff] at hxm
  subst hxm
  rfl

/-- **The pred-generic support collapse for the full honest `CheckClaim` oracle reduction**:
the run only ever outputs the default transcript together with the unchanged
statement/oracle-statement pair (from both prover and verifier). -/
theorem support_oracleReduction_run (stmt : Statement) (oStmt : ∀ i, OStatement i) :
    ∀ x ∈ support ((((oracleReduction oSpec Statement OStatement pred).toReduction.run
        (stmt, oStmt) ()).run)),
      x = some ((default, (stmt, oStmt), ()), (stmt, oStmt)) := by
  intro x hx
  simp only [oracleReduction, OracleReduction.toReduction, oracleProver, Reduction.run,
    Prover.run, Prover.runToRound] at hx
  rw [OptionT.run_bind] at hx
  dsimp only [liftM, MonadLiftT.monadLift, MonadLift.monadLift] at hx
  simp only [OptionT.run_mk, OptionT.run_lift, simulateQ_bind, simulateQ_pure,
    Option.elimM, support_bind, Set.mem_iUnion, OptionT.run_bind] at hx
  obtain ⟨i, ⟨i1, ⟨i0, hi0, ⟨i2, hi2, hi1⟩⟩, hii⟩, hxm⟩ := hx
  have hi0' := mem_support_pure_eq hi0
  subst hi0'
  rw [OracleComp.liftComp_pure] at hi2
  have hi2' := mem_support_pure_eq hi2
  subst hi2'
  have hi1' := mem_support_pure_eq hi1
  subst hi1'
  have hii' := mem_support_pure_eq hii
  subst hii'
  rw [Option.elim_some] at hxm
  simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hxm
  obtain ⟨o, ⟨v, hv, rfl⟩, hxm⟩ := hxm
  have hv' := support_toVerifier_run pred stmt oStmt _ v (support_simulateQ_subset' _ _ hv)
  subst hv'
  rw [Option.elim_some] at hxm
  simp only [Option.getM, OptionT.run_pure, support_bind, support_pure, Set.mem_iUnion,
    Set.mem_singleton_iff] at hxm
  obtain ⟨o, rfl, hxm⟩ := hxm
  rw [Option.elim_some] at hxm
  exact mem_support_pure_eq hxm

/-! ## The pred-generic completeness -/

/-- **Pred-generic perfect completeness of the oracle `CheckClaim`**: any input relation is
carried to itself — the statement and oracle statements pass through unchanged, and the
verifier never fails (the predicate's value is discarded). Strongest relation-carrying form;
consumers wanting a weaker output relation specialize via output-relation monotonicity. -/
theorem oracleReduction_perfectCompleteness_any {σ : Type} {init : ProbComp σ}
    {impl : QueryImpl oSpec (StateT σ ProbComp)}
    (rel : Set ((Statement × (∀ i, OStatement i)) × Unit)) :
    (oracleReduction oSpec Statement OStatement pred).perfectCompleteness init impl rel rel := by
  unfold OracleReduction.perfectCompleteness
  simp only [Reduction.perfectCompleteness, Reduction.completeness, Reduction.completenessFromRun,
    ENNReal.coe_zero, tsub_zero]
  intro ⟨stmt, oStmt⟩ ⟨⟩ hIn
  rw [ge_iff_le, one_le_probEvent_iff]
  refine probEvent_eq_one_of_support_init _ _ _ _ ?_
  intro y hy
  have hval := support_oracleReduction_run pred stmt oStmt y hy
  subst hval
  exact ⟨_, rfl, hIn, rfl⟩

/-- **Pred-generic never-failure of the oracle `CheckClaim`** in the standard completeness
experiment: the honest run has failure probability zero. -/
theorem oracleReduction_neverFails {σ : Type} {init : ProbComp σ}
    {impl : QueryImpl oSpec (StateT σ ProbComp)}
    (stmt : Statement) (oStmt : ∀ i, OStatement i) :
    Pr[⊥ | OptionT.mk (do StateT.run' (simulateQ (QueryImpl.addLift impl challengeQueryImpl)
        (((oracleReduction oSpec Statement OStatement pred).toReduction.run
          (stmt, oStmt) ()).run)) (← init))] = 0 := by
  refine probFailure_eq_zero_of_support_init _ _ _ fun y hy => ?_
  exact ⟨_, support_oracleReduction_run pred stmt oStmt y hy⟩

end CheckClaim

namespace Spartan.Spec.Bricks

set_option linter.unusedSectionVars false

noncomputable section

variable {R : Type 0} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] [Inhabited R]
  [SampleableType R] (pp : PublicParams)

variable {ι : Type} (oSpec : OracleSpec ι)

/-! ## Instantiation at the tight terminal check -/

/-- **The tight terminal check's run support collapse**: the honest run only outputs the
default transcript and the unchanged statement/oracle-statement pair. -/
theorem finalCheckTight_run_support
    (stmt : Statement.AfterSecondSumcheckWithTarget R pp)
    (oStmt : ∀ i, OracleStatement.AfterLinearCombination R pp i) :
    ∀ x ∈ support ((((finalCheckTight (R := R) pp oSpec).toReduction.run
        (stmt, oStmt) ()).run)),
      x = some ((default, (stmt, oStmt), ()), (stmt, oStmt)) :=
  CheckClaim.support_oracleReduction_run (tightFinalPredicate pp) stmt oStmt

/-- **The tight terminal check never fails** in the standard completeness experiment. -/
theorem finalCheckTight_neverFails {σ : Type} {init : ProbComp σ}
    {impl : QueryImpl oSpec (StateT σ ProbComp)}
    (stmt : Statement.AfterSecondSumcheckWithTarget R pp)
    (oStmt : ∀ i, OracleStatement.AfterLinearCombination R pp i) :
    Pr[⊥ | OptionT.mk (do StateT.run' (simulateQ (QueryImpl.addLift impl challengeQueryImpl)
        (((finalCheckTight (R := R) pp oSpec).toReduction.run
          (stmt, oStmt) ()).run)) (← init))] = 0 :=
  CheckClaim.oracleReduction_neverFails (tightFinalPredicate pp) stmt oStmt

/-- **`finalCheckTight` is perfectly complete from any input relation back to itself**
(zero-round; the statement and oracle statements are forwarded unchanged). The strongest
relation-carrying form, trivializing downstream seam welds. -/
theorem finalCheckTight_perfectCompleteness_any {σ : Type} {init : ProbComp σ}
    {impl : QueryImpl oSpec (StateT σ ProbComp)}
    (rel : Set (((Statement.AfterSecondSumcheckWithTarget R pp) ×
      (∀ i, OracleStatement.AfterLinearCombination R pp i)) × Unit)) :
    (finalCheckTight (R := R) pp oSpec).perfectCompleteness init impl rel rel :=
  CheckClaim.oracleReduction_perfectCompleteness_any (tightFinalPredicate pp) rel

/-- **The tight terminal completeness leaf `h₈`**: perfect completeness of the tight chain's
zero-round terminal `CheckClaim`, at `relIn = relOut = tightFinalRelOut` — the tight final
output relation is carried through unchanged. -/
theorem finalCheckTight_perfectCompleteness {σ : Type} {init : ProbComp σ}
    {impl : QueryImpl oSpec (StateT σ ProbComp)} :
    (finalCheckTight (R := R) pp oSpec).perfectCompleteness init impl
      (tightFinalRelOut (R := R) pp) (tightFinalRelOut (R := R) pp) :=
  finalCheckTight_perfectCompleteness_any pp oSpec _

end

end Spartan.Spec.Bricks

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms CheckClaim.support_toVerifier_run
#print axioms CheckClaim.support_oracleReduction_run
#print axioms CheckClaim.oracleReduction_perfectCompleteness_any
#print axioms CheckClaim.oracleReduction_neverFails
#print axioms Spartan.Spec.Bricks.finalCheckTight_run_support
#print axioms Spartan.Spec.Bricks.finalCheckTight_neverFails
#print axioms Spartan.Spec.Bricks.finalCheckTight_perfectCompleteness_any
#print axioms Spartan.Spec.Bricks.finalCheckTight_perfectCompleteness
