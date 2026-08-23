/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.SpartanBricks
import ArkLib.ProofSystem.Spartan.SecondSumcheckBridgeFree
import ArkLib.ToVCVio.Simulation

/-!
# The `finalCheck` completeness leaf, pinned to the composed-PC chain endpoints (#114)

`composedCompletenessStatement_of_five_leaves` (`ComposedCompleteness.lean`) takes the terminal
`finalCheck` leaf as its hypothesis `h₈`, with the relation endpoints pinned to the concrete
in-tree chain:

* input relation: `secondSumcheckRelOutBF` — the bridge-free output relation of the second
  sum-check phase (R1CS satisfiability carried through);
* output relation: `finalCheckRelOut` (definitionally `Set.univ` — the substantive cross-phase
  identity is carried by the *relation chain*, not by the terminal predicate; see the
  `finalPredicate` docstring in `SpartanBricks.lean`).

This module proves that leaf, **exactly at those endpoints** and under exactly the instance
context of the consumer (`[CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] [Inhabited R]
[SampleableType R]`), as `finalCheck_perfectCompleteness_leaf`:

* `finalCheck_run_leaf` — the 0-round `finalCheck` run collapses to `pure`: the honest prover is
  deterministic, and the verifier's `finalPredicate` oracle queries are eliminated by the honest
  `simOracle2` (`CheckClaim.oracleVerifier` discards the predicate's value via `let _ ←`);
* `finalCheck_perfectCompleteness_any` — the **relation-carrying** form: `finalCheck` forwards the
  (oracle) statement unchanged, so it is perfectly complete from *any* input relation `rel` back
  to `rel` itself (strictly stronger than the `Set.univ` form; available for content-bearing
  downstream consumers);
* `finalCheck_perfectCompleteness_leaf` — the `h₈` instance, by monotonicity in the output
  relation.

This is a standalone restatement of the `Bricks2.finalCheck_run` /
`Bricks2.finalCheck_perfectCompleteness` development of `ComposedCompletenessLeaves.lean`,
self-contained on the committed modules (`SpartanBricks`, `SecondSumcheckBridgeFree`,
`ToVCVio.Simulation`) and pinned to the exact consumer endpoints.

**Honesty note.** The in-tree `finalPredicate` returns the trivially-true proposition
`combined = combined` (and `CheckClaim.oracleVerifier` discards the returned `Prop` anyway), so
this leaf carries *no algebraic content*: the genuine terminal obligation — that the second
sum-check's final target equals the RLC of the honest evaluation claims — lives in the upstream
relation chain (`secondSumcheckRelInBF`'s pinned target, hypothesis `h₆` of the consumer, plus
the `secondSumCheckVirtualPolynomial_hypercubeSum_eq_evalClaimValue` algebra in `SpartanBricks`).
The completeness content here is totality (no failure) and prover/verifier output agreement.
-/

open OracleComp OracleSpec OracleInterface ProtocolSpec

namespace Spartan.Spec.Bricks

variable {R : Type} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] [Inhabited R]
  [SampleableType R]
  (pp : Spartan.PublicParams)
  {ι : Type} (oSpec : OracleSpec ι) [oSpec.Fintype] [oSpec.Inhabited]

omit [IsDomain R] [Fintype R] [DecidableEq R] [Inhabited R] [SampleableType R]
  [oSpec.Fintype] [oSpec.Inhabited] in
/-- The 0-round `finalCheck` run collapses to `pure`: the prover is deterministic and the
verifier's `finalPredicate` queries are eliminated by the honest `simOracle2` (its result is
discarded by `CheckClaim`'s `let _ ←`). Standalone restatement of `Bricks2.finalCheck_run`. -/
theorem finalCheck_run_leaf (stmt : FinalStatement R pp)
    (oStmt : ∀ i, FinalOracleStatement R pp i) :
    (finalCheck R pp oSpec).toReduction.run (stmt, oStmt) () =
      (pure (((default : (!p[] : ProtocolSpec 0).FullTranscript), (stmt, oStmt), ()),
        (stmt, oStmt)) : OptionT (OracleComp oSpec) _) := by
  simp only [finalCheck, CheckClaim.oracleReduction, CheckClaim.oracleProver,
    CheckClaim.oracleVerifier, OracleReduction.toReduction, Reduction.run, Prover.run,
    Verifier.run, OracleVerifier.toVerifier]
  unfold finalPredicate
  simp only [← OracleComp.liftComp_eq_liftM, OracleComp.liftComp_pure,
    bind_pure_comp, map_pure, liftM_pure, Option.getM]
  rfl

omit [IsDomain R] [Fintype R] [DecidableEq R] [Inhabited R] [SampleableType R]
  [oSpec.Fintype] [oSpec.Inhabited] in
/-- **`finalCheck` is perfectly complete from any input relation back to itself** (0-round; the
statement and oracle statements are forwarded unchanged). The strongest relation-carrying form;
consumers wanting the trivial output relation specialize via output-relation monotonicity. -/
theorem finalCheck_perfectCompleteness_any {σ : Type} {init : ProbComp σ}
    {impl : QueryImpl oSpec (StateT σ ProbComp)}
    (rel : Set (((FinalStatement R pp) × (∀ i, FinalOracleStatement R pp i)) × Unit)) :
    (finalCheck R pp oSpec).perfectCompleteness init impl rel rel := by
  unfold OracleReduction.perfectCompleteness
  simp only [Reduction.perfectCompleteness, Reduction.completeness, Reduction.completenessFromRun,
    ENNReal.coe_zero, tsub_zero]
  intro ⟨stmt, oStmt⟩ ⟨⟩ hIn
  simp only [finalCheck_run_leaf]
  rw [ge_iff_le, one_le_probEvent_iff, probEvent_eq_one_iff]
  refine ⟨?_, ?_⟩
  · rw [OptionT.probFailure_eq, OptionT.run_mk]
    simp only [probFailure_eq_zero, zero_add]
    apply probOutput_eq_zero_of_not_mem_support
    simp only [support_bind, Set.mem_iUnion, not_exists]
    intro s _
    change none ∈ _root_.support (StateT.run' (simulateQ _
        (pure (some (((default : (!p[] : ProtocolSpec 0).FullTranscript),
          (stmt, oStmt), ()), (stmt, oStmt))) : OracleComp _ _)) s) → False
    rw [simulateQ_pure]
    change none ∈ _root_.support (Prod.fst <$>
      (pure (some (((default : (!p[] : ProtocolSpec 0).FullTranscript),
        (stmt, oStmt), ()), (stmt, oStmt))) :
        StateT σ ProbComp _).run s) → False
    rw [StateT.run_pure]; simp [map_pure]
  · intro x hx
    rw [OptionT.mem_support_iff] at hx
    simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hx
    obtain ⟨s, _, hx⟩ := hx
    change some x ∈ _root_.support (StateT.run' (simulateQ _
        (pure (some (((default : (!p[] : ProtocolSpec 0).FullTranscript),
          (stmt, oStmt), ()), (stmt, oStmt))) : OracleComp _ _)) s) at hx
    rw [simulateQ_pure] at hx
    change some x ∈ _root_.support (Prod.fst <$>
      (pure (some (((default : (!p[] : ProtocolSpec 0).FullTranscript),
        (stmt, oStmt), ()), (stmt, oStmt))) :
        StateT σ ProbComp _).run s) at hx
    rw [StateT.run_pure] at hx
    simp only [_root_.map_pure, _root_.support_pure, Set.mem_singleton_iff,
      Option.some.injEq] at hx
    cases hx
    exact ⟨hIn, rfl⟩

omit [IsDomain R] [Fintype R] [DecidableEq R] [Inhabited R] [SampleableType R]
  [oSpec.Fintype] [oSpec.Inhabited] in
/-- **The `finalCheck` leaf of `composedCompletenessStatement_of_five_leaves` (hypothesis `h₈`)**:
perfect completeness of the terminal 0-round `CheckClaim` phase, from the second sum-check's
bridge-free output relation `secondSumcheckRelOutBF` into `finalCheckRelOut` (= `Set.univ`),
stated at exactly the consumer's endpoints and instance context. -/
theorem finalCheck_perfectCompleteness_leaf {σ : Type} {init : ProbComp σ}
    {impl : QueryImpl oSpec (StateT σ ProbComp)} :
    (finalCheck R pp oSpec).perfectCompleteness init impl
      (secondSumcheckRelOutBF (R := R) pp) (finalCheckRelOut R pp) := by
  have h := finalCheck_perfectCompleteness_any (init := init) (impl := impl) pp oSpec
    (secondSumcheckRelOutBF (R := R) pp)
  exact Reduction.completeness_relOut_mono init impl (Set.subset_univ _) h

#print axioms finalCheck_run_leaf
#print axioms finalCheck_perfectCompleteness_any
#print axioms finalCheck_perfectCompleteness_leaf

end Spartan.Spec.Bricks
