/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ProximityPrize.Compatibility.CheckClaimPassThrough
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
  deterministic, and canonical `CheckClaim` forwards the statement and oracle family without
  executing `finalPredicate`;
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
`combined = combined`; canonical `CheckClaim` does not execute this predicate. This leaf carries
*no algebraic content*: the genuine terminal obligation — that the second
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
  {ι : Type} (oSpec : OracleSpec ι) [∀ q, Fintype (oSpec.Range q)] [∀ q, Inhabited (oSpec.Range q)]

omit [IsDomain R] [Fintype R] [DecidableEq R] [Inhabited R] [SampleableType R]
  [∀ q, Fintype (oSpec.Range q)] [∀ q, Inhabited (oSpec.Range q)] in
/-- The 0-round `finalCheck` run collapses to `pure`: canonical `CheckClaim` forwards the
statement and oracle family. Standalone restatement of `Bricks2.finalCheck_run`. -/
theorem finalCheck_run_leaf (stmt : FinalStatement R pp)
    (oStmt : ∀ i, FinalOracleStatement R pp i) :
    (finalCheck R pp oSpec).toReduction.run (stmt, oStmt) () =
      (pure (((default : (!p[] : ProtocolSpec 0).FullTranscript), (stmt, oStmt), ()),
        (stmt, oStmt)) : OptionT (OracleComp oSpec) _) := by
  apply OptionT.ext
  exact CheckClaim.oracleReduction_run_run stmt oStmt

omit [IsDomain R] [Fintype R] [DecidableEq R] [Inhabited R] [SampleableType R]
  [∀ q, Fintype (oSpec.Range q)] [∀ q, Inhabited (oSpec.Range q)] in
/-- **`finalCheck` is perfectly complete from any input relation back to itself** (0-round; the
statement and oracle statements are forwarded unchanged). The strongest relation-carrying form;
consumers wanting the trivial output relation specialize via output-relation monotonicity. -/
theorem finalCheck_perfectCompleteness_any {σ : Type} {init : ProbComp σ}
    {impl : QueryImpl oSpec (StateT σ ProbComp)}
    (rel : Set (((FinalStatement R pp) × (∀ i, FinalOracleStatement R pp i)) × Unit)) :
    (finalCheck R pp oSpec).perfectCompleteness init impl rel rel := by
  exact CheckClaim.oracleReduction_perfectCompleteness_any (finalPredicate R pp) rel

omit [IsDomain R] [Fintype R] [DecidableEq R] [Inhabited R] [SampleableType R]
  [∀ q, Fintype (oSpec.Range q)] [∀ q, Inhabited (oSpec.Range q)] in
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
