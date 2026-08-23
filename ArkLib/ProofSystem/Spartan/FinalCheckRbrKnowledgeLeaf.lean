/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Spartan.FinalCheckLeafComplete
import ArkLib.ProofSystem.Spartan.SumcheckKnowledgeLeaves

/-!
# Spartan terminal `finalCheck` RBR-KS leaf progress (#114)

The in-tree `finalCheck` is a zero-round oracle `CheckClaim` that forwards the final statement and
oracle statements unchanged.  Its predicate currently carries no enforced verifier content:
`finalPredicate` is tautological and `CheckClaim.oracleVerifier` discards the returned `Prop`.

Consequently the honest RBR-KS fact available without changing protocol semantics is the
relation-preserving one: if the output is required to remain in the same relation, the zero-round
identity-style extractor is valid.  This deliberately does **not** assert the broader
`secondSumcheckRbrRelOut → finalCheckRelOut (= Set.univ)` terminal leaf, which would erase the
nontrivial second-sumcheck endpoint relation.
-/

open OracleComp OracleSpec ProtocolSpec

namespace Spartan.Spec.Bricks

variable {R : Type} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] [Inhabited R]
  [SampleableType R]
  (pp : Spartan.PublicParams)
  {ι : Type} (oSpec : OracleSpec ι) [oSpec.Fintype] [oSpec.Inhabited]

omit [IsDomain R] [Fintype R] [DecidableEq R] [Inhabited R] [SampleableType R]
  [oSpec.Fintype] [oSpec.Inhabited] in
/-- The compiled terminal `finalCheck` verifier is the identity verifier on the bundled
statement/oracle-statement pair.  The oracle predicate is simulated and discarded. -/
theorem finalCheck_toVerifier_id :
    (finalCheck R pp oSpec).verifier.toVerifier =
      (Verifier.id : Verifier oSpec
        (FinalStatement R pp × ∀ i, FinalOracleStatement R pp i)
        (FinalStatement R pp × ∀ i, FinalOracleStatement R pp i) !p[]) := by
  ext ⟨stmt, oStmt⟩ tr
  simp only [finalCheck, CheckClaim.oracleReduction, CheckClaim.oracleVerifier,
    OracleVerifier.toVerifier, Verifier.id]
  unfold finalPredicate
  simp only [bind_pure_comp]
  rfl

omit [IsDomain R] [Fintype R] [DecidableEq R] [Inhabited R] [SampleableType R]
  [oSpec.Fintype] [oSpec.Inhabited] in
/-- Relation-preserving RBR-KS for the zero-round terminal `finalCheck`. -/
theorem finalCheck_rbrKnowledgeSoundness_any
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    (rel : Set (((FinalStatement R pp) × (∀ i, FinalOracleStatement R pp i)) × Unit)) :
    (finalCheck R pp oSpec).verifier.rbrKnowledgeSoundness init impl rel rel 0 := by
  unfold OracleVerifier.rbrKnowledgeSoundness
  rw [finalCheck_toVerifier_id (R := R) pp oSpec]
  exact Verifier.id_rbrKnowledgeSoundness init impl (rel := rel)

omit [Fintype R] [Inhabited R] [SampleableType R] [oSpec.Fintype] [oSpec.Inhabited] in
/-- The relation-preserving terminal leaf at the second sum-check's transported RBR output
relation. -/
theorem finalCheck_rbrKnowledgeSoundness_secondSumcheckRbrRelOut
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)} :
    (finalCheck R pp oSpec).verifier.rbrKnowledgeSoundness init impl
      (Spartan.Spec.secondSumcheckRbrRelOut (R := R) pp oSpec)
      (Spartan.Spec.secondSumcheckRbrRelOut (R := R) pp oSpec) 0 :=
  finalCheck_rbrKnowledgeSoundness_any (R := R) pp oSpec
    (Spartan.Spec.secondSumcheckRbrRelOut (R := R) pp oSpec)

#print axioms finalCheck_toVerifier_id
#print axioms finalCheck_rbrKnowledgeSoundness_any
#print axioms finalCheck_rbrKnowledgeSoundness_secondSumcheckRbrRelOut

end Spartan.Spec.Bricks
