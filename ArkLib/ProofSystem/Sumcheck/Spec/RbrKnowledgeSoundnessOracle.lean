/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Sumcheck.Spec.General
import ArkLib.OracleReduction.Composition.Sequential.SeqComposeRbrKnowledgeProof
import ArkLib.OracleReduction.Composition.Sequential.KnowledgeFailure
/-!
# Sumcheck deterministic execution and conditional knowledge composition

The failing-deterministic verdict reads the prover's message polynomial, matching canonical
`Simple.oracleVerifier`. The completed lens and n-ary composition constructions retain explicit
simple/per-round knowledge premises. The former unconditional wrappers used an input-query
constant-knowledge proof and are retired with exact source records in
`scripts/integration/sumcheck-message-semantics-retirements.json`. No admitted theorem supplies
these new conditional premises.
-/

open OracleComp OracleSpec ProtocolSpec Polynomial Finset
open scoped NNReal

namespace Verifier

variable {ι : Type} {oSpec : OracleSpec ι}

/-- **`Verifier.liftContext` preserves failing-determinism.** If `V` has the failing-deterministic
verdict `v?`, the lifted verifier has the verdict `(v? (lens.proj s) tr).map (lens.lift s)`. -/
theorem liftContext_failingDet {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}
    {k : ℕ} {pSpec : ProtocolSpec k}
    (lens : Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut)
    (V : Verifier oSpec InnerStmtIn InnerStmtOut pSpec)
    (v? : InnerStmtIn → pSpec.FullTranscript → Option InnerStmtOut)
    (hV : V = ⟨fun s tr => OptionT.mk (pure (v? s tr))⟩) :
    V.liftContext lens
      = ⟨fun s tr => OptionT.mk (pure ((v? (lens.proj s) tr).map (lens.lift s)))⟩ := by
  subst hV
  unfold Verifier.liftContext
  congr 1
  funext s tr
  refine OptionT.ext ?_
  show (OptionT.mk (pure (v? (lens.proj s) tr))
    >>= fun innerStmtOut => pure (lens.lift s innerStmtOut)).run = _
  rw [OptionT.run_bind]
  simp only [OptionT.run_mk, pure_bind, Option.elimM]
  cases v? (lens.proj s) tr <;> simp [OptionT.run_pure, Option.elim]

end Verifier

namespace Sumcheck.Spec

variable {R : Type} [CommSemiring R] [DecidableEq R] [SampleableType R]
  {deg : ℕ} {m : ℕ} {D : Fin m ↪ R} {n : ℕ}
  {ι : Type} {oSpec : OracleSpec ι}
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

namespace SingleRound

/-- The failing-deterministic verdict of the compiled `Simple` sum-check oracle verifier: guard the
MESSAGE polynomial's `D`-sum against the target, emit the message's evaluation at the challenge (the output
oracle is the unchanged input oracle, `embed = inl`). -/
noncomputable def simpleOracleVerify? (deg : ℕ) (D : Fin m ↪ R) :
    (Simple.StmtIn R × ∀ i, Simple.OStmtIn R deg i) → (SingleRound.pSpec R deg).FullTranscript →
      Option (Simple.StmtOut R × ∀ i, Simple.OStmtOut R deg i) :=
  fun p tr =>
    if (∑ x ∈ univ.map D, (tr 0).val.eval x) = p.1
      then some (((tr 0).val.eval (tr 1), tr 1),
        fun _ => p.2 ())
      else none

/-- **The compiled `Simple` sum-check oracle verifier is failing-deterministic** with verdict
`simpleOracleVerify?`: the proven `simulateQ` collapse `simulateQ_oracleVerify_eq` in
`Option`-verdict form, through `toVerifier_eq_failingDet_of_collapse`. -/
theorem simple_oracleVerifier_toVerifier_failingDet :
    (Simple.oracleVerifier R deg D oSpec).toVerifier
      = ⟨fun p tr => OptionT.mk (pure (simpleOracleVerify? deg D p tr))⟩ := by
  rw [Simple.oracleVerifier_eq_verifier]
  ext p tr
  simp only [Simple.verifier, simpleOracleVerify?, OracleComp.guard_eq]
  split <;> simp_all

/-- **The compiled `i`-th-round sum-check oracle verifier is failing-deterministic**: the
`Verifier.liftContext` of the failing-deterministic compiled `Simple` oracle verifier, via the
proven coherence commute. -/
theorem oracleVerifier_toVerifier_failingDet (i : Fin n) :
    (oracleVerifier R n deg D oSpec i).toVerifier
      = ⟨fun s tr => OptionT.mk (pure
          ((simpleOracleVerify? deg D ((oStmtLens R n deg D i).proj s) tr).map
            ((oStmtLens R n deg D i).lift s)))⟩ := by
  rw [oracleVerifier_eq_verifier]
  exact Verifier.liftContext_failingDet (oStmtLens R n deg D i)
    (Simple.verifier R deg D oSpec) _ (by
      rw [← Simple.oracleVerifier_eq_verifier]
      exact simple_oracleVerifier_toVerifier_failingDet)

/-- The canonical executable round lens transfers a supplied simple-round knowledge bound.
The premise is explicit because the canonical message-checking Simple bound is an inherited
upstream open proof. This preserves the completed transfer independently of that obligation. -/
theorem oracleVerifier_rbrKnowledgeSoundness_indexed_of_simple
    [Fintype R] (i : Fin n)
    (hSimple : (Simple.oracleVerifier R deg D oSpec).rbrKnowledgeSoundness init impl
      (Simple.inputRelation R deg D) (Simple.outputRelation R deg)
      (fun _ => (deg : ℝ≥0) / (Fintype.card R))) :
    (oracleVerifier R n deg D oSpec i).rbrKnowledgeSoundness init impl
      (relationRound R n deg D i.castSucc) (relationRound R n deg D i.succ)
      (fun _ => (deg : ℝ≥0) / (Fintype.card R)) := by
  letI : Inhabited (Simple.StmtOut R) := ⟨(0, 0)⟩
  exact OracleVerifier.liftContext_rbr_knowledgeSoundness
    (stmtLens := oStmtExecutableLens R n deg D i)
    (witLens := Witness.InvLens.trivial)
    (Simple.oracleVerifier R deg D oSpec) (liftContextOutput R n deg D oSpec i)
    (lensKS := by simpa using extractorLens_rbr_knowledge_soundness (oSpec := oSpec) i)
    hSimple

end SingleRound

/-- The completed failing-deterministic n-ary knowledge composition, supplied with the actual
canonical per-round knowledge bounds. This construction does not discharge those bounds. -/
theorem oracleVerifier_rbrKnowledgeSoundness_failingDet_of_round
    [Fintype R] [Inhabited R] [Subsingleton σ]
    (hInit : ∃ s, s ∈ support init) (hInitNF : prFail init = 0)
    (hRound : ∀ i : Fin n, (SingleRound.oracleVerifier R n deg D oSpec i).rbrKnowledgeSoundness
      init impl (relationRound R n deg D i.castSucc) (relationRound R n deg D i.succ)
      (fun _ => (deg : ℝ≥0) / (Fintype.card R))) :
    (oracleVerifier R deg D n oSpec).rbrKnowledgeSoundness init impl
      (relationRound R n deg D 0) (relationRound R n deg D (Fin.last n))
      (fun _ => (deg : ℝ≥0) / (Fintype.card R)) := by
  letI : ∀ j : Fin (n + 1), Inhabited (StatementRound R n j × ∀ k, OracleStatement R n deg k) :=
    fun j => ⟨(⟨default, fun _ => default⟩, fun _ => ⟨0, by
      simp only [MvPolynomial.mem_restrictDegree]
      intro s hs k
      simp [MvPolynomial.support_zero] at hs⟩)⟩
  have h := OracleVerifier.seqCompose_rbrKnowledgeSoundness_failingDet
    (init := init) (impl := impl)
    (StatementRound R n) (fun _ => OracleStatement R n deg) (fun _ => Unit)
    (SingleRound.oracleVerifier R n deg D oSpec)
    (fun j => relationRound R n deg D j)
    (fun _ _ => (deg : ℝ≥0) / (Fintype.card R))
    (fun i => ⟨_, SingleRound.oracleVerifier_toVerifier_failingDet i⟩)
    (fun _ => ⟨by omega, rfl⟩)
    (fun _ => ⟨()⟩)
    hInit hInitNF
    hRound
  exact h

end Sumcheck.Spec

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms Verifier.liftContext_failingDet
#print axioms Sumcheck.Spec.SingleRound.simple_oracleVerifier_toVerifier_failingDet
#print axioms Sumcheck.Spec.SingleRound.oracleVerifier_toVerifier_failingDet
#print axioms Sumcheck.Spec.SingleRound.oracleVerifier_rbrKnowledgeSoundness_indexed_of_simple
#print axioms Sumcheck.Spec.oracleVerifier_rbrKnowledgeSoundness_failingDet_of_round
