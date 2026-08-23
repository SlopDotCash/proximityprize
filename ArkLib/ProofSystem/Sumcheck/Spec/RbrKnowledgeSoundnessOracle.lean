/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Sumcheck.Spec.General
import ArkLib.ProofSystem.Sumcheck.Spec.SingleRoundCohWired
import ArkLib.OracleReduction.Composition.Sequential.SeqComposeRbrKnowledgeProof
import ArkLib.OracleReduction.Composition.Sequential.AppendRbrKnowledgeFailingDet

/-!
# Oracle-level multi-round rbr KNOWLEDGE soundness of the generic sum-check (#114)

The knowledge mirror of `SeqComposeRbrSoundness.lean`'s plain-soundness assembly, fully
unconditional:

* `SingleRound.oracleVerifier_rbrKnowledgeSoundness_indexed` — the `i`-th-round oracle verifier
  (the `liftContext` of the `Simple` oracle verifier through the virtual-routing
  `sumcheckOracleLens`) is rbr knowledge sound on the canonical relation chain
  `relationRound i.castSucc → relationRound i.succ` with per-round error `deg/|R|`: the proven
  `Simple.oracleVerifier_rbrKnowledgeSoundness` transported through
  `Verifier.liftContext_rbr_knowledgeSoundness` at the proven lens-knowledge instance
  `extractorLens_rbr_knowledge_soundness`, with the verifier-conversion commute supplied by the
  proven `coh_proven_inst`.

* `Simple.oracleVerifier_toVerifier_failingDet` / `SingleRound.oracleVerifier_toVerifier_failingDet`
  — the compiled single-round (oracle) verifiers are failing-deterministic: the `simulateQ`
  collapse `simulateQ_oracleVerify_eq` put in `Option`-verdict form, then lifted through
  `Verifier.liftContext` (which preserves failing-determinism, `Verifier.liftContext_failingDet`).

* `oracleVerifier_rbrKnowledgeSoundness` — **the full multi-round sum-check oracle verifier is
  rbr knowledge sound**, by the n-ary `OracleVerifier.seqCompose_rbrKnowledgeSoundness_failingDet`
  fold at the per-round facts and failing-determinism witnesses, on the canonical relation chain
  `relationRound 0 → relationRound (Fin.last n)`, with error `deg/|R|` at every round.

No `sorry`/axioms; `#print axioms` must report exactly `[propext, Classical.choice, Quot.sound]`.
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
ORACLE's `D`-sum against the target, emit the oracle's evaluation at the challenge (the output
oracle is the unchanged input oracle, `embed = inl`). -/
noncomputable def simpleOracleVerify? (deg : ℕ) (D : Fin m ↪ R) :
    (Simple.StmtIn R × ∀ i, Simple.OStmtIn R deg i) → (SingleRound.pSpec R deg).FullTranscript →
      Option (Simple.StmtOut R × ∀ i, Simple.OStmtOut R deg i) :=
  fun p tr =>
    if ((Vector.finRange m).map (fun i => (p.2 ()).val.eval (D i))).sum = p.1
      then some (((p.2 ()).val.eval (tr.challenges default), tr.challenges default),
        fun _ => p.2 ())
      else none

/-- **The compiled `Simple` sum-check oracle verifier is failing-deterministic** with verdict
`simpleOracleVerify?`: the proven `simulateQ` collapse `simulateQ_oracleVerify_eq` in
`Option`-verdict form, through `toVerifier_eq_failingDet_of_collapse`. -/
theorem simple_oracleVerifier_toVerifier_failingDet :
    (Simple.oracleVerifier R deg D oSpec).toVerifier
      = ⟨fun p tr => OptionT.mk (pure (simpleOracleVerify? deg D p tr))⟩ := by
  have h := OracleVerifier.toVerifier_eq_failingDet_of_collapse
    (Simple.oracleVerifier R deg D oSpec)
    (fun p tr =>
      if ((Vector.finRange m).map (fun i => (p.2 ()).val.eval (D i))).sum = p.1
        then some ((p.2 ()).val.eval (tr.challenges default), tr.challenges default)
        else none)
    (fun stmt oStmt tr => by
      rw [Simple.simulateQ_oracleVerify_eq R deg D oSpec]
      by_cases hc : ((Vector.finRange m).map (fun i => (oStmt ()).val.eval (D i))).sum = stmt
      · simp only [if_pos hc]; rfl
      · simp only [if_neg hc]; rfl)
  rw [h]
  congr 1
  funext p tr
  by_cases hc : ((Vector.finRange m).map (fun i => (p.2 ()).val.eval (D i))).sum = p.1
  · simp only [simpleOracleVerify?, if_pos hc, Option.map_some]
    rfl
  · simp only [simpleOracleVerify?, if_neg hc, Option.map_none]

/-- **The compiled `i`-th-round sum-check oracle verifier is failing-deterministic**: the
`Verifier.liftContext` of the failing-deterministic compiled `Simple` oracle verifier, via the
proven coherence commute. -/
theorem oracleVerifier_toVerifier_failingDet (i : Fin n) :
    (oracleVerifier R n deg D oSpec i).toVerifier
      = ⟨fun s tr => OptionT.mk (pure
          ((simpleOracleVerify? deg D ((oStmtLens R n deg D i).proj s) tr).map
            ((oStmtLens R n deg D i).lift s)))⟩ := by
  letI coh : OracleVerifier.LiftContextCoherent (sumcheckOracleLens R n deg D oSpec i)
      (Simple.oracleVerifier R deg D oSpec) := by
    change OracleVerifier.LiftContextCoherent (sumcheckOracleLens R n deg D oSpec i)
      (Simple.oracleReduction R deg D oSpec).verifier
    exact coh_proven_inst i
  show ((Simple.oracleVerifier R deg D oSpec).liftContext
    (sumcheckOracleLens R n deg D oSpec i)).toVerifier = _
  rw [OracleVerifier.liftContext_toVerifier_comm]
  exact Verifier.liftContext_failingDet _ _ _
    (simple_oracleVerifier_toVerifier_failingDet (R := R) (deg := deg) (D := D) (oSpec := oSpec))

/-- **Per-round rbr knowledge soundness of the `i`-th-round sum-check oracle verifier** on the
canonical relation chain `relationRound i.castSucc → relationRound i.succ`, error `deg/|R|`:
the proven `Simple.oracleVerifier_rbrKnowledgeSoundness` transported through
`Verifier.liftContext_rbr_knowledgeSoundness` at the proven
`extractorLens_rbr_knowledge_soundness`. -/
theorem oracleVerifier_rbrKnowledgeSoundness_indexed [Fintype R] [Inhabited R] (i : Fin n) :
    (oracleVerifier R n deg D oSpec i).rbrKnowledgeSoundness init impl
      (relationRound R n deg D i.castSucc) (relationRound R n deg D i.succ)
      (fun _ => (deg : ℝ≥0) / (Fintype.card R)) := by
  letI : Inhabited (Simple.StmtOut R) := ⟨(default, default)⟩
  letI : Inhabited (Simple.StmtOut R × ∀ j, Simple.OStmtOut R deg j) :=
    ⟨((default, default), fun _ => ⟨0, by
      rw [Polynomial.mem_degreeLE]; exact le_trans (le_of_eq degree_zero) bot_le⟩)⟩
  letI coh : OracleVerifier.LiftContextCoherent (sumcheckOracleLens R n deg D oSpec i)
      (Simple.oracleVerifier R deg D oSpec) := by
    change OracleVerifier.LiftContextCoherent (sumcheckOracleLens R n deg D oSpec i)
      (Simple.oracleReduction R deg D oSpec).verifier
    exact coh_proven_inst i
  show ((oracleVerifier R n deg D oSpec i).toVerifier).rbrKnowledgeSoundness init impl _ _ _
  show (((Simple.oracleVerifier R deg D oSpec).liftContext
    (sumcheckOracleLens R n deg D oSpec i)).toVerifier).rbrKnowledgeSoundness init impl _ _ _
  rw [OracleVerifier.liftContext_toVerifier_comm]
  exact Verifier.liftContext_rbr_knowledgeSoundness
    (stmtLens := oStmtLens R n deg D i) (witLens := Witness.InvLens.trivial)
    ((Simple.oracleVerifier R deg D oSpec).toVerifier)
    (lensKS := extractorLens_rbr_knowledge_soundness i)
    (Simple.oracleVerifier_rbrKnowledgeSoundness R deg D oSpec)

end SingleRound

/-- **The full multi-round sum-check ORACLE verifier is round-by-round knowledge sound** on the
canonical relation chain `relationRound 0 → relationRound (Fin.last n)`, with per-round error
`deg/|R|`, by the n-ary failing-deterministic `seqCompose` fold (issue #114). Fully unconditional:
both the per-round facts and the failing-determinism witnesses are proven above. -/
theorem oracleVerifier_rbrKnowledgeSoundness [Fintype R] [Inhabited R] [Subsingleton σ]
    (hInit : ∃ s, s ∈ support init) (hInitNF : Pr[⊥ | init] = 0) :
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
    (fun i => SingleRound.oracleVerifier_rbrKnowledgeSoundness_indexed (impl := impl) i)
  exact h

end Sumcheck.Spec

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms Verifier.liftContext_failingDet
#print axioms Sumcheck.Spec.SingleRound.simple_oracleVerifier_toVerifier_failingDet
#print axioms Sumcheck.Spec.SingleRound.oracleVerifier_toVerifier_failingDet
#print axioms Sumcheck.Spec.SingleRound.oracleVerifier_rbrKnowledgeSoundness_indexed
#print axioms Sumcheck.Spec.oracleVerifier_rbrKnowledgeSoundness
