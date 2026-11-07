/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Spartan.TightFinalLeaf
import ArkLib.ProofSystem.Spartan.TightSecondBinding

/-!
# The pure tight terminal check: KS + completeness, unconditional (issue #329, B7)

Per the established honesty convention (`FinalCheckWithClaimLeaf`'s note), the oracle
`CheckClaim` **discards** its predicate's `Prop` — the binding currency of the terminal check
is its *semantic output relation* (`tightFinalRelOut`), not the predicate. The canonical tight
terminal check can therefore use the **trivial predicate**: the rbr-KS leaf is unchanged (the
transport is predicate-generic), and perfect completeness becomes an all-pure pass-through —
no oracle-query collapse needed.

* `finalCheckPure` — the zero-round terminal check at the doubly-carried statement, trivial
  predicate;
* `finalCheckPure_rbrKnowledgeSoundness` — leaf `h₈` at error 0 (same transport, same
  `hdoom` as `finalCheckTight_rbrKnowledgeSoundness`);
* `finalCheckPure_run` — the deterministic closed run;
* `finalCheckPure_perfectCompleteness` — from `(e₂-direct ∧ binding)` to `tightFinalRelOut`,
  no side hypotheses beyond the framework's.

(The query-making documented-predicate variant `finalCheckTight` keeps its KS leaf in
`TightFinalLeaf.lean`; its completeness would additionally need the predicate's simulateQ
collapse — `zEvalFromFinalOracles_simOracle0_*` are the building blocks — and is not needed
for the composed chain.)
-/

open OracleComp OracleSpec ProtocolSpec Function
open scoped NNReal

namespace Spartan.Spec.Bricks

set_option linter.unusedSectionVars false

noncomputable section

variable {R : Type 0} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] [Inhabited R]
  [SampleableType R] (pp : PublicParams)

variable {ι : Type} (oSpec : OracleSpec ι)

/-- **The pure tight terminal check**: a zero-round `CheckClaim` at the doubly-carried
statement with the trivial predicate (the semantic relation `tightFinalRelOut` is the binding
currency). -/
noncomputable def finalCheckPure :
    OracleReduction oSpec
      (Statement.AfterSecondSumcheckWithTarget R pp)
      (OracleStatement.AfterLinearCombination R pp) Unit
      (Statement.AfterSecondSumcheckWithTarget R pp)
      (OracleStatement.AfterLinearCombination R pp) Unit
      !p[] :=
  CheckClaim.oracleReduction oSpec
    (Statement.AfterSecondSumcheckWithTarget R pp)
    (OracleStatement.AfterLinearCombination R pp)
    (fun _ => pure True)

section Leaves

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- **Leaf `h₈` at the pure terminal check** — identical transport and `hdoom` as
`finalCheckTight_rbrKnowledgeSoundness` (the transport is predicate-generic). -/
theorem finalCheckPure_rbrKnowledgeSoundness :
    (finalCheckPure (R := R) pp oSpec).verifier.rbrKnowledgeSoundness init impl
      ((secondSumcheckWithTargetRbrRelOut (R := R) pp oSpec)
        ∩ {y | y.1 ∈ bindingAtSecondOut (R := R) pp})
      (tightFinalRelOut (R := R) pp) 0 :=
  CheckClaim.oracleVerifier_rbrKnowledgeSoundness_transport
    (fun _ => pure True) init impl
    (fun p hOut => ⟨transported₂_of_direct pp oSpec p hOut.1, hOut.2⟩)

/-- The compiled pure terminal verifier is the identity `pure`. -/
theorem finalCheckPure_toVerifier_pure :
    (finalCheckPure (R := R) pp oSpec).verifier.toVerifier
      = ⟨fun p _tr => pure p⟩ := by
  rw [OracleVerifier.toVerifier_eq_pure_of_collapse
    (finalCheckPure (R := R) pp oSpec).verifier
    (fun p _tr => p.1)
    (fun stmt oStmt tr => rfl)]
  congr 1

/-- The pure terminal check's prover passes through (0-round). -/
theorem finalCheckPureProver_run (stmt : Statement.AfterSecondSumcheckWithTarget R pp)
    (oStmt : ∀ i, OracleStatement.AfterLinearCombination R pp i) :
    (finalCheckPure (R := R) pp oSpec).prover.run (stmt, oStmt) () =
      pure ((default : (!p[] : ProtocolSpec 0).FullTranscript), (stmt, oStmt), ()) := rfl

/-- **The deterministic closed run of the pure terminal check.** -/
theorem finalCheckPure_run (stmt : Statement.AfterSecondSumcheckWithTarget R pp)
    (oStmt : ∀ i, OracleStatement.AfterLinearCombination R pp i) :
    (finalCheckPure (R := R) pp oSpec).toReduction.run (stmt, oStmt) () =
      (pure (((default : (!p[] : ProtocolSpec 0).FullTranscript),
          ((stmt, oStmt), ())),
        (stmt, oStmt)) :
        OptionT (OracleComp _) _) := by
  simp only [OracleReduction.toReduction, Reduction.run]
  rw [finalCheckPureProver_run]
  simp only [liftM_pure, pure_bind]
  rw [finalCheckPure_toVerifier_pure]
  simp only [Verifier.run, OptionT.run_pure, liftM_pure, pure_bind, Option.getM_some]

/-- **Completeness of the pure terminal check**: pass-through preservation into
`tightFinalRelOut` — `(e₂-direct ∧ binding)` is carried verbatim and implies both conjuncts. -/
theorem finalCheckPure_perfectCompleteness :
    (finalCheckPure (R := R) pp oSpec).perfectCompleteness init impl
      ((secondSumcheckWithTargetRelOutEnriched (R := R) pp)
        ∩ {y | y.1 ∈ Spartan.Spec.Bricks.bindingAtSecondOut (R := R) pp})
      (tightFinalRelOut (R := R) pp) := by
  unfold OracleReduction.perfectCompleteness
  simp only [Reduction.perfectCompleteness, Reduction.completeness,
    Reduction.completenessFromRun, ENNReal.coe_zero, tsub_zero]
  intro ⟨stmt, oStmt⟩ ⟨⟩ hIn
  simp only [finalCheckPure_run]
  rw [ge_iff_le, one_le_probEvent_iff, probEvent_eq_one_iff]
  refine ⟨?_, ?_⟩
  · rw [OptionT.probFailure_eq, OptionT.run_mk]
    simp only [OptionT.run_pure, probFailure_eq_zero, zero_add]
    apply probOutput_eq_zero_of_not_mem_support
    simp only [support_bind, Set.mem_iUnion, not_exists]
    intro s _
    rw [simulateQ_pure]
    intro hmem
    change none ∈ _root_.support (Prod.fst <$>
      (pure (some (((default : (!p[] : ProtocolSpec 0).FullTranscript),
        ((stmt, oStmt), ())), (stmt, oStmt))) : StateT σ ProbComp _).run s) at hmem
    rw [StateT.run_pure] at hmem
    simp [map_pure] at hmem
  · intro x hx
    rw [OptionT.mem_support_iff] at hx
    simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hx
    obtain ⟨s, _, hx⟩ := hx
    rw [OptionT.run_pure, simulateQ_pure] at hx
    replace hx : some x ∈ _root_.support (Prod.fst <$>
      (pure (some (((default : (!p[] : ProtocolSpec 0).FullTranscript),
        ((stmt, oStmt), ())), (stmt, oStmt))) : StateT σ ProbComp _).run s) := hx
    rw [StateT.run_pure] at hx
    simp only [map_pure, support_pure, Set.mem_singleton_iff, Option.some_inj] at hx
    subst hx
    exact ⟨⟨hIn.1, hIn.2⟩, rfl⟩

end Leaves

end

end Spartan.Spec.Bricks

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms Spartan.Spec.Bricks.finalCheckPure_rbrKnowledgeSoundness
#print axioms Spartan.Spec.Bricks.finalCheckPure_toVerifier_pure
#print axioms Spartan.Spec.Bricks.finalCheckPure_run
#print axioms Spartan.Spec.Bricks.finalCheckPure_perfectCompleteness
