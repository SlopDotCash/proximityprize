/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Spartan.TightFinalLeaf
import ArkLib.ProofSystem.Spartan.TightSecondBinding
import ProximityPrize.Compatibility.CheckClaimPassThrough

/-!
# The pure tight terminal pass-through

Canonical `CheckClaim` forwards its input unchanged without executing a predicate. The historical
`finalCheckPure` name delegates `finalCheckTight`, whose two terminal identities are semantic
output relations. Both names therefore use one canonical implementation and the same completed
knowledge and completeness guarantees.
-/

open OracleComp OracleSpec ProtocolSpec Function
open scoped NNReal

namespace Spartan.Spec.Bricks

set_option linter.unusedSectionVars false

noncomputable section

variable {R : Type 0} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] [Inhabited R]
  [SampleableType R] (pp : PublicParams)

variable {ι : Type} (oSpec : OracleSpec ι)

/-- Historical pure-terminal name for the canonical tight pass-through. -/
noncomputable def finalCheckPure :
    OracleReduction oSpec
      (Statement.AfterSecondSumcheckWithTarget R pp)
      (OracleStatement.AfterLinearCombination R pp) Unit
      (Statement.AfterSecondSumcheckWithTarget R pp)
      (OracleStatement.AfterLinearCombination R pp) Unit
      !p[] :=
  finalCheckTight pp oSpec

section Leaves

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- **Leaf `h₈` at the pure terminal check** — identical transport and `hdoom` as
`finalCheckTight_rbrKnowledgeSoundness` (the transport is predicate-generic). -/
theorem finalCheckPure_rbrKnowledgeSoundness :
    (finalCheckPure (R := R) pp oSpec).verifier.rbrKnowledgeSoundness init impl
      ((secondSumcheckWithTargetRbrRelOut (R := R) pp oSpec)
        ∩ {y | y.1 ∈ bindingAtSecondOut (R := R) pp})
      (tightFinalRelOut (R := R) pp) 0 :=
  finalCheckTight_rbrKnowledgeSoundness pp oSpec

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
  exact CheckClaim.oracleReduction_run_run stmt oStmt

/-- **Completeness of the pure terminal check**: pass-through preservation into
`tightFinalRelOut` — `(e₂-direct ∧ binding)` is carried verbatim and implies both conjuncts. -/
theorem finalCheckPure_perfectCompleteness :
    (finalCheckPure (R := R) pp oSpec).perfectCompleteness init impl
      ((secondSumcheckWithTargetRelOutEnriched (R := R) pp)
        ∩ {y | y.1 ∈ Spartan.Spec.Bricks.bindingAtSecondOut (R := R) pp})
      (tightFinalRelOut (R := R) pp) := by
  apply Reduction.perfectCompleteness_of_run_support
  rintro ⟨stmt, oStmt⟩ ⟨⟩ hIn x hx
  rw [finalCheckPure_run, OptionT.run_pure, support_pure, Set.mem_singleton_iff] at hx
  subst x
  exact ⟨_, rfl, ⟨hIn.1, hIn.2⟩, rfl⟩

end Leaves

end

end Spartan.Spec.Bricks

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms Spartan.Spec.Bricks.finalCheckPure_rbrKnowledgeSoundness
#print axioms Spartan.Spec.Bricks.finalCheckPure_toVerifier_pure
#print axioms Spartan.Spec.Bricks.finalCheckPure_run
#print axioms Spartan.Spec.Bricks.finalCheckPure_perfectCompleteness
