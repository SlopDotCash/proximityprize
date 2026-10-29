/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Spartan.TightFinalLeaf
import ArkLib.ToVCVio.OracleComp.SimSemantics.SimulateQ
import ProximityPrize.Compatibility.CheckClaimPassThrough

/-!
# Completeness of the tight terminal pass-through

The canonical oracle `CheckClaim` is pure and forwards the statement and oracle statements
unchanged. Its diagnostic predicate is not executed; the terminal identities are requirements
of `tightFinalRelOut`. Generic run, support, completeness and failure laws are shared through
`ProximityPrize.Compatibility.CheckClaimPassThrough` and instantiated here without additional
mathematical assumptions.
-/

open OracleComp OracleSpec OracleInterface ProtocolSpec

universe u v



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
    prFail (OptionT.mk (do StateT.run' (simulateQ (QueryImpl.addLift impl challengeQueryImpl)
        (((finalCheckTight (R := R) pp oSpec).toReduction.run
          (stmt, oStmt) ()).run)) (← init))) = 0 :=
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
