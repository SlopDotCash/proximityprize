/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ProximityPrize.Compatibility.CheckClaimPassThrough
import ProximityPrize.Compatibility.SpartanSendEvalClaim
import ProximityPrize.Compatibility.SpartanLinearCombination
import ArkLib.ProofSystem.Spartan.Composition
import ArkLib.ProofSystem.Spartan.SecondSumcheckComplete
import ArkLib.ProofSystem.Spartan.SecondSumcheckBridgeFree

/-!
# Spartan composed-completeness leaves (#114)

The per-phase perfect-completeness facts and the honest RLC-target adapter needed by the
8-fold composed-PC assembly for `composedPIOP_Rc` / `composedPIOPWithClaim_Rc`:

* `linearCombination_perfectCompleteness` — the `linearCombination` phase (verifier-only
  1-round challenge);
* `sendEvalClaim_perfectCompleteness` — the `sendEvalClaim` phase (prover-only forwarder of the
  bundled eval-claim oracle);
* `prependSlot_perfectCompleteness` (+ `prependTarget` / `prependClaim` instances) — the 0-round
  statement-reshaping adapters of `Composition.lean`;
* the **honest RLC-target adapter** `prependRLCTarget` (the D1 design fix): unlike `prependTarget`
  (whose carried second-sumcheck target is hardwired `0`, Composition.lean), its prover/verifier
  emit the honest RLC `∑ idx, r_lc(idx) · claims(idx)` read from the bundled eval-claim oracle, and
  `prependRLCTargetRelOut_subset_secondSumcheckRelIn` shows its output relation refines
  `secondSumcheckRelIn` — repairing the relation chain for the composed completeness fold.

The remaining leaf is the `finalCheck` (`CheckClaim`) phase completeness, handled separately.
-/

open MvPolynomial OracleComp OracleSpec OracleQuery OracleInterface ProtocolSpec

namespace Spartan.Spec

variable {R : Type} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] [SampleableType R]
  (pp : Spartan.PublicParams) {ι : Type} (oSpec : OracleSpec ι)

/-- The `linearCombination` challenge `LinearCombinationChallenge R = R1CS.MatrixIdx → R` is a
`SampleableType` (nonempty `Fintype`). Mirrors `Bricks.instSampleableTypeLinearCombinationChallenge`
in `Composition.lean`; restated here so the standalone check resolves the challenge instance. -/
noncomputable instance instSampleableTypeLinearCombinationChallenge' :
    SampleableType (LinearCombinationChallenge R) := by
  letI : Inhabited R := ⟨0⟩
  exact SampleableType.ofFintype (R1CS.MatrixIdx → R)

/-- Outer input relation of the `linearCombination` phase: R1CS satisfiability, carried through. -/
def linearCombinationRelIn :
    Set ((Statement.AfterSendEvalClaim R pp ×
        (∀ i, OracleStatement.AfterSendEvalClaim R pp i)) × Unit) :=
  { x | R1CS.relation R pp.toSizeR1CS x.1.1.2.2
      (fun idx => x.1.2 (.inr (.inl idx))) (x.1.2 (.inr (.inr 0))) }

/-- Outer output relation of the `linearCombination` phase: the same R1CS satisfiability, carried
through (the LC challenge `r` is recorded but irrelevant to satisfiability). -/
def linearCombinationRelOut :
    Set ((Statement.AfterLinearCombination R pp ×
        (∀ i, OracleStatement.AfterLinearCombination R pp i)) × Unit) :=
  { x | R1CS.relation R pp.toSizeR1CS x.1.1.2.2.2
      (fun idx => x.1.2 (.inr (.inl idx))) (x.1.2 (.inr (.inr 0))) }

instance instLinearCombinationVerifierOnly :
    VerifierOnly (⟨!v[.V_to_P], !v[LinearCombinationChallenge R]⟩ : ProtocolSpec 1) where
  verifier_first' := by simp

omit [DecidableEq R] [SampleableType R] in
/-- The completed challenge phase preserves an arbitrary relation after stripping its recorded
challenge. This is a run-support property of the completed downstream constructor. -/
theorem completedLinearCombination_perfectCompleteness_of
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    (rel : Set ((Statement.AfterSendEvalClaim R pp ×
      (∀ i, OracleStatement.AfterSendEvalClaim R pp i)) × Unit)) :
    (oracleReduction.completedLinearCombination R pp oSpec).perfectCompleteness init impl rel
      { x | ((x.1.1.2, x.1.2), ()) ∈ rel } := by
  apply Reduction.perfectCompleteness_of_run_support
  rintro ⟨stmt, oStmt⟩ ⟨⟩ hRelIn z hz
  simp only [oracleReduction.completedLinearCombination, OracleReduction.toReduction, Reduction.run,
    Prover.run_of_verifier_first, linearCombinationProver, linearCombinationVerifier,
    OracleVerifier.toVerifier, Verifier.run] at hz
  simp only [OptionT.run_bind, OptionT.run_mk, OptionT.run_pure, OptionT.run_monadLift,
    simulateQ_pure, pure_bind, map_pure, liftM_pure,
    Option.elimM, Option.getM_some, Option.map_some] at hz
  simp_all [OracleVerifier.materializeOutput, OracleVerifier.materializeOutputOracle, FullTranscript.messages]
  obtain ⟨q, _, rfl⟩ := hz
  exact ⟨_, q, stmt.1, stmt.2.1, stmt.2.2, oStmt, ⟨(), rfl⟩, hRelIn⟩

omit [DecidableEq R] [SampleableType R] in
/-- The completed RLC challenge phase carries the R1CS satisfaction relation unchanged. -/
theorem linearCombination_perfectCompleteness
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)} :
    (oracleReduction.completedLinearCombination R pp oSpec).perfectCompleteness init impl
      (linearCombinationRelIn (R := R) pp) (linearCombinationRelOut (R := R) pp) :=
  completedLinearCombination_perfectCompleteness_of pp oSpec (linearCombinationRelIn pp)

end Spartan.Spec

-- Axiom check
#print axioms Spartan.Spec.linearCombination_perfectCompleteness

open OracleComp OracleSpec ProtocolSpec OracleInterface Function

namespace Spartan.Spec

variable (R : Type) [CommRing R] [IsDomain R] [Fintype R] (pp : PublicParams)
variable {ι : Type} (oSpec : OracleSpec ι)
variable [SampleableType R]
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- Output relation for `sendEvalClaim` parameterized on an arbitrary input relation `relIn`
on `(AfterFirstSumcheck × OStmt) × Unit`. It holds for an output statement-oracle pair iff
(1) the underlying input pair (recovering the input oracle family from the `.inr` part of the
output oracle family) lies in `relIn`, and
(2) the bundled eval-claim oracle (`.inl 0`) equals the honest `evalClaimValue`. -/
@[reducible]
def sendEvalClaimRelOut
    (relIn : Set ((Statement.AfterFirstSumcheck R pp ×
        (∀ i, OracleStatement.AfterFirstSumcheck R pp i)) × Unit)) :
    Set ((Statement.AfterSendEvalClaim R pp ×
        (∀ i, OracleStatement.AfterSendEvalClaim R pp i)) × Unit) :=
  { x | ((x.1.1, fun j => x.1.2 (.inr j)), ()) ∈ relIn ∧
        (fun idx => (show R from x.1.2 (.inl idx))) = evalClaimValue R pp x.1.1 (fun j => x.1.2 (.inr j)) }

set_option maxHeartbeats 1000000 in
omit [IsDomain R] [Fintype R] [SampleableType R] in
/-- The `sendEvalClaim` oracle reduction satisfies perfect completeness: from any input relation
`relIn`, it lands in `sendEvalClaimRelOut relIn`. The honest prover forwards the input oracles and
sends the bundled eval-claim `evalClaimValue`; the verifier performs no check, so the relation
pass-through and the eval-claim honesty are deterministic. -/
theorem sendEvalClaim_perfectCompleteness
    (relIn : Set ((Statement.AfterFirstSumcheck R pp ×
        (∀ i, OracleStatement.AfterFirstSumcheck R pp i)) × Unit)) :
    (oracleReduction.completedSendEvalClaim R pp oSpec).perfectCompleteness init impl
      relIn (sendEvalClaimRelOut R pp relIn) := by
  apply Reduction.perfectCompleteness_of_run_support
  rintro ⟨stmt, oStmt⟩ ⟨⟩ hIn z hz
  have : ProverOnly (⟨!v[.P_to_V], !v[∀ i, EvalClaim R i]⟩ : ProtocolSpec 1) :=
    { prover_first' := by simp }
  simp only [OracleReduction.toReduction, oracleReduction.completedSendEvalClaim] at hz
  rw [Reduction.run_of_prover_first] at hz
  simp only [sendEvalClaimProver, sendEvalClaimVerifier, liftM_pure, pure_bind,
    bind_pure_comp, OracleVerifier.toVerifier, Verifier.run] at hz
  simp only [OptionT.run_bind, OptionT.run_mk, OptionT.run_pure, OptionT.run_monadLift,
    simulateQ_pure, pure_bind, map_pure, liftM_pure,
    Option.elimM, Option.getM_some, Option.map_some] at hz
  simp_all [sendEvalClaimRelOut, OracleVerifier.materializeOutput,
    OracleVerifier.materializeOutputOracle]
  exact ⟨rfl, rfl⟩

#print axioms sendEvalClaim_perfectCompleteness

end Spartan.Spec

open OracleComp OracleInterface ProtocolSpec Function

namespace Spartan.Spec.Bricks

noncomputable section

open scoped NNReal

variable (R : Type) [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] (pp : PublicParams)
variable {ι : Type} (oSpec : OracleSpec ι) [SampleableType R]
variable {ιₛ : Type}

/-- Output relation of a `prependSlot` step: input predicate with the prepended `(0,·)` stripped. -/
def prependSlotRelOut (Stmt : Type) (OStmt : ιₛ → Type) [∀ i, OracleInterface (OStmt i)]
    (rel : Set ((Stmt × (∀ i, OStmt i)) × Unit)) :
    Set (((R × Stmt) × (∀ i, OStmt i)) × Unit) :=
  { x | ((x.1.1.2, x.1.2), x.2) ∈ rel }

/-- The deterministic run of `prependSlot` is a single `pure` prepending `0`. -/
theorem prependSlot_run (Stmt : Type) (OStmt : ιₛ → Type) [∀ i, OracleInterface (OStmt i)]
    (stmt : Stmt) (oStmt : ∀ i, OStmt i) :
    (prependSlot (R := R) oSpec Stmt OStmt).toReduction.run (stmt, oStmt) () =
      (pure (((default : (!p[] : ProtocolSpec 0).FullTranscript),
               (((0 : R), stmt), oStmt), ()), (((0 : R), stmt), oStmt)) :
        OptionT (OracleComp _) _) := by
  simp only [prependSlot, prependSlotProver, prependSlotVerifier, OracleReduction.toReduction,
    Reduction.run, Prover.run, Verifier.run, OracleVerifier.toVerifier]
  simp only [map_pure, bind_pure_comp, liftM_pure, Option.map_some, Option.getM, Option.bind_some]
  rfl

/-- **prependSlot is perfectly complete.** (0-round adapter; deterministic, no queries.) -/
theorem prependSlot_perfectCompleteness (Stmt : Type) (OStmt : ιₛ → Type)
    [∀ i, OracleInterface (OStmt i)] {σ} {init : ProbComp σ}
    {impl : QueryImpl oSpec (StateT σ ProbComp)}
    (rel : Set ((Stmt × (∀ i, OStmt i)) × Unit)) :
    (prependSlot (R := R) oSpec Stmt OStmt).perfectCompleteness init impl
      rel (prependSlotRelOut R Stmt OStmt rel) := by
  apply Reduction.perfectCompleteness_of_run_support
  rintro ⟨stmt, oStmt⟩ ⟨⟩ hIn z hz
  rw [prependSlot_run, OptionT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  subst z
  exact ⟨_, rfl, hIn, rfl⟩

/-- **prependTarget is perfectly complete** (linearCombination→secondSumcheck adapter). -/
theorem prependTarget_perfectCompleteness {σ} {init : ProbComp σ}
    {impl : QueryImpl oSpec (StateT σ ProbComp)}
    (rel : Set ((Statement.AfterLinearCombination R pp ×
      (∀ i, OracleStatement.AfterLinearCombination R pp i)) × Unit)) :
    (prependTarget (R := R) pp oSpec).perfectCompleteness init impl
      rel (prependSlotRelOut R _ _ rel) :=
  prependSlot_perfectCompleteness R oSpec _ _ rel

/-- **prependClaim is perfectly complete** (terminal finalCheck→FinalClaimStatement adapter). -/
theorem prependClaim_perfectCompleteness {σ} {init : ProbComp σ}
    {impl : QueryImpl oSpec (StateT σ ProbComp)}
    (rel : Set ((FinalStatement R pp × (∀ i, FinalOracleStatement R pp i)) × Unit)) :
    (prependClaim (R := R) pp oSpec).perfectCompleteness init impl
      rel (prependSlotRelOut R _ _ rel) :=
  prependSlot_perfectCompleteness R oSpec _ _ rel

end

#print axioms prependSlot_perfectCompleteness
#print axioms prependTarget_perfectCompleteness
#print axioms prependClaim_perfectCompleteness

end Spartan.Spec.Bricks

open OracleComp OracleInterface ProtocolSpec Function
open MvPolynomial OracleComp Sumcheck
open scoped NNReal

namespace Spartan.Spec.Bricks

variable {R : Type} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] [SampleableType R]
  (pp : Spartan.PublicParams) {ι : Type} (oSpec : OracleSpec ι)

/-! ## D1: honest RLC-target adapter relations (Spartan #114) -/

/-! ### Output relation and the D1 inclusion fix -/

/-- **Output relation of the honest RLC-target adapter.** R1CS satisfiability carried through, the
bundled claim oracle `.inl 0` holds the honest `evalClaimValue` (the `sendEvalClaim` guarantee), and
the carried target equals the *stored* RLC `∑ idx, r idx · oStmt(.inl 0) idx`. -/
def prependRLCTargetRelOut :
    Set (((R × Statement.AfterLinearCombination R pp) ×
        (∀ i, OracleStatement.AfterLinearCombination R pp i)) × Unit) :=
  { x | R1CS.relation R pp.toSizeR1CS x.1.1.2.2.2.2
          (fun idx => x.1.2 (.inr (.inl idx))) (x.1.2 (.inr (.inr 0)))
        ∧ (∀ idx, (show R from x.1.2 (.inl idx)) =
            evalClaimValue R pp x.1.1.2.2 (fun i => x.1.2 (.inr i)) idx)
        ∧ x.1.1.1 = ∑ idx, x.1.1.2.1 idx * (show R from x.1.2 (.inl idx)) }

/-- Input relation for the honest RLC-target adapter: the R1CS instance is still satisfied and the
bundled claim oracle `.inl 0` stores the honest `evalClaimValue`. The adapter adds exactly the RLC
target required by `prependRLCTargetRelOut`. -/
def prependRLCTargetRelIn :
    Set ((Statement.AfterLinearCombination R pp ×
        (∀ i, OracleStatement.AfterLinearCombination R pp i)) × Unit) :=
  { x | R1CS.relation R pp.toSizeR1CS x.1.1.2.2.2
          (fun idx => x.1.2 (.inr (.inl idx))) (x.1.2 (.inr (.inr 0)))
        ∧ (∀ idx, (show R from x.1.2 (.inl idx)) =
            evalClaimValue R pp x.1.1.2 (fun i => x.1.2 (.inr i)) idx) }

omit [IsDomain R] [Fintype R] [DecidableEq R] [SampleableType R] in
/-- **D1 key inclusion: the honest RLC-target output relation refines `secondSumcheckRelIn`.**
The stored-RLC carried target (`∑ r idx · oStmt(.inl 0) idx`) equals the `evalClaimValue`-RLC
required by `secondSumcheckRelIn`, once the bundled claim oracle holds the honest `evalClaimValue`.
This is the set-level fix for the `prependTarget` target-`0` mismatch (Composition.lean:109). -/
theorem prependRLCTargetRelOut_subset_secondSumcheckRelIn :
    prependRLCTargetRelOut (R := R) pp ⊆ secondSumcheckRelIn (R := R) pp := by
  rintro x ⟨hR1CS, hEval, ht⟩
  refine ⟨hR1CS, ?_⟩
  rw [ht]
  refine Finset.sum_congr rfl fun idx _ => ?_
  rw [hEval idx]

/-! ### Honest-run simulation of the RLC-target verifier -/

omit [IsDomain R] [Fintype R] [DecidableEq R] [SampleableType R] in
/-- A single claim-oracle query, simulated against the true oracle, returns the stored claim. -/
theorem simulateQ_queryClaimDirect
    (oStmt : ∀ i, OracleStatement.AfterLinearCombination R pp i)
    (msgs : ∀ i, (!p[] : ProtocolSpec 0).Message i) (idx : R1CS.MatrixIdx) :
    simulateQ (OracleInterface.simOracle2 oSpec oStmt msgs) (queryClaimDirect pp oSpec idx)
      = pure ((show R from oStmt (.inl idx))) := by
  unfold queryClaimDirect OracleInterface.simOracle2
  erw [simulateQ_query]
  simp only [QueryImpl.addLift_def, QueryImpl.id,
    OracleQuery.input_query, OracleQuery.cont_query,
    QueryImpl.add_apply_inr, QueryImpl.liftTarget_apply, simOracle0,
    OracleInterface.answer, _root_.map_pure, id_eq, liftM_pure]
  rfl

omit [IsDomain R] [Fintype R] [DecidableEq R] [SampleableType R] in
/-- One verifier step, simulated against the true oracle, returns `pure (some (idx, claim idx))`. -/
theorem simulateQ_rlcStep
    (oStmt : ∀ i, OracleStatement.AfterLinearCombination R pp i)
    (msgs : ∀ i, (!p[] : ProtocolSpec 0).Message i) (idx : R1CS.MatrixIdx) :
    simulateQ (OracleInterface.simOracle2 oSpec oStmt msgs)
      (rlcStep pp oSpec idx : OracleComp _ (Option (R1CS.MatrixIdx × R)))
      = (pure (some (idx, (show R from oStmt (.inl idx))))) := by
  simp [rlcStep, OptionT.run_bind, OptionT.run_monadLift, OptionT.run_pure,
    simulateQ_bind, simulateQ_queryClaimDirect, simulateQ_pure, _root_.map_pure, Option.map_some]
  change (Option.map (Prod.mk idx) <$>
    (some <$> (pure (show R from oStmt (.inl idx)) : OracleComp oSpec R))) = _
  rfl

omit [IsDomain R] [SampleableType R] in
/-- The honest RLC-target verifier, simulated against the true oracle, deterministically emits
`(∑ idx, r idx · oStmt(.inl 0) idx, stmt)`. -/
theorem simulateQ_prependRLCTargetVerifier
    (stmt : Statement.AfterLinearCombination R pp)
    (oStmt : ∀ i, OracleStatement.AfterLinearCombination R pp i)
    (msgs : ∀ i, (!p[] : ProtocolSpec 0).Message i)
    (chals : (!p[] : ProtocolSpec 0).Challenges) :
    simulateQ (OracleInterface.simOracle2 oSpec oStmt msgs)
      ((prependRLCTargetVerifier (R := R) pp oSpec).verify stmt chals
        : OracleComp _ (Option (R × Statement.AfterLinearCombination R pp)))
      = pure (some (∑ idx, stmt.1 idx * (show R from oStmt (.inl idx)), stmt)) := by
  change simulateQ (OracleInterface.simOracle2 oSpec oStmt msgs)
    (((Finset.univ : Finset R1CS.MatrixIdx).toList.mapM (rlcStep pp oSpec) >>= fun claims =>
      pure ((claims.map (fun p => stmt.1 p.1 * p.2)).sum, stmt) :
        OptionT (OracleComp _) (R × Statement.AfterLinearCombination R pp)).run) = _
  rw [OptionT.run_bind, Option.elimM, simulateQ_bind]
  erw [simulateQ_optionT_list_mapM_pure (OracleInterface.simOracle2 oSpec oStmt msgs)
      (rlcStep pp oSpec)
      (fun idx => ((idx, (show R from oStmt (.inl idx))) : R1CS.MatrixIdx × R)) _
      (fun idx => simulateQ_rlcStep pp oSpec oStmt msgs idx)]
  simp only [pure_bind, Option.elim_some, OptionT.run_pure, simulateQ_pure]
  congr 1
  congr 1
  rw [List.map_map,
    ← Finset.sum_map_toList Finset.univ (fun idx => stmt.1 idx * (show R from oStmt (.inl idx)))]
  rfl

omit [IsDomain R] [Fintype R] [DecidableEq R] [SampleableType R] in
/-- The honest RLC-target prover's run is deterministic: default (empty) transcript, RLC-prepended
statement, oracles carried through, unit witness. Definitional (`Fin.induction` base case of
`runToRound` at the 0-round spec). -/
theorem prependRLCTargetProver_run
    (stmt : Statement.AfterLinearCombination R pp)
    (oStmt : ∀ i, OracleStatement.AfterLinearCombination R pp i) :
    (prependRLCTargetProver (R := R) pp oSpec).run (stmt, oStmt) () =
      pure ((default : (!p[] : ProtocolSpec 0).FullTranscript),
        ((∑ idx, stmt.1 idx * (show R from oStmt (.inl idx)), stmt), oStmt), ()) := rfl

omit [IsDomain R] [SampleableType R] in
/-- The honest RLC-target adapter has a deterministic 0-round run. -/
theorem prependRLCTarget_run
    (stmt : Statement.AfterLinearCombination R pp)
    (oStmt : ∀ i, OracleStatement.AfterLinearCombination R pp i) :
    (prependRLCTarget (R := R) pp oSpec).toReduction.run (stmt, oStmt) () =
      (pure (((default : (!p[] : ProtocolSpec 0).FullTranscript),
          (((∑ idx, stmt.1 idx * (show R from oStmt (.inl idx)), stmt), oStmt), ())),
        ((∑ idx, stmt.1 idx * (show R from oStmt (.inl idx)), stmt), oStmt)) :
        OptionT (OracleComp _) _) := by
  change ((prependRLCTarget (R := R) pp oSpec).toReduction.run (stmt, oStmt) ()).run = _
  simp only [prependRLCTarget, OracleReduction.toReduction, Reduction.run,
    Verifier.run, OracleVerifier.toVerifier]
  rw [prependRLCTargetProver_run]
  simp only [liftM_pure, pure_bind, OptionT.run_bind, OptionT.run_monadLift,
    OptionT.run_mk, OptionT.run_map, OptionT.run_pure, Option.elimM, Option.getM_some]
  erw [simulateQ_prependRLCTargetVerifier]
  simp only [_root_.map_pure, Option.map_some, pure_bind, liftM_pure,
    Option.getM_some]
  rfl

/-- **The honest RLC-target adapter is perfectly complete.** From an input where the bundled
eval-claim oracle is honest, the 0-round adapter carries exactly the random linear combination
of the stored claims and preserves the oracle family. -/
theorem prependRLCTarget_perfectCompleteness {σ : Type} {init : ProbComp σ}
    {impl : QueryImpl oSpec (StateT σ ProbComp)} :
    (prependRLCTarget (R := R) pp oSpec).perfectCompleteness init impl
      (prependRLCTargetRelIn (R := R) pp) (prependRLCTargetRelOut (R := R) pp) := by
  apply Reduction.perfectCompleteness_of_run_support
  rintro ⟨stmt, oStmt⟩ ⟨⟩ hIn z hz
  rw [prependRLCTarget_run, OptionT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  subst z
  obtain ⟨hR1CS, hEval⟩ := hIn
  exact ⟨_, rfl, ⟨hR1CS, hEval, rfl⟩, rfl⟩

omit [IsDomain R] [Fintype R] [DecidableEq R] [SampleableType R] in
/-- The honest RLC-target output relation refines the **bridge-free** second-sum-check input
relation `secondSumcheckRelInBF` — the exact `relG` endpoint demanded by the composed-PC
consumer (`composedCompletenessStatement_of_five_leaves`, hypothesis `h₆`). Twin of
`prependRLCTargetRelOut_subset_secondSumcheckRelIn` for the `BF` restatement. -/
theorem prependRLCTargetRelOut_subset_secondSumcheckRelInBF :
    prependRLCTargetRelOut (R := R) pp ⊆ secondSumcheckRelInBF (R := R) pp := by
  rintro x ⟨hR1CS, hEval, ht⟩
  refine ⟨hR1CS, ?_⟩
  rw [ht]
  refine Finset.sum_congr rfl fun idx _ => ?_
  rw [hEval idx]

/-- **Consumer-endpoint form of the honest RLC-target adapter completeness**: perfectly complete
from `prependRLCTargetRelIn` into `secondSumcheckRelInBF`. This discharges hypothesis `h₆` of
`composedCompletenessStatement_of_five_leaves` (with `relF := prependRLCTargetRelIn`): the output
relation is exactly the bridge-free second-sum-check input relation pinned by the consumer. -/
theorem prependRLCTarget_perfectCompleteness_secondSumcheckRelInBF {σ : Type}
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)} :
    (prependRLCTarget (R := R) pp oSpec).perfectCompleteness init impl
      (prependRLCTargetRelIn (R := R) pp) (secondSumcheckRelInBF (R := R) pp) := by
  have h := prependRLCTarget_perfectCompleteness (R := R) pp oSpec
    (σ := σ) (init := init) (impl := impl)
  unfold OracleReduction.perfectCompleteness Reduction.perfectCompleteness at h ⊢
  exact Reduction.completeness_relOut_mono init impl
    (prependRLCTargetRelOut_subset_secondSumcheckRelInBF pp) h

#print axioms prependRLCTargetProver
#print axioms prependRLCTargetVerifier
#print axioms prependRLCTarget
#print axioms prependRLCTargetRelOut_subset_secondSumcheckRelIn
#print axioms simulateQ_prependRLCTargetVerifier
#print axioms prependRLCTargetProver_run
#print axioms prependRLCTarget_run
#print axioms prependRLCTarget_perfectCompleteness
#print axioms prependRLCTargetRelOut_subset_secondSumcheckRelInBF
#print axioms prependRLCTarget_perfectCompleteness_secondSumcheckRelInBF

end Spartan.Spec.Bricks


/-! ### finalCheck (the terminal `CheckClaim` phase) -/

namespace Bricks2

open Spartan.Spec Spartan.Spec.Bricks

variable {R : Type} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R]
  [VCVCompatible R]
  (pp : Spartan.PublicParams)
  {ι : Type} (oSpec : OracleSpec ι) [∀ q, Fintype (oSpec.Range q)] [∀ q, Inhabited (oSpec.Range q)]

/-- The 0-round `finalCheck` run collapses to `pure`: the prover is deterministic and the
verifier's `finalPredicate` queries are eliminated by the honest `simOracle2` (its result is
discarded by `CheckClaim`'s `let _ ←`). -/
theorem finalCheck_run (stmt : FinalStatement R pp) (oStmt : ∀ i, FinalOracleStatement R pp i) :
    (finalCheck R pp oSpec).toReduction.run (stmt, oStmt) () =
      (pure (((default : (!p[] : ProtocolSpec 0).FullTranscript), (stmt, oStmt), ()),
        (stmt, oStmt)) : OptionT (OracleComp oSpec) _) := by
  exact CheckClaim.oracleReduction_run_run stmt oStmt

/-- **`finalCheck` is perfectly complete** (0-round; the output relation is full). The relation-
freeness on the output side matches `finalCheckRelOut = Set.univ`-style consumers: the only content
is totality (the predicate's queries are simulated honestly and its result discarded) and
prover/verifier statement agreement. -/
theorem finalCheck_perfectCompleteness {σ : Type} {init : ProbComp σ}
    {impl : QueryImpl oSpec (StateT σ ProbComp)}
    (rel : Set (((FinalStatement R pp) × (∀ i, FinalOracleStatement R pp i)) × Unit)) :
    (finalCheck R pp oSpec).perfectCompleteness init impl rel Set.univ := by
  apply Reduction.perfectCompleteness_of_run_support
  rintro ⟨stmt, oStmt⟩ ⟨⟩ _ z hz
  simp only [finalCheck_run, OptionT.run_monadLift, OptionT.run_pure, liftM_pure,
    support_pure, Set.mem_singleton_iff] at hz
  subst z
  exact ⟨_, rfl, Set.mem_univ _, rfl⟩

end Bricks2
