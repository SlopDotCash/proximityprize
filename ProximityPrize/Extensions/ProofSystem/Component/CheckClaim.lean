/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.ProofSystem.Component.CheckClaim

/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ProximityPrize.Extensions.OracleReduction.Security.RoundByRound
import ArkLib.OracleReduction.Security.ZeroKnowledge

/-!
  # Simple (Oracle) Reduction: Check if a predicate / claim on a statement is satisfied

  This is a zero-round (oracle) reduction. There is no witness.

  1. Reduction version: the input relation becomes a predicate on the statement. Verifier checks
     this predicate, and returns the same statement if successful.

  2. Oracle reduction version: the input relation becomes an oracle computation having as oracles
     the oracle statements, and taking in the (non-oracle) statement as an input (i.e. via
     `ReaderT`), and returning a `Prop`. Verifier performs this oracle computation, and returns the
     same statement & oracle statement if successful.

  In both cases, the output relation is trivial (since the input relation has been checked by the
  verifier).

  Note: after the refactor (to disallow failure in `OracleComp`), this may become a special case
  of `ReduceClaim`.
-/

open OracleComp OracleInterface ProtocolSpec Function

local instance : MeasurableSpace (FullTranscript !p[]) := ⊤

namespace CheckClaim

variable {ι : Type} (oSpec : OracleSpec ι) (Statement : Type)

section Reduction

variable (pred : Statement → Prop) [DecidablePred pred]

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- The honest transcript distribution for a valid `CheckClaim` statement is the deterministic
empty transcript. This is the concrete zero-round core used by the HVZK wrappers below. -/
theorem honestTranscriptDist_reduction_evalDist
    (stmt : Statement) (hpred : pred stmt) :
    evalDist (Reduction.honestTranscriptDist init impl
        (reduction oSpec Statement pred) stmt ()) =
      evalDist (pure default : OptionT ProbComp (FullTranscript !p[])) := by
  classical
  unfold Reduction.honestTranscriptDist
  have hrun : (reduction oSpec Statement pred).run stmt () =
      (pure ((default, stmt, ()), stmt) : OptionT (OracleComp _) _) := by
    simp [reduction, Reduction.run, prover, verifier, Prover.run, Verifier.run,
          Prover.runToRound, guard, ite_eq_left hpred]
    rfl
  simp only [hrun, map_pure, OptionT.run_pure, simulateQ_pure, StateT.run'_eq,
    StateT.run_pure, bind_pure_comp]
  rw [OptionT.evalDist_eq_comap_some, OptionT.evalDist_eq_comap_some]
  simp only [OptionT.run_mk, OptionT.run_pure, OracleComp.evalDist_map_const, evalDist_pure]

/-- `CheckClaim` is perfectly HVZK for the predicate relation. The simulator is the identity
transcript simulator, since the real protocol has no messages or challenges. -/
theorem reduction_perfectHVZK :
    Reduction.perfectHVZK init impl (relIn Statement pred)
      (reduction oSpec Statement pred) Reduction.idTranscriptSimulator := by
  intro stmt wit hrel
  cases wit
  exact (honestTranscriptDist_reduction_evalDist oSpec Statement pred stmt hrel).symm

/-- Perfect HVZK implies statistical HVZK at every error budget. -/
theorem reduction_statisticalHVZK (ε : NNReal) :
    Reduction.statisticalHVZK init impl (relIn Statement pred)
      (reduction oSpec Statement pred) Reduction.idTranscriptSimulator ε :=
  (reduction_perfectHVZK oSpec Statement pred).statisticalHVZK ε

/-- `CheckClaim` has an explicit perfect-HVZK simulator. -/
theorem reduction_isHVZK :
    Reduction.isHVZK init impl (relIn Statement pred) (reduction oSpec Statement pred) :=
  ⟨Reduction.idTranscriptSimulator, reduction_perfectHVZK oSpec Statement pred⟩

/-- `CheckClaim` has statistical HVZK at every error budget. -/
theorem reduction_isStatHVZK (ε : NNReal) :
    Reduction.isStatHVZK init impl (relIn Statement pred) (reduction oSpec Statement pred) ε :=
  (reduction_isHVZK oSpec Statement pred).isStatHVZK ε

/-- The round-by-round extractor for the `CheckClaim` reduction. Trivial since the witness is
  `Unit`. -/
def extractor : Extractor.RoundByRound oSpec Statement Unit Unit !p[] (fun _ => Unit) where
  extractIn := fun _ wit => wit
  extractMid := fun i => Fin.elim0 i
  extractOut := fun _ _ witOut => witOut

#print axioms CheckClaim.honestTranscriptDist_reduction_evalDist
#print axioms CheckClaim.reduction_perfectHVZK
#print axioms CheckClaim.reduction_statisticalHVZK
#print axioms CheckClaim.reduction_isHVZK
#print axioms CheckClaim.reduction_isStatHVZK

end Reduction

section OracleReduction

variable {ιₛ : Type} (OStatement : ιₛ → Type) [∀ i, OracleInterface (OStatement i)]

variable (pred : ReaderT Statement (OracleComp [OStatement]ₒ) Prop)
  -- (hPred : ∀ stmt, NeverFail (pred stmt))

variable {Statement} {OStatement}

-- @[reducible, simp]
-- def toRelInput : Set ((Statement × (∀ i, OStatement i)) × Unit) :=
--   { ⟨⟨stmt, oStmt⟩, _⟩ | simulateQ' (toOracleImpl OStatement oStmt) (pred stmt) (hPred stmt) }

-- -- theorem oracleProver_run

-- variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

-- /-- The `CheckClaim` reduction satisfies perfect completeness. -/
-- @[simp]
-- theorem oracleReduction_completeness (h : init.neverFails) :
--     (oracleReduction oSpec Statement OStatement pred).perfectCompleteness init impl
--     (toRelInput pred hPred) Set.univ := by
--   simp only [OracleReduction.perfectCompleteness, toRelInput, OracleReduction.toReduction,
--     oracleReduction, oracleProver, Nat.reduceAdd, Fin.isValue, MessageIdx, Message, ChallengeIdx,
--     Challenge, Fin.reduceLast, oracleVerifier, bind_pure_comp, OracleVerifier.toVerifier,
--     simulateQ_map, Embedding.inl_apply, eq_mpr_eq_cast, cast_eq, Functor.map_map,
--     Reduction.perfectCompleteness_eq_prob_one, Set.mem_setOf_eq, StateT.run'_eq, Set.mem_univ,
--     true_and, probEvent_eq_one_iff, probFailure_eq_zero_iff, neverFails_bind_iff, h,
--     neverFails_map_iff, support_bind, support_map, Set.mem_iUnion, Set.mem_image, Prod.exists,
--     exists_and_right, exists_eq_right, exists_prop, forall_exists_index, and_imp, Prod.forall,
--     Fin.forall_fin_zero_pi, Prod.mk.injEq]
--   simp only [Reduction.run, Prover.run, Verifier.run, toOracleImpl, simulateQ']
--   simp only [ChallengeIdx, Fin.reduceLast, Prover.runToRound_zero_of_prover_first, Fin.isValue,
--     bind_pure_comp, liftM_eq_liftComp, liftComp_map, Functor.map_map, pure_bind]

end OracleReduction

end CheckClaim
