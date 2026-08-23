/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.RingSwitching.SumcheckPhase

set_option linter.unusedSimpArgs false

/-!
# Ring-Switching Iterated Sumcheck Round — Perfect Completeness (residual discharge)

This file discharges `iteratedSumcheckOracleReduction_perfectCompleteness_residual`
(`ArkLib.ProofSystem.RingSwitching.SumcheckPhase`), the per-round perfect-completeness
proposition for the profile-specialized structured sumcheck round, **without** the
`[IsDomain L]` instance carried by the in-file discharge
`iteratedSumcheckOracleReduction_perfectCompleteness_proved`.

The mathematical content is exactly the pure round logic already isolated as
`iteratedSumcheck_round_logic_complete`:

1. the honest prover's round univariate `h_i := getSumcheckRoundPoly … wit.H` passes the
   verifier's check `∑_{b ∈ D.points i} h_i.eval b = stmt.sumcheck_target`
   (`getSumcheckRoundPoly_points_sum_eq_cube` + the input sum-consistency), and
2. the honest round output advances the relation: the structural invariant advances via
   `fixFirstVariablesOfMQP_projectToMid_succ` and the sum-consistency via
   `getSumcheckRoundPoly_eval_eq_cube_succ`.

Neither step needs `L` to be a domain (no Schwartz–Zippel / root counting is involved in
completeness), so the residual holds for any nontrivial commutative ring `L`. The genuinely
required hypothesis is `hInit : NeverFail init`: perfect completeness is false for a failing
initial state computation (the run's failure probability would be positive). The oracle
implementation `impl` needs no hypothesis since `oSpec = []ₒ` has no queries (the
`hImplSupp` side condition of the unroll lemma is vacuous).

## Main declarations

- `iteratedSumcheckRound_perfectCompleteness_residual_holds`: the residual, from
  `NeverFail init` alone (no `IsDomain L`).
- `iteratedSumcheckRound_perfectCompleteness`: the consumer-facing corollary — per-round
  perfect completeness for every `i : Fin ℓ'`, via the residual's in-file consumer
  `iteratedSumcheckOracleReduction_perfectCompleteness`.
-/

open OracleSpec OracleComp ProtocolSpec Finset Polynomial MvPolynomial
  Module TensorProduct Nat Matrix
open scoped NNReal ProbabilityTheory
open Sumcheck.Structured

namespace RingSwitching.SumcheckPhase

noncomputable section

variable (κ : ℕ) [NeZero κ]
variable (L : Type) [CommRing L] [Nontrivial L] [Fintype L] [DecidableEq L]
  [SampleableType L]
variable (K : Type) [CommRing K] [Fintype K] [DecidableEq K]
variable [Algebra K L]
variable (P : RingSwitchingProfile K L κ)
variable (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']
variable (h_l : ℓ = ℓ' + κ)
variable (aOStmtIn : AbstractOStmtIn L ℓ')
variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

/-- `OptionT.bind` of an honest `pure (some a)` reduces to the continuation at `a`. Used to
collapse the verifier run after the message query has been resolved to a concrete answer.
(Local copy of the `private` helper in `SumcheckPhase`.) -/
private lemma optionT_bind_pure_some {ιₐ : Type} {specₐ : OracleSpec ιₐ} {α β : Type}
    (a : α) (g : α → OptionT (OracleComp specₐ) β) :
    OptionT.bind (OptionT.mk (pure (some a))) g = g a :=
  pure_bind a g

set_option maxHeartbeats 1000000 in
/-- **Residual discharge (no `IsDomain L`).** The per-round perfect-completeness residual
`iteratedSumcheckOracleReduction_perfectCompleteness_residual` holds for every nontrivial
commutative ring `L`, given only that the initial state computation never fails. This replays
the proof of `iteratedSumcheckOracleReduction_perfectCompleteness_proved` and confirms that
its `[IsDomain L]` instance is not load-bearing: the completeness algebra
(`iteratedSumcheck_round_logic_complete`) is domain-free. -/
theorem iteratedSumcheckRound_perfectCompleteness_residual_holds
    (hInit : NeverFail init) :
    iteratedSumcheckOracleReduction_perfectCompleteness_residual
      (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l)
      (aOStmtIn := aOStmtIn) (init := init) (impl := impl) := by
  classical
  haveI : Nonempty L := ⟨0⟩
  intro i
  rw [OracleReduction.unroll_2_message_reduction_perfectCompleteness (oSpec := []ₒ)
    (pSpec := pSpecSumcheckRound L) (init := init) (impl := impl)
    (hInit := hInit) (hDir0 := by rfl) (hDir1 := by rfl)
    (hImplSupp := by simp only [Set.fmap_eq_image, IsEmpty.forall_iff, implies_true])]
  intro stmtIn oStmtIn witIn h_relIn
  obtain ⟨h_V_check, _⟩ := iteratedSumcheck_round_logic_complete (κ := κ) (L := L) (K := K)
    (P := P) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l) (aOStmtIn := aOStmtIn) i stmtIn oStmtIn witIn
    h_relIn (Classical.arbitrary L)
  -- The honest verifier run collapses to `pure (next-round statement, oracle statements)`: it
  -- queries the prover message, the sum-check guard passes (logic-completeness conjunct 1), and
  -- it forwards the unchanged oracle statements.
  have hverify : ∀ r1 : L,
      (iteratedSumcheckOracleVerifier κ L K P ℓ ℓ' aOStmtIn i).toVerifier.verify (stmtIn, oStmtIn)
          (FullTranscript.mk2 (getSumcheckRoundPoly ℓ' (boolDomain L ℓ') i witIn.H) r1)
        = (pure
            (⟨{ sumcheck_target :=
                  Polynomial.eval r1 ↑(getSumcheckRoundPoly ℓ' (boolDomain L ℓ') i witIn.H),
                challenges := Fin.cons r1 stmtIn.challenges, ctx := stmtIn.ctx },
              oStmtIn⟩ :
              Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) i.succ
                × (∀ j, aOStmtIn.OStmtIn j))
            : OptionT (OracleComp []ₒ) _) := by
    intro r1
    obtain ⟨h_V_check, -⟩ := iteratedSumcheck_round_logic_complete (κ := κ) (L := L) (K := K)
      (P := P) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l) (aOStmtIn := aOStmtIn) i stmtIn oStmtIn witIn
      h_relIn r1
    simp only [OracleVerifier.toVerifier, iteratedSumcheckOracleVerifier,
      Sumcheck.Structured.roundOracleVerifier, FullTranscript.mk2, guard_eq]
    erw [OptionT.simulateQ_bind]
    erw [OptionT.simulateQ_simOracle2_liftM_query_T2]
    erw [optionT_bind_pure_some]
    erw [OptionT.simulateQ_bind]
    simp only [OptionT.simulateQ_ite, OptionT.simulateQ_pure, OptionT.simulateQ_failure]
    split_ifs with hc
    · erw [optionT_bind_pure_some]
      erw [OptionT.simulateQ_pure]
      erw [pure_bind]
      rfl
    · exact (hc h_V_check).elim
  rw [probEvent_eq_one_iff]
  dsimp only [iteratedSumcheckOracleReduction, iteratedSumcheckOracleProver,
    Sumcheck.Structured.roundOracleReduction,
    Sumcheck.Structured.roundOracleProver, FullTranscript.mk2]
  simp only [liftComp_pure, liftM_pure, pure_bind, bind_pure_comp, Function.comp, hverify,
    liftComp_pure, _root_.map_pure]
  refine ⟨?_, ?_⟩
  · -- No failure: a uniform challenge sample followed by `pure`.
    rw [probFailure_bind_eq_zero_iff]
    refine ⟨?_, fun r1 _ => ?_⟩
    · simp only [OptionT.probFailure_liftM, OracleComp.probFailure_liftComp,
        HasEvalPMF.probFailure_eq_zero]
    · rw [probFailure_map]
      erw [OracleComp.liftComp_pure]
      apply probFailure_pure
  · -- Correctness: the honest output lies in the round-`i.succ` relation.
    intro x hx
    simp only [OptionT.mem_support_iff, OptionT.run_bind, support_bind, Set.mem_iUnion,
      OptionT.run_pure, support_pure, Set.mem_singleton_iff, exists_prop, OptionT.run_map,
      OptionT.run_monadLift, support_map, support_liftM,
      Set.mem_image, _root_.map_pure] at hx
    obtain ⟨i_1, -, x_1, hx1, rfl⟩ := hx
    obtain ⟨_, h_rel_out⟩ := iteratedSumcheck_round_logic_complete (κ := κ) (L := L) (K := K)
      (P := P) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l) (aOStmtIn := aOStmtIn) i stmtIn oStmtIn witIn
      h_relIn i_1
    change x_1 ∈ _root_.support (pure _ : OptionT (OracleComp _) _) at hx1
    simp only [OptionT.mem_support_iff, OptionT.run_pure, support_pure, Set.mem_preimage,
      Set.mem_singleton_iff, Option.some.injEq] at hx1
    subst hx1
    exact ⟨h_rel_out, rfl, rfl⟩

/-- **Per-round perfect completeness (consumer form).** Every iterated ring-switching sumcheck
round `i : Fin ℓ'` is perfectly complete, from `NeverFail init` alone. This is the residual's
in-file consumer `iteratedSumcheckOracleReduction_perfectCompleteness` fed with the discharge
above. -/
theorem iteratedSumcheckRound_perfectCompleteness
    (hInit : NeverFail init) (i : Fin ℓ') :
    OracleReduction.perfectCompleteness
      (pSpec := pSpecSumcheckRound L)
      (relIn := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn i.castSucc)
      (relOut := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn i.succ)
      (oracleReduction := iteratedSumcheckOracleReduction κ L K P ℓ ℓ' aOStmtIn i)
      (init := init)
      (impl := impl) :=
  iteratedSumcheckOracleReduction_perfectCompleteness
    (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l)
    (aOStmtIn := aOStmtIn) (init := init) (impl := impl)
    (iteratedSumcheckRound_perfectCompleteness_residual_holds
      (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l)
      (aOStmtIn := aOStmtIn) (init := init) (impl := impl) hInit) i

end

end RingSwitching.SumcheckPhase
