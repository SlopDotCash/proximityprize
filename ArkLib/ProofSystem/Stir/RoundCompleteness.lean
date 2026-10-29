/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Stir.RoundProtocol
import ArkLib.OracleReduction.Completeness
import ArkLib.ProofSystem.Whir.FoldRound

/-!
# Issue #301 — perfect completeness of the STIR fold round

Discharges the stated obligation `StirIOP.Round.stirRoundReduction_completeness`
(`RoundProtocol.lean`, previously deferred pending heterogeneous round-peeling infrastructure):

* `unroll_2_message_VP` — the generic `[V_to_P, P_to_V]` 2-message unroll lemma (the missing
  round-peeling piece), specialised from the in-tree
  `OracleReduction.unroll_n_message_reduction_perfectCompleteness`.
* `stirRoundReduction_perfectCompleteness` — the honest prover combines its single codeword at
  its own degree, which by `combine_single_self` is the input oracle itself; the verifier
  forwards it and accepts, so the output relation reduces to the input relation.
* `stirRoundReduction_completeness_proved` — the stated `def : Prop` obligation, discharged.
* `Reduction.completenessFromRun_mono_error` + `stirRoundReduction_completeness_any_error` —
  generic error monotonicity and the any-`ε` corollary.

Axiom-clean (`[propext, Classical.choice, Quot.sound]`).
-/

open OracleSpec OracleComp ProtocolSpec STIR ReedSolomon NNReal OracleReduction

namespace StirIOP.Round

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable section

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

/-! The generic challenge-first unroll proof is owned by WHIR's fold-round module. -/
abbrev unroll_2_message_VP := @WhirIOP.FoldRound.unroll_2_message_VP

private noncomputable local instance (priority := low) stirRoundUniformAnswers
    {κ : Type} {spec : OracleSpec κ}
    [∀ q, Fintype (spec.Range q)] [∀ q, Inhabited (spec.Range q)] :
    OracleSpec.UniformAnswerMeasure spec :=
  OracleSpec.UniformAnswerMeasure.ofFiniteNonempty spec

private noncomputable local instance stirChallengeUniform {N : ℕ} (p : ProtocolSpec N)
    [∀ j, SampleableType (p.Challenge j)] :
    OracleSpec.UniformAnswerMeasure ([p.Challenge]ₒ'ProtocolSpec.challengeOracleInterface) := by
  letI : ∀ t, Finite (([p.Challenge]ₒ'ProtocolSpec.challengeOracleInterface).Range t)
    | ⟨j, ()⟩ => by change Finite (p.Challenge j); infer_instance
  letI : ∀ t, Nonempty (([p.Challenge]ₒ'ProtocolSpec.challengeOracleInterface).Range t)
    | ⟨j, ()⟩ => by change Nonempty (p.Challenge j); infer_instance
  exact OracleSpec.UniformAnswerMeasure.ofFiniteNonempty _

variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))

open scoped Classical in
/-- **Perfect completeness of the honest STIR fold-round object.** The honest prover combines its
single codeword at its own degree, which by `combine_single_self` is the input oracle itself; the
verifier forwards it and always accepts, so the output relation reduces to the input relation. -/
theorem stirRoundReduction_perfectCompleteness (φ : ι ↪ F) (deg : ℕ) (δ : ℝ≥0)
    (hInit : NeverFail init) :
    OracleReduction.perfectCompleteness init impl
      (stirRoundInputRel φ deg δ) (stirRoundOutputRel φ deg δ)
      (stirRoundReduction φ deg) := by
  rw [WhirIOP.FoldRound.unroll_2_message_VP (stirRoundReduction φ deg)
    (stirRoundInputRel φ deg δ) (stirRoundOutputRel φ deg δ) init impl hInit (by rfl) (by rfl)
    (by simp only [Set.fmap_eq_image, IsEmpty.forall_iff, implies_true])]
  intro stmtIn oStmtIn witIn h_relIn
  dsimp only [stirRoundReduction, stirRoundProver, stirRoundVerifier, OracleVerifier.toVerifier,
    OStmt, stirRoundInputRel, stirRoundOutputRel]
  simp only [Fin.isValue, bind_pure_comp, pure_bind, bind_map_left, liftM_bind, liftM_map,
    Prod.mk.eta, bind_assoc, map_pure, liftComp_pure, liftM_pure]
  apply (OptionT.prEvent_mk_eq_one_iff _ _).2
  intro value hvalue
  have hopt {κ : Type} {spec : OracleSpec.{0, 0} κ} {β : Type} (mx : OracleComp spec β) :
      (liftM mx : OptionT (OracleComp spec) β) = some <$> mx := by
    change (mx >>= fun x => pure (some x)) = some <$> mx
    rw [map_eq_bind_pure_comp]
    rfl
  obtain ⟨α, hα, hvalue⟩ := OracleComp.mem_support_bind_peel _ _ hvalue
  erw [hopt] at hα
  obtain ⟨a, _, ha⟩ := OracleComp.mem_support_map_peel _ _ hα
  subst α
  simp only [OptionT.run_map, OptionT.run_monadLift, OptionT.run_pure,
    simulateQ_pure, _root_.map_pure, Option.map_some, liftComp_pure] at hvalue
  have hv := OracleComp.eq_of_mem_support_pure _ hvalue
  subst value
  refine ⟨_, rfl, ?_, trivial, by funext u; rfl⟩
  have hc : Combine.combine φ deg a (fun _ : Fin 1 => oStmtIn ()) (fun _ : Fin 1 => deg)
      = oStmtIn () := combine_single_self φ deg a (oStmtIn ())
  change Code.relDistFromCode (oStmtIn ()) (ReedSolomon.code φ deg) ≤ (δ : ENNReal) at h_relIn
  change Code.relDistFromCode _ (ReedSolomon.code φ deg : Set (ι → F)) ≤ (δ : ENNReal)
  simp only [OracleVerifier.materializeOutput, OracleVerifier.materializeOutputOracle,
    FullTranscript.messages, FullTranscript.mk2, DFunLike.coe]
  change Code.relDistFromCode
    (Combine.combine φ deg a (fun _ : Fin 1 => oStmtIn ()) (fun _ : Fin 1 => deg))
    (ReedSolomon.code φ deg) ≤ (δ : ENNReal)
  rw [hc]
  exact h_relIn

/-- The stated `stirRoundReduction_completeness` obligation is discharged: the STIR fold-round
object is (perfectly) complete whenever the shared randomness never fails. -/
theorem stirRoundReduction_completeness_proved (φ : ι ↪ F) (deg : ℕ) (δ : ℝ≥0)
    (hInit : NeverFail init) :
    stirRoundReduction_completeness init impl φ deg δ :=
  stirRoundReduction_perfectCompleteness init impl φ deg δ hInit

/-- General error-monotonicity of `Reduction.completenessFromRun`: completeness with error `ε₁`
implies completeness with any larger error `ε₂` (the acceptance threshold `1 - ε` only drops). -/
theorem _root_.Reduction.completenessFromRun_mono_error
    {StmtIn WitIn StmtOut WitOut : Type}
    {ιᵣ : Type} {runSpec : OracleSpec ιᵣ} {σᵣ : Type} {Trace : Type}
    (runInit : ProbComp σᵣ)
    (runImpl : QueryImpl runSpec (StateT σᵣ ProbComp))
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (run : (stmtIn : StmtIn) → (witIn : WitIn) →
      OptionT (OracleComp runSpec) ((Trace × StmtOut × WitOut) × StmtOut))
    {ε₁ ε₂ : ℝ≥0} (hle : ε₁ ≤ ε₂)
    (h : Reduction.completenessFromRun runInit runImpl relIn relOut run ε₁) :
    Reduction.completenessFromRun runInit runImpl relIn relOut run ε₂ := by
  intro stmtIn witIn hIn
  refine le_trans ?_ (h stmtIn witIn hIn)
  exact tsub_le_tsub_left (by exact_mod_cast hle) 1

/-- **Strengthening**: the STIR fold-round object satisfies completeness with *every*
completeness error `ε` (not just `0`), as a corollary of its perfect completeness. -/
theorem stirRoundReduction_completeness_any_error (φ : ι ↪ F) (deg : ℕ) (δ ε : ℝ≥0)
    (hInit : NeverFail init) :
    (stirRoundReduction φ deg).completeness init impl
      (stirRoundInputRel φ deg δ) (stirRoundOutputRel φ deg δ) ε :=
  Reduction.completenessFromRun_mono_error _ _ _ _ _ (by positivity)
    (stirRoundReduction_perfectCompleteness init impl φ deg δ hInit)


end

end StirIOP.Round

#print axioms StirIOP.Round.unroll_2_message_VP
#print axioms StirIOP.Round.stirRoundReduction_perfectCompleteness
#print axioms StirIOP.Round.stirRoundReduction_completeness_proved
#print axioms Reduction.completenessFromRun_mono_error
#print axioms StirIOP.Round.stirRoundReduction_completeness_any_error
