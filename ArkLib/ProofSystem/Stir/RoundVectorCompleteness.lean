/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Stir.RoundCompleteness
import ArkLib.ProofSystem.Stir.RoundVector

/-! Scratch (#301): perfect completeness of the vectorised STIR fold round, mirroring
`stirRoundReduction_perfectCompleteness` over the `VectorSpec` wire format.

Key fix vs the earlier draft: the challenge oracle-spec instances are stated in the *pinned*
`[...]ₒ' (fun i => challengeOracleInterface i)` form, so they match the interface family that
`unroll_2_message_VP` was elaborated with (the generic `ProtocolSpec.challengeOracleInterface`),
rather than the global `OracleInterface.instVector` that wins in this file's context. -/

namespace StirIOP.Round

open OracleSpec OracleComp ProtocolSpec STIR ReedSolomon NNReal WhirIOP.Construction

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

noncomputable section

set_option linter.unusedSectionVars false

/-- A field is `VCVCompatible` (finite + inhabited via `0`); local since `Field` alone does not
register an `Inhabited` instance. -/
private local instance : VCVCompatible F := { toFintype := inferInstance, toInhabited := ⟨0⟩ }

/-- Challenge payloads of the vectorised fold-round spec are finite (they are `Vector F len`). -/
instance instStirVecChalFintype :
    ∀ i, Fintype (((stirRoundVSpec ι F).toProtocolSpec F).Challenge i) :=
  fun _ => by dsimp [ProtocolSpec.Challenge]; infer_instance

/-- Challenge payloads of the vectorised fold-round spec are inhabited. -/
instance instStirVecChalInhabited :
    ∀ i, Inhabited (((stirRoundVSpec ι F).toProtocolSpec F).Challenge i) :=
  fun _ => by dsimp [ProtocolSpec.Challenge]; infer_instance

private noncomputable local instance stirVectorUniformAnswers
    {κ : Type} {spec : OracleSpec κ}
    [∀ q, Fintype (spec.Range q)] [∀ q, Inhabited (spec.Range q)] :
    OracleSpec.UniformAnswerMeasure spec :=
  OracleSpec.UniformAnswerMeasure.ofFiniteNonempty spec

instance instStirVecChalSpecFintype : ∀ t,
    Fintype (([((stirRoundVSpec ι F).toProtocolSpec F).Challenge]ₒ'
      ProtocolSpec.challengeOracleInterface).Range t) := fun ⟨i, _⟩ => by
  change Fintype (((stirRoundVSpec ι F).toProtocolSpec F).Challenge i)
  infer_instance

instance instStirVecChalSpecInhabited : ∀ t,
    Inhabited (([((stirRoundVSpec ι F).toProtocolSpec F).Challenge]ₒ'
      ProtocolSpec.challengeOracleInterface).Range t) := fun ⟨i, _⟩ => by
  change Inhabited (((stirRoundVSpec ι F).toProtocolSpec F).Challenge i)
  infer_instance

variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))

open scoped Classical in
set_option maxHeartbeats 1600000 in
/-- **Perfect completeness of the vectorised STIR fold-round object.** The honest prover packs
the genuine `Combine.combine` of its single codeword; unpacking the wire payload recovers the
input oracle (`unpack_stirRoundVector_message`), the verifier forwards the packed message and
always accepts, so the vector output relation reduces to the input relation. -/
theorem stirRoundVectorReduction_perfectCompleteness (φ : ι ↪ F) (deg : ℕ) (δ : ℝ≥0)
    (hInit : NeverFail init) :
    OracleReduction.perfectCompleteness init impl
      (stirRoundInputRel φ deg δ) (stirRoundVectorOutputRel φ deg δ)
      (stirRoundVectorReduction φ deg) := by
  rw [unroll_2_message_VP (stirRoundVectorReduction φ deg)
    (stirRoundInputRel φ deg δ) (stirRoundVectorOutputRel φ deg δ) init impl hInit
    (by rfl) (by rfl)
    (by simp only [Set.fmap_eq_image, IsEmpty.forall_iff, implies_true])]
  intro stmtIn oStmtIn witIn h_relIn
  dsimp only [stirRoundVectorReduction, stirRoundVectorProver, stirRoundVectorVerifier,
    OracleVerifier.toVerifier, OStmt, VOStmt, stirRoundInputRel, stirRoundVectorOutputRel]
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
    simulateQ_pure, LawfulApplicative.map_pure, Option.map_some, liftComp_pure] at hvalue
  have hv := OracleComp.eq_of_mem_support_pure _ hvalue
  subst value
  refine ⟨_, rfl, ?_, trivial, by funext u; rfl⟩
  change Code.relDistFromCode (oStmtIn ()) (ReedSolomon.code φ deg) ≤ (δ : ENNReal) at h_relIn
  change Code.relDistFromCode (unpackFiniteFunction ι _)
    (ReedSolomon.code φ deg : Set (ι → F)) ≤ (δ : ENNReal)
  simp only [OracleVerifier.materializeOutput, OracleVerifier.materializeOutputOracle,
    FullTranscript.messages, FullTranscript.mk2, DFunLike.coe, id_eq]
  rw [unpack_stirRoundVector_message]
  exact h_relIn

/-- **Vector-level completeness with any error** `ε`, by error monotonicity. -/
theorem stirRoundVectorReduction_completeness_any_error (φ : ι ↪ F) (deg : ℕ) (δ ε : ℝ≥0)
    (hInit : NeverFail init) :
    (stirRoundVectorReduction φ deg).completeness init impl
      (stirRoundInputRel φ deg δ) (stirRoundVectorOutputRel φ deg δ) ε :=
  Reduction.completenessFromRun_mono_error _ _ _ _ _ (by positivity)
    (stirRoundVectorReduction_perfectCompleteness init impl φ deg δ hInit)

end

end StirIOP.Round

#print axioms StirIOP.Round.stirRoundVectorReduction_perfectCompleteness
#print axioms StirIOP.Round.stirRoundVectorReduction_completeness_any_error
