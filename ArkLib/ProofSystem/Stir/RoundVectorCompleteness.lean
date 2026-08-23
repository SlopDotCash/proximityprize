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
local instance : VCVCompatible F := { toFintype := inferInstance, toInhabited := ⟨0⟩ }

/-- Challenge payloads of the vectorised fold-round spec are finite (they are `Vector F len`). -/
instance instStirVecChalFintype :
    ∀ i, Fintype (((stirRoundVSpec ι F).toProtocolSpec F).Challenge i) :=
  fun _ => by dsimp [ProtocolSpec.Challenge]; infer_instance

/-- Challenge payloads of the vectorised fold-round spec are inhabited. -/
instance instStirVecChalInhabited :
    ∀ i, Inhabited (((stirRoundVSpec ι F).toProtocolSpec F).Challenge i) :=
  fun _ => by dsimp [ProtocolSpec.Challenge]; infer_instance

/-- Finiteness of the vectorised fold-round challenge oracle spec, stated for the *pinned*
generic challenge interface (the family `unroll_2_message_VP` is elaborated with). -/
instance instStirVecChalSpecFintype :
    OracleSpec.Fintype
      ([((stirRoundVSpec ι F).toProtocolSpec F).Challenge]ₒ'
        (fun i => challengeOracleInterface i)) where
  fintype_B := fun ⟨i, _⟩ => by
    show Fintype (((stirRoundVSpec ι F).toProtocolSpec F).Challenge i)
    infer_instance

/-- Inhabitedness of the vectorised fold-round challenge oracle spec (pinned interface form). -/
instance instStirVecChalSpecInhabited :
    OracleSpec.Inhabited
      ([((stirRoundVSpec ι F).toProtocolSpec F).Challenge]ₒ'
        (fun i => challengeOracleInterface i)) where
  inhabited_B := fun ⟨i, _⟩ => by
    show Inhabited (((stirRoundVSpec ι F).toProtocolSpec F).Challenge i)
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
  rw [probEvent_eq_one_iff]
  refine ⟨?_, ?_⟩
  · -- SAFETY: the run never fails
    rw [probFailure_bind_eq_zero_iff]
    refine ⟨?_, fun α _hα => ?_⟩
    · simp only [probFailure_map, OptionT.probFailure_liftM, OptionT.probFailure_lift,
        _root_.probFailure_liftComp, HasEvalPMF.probFailure_eq_zero]
    · rw [probFailure_map, OptionT.probFailure_liftComp_of_OracleComp_Option]
      simp only [OptionT.run_map, OptionT.run_monadLift, OptionT.run_pure, _root_.map_pure,
        Function.comp_apply, Option.map_some, probFailure_map, HasEvalPMF.probFailure_eq_zero,
        probOutput_eq_zero_iff, support_map, support_liftM, Set.mem_image, reduceCtorEq,
        Set.mem_setOf_eq, not_exists, not_and, exists_const, not_false_eq_true, add_zero,
        zero_add]
      intro x hx
      erw [OptionT.simulateQ_pure, OptionT.run_pure] at hx
      simp only [support_pure, Set.mem_singleton_iff] at hx
      subst hx
      simp only [Option.map_some, reduceCtorEq, not_false_eq_true]
  · -- CORRECTNESS: every output in the support satisfies the relation + agreement
    intro x hx
    simp only [support_bind, Set.mem_iUnion, exists_prop] at hx
    obtain ⟨α, _hα, hx⟩ := hx
    rw [OptionT.mem_support_iff] at hx
    erw [OptionT.simulateQ_pure, OptionT.run_pure] at hx
    simp only [OptionT.run_map, OptionT.run_monadLift, OptionT.run_pure, _root_.map_pure,
      Function.comp_apply, Option.map_some, support_map, support_pure, Set.mem_image,
      Set.mem_singleton_iff, Option.some.injEq, exists_eq_left, exists_eq_right] at hx
    subst hx
    refine ⟨?_, trivial, by funext u; rfl⟩
    have hm : ∀ m : ((stirRoundVSpec ι F).toProtocolSpec F).«Type» 1,
        (fun _ : Unit =>
          (ProtocolSpec.FullTranscript.mk2 α m).messages ⟨1, stirRoundVSpec_dir_one⟩)
          = fun _ : Unit => m := fun _ => rfl
    rw [hm]
    exact stirRoundVectorOutputRel_of_inputRel φ deg δ _ h_relIn

/-- **Vector-level completeness with any error** `ε`, by error monotonicity. -/
theorem stirRoundVectorReduction_completeness_any_error (φ : ι ↪ F) (deg : ℕ) (δ ε : ℝ≥0)
    (hInit : NeverFail init) :
    (stirRoundVectorReduction φ deg).completeness init impl
      (stirRoundInputRel φ deg δ) (stirRoundVectorOutputRel φ deg δ) ε :=
  Reduction.completenessFromRun_mono_error _ _ _ _ _ (zero_le ε)
    (stirRoundVectorReduction_perfectCompleteness init impl φ deg δ hInit)

end

end StirIOP.Round

#print axioms StirIOP.Round.stirRoundVectorReduction_perfectCompleteness
#print axioms StirIOP.Round.stirRoundVectorReduction_completeness_any_error
