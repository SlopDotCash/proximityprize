/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Stir.VectorChain
import ArkLib.ProofSystem.Stir.Round3Completeness
import ArkLib.OracleReduction.Composition.Sequential.SeqComposeOracleCompleteness
import ArkLib.OracleReduction.Composition.Sequential.AppendPerfectCompletenessOracle
import ArkLib.OracleReduction.Composition.Sequential.AppendToVerifierKeystone
import ArkLib.OracleReduction.Composition.Sequential.ChallengeOracleFintype

/-!
# Perfect completeness of the VECTORISED STIR chain (#301)

Per-block perfect completeness of the vectorised STIR chain blocks
(`stirInitVectorReduction`, `stirRound3VectorReduction`, `stirRound3VectorReductionMid`,
`stirFinalVectorReductionMid`), against the vector-payload statement-indexed proximity
relation `stirVOStmtRel` (the unpacked oracle is `δ`-close), then the M-block mid phase and
the three append seams — the vector mirror of `BlockCompleteness`/`Round3Completeness`/
`BlocksCompleteness`/`TailCompleteness`/`ChainCompleteness`. -/

namespace StirIOP

namespace Round3

open OracleSpec OracleComp ProtocolSpec STIR ReedSolomon NNReal StirIOP.Round OracleReduction
open WhirIOP.Construction (packFiniteFunction unpackFiniteFunction unpack_packFiniteFunction)

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- A field is `VCVCompatible` (finite + inhabited via `0`); local since `Field` alone does
not register an `Inhabited` instance (the `RoundVectorCompleteness` idiom). -/
local instance : VCVCompatible F := { toFintype := inferInstance, toInhabited := ⟨0⟩ }

/-- **The uniform statement-indexed VECTOR proximity relation**: the UNPACKED oracle is
`δ`-close to the Reed-Solomon code, for any statement type `S` (the statement carries protocol
randomness, which the proximity relation ignores). The vector-payload mirror of
`stirOStmtRel`; instantiates to the input/output relations of every packed-oracle block of the
vectorised STIR chain: `S = F` (post-first-block / inter-block), `S = F × F` (post-final). -/
noncomputable def stirVOStmtRel (S : Type) (φ : ι ↪ F) (deg : ℕ) (δ : ℝ≥0) :
    Set ((S × ∀ i, VOStmt ι F i) × Unit) :=
  fun ⟨⟨_, oracle⟩, _⟩ =>
    Code.relDistFromCode (unpackFiniteFunction ι (oracle ())) (ReedSolomon.code φ deg)
      ≤ (δ : ENNReal)

/-! ### Per-challenge instances for the vector specs (every challenge payload is a
`Vector F len`), plus the challenge oracle-spec instances in the *pinned*
`[...]ₒ' (fun i => challengeOracleInterface i)` form (the `RoundVectorCompleteness` gotcha:
they must match the interface family the unroll lemmas were elaborated with). -/

instance instStirInitVChalFintype :
    ∀ i, Fintype (((stirInitVSpec).toProtocolSpec F).Challenge i) :=
  fun _ => by dsimp [ProtocolSpec.Challenge]; infer_instance

instance instStirInitVChalInhabited :
    ∀ i, Inhabited (((stirInitVSpec).toProtocolSpec F).Challenge i) :=
  fun _ => by dsimp [ProtocolSpec.Challenge]; infer_instance

instance instStirRound3VChalFintype :
    ∀ i, Fintype (((stirRound3VSpec ι F).toProtocolSpec F).Challenge i) :=
  fun _ => by dsimp [ProtocolSpec.Challenge]; infer_instance

instance instStirRound3VChalInhabited :
    ∀ i, Inhabited (((stirRound3VSpec ι F).toProtocolSpec F).Challenge i) :=
  fun _ => by dsimp [ProtocolSpec.Challenge]; infer_instance

instance instStirFinalVChalFintype :
    ∀ i, Fintype (((stirFinalVSpec ι F).toProtocolSpec F).Challenge i) :=
  fun _ => by dsimp [ProtocolSpec.Challenge]; infer_instance

instance instStirFinalVChalInhabited :
    ∀ i, Inhabited (((stirFinalVSpec ι F).toProtocolSpec F).Challenge i) :=
  fun _ => by dsimp [ProtocolSpec.Challenge]; infer_instance

instance instStirInitVChalSpecFintype :
    OracleSpec.Fintype
      ([((stirInitVSpec).toProtocolSpec F).Challenge]ₒ'
        (fun i => challengeOracleInterface i)) where
  fintype_B := fun ⟨i, _⟩ => by
    show Fintype (((stirInitVSpec).toProtocolSpec F).Challenge i)
    infer_instance

instance instStirInitVChalSpecInhabited :
    OracleSpec.Inhabited
      ([((stirInitVSpec).toProtocolSpec F).Challenge]ₒ'
        (fun i => challengeOracleInterface i)) where
  inhabited_B := fun ⟨i, _⟩ => by
    show Inhabited (((stirInitVSpec).toProtocolSpec F).Challenge i)
    infer_instance

instance instStirRound3VChalSpecFintype :
    OracleSpec.Fintype
      ([((stirRound3VSpec ι F).toProtocolSpec F).Challenge]ₒ'
        (fun i => challengeOracleInterface i)) where
  fintype_B := fun ⟨i, _⟩ => by
    show Fintype (((stirRound3VSpec ι F).toProtocolSpec F).Challenge i)
    infer_instance

instance instStirRound3VChalSpecInhabited :
    OracleSpec.Inhabited
      ([((stirRound3VSpec ι F).toProtocolSpec F).Challenge]ₒ'
        (fun i => challengeOracleInterface i)) where
  inhabited_B := fun ⟨i, _⟩ => by
    show Inhabited (((stirRound3VSpec ι F).toProtocolSpec F).Challenge i)
    infer_instance

instance instStirFinalVChalSpecFintype :
    OracleSpec.Fintype
      ([((stirFinalVSpec ι F).toProtocolSpec F).Challenge]ₒ'
        (fun i => challengeOracleInterface i)) where
  fintype_B := fun ⟨i, _⟩ => by
    show Fintype (((stirFinalVSpec ι F).toProtocolSpec F).Challenge i)
    infer_instance

instance instStirFinalVChalSpecInhabited :
    OracleSpec.Inhabited
      ([((stirFinalVSpec ι F).toProtocolSpec F).Challenge]ₒ'
        (fun i => challengeOracleInterface i)) where
  inhabited_B := fun ⟨i, _⟩ => by
    show Inhabited (((stirFinalVSpec ι F).toProtocolSpec F).Challenge i)
    infer_instance

/-! ### Per-block perfect completeness -/

variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))

open scoped Classical in
set_option maxHeartbeats 800000 in
/-- **Perfect completeness of the vectorised initial `[C_fold]` block**: the prover reads the
fold challenge off its `Vector F 1` payload and forwards the (still function-shaped) oracle
unchanged; the verifier reads the same challenge off the transcript, so agreement is
definitional and the proximity relation transfers verbatim. -/
theorem stirInitVectorReduction_perfectCompleteness (φ : ι ↪ F) (deg : ℕ) (δ : ℝ≥0)
    (hInit : NeverFail init) :
    OracleReduction.perfectCompleteness init impl
      (stirOStmtRel Unit φ deg δ) (stirOStmtRel F φ deg δ)
      (stirInitVectorReduction (ι := ι) (F := F)) := by
  rw [OracleReduction.unroll_1_message_reduction_perfectCompleteness_V_to_P
    (stirInitVectorReduction (ι := ι) (F := F))
    (stirOStmtRel Unit φ deg δ) (stirOStmtRel F φ deg δ) init impl hInit (by rfl)
    (by simp only [Set.fmap_eq_image, IsEmpty.forall_iff, implies_true])]
  intro stmtIn oStmtIn witIn h_relIn
  dsimp only [stirInitVectorReduction, stirInitVectorProver, stirInitVectorVerifier,
    OracleVerifier.toVerifier, OStmt, stirOStmtRel]
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
  · -- CORRECTNESS
    intro x hx
    simp only [support_bind, Set.mem_iUnion, exists_prop] at hx
    obtain ⟨α, _hα, hx⟩ := hx
    rw [OptionT.mem_support_iff] at hx
    erw [OptionT.simulateQ_pure, OptionT.run_pure] at hx
    simp only [OptionT.run_map, OptionT.run_monadLift, OptionT.run_pure, _root_.map_pure,
      Function.comp_apply, Option.map_some, support_map, support_pure, Set.mem_image,
      Set.mem_singleton_iff, Option.some.injEq, exists_eq_left, exists_eq_right] at hx
    subst hx
    exact ⟨h_relIn, rfl, by funext u; rfl⟩

open scoped Classical in
set_option maxHeartbeats 800000 in
/-- **Perfect completeness of the vectorised first 3-slot block** (`OStmt → VOStmt`): the
honest prover packs the genuine `Combine.combine` of its single codeword, which unpacks back
to the input oracle (`unpack_stirRound3Vector_message`); the verifier forwards the packed
message and outputs the shift challenge, so agreement is definitional and the function-level
input relation transfers to the vector output relation. -/
theorem stirRound3VectorReduction_perfectCompleteness (φ : ι ↪ F) (deg : ℕ) (δ : ℝ≥0)
    (hInit : NeverFail init) :
    OracleReduction.perfectCompleteness init impl
      (stirOStmtRel F φ deg δ) (stirVOStmtRel F φ deg δ)
      (stirRound3VectorReduction φ deg) := by
  rw [unroll_3_message_reduction_perfectCompleteness_PVV (stirRound3VectorReduction φ deg)
    (stirOStmtRel F φ deg δ) (stirVOStmtRel F φ deg δ) init impl hInit
    (by rfl) (by rfl) (by rfl)
    (by simp only [Set.fmap_eq_image, IsEmpty.forall_iff, implies_true])]
  intro stmtIn oStmtIn witIn h_relIn
  dsimp only [stirRound3VectorReduction, stirRound3VectorProver, stirRound3VectorVerifier,
    OracleVerifier.toVerifier, OStmt, VOStmt, stirOStmtRel, stirVOStmtRel]
  simp only [Fin.isValue, bind_pure_comp, pure_bind, bind_map_left, liftM_bind, liftM_map,
    Prod.mk.eta, bind_assoc, map_pure, liftComp_pure, liftM_pure]
  rw [probEvent_eq_one_iff]
  refine ⟨?_, ?_⟩
  · -- SAFETY: the run never fails
    rw [probFailure_bind_eq_zero_iff]
    refine ⟨?_, fun r1 _h1 => ?_⟩
    · simp only [probFailure_map, OptionT.probFailure_liftM, OptionT.probFailure_lift,
        _root_.probFailure_liftComp, HasEvalPMF.probFailure_eq_zero]
    · rw [probFailure_bind_eq_zero_iff]
      refine ⟨?_, fun r2 _h2 => ?_⟩
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
  · -- CORRECTNESS
    intro x hx
    simp only [support_bind, Set.mem_iUnion, exists_prop] at hx
    obtain ⟨r1, _h1, hx⟩ := hx
    obtain ⟨r2, _h2, hx⟩ := hx
    rw [OptionT.mem_support_iff] at hx
    erw [OptionT.simulateQ_pure, OptionT.run_pure] at hx
    simp only [OptionT.run_map, OptionT.run_monadLift, OptionT.run_pure, _root_.map_pure,
      Function.comp_apply, Option.map_some, support_map, support_pure, Set.mem_image,
      Set.mem_singleton_iff, Option.some.injEq, exists_eq_left, exists_eq_right] at hx
    subst hx
    refine ⟨?_, rfl, by funext u; rfl⟩
    show Code.relDistFromCode
        (unpackFiniteFunction ι (packFiniteFunction ι
          (Combine.combine φ deg stmtIn (fun _ : Fin 1 => oStmtIn ())
            (fun _ : Fin 1 => deg))))
        (ReedSolomon.code φ deg) ≤ (δ : ENNReal)
    rw [unpack_packFiniteFunction, combine_single_self]
    exact h_relIn

open scoped Classical in
set_option maxHeartbeats 800000 in
/-- **Perfect completeness of the mid-chain vectorised 3-slot block** (`VOStmt → VOStmt`): the
incoming oracle arrives packed and is unpacked before folding; the honest fold packs back, and
the round trip collapses (`unpack_stirRound3VectorMid_message`-style), so the vector relation
is preserved verbatim. This is the per-block fact the n-ary mid-phase engine consumes. -/
theorem stirRound3VectorReductionMid_perfectCompleteness (φ : ι ↪ F) (deg : ℕ) (δ : ℝ≥0)
    (hInit : NeverFail init) :
    OracleReduction.perfectCompleteness init impl
      (stirVOStmtRel F φ deg δ) (stirVOStmtRel F φ deg δ)
      (stirRound3VectorReductionMid φ deg) := by
  rw [unroll_3_message_reduction_perfectCompleteness_PVV (stirRound3VectorReductionMid φ deg)
    (stirVOStmtRel F φ deg δ) (stirVOStmtRel F φ deg δ) init impl hInit
    (by rfl) (by rfl) (by rfl)
    (by simp only [Set.fmap_eq_image, IsEmpty.forall_iff, implies_true])]
  intro stmtIn oStmtIn witIn h_relIn
  dsimp only [stirRound3VectorReductionMid, stirRound3VectorProverMid,
    stirRound3VectorVerifierMid, OracleVerifier.toVerifier, VOStmt, stirVOStmtRel]
  simp only [Fin.isValue, bind_pure_comp, pure_bind, bind_map_left, liftM_bind, liftM_map,
    Prod.mk.eta, bind_assoc, map_pure, liftComp_pure, liftM_pure]
  rw [probEvent_eq_one_iff]
  refine ⟨?_, ?_⟩
  · -- SAFETY: the run never fails
    rw [probFailure_bind_eq_zero_iff]
    refine ⟨?_, fun r1 _h1 => ?_⟩
    · simp only [probFailure_map, OptionT.probFailure_liftM, OptionT.probFailure_lift,
        _root_.probFailure_liftComp, HasEvalPMF.probFailure_eq_zero]
    · rw [probFailure_bind_eq_zero_iff]
      refine ⟨?_, fun r2 _h2 => ?_⟩
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
  · -- CORRECTNESS
    intro x hx
    simp only [support_bind, Set.mem_iUnion, exists_prop] at hx
    obtain ⟨r1, _h1, hx⟩ := hx
    obtain ⟨r2, _h2, hx⟩ := hx
    rw [OptionT.mem_support_iff] at hx
    erw [OptionT.simulateQ_pure, OptionT.run_pure] at hx
    simp only [OptionT.run_map, OptionT.run_monadLift, OptionT.run_pure, _root_.map_pure,
      Function.comp_apply, Option.map_some, support_map, support_pure, Set.mem_image,
      Set.mem_singleton_iff, Option.some.injEq, exists_eq_left, exists_eq_right] at hx
    subst hx
    refine ⟨?_, rfl, by funext u; rfl⟩
    show Code.relDistFromCode
        (unpackFiniteFunction ι (packFiniteFunction ι
          (Combine.combine φ deg stmtIn
            (fun _ : Fin 1 => unpackFiniteFunction ι (oStmtIn ()))
            (fun _ : Fin 1 => deg))))
        (ReedSolomon.code φ deg) ≤ (δ : ENNReal)
    rw [unpack_packFiniteFunction, combine_single_self]
    exact h_relIn

open scoped Classical in
set_option maxHeartbeats 800000 in
/-- **Perfect completeness of the mid-chain vectorised final `[p, C_fin]` block**
(`VOStmt → VOStmt`): the prover sends its (already packed) oracle in the clear and threads
`(pending randomness, repetition challenge)` into the statement; the verifier exposes the same
message as the output oracle, so agreement is definitional and the vector proximity relation
transfers verbatim. -/
theorem stirFinalVectorReductionMid_perfectCompleteness (φ : ι ↪ F) (deg : ℕ) (δ : ℝ≥0)
    (hInit : NeverFail init) :
    OracleReduction.perfectCompleteness init impl
      (stirVOStmtRel F φ deg δ) (stirVOStmtRel (F × F) φ deg δ)
      (stirFinalVectorReductionMid (ι := ι) (F := F)) := by
  rw [OracleReduction.unroll_2_message_reduction_perfectCompleteness
    (stirFinalVectorReductionMid (ι := ι) (F := F))
    (stirVOStmtRel F φ deg δ) (stirVOStmtRel (F × F) φ deg δ) init impl hInit
    (by rfl) (by rfl)
    (by simp only [Set.fmap_eq_image, IsEmpty.forall_iff, implies_true])]
  intro stmtIn oStmtIn witIn h_relIn
  dsimp only [stirFinalVectorReductionMid, stirFinalVectorProverMid, stirFinalVectorVerifierMid,
    OracleVerifier.toVerifier, VOStmt, stirVOStmtRel]
  simp only [Fin.isValue, bind_pure_comp, pure_bind, bind_map_left, liftM_bind, liftM_map,
    Prod.mk.eta, bind_assoc, map_pure, liftComp_pure, liftM_pure]
  rw [probEvent_eq_one_iff]
  refine ⟨?_, ?_⟩
  · -- SAFETY
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
  · -- CORRECTNESS
    intro x hx
    simp only [support_bind, Set.mem_iUnion, exists_prop] at hx
    obtain ⟨α, _hα, hx⟩ := hx
    rw [OptionT.mem_support_iff] at hx
    erw [OptionT.simulateQ_pure, OptionT.run_pure] at hx
    simp only [OptionT.run_map, OptionT.run_monadLift, OptionT.run_pure, _root_.map_pure,
      Function.comp_apply, Option.map_some, support_map, support_pure, Set.mem_image,
      Set.mem_singleton_iff, Option.some.injEq, exists_eq_left, exists_eq_right] at hx
    subst hx
    exact ⟨h_relIn, rfl, by funext u; rfl⟩

/-! ### The M-block vectorised mid phase -/

open scoped Classical in
/-- **Perfect completeness of the M-block vectorised mid phase**
(`stirVectorBlocksReduction`): the `seqCompose` of `M` packed-threading 3-slot blocks is
perfectly complete against the constant relation family `stirVOStmtRel F φ deg δ`, by the
oracle-level n-ary composition engine fed with the per-block completeness
`stirRound3VectorReductionMid_perfectCompleteness`. -/
theorem stirVectorBlocksReduction_perfectCompleteness (φ : ι ↪ F) (deg : ℕ) (M : ℕ) (δ : ℝ≥0)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery []ₒ β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp []ₒ β)) :
    (stirVectorBlocksReduction φ deg M).perfectCompleteness init impl
      (stirVOStmtRel F φ deg δ) (stirVOStmtRel F φ deg δ) :=
  OracleReduction.seqCompose_perfectCompleteness_threaded
    (fun _ : Fin (M + 1) => F) (fun _ => VOStmt ι F) (fun _ => Unit)
    (fun _ => stirRound3VectorReductionMid φ deg)
    (coh := fun _ => instStirRound3VectorReductionMidAppendCoherent φ deg)
    (fun _ => stirVOStmtRel F φ deg δ)
    (fun _ => ⟨by omega, stirRound3VSpec_dir_zero⟩)
    hInit hImplSupp
    (fun _ => stirRound3VectorReductionMid_perfectCompleteness init impl φ deg δ hInit)

/-! ### Seam A: the blocks∘finalMid tail -/

/-- **The blocks∘finalMid tail of the vectorised STIR chain** as a named object (the inner
append of `stirFullVectorReduction`). -/
noncomputable def stirVectorTailReduction (φ : ι ↪ F) (deg : ℕ) (M : ℕ) :
    OracleReduction []ₒ F (VOStmt ι F) Unit (F × F) (VOStmt ι F) Unit
      ((ProtocolSpec.seqCompose (fun _ : Fin M => (stirRound3VSpec ι F).toProtocolSpec F))
        ++ₚ ((stirFinalVSpec ι F).toProtocolSpec F)) :=
  OracleReduction.append (stirVectorBlocksReduction φ deg M) stirFinalVectorReductionMid

open scoped Classical in
set_option maxHeartbeats 2000000 in
/-- **Perfect completeness of the blocks∘finalMid tail** of the vectorised STIR chain, via the
`Reduction`-level message-seam keystone (the `TailCompleteness` recipe: step down through
`toReduction` by equation-lemma unfolds, combined-oracle seam instances from the in-tree
`ChallengeOracleFintype` helpers). -/
theorem stirVectorTailReduction_perfectCompleteness (φ : ι ↪ F) (deg : ℕ) (M : ℕ) (δ : ℝ≥0)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery []ₒ β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp []ₒ β)) :
    (stirVectorTailReduction φ deg M).perfectCompleteness init impl
      (stirVOStmtRel F φ deg δ) (stirVOStmtRel (F × F) φ deg δ) := by
  haveI : (([]ₒ : OracleSpec PEmpty)).Inhabited := { inhabited_B := fun i => nomatch i }
  haveI : (([]ₒ : OracleSpec PEmpty)).Fintype := { fintype_B := fun i => nomatch i }
  haveI := ProtocolSpec.appendCombinedOracle_fintype []ₒ
    (ProtocolSpec.seqCompose (fun _ : Fin M => (stirRound3VSpec ι F).toProtocolSpec F))
    ((stirFinalVSpec ι F).toProtocolSpec F)
  haveI := ProtocolSpec.appendCombinedOracle_inhabited []ₒ
    (ProtocolSpec.seqCompose (fun _ : Fin M => (stirRound3VSpec ι F).toProtocolSpec F))
    ((stirFinalVSpec ι F).toProtocolSpec F)
  haveI := ProtocolSpec.seqComposeCombinedOracle_fintype []ₒ
    (fun _ : Fin M => (stirRound3VSpec ι F).toProtocolSpec F)
  haveI := ProtocolSpec.seqComposeCombinedOracle_inhabited []ₒ
    (fun _ : Fin M => (stirRound3VSpec ι F).toProtocolSpec F)
  have hDirSeam : ((ProtocolSpec.seqCompose
        (fun _ : Fin M => (stirRound3VSpec ι F).toProtocolSpec F))
      ++ₚ ((stirFinalVSpec ι F).toProtocolSpec F)).dir
      (⟨Fin.vsum (fun _ : Fin M => 3), by omega⟩
        : Fin ((Fin.vsum (fun _ : Fin M => 3)) + 2)) = .P_to_V := by
    show (Fin.vappend (ProtocolSpec.seqCompose
        (fun _ : Fin M => (stirRound3VSpec ι F).toProtocolSpec F)).dir
        ((stirFinalVSpec ι F).toProtocolSpec F).dir) _ = .P_to_V
    have h0 : (⟨Fin.vsum (fun _ : Fin M => 3), by omega⟩
          : Fin ((Fin.vsum (fun _ : Fin M => 3)) + 2))
        = Fin.natAdd (Fin.vsum (fun _ : Fin M => 3)) ⟨0, by omega⟩ := by
      ext; simp
    rw [h0, Fin.vappend_eq_append, Fin.append_right]
    exact stirFinalVSpec_dir_zero
  unfold OracleReduction.perfectCompleteness
  have hb : (stirVectorTailReduction φ deg M).toReduction
      = (stirVectorBlocksReduction φ deg M).toReduction.append
          stirFinalVectorReductionMid.toReduction :=
    appendToReductionResidual_proof (stirVectorBlocksReduction φ deg M)
      stirFinalVectorReductionMid
  rw [hb]
  have hk := Reduction.append_perfectCompleteness_msg_proof
    (stirVectorBlocksReduction φ deg M).toReduction stirFinalVectorReductionMid.toReduction
    (stirVectorBlocksReduction_perfectCompleteness init impl φ deg M δ hInit hImplSupp)
    (stirFinalVectorReductionMid_perfectCompleteness init impl φ deg δ hInit)
    (Nat.zero_lt_two) hDirSeam stirFinalVSpec_dir_zero hInit hImplSupp
  exact hk

/-! ### Seam B: the firstBlock∘tail head (the `OStmt → VOStmt` packing seam) -/

/-- **The firstBlock∘(blocks∘finalMid) head-tail of the vectorised STIR chain** as a named
object (everything after the init block: the function-shaped input oracle is packed by the
first 3-slot block, then threaded packed). -/
noncomputable def stirVectorHeadReduction (φ : ι ↪ F) (deg : ℕ) (M : ℕ) :
    OracleReduction []ₒ F (OStmt ι F) Unit (F × F) (VOStmt ι F) Unit
      (((stirRound3VSpec ι F).toProtocolSpec F) ++ₚ
        ((ProtocolSpec.seqCompose (fun _ : Fin M => (stirRound3VSpec ι F).toProtocolSpec F))
          ++ₚ ((stirFinalVSpec ι F).toProtocolSpec F))) :=
  OracleReduction.append (stirRound3VectorReduction φ deg) (stirVectorTailReduction φ deg M)

open scoped Classical in
set_option maxHeartbeats 2000000 in
/-- **Perfect completeness of the firstBlock∘tail head** of the vectorised STIR chain: the
packing seam — input relation at the function payload (`stirOStmtRel F`), output relation at
the vector payload (`stirVOStmtRel (F × F)`). The seam-direction fact case-splits on `M`
(first mid block for `M > 0`, the final block for `M = 0`), per the `ChainCompleteness`
recipe. -/
theorem stirVectorHeadReduction_perfectCompleteness (φ : ι ↪ F) (deg : ℕ) (M : ℕ) (δ : ℝ≥0)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery []ₒ β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp []ₒ β)) :
    (stirVectorHeadReduction φ deg M).perfectCompleteness init impl
      (stirOStmtRel F φ deg δ) (stirVOStmtRel (F × F) φ deg δ) := by
  haveI : (([]ₒ : OracleSpec PEmpty)).Inhabited := { inhabited_B := fun i => nomatch i }
  haveI : (([]ₒ : OracleSpec PEmpty)).Fintype := { fintype_B := fun i => nomatch i }
  -- per-index challenge instances for the tail spec
  haveI hTF : ∀ j, Fintype (((ProtocolSpec.seqCompose
      (fun _ : Fin M => (stirRound3VSpec ι F).toProtocolSpec F))
      ++ₚ ((stirFinalVSpec ι F).toProtocolSpec F)).Challenge j) := appendChallenge_fintype _ _
  haveI hTI : ∀ j, Inhabited (((ProtocolSpec.seqCompose
      (fun _ : Fin M => (stirRound3VSpec ι F).toProtocolSpec F))
      ++ₚ ((stirFinalVSpec ι F).toProtocolSpec F)).Challenge j) := appendChallenge_inhabited _ _
  -- combined-oracle seam instances for the middle append keystone
  haveI := ProtocolSpec.appendCombinedOracle_fintype []ₒ
    ((stirRound3VSpec ι F).toProtocolSpec F)
    ((ProtocolSpec.seqCompose (fun _ : Fin M => (stirRound3VSpec ι F).toProtocolSpec F))
      ++ₚ ((stirFinalVSpec ι F).toProtocolSpec F))
  haveI := ProtocolSpec.appendCombinedOracle_inhabited []ₒ
    ((stirRound3VSpec ι F).toProtocolSpec F)
    ((ProtocolSpec.seqCompose (fun _ : Fin M => (stirRound3VSpec ι F).toProtocolSpec F))
      ++ₚ ((stirFinalVSpec ι F).toProtocolSpec F))
  haveI : ([]ₒ + [((ProtocolSpec.seqCompose
      (fun _ : Fin M => (stirRound3VSpec ι F).toProtocolSpec F))
      ++ₚ ((stirFinalVSpec ι F).toProtocolSpec F)).Challenge]ₒ).Fintype := by
    haveI := challengeOracle_fintype ((ProtocolSpec.seqCompose
      (fun _ : Fin M => (stirRound3VSpec ι F).toProtocolSpec F))
      ++ₚ ((stirFinalVSpec ι F).toProtocolSpec F))
    infer_instance
  haveI : ([]ₒ + [((ProtocolSpec.seqCompose
      (fun _ : Fin M => (stirRound3VSpec ι F).toProtocolSpec F))
      ++ₚ ((stirFinalVSpec ι F).toProtocolSpec F)).Challenge]ₒ).Inhabited := by
    haveI := challengeOracle_inhabited ((ProtocolSpec.seqCompose
      (fun _ : Fin M => (stirRound3VSpec ι F).toProtocolSpec F))
      ++ₚ ((stirFinalVSpec ι F).toProtocolSpec F))
    infer_instance
  -- the tail's leading slot is a prover message (case split on M: first mid block for
  -- M > 0, the final block for M = 0)
  have happ_dir : ∀ {k₁ k₂ : ℕ} (p₁ : ProtocolSpec k₁) (p₂ : ProtocolSpec k₂),
      (p₁ ++ₚ p₂).dir = Fin.vappend p₁.dir p₂.dir := fun _ _ => rfl
  have hDirTail0 : ∀ h0, ((ProtocolSpec.seqCompose
      (fun _ : Fin M => (stirRound3VSpec ι F).toProtocolSpec F))
      ++ₚ ((stirFinalVSpec ι F).toProtocolSpec F)).dir ⟨0, h0⟩ = .P_to_V := by
    intro h0
    rw [happ_dir]
    rcases M with _ | M'
    · have h0' : (⟨0, h0⟩ : Fin ((Fin.vsum fun _ : Fin 0 => 3) + 2))
          = Fin.natAdd (Fin.vsum (fun _ : Fin 0 => 3)) ⟨0, by omega⟩ := by
        ext
        show 0 = Fin.vsum (fun _ : Fin 0 => 3) + 0
        simp [Fin.vsum]
      rw [h0', Fin.vappend_eq_append, Fin.append_right]
      exact stirFinalVSpec_dir_zero
    · have h0' : (⟨0, h0⟩ : Fin ((Fin.vsum fun _ : Fin (M' + 1) => 3) + 2))
          = Fin.castAdd 2 (Fin.embedSum (⟨0, Nat.succ_pos M'⟩ : Fin (M' + 1))
              (⟨0, by omega⟩ : Fin 3)) := by
        ext
        simp [Fin.embedSum]
      rw [h0', Fin.vappend_eq_append, Fin.append_left, ProtocolSpec.seqCompose_dir,
        Fin.vflatten_embedSum]
      exact stirRound3VSpec_dir_zero
  -- the seam slot of the head spec (index 3 = the tail's slot 0)
  have hDirSeam : (((stirRound3VSpec ι F).toProtocolSpec F) ++ₚ
      ((ProtocolSpec.seqCompose (fun _ : Fin M => (stirRound3VSpec ι F).toProtocolSpec F))
        ++ₚ ((stirFinalVSpec ι F).toProtocolSpec F))).dir
      (⟨3, by omega⟩ : Fin (3 + ((Fin.vsum fun _ : Fin M => 3) + 2))) = .P_to_V := by
    rw [happ_dir]
    have h3 : (⟨3, by omega⟩ : Fin (3 + ((Fin.vsum fun _ : Fin M => 3) + 2)))
        = Fin.natAdd 3 ⟨0, by omega⟩ := by
      ext; simp
    rw [h3, Fin.vappend_eq_append, Fin.append_right]
    exact hDirTail0 _
  -- step down to the Reduction level
  unfold OracleReduction.perfectCompleteness
  have hb : (stirVectorHeadReduction φ deg M).toReduction
      = (stirRound3VectorReduction φ deg).toReduction.append
          (stirVectorTailReduction φ deg M).toReduction :=
    appendToReductionResidual_proof (stirRound3VectorReduction φ deg)
      (stirVectorTailReduction φ deg M)
  rw [hb]
  have h1 := stirRound3VectorReduction_perfectCompleteness init impl φ deg δ hInit
  unfold OracleReduction.perfectCompleteness at h1
  have h2 := stirVectorTailReduction_perfectCompleteness init impl φ deg M δ hInit hImplSupp
  unfold OracleReduction.perfectCompleteness at h2
  have hk := Reduction.append_perfectCompleteness_msg_proof
    (stirRound3VectorReduction φ deg).toReduction (stirVectorTailReduction φ deg M).toReduction
    h1 h2 (by omega) hDirSeam (hDirTail0 _) hInit hImplSupp
  exact hk

/-! ### Seam C: the full vectorised chain -/

open scoped Classical in
set_option maxHeartbeats 2000000 in
/-- **FULL vectorised chain perfect completeness (#301)**: `stirFullVectorReduction` — the
complete vectorised STIR protocol chain `[C_fold] ++ (g, C_out, C_shift)×(M+1) ++ [p, C_fin]`
at the literal `2(M+1)+2`-challenge wire-format shape — is perfectly complete from the chain
input relation (function-payload oracle `δ`-close) to the vector output relation (the
UNPACKED final oracle `δ`-close). -/
theorem stirFullVectorReduction_perfectCompleteness (φ : ι ↪ F) (deg : ℕ) (M : ℕ) (δ : ℝ≥0)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery []ₒ β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp []ₒ β)) :
    (stirFullVectorReduction φ deg M).perfectCompleteness init impl
      (stirOStmtRel Unit φ deg δ) (stirVOStmtRel (F × F) φ deg δ) := by
  haveI : (([]ₒ : OracleSpec PEmpty)).Inhabited := { inhabited_B := fun i => nomatch i }
  haveI : (([]ₒ : OracleSpec PEmpty)).Fintype := { fintype_B := fun i => nomatch i }
  -- per-index challenge instances for the tail and head++tail specs
  haveI hTF : ∀ j, Fintype (((ProtocolSpec.seqCompose
      (fun _ : Fin M => (stirRound3VSpec ι F).toProtocolSpec F))
      ++ₚ ((stirFinalVSpec ι F).toProtocolSpec F)).Challenge j) := appendChallenge_fintype _ _
  haveI hTI : ∀ j, Inhabited (((ProtocolSpec.seqCompose
      (fun _ : Fin M => (stirRound3VSpec ι F).toProtocolSpec F))
      ++ₚ ((stirFinalVSpec ι F).toProtocolSpec F)).Challenge j) := appendChallenge_inhabited _ _
  haveI hHF : ∀ j, Fintype ((((stirRound3VSpec ι F).toProtocolSpec F) ++ₚ
      ((ProtocolSpec.seqCompose (fun _ : Fin M => (stirRound3VSpec ι F).toProtocolSpec F))
        ++ₚ ((stirFinalVSpec ι F).toProtocolSpec F))).Challenge j) := appendChallenge_fintype _ _
  haveI hHI : ∀ j, Inhabited ((((stirRound3VSpec ι F).toProtocolSpec F) ++ₚ
      ((ProtocolSpec.seqCompose (fun _ : Fin M => (stirRound3VSpec ι F).toProtocolSpec F))
        ++ₚ ((stirFinalVSpec ι F).toProtocolSpec F))).Challenge j) := appendChallenge_inhabited _ _
  -- combined-oracle seam instances for the outer append keystone
  haveI := ProtocolSpec.appendCombinedOracle_fintype []ₒ (stirInitVSpec.toProtocolSpec F)
    (((stirRound3VSpec ι F).toProtocolSpec F) ++ₚ
      ((ProtocolSpec.seqCompose (fun _ : Fin M => (stirRound3VSpec ι F).toProtocolSpec F))
        ++ₚ ((stirFinalVSpec ι F).toProtocolSpec F)))
  haveI := ProtocolSpec.appendCombinedOracle_inhabited []ₒ (stirInitVSpec.toProtocolSpec F)
    (((stirRound3VSpec ι F).toProtocolSpec F) ++ₚ
      ((ProtocolSpec.seqCompose (fun _ : Fin M => (stirRound3VSpec ι F).toProtocolSpec F))
        ++ₚ ((stirFinalVSpec ι F).toProtocolSpec F)))
  haveI : ([]ₒ + [((((stirRound3VSpec ι F).toProtocolSpec F) ++ₚ
      ((ProtocolSpec.seqCompose (fun _ : Fin M => (stirRound3VSpec ι F).toProtocolSpec F))
        ++ₚ ((stirFinalVSpec ι F).toProtocolSpec F)))).Challenge]ₒ).Fintype := by
    haveI := challengeOracle_fintype (((stirRound3VSpec ι F).toProtocolSpec F) ++ₚ
      ((ProtocolSpec.seqCompose (fun _ : Fin M => (stirRound3VSpec ι F).toProtocolSpec F))
        ++ₚ ((stirFinalVSpec ι F).toProtocolSpec F)))
    infer_instance
  haveI : ([]ₒ + [((((stirRound3VSpec ι F).toProtocolSpec F) ++ₚ
      ((ProtocolSpec.seqCompose (fun _ : Fin M => (stirRound3VSpec ι F).toProtocolSpec F))
        ++ₚ ((stirFinalVSpec ι F).toProtocolSpec F)))).Challenge]ₒ).Inhabited := by
    haveI := challengeOracle_inhabited (((stirRound3VSpec ι F).toProtocolSpec F) ++ₚ
      ((ProtocolSpec.seqCompose (fun _ : Fin M => (stirRound3VSpec ι F).toProtocolSpec F))
        ++ₚ ((stirFinalVSpec ι F).toProtocolSpec F)))
    infer_instance
  -- the head++tail's leading slot is the first 3-slot block's message (no case split)
  have happ_dir : ∀ {k₁ k₂ : ℕ} (p₁ : ProtocolSpec k₁) (p₂ : ProtocolSpec k₂),
      (p₁ ++ₚ p₂).dir = Fin.vappend p₁.dir p₂.dir := fun _ _ => rfl
  have hDirHead0 : ∀ h0, ((((stirRound3VSpec ι F).toProtocolSpec F) ++ₚ
      ((ProtocolSpec.seqCompose (fun _ : Fin M => (stirRound3VSpec ι F).toProtocolSpec F))
        ++ₚ ((stirFinalVSpec ι F).toProtocolSpec F)))).dir ⟨0, h0⟩ = .P_to_V := by
    intro h0
    rw [happ_dir]
    have h0' : (⟨0, h0⟩ : Fin (3 + ((Fin.vsum fun _ : Fin M => 3) + 2)))
        = Fin.castAdd ((Fin.vsum fun _ : Fin M => 3) + 2) (⟨0, by omega⟩ : Fin 3) := by
      ext; simp
    rw [h0', Fin.vappend_eq_append, Fin.append_left]
    exact stirRound3VSpec_dir_zero
  -- the seam slot of the full spec (index 1 = the head++tail's slot 0)
  have hDirSeam : ((stirInitVSpec.toProtocolSpec F) ++ₚ
      (((stirRound3VSpec ι F).toProtocolSpec F) ++ₚ
        ((ProtocolSpec.seqCompose (fun _ : Fin M => (stirRound3VSpec ι F).toProtocolSpec F))
          ++ₚ ((stirFinalVSpec ι F).toProtocolSpec F)))).dir
      (⟨1, by omega⟩ : Fin (1 + (3 + ((Fin.vsum fun _ : Fin M => 3) + 2)))) = .P_to_V := by
    rw [happ_dir]
    have h1 : (⟨1, by omega⟩ : Fin (1 + (3 + ((Fin.vsum fun _ : Fin M => 3) + 2))))
        = Fin.natAdd 1 ⟨0, by omega⟩ := by
      ext; simp
    rw [h1, Fin.vappend_eq_append, Fin.append_right]
    exact hDirHead0 _
  -- step down to the Reduction level
  unfold OracleReduction.perfectCompleteness
  have hb : (stirFullVectorReduction φ deg M).toReduction
      = stirInitVectorReduction.toReduction.append
          ((stirRound3VectorReduction φ deg).append
            ((stirVectorBlocksReduction φ deg M).append
              stirFinalVectorReductionMid)).toReduction :=
    appendToReductionResidual_proof stirInitVectorReduction
      ((stirRound3VectorReduction φ deg).append
        ((stirVectorBlocksReduction φ deg M).append stirFinalVectorReductionMid))
  rw [hb]
  -- component facts at the Reduction level
  have h1 := stirInitVectorReduction_perfectCompleteness (ι := ι) (F := F) init impl φ deg δ
    hInit
  unfold OracleReduction.perfectCompleteness at h1
  have h2 := stirVectorHeadReduction_perfectCompleteness init impl φ deg M δ hInit hImplSupp
  unfold stirVectorHeadReduction stirVectorTailReduction
    OracleReduction.perfectCompleteness at h2
  have hk := Reduction.append_perfectCompleteness_msg_proof
    stirInitVectorReduction.toReduction
    ((stirRound3VectorReduction φ deg).append
      ((stirVectorBlocksReduction φ deg M).append stirFinalVectorReductionMid)).toReduction
    h1 h2 (by omega) hDirSeam (hDirHead0 _) hInit hImplSupp
  exact hk

end Round3

end StirIOP

#print axioms StirIOP.Round3.stirVOStmtRel
#print axioms StirIOP.Round3.stirInitVectorReduction_perfectCompleteness
#print axioms StirIOP.Round3.stirRound3VectorReduction_perfectCompleteness
#print axioms StirIOP.Round3.stirRound3VectorReductionMid_perfectCompleteness
#print axioms StirIOP.Round3.stirFinalVectorReductionMid_perfectCompleteness
#print axioms StirIOP.Round3.stirVectorBlocksReduction_perfectCompleteness
#print axioms StirIOP.Round3.stirVectorTailReduction
#print axioms StirIOP.Round3.stirVectorTailReduction_perfectCompleteness
#print axioms StirIOP.Round3.stirVectorHeadReduction
#print axioms StirIOP.Round3.stirVectorHeadReduction_perfectCompleteness
#print axioms StirIOP.Round3.stirFullVectorReduction_perfectCompleteness
