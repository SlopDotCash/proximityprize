/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Stir.FullChain
import ArkLib.ProofSystem.Stir.RoundCompleteness

/-!
# Perfect completeness of the STIR chain boundary blocks (#301)

Perfect completeness of the boundary blocks of the full STIR chain
(`stirInitReduction`, `stirFinalReduction`), against the uniform statement-indexed
proximity relation. -/

namespace StirIOP

namespace Round3

open OracleSpec OracleComp ProtocolSpec STIR ReedSolomon NNReal StirIOP.Round

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- **The uniform statement-indexed proximity relation**: the oracle is `δ`-close to the
Reed-Solomon code, for any statement type `S` (the statement carries protocol randomness,
which the proximity relation ignores). Instantiates to the input/output relations of every
block of the full STIR chain: `S = Unit` (chain input), `S = F` (post-init / inter-block),
`S = F × F` (post-final). -/
noncomputable def stirOStmtRel (S : Type) (φ : ι ↪ F) (deg : ℕ) (δ : ℝ≥0) :
    Set ((S × ∀ i, OStmt ι F i) × Unit) :=
  fun ⟨⟨_, oracle⟩, _⟩ =>
    Code.relDistFromCode (oracle ()) (ReedSolomon.code φ deg) ≤ (δ : ENNReal)

private noncomputable local instance stirBlockUniformAnswers
    {κ : Type} {spec : OracleSpec κ}
    [∀ q, Fintype (spec.Range q)] [∀ q, Inhabited (spec.Range q)] :
    OracleSpec.UniformAnswerMeasure spec :=
  OracleSpec.UniformAnswerMeasure.ofFiniteNonempty spec

private noncomputable local instance stirBlockChallengeUniform {N : ℕ} (p : ProtocolSpec N)
    [∀ j, SampleableType (p.Challenge j)] :
    OracleSpec.UniformAnswerMeasure ([p.Challenge]ₒ'ProtocolSpec.challengeOracleInterface) := by
  letI : ∀ t, Finite (([p.Challenge]ₒ'ProtocolSpec.challengeOracleInterface).Range t)
    | ⟨j, ()⟩ => by change Finite (p.Challenge j); infer_instance
  letI : ∀ t, Nonempty (([p.Challenge]ₒ'ProtocolSpec.challengeOracleInterface).Range t)
    | ⟨j, ()⟩ => by change Nonempty (p.Challenge j); infer_instance
  exact OracleSpec.UniformAnswerMeasure.ofFiniteNonempty _

private theorem liftedOption {κ : Type} {spec : OracleSpec.{0, 0} κ} {β : Type}
    (mx : OracleComp spec β) :
    (liftM mx : OptionT (OracleComp spec) β) = some <$> mx := by
  change (mx >>= fun x => pure (some x)) = some <$> mx
  rw [map_eq_bind_pure_comp]
  rfl

instance : ∀ j, SampleableType ((pSpecInit F).Challenge j)
  | ⟨0, _⟩ => by
      show SampleableType ((pSpecInit F).«Type» 0)
      simp only [pSpecInit, Fin.vcons_zero]; infer_instance

instance : ∀ j, SampleableType ((pSpecFinal ι F).Challenge j)
  | ⟨0, hj⟩ => absurd hj (by rw [pSpecFinal_dir_zero]; decide)
  | ⟨1, _⟩ => (inferInstance : SampleableType F)

variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))

open scoped Classical in
set_option maxHeartbeats 800000 in
/-- **Perfect completeness of the initial `[C_fold]` block**: the prover stores the fold
challenge as the output statement and forwards its oracle unchanged, the verifier reads the
same challenge off the transcript, so agreement is definitional and the proximity relation
transfers verbatim. -/
theorem stirInitReduction_perfectCompleteness (φ : ι ↪ F) (deg : ℕ) (δ : ℝ≥0)
    (hInit : NeverFail init) :
    OracleReduction.perfectCompleteness init impl
      (stirOStmtRel Unit φ deg δ) (stirOStmtRel F φ deg δ)
      (stirInitReduction (ι := ι) (F := F)) := by
  rw [OracleReduction.unroll_1_message_reduction_perfectCompleteness_V_to_P
    (stirInitReduction (ι := ι) (F := F))
    (stirOStmtRel Unit φ deg δ) (stirOStmtRel F φ deg δ) init impl hInit (by rfl)
    (by simp only [Set.fmap_eq_image, IsEmpty.forall_iff, implies_true])]
  intro stmtIn oStmtIn witIn h_relIn
  dsimp only [stirInitReduction, stirInitProver, stirInitVerifier, OracleVerifier.toVerifier,
    OStmt, stirOStmtRel]
  simp only [Fin.isValue, bind_pure_comp, pure_bind, bind_map_left, liftM_bind, liftM_map,
    Prod.mk.eta, bind_assoc, map_pure, liftComp_pure, liftM_pure]
  apply (OptionT.prEvent_mk_eq_one_iff _ _).2
  intro value hvalue
  obtain ⟨α, hα, hvalue⟩ := OracleComp.mem_support_bind_peel _ _ hvalue
  erw [liftedOption] at hα
  obtain ⟨a, _, ha⟩ := OracleComp.mem_support_map_peel _ _ hα
  subst α
  simp only [OptionT.run_map, OptionT.run_monadLift, OptionT.run_pure,
    simulateQ_pure, _root_.map_pure, Option.map_some, liftComp_pure] at hvalue
  have hv := OracleComp.eq_of_mem_support_pure _ hvalue
  subst value
  refine ⟨_, rfl, ?_, rfl, by funext u; rfl⟩
  change Code.relDistFromCode (oStmtIn ()) (ReedSolomon.code φ deg) ≤ (δ : ENNReal) at h_relIn
  change Code.relDistFromCode _ (ReedSolomon.code φ deg : Set (ι → F)) ≤ (δ : ENNReal)
  simpa only [OracleVerifier.materializeOutput, OracleVerifier.materializeOutputOracle,
    FullTranscript.messages, FullTranscript.mk1, FullTranscript.mk2, DFunLike.coe, id_eq] using h_relIn

open scoped Classical in
set_option maxHeartbeats 800000 in
/-- **Perfect completeness of the final `[p, C_fin]` block**: the prover sends its oracle in
the clear and threads `(pending randomness, repetition challenge)` into the statement; the
verifier exposes the same message as the output oracle, so agreement is definitional and the
proximity relation transfers verbatim. -/
theorem stirFinalReduction_perfectCompleteness (φ : ι ↪ F) (deg : ℕ) (δ : ℝ≥0)
    (hInit : NeverFail init) :
    OracleReduction.perfectCompleteness init impl
      (stirOStmtRel F φ deg δ) (stirOStmtRel (F × F) φ deg δ)
      (stirFinalReduction (ι := ι) (F := F)) := by
  rw [OracleReduction.unroll_2_message_reduction_perfectCompleteness
    (stirFinalReduction (ι := ι) (F := F))
    (stirOStmtRel F φ deg δ) (stirOStmtRel (F × F) φ deg δ) init impl hInit
    (by rfl) (by rfl)
    (by simp only [Set.fmap_eq_image, IsEmpty.forall_iff, implies_true])]
  intro stmtIn oStmtIn witIn h_relIn
  dsimp only [stirFinalReduction, stirFinalProver, stirFinalVerifier, OracleVerifier.toVerifier,
    OStmt, stirOStmtRel]
  simp only [Fin.isValue, bind_pure_comp, pure_bind, bind_map_left, liftM_bind, liftM_map,
    Prod.mk.eta, bind_assoc, map_pure, liftComp_pure, liftM_pure]
  apply (OptionT.prEvent_mk_eq_one_iff _ _).2
  intro value hvalue
  obtain ⟨α, hα, hvalue⟩ := OracleComp.mem_support_bind_peel _ _ hvalue
  erw [liftedOption] at hα
  obtain ⟨a, _, ha⟩ := OracleComp.mem_support_map_peel _ _ hα
  subst α
  simp only [OptionT.run_map, OptionT.run_monadLift, OptionT.run_pure,
    simulateQ_pure, _root_.map_pure, Option.map_some, liftComp_pure] at hvalue
  have hv := OracleComp.eq_of_mem_support_pure _ hvalue
  subst value
  refine ⟨_, rfl, ?_, rfl, by funext u; rfl⟩
  change Code.relDistFromCode (oStmtIn ()) (ReedSolomon.code φ deg) ≤ (δ : ENNReal) at h_relIn
  change Code.relDistFromCode _ (ReedSolomon.code φ deg : Set (ι → F)) ≤ (δ : ENNReal)
  simpa only [OracleVerifier.materializeOutput, OracleVerifier.materializeOutputOracle,
    FullTranscript.messages, FullTranscript.mk1, FullTranscript.mk2, DFunLike.coe, id_eq] using h_relIn

end Round3

end StirIOP

#print axioms StirIOP.Round3.stirInitReduction_perfectCompleteness
#print axioms StirIOP.Round3.stirFinalReduction_perfectCompleteness
