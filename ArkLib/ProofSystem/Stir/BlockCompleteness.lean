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

/-- Finiteness of the init-block challenge oracle spec (single index `0`, type `F`). -/
instance : [(pSpecInit F).Challenge]ₒ.Fintype where
  fintype_B
  | ⟨⟨iv, hiv⟩, _⟩ => by
    have h0 : iv = 0 := by omega
    subst h0
    simpa [pSpecInit, challengeOracleInterface, ProtocolSpec.Challenge, ProtocolSpec.«Type»,
      OracleInterface.Response, OracleInterface.toOC] using (inferInstance : Fintype F)

/-- Inhabitedness of the init-block challenge oracle spec. -/
instance : [(pSpecInit F).Challenge]ₒ.Inhabited where
  inhabited_B
  | ⟨⟨iv, hiv⟩, _⟩ => by
    have h0 : iv = 0 := by omega
    subst h0
    simpa [pSpecInit, challengeOracleInterface, ProtocolSpec.Challenge, ProtocolSpec.«Type»,
      OracleInterface.Response, OracleInterface.toOC] using (⟨(0 : F)⟩ : Inhabited F)

/-- Finiteness of the final-block challenge oracle spec (only index `1`, type `F`). -/
instance : [(pSpecFinal ι F).Challenge]ₒ.Fintype where
  fintype_B
  | ⟨⟨iv, hiv⟩, _⟩ => by
    have h1 : iv = 1 := by
      cases iv using Fin.cases with
      | zero => simp [pSpecFinal] at hiv
      | succ i1 => cases i1 using Fin.cases with
        | zero => rfl
        | succ k => exact k.elim0
    subst h1
    simpa [pSpecFinal, challengeOracleInterface, ProtocolSpec.Challenge, ProtocolSpec.«Type»,
      OracleInterface.Response, OracleInterface.toOC] using (inferInstance : Fintype F)

/-- Inhabitedness of the final-block challenge oracle spec. -/
instance : [(pSpecFinal ι F).Challenge]ₒ.Inhabited where
  inhabited_B
  | ⟨⟨iv, hiv⟩, _⟩ => by
    have h1 : iv = 1 := by
      cases iv using Fin.cases with
      | zero => simp [pSpecFinal] at hiv
      | succ i1 => cases i1 using Fin.cases with
        | zero => rfl
        | succ k => exact k.elim0
    subst h1
    simpa [pSpecFinal, challengeOracleInterface, ProtocolSpec.Challenge, ProtocolSpec.«Type»,
      OracleInterface.Response, OracleInterface.toOC] using (⟨(0 : F)⟩ : Inhabited F)

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

end Round3

end StirIOP

#print axioms StirIOP.Round3.stirInitReduction_perfectCompleteness
#print axioms StirIOP.Round3.stirFinalReduction_perfectCompleteness
