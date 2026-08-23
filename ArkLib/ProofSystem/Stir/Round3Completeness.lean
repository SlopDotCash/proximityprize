/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Stir.BlockCompleteness
import ArkLib.ProofSystem.Stir.RoundCompleteness

/-!
# Issue #301 — `[P,V,V]` 3-message unroll + perfect completeness of the 3-slot STIR block

* `ProtocolSpec.FullTranscript.mk3` — the 3-slot transcript constructor (mirrors `mk2`).
* `unroll_3_message_reduction_perfectCompleteness_PVV` — the generic `[P_to_V, V_to_P, V_to_P]`
  3-message unroll lemma, specialised from the in-tree
  `OracleReduction.unroll_n_message_reduction_perfectCompleteness`.
* `stirRound3Reduction'_perfectCompleteness` — perfect completeness of the uniform-threading
  3-slot STIR block (`FullChain.lean`), input/output relation `stirOStmtRel F φ deg δ`;
  the relation transfer is `combine_single_self`.
* `stirRound3Reduction_perfectCompleteness` — the same for the `(F × F)`-output variant
  (`Round3Block.lean`), output relation `stirOStmtRel (F × F) φ deg δ`.
-/

open OracleSpec OracleComp ProtocolSpec STIR ReedSolomon NNReal OracleReduction

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace ProtocolSpec

/-- The 3-slot full transcript constructor (mirrors `FullTranscript.mk2`). -/
@[inline, reducible]
def FullTranscript.mk3 {pSpec : ProtocolSpec 3} (msg0 : pSpec.«Type» 0) (msg1 : pSpec.«Type» 1)
    (msg2 : pSpec.«Type» 2) : FullTranscript pSpec :=
  fun | ⟨0, _⟩ => msg0 | ⟨1, _⟩ => msg1 | ⟨2, _⟩ => msg2

end ProtocolSpec

namespace StirIOP.Round3

/-! ### `[P_to_V, V_to_P, V_to_P]` 3-message unroll lemma -/

section Unroll3PVV

variable {ιₒ : Type} {oSpec : OracleSpec ιₒ} [oSpec.Fintype] [oSpec.Inhabited]
  {StmtIn WitIn StmtOut WitOut : Type}
  {ιₛᵢ ιₛₒ : Type} {OStmtIn : ιₛᵢ → Type} {OStmtOut : ιₛₒ → Type}
  [∀ i, OracleInterface (OStmtIn i)]
  {pSpecG : ProtocolSpec 3} [∀ i, SampleableType (pSpecG.Challenge i)]
  [[pSpecG.Challenge]ₒ.Fintype] [[pSpecG.Challenge]ₒ.Inhabited]
  [∀ i, OracleInterface (pSpecG.Message i)]
  {σ : Type}

/-- **Derive the 3-message `[P_to_V, V_to_P, V_to_P]` version from the generic n-message
theorem**: the prover sends one message, then receives two verifier challenges. -/
theorem unroll_3_message_reduction_perfectCompleteness_PVV
    (reduction : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpecG)
    (relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn))
    (relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut))
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp)) (hInit : NeverFail init)
    (hDir0 : pSpecG.dir 0 = .P_to_V) (hDir1 : pSpecG.dir 1 = .V_to_P)
    (hDir2 : pSpecG.dir 2 = .V_to_P)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (OracleReduction.liftQuery q)) :
    OracleReduction.perfectCompleteness init impl relIn relOut reduction ↔
    ∀ (stmtIn : StmtIn) (oStmtIn : ∀ i, OStmtIn i) (witIn : WitIn),
      ((stmtIn, oStmtIn), witIn) ∈ relIn →
      Pr[fun ((prvStmt, prvOStmt), (verStmt, verOStmt), witOut) =>
          ((verStmt, verOStmt), witOut) ∈ relOut ∧ prvStmt = verStmt ∧ prvOStmt = verOStmt
        | ((do
          let ⟨msg0, state1⟩ ← liftComp
            (reduction.prover.sendMessage ⟨0, hDir0⟩
              (reduction.prover.input ((stmtIn, oStmtIn), witIn)))
            (oSpec + [pSpecG.Challenge]ₒ)
          let r1 ← liftComp (pSpecG.getChallenge ⟨1, hDir1⟩) (oSpec + [pSpecG.Challenge]ₒ)
          let receiveChallengeFn1 ← liftComp
            (reduction.prover.receiveChallenge ⟨1, hDir1⟩ state1)
            (oSpec + [pSpecG.Challenge]ₒ)
          let state2 := receiveChallengeFn1 r1
          let r2 ← liftComp (pSpecG.getChallenge ⟨2, hDir2⟩) (oSpec + [pSpecG.Challenge]ₒ)
          let receiveChallengeFn2 ← liftComp
            (reduction.prover.receiveChallenge ⟨2, hDir2⟩ state2)
            (oSpec + [pSpecG.Challenge]ₒ)
          let state3 := receiveChallengeFn2 r2
          let ⟨⟨prvStmtOut, prvOStmtOut⟩, witOut⟩ ← liftComp (reduction.prover.output state3)
            (oSpec + [pSpecG.Challenge]ₒ)
          let transcript := ProtocolSpec.FullTranscript.mk3 msg0 r1 r2
          let verifierStmtOut ← liftComp
            (reduction.verifier.toVerifier.verify (stmtIn, oStmtIn) transcript)
            (oSpec + [pSpecG.Challenge]ₒ)
          pure ((prvStmtOut, prvOStmtOut), verifierStmtOut, witOut)
        ) : OptionT (OracleComp (oSpec + [pSpecG.Challenge]ₒ))
            ((StmtOut × ((i : ιₛₒ) → OStmtOut i)) × (StmtOut × ((i : ιₛₒ) → OStmtOut i)) × WitOut))
      ] = 1 := by
  rw [OracleReduction.unroll_n_message_reduction_perfectCompleteness (n := 3)
    (reduction := reduction) relIn relOut init impl hInit hImplSupp]
  apply forall_congr'; intro stmtIn
  apply forall_congr'; intro oStmtIn
  apply forall_congr'; intro witIn
  apply imp_congr_right; intro h_relIn
  simp only [Prover.runToRound]
  have h_last_eq_three : (Fin.last 3) = 3 := by rfl
  rw! (castMode := .all) [h_last_eq_three]
  conv_lhs =>
    simp only [Fin.induction_three']
    rw [Prover.processRound_P_to_V (h := hDir0)]
    rw [Prover.processRound_V_to_P (h := hDir1)]
    rw [Prover.processRound_V_to_P (h := hDir2)]
    simp only
  dsimp
  simp only [Fin.isValue, bind_pure_comp, pure_bind, bind_map_left, liftM_bind, liftM_map,
    Prod.mk.eta, bind_assoc]
  congr!
  all_goals
    first
    | (funext i; fin_cases i <;> rfl)
    | (congr 1 <;> (try funext i) <;> (try fin_cases i) <;> rfl)
    | (congr 2 <;> (try funext i) <;> (try fin_cases i) <;> rfl)

end Unroll3PVV

/-! ### Bespoke challenge-oracle instances for `pSpec3` (indices 1 and 2 carry `F`;
index 0 is a prover message, hence impossible as a challenge index). -/

open StirIOP.Round

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

instance : ∀ j, SampleableType ((pSpec3 ι F).Challenge j)
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => (inferInstance : SampleableType F)
  | ⟨2, _⟩ => (inferInstance : SampleableType F)

/-- Finiteness of the 3-slot block challenge oracle spec (indices `1`, `2`, both of type `F`). -/
instance : [(pSpec3 ι F).Challenge]ₒ.Fintype where
  fintype_B
  | ⟨⟨0, _⟩, h⟩ => nomatch h
  | ⟨⟨1, _⟩, _⟩ => by
      simpa [pSpec3, challengeOracleInterface, ProtocolSpec.Challenge, ProtocolSpec.«Type»,
        OracleInterface.Response, OracleInterface.toOC] using (inferInstance : Fintype F)
  | ⟨⟨2, _⟩, _⟩ => by
      simpa [pSpec3, challengeOracleInterface, ProtocolSpec.Challenge, ProtocolSpec.«Type»,
        OracleInterface.Response, OracleInterface.toOC] using (inferInstance : Fintype F)

/-- Inhabitedness of the 3-slot block challenge oracle spec. -/
instance : [(pSpec3 ι F).Challenge]ₒ.Inhabited where
  inhabited_B
  | ⟨⟨0, _⟩, h⟩ => nomatch h
  | ⟨⟨1, _⟩, _⟩ => by
      simpa [pSpec3, challengeOracleInterface, ProtocolSpec.Challenge, ProtocolSpec.«Type»,
        OracleInterface.Response, OracleInterface.toOC] using (⟨(0 : F)⟩ : Inhabited F)
  | ⟨⟨2, _⟩, _⟩ => by
      simpa [pSpec3, challengeOracleInterface, ProtocolSpec.Challenge, ProtocolSpec.«Type»,
        OracleInterface.Response, OracleInterface.toOC] using (⟨(0 : F)⟩ : Inhabited F)

/-! ### Perfect completeness of the 3-slot STIR blocks -/

variable [Nonempty ι]
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))

open scoped Classical in
set_option maxHeartbeats 800000 in
/-- **Perfect completeness of the uniform-threading 3-slot STIR block**: the honest prover
combines its single codeword at its own degree, which by `combine_single_self` is the input
oracle itself; the verifier forwards it as the output oracle and outputs the shift challenge,
so agreement is definitional and the proximity relation transfers verbatim. -/
theorem stirRound3Reduction'_perfectCompleteness (φ : ι ↪ F) (deg : ℕ) (δ : ℝ≥0)
    (hInit : NeverFail init) :
    OracleReduction.perfectCompleteness init impl
      (stirOStmtRel F φ deg δ) (stirOStmtRel F φ deg δ)
      (stirRound3Reduction' φ deg) := by
  rw [unroll_3_message_reduction_perfectCompleteness_PVV (stirRound3Reduction' φ deg)
    (stirOStmtRel F φ deg δ) (stirOStmtRel F φ deg δ) init impl hInit
    (by rfl) (by rfl) (by rfl)
    (by simp only [Set.fmap_eq_image, IsEmpty.forall_iff, implies_true])]
  intro stmtIn oStmtIn witIn h_relIn
  dsimp only [stirRound3Reduction', stirRound3Prover', stirRound3Verifier',
    OracleVerifier.toVerifier, OStmt, stirOStmtRel]
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
    have hc : Combine.combine φ deg stmtIn (fun _ : Fin 1 => oStmtIn ()) (fun _ : Fin 1 => deg)
        = oStmtIn () := combine_single_self φ deg stmtIn (oStmtIn ())
    simpa [hc] using h_relIn

open scoped Classical in
set_option maxHeartbeats 800000 in
/-- **Perfect completeness of the `(F × F)`-output 3-slot STIR block** (`Round3Block.lean`):
identical honest behaviour, with the output statement being the `(rOut, rShift)` pair. -/
theorem stirRound3Reduction_perfectCompleteness (φ : ι ↪ F) (deg : ℕ) (δ : ℝ≥0)
    (hInit : NeverFail init) :
    OracleReduction.perfectCompleteness init impl
      (stirOStmtRel F φ deg δ) (stirOStmtRel (F × F) φ deg δ)
      (stirRound3Reduction φ deg) := by
  rw [unroll_3_message_reduction_perfectCompleteness_PVV (stirRound3Reduction φ deg)
    (stirOStmtRel F φ deg δ) (stirOStmtRel (F × F) φ deg δ) init impl hInit
    (by rfl) (by rfl) (by rfl)
    (by simp only [Set.fmap_eq_image, IsEmpty.forall_iff, implies_true])]
  intro stmtIn oStmtIn witIn h_relIn
  dsimp only [stirRound3Reduction, stirRound3Prover, stirRound3Verifier,
    OracleVerifier.toVerifier, OStmt, stirOStmtRel]
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
    have hc : Combine.combine φ deg stmtIn (fun _ : Fin 1 => oStmtIn ()) (fun _ : Fin 1 => deg)
        = oStmtIn () := combine_single_self φ deg stmtIn (oStmtIn ())
    simpa [hc] using h_relIn

end StirIOP.Round3

#print axioms StirIOP.Round3.unroll_3_message_reduction_perfectCompleteness_PVV
#print axioms StirIOP.Round3.stirRound3Reduction'_perfectCompleteness
#print axioms StirIOP.Round3.stirRound3Reduction_perfectCompleteness
