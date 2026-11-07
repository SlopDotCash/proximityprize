/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.Security.Implications
import ProximityPrize.Compatibility.AveragedRbr.Security.Execution
import ProximityPrize.Compatibility.AveragedRbr.Security.RoundByRound

/-!
# Historical prover-averaged round-by-round contracts

These declarations preserve downstream proofs of the prover-averaged game.
They come from ArkLib 1040ed0e6f208de9afd1a1aa56888ccd830c0964 before #1421.
-/

section

open OracleComp OracleSpec ProtocolSpec

open scoped NNReal ProbabilityTheory

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

namespace Verifier

section Implications

/-- Prover-averaged round-by-round knowledge soundness with error `rbrKnowledgeError` implies
prover-averaged round-by-round soundness with the same error `rbrKnowledgeError`. -/
theorem rbrKnowledgeSoundnessAveraged_implies_rbrSoundnessAveraged
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0}
    (h : verifier.rbrKnowledgeSoundnessAveraged init impl relIn relOut rbrKnowledgeError) :
    verifier.rbrSoundnessAveraged init impl relIn.language relOut.language rbrKnowledgeError := by
  classical
  unfold rbrKnowledgeSoundnessAveraged at h
  obtain ⟨WitMid, extractor, kSF, hkSF⟩ := h
  by_cases hWout : Nonempty WitOut
  · unfold rbrSoundnessAveraged
    refine ⟨kSF.toStateFunction init impl, ?_⟩
    intro stmtIn hStmtIn WitIn' WitOut' witIn' prover i
    by_cases hWin : Nonempty WitIn
    · let prover' : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec :=
        { PrvState := prover.PrvState
          input := fun _ => prover.input (stmtIn, witIn')
          sendMessage := prover.sendMessage
          receiveChallenge := prover.receiveChallenge
          output := fun st => do
            let out ← prover.output st
            return (out.1, Classical.choice hWout) }
      have hrun : prover'.runToRound i.1.castSucc stmtIn (Classical.choice hWin) =
          prover.runToRound i.1.castSucc stmtIn witIn' := by rfl
      have hrunlog : prover'.runWithLogToRound i.1.castSucc stmtIn (Classical.choice hWin) =
          prover.runWithLogToRound i.1.castSucc stmtIn witIn' := by
        unfold Prover.runWithLogToRound
        rw [hrun]
      let logGame := do
        let s ← init
        (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
          (do
            let ⟨⟨transcript, _⟩, proveQueryLog⟩ ←
              prover'.runWithLogToRound i.1.castSucc stmtIn (Classical.choice hWin)
            let challenge ← liftComp (pSpec.getChallenge i) _
            return (transcript, challenge, proveQueryLog))).run' s
      let plainGame := do
        let s ← init
        (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
          (do
            let ⟨transcript, _⟩ ← prover.runToRound i.1.castSucc stmtIn witIn'
            let challenge ← liftComp (pSpec.getChallenge i) _
            return (transcript, challenge))).run' s
      have hmap : (fun x => (x.1, x.2.1)) <$> logGame = plainGame := by
        simp [logGame, plainGame, ← Prover.runWithLogToRound_discard_log_eq_runToRound, hrunlog]
        rfl
      have hk := hkSF stmtIn (Classical.choice hWin) prover' i
      change Pr{let x ← plainGame}[
        ¬ (∃ w, kSF i.1.castSucc stmtIn x.1 w) ∧
          ∃ w, kSF i.1.succ stmtIn (x.1.concat x.2) w] ≤ _
      change Pr{let x ← logGame}[∃ w,
        ¬ kSF i.1.castSucc stmtIn x.1
            (extractor.extractMid i.1 stmtIn (x.1.concat x.2.1) w) ∧
          kSF i.1.succ stmtIn (x.1.concat x.2.1) w] ≤ _ at hk
      calc
        _ = Pr{let x ← logGame}[
            ¬ (∃ w, kSF i.1.castSucc stmtIn x.1 w) ∧
              ∃ w, kSF i.1.succ stmtIn (x.1.concat x.2.1) w] := by
              rw [← hmap, prEvent_map]
        _ ≤ Pr{let x ← logGame}[∃ w,
            ¬ kSF i.1.castSucc stmtIn x.1
                (extractor.extractMid i.1 stmtIn (x.1.concat x.2.1) w) ∧
              kSF i.1.succ stmtIn (x.1.concat x.2.1) w] := by
              apply prEvent_mono
              intro x hbad
              obtain ⟨hprev, w, hnext⟩ := hbad
              exact ⟨w, fun hw => hprev ⟨_, hw⟩, hnext⟩
        _ ≤ _ := hk
    · refine (prEvent_eq_zero_of_forall_not _ _ fun x hbad ↦ ?_).trans_le zero_le
      obtain ⟨-, w, hnext⟩ := hbad
      exact hWin ⟨extractor.foldPrefix stmtIn i.1.succ (x.1.concat x.2) w⟩
  · have hLangOut : relOut.language = ∅ := by
      ext stmtOut
      simp only [Set.language, Set.mem_image, Prod.exists, exists_and_right,
        exists_eq_right, Set.mem_empty_iff_false, iff_false]
      intro hex
      exact hWout ⟨hex.choose⟩
    let sF : verifier.StateFunction init impl relIn.language relOut.language :=
      { toFun := fun m stmtIn _ => m = 0 ∧ stmtIn ∈ relIn.language
        toFun_empty := by
          intro stmtIn
          exact fun h => h.2
        toFun_next := by
          intro m hdir stmtIn tr hfalse msg htrue
          exact Fin.succ_ne_zero m htrue.1
        toFun_full := by
          intro stmtIn tr hfalse
          rw [hLangOut]
          exact prEvent_eq_zero_of_forall_not _ _ fun _ ↦ by simp }
    unfold rbrSoundnessAveraged
    refine ⟨sF, ?_⟩
    intro stmtIn hStmtIn WitIn' WitOut' witIn' prover i
    exact (prEvent_eq_zero_of_forall_not _ _ fun _ hbad ↦
      Fin.succ_ne_zero i.1 hbad.2.1).trans_le zero_le

end Implications

end Verifier

/-! ## Coordinate-wise special soundness generalizes special soundness

Both `Verifier.specialSound` (`Security.SpecialSoundness`) and
`Verifier.coordinateWiseSpecialSound` (`Security.CoordinateWiseSpecialSoundness`) are *defined* as
instances of the shape-generic `Verifier.treeSpecialSound`, differing only in the challenge-tree
shape they fix:

* plain special soundness fixes `distinctShape k` — arity `kᵢ`, node predicate `Function.Injective`
  (the `kᵢ` sibling challenges are pairwise distinct);
* CWSS fixes `D.toShape` — arity `ℓᵢ·(kᵢ-1)+1`, node predicate `IsSpecialSoundFamily ℓᵢ kᵢ`.

For the canonical `ℓᵢ = 1` structure `CWSSStructure.ofSpecialSound k` the two shapes are *equal*
(`toShape_ofSpecialSound_eq_distinctShape`): the arity is `kᵢ` and `IsSpecialSoundFamily 1 kᵢ`
reduces to injectivity (`CoordinateWise.isSpecialSoundFamily_one_iff_injective`). The bridge
`Verifier.coordinateWiseSpecialSound_ofSpecialSound_iff` is then immediate from that shape
equality. -/
