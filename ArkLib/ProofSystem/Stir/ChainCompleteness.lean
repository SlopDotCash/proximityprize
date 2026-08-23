/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Stir.TailCompleteness

/-!
# FULL chain perfect completeness of the STIR protocol object (#301)

The outer (init) seam composed onto the proven tail completeness: `stirFullReduction` — the
complete STIR chain `[C_fold] ++ (g, C_out, C_shift)×M ++ [p, C_fin]` at the literal
`2M+2`-challenge `stir_rbr_soundness` shape — is perfectly complete end-to-end. -/

namespace StirIOP

namespace Round3

open OracleSpec OracleComp ProtocolSpec STIR ReedSolomon NNReal StirIOP.Round OracleReduction

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Compound-head registration (thin-alias form): challenge sampleability of the full chain
spec `[C_fold] ++ ((blocks) ++ [p, C_fin])`. -/
@[reducible] instance instStirFullChalSampleable (M : ℕ) :
    ∀ i, SampleableType ((pSpecInit F ++ₚ
      ((ProtocolSpec.seqCompose (fun _ : Fin M => pSpec3 ι F))
        ++ₚ pSpecFinal ι F)).Challenge i) :=
  fun i => instSampleableTypeChallengeAppend i

variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))

open scoped Classical in
set_option maxHeartbeats 2000000 in
/-- **FULL chain perfect completeness (#301)**: `stirFullReduction` — the complete STIR
protocol chain `[C_fold] ++ (g, C_out, C_shift)×M ++ [p, C_fin]` at the literal `2M+2`-challenge
shape — is perfectly complete from the chain input relation to the chain output relation. -/
theorem stirFullReduction_perfectCompleteness (φ : ι ↪ F) (deg : ℕ) (M : ℕ) (δ : ℝ≥0)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery []ₒ β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp []ₒ β)) :
    (stirFullReduction φ deg M).perfectCompleteness init impl
      (stirOStmtRel Unit φ deg δ) (stirOStmtRel (F × F) φ deg δ) := by
  haveI : (([]ₒ : OracleSpec PEmpty)).Inhabited := { inhabited_B := fun i => nomatch i }
  haveI : (([]ₒ : OracleSpec PEmpty)).Fintype := { fintype_B := fun i => nomatch i }
  -- per-index challenge instances for the tail spec
  haveI hTF : ∀ j, Fintype (((ProtocolSpec.seqCompose (fun _ : Fin M => pSpec3 ι F))
      ++ₚ pSpecFinal ι F).Challenge j) := appendChallenge_fintype _ _
  haveI hTI : ∀ j, Inhabited (((ProtocolSpec.seqCompose (fun _ : Fin M => pSpec3 ι F))
      ++ₚ pSpecFinal ι F).Challenge j) := appendChallenge_inhabited _ _
  -- combined-oracle seam instances for the outer append keystone
  haveI := ProtocolSpec.appendCombinedOracle_fintype []ₒ (pSpecInit F)
    ((ProtocolSpec.seqCompose (fun _ : Fin M => pSpec3 ι F)) ++ₚ pSpecFinal ι F)
  haveI := ProtocolSpec.appendCombinedOracle_inhabited []ₒ (pSpecInit F)
    ((ProtocolSpec.seqCompose (fun _ : Fin M => pSpec3 ι F)) ++ₚ pSpecFinal ι F)
  haveI : ([]ₒ + [(pSpecInit F).Challenge]ₒ).Fintype := by
    haveI := challengeOracle_fintype (pSpecInit F); infer_instance
  haveI : ([]ₒ + [(pSpecInit F).Challenge]ₒ).Inhabited := by
    haveI := challengeOracle_inhabited (pSpecInit F); infer_instance
  haveI : ([]ₒ + [((ProtocolSpec.seqCompose (fun _ : Fin M => pSpec3 ι F))
      ++ₚ pSpecFinal ι F).Challenge]ₒ).Fintype := by
    haveI := challengeOracle_fintype ((ProtocolSpec.seqCompose
      (fun _ : Fin M => pSpec3 ι F)) ++ₚ pSpecFinal ι F)
    infer_instance
  haveI : ([]ₒ + [((ProtocolSpec.seqCompose (fun _ : Fin M => pSpec3 ι F))
      ++ₚ pSpecFinal ι F).Challenge]ₒ).Inhabited := by
    haveI := challengeOracle_inhabited ((ProtocolSpec.seqCompose
      (fun _ : Fin M => pSpec3 ι F)) ++ₚ pSpecFinal ι F)
    infer_instance
  -- the tail's leading slot is a prover message (case split on M: first 3-slot block for
  -- M > 0, the final block for M = 0)
  have happ_dir : ∀ {k₁ k₂ : ℕ} (p₁ : ProtocolSpec k₁) (p₂ : ProtocolSpec k₂),
      (p₁ ++ₚ p₂).dir = Fin.vappend p₁.dir p₂.dir := fun _ _ => rfl
  have hDirTail0 : ∀ h0, ((ProtocolSpec.seqCompose (fun _ : Fin M => pSpec3 ι F))
      ++ₚ pSpecFinal ι F).dir ⟨0, h0⟩ = .P_to_V := by
    intro h0
    rw [happ_dir]
    rcases M with _ | M'
    · have h0' : (⟨0, h0⟩ : Fin ((Fin.vsum fun _ : Fin 0 => 3) + 2))
          = Fin.natAdd (Fin.vsum (fun _ : Fin 0 => 3)) ⟨0, by omega⟩ := by
        ext
        show 0 = Fin.vsum (fun _ : Fin 0 => 3) + 0
        simp [Fin.vsum]
      rw [h0', Fin.vappend_eq_append, Fin.append_right]
      exact pSpecFinal_dir_zero
    · have h0' : (⟨0, h0⟩ : Fin ((Fin.vsum fun _ : Fin (M' + 1) => 3) + 2))
          = Fin.castAdd 2 (Fin.embedSum (⟨0, Nat.succ_pos M'⟩ : Fin (M' + 1))
              (⟨0, by omega⟩ : Fin 3)) := by
        ext
        simp [Fin.embedSum]
      rw [h0', Fin.vappend_eq_append, Fin.append_left, ProtocolSpec.seqCompose_dir,
        Fin.vflatten_embedSum]
      exact pSpec3_dir_zero
  -- the seam slot of the full spec (index 1 = the tail's slot 0)
  have hDirSeam : ((pSpecInit F) ++ₚ ((ProtocolSpec.seqCompose (fun _ : Fin M => pSpec3 ι F))
      ++ₚ pSpecFinal ι F)).dir (⟨1, by omega⟩ : Fin (1 + ((Fin.vsum fun _ : Fin M => 3) + 2)))
      = .P_to_V := by
    rw [happ_dir]
    have h1 : (⟨1, by omega⟩ : Fin (1 + ((Fin.vsum fun _ : Fin M => 3) + 2)))
        = Fin.natAdd 1 ⟨0, by omega⟩ := by
      ext; simp
    rw [h1, Fin.vappend_eq_append, Fin.append_right]
    exact hDirTail0 _
  -- step down to the Reduction level
  unfold OracleReduction.perfectCompleteness
  have hb : (stirFullReduction φ deg M).toReduction
      = stirInitReduction.toReduction.append
          ((stirBlocksReduction φ deg M).append stirFinalReduction).toReduction := by
    show (stirInitReduction.append
        ((stirBlocksReduction φ deg M).append stirFinalReduction)).toReduction = _
    exact appendToReductionResidual_proof stirInitReduction
      ((stirBlocksReduction φ deg M).append stirFinalReduction)
  rw [hb]
  -- component facts at the Reduction level
  have h1 := stirInitReduction_perfectCompleteness (ι := ι) (F := F) init impl φ deg δ hInit
  unfold OracleReduction.perfectCompleteness at h1
  have h2 := stirTailReduction_perfectCompleteness init impl φ deg M δ hInit hImplSupp
  unfold stirTailReduction OracleReduction.perfectCompleteness at h2
  have hk := Reduction.append_perfectCompleteness_msg_proof
    stirInitReduction.toReduction
    ((stirBlocksReduction φ deg M).append stirFinalReduction).toReduction
    h1 h2 (by omega) hDirSeam (hDirTail0 _) hInit hImplSupp
  exact hk

end Round3

end StirIOP

#print axioms StirIOP.Round3.stirFullReduction_perfectCompleteness
