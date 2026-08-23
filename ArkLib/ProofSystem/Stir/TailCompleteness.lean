/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Stir.BlocksCompleteness
import ArkLib.OracleReduction.Composition.Sequential.AppendPerfectCompletenessOracle
import ArkLib.OracleReduction.Composition.Sequential.AppendToVerifierKeystone
import ArkLib.OracleReduction.Composition.Sequential.ChallengeOracleFintype

/-!
# Chain-level perfect completeness: the tail seam (#301)

The blocks∘final tail of the STIR chain is perfectly complete — the first of the two binary
append seams composed onto the proven phase completeness. -/

namespace StirIOP

namespace Round3

open OracleSpec OracleComp ProtocolSpec STIR ReedSolomon NNReal StirIOP.Round OracleReduction

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))

/-- Per-challenge `Fintype` for the boundary specs. -/
instance : ∀ j, Fintype ((pSpecInit F).Challenge j)
  | ⟨0, _⟩ => (inferInstance : Fintype F)

instance : ∀ j, Inhabited ((pSpecInit F).Challenge j)
  | ⟨0, _⟩ => ⟨(0 : F)⟩

instance : ∀ j, Fintype ((pSpecFinal ι F).Challenge j)
  | ⟨0, h⟩ => absurd h (by rw [pSpecFinal_dir_zero]; decide)
  | ⟨1, _⟩ => (inferInstance : Fintype F)

instance : ∀ j, Inhabited ((pSpecFinal ι F).Challenge j)
  | ⟨0, h⟩ => absurd h (by rw [pSpecFinal_dir_zero]; decide)
  | ⟨1, _⟩ => ⟨(0 : F)⟩

set_option maxHeartbeats 4000000 in
/-- Compound-head registration (gotcha 6, thin-alias form): challenge sampleability of the
blocks++final tail, delegating to the generic append instance so downstream unification with
generic-head-elaborated facts is delta-trivial. -/
@[reducible] instance instStirBlocksFinalChalSampleable (M : ℕ) :
    ∀ i, SampleableType (((ProtocolSpec.seqCompose (fun _ : Fin M => pSpec3 ι F))
      ++ₚ pSpecFinal ι F).Challenge i) :=
  fun i => instSampleableTypeChallengeAppend i

/-- **The blocks∘final tail of the STIR chain** as a named object (the inner append of
`stirFullReduction`). -/
noncomputable def stirTailReduction (φ : ι ↪ F) (deg : ℕ) (M : ℕ) :
    OracleReduction []ₒ F (OStmt ι F) Unit (F × F) (OStmt ι F) Unit
      ((ProtocolSpec.seqCompose (fun _ : Fin M => pSpec3 ι F)) ++ₚ pSpecFinal ι F) :=
  OracleReduction.append (stirBlocksReduction φ deg M) stirFinalReduction

open scoped Classical in
set_option maxHeartbeats 2000000 in
/-- **Perfect completeness of the blocks∘final tail** of the STIR chain, via the
`Reduction`-level message-seam keystone (stepping down through `toReduction` by equation-lemma
unfolds — the oracle-level keystone's unification diverges on these concrete compound specs).
Combined-oracle seam instances supplied by the in-tree `ChallengeOracleFintype` helpers. -/
theorem stirTailReduction_perfectCompleteness (φ : ι ↪ F) (deg : ℕ) (M : ℕ) (δ : ℝ≥0)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery []ₒ β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp []ₒ β)) :
    (stirTailReduction φ deg M).perfectCompleteness init impl
      (stirOStmtRel F φ deg δ) (stirOStmtRel (F × F) φ deg δ) := by
  haveI : (([]ₒ : OracleSpec PEmpty)).Inhabited := { inhabited_B := fun i => nomatch i }
  haveI : (([]ₒ : OracleSpec PEmpty)).Fintype := { fintype_B := fun i => nomatch i }
  haveI := ProtocolSpec.appendCombinedOracle_fintype []ₒ
    (ProtocolSpec.seqCompose (fun _ : Fin M => pSpec3 ι F)) (pSpecFinal ι F)
  haveI := ProtocolSpec.appendCombinedOracle_inhabited []ₒ
    (ProtocolSpec.seqCompose (fun _ : Fin M => pSpec3 ι F)) (pSpecFinal ι F)
  haveI := ProtocolSpec.seqComposeCombinedOracle_fintype []ₒ (fun _ : Fin M => pSpec3 ι F)
  haveI := ProtocolSpec.seqComposeCombinedOracle_inhabited []ₒ (fun _ : Fin M => pSpec3 ι F)
  haveI : ([]ₒ + [(pSpecFinal ι F).Challenge]ₒ).Fintype := by
    haveI := challengeOracle_fintype (pSpecFinal ι F); infer_instance
  haveI : ([]ₒ + [(pSpecFinal ι F).Challenge]ₒ).Inhabited := by
    haveI := challengeOracle_inhabited (pSpecFinal ι F); infer_instance
  have hDirSeam : ((ProtocolSpec.seqCompose (fun _ : Fin M => pSpec3 ι F)) ++ₚ pSpecFinal ι F).dir
      (⟨Fin.vsum (fun _ : Fin M => 3), by omega⟩
        : Fin ((Fin.vsum (fun _ : Fin M => 3)) + 2)) = .P_to_V := by
    show (Fin.vappend (ProtocolSpec.seqCompose (fun _ : Fin M => pSpec3 ι F)).dir
        (pSpecFinal ι F).dir) _ = .P_to_V
    have h0 : (⟨Fin.vsum (fun _ : Fin M => 3), by omega⟩
          : Fin ((Fin.vsum (fun _ : Fin M => 3)) + 2))
        = Fin.natAdd (Fin.vsum (fun _ : Fin M => 3)) ⟨0, by omega⟩ := by
      ext; simp
    rw [h0, Fin.vappend_eq_append, Fin.append_right]
    exact pSpecFinal_dir_zero
  unfold OracleReduction.perfectCompleteness
  have hb : (stirTailReduction φ deg M).toReduction
      = (stirBlocksReduction φ deg M).toReduction.append stirFinalReduction.toReduction :=
    appendToReductionResidual_proof (stirBlocksReduction φ deg M) stirFinalReduction
  rw [hb]
  have hk := Reduction.append_perfectCompleteness_msg_proof
    (stirBlocksReduction φ deg M).toReduction stirFinalReduction.toReduction
    (stirBlocksReduction_perfectCompleteness init impl φ deg M δ hInit hImplSupp)
    (stirFinalReduction_perfectCompleteness init impl φ deg δ hInit)
    (Nat.zero_lt_two) hDirSeam pSpecFinal_dir_zero hInit hImplSupp
  exact hk

end Round3

end StirIOP

#print axioms StirIOP.Round3.stirTailReduction_perfectCompleteness
