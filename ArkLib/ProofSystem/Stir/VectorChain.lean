/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Stir.VectorBridgeMid

/-!
# The full vectorised STIR chain (#301)

The FULL VECTORISED STIR chain — the wire-format protocol object over
vector-payload specs, assembled from the landed blocks:
`[C_fold] ++ (g,C_out,C_shift) ++ (g,C_out,C_shift)×M ++ [p, C_fin]` with `M+1` fold blocks
total. Oracle threading: `OStmt → OStmt → VOStmt → VOStmt → … → VOStmt`. -/

namespace StirIOP

namespace Round3

open OracleSpec OracleComp ProtocolSpec STIR ReedSolomon NNReal StirIOP.Round

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The M-fold mid-phase of the vector chain: `seqCompose` of `M` mid-chain 3-slot blocks. -/
noncomputable def stirVectorBlocksReduction (φ : ι ↪ F) (deg : ℕ) (M : ℕ) :
    OracleReduction []ₒ F (VOStmt ι F) Unit F (VOStmt ι F) Unit
      (ProtocolSpec.seqCompose (fun _ : Fin M => (stirRound3VSpec ι F).toProtocolSpec F)) :=
  OracleReduction.seqCompose (fun _ => F) (fun _ => VOStmt ι F) (fun _ => Unit)
    (fun _ => stirRound3VectorReductionMid φ deg)
    (coh := fun _ => instStirRound3VectorReductionMidAppendCoherent φ deg)

instance instStirVectorBlocksReductionAppendCoherent (φ : ι ↪ F) (deg : ℕ) (M : ℕ) :
    OracleVerifier.Append.AppendCoherent (stirVectorBlocksReduction φ deg M).verifier :=
  OracleReduction.seqCompose_verifier_appendCoherent
    (fun _ => F) (fun _ => VOStmt ι F) (fun _ => Unit)
    (fun _ => stirRound3VectorReductionMid φ deg)
    (coh := fun _ => instStirRound3VectorReductionMidAppendCoherent φ deg)

/-! ## Compound-head interface registrations (the FullChain idiom) -/

instance instStirVecTailMsgInterface (M : ℕ) : ∀ j, OracleInterface
    (((ProtocolSpec.seqCompose (fun _ : Fin M => (stirRound3VSpec ι F).toProtocolSpec F))
      ++ₚ ((stirFinalVSpec ι F).toProtocolSpec F)).Message j) :=
  instOracleInterfaceMessageAppend

instance instStirVecTailChalInterface (M : ℕ) : ∀ j, OracleInterface
    (((ProtocolSpec.seqCompose (fun _ : Fin M => (stirRound3VSpec ι F).toProtocolSpec F))
      ++ₚ ((stirFinalVSpec ι F).toProtocolSpec F)).Challenge j) :=
  ProtocolSpec.challengeOracleInterface

@[reducible] instance instStirVecTailChalSampleable (M : ℕ) :
    ∀ i, SampleableType
      (((ProtocolSpec.seqCompose (fun _ : Fin M => (stirRound3VSpec ι F).toProtocolSpec F))
        ++ₚ ((stirFinalVSpec ι F).toProtocolSpec F)).Challenge i) :=
  fun i => instSampleableTypeChallengeAppend i

instance instStirVecHeadMsgInterface (M : ℕ) : ∀ j, OracleInterface
    ((((stirRound3VSpec ι F).toProtocolSpec F) ++ₚ
      ((ProtocolSpec.seqCompose (fun _ : Fin M => (stirRound3VSpec ι F).toProtocolSpec F))
        ++ₚ ((stirFinalVSpec ι F).toProtocolSpec F))).Message j) :=
  instOracleInterfaceMessageAppend

instance instStirVecHeadChalInterface (M : ℕ) : ∀ j, OracleInterface
    ((((stirRound3VSpec ι F).toProtocolSpec F) ++ₚ
      ((ProtocolSpec.seqCompose (fun _ : Fin M => (stirRound3VSpec ι F).toProtocolSpec F))
        ++ₚ ((stirFinalVSpec ι F).toProtocolSpec F))).Challenge j) :=
  ProtocolSpec.challengeOracleInterface

@[reducible] instance instStirVecHeadChalSampleable (M : ℕ) :
    ∀ i, SampleableType
      ((((stirRound3VSpec ι F).toProtocolSpec F) ++ₚ
        ((ProtocolSpec.seqCompose (fun _ : Fin M => (stirRound3VSpec ι F).toProtocolSpec F))
          ++ₚ ((stirFinalVSpec ι F).toProtocolSpec F))).Challenge i) :=
  fun i => instSampleableTypeChallengeAppend i

instance instStirVecFullMsgInterface (M : ℕ) : ∀ j, OracleInterface
    (((stirInitVSpec.toProtocolSpec F) ++ₚ
      (((stirRound3VSpec ι F).toProtocolSpec F) ++ₚ
        ((ProtocolSpec.seqCompose (fun _ : Fin M => (stirRound3VSpec ι F).toProtocolSpec F))
          ++ₚ ((stirFinalVSpec ι F).toProtocolSpec F)))).Message j) :=
  instOracleInterfaceMessageAppend

instance instStirVecFullChalInterface (M : ℕ) : ∀ j, OracleInterface
    (((stirInitVSpec.toProtocolSpec F) ++ₚ
      (((stirRound3VSpec ι F).toProtocolSpec F) ++ₚ
        ((ProtocolSpec.seqCompose (fun _ : Fin M => (stirRound3VSpec ι F).toProtocolSpec F))
          ++ₚ ((stirFinalVSpec ι F).toProtocolSpec F)))).Challenge j) :=
  ProtocolSpec.challengeOracleInterface

@[reducible] instance instStirVecFullChalSampleable (M : ℕ) :
    ∀ i, SampleableType
      (((stirInitVSpec.toProtocolSpec F) ++ₚ
        (((stirRound3VSpec ι F).toProtocolSpec F) ++ₚ
          ((ProtocolSpec.seqCompose (fun _ : Fin M => (stirRound3VSpec ι F).toProtocolSpec F))
            ++ₚ ((stirFinalVSpec ι F).toProtocolSpec F)))).Challenge i) :=
  fun i => instSampleableTypeChallengeAppend i

/-! ## The full vectorised chain -/

/-- **The FULL VECTORISED STIR chain** with `M + 1` fold blocks:
`[C_fold] ++ (g,C_out,C_shift) ++ (g,C_out,C_shift)×M ++ [p, C_fin]`, all payloads in the
vector wire format. The first 3-slot block consumes the chain's function-shaped input oracle
and packs; the `M` mid blocks and the final block thread packed oracles. -/
noncomputable def stirFullVectorReduction (φ : ι ↪ F) (deg : ℕ) (M : ℕ) :
    OracleReduction []ₒ Unit (OStmt ι F) Unit (F × F) (VOStmt ι F) Unit
      ((stirInitVSpec.toProtocolSpec F) ++ₚ
        (((stirRound3VSpec ι F).toProtocolSpec F) ++ₚ
          ((ProtocolSpec.seqCompose (fun _ : Fin M => (stirRound3VSpec ι F).toProtocolSpec F))
            ++ₚ ((stirFinalVSpec ι F).toProtocolSpec F)))) :=
  OracleReduction.append stirInitVectorReduction
    (OracleReduction.append (stirRound3VectorReduction φ deg)
      (OracleReduction.append (stirVectorBlocksReduction φ deg M)
        stirFinalVectorReductionMid))

/-! ## The spec-shape counts: `M+2` messages, `2(M+1)+2` challenges for `M+1` fold blocks -/

/-- The vectorised mid-phase has `2M` challenges. -/
theorem stirVectorBlocks_card_challengeIdx (M : ℕ) :
    Fintype.card (ProtocolSpec.seqCompose
      (fun _ : Fin M => (stirRound3VSpec ι F).toProtocolSpec F)).ChallengeIdx = 2 * M := by
  rw [← Fintype.card_congr (ProtocolSpec.seqComposeChallengeEquiv
    (fun _ : Fin M => (stirRound3VSpec ι F).toProtocolSpec F))]
  rw [Fintype.card_sigma]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [show Fintype.card ((stirRound3VSpec ι F).toProtocolSpec F).ChallengeIdx = 2 from
    stirRound3VSpec_card_challengeIdx]
  ring

/-- **The full vectorised chain has exactly `2(M+1)+2` challenges** (for its `M+1` fold
blocks) — the `stir_rbr_soundness` budget at depth `M+1`. -/
theorem stirFullVector_card_challengeIdx (M : ℕ) :
    Fintype.card (((stirInitVSpec.toProtocolSpec F) ++ₚ
      (((stirRound3VSpec ι F).toProtocolSpec F) ++ₚ
        ((ProtocolSpec.seqCompose (fun _ : Fin M => (stirRound3VSpec ι F).toProtocolSpec F))
          ++ₚ ((stirFinalVSpec ι F).toProtocolSpec F)))).ChallengeIdx)
      = 2 * (M + 1) + 2 := by
  rw [← Fintype.card_congr (ProtocolSpec.ChallengeIdx.sumEquiv
    (pSpec₁ := stirInitVSpec.toProtocolSpec F))]
  rw [Fintype.card_sum]
  rw [← Fintype.card_congr (ProtocolSpec.ChallengeIdx.sumEquiv
    (pSpec₁ := (stirRound3VSpec ι F).toProtocolSpec F))]
  rw [Fintype.card_sum]
  rw [← Fintype.card_congr (ProtocolSpec.ChallengeIdx.sumEquiv
    (pSpec₁ := ProtocolSpec.seqCompose
      (fun _ : Fin M => (stirRound3VSpec ι F).toProtocolSpec F)))]
  rw [Fintype.card_sum, stirInitVSpec_card_challengeIdx, stirRound3VSpec_card_challengeIdx,
    stirVectorBlocks_card_challengeIdx, stirFinalVSpec_card_challengeIdx]
  ring

end Round3

end StirIOP

#print axioms StirIOP.Round3.stirVectorBlocksReduction
#print axioms StirIOP.Round3.stirFullVectorReduction
#print axioms StirIOP.Round3.stirFullVector_card_challengeIdx
