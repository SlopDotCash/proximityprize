/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Stir.VSpecBridge

/-!
# The literal chain VectorSpec's budgets (#301)

The literal chain `VectorSpec`'s challenge/message budgets, transferred
from the proven compound counts along the packaging bridge — `stirChainVSpec` is thereby a
direct witness for `stir_rbr_soundness`'s `∃ vPSpec` with the `2(M+1)+2` count. -/

namespace StirIOP

namespace Round3

open OracleSpec OracleComp ProtocolSpec ProtocolSpec.VectorSpec STIR NNReal StirIOP.Round

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The literal chain spec's direction function agrees with the compound's (read off the
packaging bridge). -/
theorem stirChainVSpec_dir_eq (M : ℕ) :
    ((stirChainVSpec ι F M).toProtocolSpec F).dir
      = ((stirInitVSpec.toProtocolSpec F) ++ₚ
          (((stirRound3VSpec ι F).toProtocolSpec F) ++ₚ
            ((ProtocolSpec.seqCompose
                (fun _ : Fin M => (stirRound3VSpec ι F).toProtocolSpec F))
              ++ₚ ((stirFinalVSpec ι F).toProtocolSpec F)))).dir :=
  congrArg ProtocolSpec.dir (stirChainVSpec_toProtocolSpec M)

/-- **The literal chain `VectorSpec` has exactly `2(M+1)+2` challenges** — transferred from
the proven compound count along the bridge; `stirChainVSpec` is hence a direct witness for the
`∃ vPSpec` of `stir_rbr_soundness` at depth `M+1`. -/
theorem stirChainVSpec_card_challengeIdx (M : ℕ) :
    Fintype.card (stirChainVSpec ι F M).ChallengeIdx = 2 * (M + 1) + 2 := by
  have hdir := stirChainVSpec_dir_eq (ι := ι) (F := F) M
  have hcongr : Fintype.card (stirChainVSpec ι F M).ChallengeIdx
      = Fintype.card (((stirInitVSpec.toProtocolSpec F) ++ₚ
          (((stirRound3VSpec ι F).toProtocolSpec F) ++ₚ
            ((ProtocolSpec.seqCompose
                (fun _ : Fin M => (stirRound3VSpec ι F).toProtocolSpec F))
              ++ₚ ((stirFinalVSpec ι F).toProtocolSpec F)))).ChallengeIdx) := by
    apply Fintype.card_congr
    apply Equiv.subtypeEquivRight
    intro i
    rw [show (stirChainVSpec ι F M).dir
        = ((stirChainVSpec ι F M).toProtocolSpec F).dir from rfl, hdir]
  rw [hcongr]
  exact stirFullVector_card_challengeIdx M

/-- The vectorised mid-phase has `M` messages. -/
theorem stirVectorBlocks_card_messageIdx (M : ℕ) :
    Fintype.card (ProtocolSpec.seqCompose
      (fun _ : Fin M => (stirRound3VSpec ι F).toProtocolSpec F)).MessageIdx = M := by
  rw [← Fintype.card_congr (ProtocolSpec.seqComposeMessageEquiv
    (pSpec := fun _ : Fin M => (stirRound3VSpec ι F).toProtocolSpec F))]
  rw [Fintype.card_sigma]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [show Fintype.card ((stirRound3VSpec ι F).toProtocolSpec F).MessageIdx = 1 from
    stirRound3VSpec_card_messageIdx]
  ring

/-- **The full vectorised chain has exactly `M + 2` prover messages** (the `M+1` folded
oracles plus the final in-the-clear word). -/
theorem stirFullVector_card_messageIdx (M : ℕ) :
    Fintype.card (((stirInitVSpec.toProtocolSpec F) ++ₚ
      (((stirRound3VSpec ι F).toProtocolSpec F) ++ₚ
        ((ProtocolSpec.seqCompose (fun _ : Fin M => (stirRound3VSpec ι F).toProtocolSpec F))
          ++ₚ ((stirFinalVSpec ι F).toProtocolSpec F)))).MessageIdx)
      = M + 2 := by
  rw [← Fintype.card_congr (ProtocolSpec.MessageIdx.sumEquiv
    (pSpec₁ := stirInitVSpec.toProtocolSpec F))]
  rw [Fintype.card_sum]
  rw [← Fintype.card_congr (ProtocolSpec.MessageIdx.sumEquiv
    (pSpec₁ := (stirRound3VSpec ι F).toProtocolSpec F))]
  rw [Fintype.card_sum]
  rw [← Fintype.card_congr (ProtocolSpec.MessageIdx.sumEquiv
    (pSpec₁ := ProtocolSpec.seqCompose
      (fun _ : Fin M => (stirRound3VSpec ι F).toProtocolSpec F)))]
  rw [Fintype.card_sum, stirInitVSpec_card_messageIdx, stirRound3VSpec_card_messageIdx,
    stirVectorBlocks_card_messageIdx, stirFinalVSpec_card_messageIdx]
  ring

/-- **The literal chain `VectorSpec` has exactly `M + 2` messages** — transferred along the
packaging bridge (the `MessageIdx` mirror of `stirChainVSpec_card_challengeIdx`). -/
theorem stirChainVSpec_card_messageIdx (M : ℕ) :
    Fintype.card (stirChainVSpec ι F M).MessageIdx = M + 2 := by
  have hdir := stirChainVSpec_dir_eq (ι := ι) (F := F) M
  have hcongr : Fintype.card (stirChainVSpec ι F M).MessageIdx
      = Fintype.card (((stirInitVSpec.toProtocolSpec F) ++ₚ
          (((stirRound3VSpec ι F).toProtocolSpec F) ++ₚ
            ((ProtocolSpec.seqCompose
                (fun _ : Fin M => (stirRound3VSpec ι F).toProtocolSpec F))
              ++ₚ ((stirFinalVSpec ι F).toProtocolSpec F)))).MessageIdx) := by
    apply Fintype.card_congr
    apply Equiv.subtypeEquivRight
    intro i
    rw [show (stirChainVSpec ι F M).dir
        = ((stirChainVSpec ι F M).toProtocolSpec F).dir from rfl, hdir]
  rw [hcongr]
  exact stirFullVector_card_messageIdx M

end Round3

end StirIOP

#print axioms StirIOP.Round3.stirChainVSpec_card_challengeIdx
#print axioms StirIOP.Round3.stirChainVSpec_card_messageIdx
