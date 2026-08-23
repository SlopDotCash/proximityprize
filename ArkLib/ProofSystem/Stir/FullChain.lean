/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Stir.Round3Compose

/-!
# The full STIR protocol chain (#301)

The full STIR protocol chain `[C_fold] ++ (g,C_out,C_shift)×M ++ [p,C_fin]`
— the heterogeneous block assembly realising the literal `stir_rbr_soundness` spec shape
(`M+1` messages, `2M+2` challenges). -/

namespace StirIOP

namespace Round3

open OracleSpec OracleComp ProtocolSpec STIR ReedSolomon NNReal StirIOP.Round

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The uniform-threading 3-slot block (output statement = shift challenge) -/

/-- The 3-slot block prover with uniform statement threading: the output statement is just the
shift challenge (the next block's pending fold randomness), so `M` blocks chain with the
constant statement family `F`. -/
def stirRound3Prover' (φ : ι ↪ F) (deg : ℕ) :
    OracleProver []ₒ F (OStmt ι F) Unit F (OStmt ι F) Unit (pSpec3 ι F) where
  PrvState
  | 0 => (F × (∀ i, OStmt ι F i)) × Unit
  | 1 => ((ι → F) × F)
  | 2 => ((ι → F) × F) × F
  | _ => (((ι → F) × F) × F) × F
  input := id
  sendMessage
  | ⟨0, _⟩ => fun st =>
      let f : ι → F := st.1.2 ()
      let r : F := st.1.1
      let g := Combine.combine φ deg r (fun _ : Fin 1 => f) (fun _ : Fin 1 => deg)
      pure ⟨g, (g, r)⟩
  | ⟨1, h⟩ => nomatch h
  | ⟨2, h⟩ => nomatch h
  receiveChallenge
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => fun st => pure (fun (rOut : F) => ⟨st, rOut⟩)
  | ⟨2, _⟩ => fun st => pure (fun (rShift : F) => ⟨st, rShift⟩)
  output := fun st => pure ⟨⟨st.2, fun _ => st.1.1.1⟩, ()⟩

/-- The 3-slot block verifier with uniform statement threading. -/
def stirRound3Verifier' (φ : ι ↪ F) (deg : ℕ) :
    OracleVerifier []ₒ F (OStmt ι F) F (OStmt ι F) (pSpec3 ι F) where
  verify := fun _ chals => pure (chals ⟨2, pSpec3_dir_two⟩)
  embed := ⟨fun _ => Sum.inr ⟨0, pSpec3_dir_zero⟩, fun _ _ _ => rfl⟩
  hEq := by
    intro i
    show (ι → F) = (pSpec3 ι F).Message ⟨0, pSpec3_dir_zero⟩
    unfold pSpec3 ProtocolSpec.Message
    simp

/-- The uniform-threading 3-slot block reduction. -/
def stirRound3Reduction' (φ : ι ↪ F) (deg : ℕ) :
    OracleReduction []ₒ F (OStmt ι F) Unit F (OStmt ι F) Unit (pSpec3 ι F) where
  prover := stirRound3Prover' φ deg
  verifier := stirRound3Verifier' φ deg

instance instStirRound3Verifier'AppendCoherent (φ : ι ↪ F) (deg : ℕ) :
    OracleVerifier.Append.AppendCoherent (stirRound3Verifier' φ deg) where
  hCohInl := fun i k h => by
    exact absurd h (by simp [stirRound3Verifier'])
  hCohInr := fun i k h => by
    have hk : k = ⟨0, pSpec3_dir_zero⟩ := by
      have := h.symm
      simp only [stirRound3Verifier', Function.Embedding.coeFn_mk] at this
      exact (Sum.inr.inj this)
    subst hk
    apply eq_of_heq
    refine HEq.trans ?_ (cast_heq _ _).symm
    rfl

instance instStirRound3Reduction'AppendCoherent (φ : ι ↪ F) (deg : ℕ) :
    OracleVerifier.Append.AppendCoherent (stirRound3Reduction' φ deg).verifier :=
  instStirRound3Verifier'AppendCoherent φ deg

/-! ## The M-block middle composite -/

/-- **The `M`-block middle phase**: `seqCompose` of `M` uniform-threading 3-slot blocks. -/
noncomputable def stirBlocksReduction (φ : ι ↪ F) (deg : ℕ) (M : ℕ) :
    OracleReduction []ₒ F (OStmt ι F) Unit F (OStmt ι F) Unit
      (ProtocolSpec.seqCompose (fun _ : Fin M => pSpec3 ι F)) :=
  OracleReduction.seqCompose (fun _ => F) (fun _ => OStmt ι F) (fun _ => Unit)
    (fun _ => stirRound3Reduction' φ deg)
    (coh := fun _ => instStirRound3Reduction'AppendCoherent φ deg)

instance instStirBlocksReductionAppendCoherent (φ : ι ↪ F) (deg : ℕ) (M : ℕ) :
    OracleVerifier.Append.AppendCoherent (stirBlocksReduction φ deg M).verifier :=
  OracleReduction.seqCompose_verifier_appendCoherent
    (fun _ => F) (fun _ => OStmt ι F) (fun _ => Unit)
    (fun _ => stirRound3Reduction' φ deg)
    (coh := fun _ => instStirRound3Reduction'AppendCoherent φ deg)

instance instStirInitReductionAppendCoherent :
    OracleVerifier.Append.AppendCoherent (stirInitReduction (ι := ι) (F := F)).verifier :=
  instStirInitVerifierAppendCoherent

/-! ## Compound-spec interface instances (registered by name — the FRI/MultiRound idiom:
instance search does not find the generic append instance at these compound heads). -/

instance instStirChainInnerMessageInterface (M : ℕ) : ∀ j, OracleInterface
    (((ProtocolSpec.seqCompose (fun _ : Fin M => pSpec3 ι F)) ++ₚ pSpecFinal ι F).Message j) :=
  instOracleInterfaceMessageAppend

instance instStirChainInnerChallengeInterface (M : ℕ) : ∀ j, OracleInterface
    (((ProtocolSpec.seqCompose (fun _ : Fin M => pSpec3 ι F)) ++ₚ pSpecFinal ι F).Challenge j) :=
  ProtocolSpec.challengeOracleInterface

instance instStirChainMessageInterface (M : ℕ) : ∀ j, OracleInterface
    ((pSpecInit F ++ₚ
      ((ProtocolSpec.seqCompose (fun _ : Fin M => pSpec3 ι F)) ++ₚ pSpecFinal ι F)).Message j) :=
  instOracleInterfaceMessageAppend

instance instStirChainChallengeInterface (M : ℕ) : ∀ j, OracleInterface
    ((pSpecInit F ++ₚ
      ((ProtocolSpec.seqCompose (fun _ : Fin M => pSpec3 ι F)) ++ₚ pSpecFinal ι F)).Challenge j) :=
  ProtocolSpec.challengeOracleInterface

/-! ## The full chain -/

/-- **The full STIR protocol chain** `[C_fold] ++ (g, C_out, C_shift)×M ++ [p, C_fin]`:
initial fold challenge, `M` uniform 3-slot blocks, final in-the-clear message + repetition
challenge. The output statement is the final `(pending randomness, repetition challenge)`
pair; the output oracle is the final in-the-clear word. -/
noncomputable def stirFullReduction (φ : ι ↪ F) (deg : ℕ) (M : ℕ) :
    OracleReduction []ₒ Unit (OStmt ι F) Unit (F × F) (OStmt ι F) Unit
      (pSpecInit F ++ₚ
        (ProtocolSpec.seqCompose (fun _ : Fin M => pSpec3 ι F) ++ₚ pSpecFinal ι F)) :=
  OracleReduction.append stirInitReduction
    (OracleReduction.append (stirBlocksReduction φ deg M) stirFinalReduction)

/-! ## The spec-shape counts: `M+1` messages, `2M+2` challenges -/

/-- The M-block middle phase has exactly `2M` challenges. -/
theorem stirBlocks_card_challengeIdx (M : ℕ) :
    Fintype.card (ProtocolSpec.seqCompose (fun _ : Fin M => pSpec3 ι F)).ChallengeIdx
      = 2 * M := by
  rw [← Fintype.card_congr (ProtocolSpec.seqComposeChallengeEquiv
    (fun _ : Fin M => pSpec3 ι F))]
  rw [Fintype.card_sigma]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [pSpec3_card_challengeIdx]
  ring

/-- The M-block middle phase has exactly `M` messages. -/
theorem stirBlocks_card_messageIdx (M : ℕ) :
    Fintype.card (ProtocolSpec.seqCompose (fun _ : Fin M => pSpec3 ι F)).MessageIdx
      = M := by
  rw [← Fintype.card_congr (ProtocolSpec.seqComposeMessageEquiv
    (pSpec := fun _ : Fin M => pSpec3 ι F))]
  rw [Fintype.card_sigma]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [pSpec3_card_messageIdx, mul_one]

/-- **The full STIR chain has exactly `2M+2` verifier challenges** — the literal count
demanded by the opening conjunct of `stir_rbr_soundness`, now realised by an actual protocol
object (`stirFullReduction`). -/
theorem stirFull_card_challengeIdx (M : ℕ) :
    Fintype.card ((pSpecInit F ++ₚ
        (ProtocolSpec.seqCompose (fun _ : Fin M => pSpec3 ι F) ++ₚ pSpecFinal ι F))
      |>.ChallengeIdx) = 2 * M + 2 := by
  rw [← Fintype.card_congr (ProtocolSpec.ChallengeIdx.sumEquiv
    (pSpec₁ := pSpecInit F)
    (pSpec₂ := ProtocolSpec.seqCompose (fun _ : Fin M => pSpec3 ι F) ++ₚ pSpecFinal ι F))]
  rw [Fintype.card_sum]
  rw [← Fintype.card_congr (ProtocolSpec.ChallengeIdx.sumEquiv
    (pSpec₁ := ProtocolSpec.seqCompose (fun _ : Fin M => pSpec3 ι F))
    (pSpec₂ := pSpecFinal ι F))]
  rw [Fintype.card_sum, pSpecInit_card_challengeIdx, stirBlocks_card_challengeIdx,
    pSpecFinal_card_challengeIdx]
  ring

/-- **The full STIR chain has exactly `M+1` prover messages** (the `M` folded oracles plus the
final in-the-clear word). -/
theorem stirFull_card_messageIdx (M : ℕ) :
    Fintype.card ((pSpecInit F ++ₚ
        (ProtocolSpec.seqCompose (fun _ : Fin M => pSpec3 ι F) ++ₚ pSpecFinal ι F))
      |>.MessageIdx) = M + 1 := by
  rw [← Fintype.card_congr (ProtocolSpec.MessageIdx.sumEquiv
    (pSpec₁ := pSpecInit F)
    (pSpec₂ := ProtocolSpec.seqCompose (fun _ : Fin M => pSpec3 ι F) ++ₚ pSpecFinal ι F))]
  rw [Fintype.card_sum]
  rw [← Fintype.card_congr (ProtocolSpec.MessageIdx.sumEquiv
    (pSpec₁ := ProtocolSpec.seqCompose (fun _ : Fin M => pSpec3 ι F))
    (pSpec₂ := pSpecFinal ι F))]
  rw [Fintype.card_sum, pSpecInit_card_messageIdx, stirBlocks_card_messageIdx,
    pSpecFinal_card_messageIdx]
  omega

end Round3

end StirIOP

#print axioms StirIOP.Round3.stirRound3Reduction'
#print axioms StirIOP.Round3.stirBlocksReduction
#print axioms StirIOP.Round3.stirFullReduction
#print axioms StirIOP.Round3.stirFull_card_challengeIdx
#print axioms StirIOP.Round3.stirFull_card_messageIdx
