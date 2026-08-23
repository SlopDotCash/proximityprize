/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Stir.VectorBridge

/-!
# Chain-composable vectorised STIR blocks (#301)

The CHAIN-COMPOSABLE vectorised blocks — `VOStmt → VOStmt` mid-chain
variants of the 3-slot and final blocks (the landed wire-format ports take `OStmt` input, so
consecutive blocks do not compose; these variants read the incoming PACKED oracle via
`unpackFiniteFunction`, making the vector chain `OStmt → VOStmt → … → VOStmt` assemble). -/

namespace StirIOP

namespace Round3

open OracleSpec OracleComp ProtocolSpec STIR ReedSolomon NNReal StirIOP.Round
open WhirIOP.Construction

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The mid-chain 3-slot block: packed oracle in, packed oracle out -/

/-- The mid-chain vectorised 3-slot prover: identical to `stirRound3VectorProver` except the
incoming oracle arrives PACKED (`VOStmt`) and is unpacked before folding. -/
noncomputable def stirRound3VectorProverMid (φ : ι ↪ F) (deg : ℕ) :
    OracleProver []ₒ F (VOStmt ι F) Unit F (VOStmt ι F) Unit
      ((stirRound3VSpec ι F).toProtocolSpec F) where
  PrvState
  | 0 => (F × (∀ i, VOStmt ι F i)) × Unit
  | 1 => Vector F (Fintype.card ι)
  | 2 => Vector F (Fintype.card ι) × F
  | _ => (Vector F (Fintype.card ι) × F) × F

  input := id

  sendMessage
  | ⟨0, _⟩ => fun st =>
      let f : ι → F := unpackFiniteFunction ι (st.1.2 ())
      let r : F := st.1.1
      let g := packFiniteFunction ι
        (Combine.combine φ deg r (fun _ : Fin 1 => f) (fun _ : Fin 1 => deg))
      pure ⟨g, g⟩
  | ⟨1, h⟩ => nomatch h
  | ⟨2, h⟩ => nomatch h

  receiveChallenge
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => fun st => pure (fun (rOut : Vector F 1) => ⟨st, rOut.get 0⟩)
  | ⟨2, _⟩ => fun st => pure (fun (rShift : Vector F 1) => ⟨st, rShift.get 0⟩)

  output := fun st => pure ⟨⟨st.2, fun _ => st.1.1⟩, ()⟩

/-- The mid-chain vectorised 3-slot verifier (same wire behaviour; `VOStmt` input family). -/
def stirRound3VectorVerifierMid (φ : ι ↪ F) (deg : ℕ) :
    OracleVerifier []ₒ F (VOStmt ι F) F (VOStmt ι F)
      ((stirRound3VSpec ι F).toProtocolSpec F) where
  verify := fun _ chals =>
    let rShift : Vector F 1 := chals ⟨2, stirRound3VSpec_dir_two⟩
    pure (rShift.get 0)
  embed := ⟨fun _ => Sum.inr ⟨0, stirRound3VSpec_dir_zero⟩, fun _ _ _ => rfl⟩
  hEq := fun _ => rfl

/-- **The mid-chain vectorised 3-slot block** (`VOStmt → VOStmt`): chain-composable under
`seqCompose` with the constant statement family `F`. -/
noncomputable def stirRound3VectorReductionMid (φ : ι ↪ F) (deg : ℕ) :
    OracleReduction []ₒ F (VOStmt ι F) Unit F (VOStmt ι F) Unit
      ((stirRound3VSpec ι F).toProtocolSpec F) where
  prover := stirRound3VectorProverMid φ deg
  verifier := stirRound3VectorVerifierMid φ deg

instance instStirRound3VectorVerifierMidAppendCoherent (φ : ι ↪ F) (deg : ℕ) :
    OracleVerifier.Append.AppendCoherent (stirRound3VectorVerifierMid φ deg) where
  hCohInl := fun i k h => by
    exact absurd h (by simp [stirRound3VectorVerifierMid])
  hCohInr := fun i k h => by
    have hk : k = ⟨0, stirRound3VSpec_dir_zero⟩ := by
      have := h.symm
      simp only [stirRound3VectorVerifierMid, Function.Embedding.coeFn_mk] at this
      exact (Sum.inr.inj this)
    subst hk
    apply eq_of_heq
    refine HEq.trans ?_ (cast_heq _ _).symm
    rfl

instance instStirRound3VectorReductionMidAppendCoherent (φ : ι ↪ F) (deg : ℕ) :
    OracleVerifier.Append.AppendCoherent (stirRound3VectorReductionMid φ deg).verifier :=
  instStirRound3VectorVerifierMidAppendCoherent φ deg

/-! ## The mid-chain final block: packed oracle in, packed final word out -/

/-- The mid-chain vectorised final prover: the incoming oracle arrives packed; the final word
is sent (already packed) in the clear. -/
noncomputable def stirFinalVectorProverMid :
    OracleProver []ₒ F (VOStmt ι F) Unit (F × F) (VOStmt ι F) Unit
      ((stirFinalVSpec ι F).toProtocolSpec F) where
  PrvState
  | 0 => (F × (∀ i, VOStmt ι F i)) × Unit
  | 1 => (F × Vector F (Fintype.card ι))
  | _ => (F × Vector F (Fintype.card ι)) × F

  input := id

  sendMessage
  | ⟨0, _⟩ => fun st => pure ⟨st.1.2 (), (st.1.1, st.1.2 ())⟩
  | ⟨1, h⟩ => nomatch h

  receiveChallenge
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => fun st => pure (fun (rFin : Vector F 1) => ⟨st, rFin.get 0⟩)

  output := fun st => pure ⟨⟨(st.1.1, st.2), fun _ => st.1.2⟩, ()⟩

/-- The mid-chain vectorised final verifier. -/
def stirFinalVectorVerifierMid :
    OracleVerifier []ₒ F (VOStmt ι F) (F × F) (VOStmt ι F)
      ((stirFinalVSpec ι F).toProtocolSpec F) where
  verify := fun r chals =>
    let rFin : Vector F 1 := chals ⟨1, stirFinalVSpec_dir_one⟩
    pure (r, rFin.get 0)
  embed := ⟨fun _ => Sum.inr ⟨0, stirFinalVSpec_dir_zero⟩, fun _ _ _ => rfl⟩
  hEq := fun _ => rfl

/-- **The mid-chain vectorised final block** (`VOStmt → VOStmt`). -/
noncomputable def stirFinalVectorReductionMid :
    OracleReduction []ₒ F (VOStmt ι F) Unit (F × F) (VOStmt ι F) Unit
      ((stirFinalVSpec ι F).toProtocolSpec F) where
  prover := stirFinalVectorProverMid
  verifier := stirFinalVectorVerifierMid

instance instStirFinalVectorVerifierMidAppendCoherent :
    OracleVerifier.Append.AppendCoherent (stirFinalVectorVerifierMid (ι := ι) (F := F)) where
  hCohInl := fun i k h => by
    exact absurd h (by simp [stirFinalVectorVerifierMid])
  hCohInr := fun i k h => by
    have hk : k = ⟨0, stirFinalVSpec_dir_zero⟩ := by
      have := h.symm
      simp only [stirFinalVectorVerifierMid, Function.Embedding.coeFn_mk] at this
      exact (Sum.inr.inj this)
    subst hk
    apply eq_of_heq
    refine HEq.trans ?_ (cast_heq _ _).symm
    rfl

instance instStirFinalVectorReductionMidAppendCoherent :
    OracleVerifier.Append.AppendCoherent
      (stirFinalVectorReductionMid (ι := ι) (F := F)).verifier :=
  instStirFinalVectorVerifierMidAppendCoherent

/-! ## Round-trip honesty for the mid-chain blocks -/

/-- The mid-chain fold of an honestly packed oracle unpacks to the original function (the
`unpack ∘ pack ∘ combine ∘ unpack ∘ pack` round trip collapses). -/
theorem unpack_stirRound3VectorMid_message (φ : ι ↪ F) (deg : ℕ) (r : F) (f : ι → F) :
    unpackFiniteFunction ι
        (packFiniteFunction ι
          (Combine.combine φ deg r
            (fun _ : Fin 1 => unpackFiniteFunction ι (packFiniteFunction ι f))
            (fun _ : Fin 1 => deg)))
      = f := by
  rw [unpack_packFiniteFunction, combine_single_self, unpack_packFiniteFunction]

end Round3

end StirIOP

#print axioms StirIOP.Round3.stirRound3VectorReductionMid
#print axioms StirIOP.Round3.instStirRound3VectorReductionMidAppendCoherent
#print axioms StirIOP.Round3.stirFinalVectorReductionMid
#print axioms StirIOP.Round3.instStirFinalVectorReductionMidAppendCoherent
#print axioms StirIOP.Round3.unpack_stirRound3VectorMid_message
