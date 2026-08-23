/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Stir.RoundProtocol

/-!
# The 3-slot STIR round block (#301)

The 3-slot STIR round block `[P_to_V, V_to_P, V_to_P]` — the per-round
shape (folded oracle; out-sample challenge; shift challenge) whose `M`-fold composition with
the initial fold challenge and the final `[P,C]` block realises the `2M+2`-challenge budget
demanded by `stir_rbr_soundness` (the 2-slot fold block only yields `M+1`; see
`MultiRound.lean`'s bookkeeping). -/

namespace StirIOP

namespace Round3

open OracleSpec OracleComp ProtocolSpec STIR ReedSolomon NNReal StirIOP.Round

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The 3-slot STIR round block**: the prover sends the folded oracle (computed from the
pending fold randomness carried in the statement), then the verifier sends the out-of-domain
sample challenge and the shift/next-fold challenge. This is the per-round shape of the
`stirVSpec` layout `[C_fold, (g_j, C_out, C_shift)×M, p, C_fin]`. -/
@[reducible]
def pSpec3 (ι F : Type) : ProtocolSpec 3 :=
  ⟨!v[.P_to_V, .V_to_P, .V_to_P], !v[ι → F, F, F]⟩

theorem pSpec3_dir_zero : (pSpec3 ι F).dir 0 = .P_to_V := rfl

theorem pSpec3_dir_one : (pSpec3 ι F).dir 1 = .V_to_P := rfl

theorem pSpec3_dir_two : (pSpec3 ι F).dir 2 = .V_to_P := rfl

instance : ∀ j, OracleInterface ((pSpec3 ι F).Message j)
  | ⟨0, _⟩ => by
      unfold pSpec3 ProtocolSpec.Message
      simpa using (OracleInterface.instFunction : OracleInterface (ι → F))
  | ⟨1, h⟩ => nomatch h
  | ⟨2, h⟩ => nomatch h

instance : ∀ j, OracleInterface ((pSpec3 ι F).Challenge j) :=
  ProtocolSpec.challengeOracleInterface

/-- **The 3-slot round block has exactly 1 prover message.** Together with
`pSpec3_card_challengeIdx` this is the budget arithmetic behind `2M+2`: an initial `[C]`
(1 challenge) + `M` copies of this block (`M` messages, `2M` challenges) + a final `[P,C]`
(1 message, 1 challenge) totals `M+1` messages and `2M+2` challenges — exactly the
`stir_rbr_soundness` spec shape. -/
theorem pSpec3_card_messageIdx :
    Fintype.card ((pSpec3 ι F).MessageIdx) = 1 := by
  rw [Fintype.card_eq_one_iff]
  refine ⟨⟨0, pSpec3_dir_zero⟩, ?_⟩
  rintro ⟨⟨iv, hlt⟩, hi⟩
  have h0 : iv = 0 := by
    by_contra hne
    interval_cases iv
    · exact hne rfl
    · rw [show (⟨1, hlt⟩ : Fin 3) = (1 : Fin 3) from rfl, pSpec3_dir_one] at hi
      exact Direction.noConfusion hi
    · rw [show (⟨2, hlt⟩ : Fin 3) = (2 : Fin 3) from rfl, pSpec3_dir_two] at hi
      exact Direction.noConfusion hi
  subst h0
  rfl

/-- **The 3-slot round block has exactly 2 verifier challenges** (out-sample + shift). -/
theorem pSpec3_card_challengeIdx :
    Fintype.card ((pSpec3 ι F).ChallengeIdx) = 2 := by
  have h1 : Fintype.card ((pSpec3 ι F).ChallengeIdx)
      = Fintype.card {i : Fin 3 // ¬ ((pSpec3 ι F).dir i = .P_to_V)} :=
    Fintype.card_congr (Equiv.subtypeEquivRight fun i => by
      cases h : (pSpec3 ι F).dir i <;> simp [h])
  have h2 : Fintype.card {i : Fin 3 // (pSpec3 ι F).dir i = .P_to_V} = 1 := by
    rw [← pSpec3_card_messageIdx (ι := ι) (F := F)]
  rw [h1, Fintype.card_subtype_compl, h2, Fintype.card_fin]

/-- **The 3-slot STIR round-block prover.**
  - The input statement carries the pending fold randomness `r : F` (sent by the verifier in
    the *previous* block — initially the standalone fold challenge `C_fold`).
  - Slot 0 (`P_to_V`): sends the genuine `Combine.combine` fold of the input oracle at `r`.
  - Slots 1, 2 (`V_to_P`): receives the out-sample challenge `rOut` and the shift challenge
    `rShift`, which form the output statement `(rOut, rShift)` (the shift challenge is the
    next block's pending fold randomness).
  - The output oracle is the folded message. -/
def stirRound3Prover (φ : ι ↪ F) (deg : ℕ) :
    OracleProver []ₒ F (OStmt ι F) Unit (F × F) (OStmt ι F) Unit (pSpec3 ι F) where
  PrvState
  | 0 => (F × (∀ i, OStmt ι F i)) × Unit
  | 1 => ((ι → F) × F)            -- folded oracle, pending r (kept for output recomputation)
  | 2 => ((ι → F) × F) × F        -- + rOut
  | _ => (((ι → F) × F) × F) × F  -- + rShift

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

  output := fun st =>
    let g := st.1.1.1
    let rOut := st.1.2
    let rShift := st.2
    pure ⟨⟨(rOut, rShift), fun _ => g⟩, ()⟩

/-- **The 3-slot STIR round-block oracle verifier**: outputs the two fresh challenges as the
output statement and exposes the prover's folded message (slot 0) as the output oracle. -/
def stirRound3Verifier (φ : ι ↪ F) (deg : ℕ) :
    OracleVerifier []ₒ F (OStmt ι F) (F × F) (OStmt ι F) (pSpec3 ι F) where
  verify := fun _ chals =>
    pure (chals ⟨1, pSpec3_dir_one⟩, chals ⟨2, pSpec3_dir_two⟩)
  embed := ⟨fun _ => Sum.inr ⟨0, pSpec3_dir_zero⟩, fun _ _ _ => rfl⟩
  hEq := by
    intro i
    show (ι → F) = (pSpec3 ι F).Message ⟨0, pSpec3_dir_zero⟩
    unfold pSpec3 ProtocolSpec.Message
    simp

/-- **The 3-slot STIR round-block oracle reduction** — the per-round protocol object of the
`stirVSpec` layout, carrying the fold randomness through the statement and emitting the
out/shift challenge pair. -/
def stirRound3Reduction (φ : ι ↪ F) (deg : ℕ) :
    OracleReduction []ₒ F (OStmt ι F) Unit (F × F) (OStmt ι F) Unit (pSpec3 ι F) where
  prover := stirRound3Prover φ deg
  verifier := stirRound3Verifier φ deg

end Round3

end StirIOP

#print axioms StirIOP.Round3.stirRound3Reduction
#print axioms StirIOP.Round3.pSpec3_card_messageIdx
#print axioms StirIOP.Round3.pSpec3_card_challengeIdx
