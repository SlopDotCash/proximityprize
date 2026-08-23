/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Stir.Round3Block
import ArkLib.ProofSystem.Stir.MultiRound

/-!
# Coherence + the boundary blocks of the stirVSpec layout (#301)

Coherence instances and the initial `[C]` and final `[P,C]` blocks of the stirVSpec
layout `[C_fold] ++ (g, C_out, C_shift)×M ++ [p, C_fin]`. -/

namespace StirIOP

namespace Round3

open OracleSpec OracleComp ProtocolSpec STIR ReedSolomon NNReal StirIOP.Round

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The 3-slot round-block verifier is `AppendCoherent` (its `embed` routes the unique output
oracle to the prover's slot-0 message). -/
instance instStirRound3VerifierAppendCoherent (φ : ι ↪ F) (deg : ℕ) :
    OracleVerifier.Append.AppendCoherent (stirRound3Verifier φ deg) where
  hCohInl := fun i k h => by
    exact absurd h (by simp [stirRound3Verifier])
  hCohInr := fun i k h => by
    have hk : k = ⟨0, pSpec3_dir_zero⟩ := by
      have := h.symm
      simp only [stirRound3Verifier, Function.Embedding.coeFn_mk] at this
      exact (Sum.inr.inj this)
    subst hk
    apply eq_of_heq
    refine HEq.trans ?_ (cast_heq _ _).symm
    rfl

instance instStirRound3ReductionAppendCoherent (φ : ι ↪ F) (deg : ℕ) :
    OracleVerifier.Append.AppendCoherent (stirRound3Reduction φ deg).verifier :=
  instStirRound3VerifierAppendCoherent φ deg

/-! ## The initial `[C_fold]` block -/

/-- The initial 1-slot spec: the standalone fold challenge `C_fold`. -/
@[reducible]
def pSpecInit (F : Type) : ProtocolSpec 1 := ⟨!v[.V_to_P], !v[F]⟩

theorem pSpecInit_dir_zero : (pSpecInit F).dir 0 = .V_to_P := rfl

instance : ∀ j, OracleInterface ((pSpecInit F).Message j)
  | ⟨0, h⟩ => nomatch h

instance : ∀ j, OracleInterface ((pSpecInit F).Challenge j) :=
  ProtocolSpec.challengeOracleInterface

theorem pSpecInit_card_messageIdx : Fintype.card ((pSpecInit F).MessageIdx) = 0 := by
  rw [Fintype.card_eq_zero_iff]
  refine ⟨fun ⟨⟨iv, hlt⟩, hi⟩ => ?_⟩
  have h0 : iv = 0 := by omega
  subst h0
  simp [pSpecInit] at hi

theorem pSpecInit_card_challengeIdx : Fintype.card ((pSpecInit F).ChallengeIdx) = 1 := by
  have h1 : Fintype.card ((pSpecInit F).ChallengeIdx)
      = Fintype.card {i : Fin 1 // ¬ ((pSpecInit F).dir i = .P_to_V)} :=
    Fintype.card_congr (Equiv.subtypeEquivRight fun i => by
      cases h : (pSpecInit F).dir i <;> simp [h])
  have h2 : Fintype.card {i : Fin 1 // (pSpecInit F).dir i = .P_to_V} = 0 := by
    rw [← pSpecInit_card_messageIdx (F := F)]
  rw [h1, Fintype.card_subtype_compl, h2, Fintype.card_fin]

/-- **The initial block prover**: receives the standalone fold challenge `C_fold` and outputs
it as the statement (the pending randomness for the first 3-slot block); the oracle is
forwarded unchanged. -/
def stirInitProver :
    OracleProver []ₒ Unit (OStmt ι F) Unit F (OStmt ι F) Unit (pSpecInit F) where
  PrvState
  | 0 => (Unit × (∀ i, OStmt ι F i)) × Unit
  | _ => ((Unit × (∀ i, OStmt ι F i)) × Unit) × F
  input := id
  sendMessage
  | ⟨0, h⟩ => nomatch h
  receiveChallenge
  | ⟨0, _⟩ => fun st => pure (fun (r : F) => ⟨st, r⟩)
  output := fun st => pure ⟨⟨st.2, st.1.1.2⟩, ()⟩

/-- **The initial block verifier**: outputs the fold challenge as the statement and forwards
the input oracle. -/
def stirInitVerifier :
    OracleVerifier []ₒ Unit (OStmt ι F) F (OStmt ι F) (pSpecInit F) where
  verify := fun _ chals => pure (chals ⟨0, pSpecInit_dir_zero⟩)
  embed := ⟨fun _ => Sum.inl (), fun _ _ _ => rfl⟩
  hEq := fun _ => rfl

/-- **The initial `[C_fold]` block** of the stirVSpec layout. -/
def stirInitReduction :
    OracleReduction []ₒ Unit (OStmt ι F) Unit F (OStmt ι F) Unit (pSpecInit F) where
  prover := stirInitProver
  verifier := stirInitVerifier

instance instStirInitVerifierAppendCoherent :
    OracleVerifier.Append.AppendCoherent (stirInitVerifier (ι := ι) (F := F)) where
  hCohInl := fun i k h => by
    have hk : k = () := rfl
    subst hk
    apply eq_of_heq
    refine HEq.trans ?_ (cast_heq _ _).symm
    rfl
  hCohInr := fun i k h => by
    exact absurd h (by simp [stirInitVerifier])

/-! ## The final `[p, C_fin]` block -/

/-- The final 2-slot spec: the in-the-clear final message then the repetition challenge. -/
@[reducible]
def pSpecFinal (ι F : Type) : ProtocolSpec 2 := ⟨!v[.P_to_V, .V_to_P], !v[ι → F, F]⟩

theorem pSpecFinal_dir_zero : (pSpecFinal ι F).dir 0 = .P_to_V := rfl

theorem pSpecFinal_dir_one : (pSpecFinal ι F).dir 1 = .V_to_P := rfl

instance : ∀ j, OracleInterface ((pSpecFinal ι F).Message j)
  | ⟨0, _⟩ => by
      unfold pSpecFinal ProtocolSpec.Message
      simpa using (OracleInterface.instFunction : OracleInterface (ι → F))
  | ⟨1, h⟩ => nomatch h

instance : ∀ j, OracleInterface ((pSpecFinal ι F).Challenge j) :=
  ProtocolSpec.challengeOracleInterface

theorem pSpecFinal_card_messageIdx : Fintype.card ((pSpecFinal ι F).MessageIdx) = 1 := by
  rw [Fintype.card_eq_one_iff]
  refine ⟨⟨0, pSpecFinal_dir_zero⟩, ?_⟩
  rintro ⟨⟨iv, hlt⟩, hi⟩
  have h0 : iv = 0 := by
    by_contra hne
    have h1 : (⟨iv, hlt⟩ : Fin 2) = (1 : Fin 2) := by
      apply Fin.ext; simp only [Fin.val_one]; omega
    rw [h1, pSpecFinal_dir_one] at hi
    exact Direction.noConfusion hi
  subst h0
  rfl

theorem pSpecFinal_card_challengeIdx : Fintype.card ((pSpecFinal ι F).ChallengeIdx) = 1 := by
  have h1 : Fintype.card ((pSpecFinal ι F).ChallengeIdx)
      = Fintype.card {i : Fin 2 // ¬ ((pSpecFinal ι F).dir i = .P_to_V)} :=
    Fintype.card_congr (Equiv.subtypeEquivRight fun i => by
      cases h : (pSpecFinal ι F).dir i <;> simp [h])
  have h2 : Fintype.card {i : Fin 2 // (pSpecFinal ι F).dir i = .P_to_V} = 1 := by
    rw [← pSpecFinal_card_messageIdx (ι := ι) (F := F)]
  rw [h1, Fintype.card_subtype_compl, h2, Fintype.card_fin]

/-- **The final block prover**: sends its oracle in the clear (the final low-degree word) and
receives the repetition challenge, which becomes the output statement together with the
incoming pending randomness. -/
def stirFinalProver :
    OracleProver []ₒ F (OStmt ι F) Unit (F × F) (OStmt ι F) Unit (pSpecFinal ι F) where
  PrvState
  | 0 => (F × (∀ i, OStmt ι F i)) × Unit
  | 1 => (F × (ι → F))
  | _ => (F × (ι → F)) × F
  input := id
  sendMessage
  | ⟨0, _⟩ => fun st => pure ⟨st.1.2 (), (st.1.1, st.1.2 ())⟩
  | ⟨1, h⟩ => nomatch h
  receiveChallenge
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => fun st => pure (fun (rFin : F) => ⟨st, rFin⟩)
  output := fun st => pure ⟨⟨(st.1.1, st.2), fun _ => st.1.2⟩, ()⟩

/-- **The final block verifier**: outputs (pending randomness, repetition challenge) and
exposes the in-the-clear final message as the output oracle. -/
def stirFinalVerifier :
    OracleVerifier []ₒ F (OStmt ι F) (F × F) (OStmt ι F) (pSpecFinal ι F) where
  verify := fun r chals => pure (r, chals ⟨1, pSpecFinal_dir_one⟩)
  embed := ⟨fun _ => Sum.inr ⟨0, pSpecFinal_dir_zero⟩, fun _ _ _ => rfl⟩
  hEq := by
    intro i
    show (ι → F) = (pSpecFinal ι F).Message ⟨0, pSpecFinal_dir_zero⟩
    unfold pSpecFinal ProtocolSpec.Message
    simp

/-- **The final `[p, C_fin]` block** of the stirVSpec layout. -/
def stirFinalReduction :
    OracleReduction []ₒ F (OStmt ι F) Unit (F × F) (OStmt ι F) Unit (pSpecFinal ι F) where
  prover := stirFinalProver
  verifier := stirFinalVerifier

instance instStirFinalVerifierAppendCoherent :
    OracleVerifier.Append.AppendCoherent (stirFinalVerifier (ι := ι) (F := F)) where
  hCohInl := fun i k h => by
    exact absurd h (by simp [stirFinalVerifier])
  hCohInr := fun i k h => by
    have hk : k = ⟨0, pSpecFinal_dir_zero⟩ := by
      have := h.symm
      simp only [stirFinalVerifier, Function.Embedding.coeFn_mk] at this
      exact (Sum.inr.inj this)
    subst hk
    apply eq_of_heq
    refine HEq.trans ?_ (cast_heq _ _).symm
    rfl

end Round3

end StirIOP

#print axioms StirIOP.Round3.instStirRound3VerifierAppendCoherent
#print axioms StirIOP.Round3.stirInitReduction
#print axioms StirIOP.Round3.instStirInitVerifierAppendCoherent
#print axioms StirIOP.Round3.stirFinalReduction
#print axioms StirIOP.Round3.instStirFinalVerifierAppendCoherent
#print axioms StirIOP.Round3.pSpecInit_card_challengeIdx
#print axioms StirIOP.Round3.pSpecFinal_card_challengeIdx
