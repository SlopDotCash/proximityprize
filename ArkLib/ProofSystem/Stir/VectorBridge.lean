/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Stir.Round3Compose
import ArkLib.ProofSystem.Stir.RoundVector
import ArkLib.ProofSystem.Stir.MultiRoundSpec

/-!
# The vectorised stirVSpec blocks: the wire-format bridge (#301)

`stir_main` / `stir_rbr_soundness` (Stir/MainThm.lean) quantify over `VectorIOP` objects —
protocols over `(vPSpec : VectorSpec n).toProtocolSpec F`, where every payload is a
`Vector F len`.  The function-payload chain blocks live in `Round3Block.lean` /
`Round3Compose.lean` / `FullChain.lean`; this file vectorises them, block by block, following
the `RoundVector.lean` template (packed payloads via
`WhirIOP.Construction.packFiniteFunction`, challenges read off `Vector F 1` payloads):

* `stirRound3VSpec` + `stirRound3VectorReduction` — the vectorised 3-slot per-round block
  `[P g, C_out, C_shift]` with uniform statement threading `F → F` (the output statement is
  the shift challenge, the next block's pending fold randomness);
* `stirInitVSpec` + `stirInitVectorReduction` — the vectorised initial `[C_fold]` block;
* `stirFinalVSpec` + `stirFinalVectorReduction` — the vectorised final `[p, C_fin]` block;
* round-trip and relation-transfer lemmas for each (the facts the vector-level completeness
  proofs consume), and `AppendCoherent` instances for the vectorised verifiers.
-/

namespace StirIOP

namespace Round3

open OracleSpec OracleComp ProtocolSpec STIR ReedSolomon NNReal StirIOP.Round
-- Selective open: `WhirIOP.Construction` also declares an `OStmt`, which would clash with
-- `StirIOP.Round.OStmt`.
open WhirIOP.Construction (packFiniteFunction unpackFiniteFunction unpack_packFiniteFunction)

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The vectorised 3-slot block `[P g, C_out, C_shift]` -/

/-- **The vector spec of the 3-slot STIR round block**: the prover sends the folded oracle as a
length-`|ι|` vector, then the verifier sends the out-of-domain sample challenge and the
shift/next-fold challenge as length-`1` vectors. This is the `VectorSpec` counterpart of
`Round3.pSpec3` — the per-round shape of the `stirVSpec` layout
`[C_fold, (g_j, C_out, C_shift)×M, p, C_fin]`. -/
@[reducible]
def stirRound3VSpec (ι F : Type) [Fintype ι] : ProtocolSpec.VectorSpec 3 :=
  ⟨!v[.P_to_V, .V_to_P, .V_to_P], !v[Fintype.card ι, 1, 1]⟩

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] [DecidableEq ι] in
theorem stirRound3VSpec_dir_zero :
    ((stirRound3VSpec ι F).toProtocolSpec F).dir 0 = .P_to_V := rfl

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] [DecidableEq ι] in
theorem stirRound3VSpec_dir_one :
    ((stirRound3VSpec ι F).toProtocolSpec F).dir 1 = .V_to_P := rfl

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] [DecidableEq ι] in
theorem stirRound3VSpec_dir_two :
    ((stirRound3VSpec ι F).toProtocolSpec F).dir 2 = .V_to_P := rfl

/-- **The vectorised 3-slot block has exactly 1 prover message** (the budget arithmetic of the
`2M+2` count, now at the wire format). -/
theorem stirRound3VSpec_card_messageIdx :
    Fintype.card (((stirRound3VSpec ι F).toProtocolSpec F).MessageIdx) = 1 := by
  rw [Fintype.card_eq_one_iff]
  refine ⟨⟨0, stirRound3VSpec_dir_zero⟩, ?_⟩
  rintro ⟨⟨iv, hlt⟩, hi⟩
  have h0 : iv = 0 := by
    by_contra hne
    interval_cases iv
    · exact hne rfl
    · rw [show (⟨1, hlt⟩ : Fin 3) = (1 : Fin 3) from rfl, stirRound3VSpec_dir_one] at hi
      exact Direction.noConfusion hi
    · rw [show (⟨2, hlt⟩ : Fin 3) = (2 : Fin 3) from rfl, stirRound3VSpec_dir_two] at hi
      exact Direction.noConfusion hi
  subst h0
  rfl

set_option linter.unusedSimpArgs false in
/-- **The vectorised 3-slot block has exactly 2 verifier challenges** (out-sample + shift). -/
theorem stirRound3VSpec_card_challengeIdx :
    Fintype.card (((stirRound3VSpec ι F).toProtocolSpec F).ChallengeIdx) = 2 := by
  have h1 : Fintype.card (((stirRound3VSpec ι F).toProtocolSpec F).ChallengeIdx)
      = Fintype.card {i : Fin 3 // ¬ (((stirRound3VSpec ι F).toProtocolSpec F).dir i
          = .P_to_V)} :=
    Fintype.card_congr (Equiv.subtypeEquivRight fun i => by
      cases h : ((stirRound3VSpec ι F).toProtocolSpec F).dir i <;> simp [h])
  have h2 : Fintype.card {i : Fin 3 // ((stirRound3VSpec ι F).toProtocolSpec F).dir i
      = .P_to_V} = 1 := by
    rw [← stirRound3VSpec_card_messageIdx (ι := ι) (F := F)]
  rw [h1, Fintype.card_subtype_compl, h2, Fintype.card_fin]

/-- **The vectorised 3-slot STIR round-block prover** (uniform statement threading `F → F`).
Identical honest behaviour to `Round3.stirRound3Prover'` — fold the incoming oracle at the
pending randomness carried in the statement, emit the out/shift challenges' shift component as
the output statement — but speaking the vector-payload wire format: the folded oracle is sent
packed via `packFiniteFunction`, and the two challenges arrive as `Vector F 1` payloads (read
off via `·.get 0`). -/
noncomputable def stirRound3VectorProver (φ : ι ↪ F) (deg : ℕ) :
    OracleProver []ₒ F (OStmt ι F) Unit F (VOStmt ι F) Unit
      ((stirRound3VSpec ι F).toProtocolSpec F) where
  PrvState
  | 0 => (F × (∀ i, OStmt ι F i)) × Unit
  | 1 => Vector F (Fintype.card ι)
  | 2 => Vector F (Fintype.card ι) × F
  | _ => (Vector F (Fintype.card ι) × F) × F

  input := id

  sendMessage
  | ⟨0, _⟩ => fun st =>
      let f : ι → F := st.1.2 ()
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

/-- **The vectorised 3-slot STIR round-block oracle verifier**: outputs the shift challenge
(read off its `Vector F 1` payload) as the output statement and exposes the prover's packed
folded message (slot 0) as the output oracle. -/
def stirRound3VectorVerifier (φ : ι ↪ F) (deg : ℕ) :
    OracleVerifier []ₒ F (OStmt ι F) F (VOStmt ι F)
      ((stirRound3VSpec ι F).toProtocolSpec F) where
  verify := fun _ chals =>
    let rShift : Vector F 1 := chals ⟨2, stirRound3VSpec_dir_two⟩
    pure (rShift.get 0)
  embed := ⟨fun _ => Sum.inr ⟨0, stirRound3VSpec_dir_zero⟩, fun _ _ _ => rfl⟩
  hEq := fun _ => rfl

/-- **The vectorised 3-slot STIR round-block oracle reduction** — the per-round block of the
`stirVSpec` layout at the vector wire format quantified over by `stir_main` /
`stir_rbr_soundness`. -/
noncomputable def stirRound3VectorReduction (φ : ι ↪ F) (deg : ℕ) :
    OracleReduction []ₒ F (OStmt ι F) Unit F (VOStmt ι F) Unit
      ((stirRound3VSpec ι F).toProtocolSpec F) where
  prover := stirRound3VectorProver φ deg
  verifier := stirRound3VectorVerifier φ deg

/-! ## The vectorised initial `[C_fold]` block -/

/-- **The vector spec of the initial block**: a single length-`1` verifier challenge (the
standalone fold challenge `C_fold`). -/
@[reducible]
def stirInitVSpec : ProtocolSpec.VectorSpec 1 := ⟨!v[.V_to_P], !v[1]⟩

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] in
theorem stirInitVSpec_dir_zero :
    ((stirInitVSpec).toProtocolSpec F).dir 0 = .V_to_P := rfl

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] in
theorem stirInitVSpec_card_messageIdx :
    Fintype.card (((stirInitVSpec).toProtocolSpec F).MessageIdx) = 0 := by
  rw [Fintype.card_eq_zero_iff]
  refine ⟨fun ⟨⟨iv, hlt⟩, hi⟩ => ?_⟩
  have h0 : iv = 0 := by omega
  subst h0
  exact Direction.noConfusion hi

set_option linter.unusedSimpArgs false in
theorem stirInitVSpec_card_challengeIdx :
    Fintype.card (((stirInitVSpec).toProtocolSpec F).ChallengeIdx) = 1 := by
  have h1 : Fintype.card (((stirInitVSpec).toProtocolSpec F).ChallengeIdx)
      = Fintype.card {i : Fin 1 // ¬ (((stirInitVSpec).toProtocolSpec F).dir i = .P_to_V)} :=
    Fintype.card_congr (Equiv.subtypeEquivRight fun i => by
      cases h : ((stirInitVSpec).toProtocolSpec F).dir i <;> simp [h])
  have h2 : Fintype.card {i : Fin 1 // ((stirInitVSpec).toProtocolSpec F).dir i
      = .P_to_V} = 0 := by
    rw [← stirInitVSpec_card_messageIdx (F := F)]
  rw [h1, Fintype.card_subtype_compl, h2, Fintype.card_fin]

/-- **The vectorised initial block prover**: receives the standalone fold challenge `C_fold`
as a `Vector F 1` payload (read off via `·.get 0`) and outputs it as the statement (the
pending randomness for the first 3-slot block); the oracle is forwarded unchanged. -/
def stirInitVectorProver :
    OracleProver []ₒ Unit (OStmt ι F) Unit F (OStmt ι F) Unit
      ((stirInitVSpec).toProtocolSpec F) where
  PrvState
  | 0 => (Unit × (∀ i, OStmt ι F i)) × Unit
  | _ => ((Unit × (∀ i, OStmt ι F i)) × Unit) × F
  input := id
  sendMessage
  | ⟨0, h⟩ => nomatch h
  receiveChallenge
  | ⟨0, _⟩ => fun st => pure (fun (r : Vector F 1) => ⟨st, r.get 0⟩)
  output := fun st => pure ⟨⟨st.2, st.1.1.2⟩, ()⟩

/-- **The vectorised initial block verifier**: outputs the fold challenge (read off its
`Vector F 1` payload) as the statement and forwards the input oracle. -/
def stirInitVectorVerifier :
    OracleVerifier []ₒ Unit (OStmt ι F) F (OStmt ι F)
      ((stirInitVSpec).toProtocolSpec F) where
  verify := fun _ chals =>
    let r : Vector F 1 := chals ⟨0, stirInitVSpec_dir_zero⟩
    pure (r.get 0)
  embed := ⟨fun _ => Sum.inl (), fun _ _ _ => rfl⟩
  hEq := fun _ => rfl

/-- **The vectorised initial `[C_fold]` block** of the `stirVSpec` layout. -/
def stirInitVectorReduction :
    OracleReduction []ₒ Unit (OStmt ι F) Unit F (OStmt ι F) Unit
      ((stirInitVSpec).toProtocolSpec F) where
  prover := stirInitVectorProver
  verifier := stirInitVectorVerifier

/-! ## The vectorised final `[p, C_fin]` block -/

/-- **The vector spec of the final block**: the in-the-clear final message as a length-`|ι|`
vector, then the length-`1` repetition challenge `C_fin`. -/
@[reducible]
def stirFinalVSpec (ι F : Type) [Fintype ι] : ProtocolSpec.VectorSpec 2 :=
  ⟨!v[.P_to_V, .V_to_P], !v[Fintype.card ι, 1]⟩

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] [DecidableEq ι] in
theorem stirFinalVSpec_dir_zero :
    ((stirFinalVSpec ι F).toProtocolSpec F).dir 0 = .P_to_V := rfl

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] [DecidableEq ι] in
theorem stirFinalVSpec_dir_one :
    ((stirFinalVSpec ι F).toProtocolSpec F).dir 1 = .V_to_P := rfl

theorem stirFinalVSpec_card_messageIdx :
    Fintype.card (((stirFinalVSpec ι F).toProtocolSpec F).MessageIdx) = 1 := by
  rw [Fintype.card_eq_one_iff]
  refine ⟨⟨0, stirFinalVSpec_dir_zero⟩, ?_⟩
  rintro ⟨⟨iv, hlt⟩, hi⟩
  have h0 : iv = 0 := by
    by_contra hne
    have h1 : (⟨iv, hlt⟩ : Fin 2) = (1 : Fin 2) := by
      apply Fin.ext; simp only [Fin.val_one]; omega
    rw [h1, stirFinalVSpec_dir_one] at hi
    exact Direction.noConfusion hi
  subst h0
  rfl

set_option linter.unusedSimpArgs false in
theorem stirFinalVSpec_card_challengeIdx :
    Fintype.card (((stirFinalVSpec ι F).toProtocolSpec F).ChallengeIdx) = 1 := by
  have h1 : Fintype.card (((stirFinalVSpec ι F).toProtocolSpec F).ChallengeIdx)
      = Fintype.card {i : Fin 2 // ¬ (((stirFinalVSpec ι F).toProtocolSpec F).dir i
          = .P_to_V)} :=
    Fintype.card_congr (Equiv.subtypeEquivRight fun i => by
      cases h : ((stirFinalVSpec ι F).toProtocolSpec F).dir i <;> simp [h])
  have h2 : Fintype.card {i : Fin 2 // ((stirFinalVSpec ι F).toProtocolSpec F).dir i
      = .P_to_V} = 1 := by
    rw [← stirFinalVSpec_card_messageIdx (ι := ι) (F := F)]
  rw [h1, Fintype.card_subtype_compl, h2, Fintype.card_fin]

/-- **The vectorised final block prover**: sends its oracle in the clear, packed as a
length-`|ι|` vector via `packFiniteFunction`, and receives the repetition challenge as a
`Vector F 1` payload; the output statement is `(pending randomness, repetition challenge)`
and the output oracle is the packed in-the-clear word. -/
noncomputable def stirFinalVectorProver :
    OracleProver []ₒ F (OStmt ι F) Unit (F × F) (VOStmt ι F) Unit
      ((stirFinalVSpec ι F).toProtocolSpec F) where
  PrvState
  | 0 => (F × (∀ i, OStmt ι F i)) × Unit
  | 1 => F × Vector F (Fintype.card ι)
  | _ => (F × Vector F (Fintype.card ι)) × F
  input := id
  sendMessage
  | ⟨0, _⟩ => fun st =>
      let v := packFiniteFunction ι (st.1.2 ())
      pure ⟨v, (st.1.1, v)⟩
  | ⟨1, h⟩ => nomatch h
  receiveChallenge
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => fun st => pure (fun (rFin : Vector F 1) => ⟨st, rFin.get 0⟩)
  output := fun st => pure ⟨⟨(st.1.1, st.2), fun _ => st.1.2⟩, ()⟩

/-- **The vectorised final block verifier**: outputs `(pending randomness, repetition
challenge)` (the challenge read off its `Vector F 1` payload) and exposes the packed
in-the-clear final message as the output oracle. -/
def stirFinalVectorVerifier :
    OracleVerifier []ₒ F (OStmt ι F) (F × F) (VOStmt ι F)
      ((stirFinalVSpec ι F).toProtocolSpec F) where
  verify := fun r chals =>
    let rFin : Vector F 1 := chals ⟨1, stirFinalVSpec_dir_one⟩
    pure (r, rFin.get 0)
  embed := ⟨fun _ => Sum.inr ⟨0, stirFinalVSpec_dir_zero⟩, fun _ _ _ => rfl⟩
  hEq := fun _ => rfl

/-- **The vectorised final `[p, C_fin]` block** of the `stirVSpec` layout. -/
noncomputable def stirFinalVectorReduction :
    OracleReduction []ₒ F (OStmt ι F) Unit (F × F) (VOStmt ι F) Unit
      ((stirFinalVSpec ι F).toProtocolSpec F) where
  prover := stirFinalVectorProver
  verifier := stirFinalVectorVerifier

/-! ## Round-trip and relation-transfer lemmas -/

section Security

variable [Nonempty ι]

omit [Nonempty ι] in
/-- **Round-trip honesty of the vectorised 3-slot block's message**: unpacking the wire payload
recovers exactly the genuine `Combine.combine` fold; with `combine_single_self` this is
literally the input oracle on the honest run — the transfer fact the vector-level completeness
proof consumes. -/
theorem unpack_stirRound3Vector_message (φ : ι ↪ F) (deg : ℕ) (r : F) (f : ι → F) :
    unpackFiniteFunction ι
        (packFiniteFunction ι
          (Combine.combine φ deg r (fun _ : Fin 1 => f) (fun _ : Fin 1 => deg)))
      = f := by
  rw [unpack_packFiniteFunction, combine_single_self]

/-- Output relation for the vectorised 3-slot block: the *unpacked* folded oracle is `δ`-close
to the Reed-Solomon code (the vector-payload mirror of the function-level block relations; the
output statement is the pending shift challenge). -/
noncomputable def stirRound3VectorOutputRel (φ : ι ↪ F) (deg : ℕ) (δ : ℝ≥0) :
    Set ((F × ∀ i, VOStmt ι F i) × Unit) :=
  fun ⟨⟨_, oracle⟩, _⟩ =>
    Code.relDistFromCode (unpackFiniteFunction ι (oracle ())) (ReedSolomon.code φ deg)
      ≤ (δ : ENNReal)

/-- Membership transfer for the vectorised 3-slot block, stated in the tuple form the
completeness legs consume: the honest packed fold output satisfies the vector output relation
whenever the input oracle satisfies the function-level input relation. -/
theorem stirRound3VectorOutputRel_of_inputRel (φ : ι ↪ F) (deg : ℕ) (δ : ℝ≥0)
    {f : ι → F} (r rShift : F)
    (h : Code.relDistFromCode f (ReedSolomon.code φ deg) ≤ (δ : ENNReal)) :
    ((rShift, fun _ : Unit => packFiniteFunction ι
        (Combine.combine φ deg r (fun _ : Fin 1 => f) (fun _ : Fin 1 => deg))), ())
      ∈ stirRound3VectorOutputRel φ deg δ := by
  show Code.relDistFromCode
      (unpackFiniteFunction ι (packFiniteFunction ι
        (Combine.combine φ deg r (fun _ : Fin 1 => f) (fun _ : Fin 1 => deg))))
      (ReedSolomon.code φ deg) ≤ (δ : ENNReal)
  rw [unpack_stirRound3Vector_message]
  exact h

/-- Output relation for the vectorised initial block: the (unchanged, still function-payload)
forwarded oracle is `δ`-close to the Reed-Solomon code; the statement is the fold challenge. -/
noncomputable def stirInitVectorOutputRel (φ : ι ↪ F) (deg : ℕ) (δ : ℝ≥0) :
    Set ((F × ∀ i, OStmt ι F i) × Unit) :=
  fun ⟨⟨_, oracle⟩, _⟩ =>
    Code.relDistFromCode (oracle ()) (ReedSolomon.code φ deg) ≤ (δ : ENNReal)

omit [Fintype F] [SampleableType F] [DecidableEq ι] [Nonempty ι] in
/-- Membership transfer for the vectorised initial block (the oracle is forwarded unchanged,
so no packing round-trip is involved), in tuple form. -/
theorem stirInitVectorOutputRel_of_inputRel (φ : ι ↪ F) (deg : ℕ) (δ : ℝ≥0)
    {f : ι → F} (r : F)
    (h : Code.relDistFromCode f (ReedSolomon.code φ deg) ≤ (δ : ENNReal)) :
    ((r, fun _ : Unit => f), ()) ∈ stirInitVectorOutputRel φ deg δ :=
  h

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] [DecidableEq ι] [Nonempty ι] in
/-- **Round-trip honesty of the vectorised final block's message**: unpacking the packed
in-the-clear word recovers it exactly. -/
theorem unpack_stirFinalVector_message (f : ι → F) :
    unpackFiniteFunction ι (packFiniteFunction ι f) = f :=
  unpack_packFiniteFunction ι f

/-- Output relation for the vectorised final block: the *unpacked* in-the-clear word is
`δ`-close to the Reed-Solomon code; the statement is the final
`(pending randomness, repetition challenge)` pair. -/
noncomputable def stirFinalVectorOutputRel (φ : ι ↪ F) (deg : ℕ) (δ : ℝ≥0) :
    Set (((F × F) × ∀ i, VOStmt ι F i) × Unit) :=
  fun ⟨⟨_, oracle⟩, _⟩ =>
    Code.relDistFromCode (unpackFiniteFunction ι (oracle ())) (ReedSolomon.code φ deg)
      ≤ (δ : ENNReal)

omit [Fintype F] [SampleableType F] [DecidableEq ι] [Nonempty ι] in
/-- Membership transfer for the vectorised final block, in tuple form: the honest packed
in-the-clear word satisfies the vector output relation whenever the input oracle satisfies the
function-level input relation. -/
theorem stirFinalVectorOutputRel_of_inputRel (φ : ι ↪ F) (deg : ℕ) (δ : ℝ≥0)
    {f : ι → F} (r rFin : F)
    (h : Code.relDistFromCode f (ReedSolomon.code φ deg) ≤ (δ : ENNReal)) :
    (((r, rFin), fun _ : Unit => packFiniteFunction ι f), ())
      ∈ stirFinalVectorOutputRel φ deg δ := by
  show Code.relDistFromCode (unpackFiniteFunction ι (packFiniteFunction ι f))
      (ReedSolomon.code φ deg) ≤ (δ : ENNReal)
  rw [unpack_packFiniteFunction]
  exact h

end Security

/-! ## `AppendCoherent` instances for the vectorised verifiers (the `Round3Compose` shapes) -/

instance instStirRound3VectorVerifierAppendCoherent (φ : ι ↪ F) (deg : ℕ) :
    OracleVerifier.Append.AppendCoherent (stirRound3VectorVerifier φ deg) where
  hCohInl := fun i k h => by
    exact absurd h (by simp [stirRound3VectorVerifier])
  hCohInr := fun i k h => by
    have hk : k = ⟨0, stirRound3VSpec_dir_zero⟩ := by
      have := h.symm
      simp only [stirRound3VectorVerifier, Function.Embedding.coeFn_mk] at this
      exact (Sum.inr.inj this)
    subst hk
    apply eq_of_heq
    refine HEq.trans ?_ (cast_heq _ _).symm
    rfl

instance instStirRound3VectorReductionAppendCoherent (φ : ι ↪ F) (deg : ℕ) :
    OracleVerifier.Append.AppendCoherent (stirRound3VectorReduction φ deg).verifier :=
  instStirRound3VectorVerifierAppendCoherent φ deg

instance instStirInitVectorVerifierAppendCoherent :
    OracleVerifier.Append.AppendCoherent (stirInitVectorVerifier (ι := ι) (F := F)) where
  hCohInl := fun i k h => by
    have hk : k = () := rfl
    subst hk
    apply eq_of_heq
    refine HEq.trans ?_ (cast_heq _ _).symm
    rfl
  hCohInr := fun i k h => by
    exact absurd h (by simp [stirInitVectorVerifier])

instance instStirInitVectorReductionAppendCoherent :
    OracleVerifier.Append.AppendCoherent (stirInitVectorReduction (ι := ι) (F := F)).verifier :=
  instStirInitVectorVerifierAppendCoherent

instance instStirFinalVectorVerifierAppendCoherent :
    OracleVerifier.Append.AppendCoherent (stirFinalVectorVerifier (ι := ι) (F := F)) where
  hCohInl := fun i k h => by
    exact absurd h (by simp [stirFinalVectorVerifier])
  hCohInr := fun i k h => by
    have hk : k = ⟨0, stirFinalVSpec_dir_zero⟩ := by
      have := h.symm
      simp only [stirFinalVectorVerifier, Function.Embedding.coeFn_mk] at this
      exact (Sum.inr.inj this)
    subst hk
    apply eq_of_heq
    refine HEq.trans ?_ (cast_heq _ _).symm
    rfl

instance instStirFinalVectorReductionAppendCoherent :
    OracleVerifier.Append.AppendCoherent
      (stirFinalVectorReduction (ι := ι) (F := F)).verifier :=
  instStirFinalVectorVerifierAppendCoherent

end Round3

end StirIOP

/-! ### Axiom audit (#301 stirVSpec wire-format bridge) -/

#print axioms StirIOP.Round3.stirRound3VectorReduction
#print axioms StirIOP.Round3.stirRound3VSpec_card_messageIdx
#print axioms StirIOP.Round3.stirRound3VSpec_card_challengeIdx
#print axioms StirIOP.Round3.stirInitVectorReduction
#print axioms StirIOP.Round3.stirInitVSpec_card_messageIdx
#print axioms StirIOP.Round3.stirInitVSpec_card_challengeIdx
#print axioms StirIOP.Round3.stirFinalVectorReduction
#print axioms StirIOP.Round3.stirFinalVSpec_card_messageIdx
#print axioms StirIOP.Round3.stirFinalVSpec_card_challengeIdx
#print axioms StirIOP.Round3.unpack_stirRound3Vector_message
#print axioms StirIOP.Round3.stirRound3VectorOutputRel_of_inputRel
#print axioms StirIOP.Round3.stirInitVectorOutputRel_of_inputRel
#print axioms StirIOP.Round3.unpack_stirFinalVector_message
#print axioms StirIOP.Round3.stirFinalVectorOutputRel_of_inputRel
#print axioms StirIOP.Round3.instStirRound3VectorVerifierAppendCoherent
#print axioms StirIOP.Round3.instStirInitVectorVerifierAppendCoherent
#print axioms StirIOP.Round3.instStirFinalVectorVerifierAppendCoherent
