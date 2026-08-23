/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Stir.RoundProtocol
import ArkLib.ToMathlib.WhirBricksConstruction

/-!
# The vectorised STIR fold round (#301)

The single-round protocol object lifted to
the `VectorSpec` world demanded by `stir_main` / `stir_rbr_soundness` (whose `∃ π` quantifies
over `VectorIOP`/vector-spec objects). `RoundProtocol.lean` flags this lift as future work
("As an IOP-shaped object (over the vectorised protocol spec) is future work"). Payloads are
packed with the canonical `WhirIOP.Construction.packFiniteFunction` bridge. -/

namespace StirIOP

namespace Round

open OracleSpec OracleComp ProtocolSpec STIR ReedSolomon NNReal WhirIOP.Construction

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The vector spec of one STIR fold round**: the verifier sends a length-`1` field-vector
challenge, then the prover sends the folded oracle as a length-`|ι|` vector. This is the
`VectorSpec` counterpart of `Round.pSpec`. -/
@[reducible]
def stirRoundVSpec (ι F : Type) [Fintype ι] : ProtocolSpec.VectorSpec 2 :=
  ⟨!v[.V_to_P, .P_to_V], !v[1, Fintype.card ι]⟩

theorem stirRoundVSpec_dir_zero :
    ((stirRoundVSpec ι F).toProtocolSpec F).dir 0 = .V_to_P := rfl

theorem stirRoundVSpec_dir_one :
    ((stirRoundVSpec ι F).toProtocolSpec F).dir 1 = .P_to_V := rfl

/-- The single-index *vector-shaped* oracle statement family: one packed oracle payload
`Vector F |ι|` (the vector form of `Round.OStmt`). -/
@[reducible]
def VOStmt (ι F : Type) [Fintype ι] : Unit → Type := fun _ => Vector F (Fintype.card ι)

instance : OracleInterface (VOStmt ι F ()) := OracleInterface.instVector

/-- **The vectorised STIR fold-round prover.** Identical honest behaviour to
`Round.stirRoundProver` — store the fold challenge, send the genuine `Combine.combine` of the
incoming oracle — but speaking the vector-payload wire format: the challenge arrives as a
`Vector F 1` (read off via `·.get 0`) and the folded oracle is sent packed via
`packFiniteFunction`. -/
noncomputable def stirRoundVectorProver (φ : ι ↪ F) (deg : ℕ) :
    OracleProver []ₒ Unit (OStmt ι F) Unit Unit (VOStmt ι F) Unit
      ((stirRoundVSpec ι F).toProtocolSpec F) where
  PrvState
  | 0 => (Unit × (∀ i, OStmt ι F i)) × Unit
  | _ => ((Unit × (∀ i, OStmt ι F i)) × Unit) × F

  input := id

  receiveChallenge
  | ⟨0, _⟩ => fun st => pure (fun (r : Vector F 1) => ⟨st, r.get 0⟩)
  | ⟨1, h⟩ => nomatch h

  sendMessage
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => fun st =>
      pure ⟨packFiniteFunction ι
        (Combine.combine φ deg st.2 (fun _ : Fin 1 => st.1.1.2 ()) (fun _ : Fin 1 => deg)), st⟩

  output := fun st => pure ⟨⟨(), fun _ => packFiniteFunction ι
      (Combine.combine φ deg st.2 (fun _ : Fin 1 => st.1.1.2 ()) (fun _ : Fin 1 => deg))⟩, ()⟩

/-- **The vectorised STIR fold-round oracle verifier**: forwards its statement and exposes, as
its output oracle, the prover's packed combine message (protocol index `1`). -/
def stirRoundVectorVerifier (φ : ι ↪ F) (deg : ℕ) :
    OracleVerifier []ₒ Unit (OStmt ι F) Unit (VOStmt ι F)
      ((stirRoundVSpec ι F).toProtocolSpec F) where
  verify := fun _ _ => pure ()
  embed := ⟨fun _ => Sum.inr ⟨1, stirRoundVSpec_dir_one⟩, fun _ _ _ => rfl⟩
  hEq := fun _ => rfl

/-- **The vectorised STIR fold-round oracle reduction** — the first STIR protocol object over a
`VectorSpec`, the wire format quantified over by `stir_main` / `stir_rbr_soundness`. -/
noncomputable def stirRoundVectorReduction (φ : ι ↪ F) (deg : ℕ) :
    OracleReduction []ₒ Unit (OStmt ι F) Unit Unit (VOStmt ι F) Unit
      ((stirRoundVSpec ι F).toProtocolSpec F) where
  prover := stirRoundVectorProver φ deg
  verifier := stirRoundVectorVerifier φ deg

section Security

variable [Nonempty ι]

/-- Output relation for the vectorised fold round: the *unpacked* folded oracle is `δ`-close to
the Reed-Solomon code (the vector-payload mirror of `stirRoundOutputRel`). -/
noncomputable def stirRoundVectorOutputRel (φ : ι ↪ F) (deg : ℕ) (δ : ℝ≥0) :
    Set ((Unit × ∀ i, VOStmt ι F i) × Unit) :=
  fun ⟨⟨_, oracle⟩, _⟩ =>
    Code.relDistFromCode (unpackFiniteFunction ι (oracle ())) (ReedSolomon.code φ deg)
      ≤ (δ : ENNReal)

/-- **Round-trip honesty of the vectorised prover's message**: unpacking the wire payload
recovers exactly the genuine `Combine.combine` fold. With `combine_single_self` this means the
unpacked output oracle is literally the input oracle on the honest run — the transfer fact the
vector-level completeness proof consumes. -/
theorem unpack_stirRoundVector_message (φ : ι ↪ F) (deg : ℕ) (r : F) (f : ι → F) :
    unpackFiniteFunction ι
        (packFiniteFunction ι
          (Combine.combine φ deg r (fun _ : Fin 1 => f) (fun _ : Fin 1 => deg)))
      = f := by
  rw [unpack_packFiniteFunction, combine_single_self]

/-- Membership transfer: the honest packed fold output satisfies the vector output relation
whenever the input oracle satisfies the (function-level) input relation. -/
theorem stirRoundVectorOutputRel_of_inputRel (φ : ι ↪ F) (deg : ℕ) (δ : ℝ≥0)
    {f : ι → F} (r : F)
    (h : Code.relDistFromCode f (ReedSolomon.code φ deg) ≤ (δ : ENNReal)) :
    (((), fun _ : Unit => packFiniteFunction ι
        (Combine.combine φ deg r (fun _ : Fin 1 => f) (fun _ : Fin 1 => deg))), ())
      ∈ stirRoundVectorOutputRel φ deg δ := by
  show Code.relDistFromCode
      (unpackFiniteFunction ι (packFiniteFunction ι
        (Combine.combine φ deg r (fun _ : Fin 1 => f) (fun _ : Fin 1 => deg))))
      (ReedSolomon.code φ deg) ≤ (δ : ENNReal)
  rw [unpack_stirRoundVector_message]
  exact h

end Security

end Round

end StirIOP

#print axioms StirIOP.Round.stirRoundVectorReduction
#print axioms StirIOP.Round.unpack_stirRoundVector_message
#print axioms StirIOP.Round.stirRoundVectorOutputRel_of_inputRel
