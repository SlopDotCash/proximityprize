/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Stir.RoundVector
import ArkLib.OracleReduction.Composition.Sequential.General

/-!
# The multi-round STIR fold protocol object (#301)

`RoundProtocol.lean` delivers a single, sorry-free STIR fold-round `OracleReduction`
(`stirRoundReduction`) and flags the `M+1`-round protocol as future work.  This file performs
the composition, following exactly the FRI idiom (`Fri/Spec/General.lean`: `seqCompose` of the
fold rounds, then `append` the terminal phase):

* `instStirRoundVerifierAppendCoherent`: the fold-round verifier satisfies the coherence side
  condition `OracleVerifier.Append.AppendCoherent` required by sequential composition (its
  `embed` routes the unique output oracle to the prover's combine message, and the registered
  `OracleInterface` instances agree definitionally).
* `stirMultiRoundReduction`: **the `M+1`-round STIR fold protocol object**, the
  `OracleReduction.seqCompose` of `M+1` copies of `stirRoundReduction`.
* `stirMultiRound_card_challengeIdx` / `stirMultiRound_card_messageIdx`: the composed spec has
  exactly `M+1` challenges and `M+1` messages (the round-budget bookkeeping needed when matching
  the composite against `stirVSpec`-shaped wire formats; note `stir_rbr_soundness` demands
  `2M+2` challenges, so these counts *document* that the present 2-message fold block must be
  refined to a 3-message block before the literal `stir_rbr_soundness` spec can be witnessed).
* `instStirRoundVectorVerifierAppendCoherent`: the *vectorised* fold-round verifier
  (`RoundVector.lean`) is likewise `AppendCoherent`.
* `stirMultiRoundVectorReduction`: the multi-round composite `append`ed with the vectorised
  fold round, i.e. the full `M+2`-block STIR chain whose *final* oracle output is in the packed
  `Vector F |ι|` wire format quantified over by `stir_main` / `stir_rbr_soundness` — the bridge
  object from the function-form fold chain to the `VectorIOP` world.

All declarations are sorry-free and axiom-clean.
-/

open OracleSpec OracleComp ProtocolSpec

namespace StirIOP

namespace Round

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Coherence of the fold-round verifier -/

/-- The STIR fold-round verifier is `AppendCoherent`: its `embed` sends the unique output-oracle
index to the prover's combine message (`Sum.inr ⟨1, _⟩`), and the registered interfaces agree. -/
instance instStirRoundVerifierAppendCoherent (φ : ι ↪ F) (deg : ℕ) :
    OracleVerifier.Append.AppendCoherent (stirRoundVerifier φ deg) where
  hCohInl := fun i k h => by
    exact absurd h (by simp [stirRoundVerifier])
  hCohInr := fun i k h => by
    have hk : k = ⟨1, pSpec_dir_one⟩ := by
      have := h.symm
      simp only [stirRoundVerifier, Function.Embedding.coeFn_mk] at this
      exact (Sum.inr.inj this)
    subst hk
    apply eq_of_heq
    refine HEq.trans ?_ (cast_heq _ _).symm
    rfl

/-- The fold-round *reduction*'s verifier is definitionally `stirRoundVerifier`, so it inherits
`AppendCoherent` (used to `seqCompose` the fold rounds; mirrors FRI's
`instFoldOracleReductionAppendCoherent`). -/
instance instStirRoundReductionAppendCoherent (φ : ι ↪ F) (deg : ℕ) :
    OracleVerifier.Append.AppendCoherent (stirRoundReduction φ deg).verifier :=
  instStirRoundVerifierAppendCoherent φ deg

/-! ## The `M+1`-round composite -/

/-- **The `M+1`-round STIR fold protocol object**: `OracleReduction.seqCompose` of `M + 1`
copies of `stirRoundReduction` (constant context families), the multi-round protocol object
demanded by the `stir_main` / `stir_rbr_soundness` scaffolding.  Mirrors FRI's `reductionFold`
(`Fri/Spec/General.lean`).  The coherence family must be passed explicitly (`coh := …`):
instance search does not see through the `(fun _ => …) i` redex. -/
noncomputable def stirMultiRoundReduction (φ : ι ↪ F) (deg : ℕ) (M : ℕ) :
    OracleReduction []ₒ Unit (OStmt ι F) Unit Unit (OStmt ι F) Unit
      (ProtocolSpec.seqCompose (fun _ : Fin (M + 1) => pSpec ι F)) :=
  OracleReduction.seqCompose (fun _ => Unit) (fun _ => OStmt ι F) (fun _ => Unit)
    (fun _ => stirRoundReduction φ deg)
    (coh := fun _ => instStirRoundReductionAppendCoherent φ deg)

/-- The multi-round composite's verifier is again `AppendCoherent` (closure of coherence under
`seqCompose`), so the composite can itself be `append`ed onto a further phase.  Stated as an
instance on the *named* `stirMultiRoundReduction` (whose `def` is opaque to instance search). -/
instance instStirMultiRoundReductionAppendCoherent (φ : ι ↪ F) (deg : ℕ) (M : ℕ) :
    OracleVerifier.Append.AppendCoherent (stirMultiRoundReduction φ deg M).verifier :=
  OracleReduction.seqCompose_verifier_appendCoherent
    (fun _ => Unit) (fun _ => OStmt ι F) (fun _ => Unit)
    (fun _ => stirRoundReduction φ deg)
    (coh := fun _ => instStirRoundReductionAppendCoherent φ deg)

/-! ## Round-budget bookkeeping for the composed spec -/

/-- One STIR fold round has exactly one verifier challenge (the folding randomness). -/
theorem pSpec_card_challengeIdx :
    Fintype.card ((pSpec ι F).ChallengeIdx) = 1 := by
  rw [Fintype.card_eq_one_iff]
  refine ⟨⟨0, pSpec_dir_zero⟩, ?_⟩
  rintro ⟨⟨iv, hlt⟩, hi⟩
  have h0 : iv = 0 := by
    by_contra hne
    have h1 : (⟨iv, hlt⟩ : Fin 2) = (1 : Fin 2) := by
      apply Fin.ext
      simp only [Fin.val_one]
      omega
    rw [h1, pSpec_dir_one] at hi
    exact Direction.noConfusion hi
  subst h0
  rfl

/-- One STIR fold round has exactly one prover message (the combined/folded oracle). -/
theorem pSpec_card_messageIdx :
    Fintype.card ((pSpec ι F).MessageIdx) = 1 := by
  rw [Fintype.card_eq_one_iff]
  refine ⟨⟨1, pSpec_dir_one⟩, ?_⟩
  rintro ⟨⟨iv, hlt⟩, hi⟩
  have h1 : iv = 1 := by
    by_contra hne
    have h0 : (⟨iv, hlt⟩ : Fin 2) = (0 : Fin 2) := by
      apply Fin.ext
      simp only [Fin.val_zero]
      omega
    rw [h0, pSpec_dir_zero] at hi
    exact Direction.noConfusion hi
  subst h1
  rfl

/-- **Challenge budget of the `M+1`-round composite**: the `seqCompose`d fold spec has exactly
`M + 1` challenges (one folding challenge per round).  In particular the present 2-message
fold block can never witness the `card ChallengeIdx = 2M + 2` conjunct of `stir_rbr_soundness`
directly — a 3-message per-round block is required; this lemma pins that bookkeeping down. -/
theorem stirMultiRound_card_challengeIdx (M : ℕ) :
    Fintype.card (ProtocolSpec.seqCompose (fun _ : Fin (M + 1) => pSpec ι F)).ChallengeIdx
      = M + 1 := by
  rw [← Fintype.card_congr (ProtocolSpec.seqComposeChallengeEquiv
    (fun _ : Fin (M + 1) => pSpec ι F))]
  rw [Fintype.card_sigma]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [pSpec_card_challengeIdx, mul_one]

/-- **Message budget of the `M+1`-round composite**: exactly `M + 1` prover messages (one folded
oracle per round) — the count that must match the vector-spec message count when bridging to a
`VectorIOP` wire format. -/
theorem stirMultiRound_card_messageIdx (M : ℕ) :
    Fintype.card (ProtocolSpec.seqCompose (fun _ : Fin (M + 1) => pSpec ι F)).MessageIdx
      = M + 1 := by
  rw [← Fintype.card_congr (ProtocolSpec.seqComposeMessageEquiv
    (pSpec := fun _ : Fin (M + 1) => pSpec ι F))]
  rw [Fintype.card_sigma]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [pSpec_card_messageIdx, mul_one]

/-! ## The vectorised tail: bridging to the `VectorIOP` wire format -/

/-- The *vectorised* STIR fold-round verifier (`RoundVector.lean`) is `AppendCoherent`: its
`embed` routes the unique output oracle to the packed combine message, with definitionally
agreeing `OracleInterface.instVector` interfaces on both sides. -/
instance instStirRoundVectorVerifierAppendCoherent (φ : ι ↪ F) (deg : ℕ) :
    OracleVerifier.Append.AppendCoherent (stirRoundVectorVerifier φ deg) where
  hCohInl := fun i k h => by
    exact absurd h (by simp [stirRoundVectorVerifier])
  hCohInr := fun i k h => by
    have hk : k = ⟨1, stirRoundVSpec_dir_one⟩ := by
      have := h.symm
      simp only [stirRoundVectorVerifier, Function.Embedding.coeFn_mk] at this
      exact (Sum.inr.inj this)
    subst hk
    apply eq_of_heq
    refine HEq.trans ?_ (cast_heq _ _).symm
    rfl

/-- The vectorised fold-round *reduction*'s verifier is definitionally
`stirRoundVectorVerifier`, so it inherits `AppendCoherent`. -/
instance instStirRoundVectorReductionAppendCoherent (φ : ι ↪ F) (deg : ℕ) :
    OracleVerifier.Append.AppendCoherent (stirRoundVectorReduction φ deg).verifier :=
  instStirRoundVectorVerifierAppendCoherent φ deg

/-- `OracleInterface` instance for the messages of the bridge spec (fold composite `++ₚ`
vectorised round).  Registered by name, following the FRI idiom (`Fri/Spec/General.lean`):
instance search does not find the generic append instance at this compound head. -/
instance instStirBridgeMessageInterface (M : ℕ) : ∀ j, OracleInterface
    (((ProtocolSpec.seqCompose (fun _ : Fin (M + 1) => pSpec ι F)) ++ₚ
      ((stirRoundVSpec ι F).toProtocolSpec F)).Message j) :=
  instOracleInterfaceMessageAppend

/-- `OracleInterface` instance for the challenges of the bridge spec (mirrors FRI). -/
instance instStirBridgeChallengeInterface (M : ℕ) : ∀ j, OracleInterface
    (((ProtocolSpec.seqCompose (fun _ : Fin (M + 1) => pSpec ι F)) ++ₚ
      ((stirRoundVSpec ι F).toProtocolSpec F)).Challenge j) :=
  ProtocolSpec.challengeOracleInterface

/-- **The multi-round STIR chain ending in vector wire format**: the `M+1`-round fold composite
`append`ed with the vectorised fold round (`RoundVector.lean`), so the *final* output oracle is
the packed `Vector F |ι|` payload demanded by the `VectorIOP`-shaped statements of `stir_main` /
`stir_rbr_soundness`.  This is exactly FRI's `reductionFold`-then-`append`-final-phase idiom
(`Fri/Spec/General.lean:93`), realised for STIR. -/
noncomputable def stirMultiRoundVectorReduction (φ : ι ↪ F) (deg : ℕ) (M : ℕ) :
    OracleReduction []ₒ Unit (OStmt ι F) Unit Unit (VOStmt ι F) Unit
      ((ProtocolSpec.seqCompose (fun _ : Fin (M + 1) => pSpec ι F)) ++ₚ
        ((stirRoundVSpec ι F).toProtocolSpec F)) :=
  OracleReduction.append (stirMultiRoundReduction φ deg M) (stirRoundVectorReduction φ deg)

end Round

end StirIOP

/-! ### Axiom audit -/

#print axioms StirIOP.Round.instStirRoundVerifierAppendCoherent
#print axioms StirIOP.Round.instStirRoundReductionAppendCoherent
#print axioms StirIOP.Round.stirMultiRoundReduction
#print axioms StirIOP.Round.instStirMultiRoundReductionAppendCoherent
#print axioms StirIOP.Round.pSpec_card_challengeIdx
#print axioms StirIOP.Round.pSpec_card_messageIdx
#print axioms StirIOP.Round.stirMultiRound_card_challengeIdx
#print axioms StirIOP.Round.stirMultiRound_card_messageIdx
#print axioms StirIOP.Round.instStirRoundVectorVerifierAppendCoherent
#print axioms StirIOP.Round.instStirRoundVectorReductionAppendCoherent
#print axioms StirIOP.Round.stirMultiRoundVectorReduction
