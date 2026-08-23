/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
import ArkLib.ProofSystem.RingSwitching.Prelude
import ArkLib.ProofSystem.Sumcheck.Structured.SingleRound

/-! ## Protocol Specs for Ring-Switching
This module contains the protocol specs, oracle index bounds,
instances of OracleInterface and SampleableType for the Ring Switching protocol.
-/

namespace RingSwitching

noncomputable section
open OracleSpec OracleComp ProtocolSpec Finset Polynomial MvPolynomial
open scoped NNReal
open Sumcheck.Structured

variable (κ : ℕ) [NeZero κ]
variable (L : Type) [CommRing L] [Fintype L] [DecidableEq L]
  [SampleableType L]
variable (K : Type) [CommRing K] [Fintype K] [DecidableEq K]
variable [Algebra K L]
variable (P : RingSwitchingProfile K L κ)
variable (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']
variable (h_l : ℓ = ℓ' + κ)
variable (mlIOPCS : MLIOPCS L ℓ')

section Pspec

@[reducible]
def pSpecBatching : ProtocolSpec 2 :=
  ⟨![Direction.P_to_V, Direction.V_to_P],
   ![P.A, Fin κ → L]⟩

-- `pSpecSumcheckRound` was lifted to `ArkLib.ProofSystem.Sumcheck.Structured.SingleRound` as a
-- degree-neutral spec. Binius ring-switching is the degree-2 case, so this Binius-local abbrev
-- pins `d := 2` — no instantiation is privileged by a default on the generic spec.
abbrev pSpecSumcheckRound (L : Type) [Semiring L] : ProtocolSpec 2 :=
  Sumcheck.Structured.pSpecSumcheckRound L 2

@[reducible]
def pSpecSumcheckLoop := ProtocolSpec.seqCompose (fun (_: Fin ℓ') => pSpecSumcheckRound L)

def pSpecFinalSumcheck : ProtocolSpec 1 := ⟨![Direction.P_to_V], ![L]⟩

@[reducible]
def pSpecCoreInteraction := (pSpecSumcheckLoop L ℓ') ++ₚ (pSpecFinalSumcheck L)

@[reducible]
def pSpecLargeFieldReduction :=
  (pSpecBatching κ L K P) ++ₚ (pSpecCoreInteraction (L:=L) (ℓ':=ℓ'))

@[reducible]
def fullPspec := (pSpecLargeFieldReduction κ (L:=L) (K:=K) P (ℓ':=ℓ')) ++ₚ (mlIOPCS.pSpec)

/-! ## Oracle Interface instances for Messages-/

instance : OracleInterface P.A := OracleInterface.instDefault
instance : OracleInterface (Fin κ → L) := OracleInterface.instDefault

instance : ∀ j, OracleInterface ((pSpecBatching κ L K P).Message j)
  | ⟨0, _⟩ => OracleInterface.instDefault -- ŝ ∈ A
  | ⟨1, _⟩ => OracleInterface.instDefault -- r'' ∈ L^κ

-- The `OracleInterface` instance for `pSpecSumcheckRound.Message` was lifted to
-- `ArkLib.ProofSystem.Sumcheck.Structured.SingleRound` along with the spec itself.
-- Anonymous instances are looked up globally regardless of namespace, so no shim is needed.

instance instOracleInterfaceChallengePSpecSumcheckRound :
    ∀ j, OracleInterface ((pSpecSumcheckRound (L:=L)).Challenge j) :=
  ProtocolSpec.challengeOracleInterface

instance : ∀ j, OracleInterface ((pSpecSumcheckLoop (L:=L) ℓ').Message j)
  := instOracleInterfaceMessageSeqCompose

instance : ∀ i, OracleInterface ((pSpecFinalSumcheck (L:=L)).Message i)
  | ⟨0, _⟩ => OracleInterface.instDefault -- final constant c

instance : ∀ i, OracleInterface ((pSpecCoreInteraction (L:=L) (ℓ':=ℓ')).Message i) :=
  instOracleInterfaceMessageAppend

instance : ∀ i, OracleInterface
    ((pSpecLargeFieldReduction κ (L:=L) (K:=K) P (ℓ':=ℓ')).Message i) :=
  instOracleInterfaceMessageAppend

instance : ∀ i, OracleInterface (mlIOPCS.pSpec.Message i) := fun i => mlIOPCS.Oₘ i

instance : ∀ i, OracleInterface ((fullPspec κ (L:=L) (K:=K) P (ℓ':=ℓ') mlIOPCS).Message i) :=
  instOracleInterfaceMessageAppend

/-! ## SampleableType instances -/

instance : ∀ j, SampleableType ((pSpecBatching κ L K P).Challenge j)
  | ⟨0, h0⟩ => by nomatch h0
  | ⟨1, _⟩ => by
    simp only [Challenge, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    exact instSampleableTypeFinFunc (α := L)

-- The `SampleableType` instance for `pSpecSumcheckRound.Challenge` was lifted to
-- `ArkLib.ProofSystem.Sumcheck.Structured.SingleRound`. Anonymous instances are looked up
-- globally, so no shim is needed.

instance : ∀ j, SampleableType ((pSpecSumcheckLoop (L:=L) ℓ').Challenge j)
  := instSampleableTypeChallengeSeqCompose

instance : ∀ i, SampleableType ((pSpecFinalSumcheck (L:=L)).Challenge i)
  | ⟨0, h0⟩ => by nomatch h0 -- P->V message has no challenge

instance : ∀ i, SampleableType ((pSpecCoreInteraction (L:=L) (ℓ':=ℓ')).Challenge i) :=
  instSampleableTypeChallengeAppend

instance : ∀ i, SampleableType
    ((pSpecLargeFieldReduction κ (L:=L) (K:=K) P (ℓ':=ℓ')).Challenge i) :=
  instSampleableTypeChallengeAppend

instance : ∀ i, SampleableType (mlIOPCS.pSpec.Challenge i) := mlIOPCS.O_challenges

instance : ∀ i, SampleableType ((fullPspec κ (L:=L) (K:=K) P (ℓ':=ℓ') mlIOPCS).Challenge i) :=
  instSampleableTypeChallengeAppend

/-! ## OracleSpec `Inhabited`/`Fintype` instances for completeness unrolling -/

instance instInhabitedOracleSpecEmpty : (([]ₒ : OracleSpec PEmpty).Inhabited) where
  inhabited_B i := nomatch i

instance instFintypeOracleSpecEmpty : (([]ₒ : OracleSpec PEmpty).Fintype) where
  fintype_B i := nomatch i

/-- Per-index finiteness of the sumcheck-round challenges (the challenge at index `1` is `L`;
index `0` is a `P_to_V` message). Feeds the n-ary `seqCompose`/append challenge instances. -/
instance instFintypeSumcheckRoundChallengeIdx :
    ∀ j, Fintype ((pSpecSumcheckRound (L:=L)).Challenge j) := fun j => by
  rcases j with ⟨⟨v, hv⟩, hj⟩
  interval_cases v
  · exact absurd hj (by simp [pSpecSumcheckRound, Sumcheck.Structured.pSpecSumcheckRound])
  · simpa only [pSpecSumcheckRound, Sumcheck.Structured.pSpecSumcheckRound,
      ProtocolSpec.Challenge, Matrix.cons_val_one, Matrix.cons_val_fin_one] using
      (inferInstance : Fintype L)

/-- Per-index inhabitedness of the sumcheck-round challenges. -/
instance instInhabitedSumcheckRoundChallengeIdx :
    ∀ j, Inhabited ((pSpecSumcheckRound (L:=L)).Challenge j) := fun j => by
  rcases j with ⟨⟨v, hv⟩, hj⟩
  interval_cases v
  · exact absurd hj (by simp [pSpecSumcheckRound, Sumcheck.Structured.pSpecSumcheckRound])
  · simpa only [pSpecSumcheckRound, Sumcheck.Structured.pSpecSumcheckRound,
      ProtocolSpec.Challenge, Matrix.cons_val_one, Matrix.cons_val_fin_one] using
      (⟨(0 : L)⟩ : Inhabited L)

/-- Per-index finiteness of the final-sumcheck challenges (vacuous: single `P_to_V` message). -/
instance instFintypeFinalSumcheckChallengeIdx :
    ∀ j, Fintype ((pSpecFinalSumcheck (L:=L)).Challenge j) := fun j => by
  rcases j with ⟨⟨v, hv⟩, hj⟩
  interval_cases v
  · exact absurd hj (by simp [pSpecFinalSumcheck])

/-- Per-index inhabitedness of the final-sumcheck challenges (vacuous). -/
instance instInhabitedFinalSumcheckChallengeIdx :
    ∀ j, Inhabited ((pSpecFinalSumcheck (L:=L)).Challenge j) := fun j => by
  rcases j with ⟨⟨v, hv⟩, hj⟩
  interval_cases v
  · exact absurd hj (by simp [pSpecFinalSumcheck])

/-- Per-index finiteness of the batching challenges (the challenge at index `1` is `Fin κ → L`). -/
instance instFintypeBatchingChallengeIdx :
    ∀ j, Fintype ((pSpecBatching κ L K P).Challenge j) := fun j => by
  rcases j with ⟨⟨v, hv⟩, hj⟩
  interval_cases v
  · exact absurd hj (by simp [pSpecBatching])
  · simpa only [pSpecBatching, ProtocolSpec.Challenge, Matrix.cons_val_one,
      Matrix.cons_val_fin_one] using (inferInstance : Fintype (Fin κ → L))

/-- Per-index inhabitedness of the batching challenges. -/
instance instInhabitedBatchingChallengeIdx :
    ∀ j, Inhabited ((pSpecBatching κ L K P).Challenge j) := fun j => by
  rcases j with ⟨⟨v, hv⟩, hj⟩
  interval_cases v
  · exact absurd hj (by simp [pSpecBatching])
  · simpa only [pSpecBatching, ProtocolSpec.Challenge, Matrix.cons_val_one,
      Matrix.cons_val_fin_one] using (⟨fun _ => (0 : L)⟩ : Inhabited (Fin κ → L))

instance instFintypePSpecSumcheckRoundChallenge :
    ([(pSpecSumcheckRound (L:=L)).Challenge]ₒ).Fintype := by
  refine { fintype_B := ?_ }
  intro x
  rcases x with ⟨⟨i, hi⟩, q⟩
  have h1 : i = 1 := by
    fin_cases i
    · simp [pSpecSumcheckRound] at hi
    · rfl
  subst h1
  cases q
  change Fintype L
  infer_instance

instance instInhabitedPSpecSumcheckRoundChallenge :
    ([(pSpecSumcheckRound (L:=L)).Challenge]ₒ).Inhabited := by
  refine { inhabited_B := ?_ }
  intro x
  rcases x with ⟨⟨i, hi⟩, q⟩
  have h1 : i = 1 := by
    fin_cases i
    · simp [pSpecSumcheckRound] at hi
    · rfl
  subst h1
  cases q
  change Inhabited L
  exact ⟨0⟩

/-- The (empty) challenge oracle of the final sumcheck step is finite: its single round is a
`P_to_V` message, so there is no challenge index and the query type is empty. Needed by the
1-message-round completeness `unroll`. -/
instance instFintypePSpecFinalSumcheckChallenge :
    ([(pSpecFinalSumcheck (L:=L)).Challenge]ₒ).Fintype := by
  refine { fintype_B := ?_ }
  rintro ⟨⟨i, hi⟩, q⟩
  exact absurd hi (by
    obtain rfl : i = 0 := by omega
    simp [pSpecFinalSumcheck])

instance instInhabitedPSpecFinalSumcheckChallenge :
    ([(pSpecFinalSumcheck (L:=L)).Challenge]ₒ).Inhabited := by
  refine { inhabited_B := ?_ }
  rintro ⟨⟨i, hi⟩, q⟩
  exact absurd hi (by
    obtain rfl : i = 0 := by omega
    simp [pSpecFinalSumcheck])

/-- The challenge oracle of the batching phase (round 1, type `Fin κ → L`). -/
instance instOracleInterfaceChallengePSpecBatching :
    ∀ j, OracleInterface ((pSpecBatching κ L K P).Challenge j) :=
  ProtocolSpec.challengeOracleInterface

/-- The batching challenge oracle is finite (its only query, round 1, returns `Fin κ → L`). Needed
by the 2-message-round completeness `unroll`, mirroring the sumcheck-round instance. -/
instance instFintypePSpecBatchingChallenge :
    ([(pSpecBatching κ L K P).Challenge]ₒ).Fintype := by
  refine { fintype_B := ?_ }
  intro x
  rcases x with ⟨⟨i, hi⟩, q⟩
  have h1 : i = 1 := by fin_cases i <;> first | rfl | (simp [pSpecBatching] at hi)
  subst h1
  cases q
  change Fintype (Fin κ → L)
  infer_instance

instance instInhabitedPSpecBatchingChallenge :
    ([(pSpecBatching κ L K P).Challenge]ₒ).Inhabited := by
  refine { inhabited_B := ?_ }
  intro x
  rcases x with ⟨⟨i, hi⟩, q⟩
  have h1 : i = 1 := by fin_cases i <;> first | rfl | (simp [pSpecBatching] at hi)
  subst h1
  cases q
  change Inhabited (Fin κ → L)
  exact ⟨fun _ => 0⟩

end Pspec

end
end RingSwitching

/-! ### Axiom audit (issue #19 sumcheck unroll instance plumbing) -/

#print axioms RingSwitching.instOracleInterfaceChallengePSpecSumcheckRound
#print axioms RingSwitching.instInhabitedOracleSpecEmpty
#print axioms RingSwitching.instFintypeOracleSpecEmpty
#print axioms RingSwitching.instFintypePSpecSumcheckRoundChallenge
#print axioms RingSwitching.instInhabitedPSpecSumcheckRoundChallenge
