/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliza
-/

import ArkLib.OracleReduction.Basic
import ArkLib.OracleReduction.VectorIOR
import ArkLib.OracleReduction.Security.Basic
import ArkLib.OracleReduction.Security.RoundByRound
import ArkLib.Data.Polynomial.Interface
import ArkLib.ProofSystem.Whir.Folding
import ArkLib.ProofSystem.Whir.RBRSoundness
import ArkLib.ProofSystem.Whir.RbrBudgetAccounting

/-!
# WHIR VectorSpec challenge budget (scratch brick B)

Prior to this file, `ArkLib/ProofSystem/Whir/` contained only soundness *ingredients*
(folding lemmas, block-relative distance, MCA/Johnson machinery) and the statement-only
`whir_rbr_soundness` (`Whir/RBRSoundness.lean`), whose docstring records that the WHIR Vector
IOPP `π` (paper Construction 5.1) "is built nowhere in ArkLib yet, so the `∃ π` cannot be
introduced."

This file closes the first *protocol-spec bookkeeping* gap.  It builds a genuine, `sorry`-free
`VectorSpec` with exactly `2 * M + 2` verifier challenges — the challenge budget that
`whir_rbr_soundness` quantifies over — and no prover-message payload.  It does not yet construct
the WHIR `VectorIOP` object `π`; the honest fold/OOD messages, verifier, completeness, and
round-by-round soundness proof remain the larger #113 construction work.

## References

* [Arnon, G., Chiesa, A., Fenzi, G., and Yogev, E., *WHIR: Reed–Solomon Proximity Testing
    with Super-Fast Verification*][ACFY24], Construction 5.1.
-/

open OracleSpec OracleComp ProtocolSpec NNReal ReedSolomon

namespace WhirIOP

namespace Construction

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The single-index oracle statement family for the WHIR Vector IOPP: the prover holds one
  oracle function `f : ι → F` (the purported low-degree evaluation being proximity-tested). -/
@[reducible]
def OStmt (ι F : Type) : Unit → Type := fun _ => ι → F

instance : OracleInterface (OStmt ι F ()) := OracleInterface.instFunction

/-! ### Faithful paper transcript scaffold

Construction 5.1 has more transcript structure than the RBR error-budget skeleton below: an initial
sumcheck, per-transition folded-oracle/OOD/shift/sumcheck slots, and a final polynomial/randomness
check.  The inductive type here records that ordered paper schedule as finite data, so the eventual
honest prover can depend on earlier verifier challenges.  It is still syntax: the algebraic prover,
verifier checks, completeness, and RBR soundness are separate obligations.
-/

/-- The ordered high-level transcript slots of WHIR Construction 5.1.

For `i : Fin M`, `i.succ : Fin (M + 1)` denotes the transition round from the previous oracle to
the next folded oracle.  The `mainShiftChallenge` payload represents the batch of shift samples
plus the random linear-combination coefficient used in that transition round. -/
inductive PaperTranscriptSlot {M : ℕ} {ιs : Fin (M + 1) → Type} (P : Params ιs F) : Type
  | initialSumcheckMessage : Fin (P.foldingParam 0) → PaperTranscriptSlot P
  | initialSumcheckChallenge : Fin (P.foldingParam 0) → PaperTranscriptSlot P
  | mainFoldedOracle : Fin M → PaperTranscriptSlot P
  | mainOutOfDomainChallenge : Fin M → PaperTranscriptSlot P
  | mainOutOfDomainReply : Fin M → PaperTranscriptSlot P
  | mainShiftChallenge : Fin M → PaperTranscriptSlot P
  | mainSumcheckMessage : (i : Fin M) → Fin (P.foldingParam i.succ) → PaperTranscriptSlot P
  | mainSumcheckChallenge : (i : Fin M) → Fin (P.foldingParam i.succ) → PaperTranscriptSlot P
  | finalPolynomial : PaperTranscriptSlot P
  | finalRandomness : PaperTranscriptSlot P
  deriving DecidableEq, Fintype

/-- Direction of a faithful WHIR Construction 5.1 transcript slot. -/
def paperTranscriptSlotDirection {M : ℕ} {ιs : Fin (M + 1) → Type} {P : Params ιs F} :
    PaperTranscriptSlot P → Direction
  | .initialSumcheckMessage _ => Direction.P_to_V
  | .initialSumcheckChallenge _ => Direction.V_to_P
  | .mainFoldedOracle _ => Direction.P_to_V
  | .mainOutOfDomainChallenge _ => Direction.V_to_P
  | .mainOutOfDomainReply _ => Direction.P_to_V
  | .mainShiftChallenge _ => Direction.V_to_P
  | .mainSumcheckMessage _ _ => Direction.P_to_V
  | .mainSumcheckChallenge _ _ => Direction.V_to_P
  | .finalPolynomial => Direction.P_to_V
  | .finalRandomness => Direction.V_to_P

/-- Field-vector payload length of each faithful WHIR Construction 5.1 transcript slot.

The `d` parameter is the paper's sumcheck-message degree budget.  Folded-oracle and final-polynomial
messages are represented extensionally as field vectors over their evaluation domains. -/
def paperTranscriptSlotLength {M : ℕ} {ιs : Fin (M + 1) → Type}
    [∀ i : Fin (M + 1), Fintype (ιs i)] (P : Params ιs F) (d : ℕ) :
    PaperTranscriptSlot P → ℕ
  | .initialSumcheckMessage _ => d
  | .initialSumcheckChallenge _ => 1
  | .mainFoldedOracle i => Fintype.card (ιs i.succ)
  | .mainOutOfDomainChallenge _ => 1
  | .mainOutOfDomainReply _ => 1
  | .mainShiftChallenge i => P.repeatParam i.succ
  | .mainSumcheckMessage _ _ => d
  | .mainSumcheckChallenge _ _ => 1
  | .finalPolynomial => 2 ^ P.varCount (Fin.last M)
  | .finalRandomness => P.repeatParam (Fin.last M)

/-- The faithful paper-order WHIR transcript scaffold as a `VectorSpec`.

This is the protocol shape that a Construction 5.1 `VectorIOP` should target.  It differs from the
block-ordered skeleton below because prover messages and verifier challenges are interleaved in the
order needed for the honest prover's state updates. -/
noncomputable def whirPaperTranscriptVectorSpec {M : ℕ} {ιs : Fin (M + 1) → Type}
    [∀ i : Fin (M + 1), Fintype (ιs i)] (P : Params ιs F) (d : ℕ) :
    ProtocolSpec.VectorSpec (Fintype.card (PaperTranscriptSlot P)) where
  dir := fun i =>
    paperTranscriptSlotDirection ((Fintype.equivFin (PaperTranscriptSlot P)).symm i)
  length := fun i =>
    paperTranscriptSlotLength P d ((Fintype.equivFin (PaperTranscriptSlot P)).symm i)

omit [Field F] [DecidableEq F] [SampleableType F] in
@[simp] theorem whirPaperTranscriptVectorSpec_dir {M : ℕ}
    {ιs : Fin (M + 1) → Type} [∀ i : Fin (M + 1), Fintype (ιs i)]
    (P : Params ιs F) (d : ℕ) (i : Fin (Fintype.card (PaperTranscriptSlot P))) :
    (whirPaperTranscriptVectorSpec P d).dir i =
      paperTranscriptSlotDirection ((Fintype.equivFin (PaperTranscriptSlot P)).symm i) :=
  rfl

omit [Field F] [DecidableEq F] [SampleableType F] in
@[simp] theorem whirPaperTranscriptVectorSpec_length {M : ℕ}
    {ιs : Fin (M + 1) → Type} [∀ i : Fin (M + 1), Fintype (ιs i)]
    (P : Params ιs F) (d : ℕ) (i : Fin (Fintype.card (PaperTranscriptSlot P))) :
    (whirPaperTranscriptVectorSpec P d).length i =
      paperTranscriptSlotLength P d ((Fintype.equivFin (PaperTranscriptSlot P)).symm i) :=
  rfl

/-! ### Payload packing for the paper-order scaffold

The paper messages such as folded oracles and the final polynomial are functions over finite
domains, while `VectorSpec.toProtocolSpec` represents every payload as a `Vector F n`.  These
helpers provide the canonical finite-enumeration bridge needed by the honest prover and verifier.
-/

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] in
/-- Pack a finite-domain function into the corresponding vector payload using `Fintype.equivFin`. -/
noncomputable def packFiniteFunction (α : Type) [Fintype α] (f : α → F) :
    Vector F (Fintype.card α) :=
  Vector.ofFn fun i => f ((Fintype.equivFin α).symm i)

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] in
/-- Unpack a vector payload back into the finite-domain function it represents. -/
noncomputable def unpackFiniteFunction (α : Type) [Fintype α]
    (v : Vector F (Fintype.card α)) : α → F :=
  fun x => v.get (Fintype.equivFin α x)

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] in
@[simp] theorem unpack_packFiniteFunction (α : Type) [Fintype α] (f : α → F) :
    unpackFiniteFunction α (packFiniteFunction α f) = f := by
  funext x
  simp [unpackFiniteFunction, packFiniteFunction]

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] in
@[simp] theorem pack_unpackFiniteFunction (α : Type) [Fintype α]
    (v : Vector F (Fintype.card α)) :
    packFiniteFunction α (unpackFiniteFunction α v) = v := by
  ext i
  simp [unpackFiniteFunction, packFiniteFunction]

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] in
/-- The canonical `Fin` index of a paper transcript slot inside `whirPaperTranscriptVectorSpec`. -/
noncomputable def paperTranscriptSlotIndex {M : ℕ} {ιs : Fin (M + 1) → Type}
    [∀ i : Fin (M + 1), Fintype (ιs i)] {P : Params ιs F} :
    PaperTranscriptSlot P → Fin (Fintype.card (PaperTranscriptSlot P)) :=
  Fintype.equivFin (PaperTranscriptSlot P)

omit [Field F] [DecidableEq F] [SampleableType F] in
@[simp] theorem paperTranscriptSlotIndex_symm_apply {M : ℕ} {ιs : Fin (M + 1) → Type}
    [∀ i : Fin (M + 1), Fintype (ιs i)] {P : Params ιs F}
    (slot : PaperTranscriptSlot P) :
    (Fintype.equivFin (PaperTranscriptSlot P)).symm (paperTranscriptSlotIndex slot) = slot := by
  exact (Fintype.equivFin (PaperTranscriptSlot P)).symm_apply_apply slot

omit [Field F] [SampleableType F] in
/-- Turn a paper prover-message slot into the corresponding `VectorSpec.MessageIdx`. -/
noncomputable def paperMessageIdx {M : ℕ} {ιs : Fin (M + 1) → Type}
    [∀ i : Fin (M + 1), Fintype (ιs i)] (P : Params ιs F) (d : ℕ)
  (slot : PaperTranscriptSlot P) (hslot : paperTranscriptSlotDirection slot = Direction.P_to_V) :
    (whirPaperTranscriptVectorSpec P d).MessageIdx :=
  ⟨paperTranscriptSlotIndex slot, by
    change paperTranscriptSlotDirection
        ((Fintype.equivFin (PaperTranscriptSlot P)).symm (paperTranscriptSlotIndex slot)) =
      Direction.P_to_V
    simpa [paperTranscriptSlotIndex] using hslot⟩

omit [Field F] [SampleableType F] in
/-- Turn a paper verifier-challenge slot into the corresponding `VectorSpec.ChallengeIdx`. -/
noncomputable def paperChallengeIdx {M : ℕ} {ιs : Fin (M + 1) → Type}
    [∀ i : Fin (M + 1), Fintype (ιs i)] (P : Params ιs F) (d : ℕ)
  (slot : PaperTranscriptSlot P) (hslot : paperTranscriptSlotDirection slot = Direction.V_to_P) :
    (whirPaperTranscriptVectorSpec P d).ChallengeIdx :=
  ⟨paperTranscriptSlotIndex slot, by
    change paperTranscriptSlotDirection
        ((Fintype.equivFin (PaperTranscriptSlot P)).symm (paperTranscriptSlotIndex slot)) =
      Direction.V_to_P
    simpa [paperTranscriptSlotIndex] using hslot⟩

omit [Field F] [SampleableType F] in
noncomputable def initialSumcheckMessageIdx {M : ℕ} {ιs : Fin (M + 1) → Type}
    [∀ i : Fin (M + 1), Fintype (ιs i)] (P : Params ιs F) (d : ℕ)
    (s : Fin (P.foldingParam 0)) :
    (whirPaperTranscriptVectorSpec P d).MessageIdx :=
  paperMessageIdx P d (.initialSumcheckMessage s) rfl

omit [Field F] [SampleableType F] in
noncomputable def initialSumcheckChallengeIdx {M : ℕ} {ιs : Fin (M + 1) → Type}
    [∀ i : Fin (M + 1), Fintype (ιs i)] (P : Params ιs F) (d : ℕ)
    (s : Fin (P.foldingParam 0)) :
    (whirPaperTranscriptVectorSpec P d).ChallengeIdx :=
  paperChallengeIdx P d (.initialSumcheckChallenge s) rfl

omit [Field F] [SampleableType F] in
noncomputable def mainFoldedOracleMessageIdx {M : ℕ} {ιs : Fin (M + 1) → Type}
    [∀ i : Fin (M + 1), Fintype (ιs i)] (P : Params ιs F) (d : ℕ) (i : Fin M) :
    (whirPaperTranscriptVectorSpec P d).MessageIdx :=
  paperMessageIdx P d (.mainFoldedOracle i) rfl

omit [Field F] [SampleableType F] in
noncomputable def mainOutOfDomainChallengeIdx {M : ℕ} {ιs : Fin (M + 1) → Type}
    [∀ i : Fin (M + 1), Fintype (ιs i)] (P : Params ιs F) (d : ℕ) (i : Fin M) :
    (whirPaperTranscriptVectorSpec P d).ChallengeIdx :=
  paperChallengeIdx P d (.mainOutOfDomainChallenge i) rfl

omit [Field F] [SampleableType F] in
noncomputable def mainOutOfDomainReplyMessageIdx {M : ℕ} {ιs : Fin (M + 1) → Type}
    [∀ i : Fin (M + 1), Fintype (ιs i)] (P : Params ιs F) (d : ℕ) (i : Fin M) :
    (whirPaperTranscriptVectorSpec P d).MessageIdx :=
  paperMessageIdx P d (.mainOutOfDomainReply i) rfl

omit [Field F] [SampleableType F] in
noncomputable def mainShiftChallengeIdx {M : ℕ} {ιs : Fin (M + 1) → Type}
    [∀ i : Fin (M + 1), Fintype (ιs i)] (P : Params ιs F) (d : ℕ) (i : Fin M) :
    (whirPaperTranscriptVectorSpec P d).ChallengeIdx :=
  paperChallengeIdx P d (.mainShiftChallenge i) rfl

omit [Field F] [SampleableType F] in
noncomputable def mainSumcheckMessageIdx {M : ℕ} {ιs : Fin (M + 1) → Type}
    [∀ i : Fin (M + 1), Fintype (ιs i)] (P : Params ιs F) (d : ℕ) (i : Fin M)
    (s : Fin (P.foldingParam i.succ)) :
    (whirPaperTranscriptVectorSpec P d).MessageIdx :=
  paperMessageIdx P d (.mainSumcheckMessage i s) rfl

omit [Field F] [SampleableType F] in
noncomputable def mainSumcheckChallengeIdx {M : ℕ} {ιs : Fin (M + 1) → Type}
    [∀ i : Fin (M + 1), Fintype (ιs i)] (P : Params ιs F) (d : ℕ) (i : Fin M)
    (s : Fin (P.foldingParam i.succ)) :
    (whirPaperTranscriptVectorSpec P d).ChallengeIdx :=
  paperChallengeIdx P d (.mainSumcheckChallenge i s) rfl

omit [Field F] [SampleableType F] in
noncomputable def finalPolynomialMessageIdx {M : ℕ} {ιs : Fin (M + 1) → Type}
    [∀ i : Fin (M + 1), Fintype (ιs i)] (P : Params ιs F) (d : ℕ) :
    (whirPaperTranscriptVectorSpec P d).MessageIdx :=
  paperMessageIdx P d .finalPolynomial rfl

omit [Field F] [SampleableType F] in
noncomputable def finalRandomnessChallengeIdx {M : ℕ} {ιs : Fin (M + 1) → Type}
    [∀ i : Fin (M + 1), Fintype (ιs i)] (P : Params ιs F) (d : ℕ) :
    (whirPaperTranscriptVectorSpec P d).ChallengeIdx :=
  paperChallengeIdx P d .finalRandomness rfl

/-! ### Typed payloads and full transcript assembly

These constructors target the concrete payload types of
`(whirPaperTranscriptVectorSpec P d).toProtocolSpec F`.  They are the typed bridge needed before
writing the honest prover: folded oracles and the final polynomial are finite-domain functions
packed as vectors, scalar OOD/sumcheck challenges are singleton vectors, and shift/final randomness
batches keep their prescribed vector lengths.
-/

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] in
/-- A singleton field payload represented as the vector type used by `VectorSpec.toProtocolSpec`. -/
def singletonFieldPayload (x : F) : Vector F 1 :=
  Vector.ofFn fun _ => x

omit [Field F] [SampleableType F] in
/-- Payload for an initial sumcheck polynomial-message slot. -/
def initialSumcheckMessagePayload {M : ℕ} {ιs : Fin (M + 1) → Type}
    [∀ i : Fin (M + 1), Fintype (ιs i)] (P : Params ιs F) (d : ℕ)
    (s : Fin (P.foldingParam 0)) (coeffs : Vector F d) :
    ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F).Message
      (initialSumcheckMessageIdx P d s) := by
  simpa [initialSumcheckMessageIdx, paperMessageIdx, whirPaperTranscriptVectorSpec,
    paperTranscriptSlotIndex] using coeffs

omit [Field F] [SampleableType F] in
/-- Payload for an initial sumcheck scalar challenge. -/
def initialSumcheckChallengePayload {M : ℕ} {ιs : Fin (M + 1) → Type}
    [∀ i : Fin (M + 1), Fintype (ιs i)] (P : Params ιs F) (d : ℕ)
    (s : Fin (P.foldingParam 0)) (x : F) :
    ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F).Challenge
      (initialSumcheckChallengeIdx P d s) := by
  simpa [initialSumcheckChallengeIdx, paperChallengeIdx, whirPaperTranscriptVectorSpec,
    paperTranscriptSlotIndex] using singletonFieldPayload x

omit [Field F] [SampleableType F] in
/-- Payload for a folded-oracle message in transition round `i`. -/
noncomputable def mainFoldedOraclePayload {M : ℕ} {ιs : Fin (M + 1) → Type}
    [∀ i : Fin (M + 1), Fintype (ιs i)] (P : Params ιs F) (d : ℕ) (i : Fin M)
    (f : ιs i.succ → F) :
    ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F).Message
      (mainFoldedOracleMessageIdx P d i) := by
  simpa [mainFoldedOracleMessageIdx, paperMessageIdx, whirPaperTranscriptVectorSpec,
    paperTranscriptSlotIndex] using packFiniteFunction (ιs i.succ) f

omit [Field F] [SampleableType F] in
/-- Challenge payload for an out-of-domain sample in transition round `i`. -/
def mainOutOfDomainChallengePayload {M : ℕ} {ιs : Fin (M + 1) → Type}
    [∀ i : Fin (M + 1), Fintype (ιs i)] (P : Params ιs F) (d : ℕ) (i : Fin M)
    (z : F) :
    ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F).Challenge
      (mainOutOfDomainChallengeIdx P d i) := by
  simpa [mainOutOfDomainChallengeIdx, paperChallengeIdx, whirPaperTranscriptVectorSpec,
    paperTranscriptSlotIndex] using singletonFieldPayload z

omit [Field F] [SampleableType F] in
/-- Payload for an out-of-domain reply message in transition round `i`. -/
def mainOutOfDomainReplyPayload {M : ℕ} {ιs : Fin (M + 1) → Type}
    [∀ i : Fin (M + 1), Fintype (ιs i)] (P : Params ιs F) (d : ℕ) (i : Fin M)
    (y : F) :
    ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F).Message
      (mainOutOfDomainReplyMessageIdx P d i) := by
  simpa [mainOutOfDomainReplyMessageIdx, paperMessageIdx, whirPaperTranscriptVectorSpec,
    paperTranscriptSlotIndex] using singletonFieldPayload y

omit [Field F] [SampleableType F] in
/-- Challenge payload constructor for the batched shift/random-linear-combination samples. -/
def mainShiftChallengePayload {M : ℕ} {ιs : Fin (M + 1) → Type}
    [∀ i : Fin (M + 1), Fintype (ιs i)] (P : Params ιs F) (d : ℕ) (i : Fin M)
    (xs : Vector F (P.repeatParam i.succ)) :
    ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F).Challenge
      (mainShiftChallengeIdx P d i) := by
  simpa [mainShiftChallengeIdx, paperChallengeIdx, whirPaperTranscriptVectorSpec,
    paperTranscriptSlotIndex] using xs

omit [Field F] [SampleableType F] in
/-- Payload for a main-loop sumcheck polynomial-message slot. -/
def mainSumcheckMessagePayload {M : ℕ} {ιs : Fin (M + 1) → Type}
    [∀ i : Fin (M + 1), Fintype (ιs i)] (P : Params ιs F) (d : ℕ) (i : Fin M)
    (s : Fin (P.foldingParam i.succ)) (coeffs : Vector F d) :
    ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F).Message
      (mainSumcheckMessageIdx P d i s) := by
  simpa [mainSumcheckMessageIdx, paperMessageIdx, whirPaperTranscriptVectorSpec,
    paperTranscriptSlotIndex] using coeffs

omit [Field F] [SampleableType F] in
/-- Challenge payload for a main-loop sumcheck scalar challenge. -/
def mainSumcheckChallengePayload {M : ℕ} {ιs : Fin (M + 1) → Type}
    [∀ i : Fin (M + 1), Fintype (ιs i)] (P : Params ιs F) (d : ℕ) (i : Fin M)
    (s : Fin (P.foldingParam i.succ)) (x : F) :
    ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F).Challenge
      (mainSumcheckChallengeIdx P d i s) := by
  simpa [mainSumcheckChallengeIdx, paperChallengeIdx, whirPaperTranscriptVectorSpec,
    paperTranscriptSlotIndex] using singletonFieldPayload x

omit [Field F] [SampleableType F] in
/-- Payload for the final polynomial message. -/
noncomputable def finalPolynomialPayload {M : ℕ} {ιs : Fin (M + 1) → Type}
    [∀ i : Fin (M + 1), Fintype (ιs i)] (P : Params ιs F) (d : ℕ)
    (f : Fin (2 ^ P.varCount (Fin.last M)) → F) :
    ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F).Message
      (finalPolynomialMessageIdx P d) := by
  simpa [finalPolynomialMessageIdx, paperMessageIdx, whirPaperTranscriptVectorSpec,
    paperTranscriptSlotIndex] using
      packFiniteFunction (Fin (2 ^ P.varCount (Fin.last M))) f

omit [Field F] [SampleableType F] in
/-- Challenge payload constructor for the final randomness batch. -/
def finalRandomnessChallengePayload {M : ℕ} {ιs : Fin (M + 1) → Type}
    [∀ i : Fin (M + 1), Fintype (ιs i)] (P : Params ιs F) (d : ℕ)
    (xs : Vector F (P.repeatParam (Fin.last M))) :
    ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F).Challenge
      (finalRandomnessChallengeIdx P d) := by
  simpa [finalRandomnessChallengeIdx, paperChallengeIdx, whirPaperTranscriptVectorSpec,
    paperTranscriptSlotIndex] using xs

/-- Field data for one complete paper-order WHIR transcript.

This is still not a prover.  It is the typed transcript boundary that a real prover must produce
and the real verifier must consume. -/
structure PaperTranscriptData {M : ℕ} {ιs : Fin (M + 1) → Type}
    [∀ i : Fin (M + 1), Fintype (ιs i)] (P : Params ιs F) (d : ℕ) where
  initialSumcheckMessage : Fin (P.foldingParam 0) → Vector F d
  initialSumcheckChallenge : Fin (P.foldingParam 0) → F
  mainFoldedOracle : (i : Fin M) → ιs i.succ → F
  mainOutOfDomainChallenge : Fin M → F
  mainOutOfDomainReply : Fin M → F
  mainShiftChallenge : (i : Fin M) → Vector F (P.repeatParam i.succ)
  mainSumcheckMessage : (i : Fin M) → Fin (P.foldingParam i.succ) → Vector F d
  mainSumcheckChallenge : (i : Fin M) → Fin (P.foldingParam i.succ) → F
  finalPolynomial : Fin (2 ^ P.varCount (Fin.last M)) → F
  finalRandomness : Vector F (P.repeatParam (Fin.last M))

omit [Field F] [SampleableType F] in
/-- Convert typed paper transcript data into the payload for one named paper transcript slot. -/
noncomputable def paperTranscriptSlotPayload {M : ℕ} {ιs : Fin (M + 1) → Type}
    [∀ i : Fin (M + 1), Fintype (ιs i)] (P : Params ιs F) (d : ℕ)
    (T : PaperTranscriptData P d) :
    (slot : PaperTranscriptSlot P) → Vector F (paperTranscriptSlotLength P d slot)
  | .initialSumcheckMessage s => T.initialSumcheckMessage s
  | .initialSumcheckChallenge s => singletonFieldPayload (T.initialSumcheckChallenge s)
  | .mainFoldedOracle i => packFiniteFunction (ιs i.succ) (T.mainFoldedOracle i)
  | .mainOutOfDomainChallenge i => singletonFieldPayload (T.mainOutOfDomainChallenge i)
  | .mainOutOfDomainReply i => singletonFieldPayload (T.mainOutOfDomainReply i)
  | .mainShiftChallenge i => T.mainShiftChallenge i
  | .mainSumcheckMessage i s => T.mainSumcheckMessage i s
  | .mainSumcheckChallenge i s => singletonFieldPayload (T.mainSumcheckChallenge i s)
  | .finalPolynomial => Vector.ofFn T.finalPolynomial
  | .finalRandomness => T.finalRandomness

omit [Field F] [SampleableType F] in
/-- Assemble typed paper data into a full transcript for the paper-order `ProtocolSpec`. -/
noncomputable def paperTranscriptFullTranscript {M : ℕ} {ιs : Fin (M + 1) → Type}
    [∀ i : Fin (M + 1), Fintype (ιs i)] (P : Params ιs F) (d : ℕ)
    (T : PaperTranscriptData P d) :
    ProtocolSpec.FullTranscript ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F) :=
  fun i => by
    change Vector F ((whirPaperTranscriptVectorSpec P d).length i)
    exact paperTranscriptSlotPayload P d T
      ((Fintype.equivFin (PaperTranscriptSlot P)).symm i)

omit [Field F] [SampleableType F] in
/-- The prover-message projection of assembled paper transcript data. -/
noncomputable def paperTranscriptMessage {M : ℕ} {ιs : Fin (M + 1) → Type}
    [∀ i : Fin (M + 1), Fintype (ιs i)] (P : Params ιs F) (d : ℕ)
    (T : PaperTranscriptData P d)
    (i : ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F).MessageIdx) :
    ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F).Message i :=
  (paperTranscriptFullTranscript P d T).messages i

omit [Field F] [SampleableType F] in
/-- The verifier-challenge projection of assembled paper transcript data. -/
noncomputable def paperTranscriptChallenge {M : ℕ} {ιs : Fin (M + 1) → Type}
    [∀ i : Fin (M + 1), Fintype (ιs i)] (P : Params ιs F) (d : ℕ)
    (T : PaperTranscriptData P d)
    (i : ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F).ChallengeIdx) :
    ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F).Challenge i :=
  (paperTranscriptFullTranscript P d T).challenges i

omit [Field F] [SampleableType F] in
/-- The full transcript shape seen by the verifier during honest execution of the paper adapter.

The prover-message slots are emitted from the supplied `PaperTranscriptData`, while the verifier
challenge slots are the actual runtime challenges sampled by ArkLib's execution semantics.  This is
the transcript surface a future perfect-completeness proof for `paperTranscriptVectorIOP` must show
the WHIR verifier accepts. -/
noncomputable def paperTranscriptRuntimeFullTranscript {M : ℕ}
    {ιs : Fin (M + 1) → Type} [∀ i : Fin (M + 1), Fintype (ιs i)]
    (P : Params ιs F) (d : ℕ) (T : PaperTranscriptData P d)
    (challenges : ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F).Challenges) :
    ProtocolSpec.FullTranscript ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F) :=
  fun i =>
    if h : (whirPaperTranscriptVectorSpec P d).dir i = Direction.P_to_V then
      paperTranscriptMessage P d T ⟨i, h⟩
    else
      challenges ⟨i, Direction.not_V_to_P_eq_P_to_V h⟩

omit [Field F] [SampleableType F] in
@[simp] theorem paperTranscriptRuntimeFullTranscript_messages {M : ℕ}
    {ιs : Fin (M + 1) → Type} [∀ i : Fin (M + 1), Fintype (ιs i)]
    (P : Params ιs F) (d : ℕ) (T : PaperTranscriptData P d)
    (challenges : ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F).Challenges)
    (i : ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F).MessageIdx) :
    (paperTranscriptRuntimeFullTranscript P d T challenges).messages i =
      paperTranscriptMessage P d T i := by
  cases i with
  | mk i hi =>
      simp only [FullTranscript.messages, FullTranscript.challenges,
        paperTranscriptRuntimeFullTranscript]
      split <;> aesop

omit [Field F] [SampleableType F] in
@[simp] theorem paperTranscriptRuntimeFullTranscript_challenges {M : ℕ}
    {ιs : Fin (M + 1) → Type} [∀ i : Fin (M + 1), Fintype (ιs i)]
    (P : Params ιs F) (d : ℕ) (T : PaperTranscriptData P d)
    (challenges : ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F).Challenges)
    (i : ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F).ChallengeIdx) :
    (paperTranscriptRuntimeFullTranscript P d T challenges).challenges i = challenges i := by
  cases i with
  | mk i hi =>
      simp only [FullTranscript.challenges, paperTranscriptRuntimeFullTranscript]
      have hi' : (whirPaperTranscriptVectorSpec P d).dir i = Direction.V_to_P := hi
      split
      · rename_i h
        cases h.symm.trans hi'
      · rfl

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] in
@[simp] theorem paperTranscriptSlotPayload_mainFoldedOracle {M : ℕ}
    {ιs : Fin (M + 1) → Type} [∀ i : Fin (M + 1), Fintype (ιs i)]
    (P : Params ιs F) (d : ℕ) (T : PaperTranscriptData P d) (i : Fin M) :
    paperTranscriptSlotPayload P d T (.mainFoldedOracle i) =
      packFiniteFunction (ιs i.succ) (T.mainFoldedOracle i) :=
  rfl

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] in
@[simp] theorem paperTranscriptSlotPayload_mainOutOfDomainReply {M : ℕ}
    {ιs : Fin (M + 1) → Type} [∀ i : Fin (M + 1), Fintype (ιs i)]
    (P : Params ιs F) (d : ℕ) (T : PaperTranscriptData P d) (i : Fin M) :
    paperTranscriptSlotPayload P d T (.mainOutOfDomainReply i) =
      singletonFieldPayload (T.mainOutOfDomainReply i) :=
  rfl

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] in
@[simp] theorem paperTranscriptSlotPayload_mainShiftChallenge {M : ℕ}
    {ιs : Fin (M + 1) → Type} [∀ i : Fin (M + 1), Fintype (ιs i)]
    (P : Params ιs F) (d : ℕ) (T : PaperTranscriptData P d) (i : Fin M) :
    paperTranscriptSlotPayload P d T (.mainShiftChallenge i) = T.mainShiftChallenge i :=
  rfl

omit [Field F] [SampleableType F] in
/-- A prover-side adapter that emits the prover-message slots from supplied paper transcript data.

This is not yet the WHIR honest prover: the real prover must compute `PaperTranscriptData` from the
input oracle and prior verifier challenges.  This adapter is the first actual `OracleProver` object
over the paper-order protocol shape, isolating the remaining algebraic transcript-generation
problem from ArkLib's prover-state API. -/
noncomputable def paperTranscriptOracleProver {M : ℕ} {ιs : Fin (M + 1) → Type}
    [∀ i : Fin (M + 1), Fintype (ιs i)] (P : Params ιs F) (d : ℕ)
    (makeTranscript :
      (Unit × (∀ u : Unit, OracleStatement (ιs 0) F u)) × Unit → PaperTranscriptData P d) :
    OracleProver []ₒ Unit (OracleStatement (ιs 0) F) Unit
      Bool (fun _ : Empty => Unit) Unit ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F) where
  PrvState := fun _ => PaperTranscriptData P d
  input := makeTranscript
  sendMessage := fun i T => pure (paperTranscriptMessage P d T i, T)
  receiveChallenge := fun _ T => pure (fun _ => T)
  output := fun _ => pure ((true, fun e => nomatch e), ())

omit [Field F] [SampleableType F] in
/-- A verifier-side adapter for the faithful paper-order transcript shape.

The supplied `verify` computation is the real WHIR verifier logic still to be built: it receives
the public statement and all verifier challenges, and may query the input oracle and prover-message
oracles through ArkLib's `OracleComp` interface.  The adapter records that WHIR IOPs have no output
oracle statements. -/
noncomputable def paperTranscriptOracleVerifier {M : ℕ} {ιs : Fin (M + 1) → Type}
    [∀ i : Fin (M + 1), Fintype (ιs i)] (P : Params ιs F) (d : ℕ)
    (verify :
      Unit → ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F).Challenges →
        OptionT
          (OracleComp
            ([]ₒ +
              ([OracleStatement (ιs 0) F]ₒ +
                [((whirPaperTranscriptVectorSpec P d).toProtocolSpec F).Message]ₒ)))
          Bool) :
    OracleVerifier []ₒ Unit (OracleStatement (ιs 0) F)
      Bool (fun _ : Empty => Unit) ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F) where
  verify := verify
  embed := {
    toFun := fun e => nomatch e
    inj' := fun e => nomatch e
  }
  hEq := fun e => nomatch e

omit [Field F] [SampleableType F] in
/-- Package supplied paper-order transcript generation and verifier logic as an actual WHIR-shaped
`VectorIOP`.

This is the first `VectorIOP` constructor over the faithful Construction 5.1 `VectorSpec`.  It is
intentionally an adapter: perfect completeness and RBR soundness still require instantiating
`verify` with the algebraic WHIR checks and proving the corresponding security obligations. -/
noncomputable def paperTranscriptVectorIOP {M : ℕ} {ιs : Fin (M + 1) → Type}
    [∀ i : Fin (M + 1), Fintype (ιs i)] (P : Params ιs F) (d : ℕ)
    (makeTranscript :
      (Unit × (∀ u : Unit, OracleStatement (ιs 0) F u)) × Unit → PaperTranscriptData P d)
    (verify :
      Unit → ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F).Challenges →
        OptionT
          (OracleComp
            ([]ₒ +
              ([OracleStatement (ιs 0) F]ₒ +
                [((whirPaperTranscriptVectorSpec P d).toProtocolSpec F).Message]ₒ)))
          Bool) :
    VectorIOP Unit (OracleStatement (ιs 0) F) Unit (whirPaperTranscriptVectorSpec P d) F where
  prover := paperTranscriptOracleProver P d makeTranscript
  verifier := paperTranscriptOracleVerifier P d verify

omit [Field F] [DecidableEq F] [Fintype ι] [DecidableEq ι] [Nonempty ι] in
/-- Package the two semantic proof obligations for the paper-transcript adapter into the
`VectorIOP.IsSecureWithGap` class consumed by the WHIR RBR assembly wrappers.

This is pure assembly around the concrete `paperTranscriptVectorIOP`: callers still have to prove
perfect completeness for the supplied transcript generator and RBR knowledge soundness for the
supplied verifier logic. -/
theorem paperTranscriptVectorIOP_isSecureWithGap_of_complete_and_rbr {M : ℕ}
    {ιs : Fin (M + 1) → Type} [∀ i : Fin (M + 1), Fintype (ιs i)]
    (P : Params ιs F) (d : ℕ)
    (makeTranscript :
      (Unit × (∀ u : Unit, OracleStatement (ιs 0) F u)) × Unit → PaperTranscriptData P d)
    (verify :
      Unit → ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F).Challenges →
        OptionT
          (OracleComp
            ([]ₒ +
              ([OracleStatement (ιs 0) F]ₒ +
                [((whirPaperTranscriptVectorSpec P d).toProtocolSpec F).Message]ₒ)))
          Bool)
    {completeRelation soundRelation :
      Set ((Unit × ∀ i, OracleStatement (ιs 0) F i) × Unit)}
    {ε_rbr : (whirPaperTranscriptVectorSpec P d).ChallengeIdx → ℝ≥0}
    (hComplete :
      (paperTranscriptVectorIOP P d makeTranscript verify).perfectCompleteness
        (pure ()) isEmptyElim completeRelation)
    (hRbr :
      OracleProof.rbrKnowledgeSoundness (pure ()) isEmptyElim soundRelation
        (paperTranscriptOracleVerifier P d verify) ε_rbr) :
    VectorIOP.IsSecureWithGap completeRelation soundRelation ε_rbr
      (paperTranscriptVectorIOP P d makeTranscript verify) where
  is_complete := hComplete
  is_rbr_knowledge_sound := hRbr

omit [Fintype F] [DecidableEq F] [SampleableType F] in
/-- Folding challenges for each WHIR transition, read from the paper-order transcript schedule.

The first transition uses the initial sumcheck challenges.  Transition `k+1` uses the main
sumcheck challenges from the previous main-loop slot `k`, matching Construction 5.1's challenge
flow from one folded oracle to the next. -/
def paperTranscriptFoldingChallenge {M : ℕ} {ιs : Fin ((M + 1) + 1) → Type}
    [∀ i : Fin ((M + 1) + 1), Fintype (ιs i)] (P : Params ιs F) (d : ℕ)
    (T : PaperTranscriptData P d) (i : Fin (M + 1)) :
    Fin (P.foldingParam i.castSucc) → F :=
  Fin.cases (motive := fun i : Fin (M + 1) =>
      Fin (P.foldingParam i.castSucc) → F)
    T.initialSumcheckChallenge
    (fun k => T.mainSumcheckChallenge k.castSucc)
    i

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] in
@[simp] theorem paperTranscriptFoldingChallenge_zero {M : ℕ}
    {ιs : Fin ((M + 1) + 1) → Type}
    [∀ i : Fin ((M + 1) + 1), Fintype (ιs i)]
    (P : Params ιs F) (d : ℕ) (T : PaperTranscriptData P d)
    (j : Fin (P.foldingParam 0)) :
    paperTranscriptFoldingChallenge P d T 0 j = T.initialSumcheckChallenge j := by
  rfl

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] in
@[simp] theorem paperTranscriptFoldingChallenge_succ {M : ℕ}
    {ιs : Fin ((M + 1) + 1) → Type}
    [∀ i : Fin ((M + 1) + 1), Fintype (ιs i)]
    (P : Params ιs F) (d : ℕ) (T : PaperTranscriptData P d)
    (i : Fin M) (j : Fin (P.foldingParam i.succ.castSucc)) :
    paperTranscriptFoldingChallenge P d T i.succ j =
      T.mainSumcheckChallenge i.castSucc j := by
  rfl

omit [Fintype F] [DecidableEq F] [SampleableType F] in
/-- Domain bridge needed to state that a paper-order folded-oracle message is an actual
`Fold.fold_k` output.

The folding library computes on `BlockRelDistance.indexPowT (S i) (P.φ i) k`, while the WHIR
parameter record exposes the next paper domain as `ιs (i+1)`.  A real Construction 5.1 prover must
either provide this identification or strengthen `Params` so the identification is definitional. -/
structure PaperFoldDomainBridge {M : ℕ} {ιs : Fin (M + 1) → Type}
    (P : Params ιs F) (S : ∀ i : Fin (M + 1), Finset (ιs i)) where
  nextDomainEquiv :
    (i : Fin M) →
      ιs i.succ ≃
        BlockRelDistance.indexPowT (S i.castSucc) (P.φ i.castSucc)
          (P.foldingParam i.castSucc)

omit [Fintype F] [DecidableEq F] [SampleableType F] in
/-- Domain bridge for the *input* oracle.

`PaperFoldDomainBridge` identifies every next folded-oracle paper domain `ιs (i+1)` with the
power-domain used by the folding library.  The first transition also needs an identification of the
original input-oracle domain `ιs 0` with the source power-domain `indexPowT ... 0`; this structure
keeps that extra assumption explicit instead of hiding it inside the verifier binding check. -/
structure PaperInputDomainBridge {M : ℕ} {ιs : Fin (M + 1) → Type}
    (P : Params ιs F) (S : ∀ i : Fin (M + 1), Finset (ιs i)) where
  sourceDomainEquiv :
    ιs 0 ≃ BlockRelDistance.indexPowT (S 0) (P.φ 0) 0

omit [Fintype F] [DecidableEq F] [SampleableType F] in
@[simp] theorem paperInputDomainBridge_sourceDomainEquiv_apply {M : ℕ}
    {ιs : Fin (M + 1) → Type} (P : Params ιs F)
    (S : ∀ i : Fin (M + 1), Finset (ιs i)) (bridge : PaperInputDomainBridge P S)
    (x : ιs 0) :
    bridge.sourceDomainEquiv x = (bridge.sourceDomainEquiv) x :=
  rfl

omit [Fintype F] [DecidableEq F] [SampleableType F] in
/-- Transport an input oracle to the source domain used by the first WHIR fold. -/
noncomputable def paperInputSourceFromOracle {M : ℕ} {ιs : Fin (M + 1) → Type}
    (P : Params ιs F) (S : ∀ i : Fin (M + 1), Finset (ιs i))
    (bridge : PaperInputDomainBridge P S) (oracle : OracleStatement (ιs 0) F ()) :
    BlockRelDistance.indexPowT (S 0) (P.φ 0) 0 → F :=
  fun x => oracle (bridge.sourceDomainEquiv.symm x)

omit [Fintype F] [DecidableEq F] [SampleableType F] in
@[simp] theorem paperInputSourceFromOracle_apply {M : ℕ} {ιs : Fin (M + 1) → Type}
    (P : Params ιs F) (S : ∀ i : Fin (M + 1), Finset (ιs i))
    (bridge : PaperInputDomainBridge P S) (oracle : OracleStatement (ιs 0) F ())
    (x : BlockRelDistance.indexPowT (S 0) (P.φ 0) 0) :
    paperInputSourceFromOracle P S bridge oracle x =
      oracle (bridge.sourceDomainEquiv.symm x) :=
  rfl

omit [Fintype F] [DecidableEq F] [SampleableType F] in
@[simp] theorem paperFoldDomainBridge_nextDomainEquiv_apply {M : ℕ}
    {ιs : Fin (M + 1) → Type} (P : Params ιs F)
    (S : ∀ i : Fin (M + 1), Finset (ιs i)) (bridge : PaperFoldDomainBridge P S)
    (i : Fin M) (x : ιs i.succ) :
    bridge.nextDomainEquiv i x =
      (bridge.nextDomainEquiv i) x :=
  rfl

omit [Fintype F] [DecidableEq F] [SampleableType F] in
/-- The folded oracle produced by one WHIR transition, transported back to the paper domain.

`source i` is the function on the current round's power-domain representation, and
`foldChallenge i` is the batch of folding challenges for that transition. -/
noncomputable def paperFoldedOracleFrom {M : ℕ} {ιs : Fin (M + 1) → Type}
    (P : Params ιs F) (S : ∀ i : Fin (M + 1), Finset (ιs i))
    (bridge : PaperFoldDomainBridge P S)
    (hNeg :
      ∀ i : Fin M, ∀ j : ℕ,
        Neg (BlockRelDistance.indexPowT (S i.castSucc) (P.φ i.castSucc) j))
    (source :
      (i : Fin M) →
        BlockRelDistance.indexPowT (S i.castSucc) (P.φ i.castSucc) 0 → F)
    (foldChallenge : (i : Fin M) → Fin (P.foldingParam i.castSucc) → F)
    (hFoldLe : ∀ i : Fin M, P.foldingParam i.castSucc ≤ P.varCount i.castSucc)
    (i : Fin M) (x : ιs i.succ) : F :=
  letI : ∀ j : ℕ,
      Neg (BlockRelDistance.indexPowT (S i.castSucc) (P.φ i.castSucc) j) :=
    hNeg i
  Fold.fold_k (source i) (foldChallenge i) (hFoldLe i) (bridge.nextDomainEquiv i x)

omit [Fintype F] [DecidableEq F] [SampleableType F] in
@[simp] theorem paperFoldedOracleFrom_apply {M : ℕ} {ιs : Fin (M + 1) → Type}
    (P : Params ιs F) (S : ∀ i : Fin (M + 1), Finset (ιs i))
    (bridge : PaperFoldDomainBridge P S)
    (hNeg :
      ∀ i : Fin M, ∀ j : ℕ,
        Neg (BlockRelDistance.indexPowT (S i.castSucc) (P.φ i.castSucc) j))
    (source :
      (i : Fin M) →
        BlockRelDistance.indexPowT (S i.castSucc) (P.φ i.castSucc) 0 → F)
    (foldChallenge : (i : Fin M) → Fin (P.foldingParam i.castSucc) → F)
    (hFoldLe : ∀ i : Fin M, P.foldingParam i.castSucc ≤ P.varCount i.castSucc)
    (i : Fin M) (x : ιs i.succ) :
    paperFoldedOracleFrom P S bridge hNeg source foldChallenge hFoldLe i x =
      letI : ∀ j : ℕ,
          Neg (BlockRelDistance.indexPowT (S i.castSucc) (P.φ i.castSucc) j) :=
        hNeg i
      Fold.fold_k (source i) (foldChallenge i) (hFoldLe i)
        (bridge.nextDomainEquiv i x) :=
  rfl

omit [Fintype F] [DecidableEq F] [SampleableType F] in
/-- Predicate saying the paper transcript's folded-oracle messages are the actual `Fold.fold_k`
outputs for the supplied source functions and folding challenges. -/
def paperTranscriptHasFoldedOracles {M : ℕ} {ιs : Fin (M + 1) → Type}
    [∀ i : Fin (M + 1), Fintype (ιs i)] (P : Params ιs F) (d : ℕ)
    (S : ∀ i : Fin (M + 1), Finset (ιs i))
    (bridge : PaperFoldDomainBridge P S)
    (hNeg :
      ∀ i : Fin M, ∀ j : ℕ,
        Neg (BlockRelDistance.indexPowT (S i.castSucc) (P.φ i.castSucc) j))
    (source :
      (i : Fin M) →
        BlockRelDistance.indexPowT (S i.castSucc) (P.φ i.castSucc) 0 → F)
    (foldChallenge : (i : Fin M) → Fin (P.foldingParam i.castSucc) → F)
    (hFoldLe : ∀ i : Fin M, P.foldingParam i.castSucc ≤ P.varCount i.castSucc)
    (T : PaperTranscriptData P d) : Prop :=
  ∀ i x,
    T.mainFoldedOracle i x =
      paperFoldedOracleFrom P S bridge hNeg source foldChallenge hFoldLe i x

omit [Fintype F] [DecidableEq F] [SampleableType F] in
/-- If a transcript's folded-oracle slot satisfies the folding predicate, then the packed payload
for that named paper slot is exactly the packed transported `Fold.fold_k` output. -/
theorem paperTranscriptSlotPayload_mainFoldedOracle_of_hasFoldedOracles {M : ℕ}
    {ιs : Fin (M + 1) → Type} [∀ i : Fin (M + 1), Fintype (ιs i)]
    (P : Params ιs F) (d : ℕ) (S : ∀ i : Fin (M + 1), Finset (ιs i))
    (bridge : PaperFoldDomainBridge P S)
    (hNeg :
      ∀ i : Fin M, ∀ j : ℕ,
        Neg (BlockRelDistance.indexPowT (S i.castSucc) (P.φ i.castSucc) j))
    (source :
      (i : Fin M) →
        BlockRelDistance.indexPowT (S i.castSucc) (P.φ i.castSucc) 0 → F)
    (foldChallenge : (i : Fin M) → Fin (P.foldingParam i.castSucc) → F)
    (hFoldLe : ∀ i : Fin M, P.foldingParam i.castSucc ≤ P.varCount i.castSucc)
    (T : PaperTranscriptData P d)
    (hT : paperTranscriptHasFoldedOracles P d S bridge hNeg source foldChallenge hFoldLe T)
    (i : Fin M) :
    paperTranscriptSlotPayload P d T (.mainFoldedOracle i) =
      packFiniteFunction (ιs i.succ)
        (paperFoldedOracleFrom P S bridge hNeg source foldChallenge hFoldLe i) := by
  rw [paperTranscriptSlotPayload_mainFoldedOracle]
  exact congrArg (packFiniteFunction (ιs i.succ)) (funext (hT i))

omit [Fintype F] [DecidableEq F] [SampleableType F] in
/-- Folded-oracle consistency using the folding challenges read from the paper transcript itself.

This is the challenge-schedule-specialized form needed by the honest Construction 5.1 transcript:
the initial transition uses `T.initialSumcheckChallenge`, and every later transition uses the
previous main-loop `T.mainSumcheckChallenge`. -/
def paperTranscriptHasFoldedOraclesFromTranscript {M : ℕ}
    {ιs : Fin ((M + 1) + 1) → Type}
    [∀ i : Fin ((M + 1) + 1), Fintype (ιs i)] (P : Params ιs F) (d : ℕ)
    (S : ∀ i : Fin ((M + 1) + 1), Finset (ιs i))
    (bridge : PaperFoldDomainBridge P S)
    (hNeg :
      ∀ i : Fin (M + 1), ∀ j : ℕ,
        Neg (BlockRelDistance.indexPowT (S i.castSucc) (P.φ i.castSucc) j))
    (source :
      (i : Fin (M + 1)) →
        BlockRelDistance.indexPowT (S i.castSucc) (P.φ i.castSucc) 0 → F)
    (hFoldLe : ∀ i : Fin (M + 1), P.foldingParam i.castSucc ≤ P.varCount i.castSucc)
    (T : PaperTranscriptData P d) : Prop :=
  paperTranscriptHasFoldedOracles P d S bridge hNeg source
    (paperTranscriptFoldingChallenge P d T) hFoldLe T

omit [Fintype F] [DecidableEq F] [SampleableType F] in
/-- The transcript-derived folding-challenge predicate gives the same folded-oracle payload
equation, with no external folding-challenge schedule left to supply. -/
theorem paperTranscriptSlotPayload_mainFoldedOracle_of_hasFoldedOraclesFromTranscript {M : ℕ}
    {ιs : Fin ((M + 1) + 1) → Type}
    [∀ i : Fin ((M + 1) + 1), Fintype (ιs i)] (P : Params ιs F) (d : ℕ)
    (S : ∀ i : Fin ((M + 1) + 1), Finset (ιs i))
    (bridge : PaperFoldDomainBridge P S)
    (hNeg :
      ∀ i : Fin (M + 1), ∀ j : ℕ,
        Neg (BlockRelDistance.indexPowT (S i.castSucc) (P.φ i.castSucc) j))
    (source :
      (i : Fin (M + 1)) →
        BlockRelDistance.indexPowT (S i.castSucc) (P.φ i.castSucc) 0 → F)
    (hFoldLe : ∀ i : Fin (M + 1), P.foldingParam i.castSucc ≤ P.varCount i.castSucc)
    (T : PaperTranscriptData P d)
    (hT : paperTranscriptHasFoldedOraclesFromTranscript P d S bridge hNeg source hFoldLe T)
    (i : Fin (M + 1)) :
    paperTranscriptSlotPayload P d T (.mainFoldedOracle i) =
      packFiniteFunction (ιs i.succ)
        (paperFoldedOracleFrom P S bridge hNeg source
          (paperTranscriptFoldingChallenge P d T) hFoldLe i) :=
  paperTranscriptSlotPayload_mainFoldedOracle_of_hasFoldedOracles P d S bridge hNeg source
    (paperTranscriptFoldingChallenge P d T) hFoldLe T hT i

omit [SampleableType F] in
/-- Polynomial-extension consistency for the main-loop out-of-domain replies. -/
structure PaperOutOfDomainExtension {M : ℕ} {ιs : Fin (M + 1) → Type}
    [∀ i : Fin (M + 1), Fintype (ιs i)] (P : Params ιs F) (d : ℕ)
    (T : PaperTranscriptData P d) where
  extensionPolynomial : Fin M → Polynomial F
  agreesWithFoldedOracle :
    ∀ i : Fin M, ∀ x : ιs i.succ,
      (extensionPolynomial i).eval (P.φ i.succ x) = T.mainFoldedOracle i x
  reply_eq_eval :
    ∀ i : Fin M,
      T.mainOutOfDomainReply i =
        (extensionPolynomial i).eval (T.mainOutOfDomainChallenge i)

omit [Fintype F] [DecidableEq F] [SampleableType F] in
@[simp] theorem paperOutOfDomainExtension_reply {M : ℕ}
    {ιs : Fin (M + 1) → Type} [∀ i : Fin (M + 1), Fintype (ιs i)]
    (P : Params ιs F) (d : ℕ) (T : PaperTranscriptData P d)
    (ext : PaperOutOfDomainExtension P d T) (i : Fin M) :
    T.mainOutOfDomainReply i =
      (ext.extensionPolynomial i).eval (T.mainOutOfDomainChallenge i) :=
  ext.reply_eq_eval i

omit [Fintype F] [DecidableEq F] [SampleableType F] in
/-- Under OOD-extension consistency, the named OOD-reply payload is the singleton vector containing
the extension polynomial's evaluation at the named OOD challenge. -/
theorem paperTranscriptSlotPayload_mainOutOfDomainReply_of_extension {M : ℕ}
    {ιs : Fin (M + 1) → Type} [∀ i : Fin (M + 1), Fintype (ιs i)]
    (P : Params ιs F) (d : ℕ) (T : PaperTranscriptData P d)
    (ext : PaperOutOfDomainExtension P d T) (i : Fin M) :
    paperTranscriptSlotPayload P d T (.mainOutOfDomainReply i) =
      singletonFieldPayload
        ((ext.extensionPolynomial i).eval (T.mainOutOfDomainChallenge i)) := by
  rw [paperTranscriptSlotPayload_mainOutOfDomainReply, ext.reply_eq_eval i]

omit [Fintype F] [SampleableType F] in
/-- Interpret the final coefficient vector from the paper transcript as a univariate polynomial. -/
noncomputable def paperFinalPolynomialAsPolynomial {M : ℕ}
    {ιs : Fin (M + 1) → Type} [∀ i : Fin (M + 1), Fintype (ιs i)]
    (P : Params ιs F) (d : ℕ) (T : PaperTranscriptData P d) : Polynomial F :=
  polynomialOfCoeffs T.finalPolynomial

omit [Fintype F] [SampleableType F] in
@[simp] theorem paperFinalPolynomialAsPolynomial_coeff {M : ℕ}
    {ιs : Fin (M + 1) → Type} [∀ i : Fin (M + 1), Fintype (ιs i)]
    (P : Params ιs F) (d : ℕ) (T : PaperTranscriptData P d)
    (k : Fin (2 ^ P.varCount (Fin.last M))) :
    (paperFinalPolynomialAsPolynomial P d T).coeff k = T.finalPolynomial k := by
  simpa [paperFinalPolynomialAsPolynomial, Fin.liftF'] using
    congrFun (coeff_polynomialOfCoeffs_eq_coeffs (coeffs := T.finalPolynomial)) k

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] in
@[simp] theorem paperTranscriptSlotPayload_finalPolynomial {M : ℕ}
    {ιs : Fin (M + 1) → Type} [∀ i : Fin (M + 1), Fintype (ιs i)]
    (P : Params ιs F) (d : ℕ) (T : PaperTranscriptData P d) :
    paperTranscriptSlotPayload P d T .finalPolynomial =
      Vector.ofFn T.finalPolynomial :=
  rfl

omit [Fintype F] [SampleableType F] in
/-- The named final-polynomial payload is the coefficient vector of the polynomial interpretation
of the transcript's final polynomial message. -/
theorem paperTranscriptSlotPayload_finalPolynomial_of_coefficients {M : ℕ}
    {ιs : Fin (M + 1) → Type} [∀ i : Fin (M + 1), Fintype (ιs i)]
    (P : Params ιs F) (d : ℕ) (T : PaperTranscriptData P d) :
    paperTranscriptSlotPayload P d T .finalPolynomial =
      Vector.ofFn fun k : Fin (2 ^ P.varCount (Fin.last M)) =>
        (paperFinalPolynomialAsPolynomial P d T).coeff k := by
  rw [paperTranscriptSlotPayload_finalPolynomial]
  ext k
  simp [paperFinalPolynomialAsPolynomial, Fin.liftF]

omit [SampleableType F] in
/-- Coefficient consistency for the final polynomial that Construction 5.1 sends before the final
randomness checks. -/
structure PaperFinalPolynomialCoefficients {M : ℕ}
    {ιs : Fin (M + 1) → Type} [∀ i : Fin (M + 1), Fintype (ιs i)]
    (P : Params ιs F) (d : ℕ) (T : PaperTranscriptData P d) where
  polynomial : Polynomial F
  coeff_eq :
    ∀ k : Fin (2 ^ P.varCount (Fin.last M)),
      polynomial.coeff k = T.finalPolynomial k

omit [Fintype F] [SampleableType F] in
/-- The canonical final-polynomial coefficient witness obtained by interpreting the transcript's
coefficient vector with ArkLib's polynomial interface. -/
noncomputable def paperFinalPolynomialCoefficientsOfTranscript {M : ℕ}
    {ιs : Fin (M + 1) → Type} [∀ i : Fin (M + 1), Fintype (ιs i)]
    (P : Params ιs F) (d : ℕ) (T : PaperTranscriptData P d) :
    PaperFinalPolynomialCoefficients P d T where
  polynomial := paperFinalPolynomialAsPolynomial P d T
  coeff_eq := paperFinalPolynomialAsPolynomial_coeff P d T

omit [Fintype F] [DecidableEq F] [SampleableType F] in
/-- Under final-polynomial coefficient consistency, the named payload is exactly the coefficient
vector of the supplied final polynomial. -/
theorem paperTranscriptSlotPayload_finalPolynomial_of_coefficientsWitness {M : ℕ}
    {ιs : Fin (M + 1) → Type} [∀ i : Fin (M + 1), Fintype (ιs i)]
    (P : Params ιs F) (d : ℕ) (T : PaperTranscriptData P d)
    (final : PaperFinalPolynomialCoefficients P d T) :
    paperTranscriptSlotPayload P d T .finalPolynomial =
      Vector.ofFn fun k : Fin (2 ^ P.varCount (Fin.last M)) => final.polynomial.coeff k := by
  rw [paperTranscriptSlotPayload_finalPolynomial]
  apply Vector.ext
  intro k hk
  simp
  exact (final.coeff_eq ⟨k, hk⟩).symm

omit [Fintype F] [DecidableEq F] [SampleableType F] in
/-- Evaluation of the supplied final polynomial at one final-randomness challenge coordinate. -/
noncomputable def paperFinalRandomnessEvaluation {M : ℕ}
    {ιs : Fin (M + 1) → Type} [∀ i : Fin (M + 1), Fintype (ιs i)]
    (P : Params ιs F) (d : ℕ) (T : PaperTranscriptData P d)
    (final : PaperFinalPolynomialCoefficients P d T)
    (j : Fin (P.repeatParam (Fin.last M))) : F :=
  final.polynomial.eval (T.finalRandomness.get j)

omit [Fintype F] [DecidableEq F] [SampleableType F] in
/-- Vector of final-polynomial evaluations at all final-randomness challenge coordinates. -/
noncomputable def paperFinalRandomnessEvaluations {M : ℕ}
    {ιs : Fin (M + 1) → Type} [∀ i : Fin (M + 1), Fintype (ιs i)]
    (P : Params ιs F) (d : ℕ) (T : PaperTranscriptData P d)
    (final : PaperFinalPolynomialCoefficients P d T) :
    Vector F (P.repeatParam (Fin.last M)) :=
  Vector.ofFn fun j => paperFinalRandomnessEvaluation P d T final j

omit [Fintype F] [DecidableEq F] [SampleableType F] in
@[simp] theorem paperFinalRandomnessEvaluations_get {M : ℕ}
    {ιs : Fin (M + 1) → Type} [∀ i : Fin (M + 1), Fintype (ιs i)]
    (P : Params ιs F) (d : ℕ) (T : PaperTranscriptData P d)
    (final : PaperFinalPolynomialCoefficients P d T)
    (j : Fin (P.repeatParam (Fin.last M))) :
    (paperFinalRandomnessEvaluations P d T final).get j =
      paperFinalRandomnessEvaluation P d T final j := by
  simp [paperFinalRandomnessEvaluations]

omit [Fintype F] [SampleableType F] in
/-- Final-randomness evaluations for the canonical polynomial reconstructed from transcript
coefficients. -/
noncomputable def paperFinalRandomnessEvaluationsOfTranscript {M : ℕ}
    {ιs : Fin (M + 1) → Type} [∀ i : Fin (M + 1), Fintype (ιs i)]
    (P : Params ιs F) (d : ℕ) (T : PaperTranscriptData P d) :
    Vector F (P.repeatParam (Fin.last M)) :=
  paperFinalRandomnessEvaluations P d T (paperFinalPolynomialCoefficientsOfTranscript P d T)

omit [Fintype F] [SampleableType F] in
@[simp] theorem paperFinalRandomnessEvaluationsOfTranscript_get {M : ℕ}
    {ιs : Fin (M + 1) → Type} [∀ i : Fin (M + 1), Fintype (ιs i)]
    (P : Params ιs F) (d : ℕ) (T : PaperTranscriptData P d)
    (j : Fin (P.repeatParam (Fin.last M))) :
    (paperFinalRandomnessEvaluationsOfTranscript P d T).get j =
      (paperFinalPolynomialAsPolynomial P d T).eval (T.finalRandomness.get j) := by
  simp [paperFinalRandomnessEvaluationsOfTranscript, paperFinalRandomnessEvaluation,
    paperFinalPolynomialCoefficientsOfTranscript]

omit [Fintype F] [DecidableEq F] [SampleableType F] in
/-- Algebraic consistency data for one paper-order WHIR transcript.

This bundles the three transcript facts that an honest Construction 5.1 prover must establish
before the verifier can run the fold/OOD/final checks: folded-oracle messages are transported
`Fold.fold_k` outputs, OOD replies are evaluations of the extension polynomials, and the final
polynomial payload is the coefficient vector of the polynomial used for final-randomness checks. -/
structure PaperTranscriptAlgebraicConsistency {M : ℕ}
    {ιs : Fin (M + 1) → Type} [∀ i : Fin (M + 1), Fintype (ιs i)]
    (P : Params ιs F) (d : ℕ) (S : ∀ i : Fin (M + 1), Finset (ιs i))
    (bridge : PaperFoldDomainBridge P S)
    (hNeg :
      ∀ i : Fin M, ∀ j : ℕ,
        Neg (BlockRelDistance.indexPowT (S i.castSucc) (P.φ i.castSucc) j))
    (source :
      (i : Fin M) →
        BlockRelDistance.indexPowT (S i.castSucc) (P.φ i.castSucc) 0 → F)
    (foldChallenge : (i : Fin M) → Fin (P.foldingParam i.castSucc) → F)
    (hFoldLe : ∀ i : Fin M, P.foldingParam i.castSucc ≤ P.varCount i.castSucc)
    (T : PaperTranscriptData P d) where
  folded_oracles :
    paperTranscriptHasFoldedOracles P d S bridge hNeg source foldChallenge hFoldLe T
  ood_extension : PaperOutOfDomainExtension P d T
  final_polynomial : PaperFinalPolynomialCoefficients P d T

omit [Fintype F] [DecidableEq F] [SampleableType F] in
/-- Final-randomness evaluations supplied by a bundled algebraically consistent transcript. -/
noncomputable def paperTranscriptAlgebraicConsistencyFinalEvaluations {M : ℕ}
    {ιs : Fin (M + 1) → Type} [∀ i : Fin (M + 1), Fintype (ιs i)]
    (P : Params ιs F) (d : ℕ) (S : ∀ i : Fin (M + 1), Finset (ιs i))
    (bridge : PaperFoldDomainBridge P S)
    (hNeg :
      ∀ i : Fin M, ∀ j : ℕ,
        Neg (BlockRelDistance.indexPowT (S i.castSucc) (P.φ i.castSucc) j))
    (source :
      (i : Fin M) →
        BlockRelDistance.indexPowT (S i.castSucc) (P.φ i.castSucc) 0 → F)
    (foldChallenge : (i : Fin M) → Fin (P.foldingParam i.castSucc) → F)
    (hFoldLe : ∀ i : Fin M, P.foldingParam i.castSucc ≤ P.varCount i.castSucc)
    (T : PaperTranscriptData P d)
    (cons :
      PaperTranscriptAlgebraicConsistency P d S bridge hNeg source foldChallenge hFoldLe T) :
    Vector F (P.repeatParam (Fin.last M)) :=
  paperFinalRandomnessEvaluations P d T cons.final_polynomial

omit [Fintype F] [DecidableEq F] [SampleableType F] in
@[simp] theorem paperTranscriptAlgebraicConsistencyFinalEvaluations_get {M : ℕ}
    {ιs : Fin (M + 1) → Type} [∀ i : Fin (M + 1), Fintype (ιs i)]
    (P : Params ιs F) (d : ℕ) (S : ∀ i : Fin (M + 1), Finset (ιs i))
    (bridge : PaperFoldDomainBridge P S)
    (hNeg :
      ∀ i : Fin M, ∀ j : ℕ,
        Neg (BlockRelDistance.indexPowT (S i.castSucc) (P.φ i.castSucc) j))
    (source :
      (i : Fin M) →
        BlockRelDistance.indexPowT (S i.castSucc) (P.φ i.castSucc) 0 → F)
    (foldChallenge : (i : Fin M) → Fin (P.foldingParam i.castSucc) → F)
    (hFoldLe : ∀ i : Fin M, P.foldingParam i.castSucc ≤ P.varCount i.castSucc)
    (T : PaperTranscriptData P d)
    (cons :
      PaperTranscriptAlgebraicConsistency P d S bridge hNeg source foldChallenge hFoldLe T)
    (j : Fin (P.repeatParam (Fin.last M))) :
    (paperTranscriptAlgebraicConsistencyFinalEvaluations P d S bridge hNeg source foldChallenge
      hFoldLe T cons).get j =
      cons.final_polynomial.polynomial.eval (T.finalRandomness.get j) := by
  simp [paperTranscriptAlgebraicConsistencyFinalEvaluations, paperFinalRandomnessEvaluation]

omit [Fintype F] [DecidableEq F] [SampleableType F] in
/-- A bundled transcript consistency witness exposes the folded-oracle payload equation. -/
theorem paperTranscriptSlotPayload_mainFoldedOracle_of_algebraicConsistency {M : ℕ}
    {ιs : Fin (M + 1) → Type} [∀ i : Fin (M + 1), Fintype (ιs i)]
    (P : Params ιs F) (d : ℕ) (S : ∀ i : Fin (M + 1), Finset (ιs i))
    (bridge : PaperFoldDomainBridge P S)
    (hNeg :
      ∀ i : Fin M, ∀ j : ℕ,
        Neg (BlockRelDistance.indexPowT (S i.castSucc) (P.φ i.castSucc) j))
    (source :
      (i : Fin M) →
        BlockRelDistance.indexPowT (S i.castSucc) (P.φ i.castSucc) 0 → F)
    (foldChallenge : (i : Fin M) → Fin (P.foldingParam i.castSucc) → F)
    (hFoldLe : ∀ i : Fin M, P.foldingParam i.castSucc ≤ P.varCount i.castSucc)
    (T : PaperTranscriptData P d)
    (cons :
      PaperTranscriptAlgebraicConsistency P d S bridge hNeg source foldChallenge hFoldLe T)
    (i : Fin M) :
    paperTranscriptSlotPayload P d T (.mainFoldedOracle i) =
      packFiniteFunction (ιs i.succ)
        (paperFoldedOracleFrom P S bridge hNeg source foldChallenge hFoldLe i) :=
  paperTranscriptSlotPayload_mainFoldedOracle_of_hasFoldedOracles P d S bridge hNeg source
    foldChallenge hFoldLe T cons.folded_oracles i

omit [Fintype F] [DecidableEq F] [SampleableType F] in
/-- A bundled transcript consistency witness exposes the OOD-reply payload equation. -/
theorem paperTranscriptSlotPayload_mainOutOfDomainReply_of_algebraicConsistency {M : ℕ}
    {ιs : Fin (M + 1) → Type} [∀ i : Fin (M + 1), Fintype (ιs i)]
    (P : Params ιs F) (d : ℕ) (S : ∀ i : Fin (M + 1), Finset (ιs i))
    (bridge : PaperFoldDomainBridge P S)
    (hNeg :
      ∀ i : Fin M, ∀ j : ℕ,
        Neg (BlockRelDistance.indexPowT (S i.castSucc) (P.φ i.castSucc) j))
    (source :
      (i : Fin M) →
        BlockRelDistance.indexPowT (S i.castSucc) (P.φ i.castSucc) 0 → F)
    (foldChallenge : (i : Fin M) → Fin (P.foldingParam i.castSucc) → F)
    (hFoldLe : ∀ i : Fin M, P.foldingParam i.castSucc ≤ P.varCount i.castSucc)
    (T : PaperTranscriptData P d)
    (cons :
      PaperTranscriptAlgebraicConsistency P d S bridge hNeg source foldChallenge hFoldLe T)
    (i : Fin M) :
    paperTranscriptSlotPayload P d T (.mainOutOfDomainReply i) =
      singletonFieldPayload
        ((cons.ood_extension.extensionPolynomial i).eval (T.mainOutOfDomainChallenge i)) :=
  paperTranscriptSlotPayload_mainOutOfDomainReply_of_extension P d T cons.ood_extension i

omit [Fintype F] [DecidableEq F] [SampleableType F] in
/-- A bundled transcript consistency witness exposes the final-polynomial payload equation. -/
theorem paperTranscriptSlotPayload_finalPolynomial_of_algebraicConsistency {M : ℕ}
    {ιs : Fin (M + 1) → Type} [∀ i : Fin (M + 1), Fintype (ιs i)]
    (P : Params ιs F) (d : ℕ) (S : ∀ i : Fin (M + 1), Finset (ιs i))
    (bridge : PaperFoldDomainBridge P S)
    (hNeg :
      ∀ i : Fin M, ∀ j : ℕ,
        Neg (BlockRelDistance.indexPowT (S i.castSucc) (P.φ i.castSucc) j))
    (source :
      (i : Fin M) →
        BlockRelDistance.indexPowT (S i.castSucc) (P.φ i.castSucc) 0 → F)
    (foldChallenge : (i : Fin M) → Fin (P.foldingParam i.castSucc) → F)
    (hFoldLe : ∀ i : Fin M, P.foldingParam i.castSucc ≤ P.varCount i.castSucc)
    (T : PaperTranscriptData P d)
    (cons :
      PaperTranscriptAlgebraicConsistency P d S bridge hNeg source foldChallenge hFoldLe T) :
    paperTranscriptSlotPayload P d T .finalPolynomial =
      Vector.ofFn fun k : Fin (2 ^ P.varCount (Fin.last M)) =>
        cons.final_polynomial.polynomial.coeff k :=
  paperTranscriptSlotPayload_finalPolynomial_of_coefficientsWitness P d T cons.final_polynomial

/-! ### Semantic WHIR per-round transcript slots

Construction 5.1 has real prover-message slots: a folded-function oracle / sumcheck message and an
out-of-domain answer, paired with the folding and out-of-domain/shift verifier challenges.  The
existing `whirVectorSpec` below is still the minimal all-challenge budget skeleton required by the
current `whir_rbr_soundness` statement.  These semantic indices record the faithful per-round shape
that the eventual `VectorIOP` constructor must refine into ArkLib's `ProtocolSpec.VectorSpec`.
-/

/-- The two prover-message roles in each WHIR round of the Construction 5.1 skeleton. -/
abbrev RoundMessageKind := Fin 2

namespace RoundMessageKind

/-- The folded-function oracle / sumcheck-message role. -/
def foldedOracle : RoundMessageKind := 0

/-- The out-of-domain answer role. -/
def outOfDomainReply : RoundMessageKind := 1

end RoundMessageKind

/-- The two verifier-challenge roles in each WHIR round of the Construction 5.1 skeleton. -/
abbrev RoundChallengeKind := Fin 2

namespace RoundChallengeKind

/-- The folding challenge role. -/
def folding : RoundChallengeKind := 0

/-- The out-of-domain or shift challenge role. -/
def outOfDomainOrShift : RoundChallengeKind := 1

end RoundChallengeKind

/-- Semantic WHIR prover-message indices: two prover-originated slots per round. -/
abbrev semanticMessageIdx (M : ℕ) := Fin (M + 1) × RoundMessageKind

/-- Semantic WHIR verifier-challenge indices: two verifier-originated slots per round. -/
abbrev semanticChallengeIdx (M : ℕ) := Fin (M + 1) × RoundChallengeKind

/-- Construction 5.1 contributes exactly `2 * M + 2` semantic verifier challenges. -/
theorem semanticChallengeIdx_card (M : ℕ) :
    Fintype.card (semanticChallengeIdx M) = 2 * M + 2 := by
  simp [semanticChallengeIdx, RoundChallengeKind]
  rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm M 2]

/-- A concrete finite indexing for semantic WHIR verifier-challenge roles. -/
noncomputable def semanticChallengeIdxEquivFin (M : ℕ) :
    semanticChallengeIdx M ≃ Fin (2 * M + 2) :=
  Fintype.equivFinOfCardEq (semanticChallengeIdx_card M)

/-- The semantic WHIR skeleton has the same number of prover-message slots as verifier challenges. -/
theorem semanticMessageIdx_card (M : ℕ) :
    Fintype.card (semanticMessageIdx M) = 2 * M + 2 := by
  simp [semanticMessageIdx, RoundMessageKind]
  rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm M 2]

/-- A concrete finite indexing for semantic WHIR prover-message roles. -/
noncomputable def semanticMessageIdxEquivFin (M : ℕ) :
    semanticMessageIdx M ≃ Fin (2 * M + 2) :=
  Fintype.equivFinOfCardEq (semanticMessageIdx_card M)

/-! ### A WHIR `VectorSpec` with real prover-message slots

The all-challenge `whirVectorSpec` below is the exact shape currently consumed by
`whir_rbr_soundness`.  The next construction layer is a bona fide ArkLib `VectorSpec` with both
prover-message and verifier-challenge indices.  We keep the prover-message block first and the
challenge block second; interleaving those slots into the exact paper transcript order is a later
transport/equivalence brick.
-/

/-- A block-ordered WHIR vector protocol shape with `2*M+2` prover messages followed by
`2*M+2` verifier challenges.  Every payload is represented as one field element for this skeleton;
the eventual Construction 5.1 `VectorIOP` will refine the message payload meanings. -/
@[reducible]
def whirBlockVectorSpec (M : ℕ) :
    ProtocolSpec.VectorSpec ((2 * M + 2) + (2 * M + 2)) where
  dir := fun i => if i.1 < 2 * M + 2 then Direction.P_to_V else Direction.V_to_P
  length := fun _ => 1

/-- Challenge indices of the block-ordered WHIR skeleton are the second block. -/
def whirBlockVectorSpec_challengeIdxEquivFin (M : ℕ) :
    (whirBlockVectorSpec M).ChallengeIdx ≃ Fin (2 * M + 2) where
  toFun i := ⟨i.1.1 - (2 * M + 2), by
    have hiUpper : i.1.1 < (2 * M + 2) + (2 * M + 2) := i.1.2
    have hnot : ¬ i.1.1 < 2 * M + 2 := by
      intro hlt
      have hv := i.2
      simp [whirBlockVectorSpec, hlt] at hv
    omega⟩
  invFun j := ⟨⟨(2 * M + 2) + j.1, by omega⟩, by
    have hnot : ¬ (2 * M + 2) + j.1 < 2 * M + 2 := by omega
    simp [hnot]⟩
  left_inv i := by
    ext
    have hiUpper : i.1.1 < (2 * M + 2) + (2 * M + 2) := i.1.2
    have hnot : ¬ i.1.1 < 2 * M + 2 := by
      intro hlt
      have hv := i.2
      simp [whirBlockVectorSpec, hlt] at hv
    simp
    omega
  right_inv j := by
    ext
    simp

/-- Prover-message indices of the block-ordered WHIR skeleton are the first block. -/
def whirBlockVectorSpec_messageIdxEquivFin (M : ℕ) :
    (whirBlockVectorSpec M).MessageIdx ≃ Fin (2 * M + 2) where
  toFun i := ⟨i.1.1, by
    by_cases hlt : i.1.1 < 2 * M + 2
    · exact hlt
    · have hv := i.2
      simp [whirBlockVectorSpec, hlt] at hv⟩
  invFun j := ⟨⟨j.1, by omega⟩, by
    have hlt : j.1 < 2 * M + 2 := j.2
    simp [hlt]⟩
  left_inv i := by
    ext
    simp
  right_inv j := by
    ext
    simp

/-- The block-ordered WHIR skeleton has the expected challenge budget. -/
theorem whirBlockVectorSpec_card_challengeIdx (M : ℕ) :
    Fintype.card (whirBlockVectorSpec M).ChallengeIdx = 2 * M + 2 := by
  rw [Fintype.card_congr (whirBlockVectorSpec_challengeIdxEquivFin M)]
  simp

/-- The block-ordered WHIR skeleton has the expected prover-message budget. -/
theorem whirBlockVectorSpec_card_messageIdx (M : ℕ) :
    Fintype.card (whirBlockVectorSpec M).MessageIdx = 2 * M + 2 := by
  rw [Fintype.card_congr (whirBlockVectorSpec_messageIdxEquivFin M)]
  simp

/-- Every verifier-challenge payload in the block-ordered WHIR skeleton has length one. -/
theorem whirBlockVectorSpec_challengeLength (M : ℕ)
    (i : (whirBlockVectorSpec M).ChallengeIdx) :
    (whirBlockVectorSpec M).challengeLength i = 1 := by
  rfl

/-- Every prover-message payload in the block-ordered WHIR skeleton has length one. -/
theorem whirBlockVectorSpec_messageLength (M : ℕ)
    (i : (whirBlockVectorSpec M).MessageIdx) :
    (whirBlockVectorSpec M).messageLength i = 1 := by
  rfl

/-- The total verifier-challenge payload length of the block-ordered WHIR skeleton is `2*M+2`. -/
theorem whirBlockVectorSpec_totalChallengeLength (M : ℕ) :
    (whirBlockVectorSpec M).totalChallengeLength = 2 * M + 2 := by
  classical
  rw [ProtocolSpec.VectorSpec.totalChallengeLength]
  trans Fintype.card (whirBlockVectorSpec M).ChallengeIdx
  · simp [whirBlockVectorSpec_challengeLength]
  · exact whirBlockVectorSpec_card_challengeIdx M

/-- The total prover-message payload length of the block-ordered WHIR skeleton is `2*M+2`. -/
theorem whirBlockVectorSpec_totalMessageLength (M : ℕ) :
    (whirBlockVectorSpec M).totalMessageLength = 2 * M + 2 := by
  classical
  rw [ProtocolSpec.VectorSpec.totalMessageLength]
  trans Fintype.card (whirBlockVectorSpec M).MessageIdx
  · simp [whirBlockVectorSpec_messageLength]
  · exact whirBlockVectorSpec_card_messageIdx M

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] in
/-- Converted `ProtocolSpec` challenge indices of the block-ordered WHIR skeleton are the second
block. -/
def whirBlockVectorSpec_toProtocolSpec_challengeIdxEquivFin (M : ℕ) :
    ((whirBlockVectorSpec M).toProtocolSpec F).ChallengeIdx ≃ Fin (2 * M + 2) :=
  whirBlockVectorSpec_challengeIdxEquivFin M

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] in
/-- Converted `ProtocolSpec` prover-message indices of the block-ordered WHIR skeleton are the
first block. -/
def whirBlockVectorSpec_toProtocolSpec_messageIdxEquivFin (M : ℕ) :
    ((whirBlockVectorSpec M).toProtocolSpec F).MessageIdx ≃ Fin (2 * M + 2) :=
  whirBlockVectorSpec_messageIdxEquivFin M

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] in
/-- The converted block-ordered WHIR skeleton has the expected challenge budget. -/
theorem whirBlockVectorSpec_toProtocolSpec_card_challengeIdx (M : ℕ) :
    Fintype.card (((whirBlockVectorSpec M).toProtocolSpec F).ChallengeIdx) = 2 * M + 2 := by
  rw [Fintype.card_congr
    (whirBlockVectorSpec_toProtocolSpec_challengeIdxEquivFin (F := F) M)]
  simp

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] in
/-- The converted block-ordered WHIR skeleton has the expected prover-message budget. -/
theorem whirBlockVectorSpec_toProtocolSpec_card_messageIdx (M : ℕ) :
    Fintype.card (((whirBlockVectorSpec M).toProtocolSpec F).MessageIdx) = 2 * M + 2 := by
  rw [Fintype.card_congr
    (whirBlockVectorSpec_toProtocolSpec_messageIdxEquivFin (F := F) M)]
  simp

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] in
@[simp] theorem whirBlockVectorSpec_toProtocolSpec_challengeIdxEquivFin_apply (M : ℕ)
    (i : ((whirBlockVectorSpec M).toProtocolSpec F).ChallengeIdx) :
    whirBlockVectorSpec_toProtocolSpec_challengeIdxEquivFin (F := F) M i =
      whirBlockVectorSpec_challengeIdxEquivFin M i :=
  rfl

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] in
@[simp] theorem whirBlockVectorSpec_toProtocolSpec_challengeIdxEquivFin_symm_apply (M : ℕ)
    (i : Fin (2 * M + 2)) :
    (whirBlockVectorSpec_toProtocolSpec_challengeIdxEquivFin (F := F) M).symm i =
      (whirBlockVectorSpec_challengeIdxEquivFin M).symm i :=
  rfl

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] in
@[simp] theorem whirBlockVectorSpec_toProtocolSpec_messageIdxEquivFin_apply (M : ℕ)
    (i : ((whirBlockVectorSpec M).toProtocolSpec F).MessageIdx) :
    whirBlockVectorSpec_toProtocolSpec_messageIdxEquivFin (F := F) M i =
      whirBlockVectorSpec_messageIdxEquivFin M i :=
  rfl

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] in
@[simp] theorem whirBlockVectorSpec_toProtocolSpec_messageIdxEquivFin_symm_apply (M : ℕ)
    (i : Fin (2 * M + 2)) :
    (whirBlockVectorSpec_toProtocolSpec_messageIdxEquivFin (F := F) M).symm i =
      (whirBlockVectorSpec_messageIdxEquivFin M).symm i :=
  rfl

/-! ### The WHIR protocol-spec direction vector

WHIR runs `M + 1` rounds; each round contributes **two** verifier challenges (the folding
challenge and the out-of-domain / shift challenge).  We model the whole interaction with `2*M+2`
challenge slots, all `V_to_P`.  This is the minimal `VectorSpec` whose `ChallengeIdx` cardinality
and total challenge length are exactly `2 * M + 2`, matching the `whir_rbr_soundness` requirement
`Fintype.card vPSpec.ChallengeIdx = 2 * M + 2`.  The full
`2 P_to_V`/`2 V_to_P`-per-round WHIR interleaving is the faithful refinement of this skeleton; the
challenge budget — the load-bearing datum the soundness statement quantifies over — is realised
exactly here. -/
@[reducible]
def whirVectorSpec (M : ℕ) : ProtocolSpec.VectorSpec (2 * M + 2) where
  dir := fun _ => Direction.V_to_P
  length := fun _ => 1

/-- The protocol spec has exactly `2 * M + 2` verifier challenges. -/
theorem whirVectorSpec_card_challengeIdx (M : ℕ) :
    Fintype.card (whirVectorSpec M).ChallengeIdx = 2 * M + 2 := by
  classical
  -- `ChallengeIdx` is the subtype of `Fin (2*M+2)` with `dir i = V_to_P`, which is everything.
  change Fintype.card {i : Fin (2 * M + 2) // Direction.V_to_P = Direction.V_to_P} =
    2 * M + 2
  simp

/-- Challenge slots in the all-challenge WHIR scratch `VectorSpec` are exactly
`Fin (2 * M + 2)`. -/
def whirVectorSpec_challengeIdxEquivFin (M : ℕ) :
    (whirVectorSpec M).ChallengeIdx ≃ Fin (2 * M + 2) where
  toFun i := i.1
  invFun i := ⟨i, rfl⟩
  left_inv := by
    intro i
    cases i
    rfl
  right_inv := by
    intro i
    rfl

@[simp] theorem whirVectorSpec_challengeIdxEquivFin_apply (M : ℕ)
    (i : (whirVectorSpec M).ChallengeIdx) :
    whirVectorSpec_challengeIdxEquivFin M i = i.1 :=
  rfl

@[simp] theorem whirVectorSpec_challengeIdxEquivFin_symm_apply (M : ℕ)
    (i : Fin (2 * M + 2)) :
    (whirVectorSpec_challengeIdxEquivFin M).symm i = ⟨i, rfl⟩ :=
  rfl

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] in
/-- There are **no** prover messages in `whirVectorSpec`: every slot is a challenge. -/
theorem whirVectorSpec_messageIdx_isEmpty (M : ℕ) :
    IsEmpty ((whirVectorSpec M).toProtocolSpec F).MessageIdx := by
  constructor
  rintro ⟨i, hi⟩
  -- `dir i = P_to_V` but every dir is `V_to_P`.
  change Direction.V_to_P = Direction.P_to_V at hi
  cases hi

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] in
/-- The protocol spec has no prover-message indices. -/
theorem whirVectorSpec_card_messageIdx (M : ℕ) :
    Fintype.card (((whirVectorSpec M).toProtocolSpec F).MessageIdx) = 0 := by
  exact Fintype.card_eq_zero_iff.mpr (whirVectorSpec_messageIdx_isEmpty (F := F) M)

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] in
/-- Message indices in the converted WHIR scratch `ProtocolSpec` are exactly `Fin 0`. -/
noncomputable def whirVectorSpec_toProtocolSpec_messageIdxEquivFin (M : ℕ) :
    ((whirVectorSpec M).toProtocolSpec F).MessageIdx ≃ Fin 0 :=
  Fintype.equivFinOfCardEq (whirVectorSpec_card_messageIdx (F := F) M)

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] in
/-- The converted protocol spec has the same `2 * M + 2` verifier-challenge indices. -/
theorem whirVectorSpec_toProtocolSpec_card_challengeIdx (M : ℕ) :
    Fintype.card (((whirVectorSpec M).toProtocolSpec F).ChallengeIdx) = 2 * M + 2 := by
  classical
  change Fintype.card {i : Fin (2 * M + 2) // Direction.V_to_P = Direction.V_to_P} =
    2 * M + 2
  simp

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] in
/-- Challenge slots in the converted WHIR scratch `ProtocolSpec` are exactly
`Fin (2 * M + 2)`. -/
def whirVectorSpec_toProtocolSpec_challengeIdxEquivFin (M : ℕ) :
    ((whirVectorSpec M).toProtocolSpec F).ChallengeIdx ≃ Fin (2 * M + 2) where
  toFun i := i.1
  invFun i := ⟨i, rfl⟩
  left_inv := by
    intro i
    cases i
    rfl
  right_inv := by
    intro i
    rfl

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] in
@[simp] theorem whirVectorSpec_toProtocolSpec_challengeIdxEquivFin_apply (M : ℕ)
    (i : ((whirVectorSpec M).toProtocolSpec F).ChallengeIdx) :
    whirVectorSpec_toProtocolSpec_challengeIdxEquivFin (F := F) M i = i.1 :=
  rfl

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] in
@[simp] theorem whirVectorSpec_toProtocolSpec_challengeIdxEquivFin_symm_apply (M : ℕ)
    (i : Fin (2 * M + 2)) :
    (whirVectorSpec_toProtocolSpec_challengeIdxEquivFin (F := F) M).symm i = ⟨i, rfl⟩ :=
  rfl

/-! ### WHIR RBR budget accounting adapters

`ArkLib.ProofSystem.Whir.RbrBudgetAccounting` proves the `max'`/`sup` budget facts in an
abstract `fp : Fin (M + 1) → ℕ` setting.  The adapters below instantiate that accounting to the
actual WHIR parameter record `P.foldingParam`, so downstream soundness proofs can cite the named
budget API instead of re-opening the inline `whir_rbr_soundness` expression.
-/

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [Fintype ι] [DecidableEq ι] [Nonempty ι] in
/-- The concrete WHIR RBR per-challenge budget, instantiated from
`Issue113WHIR.epsRbr` with `fp = P.foldingParam`. -/
noncomputable def whirRbrBudgetValue {M : ℕ} {ιs : Fin (M + 1) → Type}
    (P : Params ιs F)
    (ε_fold : (i : Fin (M + 1)) → Fin (P.foldingParam i) → ℝ≥0)
    (ε_out : Fin (M + 1) → ℝ≥0) (ε_shift : Fin M → ℝ≥0) (ε_fin : ℝ≥0) : ℝ≥0 :=
  Issue113WHIR.epsRbr (fp := P.foldingParam) ε_fold ε_out ε_shift ε_fin

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [Fintype ι] [DecidableEq ι] [Nonempty ι] in
/-- The final-round error is dominated by the concrete WHIR RBR budget. -/
theorem whirRbrBudgetValue_fin_le {M : ℕ} {ιs : Fin (M + 1) → Type}
    (P : Params ιs F)
    (ε_fold : (i : Fin (M + 1)) → Fin (P.foldingParam i) → ℝ≥0)
    (ε_out : Fin (M + 1) → ℝ≥0) (ε_shift : Fin M → ℝ≥0) (ε_fin : ℝ≥0) :
    ε_fin ≤ whirRbrBudgetValue P ε_fold ε_out ε_shift ε_fin :=
  Issue113WHIR.eps_fin_le_epsRbr (fp := P.foldingParam) ε_fold ε_out ε_shift ε_fin

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [Fintype ι] [DecidableEq ι] [Nonempty ι] in
/-- Every OOD-round error is dominated by the concrete WHIR RBR budget. -/
theorem whirRbrBudgetValue_out_le {M : ℕ} {ιs : Fin (M + 1) → Type}
    (P : Params ιs F)
    (ε_fold : (i : Fin (M + 1)) → Fin (P.foldingParam i) → ℝ≥0)
    (ε_out : Fin (M + 1) → ℝ≥0) (ε_shift : Fin M → ℝ≥0) (ε_fin : ℝ≥0)
    (i : Fin (M + 1)) :
    ε_out i ≤ whirRbrBudgetValue P ε_fold ε_out ε_shift ε_fin :=
  Issue113WHIR.eps_out_le_epsRbr (fp := P.foldingParam) ε_fold ε_out ε_shift ε_fin i

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [Fintype ι] [DecidableEq ι] [Nonempty ι] in
/-- Every shift-round error is dominated by the concrete WHIR RBR budget. -/
theorem whirRbrBudgetValue_shift_le {M : ℕ} {ιs : Fin (M + 1) → Type}
    (P : Params ιs F)
    (ε_fold : (i : Fin (M + 1)) → Fin (P.foldingParam i) → ℝ≥0)
    (ε_out : Fin (M + 1) → ℝ≥0) (ε_shift : Fin M → ℝ≥0) (ε_fin : ℝ≥0)
    (i : Fin M) :
    ε_shift i ≤ whirRbrBudgetValue P ε_fold ε_out ε_shift ε_fin :=
  Issue113WHIR.eps_shift_le_epsRbr (fp := P.foldingParam) ε_fold ε_out ε_shift ε_fin i

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [Fintype ι] [DecidableEq ι] [Nonempty ι] in
/-- Every inner fold-step error is dominated by the concrete WHIR RBR budget. -/
theorem whirRbrBudgetValue_fold_le {M : ℕ} {ιs : Fin (M + 1) → Type}
    (P : Params ιs F)
    (ε_fold : (i : Fin (M + 1)) → Fin (P.foldingParam i) → ℝ≥0)
    (ε_out : Fin (M + 1) → ℝ≥0) (ε_shift : Fin M → ℝ≥0) (ε_fin : ℝ≥0)
    (i : Fin (M + 1)) (j : Fin (P.foldingParam i)) :
    ε_fold i j ≤ whirRbrBudgetValue P ε_fold ε_out ε_shift ε_fin :=
  Issue113WHIR.eps_fold_le_epsRbr (fp := P.foldingParam) ε_fold ε_out ε_shift ε_fin i j

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [Fintype ι] [DecidableEq ι] [Nonempty ι] in
/-- Universal-property package for the concrete WHIR RBR budget. -/
theorem whirRbrBudgetValue_isLUB {M : ℕ} {ιs : Fin (M + 1) → Type}
    (P : Params ιs F)
    (ε_fold : (i : Fin (M + 1)) → Fin (P.foldingParam i) → ℝ≥0)
    (ε_out : Fin (M + 1) → ℝ≥0) (ε_shift : Fin M → ℝ≥0) (ε_fin : ℝ≥0) :
    (∀ i j, ε_fold i j ≤ whirRbrBudgetValue P ε_fold ε_out ε_shift ε_fin) ∧
    (∀ i, ε_out i ≤ whirRbrBudgetValue P ε_fold ε_out ε_shift ε_fin) ∧
    (∀ i, ε_shift i ≤ whirRbrBudgetValue P ε_fold ε_out ε_shift ε_fin) ∧
    (ε_fin ≤ whirRbrBudgetValue P ε_fold ε_out ε_shift ε_fin) ∧
    (∀ c, (∀ i j, ε_fold i j ≤ c) → (∀ i, ε_out i ≤ c) → (∀ i, ε_shift i ≤ c) →
      ε_fin ≤ c → whirRbrBudgetValue P ε_fold ε_out ε_shift ε_fin ≤ c) :=
  Issue113WHIR.epsRbr_isLUB (fp := P.foldingParam) ε_fold ε_out ε_shift ε_fin

omit [Fintype ι] [Nonempty ι] in
/-- Using the named WHIR RBR budget in `IsSecureWithGap` is definitionally the same as using the
inline `ε_rbr` expression from `whir_rbr_soundness`. -/
theorem whirSecureWithGap_namedBudget_iff_inline {M : ℕ}
    {ιs : Fin (M + 1) → Type} [∀ i : Fin (M + 1), Fintype (ιs i)]
    {P : Params ιs F} {m_0 : ℕ} [Smooth (P.φ 0)] [Nonempty (ιs 0)]
    {δ : ℝ≥0} {n : ℕ} {vPSpec : ProtocolSpec.VectorSpec n}
    (π : VectorIOP Unit (OracleStatement (ιs 0) F) Unit vPSpec F)
    (ε_fold : (i : Fin (M + 1)) → Fin (P.foldingParam i) → ℝ≥0)
    (ε_out : Fin (M + 1) → ℝ≥0) (ε_shift : Fin M → ℝ≥0) (ε_fin : ℝ≥0) :
    VectorIOP.IsSecureWithGap (whirRelation m_0 (P.φ 0) 0)
      (whirRelation m_0 (P.φ 0) δ)
      (fun _ : vPSpec.ChallengeIdx => whirRbrBudgetValue P ε_fold ε_out ε_shift ε_fin) π ↔
    (let max_ε_folds : (i : Fin (M + 1)) → ℝ≥0 :=
        fun i => (Finset.univ : Finset (Fin (P.foldingParam i))).sup (ε_fold i)
      let ε_rbr : vPSpec.ChallengeIdx → ℝ≥0 :=
        fun _ => ((Finset.univ : Finset (Fin (M + 1))).image max_ε_folds ∪ {ε_fin} ∪
          (Finset.univ : Finset (Fin (M + 1))).image ε_out ∪
          (Finset.univ : Finset (Fin M)).image ε_shift).max' (by simp)
      VectorIOP.IsSecureWithGap (whirRelation m_0 (P.φ 0) 0)
        (whirRelation m_0 (P.φ 0) δ) ε_rbr π) := by
  rfl

/-- Every verifier-challenge index has length one in the WHIR scratch vector spec. -/
theorem whirVectorSpec_challengeLength (M : ℕ) (i : (whirVectorSpec M).ChallengeIdx) :
    (whirVectorSpec M).challengeLength i = 1 := by
  rfl

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F] in
/-- Every verifier challenge in the converted WHIR skeleton is a single field element. -/
theorem whirVectorSpec_challenge_eq_vector_one (M : ℕ)
    (i : ((whirVectorSpec M).toProtocolSpec F).ChallengeIdx) :
    ((whirVectorSpec M).toProtocolSpec F).Challenge i = Vector F 1 := by
  simp [ProtocolSpec.Challenge]

/-- The total challenge payload length of the scratch WHIR vector spec is `2 * M + 2`. -/
theorem whirVectorSpec_totalChallengeLength (M : ℕ) :
    (whirVectorSpec M).totalChallengeLength = 2 * M + 2 := by
  classical
  rw [ProtocolSpec.VectorSpec.totalChallengeLength]
  simp [ProtocolSpec.VectorSpec.challengeLength, whirVectorSpec]

/-- The scratch WHIR vector spec has no prover-message payload. -/
theorem whirVectorSpec_totalMessageLength (M : ℕ) :
    (whirVectorSpec M).totalMessageLength = 0 := by
  classical
  rw [ProtocolSpec.VectorSpec.totalMessageLength]
  simp [ProtocolSpec.VectorSpec.messageLength, whirVectorSpec]

instance (M : ℕ) :
    ∀ j, OracleInterface (((whirVectorSpec M).toProtocolSpec F).Message j) :=
  fun j => (whirVectorSpec_messageIdx_isEmpty (F := F) M).elim j

/-! ### `whir_rbr_soundness` existential assembly

The top-level WHIR soundness statement in `RBRSoundness.lean` is an existential over a concrete
`VectorIOP` plus the bundled `IsSecureWithGap` proof and the per-round numeric budget.  The theorem
below proves the final packaging step: once a candidate protocol `π`, its security proof, and the
paper's named fold/out/shift/final inequalities are supplied, the existential statement follows.

This intentionally does **not** construct `π`; it isolates the remaining protocol/completeness/RBR
knowledge-soundness obligation from the now-checked existential and budget assembly. -/
section RBRSoundnessAssembly

variable {M : ℕ}
variable {ιs : Fin (M + 1) → Type} [∀ i : Fin (M + 1), Fintype (ιs i)]

omit [SampleableType F] [Fintype ι] [Nonempty ι] in
/-- Assemble `whir_rbr_soundness` from a concrete WHIR `VectorIOP`, its `IsSecureWithGap` proof,
and the named per-round bounds from Theorem 5.2.

This is the exact downstream witness-introduction step for issue #113.  It keeps the hard residual
honest: callers must still provide the actual Construction 5.1 protocol `π`, prove its perfect
completeness/RBR knowledge soundness via `IsSecureWithGap`, and discharge the fold/OOD/shift/final
numeric inequalities. -/
theorem whir_rbr_soundness_of_secure_gap
    [SampleableType F] {d dstar : ℕ}
    {P : Params ιs F} {S : ∀ i : Fin (M + 1), Finset (ιs i)}
    {hParams : ParamConditions ιs P} {h : GenMutualCorrParams ιs P S}
    {m_0 : ℕ} (hm_0 : m_0 = P.varCount 0) {σ₀ : F}
    {wPoly₀ : MvPolynomial (Fin (m_0 + 1)) F} {δ : ℝ≥0}
    [Smooth (P.φ 0)] [Nonempty (ιs 0)]
    [∀ i : Fin (M + 1), Fact (0 < P.foldingParam i)]
    (ε_fold : (i : Fin (M + 1)) → Fin (P.foldingParam i) → ℝ≥0)
    (ε_out : Fin (M + 1) → ℝ≥0)
    (ε_shift : Fin M → ℝ≥0) (ε_fin : ℝ≥0)
    (h_fold_0 :
        let maxDeg := (Finset.univ : Finset (Fin m_0)).sup (fun i => wPoly₀.degreeOf (Fin.succ i))
        let dstar := 1 + (wPoly₀.degreeOf 0) + maxDeg
        let _ : ∀ j : Fin ((P.foldingParam 0) + 1),
          Fintype (BlockRelDistance.indexPowT (S 0) (P.φ 0) j) := h.inst1 0
        let _ : ∀ j : Fin ((P.foldingParam 0) + 1),
          Nonempty (BlockRelDistance.indexPowT (S 0) (P.φ 0) j) := h.inst2 0
        ∀ j : Fin ((P.foldingParam 0) + 1),
          let errStar_0 j := h.errStar 0 j (h.C 0 j) (h.Gen_α 0 j).parℓ (h.δ 0)
        ∀ j : Fin (P.foldingParam 0),
          ε_fold 0 j ≤ ((dstar * (h.dist 0 j.castSucc)) / Fintype.card F) + (errStar_0 j.succ))
    (h_out :
        ∀ i : Fin (M + 1),
          ε_out i ≤
            2^(P.varCount i) * (h.dist i 0)^2 / (2 * Fintype.card F))
    (h_shift :
        ∀ i : Fin M,
          ε_shift i ≤ (1 - (h.δ i.castSucc))^(P.repeatParam i.castSucc)
            + ((h.dist i.succ 0) * (P.repeatParam i.castSucc) + 1) / Fintype.card F)
    (h_fold_i :
        let maxDeg := (Finset.univ : Finset (Fin m_0)).sup (fun i => wPoly₀.degreeOf (Fin.succ i))
        let dstar := 1 + (wPoly₀.degreeOf 0) + maxDeg
        let d := max dstar 3
        let _ : ∀ i : Fin (M + 1), ∀ j : Fin ((P.foldingParam i) + 1),
          Fintype (BlockRelDistance.indexPowT (S i) (P.φ i) j) := h.inst1
        let _ : ∀ i : Fin (M + 1), ∀ j : Fin ((P.foldingParam i) + 1),
          Nonempty (BlockRelDistance.indexPowT (S i) (P.φ i) j) := h.inst2
        ∀ i : Fin (M + 1), ∀ j : Fin ((P.foldingParam i) + 1),
          let errStar i j := h.errStar i j (h.C i j) (h.Gen_α i j).parℓ (h.δ i)
        ∀ i : Fin (M + 1), ∀ j : Fin (P.foldingParam i),
          ε_fold i j ≤ d * (h.dist i j.castSucc) / Fintype.card F + errStar i j.succ)
    (h_fin :
        ε_fin ≤ (1 - h.δ (Fin.last M))^(P.repeatParam (Fin.last M)))
    {n : ℕ} {vPSpec : ProtocolSpec.VectorSpec n}
    (hChallengeCard : Fintype.card (vPSpec.ChallengeIdx) = 2 * M + 2)
    (π : VectorIOP Unit (OracleStatement (ιs 0) F) Unit vPSpec F)
    (hSecure :
      let max_ε_folds : (i : Fin (M + 1)) → ℝ≥0 :=
        fun i => (Finset.univ : Finset (Fin (P.foldingParam i))).sup (ε_fold i)
      let ε_rbr : vPSpec.ChallengeIdx → ℝ≥0 :=
        fun _ => (Finset.univ.image max_ε_folds ∪ {ε_fin} ∪ Finset.univ.image ε_out ∪
          Finset.univ.image ε_shift).max' (by simp)
      VectorIOP.IsSecureWithGap (whirRelation m_0 (P.φ 0) 0)
        (whirRelation m_0 (P.φ 0) (h.δ 0)) ε_rbr π) :
    whir_rbr_soundness (F := F) (M := M) ιs (d := d) (dstar := dstar)
      (P := P) (S := S) (hParams := hParams) (h := h)
      hm_0 (σ₀ := σ₀) (wPoly₀ := wPoly₀) (δ := δ)
      ε_fold ε_out ε_shift ε_fin h_fold_0 h_out h_shift h_fold_i h_fin := by
  refine ⟨n, vPSpec, hChallengeCard, π, ?_⟩
  exact hSecure

omit [Fintype ι] [Nonempty ι] in
/-- Assemble `whir_rbr_soundness` using the checked scratch WHIR `VectorSpec`.

This specializes `whir_rbr_soundness_of_secure_gap` to `whirVectorSpec M`, so callers of the
scratch construction no longer have to pass the challenge-cardinality witness manually.  It remains
purely downstream plumbing: callers still supply the concrete WHIR `VectorIOP`, its
`IsSecureWithGap` proof, and the paper budget inequalities. -/
theorem whir_rbr_soundness_of_whirVectorSpec_secure_gap
    [SampleableType F] {d dstar : ℕ}
    {P : Params ιs F} {S : ∀ i : Fin (M + 1), Finset (ιs i)}
    {hParams : ParamConditions ιs P} {h : GenMutualCorrParams ιs P S}
    {m_0 : ℕ} (hm_0 : m_0 = P.varCount 0) {σ₀ : F}
    {wPoly₀ : MvPolynomial (Fin (m_0 + 1)) F} {δ : ℝ≥0}
    [Smooth (P.φ 0)] [Nonempty (ιs 0)]
    [∀ i : Fin (M + 1), Fact (0 < P.foldingParam i)]
    (ε_fold : (i : Fin (M + 1)) → Fin (P.foldingParam i) → ℝ≥0)
    (ε_out : Fin (M + 1) → ℝ≥0)
    (ε_shift : Fin M → ℝ≥0) (ε_fin : ℝ≥0)
    (h_fold_0 :
        let maxDeg := (Finset.univ : Finset (Fin m_0)).sup (fun i => wPoly₀.degreeOf (Fin.succ i))
        let dstar := 1 + (wPoly₀.degreeOf 0) + maxDeg
        let _ : ∀ j : Fin ((P.foldingParam 0) + 1),
          Fintype (BlockRelDistance.indexPowT (S 0) (P.φ 0) j) := h.inst1 0
        let _ : ∀ j : Fin ((P.foldingParam 0) + 1),
          Nonempty (BlockRelDistance.indexPowT (S 0) (P.φ 0) j) := h.inst2 0
        ∀ j : Fin ((P.foldingParam 0) + 1),
          let errStar_0 j := h.errStar 0 j (h.C 0 j) (h.Gen_α 0 j).parℓ (h.δ 0)
        ∀ j : Fin (P.foldingParam 0),
          ε_fold 0 j ≤ ((dstar * (h.dist 0 j.castSucc)) / Fintype.card F) + (errStar_0 j.succ))
    (h_out :
        ∀ i : Fin (M + 1),
          ε_out i ≤
            2^(P.varCount i) * (h.dist i 0)^2 / (2 * Fintype.card F))
    (h_shift :
        ∀ i : Fin M,
          ε_shift i ≤ (1 - (h.δ i.castSucc))^(P.repeatParam i.castSucc)
            + ((h.dist i.succ 0) * (P.repeatParam i.castSucc) + 1) / Fintype.card F)
    (h_fold_i :
        let maxDeg := (Finset.univ : Finset (Fin m_0)).sup (fun i => wPoly₀.degreeOf (Fin.succ i))
        let dstar := 1 + (wPoly₀.degreeOf 0) + maxDeg
        let d := max dstar 3
        let _ : ∀ i : Fin (M + 1), ∀ j : Fin ((P.foldingParam i) + 1),
          Fintype (BlockRelDistance.indexPowT (S i) (P.φ i) j) := h.inst1
        let _ : ∀ i : Fin (M + 1), ∀ j : Fin ((P.foldingParam i) + 1),
          Nonempty (BlockRelDistance.indexPowT (S i) (P.φ i) j) := h.inst2
        ∀ i : Fin (M + 1), ∀ j : Fin ((P.foldingParam i) + 1),
          let errStar i j := h.errStar i j (h.C i j) (h.Gen_α i j).parℓ (h.δ i)
        ∀ i : Fin (M + 1), ∀ j : Fin (P.foldingParam i),
          ε_fold i j ≤ d * (h.dist i j.castSucc) / Fintype.card F + errStar i j.succ)
    (h_fin :
        ε_fin ≤ (1 - h.δ (Fin.last M))^(P.repeatParam (Fin.last M)))
    (π : VectorIOP Unit (OracleStatement (ιs 0) F) Unit (whirVectorSpec M) F)
    (hSecure :
      let max_ε_folds : (i : Fin (M + 1)) → ℝ≥0 :=
        fun i => (Finset.univ : Finset (Fin (P.foldingParam i))).sup (ε_fold i)
      let ε_rbr : (whirVectorSpec M).ChallengeIdx → ℝ≥0 :=
        fun _ => (Finset.univ.image max_ε_folds ∪ {ε_fin} ∪ Finset.univ.image ε_out ∪
          Finset.univ.image ε_shift).max' (by simp)
      VectorIOP.IsSecureWithGap (whirRelation m_0 (P.φ 0) 0)
        (whirRelation m_0 (P.φ 0) (h.δ 0)) ε_rbr π) :
    whir_rbr_soundness (F := F) (M := M) ιs (d := d) (dstar := dstar)
      (P := P) (S := S) (hParams := hParams) (h := h)
      hm_0 (σ₀ := σ₀) (wPoly₀ := wPoly₀) (δ := δ)
      ε_fold ε_out ε_shift ε_fin h_fold_0 h_out h_shift h_fold_i h_fin := by
  refine ⟨2 * M + 2, whirVectorSpec M, whirVectorSpec_card_challengeIdx M, π, ?_⟩
  exact hSecure

end RBRSoundnessAssembly

#print axioms whirVectorSpec_card_challengeIdx
#print axioms paperTranscriptSlotDirection
#print axioms paperTranscriptSlotLength
#print axioms whirPaperTranscriptVectorSpec
#print axioms whirPaperTranscriptVectorSpec_dir
#print axioms whirPaperTranscriptVectorSpec_length
#print axioms packFiniteFunction
#print axioms unpackFiniteFunction
#print axioms unpack_packFiniteFunction
#print axioms pack_unpackFiniteFunction
#print axioms paperTranscriptSlotIndex
#print axioms paperTranscriptSlotIndex_symm_apply
#print axioms paperMessageIdx
#print axioms paperChallengeIdx
#print axioms mainFoldedOracleMessageIdx
#print axioms finalPolynomialMessageIdx
#print axioms singletonFieldPayload
#print axioms initialSumcheckMessagePayload
#print axioms initialSumcheckChallengePayload
#print axioms mainFoldedOraclePayload
#print axioms mainOutOfDomainChallengePayload
#print axioms mainOutOfDomainReplyPayload
#print axioms mainShiftChallengePayload
#print axioms mainSumcheckMessagePayload
#print axioms mainSumcheckChallengePayload
#print axioms finalPolynomialPayload
#print axioms finalRandomnessChallengePayload
#print axioms paperTranscriptSlotPayload
#print axioms paperTranscriptFullTranscript
#print axioms paperTranscriptMessage
#print axioms paperTranscriptChallenge
#print axioms paperTranscriptRuntimeFullTranscript
#print axioms paperTranscriptRuntimeFullTranscript_messages
#print axioms paperTranscriptRuntimeFullTranscript_challenges
#print axioms paperTranscriptSlotPayload_mainFoldedOracle
#print axioms paperTranscriptSlotPayload_mainOutOfDomainReply
#print axioms paperTranscriptSlotPayload_mainShiftChallenge
#print axioms paperTranscriptOracleProver
#print axioms paperTranscriptOracleVerifier
#print axioms paperTranscriptVectorIOP
#print axioms paperTranscriptVectorIOP_isSecureWithGap_of_complete_and_rbr
#print axioms paperTranscriptFoldingChallenge
#print axioms paperTranscriptFoldingChallenge_zero
#print axioms paperTranscriptFoldingChallenge_succ
#print axioms PaperFoldDomainBridge
#print axioms PaperInputDomainBridge
#print axioms paperInputDomainBridge_sourceDomainEquiv_apply
#print axioms paperInputSourceFromOracle
#print axioms paperInputSourceFromOracle_apply
#print axioms paperFoldDomainBridge_nextDomainEquiv_apply
#print axioms paperFoldedOracleFrom
#print axioms paperFoldedOracleFrom_apply
#print axioms paperTranscriptHasFoldedOracles
#print axioms paperTranscriptSlotPayload_mainFoldedOracle_of_hasFoldedOracles
#print axioms paperTranscriptHasFoldedOraclesFromTranscript
#print axioms paperTranscriptSlotPayload_mainFoldedOracle_of_hasFoldedOraclesFromTranscript
#print axioms PaperOutOfDomainExtension
#print axioms paperOutOfDomainExtension_reply
#print axioms paperTranscriptSlotPayload_mainOutOfDomainReply_of_extension
#print axioms paperFinalPolynomialAsPolynomial
#print axioms paperFinalPolynomialAsPolynomial_coeff
#print axioms paperTranscriptSlotPayload_finalPolynomial
#print axioms paperTranscriptSlotPayload_finalPolynomial_of_coefficients
#print axioms PaperFinalPolynomialCoefficients
#print axioms paperFinalPolynomialCoefficientsOfTranscript
#print axioms paperTranscriptSlotPayload_finalPolynomial_of_coefficientsWitness
#print axioms paperFinalRandomnessEvaluation
#print axioms paperFinalRandomnessEvaluations
#print axioms paperFinalRandomnessEvaluations_get
#print axioms paperFinalRandomnessEvaluationsOfTranscript
#print axioms paperFinalRandomnessEvaluationsOfTranscript_get
#print axioms PaperTranscriptAlgebraicConsistency
#print axioms paperTranscriptAlgebraicConsistencyFinalEvaluations
#print axioms paperTranscriptAlgebraicConsistencyFinalEvaluations_get
#print axioms paperTranscriptSlotPayload_mainFoldedOracle_of_algebraicConsistency
#print axioms paperTranscriptSlotPayload_mainOutOfDomainReply_of_algebraicConsistency
#print axioms paperTranscriptSlotPayload_finalPolynomial_of_algebraicConsistency
#print axioms whirVectorSpec_challengeIdxEquivFin
#print axioms whirVectorSpec_challengeIdxEquivFin_apply
#print axioms whirVectorSpec_challengeIdxEquivFin_symm_apply
#print axioms whirVectorSpec_messageIdx_isEmpty
#print axioms whirVectorSpec_card_messageIdx
#print axioms whirVectorSpec_toProtocolSpec_messageIdxEquivFin
#print axioms whirVectorSpec_toProtocolSpec_card_challengeIdx
#print axioms whirVectorSpec_toProtocolSpec_challengeIdxEquivFin
#print axioms whirVectorSpec_toProtocolSpec_challengeIdxEquivFin_apply
#print axioms whirVectorSpec_toProtocolSpec_challengeIdxEquivFin_symm_apply
#print axioms whirRbrBudgetValue
#print axioms whirRbrBudgetValue_fin_le
#print axioms whirRbrBudgetValue_out_le
#print axioms whirRbrBudgetValue_shift_le
#print axioms whirRbrBudgetValue_fold_le
#print axioms whirRbrBudgetValue_isLUB
#print axioms whirSecureWithGap_namedBudget_iff_inline
#print axioms whirVectorSpec_challengeLength
#print axioms whirVectorSpec_challenge_eq_vector_one
#print axioms whirVectorSpec_totalChallengeLength
#print axioms whirVectorSpec_totalMessageLength
#print axioms whir_rbr_soundness_of_secure_gap
#print axioms semanticChallengeIdx_card
#print axioms semanticChallengeIdxEquivFin
#print axioms semanticMessageIdx_card
#print axioms semanticMessageIdxEquivFin
#print axioms whirBlockVectorSpec_challengeIdxEquivFin
#print axioms whirBlockVectorSpec_messageIdxEquivFin
#print axioms whirBlockVectorSpec_card_challengeIdx
#print axioms whirBlockVectorSpec_card_messageIdx
#print axioms whirBlockVectorSpec_challengeLength
#print axioms whirBlockVectorSpec_messageLength
#print axioms whirBlockVectorSpec_totalChallengeLength
#print axioms whirBlockVectorSpec_totalMessageLength
#print axioms whirBlockVectorSpec_toProtocolSpec_challengeIdxEquivFin
#print axioms whirBlockVectorSpec_toProtocolSpec_messageIdxEquivFin
#print axioms whirBlockVectorSpec_toProtocolSpec_card_challengeIdx
#print axioms whirBlockVectorSpec_toProtocolSpec_card_messageIdx
#print axioms whirBlockVectorSpec_toProtocolSpec_challengeIdxEquivFin_apply
#print axioms whirBlockVectorSpec_toProtocolSpec_challengeIdxEquivFin_symm_apply
#print axioms whirBlockVectorSpec_toProtocolSpec_messageIdxEquivFin_apply
#print axioms whirBlockVectorSpec_toProtocolSpec_messageIdxEquivFin_symm_apply
#print axioms whir_rbr_soundness_of_whirVectorSpec_secure_gap

end Construction

end WhirIOP
