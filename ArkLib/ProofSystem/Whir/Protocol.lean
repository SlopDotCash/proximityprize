import ArkLib.ToMathlib.WhirBricksConstruction

/-!
# Placeholder WHIR `VectorIOP`

`whirVectorIOP` packages `whirMakeTranscript` and `whirVerify` through the paper-slot adapter
`paperTranscriptVectorIOP`.  Both are placeholders: the transcript generator ignores its input and
emits the all-zero transcript, and the verifier ignores its challenges, the input oracle and the
prover messages and accepts every transcript (`pure true`).  So `whirVectorIOP` does not implement
the WHIR checks of Construction 5.1, and no theorem establishes sub-unit soundness for it: the
declarations below only name its security propositions and package supplied proofs.  Perfect
completeness is proved in `ProtocolCompleteness.lean`; the only proved RBR statement is the
indicator budget with total error one (`WhirIOP.whirVectorIOP_rbrKnowledgeSoundness_indicator`,
`ProtocolSoundness.lean`).  The checking verifier `Whir302Checked.whirVerifyChecked`
(`CheckedVerifier.lean`) makes real checks but never queries the input oracle
(`CheckedObliviousness.lean`).
-/

open MvPolynomial
open WhirIOP
open WhirIOP.Construction
open scoped NNReal

/-- Placeholder transcript generator: ignores its input and returns the all-zero
`PaperTranscriptData`. -/
noncomputable def whirMakeTranscript {F : Type} [Field F] [Fintype F] [DecidableEq F]
    [SampleableType F] {M : ℕ} {ιs : Fin (M + 1) → Type}
    [∀ i : Fin (M + 1), Fintype (ιs i)] (P : Params ιs F) (d : ℕ) :
    (Unit × (∀ u : Unit, OracleStatement (ιs 0) F u)) × Unit → PaperTranscriptData P d :=
  fun _ => {
    initialSumcheckMessage := fun _ => Vector.replicate d 0
    initialSumcheckChallenge := fun _ => 0
    mainFoldedOracle := fun _ _ => 0
    mainOutOfDomainChallenge := fun _ => 0
    mainOutOfDomainReply := fun _ => 0
    mainShiftChallenge := fun i => Vector.replicate (P.repeatParam i.succ) 0
    mainSumcheckMessage := fun _ _ => Vector.replicate d 0
    mainSumcheckChallenge := fun _ _ => 0
    finalPolynomial := fun _ => 0
    finalRandomness := Vector.replicate (P.repeatParam (Fin.last M)) 0
  }

/-- Placeholder verifier logic: ignores the statement, every challenge, the input oracle and the
prover messages, and accepts (`pure true`). -/
noncomputable def whirVerify {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    {M : ℕ} {ιs : Fin (M + 1) → Type}
    [∀ i : Fin (M + 1), Fintype (ιs i)] (P : Params ιs F) (d : ℕ) :
    Unit → ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F).Challenges →
        OptionT
          (OracleComp
            ([]ₒ +
              ([OracleStatement (ιs 0) F]ₒ +
                [((whirPaperTranscriptVectorSpec P d).toProtocolSpec F).Message]ₒ)))
          Bool :=
  fun _ _ => pure true

/-- The placeholder WHIR-shaped `VectorIOP` built from `whirMakeTranscript` and `whirVerify`.  It
does not implement the WHIR checks of Construction 5.1. -/
noncomputable def whirVectorIOP {F : Type} [Field F] [Fintype F] [DecidableEq F]
    [SampleableType F] {M : ℕ}
    {ιs : Fin (M + 1) → Type} [∀ i : Fin (M + 1), Fintype (ιs i)]
    (P : Params ιs F) (d : ℕ) :
    VectorIOP Unit (OracleStatement (ιs 0) F) Unit (whirPaperTranscriptVectorSpec P d) F :=
  paperTranscriptVectorIOP P d (whirMakeTranscript P d) (whirVerify P d)

/-- Perfect completeness of the placeholder `whirVectorIOP` (immediate for an always-accepting
verifier; proved as `Whir302.whirVectorIOP_perfectCompleteness_holds` in
`ProtocolCompleteness.lean`). -/
def whirVectorIOP_perfectCompleteness {F : Type} [Field F] [Fintype F] [DecidableEq F]
    [SampleableType F] {M : ℕ}
    {ιs : Fin (M + 1) → Type} [∀ i : Fin (M + 1), Fintype (ιs i)]
    (P : Params ιs F) (d : ℕ) {m0 : ℕ} [ReedSolomon.Smooth (P.φ 0)]
    [Nonempty (ιs 0)] :
    Prop :=
  (whirVectorIOP P d).perfectCompleteness (pure ()) isEmptyElim
    (whirRelation m0 (P.φ 0) 0)

/-- Round-by-round knowledge soundness of the placeholder `whirVectorIOP` at budget `εRbr`.  This
is not a WHIR soundness obligation: `whirVerify` accepts every transcript, so this can hold only
at budgets whose per-challenge errors sum to at least one when a δ-far input exists.  The proved
instance is the indicator budget with value `1` at the final randomness challenge
(`whirVectorIOP_rbrKnowledgeSoundness_indicator`, `ProtocolSoundness.lean`). -/
def whirVectorIOP_rbrKnowledgeSoundness {F : Type} [Field F] [Fintype F] [DecidableEq F]
    [SampleableType F] {M : ℕ}
    {ιs : Fin (M + 1) → Type} [∀ i : Fin (M + 1), Fintype (ιs i)]
    (P : Params ιs F) (d : ℕ) {m0 : ℕ} [ReedSolomon.Smooth (P.φ 0)]
    [Nonempty (ιs 0)] (δ : ℝ≥0)
    (εRbr : (whirPaperTranscriptVectorSpec P d).ChallengeIdx → ℝ≥0) :
    Prop :=
  OracleProof.rbrKnowledgeSoundness (pure ()) isEmptyElim
    (whirRelation m0 (P.φ 0) δ)
      (OracleProof.toOracleVerifier (whirVectorIOP P d)) εRbr

/-- The two security legs (`IsSecureWithGap`) of the placeholder `whirVectorIOP` at budget
`εRbr`, with the same caveat as `whirVectorIOP_rbrKnowledgeSoundness`. -/
def whirVectorIOP_isSecureWithGap {F : Type} [Field F] [Fintype F] [DecidableEq F]
    [SampleableType F] {M : ℕ}
    {ιs : Fin (M + 1) → Type} [∀ i : Fin (M + 1), Fintype (ιs i)]
    (P : Params ιs F) (d : ℕ) {m0 : ℕ} [ReedSolomon.Smooth (P.φ 0)]
    [Nonempty (ιs 0)] (δ : ℝ≥0)
    (εRbr : (whirPaperTranscriptVectorSpec P d).ChallengeIdx → ℝ≥0) :
    Prop :=
  VectorIOP.IsSecureWithGap (whirRelation m0 (P.φ 0) 0) (whirRelation m0 (P.φ 0) δ)
    εRbr (whirVectorIOP P d)

/-- The placeholder `whirVectorIOP` is secure with gap whenever its completeness and RBR soundness
propositions hold (pure packaging). -/
theorem whirVectorIOP_isSecureWithGap_holds {F : Type} [Field F] [Fintype F] [DecidableEq F]
    [SampleableType F] {M : ℕ}
    {ιs : Fin (M + 1) → Type} [∀ i : Fin (M + 1), Fintype (ιs i)]
    (P : Params ιs F) (d : ℕ) {m0 : ℕ} [ReedSolomon.Smooth (P.φ 0)]
    [Nonempty (ιs 0)] (δ : ℝ≥0)
    (εRbr : (whirPaperTranscriptVectorSpec P d).ChallengeIdx → ℝ≥0)
    (hComplete : whirVectorIOP_perfectCompleteness P d (m0 := m0))
    (hSound : whirVectorIOP_rbrKnowledgeSoundness P d δ εRbr (m0 := m0)) :
    whirVectorIOP_isSecureWithGap P d δ εRbr (m0 := m0) :=
  ⟨hComplete, hSound⟩
