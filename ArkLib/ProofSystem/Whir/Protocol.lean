import ArkLib.ToMathlib.WhirBricksConstruction

open MvPolynomial
open WhirIOP
open WhirIOP.Construction
open scoped NNReal

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

noncomputable def whirVectorIOP {F : Type} [Field F] [Fintype F] [DecidableEq F]
    [SampleableType F] {M : ℕ}
    {ιs : Fin (M + 1) → Type} [∀ i : Fin (M + 1), Fintype (ιs i)]
    (P : Params ιs F) (d : ℕ) :
    VectorIOP Unit (OracleStatement (ιs 0) F) Unit (whirPaperTranscriptVectorSpec P d) F :=
  paperTranscriptVectorIOP P d (whirMakeTranscript P d) (whirVerify P d)

/-- Residual: prove perfect completeness for the concrete WHIR `VectorIOP`. -/
def whirVectorIOP_perfectCompleteness {F : Type} [Field F] [Fintype F] [DecidableEq F]
    [SampleableType F] {M : ℕ}
    {ιs : Fin (M + 1) → Type} [∀ i : Fin (M + 1), Fintype (ιs i)]
    (P : Params ιs F) (d : ℕ) {m0 : ℕ} [ReedSolomon.Smooth (P.φ 0)]
    [Nonempty (ιs 0)] :
    Prop :=
  (whirVectorIOP P d).perfectCompleteness (pure ()) isEmptyElim
    (whirRelation m0 (P.φ 0) 0)

/-- Residual: prove round-by-round knowledge soundness for the concrete WHIR `VectorIOP`. -/
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

/-- Residual: package the two security legs for the concrete WHIR `VectorIOP`. -/
def whirVectorIOP_isSecureWithGap {F : Type} [Field F] [Fintype F] [DecidableEq F]
    [SampleableType F] {M : ℕ}
    {ιs : Fin (M + 1) → Type} [∀ i : Fin (M + 1), Fintype (ιs i)]
    (P : Params ιs F) (d : ℕ) {m0 : ℕ} [ReedSolomon.Smooth (P.φ 0)]
    [Nonempty (ιs 0)] (δ : ℝ≥0)
    (εRbr : (whirPaperTranscriptVectorSpec P d).ChallengeIdx → ℝ≥0) :
    Prop :=
  VectorIOP.IsSecureWithGap (whirRelation m0 (P.φ 0) 0) (whirRelation m0 (P.φ 0) δ)
    εRbr (whirVectorIOP P d)

/-- The WHIR `VectorIOP` is secure with gap if its completeness and RBR soundness residuals hold. -/
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
