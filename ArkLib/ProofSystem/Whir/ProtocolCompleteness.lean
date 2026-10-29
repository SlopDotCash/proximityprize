/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.WhirBricksConstruction
import ArkLib.OracleReduction.Completeness
import ProximityPrize.Compatibility.ConstantOutputCompleteness
import ArkLib.ProofSystem.Whir.Protocol

open OracleSpec OracleComp ProtocolSpec NNReal WhirIOP WhirIOP.Construction

-- The retained finite-oracle API chooses uniform answer measures locally.
private noncomputable local instance (priority := low) whirPaperUniformAnswers
    {κ : Type} {spec : OracleSpec κ}
    [∀ q, Fintype (spec.Range q)] [∀ q, Inhabited (spec.Range q)] :
    OracleSpec.UniformAnswerMeasure spec :=
  OracleSpec.UniformAnswerMeasure.ofFiniteNonempty spec

namespace Whir302

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {M : ℕ} {ιs : Fin (M + 1) → Type} [∀ i : Fin (M + 1), Fintype (ιs i)]

/-! ### Local instances needed by the generic unroll theorem -/



noncomputable local instance : VCVCompatible F :=
  { toFintype := inferInstance, toInhabited := ⟨0⟩ }

/-- Challenge payloads of the paper-order WHIR spec are finite. -/
noncomputable instance (P : Params ιs F) (d : ℕ) :
    ∀ i, Fintype (((whirPaperTranscriptVectorSpec P d).toProtocolSpec F).Challenge i) :=
  fun _ => by dsimp [ProtocolSpec.Challenge]; infer_instance

noncomputable instance (P : Params ιs F) (d : ℕ) :
    ∀ i, Inhabited (((whirPaperTranscriptVectorSpec P d).toProtocolSpec F).Challenge i) :=
  fun _ => by dsimp [ProtocolSpec.Challenge]; infer_instance

noncomputable instance instChalFintype (P : Params ιs F) (d : ℕ) :
    ∀ t, Fintype (([((whirPaperTranscriptVectorSpec P d).toProtocolSpec F).Challenge]ₒ'
        (fun i => challengeOracleInterface i)).Range t) := fun ⟨i, _⟩ => by
    show Fintype (((whirPaperTranscriptVectorSpec P d).toProtocolSpec F).Challenge i)
    infer_instance

noncomputable instance instChalInhabited (P : Params ιs F) (d : ℕ) :
    ∀ t, Inhabited (([((whirPaperTranscriptVectorSpec P d).toProtocolSpec F).Challenge]ₒ'
        (fun i => challengeOracleInterface i)).Range t) := fun ⟨i, _⟩ => by
    show Inhabited (((whirPaperTranscriptVectorSpec P d).toProtocolSpec F).Challenge i)
    infer_instance

/-! ### Statement A: the paper prover's partial run never fails -/

theorem probFailure_runToRound_paperProver (P : Params ιs F) (d : ℕ)
    (mk : (Unit × (∀ u : Unit, OracleStatement (ιs 0) F u)) × Unit → PaperTranscriptData P d)
    (stmt : Unit × (∀ u : Unit, OracleStatement (ιs 0) F u)) (wit : Unit)
    (i : Fin (Fintype.card (PaperTranscriptSlot P) + 1)) :
    probFailure ((paperTranscriptOracleProver P d mk).runToRound i stmt wit) = 0 :=
  OracleComp.prFail_eq_zero _

/-! ### Statement B: perfect completeness with the always-accepting verifier -/

set_option backward.isDefEq.respectTransparency false in
theorem paperTranscriptVectorIOP_pureTrue_perfectCompleteness (P : Params ιs F) (d : ℕ)
    (mk : (Unit × (∀ u : Unit, OracleStatement (ιs 0) F u)) × Unit → PaperTranscriptData P d)
    (relation : Set ((Unit × ∀ u : Unit, OracleStatement (ιs 0) F u) × Unit)) :
    (paperTranscriptVectorIOP P d mk (fun _ _ => pure true)).perfectCompleteness
      (pure ()) isEmptyElim relation := by
  show OracleReduction.perfectCompleteness (Oₛₒ := fun i : Empty => nomatch i)
    (pure ()) isEmptyElim relation acceptRejectOracleRel
    (paperTranscriptVectorIOP P d mk (fun _ _ => pure true))
  unfold OracleReduction.perfectCompleteness
  refine Reduction.perfectCompleteness_of_constant_output _ _ _ _ _
    (true, fun e : Empty => nomatch e) () (fun _ => rfl) ?_ ?_
  · intro stmt tr
    apply OptionT.ext
    simp only [Verifier.run, OracleReduction.toReduction, paperTranscriptVectorIOP,
      paperTranscriptOracleVerifier, OracleProofVerifier.ofVerify, OracleVerifier.toVerifier,
      OptionT.run_pure, simulateQ_pure, LawfulApplicative.map_pure]
    congr 2
  · rfl

/-! ### Wiring: discharge Protocol.lean's perfect-completeness residual

`whirVerify P d` is definitionally `fun _ _ => pure true`, so the concrete WHIR
`VectorIOP` placeholder satisfies its perfect-completeness residual outright. -/

theorem whirVectorIOP_perfectCompleteness_holds (P : Params ιs F) (d : ℕ) {m0 : ℕ}
    [ReedSolomon.Smooth (P.φ 0)] [Nonempty (ιs 0)] :
    whirVectorIOP_perfectCompleteness P d (m0 := m0) :=
  paperTranscriptVectorIOP_pureTrue_perfectCompleteness P d (whirMakeTranscript P d)
    (whirRelation m0 (P.φ 0) 0)

/-- With the completeness leg discharged, `whirVectorIOP_isSecureWithGap` reduces to the
single RBR knowledge-soundness residual. -/
theorem whirVectorIOP_isSecureWithGap_of_rbr (P : Params ιs F) (d : ℕ) {m0 : ℕ}
    [ReedSolomon.Smooth (P.φ 0)] [Nonempty (ιs 0)] (δ : ℝ≥0)
    (εRbr : (whirPaperTranscriptVectorSpec P d).ChallengeIdx → ℝ≥0)
    (hSound : whirVectorIOP_rbrKnowledgeSoundness P d δ εRbr (m0 := m0)) :
    whirVectorIOP_isSecureWithGap P d δ εRbr (m0 := m0) :=
  whirVectorIOP_isSecureWithGap_holds P d δ εRbr
    (whirVectorIOP_perfectCompleteness_holds P d) hSound

end Whir302

#print axioms Whir302.probFailure_runToRound_paperProver
#print axioms Whir302.paperTranscriptVectorIOP_pureTrue_perfectCompleteness
#print axioms Whir302.whirVectorIOP_perfectCompleteness_holds
#print axioms Whir302.whirVectorIOP_isSecureWithGap_of_rbr
