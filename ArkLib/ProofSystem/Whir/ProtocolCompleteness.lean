/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.WhirBricksConstruction
import ArkLib.OracleReduction.Completeness
import ArkLib.ProofSystem.Whir.Protocol

open OracleSpec OracleComp ProtocolSpec NNReal WhirIOP WhirIOP.Construction

namespace Whir302

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {M : ℕ} {ιs : Fin (M + 1) → Type} [∀ i : Fin (M + 1), Fintype (ιs i)]

/-! ### Local instances needed by the generic unroll theorem -/

instance : (([]ₒ : OracleSpec PEmpty)).Inhabited where
  inhabited_B i := nomatch i

instance : (([]ₒ : OracleSpec PEmpty)).Fintype where
  fintype_B i := nomatch i

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
    OracleSpec.Fintype
      ([((whirPaperTranscriptVectorSpec P d).toProtocolSpec F).Challenge]ₒ'
        (fun i => challengeOracleInterface i)) where
  fintype_B := fun ⟨i, _⟩ => by
    show Fintype (((whirPaperTranscriptVectorSpec P d).toProtocolSpec F).Challenge i)
    infer_instance

noncomputable instance instChalInhabited (P : Params ιs F) (d : ℕ) :
    OracleSpec.Inhabited
      ([((whirPaperTranscriptVectorSpec P d).toProtocolSpec F).Challenge]ₒ'
        (fun i => challengeOracleInterface i)) where
  inhabited_B := fun ⟨i, _⟩ => by
    show Inhabited (((whirPaperTranscriptVectorSpec P d).toProtocolSpec F).Challenge i)
    infer_instance

/-! ### Statement A: the paper prover's partial run never fails -/

omit [SampleableType F] in
theorem probFailure_runToRound_paperProver (P : Params ιs F) (d : ℕ)
    (mk : (Unit × (∀ u : Unit, OracleStatement (ιs 0) F u)) × Unit → PaperTranscriptData P d)
    (stmt : Unit × (∀ u : Unit, OracleStatement (ιs 0) F u)) (wit : Unit)
    (i : Fin (Fintype.card (PaperTranscriptSlot P) + 1)) :
    Pr[⊥ | (paperTranscriptOracleProver P d mk).runToRound i stmt wit] = 0 :=
  HasEvalPMF.probFailure_eq_zero _

/-! ### Statement B: perfect completeness with the always-accepting verifier -/

/-- Spec-lifting an `OptionT`-level `pure` is `pure` (definitional). -/
private lemma liftComp_optionT_pure {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁}
    {spec₂ : OracleSpec ι₂} [MonadLiftT (OracleQuery spec₁) (OracleQuery spec₂)]
    {α : Type} (y : α) :
    (OracleComp.liftComp (pure y : OptionT (OracleComp spec₁) α) spec₂ :
      OptionT (OracleComp spec₂) α) = pure y := rfl

theorem paperTranscriptVectorIOP_pureTrue_perfectCompleteness (P : Params ιs F) (d : ℕ)
    (mk : (Unit × (∀ u : Unit, OracleStatement (ιs 0) F u)) × Unit → PaperTranscriptData P d)
    (relation : Set ((Unit × ∀ u : Unit, OracleStatement (ιs 0) F u) × Unit)) :
    (paperTranscriptVectorIOP P d mk (fun _ _ => pure true)).perfectCompleteness
      (pure ()) isEmptyElim relation := by
  show OracleReduction.perfectCompleteness (pure ()) isEmptyElim relation acceptRejectOracleRel
    (paperTranscriptVectorIOP P d mk (fun _ _ => pure true))
  rw [OracleReduction.unroll_n_message_reduction_perfectCompleteness
    (reduction := paperTranscriptVectorIOP P d mk (fun _ _ => pure true))
    relation acceptRejectOracleRel (pure ()) isEmptyElim
    (by simp)
    (by intro β q s; exact nomatch q.1)]
  intro stmtIn oStmtIn witIn _h_relIn
  -- The pure-true verifier's lifted verify computation is a `pure`.
  have hverify0 : ∀ transcript, ∃ g : ∀ _ : Empty, Unit,
      (paperTranscriptVectorIOP P d mk (fun _ _ => pure true)).verifier.toVerifier.verify
        (stmtIn, oStmtIn) transcript
      = pure (true, g) := fun _ => ⟨_, rfl⟩
  choose g hverify using hverify0
  have houtput : ∀ state,
      (paperTranscriptVectorIOP P d mk (fun _ _ => pure true)).prover.output state
      = pure ((true, fun e : Empty => nomatch e), ()) := fun _ => rfl
  rw [probEvent_eq_one_iff]
  constructor
  · -- SAFETY: prover run is a plain `OracleComp` (never fails); output and verify are `pure`.
    simp only [houtput, hverify, liftComp_optionT_pure, liftComp_pure, liftM_pure, pure_bind]
    rw [probFailure_bind_eq_zero_iff]
    refine ⟨?_, ?_⟩
    · rw [OptionT.probFailure_liftM]
      exact HasEvalPMF.probFailure_eq_zero _
    · rintro ⟨transcript, state⟩ _
      exact probFailure_pure _
  · -- CORRECTNESS: the unique reachable output accepts.
    intro x hx
    simp only [houtput, hverify, liftComp_optionT_pure, liftComp_pure, liftM_pure, pure_bind,
      support_bind, OptionT.support_liftM, Set.mem_iUnion, exists_prop] at hx
    obtain ⟨⟨transcript, state⟩, _, hx⟩ := hx
    obtain ⟨v, hv, hx⟩ := hx
    simp only [support_pure, Set.mem_singleton_iff] at hx
    subst hx
    replace hv : v ∈ (some ⁻¹'
        ({some (true, g transcript)} : Set (Option (Bool × (Empty → Unit))))) := hv
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Option.some.injEq] at hv
    subst hv
    refine ⟨?_, rfl, Subsingleton.elim _ _⟩
    show _ ∈ acceptRejectOracleRel
    simp only [acceptRejectOracleRel, Set.mem_singleton_iff]

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
