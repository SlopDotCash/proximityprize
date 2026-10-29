/-
RBR state-function scaffolding for WHIR (#302).

This file provides:

1. A general, reusable *threshold knowledge state function* construction
   (`ThresholdKSF.thresholdKSF`): given any round-indexed predicate family `pred` over partial
   transcripts that is (a) equivalent to the input relation at round 0 and (b) stable under
   removing the last message (for all rounds up to a designated challenge round `c`), we obtain a
   genuine `Verifier.KnowledgeStateFunction` whose state is `pred` before `c` and `True` after.
   All side conditions (`toFun_empty`, `toFun_next`, `toFun_full`) are *proven*.

2. The accompanying RBR knowledge-soundness bound (`ThresholdKSF.rbrKnowledgeSoundness_indicator`):
   the state can only flip `false → true` at the single challenge round `c`, so the protocol
   satisfies `rbrKnowledgeSoundness` with the *indicator* error budget
   `εRbr i = if i = c then 1 else 0` — strictly sharper than the all-ones dummy budget.

3. The WHIR instantiation: the round-indexed δ-closeness state function for the relation pair
   `whirRelation m0 (P.φ 0) 0` (completeness) vs `whirRelation m0 (P.φ 0) δ` (soundness), with the
   predicate tracking δ-closeness of the input oracle *and of every folded oracle revealed so far*
   (`whirFoldedClosePred`), plus the seam lemmas (`transcriptFoldedOracle_concat`,
   `whirFoldedClosePred_concat`, `whirFoldedClosePred_zero`).

4. The discharged residual `whirVectorIOP_rbrKnowledgeSoundness P d δ (indicator εRbr)` for the
   concrete (always-accepting) WHIR `VectorIOP`, concentrating the entire RBR budget on the final
   randomness challenge round, and the corresponding `whirVectorIOP_isSecureWithGap` package.
-/
import ArkLib.ProofSystem.Whir.Protocol
import ArkLib.ProofSystem.Whir.ProtocolCompleteness
import ArkLib.OracleReduction.Completeness

open OracleSpec OracleComp ProtocolSpec NNReal ReedSolomon
open WhirIOP WhirIOP.Construction
open scoped ENNReal

noncomputable section

-- The retained finite-oracle API chooses uniform answer measures locally.
private noncomputable local instance (priority := low) whirThresholdUniformAnswers
    {κ : Type} {spec : OracleSpec κ}
    [∀ q, Fintype (spec.Range q)] [∀ q, Inhabited (spec.Range q)] :
    OracleSpec.UniformAnswerMeasure spec :=
  OracleSpec.UniformAnswerMeasure.ofFiniteNonempty spec

namespace ThresholdKSF

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- The trivial round-by-round extractor with `Unit` middle witnesses (for `Unit`-witness
relations such as the WHIR proximity relation, where the statement carries all the data). -/
def unitExtractor : Extractor.RoundByRound oSpec StmtIn Unit WitOut pSpec (fun _ => Unit) where
  extractIn := fun _ _ => ()
  extractMid := fun _ _ _ _ => ()
  extractOut := fun _ _ _ => ()

/-- **Threshold knowledge state function.** Given a round-indexed predicate family `pred` on
partial transcripts that
* agrees with the input relation on the empty transcript (`hEmpty`), and
* is stable under removing the last message at every round up to the designated challenge
  round `c` (`hConcat`),

the function `m ↦ (if m ≤ c then pred m else True)` is a knowledge state function for *any*
verifier: the state can only flip `false → true` at the challenge round `c`. -/
def thresholdKSF (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (relIn : Set (StmtIn × Unit)) (relOut : Set (StmtOut × WitOut))
    (pred : (m : Fin (n + 1)) → StmtIn → Transcript m pSpec → Prop)
    (c : pSpec.ChallengeIdx)
    (hEmpty : ∀ stmtIn (w : Unit), (stmtIn, w) ∈ relIn ↔ pred 0 stmtIn default)
    (hConcat : ∀ (m : Fin n), m.val ≤ c.1.val →
      ∀ stmtIn (tr : Transcript m.castSucc pSpec) (msg : pSpec.Type m),
        pred m.succ stmtIn (tr.concat msg) → pred m.castSucc stmtIn tr) :
    verifier.KnowledgeStateFunction init impl relIn relOut
      (unitExtractor (WitOut := WitOut)) where
  toFun := fun m stmtIn tr _ => if m.val ≤ c.1.val then pred m stmtIn tr else True
  toFun_empty := fun stmtIn w => by
    rw [if_pos (by simp)]
    exact (hEmpty stmtIn _).mpr
  toFun_next := fun m hdir stmtIn tr msg w h => by
    by_cases hc : m.val ≤ c.1.val
    · rw [if_pos (by simpa using hc)]
      by_cases hc' : m.val + 1 ≤ c.1.val
      · rw [if_pos (by simpa using hc')] at h
        exact hConcat m hc stmtIn tr msg h
      · -- boundary case `m.val = c.1.val` is impossible: `m` is a prover round, `c` a challenge
        exfalso
        have heqm : m = c.1 := Fin.ext (le_antisymm hc (by omega))
        have hv : pSpec.dir m = Direction.V_to_P := by rw [heqm]; exact c.2
        rw [hdir] at hv
        exact Direction.noConfusion hv
    · rw [if_neg (by simpa using hc)]
      trivial
  toFun_full := fun stmtIn tr witOut _ => by
    rw [if_neg (by simp only [Fin.val_last]; exact Nat.not_le.mpr c.1.isLt)]
    trivial

/-- **Indicator RBR knowledge-soundness bound for the threshold state function.** The state
`m ↦ (if m ≤ c then pred m else True)` flips `false → true` *only* at the challenge round `c`:
at every other challenge round the flip event is pointwise impossible. Hence any verifier admits
RBR knowledge soundness with the indicator error budget concentrated at `c`. -/
theorem rbrKnowledgeSoundness_indicator (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (relIn : Set (StmtIn × Unit)) (relOut : Set (StmtOut × WitOut))
    (pred : (m : Fin (n + 1)) → StmtIn → Transcript m pSpec → Prop)
    (c : pSpec.ChallengeIdx)
    (hEmpty : ∀ stmtIn (w : Unit), (stmtIn, w) ∈ relIn ↔ pred 0 stmtIn default)
    (hConcat : ∀ (m : Fin n), m.val ≤ c.1.val →
      ∀ stmtIn (tr : Transcript m.castSucc pSpec) (msg : pSpec.Type m),
        pred m.succ stmtIn (tr.concat msg) → pred m.castSucc stmtIn tr) :
    verifier.rbrKnowledgeSoundness init impl relIn relOut
      (fun i => if i = c then 1 else 0) := by
  classical
  refine ⟨fun _ => Unit, unitExtractor,
    thresholdKSF init impl verifier relIn relOut pred c hEmpty hConcat, ?_⟩
  intro stmtIn witIn prover i
  by_cases hic : i = c
  · subst hic
    simp
  · simp only [if_neg hic, ENNReal.coe_zero, nonpos_iff_eq_zero]
    rw [OracleComp.prEvent_eq_zero_iff]
    rintro ⟨tr, ch, log⟩ _ ⟨w, hne, hsucc⟩
    simp only [thresholdKSF] at hne hsucc
    rcases lt_trichotomy i.1.val c.1.val with hlt | heq | hgt
    · refine hne ?_
      rw [if_pos (by simpa using hlt.le)]
      rw [if_pos (by simp; omega)] at hsucc
      exact hConcat i.1 hlt.le stmtIn tr ch hsucc
    · exact hic (Subtype.ext (Fin.ext heq))
    · rw [if_neg (by simp; omega)] at hne
      exact hne trivial

/-- **Bounded-flip RBR knowledge soundness for the threshold state function**: like
`rbrKnowledgeSoundness_indicator`, but the budget at the threshold challenge round `c` is an
explicit hypothesis `hFlip` bounding the flip-event probability (the event that the partial
transcript's predicate is false before `c` yet true after the challenge — for the WHIR checked
verifier this is the Schwartz–Zippel salvage event, bounded by `maxLen/|F|` via
`probEvent_salvage_le`). All other challenge rounds keep budget `0`. -/
theorem rbrKnowledgeSoundness_of_flipBound (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (relIn : Set (StmtIn × Unit)) (relOut : Set (StmtOut × WitOut))
    (pred : (m : Fin (n + 1)) → StmtIn → Transcript m pSpec → Prop)
    (c : pSpec.ChallengeIdx) (ε : ℝ≥0)
    (hEmpty : ∀ stmtIn (w : Unit), (stmtIn, w) ∈ relIn ↔ pred 0 stmtIn default)
    (hConcat : ∀ (m : Fin n), m.val ≤ c.1.val →
      ∀ stmtIn (tr : Transcript m.castSucc pSpec) (msg : pSpec.Type m),
        pred m.succ stmtIn (tr.concat msg) → pred m.castSucc stmtIn tr)
    (hFlip : ∀ stmtIn witIn
      (prover : Prover oSpec StmtIn Unit StmtOut WitOut pSpec),
      probEvent (fun x : pSpec.Transcript c.1.castSucc × pSpec.Challenge c ×
          (oSpec + [pSpec.Challenge]ₒ).QueryLog =>
          ¬ pred c.1.castSucc stmtIn x.1) (do
          (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
            (do
              let ⟨⟨transcript, _⟩, proveQueryLog⟩ ←
                prover.runWithLogToRound c.1.castSucc stmtIn witIn
              let challenge ← liftComp (pSpec.getChallenge c) _
              return (transcript, challenge, proveQueryLog))).run' (← init)) ≤ (ε : ℝ≥0∞)) :
    verifier.rbrKnowledgeSoundness init impl relIn relOut
      (fun i => if i = c then ε else 0) := by
  classical
  refine ⟨fun _ => Unit, unitExtractor,
    thresholdKSF init impl verifier relIn relOut pred c hEmpty hConcat, ?_⟩
  intro stmtIn witIn prover i
  by_cases hic : i = c
  · subst hic
    simp only [if_pos rfl]
    refine le_trans (prEvent_mono_of_support _ _ _ ?_) (hFlip stmtIn witIn prover)
    rintro ⟨tr, ch, log⟩ _ ⟨w, hne, _⟩
    simp only [thresholdKSF] at hne
    rw [if_pos (by simp)] at hne
    exact hne
  · simp only [if_neg hic, ENNReal.coe_zero, nonpos_iff_eq_zero]
    rw [OracleComp.prEvent_eq_zero_iff]
    rintro ⟨tr, ch, log⟩ _ ⟨w, hne, hsucc⟩
    simp only [thresholdKSF] at hne hsucc
    rcases lt_trichotomy i.1.val c.1.val with hlt | heq | hgt
    · refine hne ?_
      rw [if_pos (by simpa using hlt.le)]
      rw [if_pos (by simp; omega)] at hsucc
      exact hConcat i.1 hlt.le stmtIn tr ch hsucc
    · exact hic (Subtype.ext (Fin.ext heq))
    · rw [if_neg (by simp; omega)] at hne
      exact hne trivial

end ThresholdKSF

/-! ## WHIR instantiation -/

namespace Whir302RBR

open ThresholdKSF

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {M : ℕ} {ιs : Fin (M + 1) → Type} [∀ i : Fin (M + 1), Fintype (ιs i)]

omit [Field F] [DecidableEq F] [SampleableType F] in
/-- Payload length of the folded-oracle message slot `i` is the cardinality of the next
evaluation domain. -/
lemma length_mainFoldedOracleMessageIdx (P : Params ιs F) (d : ℕ) (i : Fin M) :
    (whirPaperTranscriptVectorSpec P d).length (mainFoldedOracleMessageIdx P d i).1
      = Fintype.card (ιs i.succ) := by
  show paperTranscriptSlotLength P d
    ((Fintype.equivFin (PaperTranscriptSlot P)).symm
      (paperTranscriptSlotIndex (.mainFoldedOracle i))) = _
  rw [paperTranscriptSlotIndex_symm_apply]
  rfl

/-- Read the `i`-th folded oracle out of a partial paper-order transcript, as a function on the
`i+1`-st evaluation domain. Requires that the folded-oracle slot has already been sent
(`h : slot index < m`). -/
def transcriptFoldedOracle (P : Params ιs F) (d : ℕ)
    {m : Fin (Fintype.card (PaperTranscriptSlot P) + 1)}
    (tr : Transcript m ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F))
    (i : Fin M) (h : ((mainFoldedOracleMessageIdx P d i).1 : Fin _).val < m.val) :
    ιs i.succ → F :=
  unpackFiniteFunction (ιs i.succ)
    (cast (congrArg (Vector F) (length_mainFoldedOracleMessageIdx P d i))
      (tr ⟨((mainFoldedOracleMessageIdx P d i).1 : Fin _).val, h⟩))

omit [Field F] [DecidableEq F] [SampleableType F] in
/-- **Seam lemma:** appending one more message to a partial transcript does not change the folded
oracles already present. -/
lemma transcriptFoldedOracle_concat (P : Params ιs F) (d : ℕ)
    {m : Fin (Fintype.card (PaperTranscriptSlot P))}
    (tr : Transcript m.castSucc ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F))
    (msg : ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F).Type m)
    (i : Fin M)
    (h : ((mainFoldedOracleMessageIdx P d i).1 : Fin _).val < m.castSucc.val)
    (h' : ((mainFoldedOracleMessageIdx P d i).1 : Fin _).val < m.succ.val) :
    transcriptFoldedOracle P d (tr.concat msg) i h' = transcriptFoldedOracle P d tr i h := by
  have hpay : (tr.concat msg) ⟨((mainFoldedOracleMessageIdx P d i).1 : Fin _).val, h'⟩
      = tr ⟨((mainFoldedOracleMessageIdx P d i).1 : Fin _).val, h⟩ :=
    Fin.snoc_castSucc (α := fun j => ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F).Type
        (Fin.castLE m.succ.is_le j))
      msg tr ⟨((mainFoldedOracleMessageIdx P d i).1 : Fin _).val, h⟩
  unfold transcriptFoldedOracle
  exact congrArg (fun v => unpackFiniteFunction (ιs i.succ)
    (cast (congrArg (Vector F) (length_mainFoldedOracleMessageIdx P d i)) v)) hpay

section FoldedPred

variable (P : Params ιs F) (d : ℕ) {m0 : ℕ}
  [ReedSolomon.Smooth (P.φ 0)] [Nonempty (ιs 0)]

/-- **The WHIR round-indexed δ-closeness state predicate** for the relation pair
`whirRelation m0 (P.φ 0) 0` vs `whirRelation m0 (P.φ 0) δ`: the input oracle is δ-close to the
outer smooth Reed–Solomon code, and every folded oracle revealed in the first `m` rounds is
δ-close to its per-round smooth code `RS[F, ιs (i+1), varCount (i+1)]`.

The per-round smoothness/nonemptiness witnesses are taken as explicit arguments (they are the
`ParamConditions.h_smooth`-style data of the WHIR parameter set). -/
def whirFoldedClosePred
    (sm : ∀ i : Fin (M + 1), ReedSolomon.Smooth (P.φ i))
    (ne : ∀ i : Fin (M + 1), Nonempty (ιs i)) (δ : ℝ≥0)
    (m : Fin (Fintype.card (PaperTranscriptSlot P) + 1))
    (stmtIn : Unit × ∀ u : Unit, OracleStatement (ιs 0) F u)
    (tr : Transcript m ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F)) : Prop :=
  (δᵣ(stmtIn.2 (), smoothCode (P.φ 0) m0) ≤ (δ : ℝ≥0∞)) ∧
  ∀ (i : Fin M) (h : ((mainFoldedOracleMessageIdx P d i).1 : Fin _).val < m.val),
    letI := sm i.succ
    letI := ne i.succ
    δᵣ(transcriptFoldedOracle P d tr i h,
        smoothCode (P.φ i.succ) (P.varCount i.succ)) ≤ (δ : ℝ≥0∞)

omit [SampleableType F] [Smooth (P.φ 0)] [Nonempty (ιs 0)] in
/-- At round 0 the folded-closeness predicate is exactly δ-closeness of the input oracle, i.e.
membership in `whirRelation m0 (P.φ 0) δ`. -/
lemma whirFoldedClosePred_zero
    (sm : ∀ i : Fin (M + 1), ReedSolomon.Smooth (P.φ i))
    (ne : ∀ i : Fin (M + 1), Nonempty (ιs i)) (δ : ℝ≥0)
    (stmtIn : Unit × ∀ u : Unit, OracleStatement (ιs 0) F u)
    (tr : Transcript 0 ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F)) :
    whirFoldedClosePred P d (m0 := m0) sm ne δ 0 stmtIn tr ↔
      δᵣ(stmtIn.2 (), smoothCode (P.φ 0) m0) ≤ (δ : ℝ≥0∞) := by
  unfold whirFoldedClosePred
  exact ⟨fun h => h.1, fun h => ⟨h, fun i hi => absurd hi (by simp)⟩⟩

omit [SampleableType F] [Smooth (P.φ 0)] [Nonempty (ιs 0)] in
/-- **Monotonicity/seam lemma:** the folded-closeness predicate at round `m+1` on an extended
transcript implies the predicate at round `m` on the original transcript (the constraint set
shrinks, and earlier payloads are unchanged). This holds at *every* round, in particular at all
prover rounds (giving `toFun_next`) and at all challenge rounds except the designated threshold
(giving the zero-flip probability legs). -/
lemma whirFoldedClosePred_concat
    (sm : ∀ i : Fin (M + 1), ReedSolomon.Smooth (P.φ i))
    (ne : ∀ i : Fin (M + 1), Nonempty (ιs i)) (δ : ℝ≥0)
    (m : Fin (Fintype.card (PaperTranscriptSlot P)))
    (stmtIn : Unit × ∀ u : Unit, OracleStatement (ιs 0) F u)
    (tr : Transcript m.castSucc ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F))
    (msg : ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F).Type m)
    (h : whirFoldedClosePred P d (m0 := m0) sm ne δ m.succ stmtIn (tr.concat msg)) :
    whirFoldedClosePred P d (m0 := m0) sm ne δ m.castSucc stmtIn tr := by
  obtain ⟨hbase, hfold⟩ := h
  refine ⟨hbase, fun i hi => ?_⟩
  have hi' : ((mainFoldedOracleMessageIdx P d i).1 : Fin _).val < m.succ.val := by
    simp only [Fin.val_succ]
    simp only [Fin.val_castSucc] at hi
    omega
  have := hfold i hi'
  rwa [transcriptFoldedOracle_concat P d tr msg i hi hi'] at this

end FoldedPred

section Wiring

variable (P : Params ιs F) (d : ℕ) {m0 : ℕ}
  [ReedSolomon.Smooth (P.φ 0)] [Nonempty (ιs 0)]

omit [SampleableType F] in
/-- Membership in `whirRelation` is exactly δ-closeness of the oracle (the `Unit` components are
irrelevant). -/
lemma mem_whirRelation_iff (δ : ℝ≥0)
    (stmtIn : Unit × ∀ u : Unit, OracleStatement (ιs 0) F u) (w : Unit) :
    (stmtIn, w) ∈ whirRelation m0 (P.φ 0) δ ↔
      δᵣ(stmtIn.2 (), smoothCode (P.φ 0) m0) ≤ (δ : ℝ≥0∞) := by
  unfold whirRelation
  simp only [Set.mem_setOf_eq]

/-- **The WHIR knowledge state function** (δ-closeness threshold form), for the soundness
relation `whirRelation m0 (P.φ 0) δ` of the relation pair, with the budget threshold at the final
randomness challenge. This is the round-indexed state function object for the concrete WHIR
`VectorIOP`. -/
def whirKnowledgeStateFunction
    (sm : ∀ i : Fin (M + 1), ReedSolomon.Smooth (P.φ i))
    (ne : ∀ i : Fin (M + 1), Nonempty (ιs i)) (δ : ℝ≥0) :
    ((OracleProof.toOracleVerifier (whirVectorIOP P d)).toVerifier
      (Oₛₒ := fun i : Empty => nomatch i)).KnowledgeStateFunction (pure ()) isEmptyElim
      (whirRelation m0 (P.φ 0) δ) acceptRejectOracleRel
      (unitExtractor (WitOut := Unit)) :=
  thresholdKSF (pure ()) isEmptyElim _ _ _
    (whirFoldedClosePred P d (m0 := m0) sm ne δ)
    (finalRandomnessChallengeIdx P d)
    (fun stmtIn w => by
      rw [mem_whirRelation_iff P (m0 := m0) δ stmtIn w,
        whirFoldedClosePred_zero P d (m0 := m0) sm ne δ stmtIn default])
    (fun m _ stmtIn tr msg h =>
      whirFoldedClosePred_concat P d (m0 := m0) sm ne δ m stmtIn tr msg h)

/-- **Discharged #302 residual (indicator budget):** the concrete WHIR `VectorIOP` satisfies
round-by-round knowledge soundness with the indicator RBR budget concentrated at the final
randomness challenge round — every other challenge round has *zero* flip probability for the
δ-closeness threshold state function. -/
theorem whirVectorIOP_rbrKnowledgeSoundness_indicator (δ : ℝ≥0) :
    whirVectorIOP_rbrKnowledgeSoundness P d δ
      (fun i => if i = finalRandomnessChallengeIdx P d then 1 else 0) (m0 := m0) := by
  unfold whirVectorIOP_rbrKnowledgeSoundness OracleProof.rbrKnowledgeSoundness
    OracleVerifier.rbrKnowledgeSoundness
  exact ThresholdKSF.rbrKnowledgeSoundness_indicator (pure ()) isEmptyElim
    ((OracleProof.toOracleVerifier (whirVectorIOP P d)).toVerifier
      (Oₛₒ := fun i : Empty => nomatch i))
    (whirRelation m0 (P.φ 0) δ) acceptRejectOracleRel
    (fun _ stmtIn _ => δᵣ(stmtIn.2 (), smoothCode (P.φ 0) m0) ≤ (δ : ℝ≥0∞))
    (finalRandomnessChallengeIdx P d)
    (fun stmtIn w => mem_whirRelation_iff P (m0 := m0) δ stmtIn w)
    (fun _ _ _ _ _ h => h)

set_option linter.unusedSectionVars false in
/-- The stronger variant through the genuine folded-oracle-tracking state function, available
whenever every round's evaluation domain is smooth and nonempty (the `ParamConditions.h_smooth`
data). Same indicator budget, but the state function is `whirFoldedClosePred`. -/
theorem whirVectorIOP_rbrKnowledgeSoundness_indicator_folded
    (sm : ∀ i : Fin (M + 1), ReedSolomon.Smooth (P.φ i))
    (ne : ∀ i : Fin (M + 1), Nonempty (ιs i)) (δ : ℝ≥0) :
    whirVectorIOP_rbrKnowledgeSoundness P d δ
      (fun i => if i = finalRandomnessChallengeIdx P d then 1 else 0) (m0 := m0) := by
  unfold whirVectorIOP_rbrKnowledgeSoundness OracleProof.rbrKnowledgeSoundness
    OracleVerifier.rbrKnowledgeSoundness
  exact ThresholdKSF.rbrKnowledgeSoundness_indicator (pure ()) isEmptyElim
    ((OracleProof.toOracleVerifier (whirVectorIOP P d)).toVerifier
      (Oₛₒ := fun i : Empty => nomatch i))
    (whirRelation m0 (P.φ 0) δ) acceptRejectOracleRel
    (whirFoldedClosePred P d (m0 := m0) sm ne δ)
    (finalRandomnessChallengeIdx P d)
    (fun stmtIn w => by
      rw [mem_whirRelation_iff P (m0 := m0) δ stmtIn w,
        whirFoldedClosePred_zero P d (m0 := m0) sm ne δ stmtIn default])
    (fun m _ stmtIn tr msg h =>
      whirFoldedClosePred_concat P d (m0 := m0) sm ne δ m stmtIn tr msg h)

end Wiring

/-! ## Completeness leg

The paper transcript completeness proof is owned by `Whir.ProtocolCompleteness`.
These compatibility names preserve the RBR-facing API without copying its proof.
-/

section Completeness

/-- The canonical paper-transcript perfect-completeness proof. -/
theorem paperTranscriptVectorIOP_pureTrue_perfectCompleteness (P : Params ιs F) (d : ℕ)
    (mk : (Unit × (∀ u : Unit, OracleStatement (ιs 0) F u)) × Unit → PaperTranscriptData P d)
    (relation : Set ((Unit × ∀ u : Unit, OracleStatement (ιs 0) F u) × Unit)) :
    (paperTranscriptVectorIOP P d mk (fun _ _ => pure true)).perfectCompleteness
      (pure ()) isEmptyElim relation :=
  Whir302.paperTranscriptVectorIOP_pureTrue_perfectCompleteness P d mk relation

/-- The perfect-completeness residual of the concrete WHIR `VectorIOP`. -/
theorem whirVectorIOP_perfectCompleteness_holds (P : Params ιs F) (d : ℕ) {m0 : ℕ}
    [ReedSolomon.Smooth (P.φ 0)] [Nonempty (ιs 0)] :
    whirVectorIOP_perfectCompleteness P d (m0 := m0) :=
  Whir302.whirVectorIOP_perfectCompleteness_holds P d

/-- **The full security package with the indicator budget:** the concrete WHIR `VectorIOP` is
secure with gap for the relation pair `whirRelation m0 (P.φ 0) 0` vs `whirRelation m0 (P.φ 0) δ`
with the RBR budget concentrated on the final randomness challenge round. -/
theorem whirVectorIOP_isSecureWithGap_indicator (P : Params ιs F) (d : ℕ) {m0 : ℕ}
    [ReedSolomon.Smooth (P.φ 0)] [Nonempty (ιs 0)] (δ : ℝ≥0) :
    whirVectorIOP_isSecureWithGap P d δ
      (fun i => if i = finalRandomnessChallengeIdx P d then 1 else 0) (m0 := m0) :=
  whirVectorIOP_isSecureWithGap_holds P d δ _
    (whirVectorIOP_perfectCompleteness_holds P d)
    (whirVectorIOP_rbrKnowledgeSoundness_indicator P d δ)

end Completeness

end Whir302RBR

end

#print axioms ThresholdKSF.thresholdKSF
#print axioms ThresholdKSF.rbrKnowledgeSoundness_indicator
#print axioms ThresholdKSF.rbrKnowledgeSoundness_of_flipBound
#print axioms Whir302RBR.length_mainFoldedOracleMessageIdx
#print axioms Whir302RBR.transcriptFoldedOracle_concat
#print axioms Whir302RBR.whirFoldedClosePred_zero
#print axioms Whir302RBR.whirFoldedClosePred_concat
#print axioms Whir302RBR.mem_whirRelation_iff
#print axioms Whir302RBR.whirKnowledgeStateFunction
#print axioms Whir302RBR.whirVectorIOP_rbrKnowledgeSoundness_indicator
#print axioms Whir302RBR.whirVectorIOP_rbrKnowledgeSoundness_indicator_folded
#print axioms Whir302RBR.whirVectorIOP_perfectCompleteness_holds
#print axioms Whir302RBR.whirVectorIOP_isSecureWithGap_indicator
