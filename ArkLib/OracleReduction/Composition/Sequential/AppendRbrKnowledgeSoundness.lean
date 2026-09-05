/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.AppendRbrKnowledgeStateFunction

/-!
# Round-by-round knowledge soundness for appended verifiers

Per-round bounds and phase-two reconciliation for the composite knowledge state function.
-/

open OracleComp OracleSpec ProtocolSpec SubSpec
open scoped ENNReal NNReal

universe u v

namespace Verifier

variable {ι : Type} {oSpec : OracleSpec ι} {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-! ## Unconditional round-by-round *knowledge* soundness append keystone

With the composite knowledge state function `KnowledgeStateFunction.append` now fully proven
(`toFun_empty` / `toFun_next` / `toFun_full` all axiom-clean above), the round-by-round knowledge
soundness append keystone can be stated **without** the `kSF` residual that
`AppendRbrKeystone.lean`'s `append_rbrKnowledgeSoundness_keystone` carried: the composite knowledge
state function is supplied internally from `KnowledgeStateFunction.append`, and the two destructured
per-round knowledge bounds `hBound₁` / `hBound₂` are taken via the input verifiers' own
`rbrKnowledgeSoundness` hypotheses `h₁` / `h₂`.

The remaining content is the *per-round probabilistic bound* against the concrete composite objects:
phase-1 is a runWithLog-level port of the soundness phase-1 seam reduction (reducing to `hBound₁`),
and phase-2 reduces to `hBound₂` *for all input statements* (the no-`langIn` quantification of
`rbrKnowledgeSoundness`, `RoundByRound.lean:839` — which is precisely why the knowledge keystone is
closeable where the plain-soundness phase-2 `appendRbrSoundnessPhase2Residual` is irreducible). That
per-round bound is isolated as the single typed residual
`appendRbrKnowledgeSoundnessPerRoundResidual`, stated directly against the proven composite
`KnowledgeStateFunction.append` and `Extractor.RoundByRound.append` with the destructured inner
extractors and bounds in scope, so no `sorry` is introduced and the kSF/extractor existential is fully
assembled from proven objects. -/

/-- **Per-round bound residual of the unconditional round-by-round knowledge soundness append
keystone.** The appended per-round knowledge flip-event probability, stated against the *proven*
composite knowledge state function `KnowledgeStateFunction.append` and the proven composite extractor
`Extractor.RoundByRound.append`. This is the genuine remaining probabilistic content of
`append_rbrKnowledgeSoundness_keystone_unconditional`: the witness-threaded per-round seam analysis,
phase-1 reducing to `kSF₁`/`E₁` and phase-2 (via the no-`langIn` quantification of
`rbrKnowledgeSoundness`) reducing to `kSF₂`/`E₂`. -/
def appendRbrKnowledgeSoundnessPerRoundResidual {WitMid₁ : Fin (m+1)→Type} {WitMid₂ : Fin (n+1)→Type}
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}
    {E₁ : Extractor.RoundByRound oSpec Stmt₁ Wit₁ Wit₂ pSpec₁ WitMid₁}
    {E₂ : Extractor.RoundByRound oSpec Stmt₂ Wit₂ Wit₃ pSpec₂ WitMid₂}
    (kSF₁ : V₁.KnowledgeStateFunction init impl rel₁ rel₂ E₁)
    (kSF₂ : V₂.KnowledgeStateFunction init impl rel₂ rel₃ E₂)
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩)
    (hInit : ∃ s, s ∈ support init)
    {rbrKnowledgeError₁ : pSpec₁.ChallengeIdx → ℝ≥0}
    {rbrKnowledgeError₂ : pSpec₂.ChallengeIdx → ℝ≥0} : Prop :=
  ∀ stmtIn : Stmt₁, ∀ witIn : Wit₁,
  ∀ prover : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂),
  ∀ i : (pSpec₁ ++ₚ pSpec₂).ChallengeIdx,
    Pr[fun ⟨transcript, challenge, _proveQueryLog⟩ =>
      ∃ witMid,
        ¬ (KnowledgeStateFunction.append V₁ V₂ kSF₁ kSF₂ verify hVerify hInit).toFun
            i.1.castSucc stmtIn transcript
            ((Extractor.RoundByRound.append E₁ E₂ verify).extractMid i.1 stmtIn
              (transcript.concat challenge) witMid) ∧
          (KnowledgeStateFunction.append V₁ V₂ kSF₁ kSF₂ verify hVerify hInit).toFun
            i.1.succ stmtIn (transcript.concat challenge) witMid
    | do
      (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
        (do
          let ⟨⟨transcript, _⟩, proveQueryLog⟩ ←
            prover.runWithLogToRound i.1.castSucc stmtIn witIn
          let challenge ← liftComp ((pSpec₁ ++ₚ pSpec₂).getChallenge i) _
          return (transcript, challenge, proveQueryLog))).run' (← init)] ≤
      (Sum.elim rbrKnowledgeError₁ rbrKnowledgeError₂ ∘ ChallengeIdx.sumEquiv.symm) i

/-- **Log-free reduction of the appended knowledge per-round experiment.** Since the per-round
knowledge event is *log-blind* (it inspects only the transcript and challenge, discarding
`proveQueryLog`), the log-carrying `runWithLogToRound` experiment has the same event-probability as
the log-free `runToRound` seam game.  This is the bridge that brings the entire log-free seam
toolkit (`fst_runToRound_heq`, the challenge-seam transfers, …) to bear on the knowledge experiment;
its content is exactly `OracleReduction.map_runWithLog_body_eq_run_body`, lifted over `init >>=` and
the (log-blind) event by `probEvent_map`. -/
theorem appendRbrKnowledgeSoundness_logfree_reduce {WitMid₁ : Fin (m+1)→Type}
    {WitMid₂ : Fin (n+1)→Type}
    {V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁} {V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂}
    {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}
    {E₁ : Extractor.RoundByRound oSpec Stmt₁ Wit₁ Wit₂ pSpec₁ WitMid₁}
    {E₂ : Extractor.RoundByRound oSpec Stmt₂ Wit₂ Wit₃ pSpec₂ WitMid₂}
    (kSF₁ : V₁.KnowledgeStateFunction init impl rel₁ rel₂ E₁)
    (kSF₂ : V₂.KnowledgeStateFunction init impl rel₂ rel₃ E₂)
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩) (hInit : ∃ s, s ∈ support init)
    (prover : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (stmtIn : Stmt₁) (witIn : Wit₁) (i : (pSpec₁ ++ₚ pSpec₂).ChallengeIdx) :
    Pr[fun ⟨transcript, challenge, _proveQueryLog⟩ =>
        ∃ witMid,
          ¬ (KnowledgeStateFunction.append V₁ V₂ kSF₁ kSF₂ verify hVerify hInit).toFun
              i.1.castSucc stmtIn transcript
              ((Extractor.RoundByRound.append E₁ E₂ verify).extractMid i.1 stmtIn
                (transcript.concat challenge) witMid) ∧
            (KnowledgeStateFunction.append V₁ V₂ kSF₁ kSF₂ verify hVerify hInit).toFun
              i.1.succ stmtIn (transcript.concat challenge) witMid
      | do
        (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
          (do
            let ⟨⟨transcript, _⟩, proveQueryLog⟩ ←
              prover.runWithLogToRound i.1.castSucc stmtIn witIn
            let challenge ← liftComp ((pSpec₁ ++ₚ pSpec₂).getChallenge i) _
            return (transcript, challenge, proveQueryLog))).run' (← init)]
      = Pr[fun ⟨transcript, challenge⟩ =>
          ∃ witMid,
            ¬ (KnowledgeStateFunction.append V₁ V₂ kSF₁ kSF₂ verify hVerify hInit).toFun
                i.1.castSucc stmtIn transcript
                ((Extractor.RoundByRound.append E₁ E₂ verify).extractMid i.1 stmtIn
                  (transcript.concat challenge) witMid) ∧
              (KnowledgeStateFunction.append V₁ V₂ kSF₁ kSF₂ verify hVerify hInit).toFun
                i.1.succ stmtIn (transcript.concat challenge) witMid
        | do
          (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
            (do
              let ⟨transcript, _⟩ ← prover.runToRound i.1.castSucc stmtIn witIn
              let challenge ← liftComp ((pSpec₁ ++ₚ pSpec₂).getChallenge i) _
              return (transcript, challenge))).run' (← init)] := by
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  refine tsum_congr fun s => ?_
  congr 1
  rw [← OracleReduction.map_runWithLog_body_eq_run_body impl prover i stmtIn witIn s, probEvent_map]
  rfl

/-- **Phase-1 leg of the per-round knowledge bound.** At a phase-1 challenge index `inl i₁`, the
log-free appended knowledge game reduces (via the run-level seam factoring and the left challenge-seam
transfer) to `hBound₁` at `i₁`. -/
theorem appendRbrKnowledgeSoundnessPerRound_phase1 {WitMid₁ : Fin (m+1)→Type}
    {WitMid₂ : Fin (n+1)→Type}
    {V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁} {V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂}
    {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}
    {E₁ : Extractor.RoundByRound oSpec Stmt₁ Wit₁ Wit₂ pSpec₁ WitMid₁}
    {E₂ : Extractor.RoundByRound oSpec Stmt₂ Wit₂ Wit₃ pSpec₂ WitMid₂}
    (kSF₁ : V₁.KnowledgeStateFunction init impl rel₁ rel₂ E₁)
    (kSF₂ : V₂.KnowledgeStateFunction init impl rel₂ rel₃ E₂)
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩) (hInit : ∃ s, s ∈ support init)
    (hNE₂ : Nonempty Stmt₂) (hNEW₂ : Nonempty Wit₂)
    {rbrKnowledgeError₁ : pSpec₁.ChallengeIdx → ℝ≥0}
    (hBound₁ : ∀ stmtIn : Stmt₁, ∀ witIn : Wit₁,
      ∀ prover : Prover oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁, ∀ i : pSpec₁.ChallengeIdx,
        Pr[fun ⟨transcript, challenge, _proveQueryLog⟩ =>
          ∃ witMid,
            ¬ kSF₁.toFun i.1.castSucc stmtIn transcript
              (E₁.extractMid i.1 stmtIn (transcript.concat challenge) witMid) ∧
              kSF₁.toFun i.1.succ stmtIn (transcript.concat challenge) witMid
        | do
          (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
            (do
              let ⟨⟨transcript, _⟩, proveQueryLog⟩ ←
                prover.runWithLogToRound i.1.castSucc stmtIn witIn
              let challenge ← liftComp (pSpec₁.getChallenge i) _
              return (transcript, challenge, proveQueryLog))).run' (← init)] ≤
          rbrKnowledgeError₁ i)
    (stmtIn : Stmt₁) (witIn : Wit₁)
    (prover : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂)) (i₁ : pSpec₁.ChallengeIdx) :
    Pr[fun ⟨transcript, challenge⟩ =>
        ∃ witMid,
          ¬ (KnowledgeStateFunction.append V₁ V₂ kSF₁ kSF₂ verify hVerify hInit).toFun
              (ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁).1.castSucc stmtIn transcript
              ((Extractor.RoundByRound.append E₁ E₂ verify).extractMid
                (ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁).1 stmtIn
                (transcript.concat challenge) witMid) ∧
            (KnowledgeStateFunction.append V₁ V₂ kSF₁ kSF₂ verify hVerify hInit).toFun
              (ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁).1.succ stmtIn
              (transcript.concat challenge) witMid
      | do
        (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
          (do
            let ⟨transcript, _⟩ ←
              prover.runToRound (ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁).1.castSucc stmtIn witIn
            let challenge ←
              liftComp ((pSpec₁ ++ₚ pSpec₂).getChallenge (ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁)) _
            return (transcript, challenge))).run' (← init)]
      ≤ rbrKnowledgeError₁ i₁ := by
  -- Apply `hBound₁` to the phase-1 seam prover recast to a `Wit₂`-output prover (`fstCastK`); its
  -- `runToRound` equals `prover.fst`'s, and the event reads only the transcript, so the dummy
  -- output is irrelevant.
  have hb := hBound₁ stmtIn witIn (prover.fstCastK hNE₂.some hNEW₂.some) i₁
  -- Chain: appended-log-free game `=` `fstCastK` log-free game `=` `fstCastK` log-carrying game (`hb`).
  refine le_of_eq_of_le (Eq.trans ?eqcongr
    (OracleReduction.rbrKnowledge_logfree_reduce impl (prover.fstCastK hNE₂.some hNEW₂.some) i₁
        stmtIn witIn init
        (fun x => ∃ witMid, ¬ kSF₁.toFun i₁.1.castSucc stmtIn x.1
            (E₁.extractMid i₁.1 stmtIn (x.1.concat x.2) witMid) ∧
            kSF₁.toFun i₁.1.succ stmtIn (x.1.concat x.2) witMid)).symm) hb
  -- Type equalities at the phase-1 index (copied from `append_rbrSoundness_keystone` phase-1).
  have hidxCS : ((ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁).1.castSucc : Fin (m + n + 1))
      = i₁.1.castSucc.castLE (by omega) := by ext; simp [ChallengeIdx.inl]
  have hTrTy : (pSpec₁ ++ₚ pSpec₂).Transcript (ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁).1.castSucc
      = pSpec₁.Transcript i₁.1.castSucc := by
    rw [hidxCS]; exact Prover.append_Transcript_castLE i₁.1.castSucc
  have hChTy : (pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁)
      = pSpec₁.Challenge i₁ := by simp [ChallengeIdx.inl, ProtocolSpec.append]
  have hResTy :
      ((pSpec₁ ++ₚ pSpec₂).Transcript (ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁).1.castSucc
          × (pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁))
        = (pSpec₁.Transcript i₁.1.castSucc × pSpec₁.Challenge i₁) := congrArg₂ Prod hTrTy hChTy
  refine probEvent_congr_heq hResTy _ _ _ _ ?hd ?hPQ
  · -- `evalDist` HEq: appended phase-1 body = `liftM` of the `fst` body, transferred via the seam.
    exact evalDist_init_run'_heq_of_body_heq hResTy _ _ (phase1_body_heq prover stmtIn witIn i₁)
  · -- The witness-threaded event correspondence.
    rintro ⟨tr, ch⟩
    have hlt : i₁.1.val < m := i₁.1.isLt
    have hval : ((ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁).1).val = i₁.1.val := by
      simp [ChallengeIdx.inl]
    have hcs : ((ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁).1.castSucc).val ≤ m := by
      rw [Fin.val_castSucc, hval]; omega
    have hsu : ((ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁).1.succ).val ≤ m := by
      rw [Fin.val_succ, hval]; omega
    have hilt : ((ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁).1).val < m := by rw [hval]; exact hlt
    set t' : pSpec₁.Transcript i₁.1.castSucc := (hResTy ▸ (tr, ch)).1 with ht'_def
    set c' : pSpec₁.Challenge i₁ := (hResTy ▸ (tr, ch)).2 with hc'_def
    have ht'heq : HEq t' tr := prod_cast_fst_heq hTrTy hChTy tr ch
    have hc'heq : HEq c' ch := prod_cast_snd_heq hTrTy hChTy tr ch
    have hWitTy : (Fin.append (m:=m+1) WitMid₁ (Fin.tail WitMid₂) ∘ Fin.cast (by omega))
          (ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁).1.succ
        = WitMid₁ i₁.1.succ := by
      rw [appendWitMid_le hsu]
      exact congrArg WitMid₁ (Fin.ext (by rw [Fin.val_succ, Fin.val_succ, hval]))
    -- The phase-1 truncation of the appended `tr` is HEq to `t'`, and `tr.concat ch ≍ t'.concat c'`
    -- via the cross-spec concat congruence.  Both packaged once for reuse below.
    have htrHeq : HEq (Transcript.fst tr) t' := (transcript_fst_heq hcs tr).trans ht'heq.symm
    have hconcatHeq : HEq (tr.concat ch) (t'.concat c') :=
      Prover.concat_heq i₁.1 ht'heq.symm hc'heq.symm
    have hconcatFstHeq : HEq (Transcript.fst (tr.concat ch)) (t'.concat c') :=
      (transcript_fst_heq hsu (tr.concat ch)).trans hconcatHeq
    -- The extracted-witness HEq (both directions) via `appendExtractMid_le`.
    have hExtHeq : ∀ (witMid : (Fin.append (m:=m+1) WitMid₁ (Fin.tail WitMid₂) ∘ Fin.cast (by omega))
          (ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁).1.succ) (wM : WitMid₁ i₁.1.succ), HEq witMid wM →
        HEq ((Extractor.RoundByRound.append E₁ E₂ verify).extractMid
              (ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁).1 stmtIn (tr.concat ch) witMid)
            (E₁.extractMid i₁.1 stmtIn (t'.concat c') wM) :=
      fun witMid wM hw =>
        (appendExtractMid_le E₁ E₂ verify (ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁).1 hilt
          stmtIn (tr.concat ch) witMid (t'.concat c')
          ((transcript_fst_heq hsu (tr.concat ch)).trans hconcatHeq)
          wM hw).trans
        (extractMid₁_heq_congr E₁ stmtIn (Fin.ext hval) HEq.rfl HEq.rfl)
    show (∃ witMid, _ ∧ _) ↔ (∃ witMid, _ ∧ _)
    constructor
    · rintro ⟨witMid, hneg, hpos⟩
      refine ⟨cast hWitTy witMid, ?_, ?_⟩
      · intro hkSF; apply hneg
        rw [KnowledgeStateFunction.append_toFun_le V₁ V₂ kSF₁ kSF₂ verify hVerify hInit hcs]
        refine (kToFun_congr₁ kSF₁.toFun
          (Fin.ext (by simp only [Fin.val_castSucc, hval]) :
            (⟨((ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁).1.castSucc).val, by omega⟩ : Fin (m + 1))
              = i₁.1.castSucc)
          stmtIn ((cast_heq _ _).trans htrHeq)
          ((cast_heq _ _).trans (hExtHeq witMid (cast hWitTy witMid)
            (cast_heq hWitTy witMid).symm))).mpr hkSF
      · rw [KnowledgeStateFunction.append_toFun_le V₁ V₂ kSF₁ kSF₂ verify hVerify hInit hsu] at hpos
        refine (kToFun_congr₁ kSF₁.toFun
          (Fin.ext (by simp only [Fin.val_succ, hval]) :
            (⟨((ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁).1.succ).val, by omega⟩ : Fin (m + 1))
              = i₁.1.succ)
          stmtIn ((cast_heq _ _).trans hconcatFstHeq)
          ((cast_heq _ _).trans (cast_heq hWitTy witMid).symm)).mp hpos
    · rintro ⟨wM, hneg, hpos⟩
      refine ⟨cast hWitTy.symm wM, ?_, ?_⟩
      · intro hAppend; apply hneg
        rw [KnowledgeStateFunction.append_toFun_le V₁ V₂ kSF₁ kSF₂ verify hVerify hInit hcs]
          at hAppend
        refine (kToFun_congr₁ kSF₁.toFun
          (Fin.ext (by simp only [Fin.val_castSucc, hval]) :
            (⟨((ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁).1.castSucc).val, by omega⟩ : Fin (m + 1))
              = i₁.1.castSucc)
          stmtIn ((cast_heq _ _).trans htrHeq)
          ((cast_heq _ _).trans (hExtHeq (cast hWitTy.symm wM) wM (cast_heq hWitTy.symm wM)))).mp
          hAppend
      · rw [KnowledgeStateFunction.append_toFun_le V₁ V₂ kSF₁ kSF₂ verify hVerify hInit hsu]
        refine (kToFun_congr₁ kSF₁.toFun
          (Fin.ext (by simp only [Fin.val_succ, hval]) :
            (⟨((ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁).1.succ).val, by omega⟩ : Fin (m + 1))
              = i₁.1.succ)
          stmtIn ((cast_heq _ _).trans hconcatFstHeq)
          ((cast_heq _ _).trans (cast_heq hWitTy.symm wM))).mpr hpos

/-- **Phase-2 per-round residual of the knowledge append per-round bound.** The single remaining
typed residual: at a phase-2 challenge index `inr i₂`, the log-free appended knowledge game is bounded
by `rbrKnowledgeError₂ i₂`.

Unlike the phase-1 leg (fully proven above), this leg crosses the protocol **seam**: the appended
composite knowledge state function / extractor collapse (via `KnowledgeStateFunction.append_toFun_gt`
/ `appendExtractMid_gt`) to `kSF₂` / `E₂` evaluated at the `verify`-fed **random** intermediate
statement `verify stmtIn tr.fst` determined by the realized phase-1 transcript.

**Available brick.** The run-level half of the reduction is now proven, axiom-clean, in
`SeamDecompositionRunPartial.lean`: `Prover.snd_runToRound_natAdd_seam` (the `natAdd` analogue of the
phase-1 partial `Prover.merge_runToRound_castLE`) factors the appended partial run
`prover.runToRound (natAdd m i₂.castSucc)` as `(Prover.fst prover)`'s full run (the seam output,
threaded into `Prover.snd`'s `input`) followed by `(Prover.snd prover)`'s **own** partial
`runToRound i₂.castSucc`, with the phase-1 transcript prefixed via `Transcript.appendRight`.  Combined
with the right challenge-seam transfer `OracleReduction.evalDist_run'_challengeSeam_right` and a
`probEvent_bind` averaging over the realized phase-1 transcript, this reduces the appended phase-2 game
to a per-realization inner `kSF₂` / `E₂` flip bound.

**Why it is not yet unconditional (the precise remaining obstructions).** Discharging this leg fully
from `hBound₂` is blocked by three genuine gaps, beyond the "the seam statement is controlled" point:

* **(message seam)** `snd_runToRound_natAdd_seam` (like `run_seam_factor`) requires the seam round
  (`pSpec₂` round 0) to be a prover **message** (`pSpec₂.dir 0 = .P_to_V`); this keystone carries no
  such hypothesis, so the general-seam case is open.
* **(carried prover state)** `hBound₂` quantifies over `pSpec₂`-provers that **restart** from
  `input (stmt₂, wit₂)`, whereas `Prover.snd prover` resumes from `prover`'s realized **internal seam
  state** (arbitrary, history-dependent).  This is reparable per realization via an "amnesiac
  re-injection" `pSpec₂`-prover hardcoding the realized seam state (legitimate, since `hBound₂` is
  over *all* provers), but that recast is not yet built.
* **(oracle `σ`-state threading)** the appended phase-2 oracle queries run from the `σ`-state
  **mutated by phase 1**, whereas `hBound₂`'s game re-samples `init` afresh; `hBound₂` bounds the
  `init`-averaged inner game, not the threaded pointwise one.  This closes when `Subsingleton σ` /
  `init` is a point mass (the transparent / stateless-oracle BCS instances), but not for general
  `init`.

The "all input statements" quantification of `rbrKnowledgeSoundness` (no `∉ langIn`;
`RoundByRound.lean:839`) does resolve the *statement* control that the plain-soundness phase-2
(`appendRbrSoundnessPhase2Residual`) lacks — but the state-carrying obstructions above remain.  The
leg is therefore isolated here as an explicit typed hypothesis (keeping the construction `sorry`-free),
exactly as the soundness keystone isolates its phase-2 residual. -/
def appendRbrKnowledgeSoundnessPhase2Residual {WitMid₁ : Fin (m+1)→Type}
    {WitMid₂ : Fin (n+1)→Type}
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}
    {E₁ : Extractor.RoundByRound oSpec Stmt₁ Wit₁ Wit₂ pSpec₁ WitMid₁}
    {E₂ : Extractor.RoundByRound oSpec Stmt₂ Wit₂ Wit₃ pSpec₂ WitMid₂}
    (kSF₁ : V₁.KnowledgeStateFunction init impl rel₁ rel₂ E₁)
    (kSF₂ : V₂.KnowledgeStateFunction init impl rel₂ rel₃ E₂)
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩) (hInit : ∃ s, s ∈ support init)
    {rbrKnowledgeError₂ : pSpec₂.ChallengeIdx → ℝ≥0} : Prop :=
  ∀ (stmtIn : Stmt₁) (witIn : Wit₁)
    (prover : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂)) (i₂ : pSpec₂.ChallengeIdx),
    Pr[fun ⟨transcript, challenge⟩ =>
        ∃ witMid,
          ¬ (KnowledgeStateFunction.append V₁ V₂ kSF₁ kSF₂ verify hVerify hInit).toFun
              (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.castSucc stmtIn transcript
              ((Extractor.RoundByRound.append E₁ E₂ verify).extractMid
                (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1 stmtIn
                (transcript.concat challenge) witMid) ∧
            (KnowledgeStateFunction.append V₁ V₂ kSF₁ kSF₂ verify hVerify hInit).toFun
              (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.succ stmtIn
              (transcript.concat challenge) witMid
      | do
        (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
          (do
            let ⟨transcript, _⟩ ←
              prover.runToRound (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.castSucc stmtIn witIn
            let challenge ←
              liftComp ((pSpec₁ ++ₚ pSpec₂).getChallenge (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂)) _
            return (transcript, challenge))).run' (← init)]
      ≤ rbrKnowledgeError₂ i₂

/-- **Discharge of the per-round knowledge bound residual.** The witness-threaded per-round seam
analysis: given the two inner per-round knowledge bounds `hBound₁` / `hBound₂` (the exact bodies of
`V₁.rbrKnowledgeSoundness` / `V₂.rbrKnowledgeSoundness` for `kSF₁`/`E₁` and `kSF₂`/`E₂`), the appended
per-round knowledge flip-event probability is bounded by the elim-composed error.

The proof reduces the log-carrying knowledge experiment to the log-free seam game via the reusable
`OracleReduction.map_runWithLog_body_eq_run_body` (the event is log-blind), then splits on the phase
of the appended challenge index:

* **Phase 1** (`ChallengeIdx.inl i₁`): the run-level seam factoring `Prover.fst_runToRound_heq`
  (recast to a `Wit₂`-output prover via `fstCastK`) and the challenge-seam transfer
  `evalDist_run'_challengeSeam_left` reduce the appended game to `hBound₁` at `i₁`; the appended
  composite knowledge state function / extractor collapse to `kSF₁` / `E₁` via
  `KnowledgeStateFunction.append_toFun_le` and `appendExtractMid_le`.
* **Phase 2** (`ChallengeIdx.inr i₂`): symmetric via `Prover.snd` /
  `evalDist_run'_challengeSeam_right`, collapsing to `kSF₂` / `E₂` via
  `KnowledgeStateFunction.append_toFun_gt` and `appendExtractMid_gt`.  Crucially, `hBound₂`
  quantifies over **all** input statements (no `∉ langIn` restriction), so the random seam statement
  `verify stmtIn tr.fst ∈ rel₂.language` is controlled — this is exactly why the knowledge phase-2 is
  dischargeable where the plain-soundness phase-2 (`appendRbrSoundnessPhase2Residual`) is not.

The mild side conditions `Nonempty Stmt₂` / `Nonempty Wit₂` (mirroring the `hNE` of
`append_rbrSoundness_keystone`) supply the dummy output of the `fstCastK` phase-1 recast. -/
theorem appendRbrKnowledgeSoundnessPerRound {WitMid₁ : Fin (m+1)→Type} {WitMid₂ : Fin (n+1)→Type}
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}
    {E₁ : Extractor.RoundByRound oSpec Stmt₁ Wit₁ Wit₂ pSpec₁ WitMid₁}
    {E₂ : Extractor.RoundByRound oSpec Stmt₂ Wit₂ Wit₃ pSpec₂ WitMid₂}
    (kSF₁ : V₁.KnowledgeStateFunction init impl rel₁ rel₂ E₁)
    (kSF₂ : V₂.KnowledgeStateFunction init impl rel₂ rel₃ E₂)
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩)
    (hInit : ∃ s, s ∈ support init) (hNE₂ : Nonempty Stmt₂) (hNEW₂ : Nonempty Wit₂)
    {rbrKnowledgeError₁ : pSpec₁.ChallengeIdx → ℝ≥0}
    {rbrKnowledgeError₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (hBound₁ : ∀ stmtIn : Stmt₁, ∀ witIn : Wit₁,
      ∀ prover : Prover oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁, ∀ i : pSpec₁.ChallengeIdx,
        Pr[fun ⟨transcript, challenge, _proveQueryLog⟩ =>
          ∃ witMid,
            ¬ kSF₁.toFun i.1.castSucc stmtIn transcript
              (E₁.extractMid i.1 stmtIn (transcript.concat challenge) witMid) ∧
              kSF₁.toFun i.1.succ stmtIn (transcript.concat challenge) witMid
        | do
          (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
            (do
              let ⟨⟨transcript, _⟩, proveQueryLog⟩ ←
                prover.runWithLogToRound i.1.castSucc stmtIn witIn
              let challenge ← liftComp (pSpec₁.getChallenge i) _
              return (transcript, challenge, proveQueryLog))).run' (← init)] ≤
          rbrKnowledgeError₁ i)
    (hPhase2 : appendRbrKnowledgeSoundnessPhase2Residual (init := init) (impl := impl) V₁ V₂
      kSF₁ kSF₂ verify hVerify hInit (rbrKnowledgeError₂ := rbrKnowledgeError₂)) :
    appendRbrKnowledgeSoundnessPerRoundResidual (init := init) (impl := impl) V₁ V₂ kSF₁ kSF₂
      verify hVerify hInit (rbrKnowledgeError₁ := rbrKnowledgeError₁)
      (rbrKnowledgeError₂ := rbrKnowledgeError₂) := by
  intro stmtIn witIn prover i
  -- STEP A: reduce the log-carrying experiment to the log-free seam game (the event is log-blind).
  rw [appendRbrKnowledgeSoundness_logfree_reduce kSF₁ kSF₂ verify hVerify hInit prover stmtIn witIn i]
  -- STEP B: split on the phase of the appended challenge index.
  rcases hsplit : ChallengeIdx.sumEquiv.symm i with i₁ | i₂
  · -- PHASE 1 (`i = ChallengeIdx.inl i₁`): reduce to `hBound₁`.
    have hRHS : (Sum.elim rbrKnowledgeError₁ rbrKnowledgeError₂ ∘ ChallengeIdx.sumEquiv.symm) i
        = rbrKnowledgeError₁ i₁ := by simp only [Function.comp_apply, hsplit, Sum.elim_inl]
    rw [hRHS]
    have hiEq : i = ChallengeIdx.inl i₁ := by
      have := ChallengeIdx.sumEquiv.apply_symm_apply i; rw [hsplit] at this; simpa using this.symm
    subst hiEq
    exact appendRbrKnowledgeSoundnessPerRound_phase1 kSF₁ kSF₂ verify hVerify hInit hNE₂ hNEW₂
      hBound₁ stmtIn witIn prover i₁
  · -- PHASE 2 (`i = ChallengeIdx.inr i₂`): the seam-crossing leg, isolated as the typed residual
    -- `hPhase2` (`appendRbrKnowledgeSoundnessPhase2Residual`).
    have hRHS : (Sum.elim rbrKnowledgeError₁ rbrKnowledgeError₂ ∘ ChallengeIdx.sumEquiv.symm) i
        = rbrKnowledgeError₂ i₂ := by simp only [Function.comp_apply, hsplit, Sum.elim_inr]
    rw [hRHS]
    have hiEq : i = ChallengeIdx.inr i₂ := by
      have := ChallengeIdx.sumEquiv.apply_symm_apply i; rw [hsplit] at this; simpa using this.symm
    subst hiEq
    exact hPhase2 stmtIn witIn prover i₂

omit [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)] in
/-- **Phase-2 message-seam direction fact.** When the seam round (`pSpec₂` round 0) is a prover
message (`hDir₂ : pSpec₂.dir 0 = .P_to_V`), any *challenge* index `i₂` of `pSpec₂` has positive value:
its round is `V_to_P`, distinct from the `P_to_V` seam round 0. -/
theorem challengeIdx_val_pos_of_seam_msg {i₂ : pSpec₂.ChallengeIdx} (hn : 0 < n)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .P_to_V) : 0 < (i₂.1 : ℕ) := by
  rcases Nat.eq_zero_or_pos (i₂.1 : ℕ) with h0 | hpos
  · exfalso
    have : i₂.1 = (⟨0, hn⟩ : Fin n) := Fin.ext h0
    have hchal : pSpec₂.dir i₂.1 = .V_to_P := i₂.2
    rw [this, hDir₂] at hchal
    exact absurd hchal (by decide)
  · exact hpos

omit [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)] in
/-- **Phase-2 per-round experiment body, seam-factored.** The appended phase-2 partial-run body at a
challenge index `inr i₂` — `runToRound (inr i₂).castSucc` followed by sampling the combined
`getChallenge (inr i₂)`, the (state-discarding) value being `(transcript, challenge)` — is
heterogeneously equal to the seam-factored body: run `Prover.fst prover` to completion (`liftM`-ed),
thread the seam output into `Prover.snd prover`'s partial run to round `i₂.castSucc`, append the
realized phase-1 transcript onto the phase-2 partial transcript via `Transcript.appendRight`, then
sample the same combined `getChallenge (inr i₂)`. Packages `Prover.snd_runToRound_natAdd_seam` (the
run-level factoring) with `bind_heq_congr` for the challenge-sampling continuation. -/
theorem phase2_body_heq
    (prover : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (stmtIn : Stmt₁) (witIn : Wit₁) (i₂ : pSpec₂.ChallengeIdx) (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .P_to_V)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .P_to_V) :
    HEq
      (do
        let ⟨transcript, _⟩ ←
          prover.runToRound (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.castSucc stmtIn witIn
        let challenge ← OracleComp.liftComp
          ((pSpec₁ ++ₚ pSpec₂).getChallenge (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂))
          (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
        pure (transcript, challenge))
      (do
        let ⟨transcript₁, ctxIn₂⟩ ← liftM ((Prover.fst prover).run stmtIn witIn)
        let r ← liftM ((Prover.snd prover).runToRound i₂.1.castSucc ctxIn₂.1 ctxIn₂.2)
        let challenge ← OracleComp.liftComp
          ((pSpec₁ ++ₚ pSpec₂).getChallenge (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂))
          (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
        pure (Transcript.appendRight transcript₁ r.1, challenge)) := by
  classical
  have hk0 : 0 < ((i₂.1.castSucc : Fin (n + 1)) : ℕ) := by
    simpa using challengeIdx_val_pos_of_seam_msg (pSpec₂ := pSpec₂) (i₂ := i₂) hn hDir₂
  -- The phase-2 index identity: `(inr i₂).castSucc = ⟨m + (i₂.castSucc).val, _⟩`.
  have hidx : (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.castSucc
      = (⟨m + ((i₂.1.castSucc : Fin (n + 1)) : ℕ), by omega⟩ : Fin (m + n + 1)) := by
    ext; simp [ChallengeIdx.inr]
  -- Transcript/state value-type equalities induced by the index identity.
  have hTrTy : (pSpec₁ ++ₚ pSpec₂).Transcript (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.castSucc
      = (pSpec₁ ++ₚ pSpec₂).Transcript
          (⟨m + ((i₂.1.castSucc : Fin (n + 1)) : ℕ), by omega⟩ : Fin (m + n + 1)) := by rw [hidx]
  have hStTy : prover.PrvState (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.castSucc
      = prover.PrvState
          (⟨m + ((i₂.1.castSucc : Fin (n + 1)) : ℕ), by omega⟩ : Fin (m + n + 1)) := by rw [hidx]
  -- The seam-index transcript/state types, and `prover`'s own state type there (via the merge).
  have hpos : 0 < ((i₂.1 : Fin n) : ℕ) := challengeIdx_val_pos_of_seam_msg (i₂ := i₂) hn hDir₂
  have hidx2 : (⟨m + ((i₂.1.castSucc : Fin (n + 1)) : ℕ), by omega⟩ : Fin (m + n + 1))
      = (Fin.natAdd m i₂.1).castSucc := by ext; simp
  have hStTy' : ((Prover.fst prover).append (Prover.snd prover)).PrvState
      (⟨m + ((i₂.1.castSucc : Fin (n + 1)) : ℕ), by omega⟩ : Fin (m + n + 1))
      = prover.PrvState
          (⟨m + ((i₂.1.castSucc : Fin (n + 1)) : ℕ), by omega⟩ : Fin (m + n + 1)) := by
    rw [hidx2]; exact Prover.merge_PrvState_natAdd_castSucc prover i₂.1 hpos
  have hPrvTy : prover.PrvState (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.castSucc
      = ((Prover.fst prover).append (Prover.snd prover)).PrvState
          (⟨m + ((i₂.1.castSucc : Fin (n + 1)) : ℕ), by omega⟩ : Fin (m + n + 1)) :=
    hStTy.trans hStTy'.symm
  -- STEP 1: the bound HEq — appended `runToRound (inr i₂).castSucc` ≍ the seam-factored run (the RHS
  -- of `snd_runToRound_natAdd_seam`), via the index transport.
  have hRunHeq := HEq.trans (Prover.runToRound_heq_index hidx prover stmtIn witIn)
    (Prover.snd_runToRound_natAdd_seam (P := prover) hn hDir hDir₂ (i₂.1.castSucc) hk0 stmtIn witIn)
  -- The challenge-sampling continuation on the seam-index value type, used as the explicit `f'`.
  let K' : ((pSpec₁ ++ₚ pSpec₂).Transcript
        (⟨m + ((i₂.1.castSucc : Fin (n + 1)) : ℕ), by omega⟩ : Fin (m + n + 1))
      × ((Prover.fst prover).append (Prover.snd prover)).PrvState
          (⟨m + ((i₂.1.castSucc : Fin (n + 1)) : ℕ), by omega⟩ : Fin (m + n + 1)))
      → OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
          ((pSpec₁ ++ₚ pSpec₂).Transcript
              (⟨m + ((i₂.1.castSucc : Fin (n + 1)) : ℕ), by omega⟩ : Fin (m + n + 1))
            × (pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂)) :=
    fun p => do
      let challenge ← OracleComp.liftComp
        ((pSpec₁ ++ₚ pSpec₂).getChallenge (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂))
        (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
      pure (p.1, challenge)
  -- STEP 2: bind congruence over the top-level bind into `(seam-run) >>= K'`, then collapse the
  -- inner `do`-block by `bind_assoc` to the stated RHS.  `K'` reads only the transcript component, so
  -- the (discarded) trailing state cast in the seam run is irrelevant.
  refine HEq.trans (Prover.bind_heq_congr (congrArg₂ Prod hTrTy hPrvTy)
    (by rw [hTrTy]) (f' := K') hRunHeq (fun ⟨trA, stA⟩ ⟨trB, stB⟩ hpair => ?_)) (heq_of_eq ?_)
  · -- continuation HEq: same combined `getChallenge`, then `pure (·, challenge)` on HEq transcripts.
    obtain ⟨htr, _⟩ := Prover.prod_heq_split hTrTy hPrvTy hpair
    refine Prover.bind_heq_congr rfl (by rw [hTrTy]) HEq.rfl ?_
    rintro cA cB hc
    exact Prover.pure_heq_pure (by rw [hTrTy]) (Prover.prodMk_heq hTrTy rfl htr hc)
  · -- the inner-block collapse: `(seam-run) >>= K' = stated RHS`.
    show _ >>= K' = _
    simp only [K', bind_assoc, pure_bind]

/-- **Phase-2 inner seam reconciliation residual.** The single remaining typed gap of
`appendRbrKnowledgeSoundnessPhase2_subsingleton`: at a fixed Subsingleton state `s` and a realized
`Prover.fst`-output `ctx = (tr₁, seamState, ())`, the appended phase-2 inner game — running
`Prover.snd prover` from the realized seam state under the **combined** challenge oracle, prefixing the
phase-2 transcript with the realized phase-1 transcript `ctx.1` via `Transcript.appendRight`, and
reading the per-round flip event through the *composite* `KnowledgeStateFunction.append` /
`Extractor.RoundByRound.append` — has the same event-probability as the inner `pSpec₂` snd game (over
`pSpec₂`'s **own** challenge oracle, with the event read directly through `kSF₂` / `E₂` at the realized
seam statement `verify stmtIn ctx.1`).

This is the phase-2 analogue of the proven phase-1 witness-event correspondence
(`appendRbrKnowledgeSoundnessPerRound_phase1`): it combines the right challenge-oracle-seam transfer
`OracleReduction.evalDist_run'_challengeSeam_right` (via `Prover.append_getChallenge_natAdd`) with the
gt-event collapse `KnowledgeStateFunction.append_toFun_gt` / `appendExtractMid_gt`, under the
`Transcript.appendRight ctx.1` prefix. -/
def appendRbrKnowledgePhase2SeamReconcile {WitMid₁ : Fin (m+1)→Type} {WitMid₂ : Fin (n+1)→Type}
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}
    {E₁ : Extractor.RoundByRound oSpec Stmt₁ Wit₁ Wit₂ pSpec₁ WitMid₁}
    {E₂ : Extractor.RoundByRound oSpec Stmt₂ Wit₂ Wit₃ pSpec₂ WitMid₂}
    (kSF₁ : V₁.KnowledgeStateFunction init impl rel₁ rel₂ E₁)
    (kSF₂ : V₂.KnowledgeStateFunction init impl rel₂ rel₃ E₂)
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩) (hInit : ∃ s, s ∈ support init) : Prop :=
  ∀ (stmtIn : Stmt₁)
    (prover : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂)) (i₂ : pSpec₂.ChallengeIdx)
    (s : σ)
    (ctx : pSpec₁.FullTranscript ×
      prover.PrvState (Fin.castLE (show m + 1 ≤ m + n + 1 by omega) (Fin.last m)) × Unit),
    Pr[fun x =>
        ∃ witMid,
          ¬ (KnowledgeStateFunction.append V₁ V₂ kSF₁ kSF₂ verify hVerify hInit).toFun
              (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.castSucc stmtIn x.1
              ((Extractor.RoundByRound.append E₁ E₂ verify).extractMid
                (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1 stmtIn (x.1.concat x.2) witMid) ∧
            (KnowledgeStateFunction.append V₁ V₂ kSF₁ kSF₂ verify hVerify hInit).toFun
              (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.succ stmtIn (x.1.concat x.2) witMid
      | ((do
          let x ← (simulateQ (impl.addLift challengeQueryImpl
              : QueryImpl (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (StateT σ ProbComp))
              (liftM ((Prover.snd prover).runToRound i₂.1.castSucc ctx.2.1 ctx.2.2))).run' s
          let x_1 ← (simulateQ (impl.addLift challengeQueryImpl
              : QueryImpl (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (StateT σ ProbComp))
              (OracleComp.liftComp
                ((pSpec₁ ++ₚ pSpec₂).getChallenge (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂))
                (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ))).run' s
          (simulateQ (impl.addLift challengeQueryImpl
              : QueryImpl (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (StateT σ ProbComp))
              (pure (Transcript.appendRight ctx.1 x.1, x_1))).run' s) :
            ProbComp ((pSpec₁ ++ₚ pSpec₂).Transcript
              (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.castSucc
                × (pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂)))]
    = Pr[fun x =>
          ∃ witMid,
            ¬ kSF₂.toFun i₂.1.castSucc (verify stmtIn ctx.1) x.1
              (E₂.extractMid i₂.1 (verify stmtIn ctx.1) (x.1.concat x.2) witMid) ∧
              kSF₂.toFun i₂.1.succ (verify stmtIn ctx.1) (x.1.concat x.2) witMid
        | (simulateQ (impl.addLift challengeQueryImpl
              : QueryImpl (oSpec + [pSpec₂.Challenge]ₒ) (StateT σ ProbComp))
            (do
              let ⟨transcript, _⟩ ← ((Prover.snd prover).runToRound i₂.1.castSucc ctx.2.1 ()
                : OracleComp (oSpec + [pSpec₂.Challenge]ₒ)
                    (pSpec₂.Transcript i₂.1.castSucc × (Prover.snd prover).PrvState i₂.1.castSucc))
              let challenge ← liftComp (pSpec₂.getChallenge i₂)
                (oSpec + [pSpec₂.Challenge]ₒ)
              return (transcript, challenge))).run' s]

/-- **Discharge of the phase-2 per-round knowledge residual under `Subsingleton σ` (stateless /
transparent-oracle regime).** This proves `appendRbrKnowledgeSoundnessPhase2Residual` *unconditionally*
in the setting where the simulator state `σ` is a `Subsingleton` (e.g. `σ = Unit`, the case of
`oSpec = []ₒ` RingSwitching and transparent-BCS) and the seam round is a prover message
(`hDir`/`hDir₂`), modulo the isolated inner seam reconciliation
`appendRbrKnowledgePhase2SeamReconcile`.

This is exactly the regime that kills the three obstructions of the general residual:
* the **message-seam** obstruction is resolved by `hDir`/`hDir₂` (the hypotheses of
  `Prover.snd_runToRound_natAdd_seam` / `Prover.run_seam_factor`);
* the **carried-prover-state** obstruction is resolved by the amnesiac re-injection prover
  `Prover.sndAmnesiac P rSeam` (hardcoding the realized seam state, applied via `hBound₂`'s
  quantification over *all* `pSpec₂`-provers);
* the **oracle `σ`-threading** obstruction is resolved by `Subsingleton σ`: under it
  `simulateQ_run'_bind_of_subsingleton` makes the simulated bind distribute, so the threaded-state
  game equals the *bind* of the per-stage games, and `hBound₂` (init-averaged) applies pointwise to
  each realized seam transcript via `probEvent_bind_le_of_forall_le`. -/
theorem appendRbrKnowledgeSoundnessPhase2_subsingleton [Subsingleton σ]
    {WitMid₁ : Fin (m+1)→Type} {WitMid₂ : Fin (n+1)→Type}
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}
    {E₁ : Extractor.RoundByRound oSpec Stmt₁ Wit₁ Wit₂ pSpec₁ WitMid₁}
    {E₂ : Extractor.RoundByRound oSpec Stmt₂ Wit₂ Wit₃ pSpec₂ WitMid₂}
    (kSF₁ : V₁.KnowledgeStateFunction init impl rel₁ rel₂ E₁)
    (kSF₂ : V₂.KnowledgeStateFunction init impl rel₂ rel₃ E₂)
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩) (hInit : ∃ s, s ∈ support init)
    (hNEW₂ : Nonempty Wit₂) (hInitNF : Pr[⊥ | init] = 0)
    (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .P_to_V)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .P_to_V)
    {rbrKnowledgeError₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (hBound₂ : ∀ stmtIn : Stmt₂, ∀ witIn : Wit₂,
      ∀ prover : Prover oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂, ∀ i : pSpec₂.ChallengeIdx,
        Pr[fun ⟨transcript, challenge, _proveQueryLog⟩ =>
          ∃ witMid,
            ¬ kSF₂.toFun i.1.castSucc stmtIn transcript
              (E₂.extractMid i.1 stmtIn (transcript.concat challenge) witMid) ∧
              kSF₂.toFun i.1.succ stmtIn (transcript.concat challenge) witMid
        | do
          (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
            (do
              let ⟨⟨transcript, _⟩, proveQueryLog⟩ ←
                prover.runWithLogToRound i.1.castSucc stmtIn witIn
              let challenge ← liftComp (pSpec₂.getChallenge i) _
              return (transcript, challenge, proveQueryLog))).run' (← init)] ≤
          rbrKnowledgeError₂ i)
    (hReconcile : appendRbrKnowledgePhase2SeamReconcile (init := init) (impl := impl)
      V₁ V₂ kSF₁ kSF₂ verify hVerify hInit) :
    appendRbrKnowledgeSoundnessPhase2Residual (init := init) (impl := impl) V₁ V₂
      kSF₁ kSF₂ verify hVerify hInit (rbrKnowledgeError₂ := rbrKnowledgeError₂) := by
  intro stmtIn witIn prover i₂
  classical
  have hpos : 0 < ((i₂.1 : Fin n) : ℕ) := challengeIdx_val_pos_of_seam_msg (i₂ := i₂) hn hDir₂
  -- Abbreviations for the appended phase-2 per-round event `E` and the seam-factored experiment body.
  set E : (pSpec₁ ++ₚ pSpec₂).Transcript (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.castSucc
      × (pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂) → Prop :=
    fun ⟨transcript, challenge⟩ =>
      ∃ witMid,
        ¬ (KnowledgeStateFunction.append V₁ V₂ kSF₁ kSF₂ verify hVerify hInit).toFun
            (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.castSucc stmtIn transcript
            ((Extractor.RoundByRound.append E₁ E₂ verify).extractMid
              (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1 stmtIn
              (transcript.concat challenge) witMid) ∧
          (KnowledgeStateFunction.append V₁ V₂ kSF₁ kSF₂ verify hVerify hInit).toFun
            (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.succ stmtIn
            (transcript.concat challenge) witMid with hE
  -- The seam index identity and the induced transcript value-type equality.
  have hidx : (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.castSucc
      = (⟨m + ((i₂.1.castSucc : Fin (n + 1)) : ℕ), by omega⟩ : Fin (m + n + 1)) := by
    ext; simp [ChallengeIdx.inr]
  have hTrTy : (pSpec₁ ++ₚ pSpec₂).Transcript (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.castSucc
      = (pSpec₁ ++ₚ pSpec₂).Transcript
          (⟨m + ((i₂.1.castSucc : Fin (n + 1)) : ℕ), by omega⟩ : Fin (m + n + 1)) := by rw [hidx]
  have hResTy : ((pSpec₁ ++ₚ pSpec₂).Transcript (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.castSucc
        × (pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂))
      = ((pSpec₁ ++ₚ pSpec₂).Transcript
            (⟨m + ((i₂.1.castSucc : Fin (n + 1)) : ℕ), by omega⟩ : Fin (m + n + 1))
          × (pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂)) :=
    congrArg (· × _) hTrTy
  -- STEP 1: transport the appended game to the seam-factored game via `phase2_body_heq`.
  have hbody := phase2_body_heq prover stmtIn witIn i₂ hn hDir hDir₂
  -- evalDist HEq of the two experiments, from the body HEq.
  have hd : HEq
      (𝒟[init >>= fun s =>
        (simulateQ (impl.addLift challengeQueryImpl : QueryImpl (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (StateT σ ProbComp))
          (do
            let ⟨transcript, _⟩ ←
              prover.runToRound (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.castSucc stmtIn witIn
            let challenge ←
              liftComp ((pSpec₁ ++ₚ pSpec₂).getChallenge (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂)) _
            return (transcript, challenge))).run' s])
      (𝒟[init >>= fun s =>
        (simulateQ (impl.addLift challengeQueryImpl : QueryImpl (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (StateT σ ProbComp))
          (do
            let ⟨transcript₁, ctxIn₂⟩ ← liftM ((Prover.fst prover).run stmtIn witIn)
            let r ← liftM ((Prover.snd prover).runToRound i₂.1.castSucc ctxIn₂.1 ctxIn₂.2)
            let challenge ←
              liftComp ((pSpec₁ ++ₚ pSpec₂).getChallenge (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂)) _
            return (Transcript.appendRight transcript₁ r.1, challenge))).run' s]) := by
    -- A local `evalDist`-respects-HEq helper.
    have heq_evalDist : ∀ {A B : Type} (hAB : A = B) (a : ProbComp A) (b : ProbComp B),
        HEq a b → HEq (𝒟[a]) (𝒟[b]) := by
      intro A B hAB a b hab; subst hAB; rw [eq_of_heq hab]
    -- A local `(simulateQ _).run'`-respects-HEq helper (for the shared `s`-state).
    have heq_simrun : ∀ {A B : Type} (s : σ) (hAB : A = B)
        (a : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) A)
        (b : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) B), HEq a b →
        HEq ((simulateQ (impl.addLift challengeQueryImpl
              : QueryImpl (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (StateT σ ProbComp)) a).run' s)
            ((simulateQ (impl.addLift challengeQueryImpl
              : QueryImpl (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (StateT σ ProbComp)) b).run' s) := by
      intro A B s hAB a b hab; subst hAB; rw [eq_of_heq hab]
    refine heq_evalDist hResTy _ _ ?_
    -- The computation-level HEq: shared `init`, HEq continuations (only the value type differs).
    refine Prover.bind_heq_congr rfl hResTy HEq.rfl (fun s s' hs => ?_)
    cases eq_of_heq hs
    exact heq_simrun s hResTy _ _ hbody
  rw [probEvent_congr_heq hResTy _ _ E (fun x => E (hResTy ▸ x)) hd (fun x => Iff.rfl)]
  -- STEP 2: bound the seam-factored game via the Subsingleton bind split.
  -- Under `Subsingleton σ`, `simulateQ_run'_bind_of_subsingleton` distributes the simulated
  -- experiment over the seam bind `liftM (fst.run) >>= REST`.
  simp only [simulateQ_run'_bind_of_subsingleton]
  -- Outer bind over `init`: bound uniformly over each sampled `s`.
  refine probEvent_bind_le_of_forall_le (fun s _hs => ?_)
  -- Inner bind over the (simulated) `fst.run` realization `ctx = (tr₁, seamState, ())`.
  refine probEvent_bind_le_of_forall_le (fun ctx hctx => ?_)
  -- The realized seam statement `s₂ := verify stmtIn tr₁` and the amnesiac re-injection prover that
  -- resumes `Prover.snd prover` from the realized seam state `ctx.2.1`.
  set s₂ : Stmt₂ := verify stmtIn ctx.1 with hs₂
  -- Apply the inner bound `hBound₂` to the amnesiac prover, then `logfree_reduce` to drop its log.
  have hb := hBound₂ s₂ hNEW₂.some (Prover.sndAmnesiac prover ctx.2.1) i₂
  rw [OracleReduction.rbrKnowledge_logfree_reduce impl (Prover.sndAmnesiac prover ctx.2.1) i₂ s₂
      hNEW₂.some init
      (fun x => ∃ witMid, ¬ kSF₂.toFun i₂.1.castSucc s₂ x.1
          (E₂.extractMid i₂.1 s₂ (x.1.concat x.2) witMid) ∧
          kSF₂.toFun i₂.1.succ s₂ (x.1.concat x.2) witMid)] at hb
  -- The amnesiac's partial run is `Prover.snd prover`'s from the seam state `ctx.2.1`.
  simp only [Prover.sndAmnesiac_runToRound] at hb
  -- Under `Subsingleton σ`, the inner `init`-averaged game equals its value at our fixed `s` (all
  -- states are forced equal); with `Pr[⊥|init]=0`, `hb` collapses to the fixed-`s` snd game.
  rw [probEvent_bind_of_const init
      (r := Pr[fun x => ∃ witMid, ¬ kSF₂.toFun i₂.1.castSucc s₂ x.1
            (E₂.extractMid i₂.1 s₂ (x.1.concat x.2) witMid) ∧
            kSF₂.toFun i₂.1.succ s₂ (x.1.concat x.2) witMid
        | (simulateQ (impl.addLift challengeQueryImpl
            : QueryImpl (oSpec + [pSpec₂.Challenge]ₒ) (StateT σ ProbComp))
            (do
              let ⟨transcript, _⟩ ← (Prover.snd prover).runToRound i₂.1.castSucc ctx.2.1 ()
              let challenge ← liftComp (pSpec₂.getChallenge i₂) _
              return (transcript, challenge))).run' s])
      (fun s' _ => by rw [Subsingleton.elim s' s]; rfl),
      hInitNF] at hb
  simp only [tsub_zero, one_mul] at hb
  -- FINAL SEAM RECONCILIATION (the smallest remaining typed residual): the appended phase-2 inner
  -- game (combined challenge oracle, transcript prefixed by the realized phase-1 transcript `ctx.1`,
  -- event read through the composite `KnowledgeStateFunction.append` / `Extractor.RoundByRound.append`)
  -- equals — at our fixed Subsingleton state `s` — the inner `pSpec₂` snd game of `hb` (`pSpec₂`'s own
  -- challenge oracle, `kSF₂`/`E₂` at the realized seam statement `s₂ = verify stmtIn ctx.1`).  Two
  -- ingredients: (a) the right challenge-oracle-seam transfer `evalDist_run'_challengeSeam_right`
  -- (`append_getChallenge_natAdd`), and (b) the gt-event correspondence
  -- `KnowledgeStateFunction.append_toFun_gt` / `appendExtractMid_gt` (the phase-2 analogue of the
  -- proven phase-1 witness-event block), under the `appendRight ctx.1` transcript prefix.
  -- Discharge by the isolated inner seam reconciliation `hReconcile` (the appended combined-oracle
  -- inner game, with the `appendRight ctx.1` prefix and composite gt-event, equals the inner `pSpec₂`
  -- snd game of `hb`).
  unfold appendRbrKnowledgePhase2SeamReconcile at hReconcile
  exact le_of_eq_of_le (hReconcile stmtIn prover i₂ s ctx) hb

/-- **Round-by-round knowledge soundness append keystone, deterministic-`V₁` message-seam case.**

Removes the `kSF` residual of `append_rbrKnowledgeSoundness_keystone` and discharges the **phase-1**
half of the per-round knowledge bound entirely: the composite knowledge state function is supplied
internally from the *proven* `KnowledgeStateFunction.append`, the composite extractor from the proven
`Extractor.RoundByRound.append`, and the phase-1 per-round bound is proven internally by
`appendRbrKnowledgeSoundnessPerRound` from the inner bound `hBound₁` destructured from `h₁` (the
run-level seam factoring `Prover.fst_runToRound_heq`, recast via `fstCastK`, with the appended
composite objects collapsing to `kSF₁` / `E₁` via `KnowledgeStateFunction.append_toFun_le` /
`appendExtractMid_le`).

The single remaining content is the **phase-2** seam-crossing leg, isolated as the typed residual
`hPhase2` (`appendRbrKnowledgeSoundnessPhase2Residual`): at a phase-2 round the appended objects
collapse to `kSF₂` / `E₂` at the `verify`-fed **random** intermediate statement, whose discharge needs
the `Prover.snd` run-seam factoring and a `probEvent_bind` averaging over the realized phase-1
transcript.  Unlike the plain-soundness phase-2 obstruction, this *is* dischargeable in principle —
`hBound₂` from `h₂` quantifies over **all** input statements (no `∉ langIn` restriction;
`RoundByRound.lean:839`), so the random seam statement is controlled — but it is left here as an
explicit typed hypothesis (exactly as the proven soundness keystone isolates its phase-2 residual).

The mild `Nonempty Stmt₂` / `Nonempty Wit₂` side conditions (mirroring the `hNE` of
`append_rbrSoundness_keystone`) supply the dummy output of the phase-1 `fstCastK` recast.  This
keystone is fully axiom-clean (no `sorry`). -/
theorem append_rbrKnowledgeSoundness_keystone_unconditional
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}
    {rbrKnowledgeError₁ : pSpec₁.ChallengeIdx → ℝ≥0}
    {rbrKnowledgeError₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩)
    (hInit : ∃ s, s ∈ support init)
    (hNE₂ : Nonempty Stmt₂) (hNEW₂ : Nonempty Wit₂)
    (h₁ : V₁.rbrKnowledgeSoundness init impl rel₁ rel₂ rbrKnowledgeError₁)
    (h₂ : V₂.rbrKnowledgeSoundness init impl rel₂ rel₃ rbrKnowledgeError₂)
    -- The single remaining seam-crossing residual (phase 2), quantified over the inner extractors /
    -- knowledge state functions destructured from `h₁` / `h₂`.
    (hPhase2 : ∀ {WitMid₁ : Fin (m+1)→Type} {WitMid₂ : Fin (n+1)→Type}
      {E₁ : Extractor.RoundByRound oSpec Stmt₁ Wit₁ Wit₂ pSpec₁ WitMid₁}
      {E₂ : Extractor.RoundByRound oSpec Stmt₂ Wit₂ Wit₃ pSpec₂ WitMid₂}
      (kSF₁ : V₁.KnowledgeStateFunction init impl rel₁ rel₂ E₁)
      (kSF₂ : V₂.KnowledgeStateFunction init impl rel₂ rel₃ E₂),
      appendRbrKnowledgeSoundnessPhase2Residual (init := init) (impl := impl) V₁ V₂ kSF₁ kSF₂
        verify hVerify hInit (rbrKnowledgeError₂ := rbrKnowledgeError₂)) :
      (V₁.append V₂).rbrKnowledgeSoundness init impl rel₁ rel₃
        (Sum.elim rbrKnowledgeError₁ rbrKnowledgeError₂ ∘ ChallengeIdx.sumEquiv.symm) := by
  obtain ⟨WitMid₁, E₁, kSF₁, hBound₁⟩ := h₁
  obtain ⟨WitMid₂, E₂, kSF₂, _hBound₂⟩ := h₂
  exact ⟨_, Extractor.RoundByRound.append E₁ E₂ verify,
    KnowledgeStateFunction.append V₁ V₂ kSF₁ kSF₂ verify hVerify hInit,
    appendRbrKnowledgeSoundnessPerRound V₁ V₂ kSF₁ kSF₂ verify hVerify hInit hNE₂ hNEW₂
      hBound₁ (hPhase2 kSF₁ kSF₂)⟩

/-- **Round-by-round knowledge soundness append keystone, `Subsingleton σ` message-seam case.**

The stateless / transparent-oracle specialization of `append_rbrKnowledgeSoundness_keystone_unconditional`:
in the `Subsingleton σ` regime (e.g. `σ = Unit`, the case of `oSpec = []ₒ` RingSwitching and
transparent-BCS), with a lossless `init` and a prover-message seam (`hDir`/`hDir₂`), the phase-2
seam-crossing leg is discharged **internally** by `appendRbrKnowledgeSoundnessPhase2_subsingleton` —
which kills the three obstructions of the general residual (message-seam via `hDir`/`hDir₂`,
carried-prover-state via the amnesiac re-injection `Prover.sndAmnesiac`, and `σ`-state threading via
`simulateQ_run'_bind_of_subsingleton`).

The only remaining content is the per-realization inner *seam reconciliation*
`appendRbrKnowledgePhase2SeamReconcile` (the phase-2 analogue of the proven phase-1 witness-event
correspondence: right challenge-oracle-seam transfer + gt-event collapse under the `appendRight`
prefix), isolated as the explicit typed residual `hReconcile` (quantified over the inner extractors /
knowledge state functions destructured from `h₁` / `h₂`).  Everything else — the Subsingleton bind
split, the amnesiac `hBound₂` application, and the seam factoring — is proven axiom-clean. -/
theorem append_rbrKnowledgeSoundness_keystone_subsingleton [Subsingleton σ]
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}
    {rbrKnowledgeError₁ : pSpec₁.ChallengeIdx → ℝ≥0}
    {rbrKnowledgeError₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩)
    (hInit : ∃ s, s ∈ support init) (hInitNF : Pr[⊥ | init] = 0)
    (hNE₂ : Nonempty Stmt₂) (hNEW₂ : Nonempty Wit₂)
    (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .P_to_V)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .P_to_V)
    (h₁ : V₁.rbrKnowledgeSoundness init impl rel₁ rel₂ rbrKnowledgeError₁)
    (h₂ : V₂.rbrKnowledgeSoundness init impl rel₂ rel₃ rbrKnowledgeError₂)
    -- The single remaining inner seam reconciliation (the phase-2 analogue of the proven phase-1
    -- witness-event correspondence), quantified over the inner extractors / knowledge state functions.
    (hReconcile : ∀ {WitMid₁ : Fin (m+1)→Type} {WitMid₂ : Fin (n+1)→Type}
      {E₁ : Extractor.RoundByRound oSpec Stmt₁ Wit₁ Wit₂ pSpec₁ WitMid₁}
      {E₂ : Extractor.RoundByRound oSpec Stmt₂ Wit₂ Wit₃ pSpec₂ WitMid₂}
      (kSF₁ : V₁.KnowledgeStateFunction init impl rel₁ rel₂ E₁)
      (kSF₂ : V₂.KnowledgeStateFunction init impl rel₂ rel₃ E₂),
      appendRbrKnowledgePhase2SeamReconcile (init := init) (impl := impl) V₁ V₂ kSF₁ kSF₂
        verify hVerify hInit) :
      (V₁.append V₂).rbrKnowledgeSoundness init impl rel₁ rel₃
        (Sum.elim rbrKnowledgeError₁ rbrKnowledgeError₂ ∘ ChallengeIdx.sumEquiv.symm) := by
  obtain ⟨WitMid₁, E₁, kSF₁, hBound₁⟩ := h₁
  obtain ⟨WitMid₂, E₂, kSF₂, hBound₂⟩ := h₂
  exact ⟨_, Extractor.RoundByRound.append E₁ E₂ verify,
    KnowledgeStateFunction.append V₁ V₂ kSF₁ kSF₂ verify hVerify hInit,
    appendRbrKnowledgeSoundnessPerRound V₁ V₂ kSF₁ kSF₂ verify hVerify hInit hNE₂ hNEW₂
      hBound₁ (appendRbrKnowledgeSoundnessPhase2_subsingleton V₁ V₂ kSF₁ kSF₂ verify hVerify hInit
        hNEW₂ hInitNF hn hDir hDir₂ hBound₂ (hReconcile kSF₁ kSF₂))⟩

end Verifier

-- Axiom audit for the sorry-free bricks: each should report only
-- `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms Verifier.appendWitMid_le
#print axioms Verifier.appendWitMid_gt
#print axioms Verifier.appendExtractMid_le
#print axioms Verifier.appendExtractMid_gt
#print axioms Verifier.appendExtractMid_cross
#print axioms Verifier.appendExtractOut_gt
#print axioms Verifier.kToFun_congr
#print axioms Verifier.kToFun_congr₁
#print axioms Verifier.concat_fst_heq_phase1
#print axioms Verifier.extractMid₁_heq_congr
#print axioms Verifier.KnowledgeStateFunction.append
#print axioms Verifier.KnowledgeStateFunction.append_toFun_le
#print axioms Verifier.KnowledgeStateFunction.append_toFun_gt
#print axioms Verifier.appendRbrKnowledgeSoundness_logfree_reduce
#print axioms Verifier.appendRbrKnowledgeSoundnessPerRound_phase1
#print axioms Verifier.appendRbrKnowledgeSoundnessPerRound
#print axioms Verifier.append_rbrKnowledgeSoundness_keystone_unconditional
#print axioms Prover.sndAmnesiac
#print axioms Prover.sndAmnesiac_runToRound
#print axioms Verifier.challengeIdx_val_pos_of_seam_msg
#print axioms Verifier.phase2_body_heq
#print axioms Verifier.appendRbrKnowledgeSoundnessPhase2_subsingleton
#print axioms Verifier.append_rbrKnowledgeSoundness_keystone_subsingleton
