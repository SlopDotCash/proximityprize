/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.Composition.Sequential.AppendRbrKnowledgeStateFunction
import ArkLib.OracleReduction.Composition.Sequential.AppendRightPartialProjections

/-!
# Discharge of the phase-2 seam reconciliation (rbr knowledge soundness append)

This file proves `appendRbrKnowledgePhase2SeamReconcile` — the single remaining typed residual of
`Verifier.append_rbrKnowledgeSoundness_keystone_subsingleton` — and assembles the resulting
**fully unconditional** round-by-round knowledge soundness append keystone in the
`Subsingleton σ` (stateless / transparent-oracle) message-seam regime:
`append_rbrKnowledgeSoundness_keystone_subsingleton_unconditional`.

The reconciliation is the phase-2 analogue of the proven phase-1 witness-event correspondence
(`appendRbrKnowledgeSoundnessPerRound_phase1`).  Its three ingredients, all previously proven:

* **(A) body recombination** — the three-block Subsingleton-split experiment recombines (via
  `simulateQ_run'_bind_of_subsingleton`, read right-to-left) into a single simulated body, which is
  the `liftComp` of a `pSpec₂`-own inner body producing combined-spec values; the combined
  `getChallenge (.inr i₂)` collapses to `pSpec₂.getChallenge i₂` by
  `Prover.append_getChallenge_natAdd`.
* **(B) right challenge-oracle-seam transfer** — `OracleReduction.evalDist_run'_challengeSeam_right`
  trades the combined challenge oracle for `pSpec₂`'s own.
* **(C) gt-event collapse** — under the `Transcript.appendRight ctx.1` prefix, the composite
  `KnowledgeStateFunction.append` / `Extractor.RoundByRound.append` collapse to `kSF₂` / `E₂` at the
  realized seam statement `verify stmtIn ctx.1`, via `KnowledgeStateFunction.append_toFun_gt` /
  `appendExtractMid_gt` and the partial `appendRight` projections (`appendRight_fst/snd`,
  `appendRight_concat_fst/snd`).
-/

open OracleComp OracleSpec ProtocolSpec SubSpec
open scoped ENNReal NNReal

namespace Verifier

variable {ι : Type} {oSpec : OracleSpec ι} {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

omit [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)] in
/-- **Dependent congruence for a knowledge state function's `toFun`, statement-aware.** Like
`kToFun_congr`, but additionally transporting an *equality of statements* — the phase-2 collapse
produces `kSF₂.toFun` at the `verify`-fed statement read off the appended transcript's phase-1
truncation, which is propositionally (not syntactically) the realized seam statement
`verify stmtIn ctx.1`. -/
theorem kToFun_congr_stmt {WitMid : Fin (n+1) → Type} {Stmt : Type}
    (f : (r : Fin (n+1)) → Stmt → pSpec₂.Transcript r → WitMid r → Prop)
    {r₁ r₂ : Fin (n+1)} (hr : r₁ = r₂) {stmt₁ stmt₂ : Stmt} (hstmt : stmt₁ = stmt₂)
    {t₁ : pSpec₂.Transcript r₁} {t₂ : pSpec₂.Transcript r₂} (ht : HEq t₁ t₂)
    {w₁ : WitMid r₁} {w₂ : WitMid r₂} (hw : HEq w₁ w₂) :
    f r₁ stmt₁ t₁ w₁ = f r₂ stmt₂ t₂ w₂ := by
  subst hr; subst hstmt; rw [eq_of_heq ht, eq_of_heq hw]

/-- **Discharge of the phase-2 inner seam reconciliation.** Proves
`appendRbrKnowledgePhase2SeamReconcile` under `Subsingleton σ` and the prover-message seam
(`hDir₂ : pSpec₂.dir 0 = .P_to_V`, which forces every `pSpec₂` challenge index to be interior,
`0 < i₂.1`, so the gt-collapse lemmas apply at both the `castSucc` and `succ` rounds). -/
theorem appendRbrKnowledgePhase2SeamReconcile_proof [Subsingleton σ]
    {WitMid₁ : Fin (m+1)→Type} {WitMid₂ : Fin (n+1)→Type}
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}
    {E₁ : Extractor.RoundByRound oSpec Stmt₁ Wit₁ Wit₂ pSpec₁ WitMid₁}
    {E₂ : Extractor.RoundByRound oSpec Stmt₂ Wit₂ Wit₃ pSpec₂ WitMid₂}
    (kSF₁ : V₁.KnowledgeStateFunction init impl rel₁ rel₂ E₁)
    (kSF₂ : V₂.KnowledgeStateFunction init impl rel₂ rel₃ E₂)
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩) (hInit : ∃ s, s ∈ support init)
    (hDir₂ : ∀ (hn : 0 < n), pSpec₂.dir (⟨0, hn⟩ : Fin n) = .P_to_V) :
    appendRbrKnowledgePhase2SeamReconcile (init := init) (impl := impl)
      V₁ V₂ kSF₁ kSF₂ verify hVerify hInit := by
  intro stmtIn prover i₂ s ctx
  classical
  have hn : 0 < n := Fin.pos_iff_nonempty.mpr ⟨i₂.1⟩
  have hpos : 0 < ((i₂.1 : Fin n) : ℕ) :=
    challengeIdx_val_pos_of_seam_msg (i₂ := i₂) hn (hDir₂ hn)
  -- The combined-spec phase-2 per-round event (verbatim from the goal LHS).
  set E : (pSpec₁ ++ₚ pSpec₂).Transcript (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.castSucc
      × (pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂) → Prop :=
    fun x =>
      ∃ witMid,
        ¬ (KnowledgeStateFunction.append V₁ V₂ kSF₁ kSF₂ verify hVerify hInit).toFun
            (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.castSucc stmtIn x.1
            ((Extractor.RoundByRound.append E₁ E₂ verify).extractMid
              (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1 stmtIn (x.1.concat x.2) witMid) ∧
          (KnowledgeStateFunction.append V₁ V₂ kSF₁ kSF₂ verify hVerify hInit).toFun
            (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.succ stmtIn (x.1.concat x.2) witMid
    with hEdef
  -- The recombined LHS body (combined oracle).
  set BODY : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
      ((pSpec₁ ++ₚ pSpec₂).Transcript (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.castSucc
        × (pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂)) :=
    (do
      let x ← liftM ((Prover.snd prover).runToRound i₂.1.castSucc ctx.2.1 ctx.2.2)
      let x_1 ← OracleComp.liftComp
        ((pSpec₁ ++ₚ pSpec₂).getChallenge (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂))
        (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
      pure (Transcript.appendRight ctx.1 x.1, x_1)) with hBODY
  show Pr[E | _] = _
  -- Reduce the goal's 3-block computation to `(simulateQ impl BODY).run' s` via the subsingleton
  -- split.
  suffices hkey : Pr[E | (simulateQ (impl.addLift challengeQueryImpl
        : QueryImpl (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (StateT σ ProbComp)) BODY).run' s]
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
              return (transcript, challenge))).run' s] by
    simpa only [hBODY, simulateQ_run'_bind_of_subsingleton] using hkey
  -- The challenge value-type equality at the phase-2 index.
  have hChTy : (pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂)
      = pSpec₂.Challenge i₂ := by
    show (pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inr i₂) = pSpec₂.Challenge i₂
    simp [ChallengeIdx.inr, ProtocolSpec.append]
  have hChalDir : (pSpec₁ ++ₚ pSpec₂).dir (Fin.natAdd m i₂.1) = .V_to_P := by
    rw [Prover.append_dir_natAdd i₂.1]; exact i₂.2
  -- The inner pSpec₂-own body that produces *combined* values (challenge cast into combined spec).
  set INNER : OracleComp (oSpec + [pSpec₂.Challenge]ₒ)
      ((pSpec₁ ++ₚ pSpec₂).Transcript (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.castSucc
        × (pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂)) :=
    (do
      let r ← (Prover.snd prover).runToRound i₂.1.castSucc ctx.2.1 ()
      let ch ← OracleComp.liftComp (pSpec₂.getChallenge i₂) (oSpec + [pSpec₂.Challenge]ₒ)
      pure (Transcript.appendRight ctx.1 r.1, cast hChTy.symm ch)) with hINNER
  -- STEP A: `BODY = liftComp INNER combined` (same combined value type ⟹ HEq is Eq).
  have hbodyEq : BODY = OracleComp.liftComp INNER (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) := by
    apply eq_of_heq
    rw [hBODY, hINNER]
    rw [OracleComp.liftComp_bind]
    refine Prover.bind_heq_congr rfl rfl ?_ ?_
    · -- the snd run: `ctx.2.2 = ()` and `liftM = liftComp`.
      rfl
    · rintro ⟨tr, st⟩ ⟨tr', st'⟩ hpair
      obtain ⟨htr, _⟩ := Prover.prod_heq_split rfl rfl hpair
      rw [OracleComp.liftComp_bind]
      refine Prover.bind_heq_congr hChTy rfl ?_ ?_
      · -- the challenge: combined getChallenge (lifted) ≍ liftComp (pSpec₂ getChallenge).
        have hChTy' : (pSpec₁ ++ₚ pSpec₂).Challenge (⟨Fin.natAdd m i₂.1, hChalDir⟩) =
            pSpec₂.Challenge i₂ := hChTy
        have hgc := Prover.append_getChallenge_natAdd (pSpec₁ := pSpec₁) i₂.1 hChalDir i₂.2
        rw [show (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂)
              = (⟨Fin.natAdd m i₂.1, hChalDir⟩ : (pSpec₁ ++ₚ pSpec₂).ChallengeIdx) from rfl]
        -- transport `hgc` through the outer `liftComp ... combined`.
        refine HEq.trans (Prover.liftComp_heq_congr
          (superSpec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) hChTy' hgc) ?_
        apply heq_of_eq
        rw [show (liftM (pSpec₂.getChallenge i₂)
                : OracleComp [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ _)
              = OracleComp.liftComp (pSpec₂.getChallenge i₂) [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ from
            (OracleComp.liftComp_eq_liftM _).symm]
        rw [show OracleComp.liftComp (OracleComp.liftComp (pSpec₂.getChallenge i₂)
                  [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
                = OracleComp.liftComp (pSpec₂.getChallenge i₂)
                    (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
              from Prover.liftComp_liftComp (midSpec := [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
                  (superSpec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
                  (fun t => rfl) (pSpec₂.getChallenge i₂),
            show OracleComp.liftComp (OracleComp.liftComp (pSpec₂.getChallenge i₂)
                  (oSpec + [pSpec₂.Challenge]ₒ)) (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
                = OracleComp.liftComp (pSpec₂.getChallenge i₂)
                    (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
              from Prover.liftComp_liftComp (midSpec := oSpec + [pSpec₂.Challenge]ₒ)
                  (superSpec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
                  (fun t => rfl) (pSpec₂.getChallenge i₂)]
      · rintro cA cB hc
        refine Prover.pure_heq_pure rfl ?_
        refine Prover.prodMk_heq rfl rfl ?_ ?_
        · exact congrArg (Transcript.appendRight ctx.1) (eq_of_heq htr) ▸ HEq.rfl
        · exact ((cast_heq hChTy.symm cB).trans hc.symm).symm
  rw [hbodyEq]
  -- STEP B: challenge-seam transfer (right half): combined → pSpec₂-own oracle, at `probEvent`.
  rw [show OracleComp.liftComp INNER (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
        = (liftM INNER : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _) from
      OracleComp.liftComp_eq_liftM _]
  have hseam := OracleReduction.evalDist_run'_challengeSeam_right (pSpec₁ := pSpec₁)
    (impl := impl) INNER s
  rw [probEvent_congr_heq rfl _
    ((simulateQ (impl.addLift (challengeQueryImpl (pSpec := pSpec₂))
      : QueryImpl _ (StateT σ ProbComp)) INNER).run' s) E E (heq_of_eq hseam) (fun x => Iff.rfl)]
  -- STEP C: `INNER = wrap <$> RHSbody`; push the map out and collapse via `probEvent_map`.
  set RHSbody : OracleComp (oSpec + [pSpec₂.Challenge]ₒ)
      (pSpec₂.Transcript i₂.1.castSucc × pSpec₂.Challenge i₂) :=
    (do
      let ⟨transcript, _⟩ ← ((Prover.snd prover).runToRound i₂.1.castSucc ctx.2.1 ()
        : OracleComp (oSpec + [pSpec₂.Challenge]ₒ)
            (pSpec₂.Transcript i₂.1.castSucc × (Prover.snd prover).PrvState i₂.1.castSucc))
      let challenge ← liftComp (pSpec₂.getChallenge i₂) (oSpec + [pSpec₂.Challenge]ₒ)
      return (transcript, challenge)) with hRHSbody
  set wrap : (pSpec₂.Transcript i₂.1.castSucc × pSpec₂.Challenge i₂)
      → ((pSpec₁ ++ₚ pSpec₂).Transcript (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.castSucc
          × (pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂)) :=
    fun p => (Transcript.appendRight ctx.1 p.1, cast hChTy.symm p.2) with hwrap
  have hINNERmap : INNER = wrap <$> RHSbody := by
    rw [hINNER, hRHSbody, hwrap, map_eq_bind_pure_comp, bind_assoc]
    refine bind_congr fun r => ?_
    obtain ⟨t, st⟩ := r
    simp only [bind_assoc, pure_bind, Function.comp_apply]
  rw [hINNERmap]
  -- push `wrap <$>` out of `(simulateQ _).run' s`.
  rw [show (simulateQ (impl.addLift (challengeQueryImpl (pSpec := pSpec₂))
          : QueryImpl _ (StateT σ ProbComp)) (wrap <$> RHSbody)).run' s
        = wrap <$> (simulateQ (impl.addLift (challengeQueryImpl (pSpec := pSpec₂))
          : QueryImpl _ (StateT σ ProbComp)) RHSbody).run' s from by
      simp only [simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map]]
  rw [probEvent_map]
  -- STEP D: the event correspondence `E ∘ wrap = E_inner` (pointwise).
  refine congrArg (fun p => Pr[p | (simulateQ (impl.addLift (challengeQueryImpl (pSpec := pSpec₂))
      : QueryImpl _ (StateT σ ProbComp)) RHSbody).run' s]) ?_
  funext x
  apply propext
  -- Notation: `trW := appendRight ctx.1 x.1`, the wrapped combined transcript; `chW := cast .. x.2`.
  set trW : (pSpec₁ ++ₚ pSpec₂).Transcript (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.castSucc :=
    Transcript.appendRight ctx.1 x.1 with htrW
  set chW : (pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂) :=
    cast hChTy.symm x.2 with hchW
  show E (trW, chW) ↔ _
  rw [hEdef]
  simp only []
  -- gt-round facts.
  have hval : ((ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1).val = m + (i₂.1 : ℕ) := by
    simp [ChallengeIdx.inr]
  have hcs_gt : ¬ ((ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.castSucc).val ≤ m := by
    rw [Fin.val_castSucc, hval]; omega
  have hsu_gt : ¬ ((ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.succ).val ≤ m := by
    rw [Fin.val_succ, hval]; omega
  have hidx_gt : m < (((ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1) : ℕ) := by rw [hval]; omega
  -- The witness-leg type equality at the `.succ` round (phase-2 leg).
  have hWitTy : (Fin.append (m:=m+1) WitMid₁ (Fin.tail WitMid₂) ∘ Fin.cast (by omega))
        (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.succ
      = WitMid₂ i₂.1.succ := by
    rw [appendWitMid_gt hsu_gt]
    refine congrArg WitMid₂ (Fin.ext ?_)
    show ((ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.succ : ℕ) - m
      = ((i₂.1.succ : Fin (n + 1)) : ℕ)
    rw [Fin.val_succ, Fin.val_succ, hval]; omega
  -- Transcript projections of `trW = appendRight ctx.1 x.1`.
  have htrW_fst : HEq (Transcript.fst trW) ctx.1 := by
    rw [htrW]; exact Transcript.appendRight_fst ctx.1 x.1
  have htrW_snd : HEq (Transcript.snd trW) x.1 := by
    rw [htrW]; exact Transcript.appendRight_snd ctx.1 x.1
  -- `chW` is the cast of the pSpec₂ message `x.2`; rewrite to the `append_Type_natAdd` cast form
  -- used by the `appendRight_concat` bricks.
  have hchW_eq : chW = cast (append_Type_natAdd i₂.1).symm x.2 := by
    rw [hchW]; rfl
  -- The concat'd transcript projections.
  have hconcat_fst : HEq (Transcript.fst (Transcript.concat chW trW)) ctx.1 := by
    rw [htrW, hchW_eq]
    exact Transcript.appendRight_concat_fst ctx.1 x.2 x.1
  have hconcat_snd : HEq (Transcript.snd (Transcript.concat chW trW))
      (Transcript.concat x.2 x.1) := by
    rw [htrW, hchW_eq]
    exact Transcript.appendRight_concat_snd ctx.1 x.2 x.1
  -- The phase-2 reindex of the toFun rounds: `(inr i₂).1.castSucc - m = i₂.1.castSucc` etc.
  have hidxcs : (⟨((ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.castSucc : ℕ) - m, by
        rw [Fin.val_castSucc, hval]; omega⟩ : Fin (n + 1)) = i₂.1.castSucc := by
    apply Fin.ext
    show ((ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.castSucc : ℕ) - m = (i₂.1.castSucc : ℕ)
    rw [Fin.val_castSucc, Fin.val_castSucc, hval]; omega
  have hidxsu : (⟨((ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.succ : ℕ) - m, by
        rw [Fin.val_succ, hval]; omega⟩ : Fin (n + 1)) = i₂.1.succ := by
    apply Fin.ext
    show ((ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.succ : ℕ) - m = (i₂.1.succ : ℕ)
    rw [Fin.val_succ, Fin.val_succ, hval]; omega
  -- The `Fin n`-level reindex (for the extractor leg) and the induced transport type equalities.
  have hidxFin : (⟨(((ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1) : ℕ) - m, by omega⟩ : Fin n)
      = i₂.1 := by
    apply Fin.ext
    show (((ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1) : ℕ) - m = (i₂.1 : ℕ)
    rw [hval]; omega
  have hTr2Ty : pSpec₂.Transcript i₂.1.succ
      = pSpec₂.Transcript
          (⟨(((ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1) : ℕ) - m, by omega⟩ : Fin n).succ := by
    rw [hidxFin]
  have hWit2Ty : WitMid₂ i₂.1.succ
      = WitMid₂
          (⟨(((ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1) : ℕ) - m, by omega⟩ : Fin n).succ := by
    rw [hidxFin]
  -- The extracted-witness HEq via `appendExtractMid_gt` (composite collapses to `E₂` at the
  -- realized seam statement), transported back to the canonical `i₂.1` index.
  have hExtHeq : ∀ (witMid : (Fin.append (m:=m+1) WitMid₁ (Fin.tail WitMid₂) ∘ Fin.cast (by omega))
        (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.succ) (wM : WitMid₂ i₂.1.succ), HEq witMid wM →
      HEq ((Extractor.RoundByRound.append E₁ E₂ verify).extractMid
            (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1 stmtIn (Transcript.concat chW trW) witMid)
          (E₂.extractMid i₂.1 (verify stmtIn ctx.1) (Transcript.concat x.2 x.1) wM) := by
    intro witMid wM hw
    refine HEq.trans (appendExtractMid_gt E₁ E₂ verify (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1
        hidx_gt stmtIn (Transcript.concat chW trW) witMid ctx.1 hconcat_fst
        (cast hTr2Ty (Transcript.concat x.2 x.1)) (hconcat_snd.trans (cast_heq hTr2Ty _).symm)
        (cast hWit2Ty wM) (hw.trans (cast_heq hWit2Ty wM).symm)) ?_
    exact extractMid₁_heq_congr (pSpec₁ := pSpec₂) E₂ (verify stmtIn ctx.1) hidxFin
      (cast_heq hTr2Ty _) (cast_heq hWit2Ty wM)
  -- The two-sided witness-threaded event correspondence (the phase-2 mirror of the proven phase-1
  -- block in `appendRbrKnowledgeSoundnessPerRound_phase1`).
  constructor
  · rintro ⟨witMid, hneg, hpos⟩
    refine ⟨cast hWitTy witMid, ?_, ?_⟩
    · intro hkSF
      apply hneg
      rw [KnowledgeStateFunction.append_toFun_gt V₁ V₂ kSF₁ kSF₂ verify hVerify hInit hcs_gt]
      refine (kToFun_congr_stmt kSF₂.toFun hidxcs ?_ ?_ ?_).mpr hkSF
      · exact congrArg (verify stmtIn) (eq_of_heq ((cast_heq _ _).trans htrW_fst))
      · exact HEq.trans HEq.rfl htrW_snd
      · exact (cast_heq _ _).trans (hExtHeq witMid (cast hWitTy witMid)
          (cast_heq hWitTy witMid).symm)
    · rw [KnowledgeStateFunction.append_toFun_gt V₁ V₂ kSF₁ kSF₂ verify hVerify hInit hsu_gt]
        at hpos
      refine (kToFun_congr_stmt kSF₂.toFun hidxsu ?_ ?_ ?_).mp hpos
      · exact congrArg (verify stmtIn) (eq_of_heq ((cast_heq _ _).trans hconcat_fst))
      · exact HEq.trans HEq.rfl hconcat_snd
      · exact (cast_heq _ _).trans (cast_heq hWitTy witMid).symm
  · rintro ⟨wM, hneg, hpos⟩
    refine ⟨cast hWitTy.symm wM, ?_, ?_⟩
    · intro hAppend
      apply hneg
      rw [KnowledgeStateFunction.append_toFun_gt V₁ V₂ kSF₁ kSF₂ verify hVerify hInit hcs_gt]
        at hAppend
      refine (kToFun_congr_stmt kSF₂.toFun hidxcs ?_ ?_ ?_).mp hAppend
      · exact congrArg (verify stmtIn) (eq_of_heq ((cast_heq _ _).trans htrW_fst))
      · exact HEq.trans HEq.rfl htrW_snd
      · exact (cast_heq _ _).trans (hExtHeq (cast hWitTy.symm wM) wM
          (cast_heq hWitTy.symm wM))
    · rw [KnowledgeStateFunction.append_toFun_gt V₁ V₂ kSF₁ kSF₂ verify hVerify hInit hsu_gt]
      refine (kToFun_congr_stmt kSF₂.toFun hidxsu ?_ ?_ ?_).mpr hpos
      · exact congrArg (verify stmtIn) (eq_of_heq ((cast_heq _ _).trans hconcat_fst))
      · exact HEq.trans HEq.rfl hconcat_snd
      · exact (cast_heq _ _).trans (cast_heq hWitTy.symm wM)

/-- **Round-by-round knowledge soundness append keystone, `Subsingleton σ` message-seam case —
UNCONDITIONAL.** The `hReconcile` residual of `append_rbrKnowledgeSoundness_keystone_subsingleton`
is discharged internally by `appendRbrKnowledgePhase2SeamReconcile_proof`; what remains are only the
standard structural side conditions of the regime: a deterministic first verifier (`hVerify` — which
*supplies* the `verify` map that the composite extractor and knowledge state function thread), a
reachable lossless `init`, the prover-message seam (`hDir`/`hDir₂`), and `Subsingleton σ` (the
stateless / transparent-oracle setting of the BCS and RingSwitching instances). -/
theorem append_rbrKnowledgeSoundness_keystone_subsingleton_unconditional [Subsingleton σ]
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
    (h₂ : V₂.rbrKnowledgeSoundness init impl rel₂ rel₃ rbrKnowledgeError₂) :
      (V₁.append V₂).rbrKnowledgeSoundness init impl rel₁ rel₃
        (Sum.elim rbrKnowledgeError₁ rbrKnowledgeError₂ ∘ ChallengeIdx.sumEquiv.symm) :=
  append_rbrKnowledgeSoundness_keystone_subsingleton V₁ V₂ verify hVerify hInit hInitNF
    hNE₂ hNEW₂ hn hDir hDir₂ h₁ h₂
    (fun kSF₁ kSF₂ => appendRbrKnowledgePhase2SeamReconcile_proof V₁ V₂ kSF₁ kSF₂
      verify hVerify hInit (fun _ => hDir₂))

end Verifier

-- Axiom audit: each should report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms Verifier.kToFun_congr_stmt
#print axioms Verifier.appendRbrKnowledgePhase2SeamReconcile_proof
#print axioms Verifier.append_rbrKnowledgeSoundness_keystone_subsingleton_unconditional
