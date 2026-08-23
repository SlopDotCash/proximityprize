/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.AppendRbrKnowledgeChallengeBody
import ArkLib.OracleReduction.Composition.Sequential.AppendRbrKnowledgePhase2ReconcileProof

/-!
# The seam-challenge (`i₂ = 0`) flip bound — discharge of `hSeamZero` (#114 rbr chain)

This file proves the **last named residual of the challenge-seam rbr knowledge-soundness append
keystone**: the per-round flip bound at the seam challenge itself (`i₂ = 0`, which exists only at
a `V_to_P` seam). Two theorems:

* `appendRbrKnowledgePhase2SeamReconcileZero_le` — the **zero-reconcile** (containment form):
  the `i₂ = 0` instance of the phase-2 seam reconciliation. The run side (STEPS A–C: body
  recombination, right challenge-oracle-seam transfer, `wrap`-map collapse) is identical to the
  proven positive-index reconcile `appendRbrKnowledgePhase2SeamReconcile_proof_pos`; the event
  side replaces the two-sided gt-collapse with a one-sided **containment** through the *semantic
  seam glue*. At the boundary the composite knowledge state function's value is `kSF₁`-at-last
  (the `dif_pos` branch) while the inner game's is `kSF₂`-at-`0`; the glue
  `¬ kSF₁-last → ¬ kSF₂-0(verify ·)` is the contrapositive of the chain
  `kSF₂.toFun_empty` → `run_pos_of_mem_rel` → `kSF₁.toFun_full` (truth propagated backwards
  across the seam through the deterministic `V₁ = pure ∘ verify`), with the appended extractor's
  crossing coherence `appendExtractMid_cross` identifying the two extracted witnesses. Since the
  flip event only needs an *inequality*, the containment (`probEvent_mono''`) suffices — no
  reverse implication is needed (and none holds in general: `kSF₁.toFun_full` is one-directional).

* `appendRbrKnowledgeSeamZero_proven` — the **`hSeamZero` discharge**: the appended experiment's
  seam-challenge flip probability is `≤ rbrKnowledgeError₂ i₂`, from the inner per-round bound
  `hBound₂` alone. The experiment factors through the proven seam-challenge zero body factoring
  `phase2_body_heq_challenge_zero` (at the seam challenge the appended run is `fst`'s full partial
  run with no right block), then the `Subsingleton σ` bind split + amnesiac re-injection of
  `hBound₂` (verbatim the positive-index branch of
  `appendRbrKnowledgeSoundnessPhase2_subsingleton_challenge`), and closes with the containment
  zero-reconcile.

With these, `Verifier.append_rbrKnowledgeSoundness_keystone_subsingleton_challenge`
(`AppendRbrKnowledgeChallenge.lean`) is **residual-free**, completing the rbr knowledge-soundness
append keystone triple (message / empty / challenge seams) in the `Subsingleton σ` regime.
-/

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace Verifier

variable {ι : Type} {oSpec : OracleSpec ι} {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- **Zero-reconcile (containment form).** The `i₂ = 0` instance of the phase-2 seam
reconciliation: at the seam challenge itself, the appended inner game's flip probability is
*bounded by* (not equal to) `kSF₂`'s own round-`0` flip probability at the realized seam statement
`verify stmtIn ctx.1`. The run side is identical to the proven positive-index reconcile
(`appendRbrKnowledgePhase2SeamReconcile_proof_pos`, STEPS A–C); the event side replaces the
two-sided gt-collapse with the one-sided **semantic seam glue**: a flip out of the composite
boundary value (`kSF₁`-at-last, the `dif_pos` branch) entails a flip out of `kSF₂`-at-`0`, via
`kSF₂.toFun_empty` → `run_pos_of_mem_rel` → `kSF₁.toFun_full` (contrapositive), with the appended
extractor's crossing coherence `appendExtractMid_cross` identifying the two extracted witnesses. -/
theorem appendRbrKnowledgePhase2SeamReconcileZero_le [Subsingleton σ]
    {WitMid₁ : Fin (m+1)→Type} {WitMid₂ : Fin (n+1)→Type}
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}
    {E₁ : Extractor.RoundByRound oSpec Stmt₁ Wit₁ Wit₂ pSpec₁ WitMid₁}
    {E₂ : Extractor.RoundByRound oSpec Stmt₂ Wit₂ Wit₃ pSpec₂ WitMid₂}
    (kSF₁ : V₁.KnowledgeStateFunction init impl rel₁ rel₂ E₁)
    (kSF₂ : V₂.KnowledgeStateFunction init impl rel₂ rel₃ E₂)
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩) (hInit : ∃ s, s ∈ support init)
    (stmtIn : Stmt₁)
    (prover : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂)) (i₂ : pSpec₂.ChallengeIdx)
    (hz : ((i₂.1 : Fin n) : ℕ) = 0)
    (s : σ)
    (ctx : pSpec₁.FullTranscript ×
      prover.PrvState (Fin.castLE (show m + 1 ≤ m + n + 1 by omega) (Fin.last m)) × Unit) :
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
    ≤ Pr[fun x =>
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
              return (transcript, challenge))).run' s] := by
  classical
  have hn : 0 < n := Fin.pos_iff_nonempty.mpr ⟨i₂.1⟩
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
  show Pr[E | _] ≤ _
  -- Reduce the goal's 3-block computation to `(simulateQ impl BODY).run' s` via the subsingleton
  -- split.
  suffices hkey : Pr[E | (simulateQ (impl.addLift challengeQueryImpl
        : QueryImpl (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (StateT σ ProbComp)) BODY).run' s]
      ≤ Pr[fun x =>
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
  -- STEP D (zero case): the event CONTAINMENT `E ∘ wrap ⊆ E_inner` (pointwise), via the semantic
  -- seam glue; conclude with `probEvent_mono''`.
  refine probEvent_mono'' (fun x hEx => ?_)
  -- Notation: `trW := appendRight ctx.1 x.1`, the wrapped combined transcript; `chW := cast .. x.2`.
  set trW : (pSpec₁ ++ₚ pSpec₂).Transcript (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.castSucc :=
    Transcript.appendRight ctx.1 x.1 with htrW
  set chW : (pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂) :=
    cast hChTy.symm x.2 with hchW
  have hx : E (trW, chW) := hEx
  rw [hEdef] at hx
  simp only [] at hx
  obtain ⟨witMid, hneg, hpos⟩ := hx
  -- zero-round facts.
  have hval : ((ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1).val = m + (i₂.1 : ℕ) := by
    simp [ChallengeIdx.inr]
  have hcs_le : ((ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.castSucc).val ≤ m := by
    rw [Fin.val_castSucc, hval, hz]; omega
  have hsu_gt : ¬ ((ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.succ).val ≤ m := by
    rw [Fin.val_succ, hval]; omega
  have hidx_eq : (((ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1) : ℕ) = m := by
    rw [hval, hz]; omega
  have hi₂0 : i₂.1 = (⟨0, hn⟩ : Fin n) := Fin.ext hz
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
  -- The phase-2 reindex of the `.succ` toFun round.
  have hidxsu : (⟨((ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.succ : ℕ) - m, by
        rw [Fin.val_succ, hval]; omega⟩ : Fin (n + 1)) = i₂.1.succ := by
    apply Fin.ext
    show ((ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.succ : ℕ) - m = (i₂.1.succ : ℕ)
    rw [Fin.val_succ, Fin.val_succ, hval]; omega
  -- The crossing-transport type equalities (the `Fin n`-index `⟨0, hn⟩` form of the seam round).
  have hTr0 : pSpec₂.Transcript i₂.1.succ = pSpec₂.Transcript (⟨0, hn⟩ : Fin n).succ := by
    rw [hi₂0]
  have hWit0 : WitMid₂ i₂.1.succ = WitMid₂ (⟨0, hn⟩ : Fin n).succ := by rw [hi₂0]
  -- The witness threaded into the inner event.
  refine ⟨cast hWitTy witMid, ?_, ?_⟩
  · -- THE SEMANTIC SEAM GLUE: a flip out of the composite boundary (kSF₁-at-last) entails a flip
    -- out of kSF₂-at-0 — contrapositive via toFun_empty → run_pos_of_mem_rel → toFun_full.
    intro hkSF
    apply hneg
    -- (i) reshape `hkSF` to round `0` with the (subsingleton) empty transcript.
    have hcs0 : i₂.1.castSucc = (0 : Fin (n + 1)) := by ext; simp [hz]
    set w0 : WitMid₂ i₂.1.castSucc :=
      E₂.extractMid i₂.1 (verify stmtIn ctx.1) ((Transcript.concat x.2 x.1))
        (cast hWitTy witMid) with hw0
    have hkSF0 : kSF₂.toFun 0 (verify stmtIn ctx.1) default
        (cast (congrArg WitMid₂ hcs0) w0) := by
      refine (kToFun_congr kSF₂.toFun hcs0 (verify stmtIn ctx.1) ?_ ?_).mp hkSF
      · -- `x.1 ≍ default` (both empty transcripts).
        apply Function.hfunext (by rw [hcs0])
        intro a a' _
        exact a'.elim0
      · exact (cast_heq _ _).symm
    -- (ii) `kSF₂.toFun_empty` → membership in `rel₂` at the realized seam statement.
    have hMem : (verify stmtIn ctx.1,
        cast E₂.eqIn (cast (congrArg WitMid₂ hcs0) w0)) ∈ rel₂ :=
      (kSF₂.toFun_empty (verify stmtIn ctx.1) (cast (congrArg WitMid₂ hcs0) w0)).mpr hkSF0
    -- (iii) deterministic-run positivity + `kSF₁.toFun_full`.
    have hPr := run_pos_of_mem_rel (impl := impl) (init := init) verify hVerify hInit stmtIn ctx.1
      (cast E₂.eqIn (cast (congrArg WitMid₂ hcs0) w0)) hMem
    have hFull := kSF₁.toFun_full stmtIn ctx.1
      (cast E₂.eqIn (cast (congrArg WitMid₂ hcs0) w0)) hPr
    -- (iv) the composite boundary value is `kSF₁`-at-last (`dif_pos`), and the appended extractor
    -- crosses through `E₂.extractMid 0` into `E₁.extractOut` (`appendExtractMid_cross`).
    rw [KnowledgeStateFunction.append_toFun_le V₁ V₂ kSF₁ kSF₂ verify hVerify hInit hcs_le]
    -- the crossing coherence of the appended extractor at the seam round.
    have hcross : HEq
        ((Extractor.RoundByRound.append E₁ E₂ verify).extractMid
          (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1 stmtIn (Transcript.concat chW trW) witMid)
        (E₁.extractOut stmtIn ctx.1
          (cast E₂.eqIn (E₂.extractMid (⟨0, hn⟩ : Fin n) (verify stmtIn ctx.1)
            (cast hTr0 (Transcript.concat x.2 x.1)) (cast hWit0 (cast hWitTy witMid))))) :=
      appendExtractMid_cross E₁ E₂ verify (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1 hidx_eq hn
        stmtIn (Transcript.concat chW trW) witMid ctx.1 hconcat_fst
        (cast hTr0 (Transcript.concat x.2 x.1)) (hconcat_snd.trans (cast_heq hTr0 _).symm)
        (cast hWit0 (cast hWitTy witMid))
        (((cast_heq hWit0 _).trans (cast_heq hWitTy witMid)).symm)
    -- identify the crossing's `E₂.extractMid ⟨0,hn⟩` leg with `w0` (canonical `i₂.1` index).
    have hlegs : HEq (E₂.extractMid (⟨0, hn⟩ : Fin n) (verify stmtIn ctx.1)
          (cast hTr0 (Transcript.concat x.2 x.1)) (cast hWit0 (cast hWitTy witMid))) w0 := by
      rw [hw0]
      exact extractMid₁_heq_congr (pSpec₁ := pSpec₂) E₂ (verify stmtIn ctx.1) hi₂0.symm
        (cast_heq hTr0 _) (cast_heq hWit0 _)
    have hcastEq : cast E₂.eqIn (cast (congrArg WitMid₂ hcs0) w0)
        = cast E₂.eqIn (E₂.extractMid (⟨0, hn⟩ : Fin n) (verify stmtIn ctx.1)
            (cast hTr0 (Transcript.concat x.2 x.1)) (cast hWit0 (cast hWitTy witMid))) := by
      apply eq_of_heq
      refine HEq.trans (cast_heq _ _) (HEq.trans (cast_heq _ _) ?_)
      exact (HEq.trans (cast_heq _ _) hlegs).symm
    rw [hcastEq] at hFull
    -- transport `hFull` across the index/transcript/witness coherences to the goal.
    refine Eq.mp (kToFun_congr₁ kSF₁.toFun ?_ stmtIn ?_ ?_) hFull
    · -- `last m = ⟨(inr i₂).castSucc.val, _⟩`.
      apply Fin.ext
      rw [Fin.val_last]
      exact (by rw [Fin.val_castSucc, hval, hz]; omega : ((ChallengeIdx.inr (pSpec₁ := pSpec₁)
        i₂).1.castSucc).val = m).symm
    · -- transcript: `ctx.1 ≍ (simpa'd trW.fst)`.
      exact htrW_fst.symm.trans (cast_heq _ _).symm
    · -- witness: `E₁.extractOut … ≍ cast (appendWitMid_le) (append.extractMid …)`.
      exact ((cast_heq _ _).trans hcross).symm
  · -- the `.succ` leg: identical to the positive-index case (the `.succ` round is interior).
    rw [KnowledgeStateFunction.append_toFun_gt V₁ V₂ kSF₁ kSF₂ verify hVerify hInit hsu_gt]
      at hpos
    refine (kToFun_congr_stmt kSF₂.toFun hidxsu ?_ ?_ ?_).mp hpos
    · exact congrArg (verify stmtIn) (eq_of_heq ((cast_heq _ _).trans hconcat_fst))
    · exact HEq.trans HEq.rfl hconcat_snd
    · exact (cast_heq _ _).trans (cast_heq hWitTy witMid).symm

/-- **Discharge of `hSeamZero`** — the per-round flip bound of the appended rbr knowledge
experiment at the seam challenge itself (`i₂ = 0`, which exists only at a `V_to_P` seam), proven
from the inner per-round bound `hBound₂` alone. The run side is the proven seam-challenge body
factoring `phase2_body_heq_challenge_zero` followed by the `Subsingleton σ` bind split and the
amnesiac re-injection of `hBound₂` (identical to the positive-index branch of
`appendRbrKnowledgeSoundnessPhase2_subsingleton_challenge`); the event side is the containment
zero-reconcile `appendRbrKnowledgePhase2SeamReconcileZero_le` above. -/
theorem appendRbrKnowledgeSeamZero_proven [Subsingleton σ]
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
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .V_to_P)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .V_to_P)
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
    (stmtIn : Stmt₁) (witIn : Wit₁)
    (prover : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂)) (i₂ : pSpec₂.ChallengeIdx)
    (hz : ((i₂.1 : Fin n) : ℕ) = 0) :
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
            let challenge ← OracleComp.liftComp
              ((pSpec₁ ++ₚ pSpec₂).getChallenge (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂))
              (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
            return (transcript, challenge))).run' (← init)] ≤ rbrKnowledgeError₂ i₂ := by
  classical
  -- Abbreviations for the appended phase-2 per-round event `E` and the seam-factored experiment
  -- body (verbatim from the positive-index branch).
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
  -- STEP 1: transport the appended game to the seam-factored game via the proven *zero* body
  -- factoring `phase2_body_heq_challenge_zero`.
  have hbody := phase2_body_heq_challenge_zero prover stmtIn witIn i₂ hn hz hDir hDir₂
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
  simp only [simulateQ_run'_bind_of_subsingleton]
  -- Outer bind over `init`: bound uniformly over each sampled `s`.
  refine probEvent_bind_le_of_forall_le (fun s _hs => ?_)
  -- Inner bind over the (simulated) `fst.run` realization `ctx = (tr₁, seamState, ())`.
  refine probEvent_bind_le_of_forall_le (fun ctx hctx => ?_)
  -- The realized seam statement `s₂ := verify stmtIn tr₁` and the amnesiac re-injection prover
  -- that resumes `Prover.snd prover` from the realized seam state `ctx.2.1`.
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
  -- Under `Subsingleton σ`, the inner `init`-averaged game equals its value at our fixed `s`; with
  -- `Pr[⊥|init]=0`, `hb` collapses to the fixed-`s` snd game.
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
  -- FINAL: the containment zero-reconcile chains the appended 3-block game into the snd game.
  exact le_trans (appendRbrKnowledgePhase2SeamReconcileZero_le V₁ V₂ kSF₁ kSF₂ verify hVerify
    hInit stmtIn prover i₂ hz s ctx) hb

end Verifier

#print axioms Verifier.appendRbrKnowledgePhase2SeamReconcileZero_le
#print axioms Verifier.appendRbrKnowledgeSeamZero_proven
