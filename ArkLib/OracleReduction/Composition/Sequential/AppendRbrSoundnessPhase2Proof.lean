/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.AppendRbrKnowledgeSoundness
import ArkLib.OracleReduction.Composition.Sequential.AppendRightPartialProjections

/-!
# Unconditional round-by-round soundness for message-seam append

This file proves `append_rbrSoundness_keystone_subsingleton_unconditional` and discharges
`appendRbrSoundnessResidual_msg_subsingleton`. Both retain their component soundness premises,
deterministic first verifier, message-first seam, and `Subsingleton` simulation state.

The composite is canonical `StateFunction.append` applied to `S₁` and `S₂.doom`. Its second-phase
state is

  `S₁ (last m) stmt tr₁ ∨ verify stmt tr₁ ∈ lang₂ ∨ S₂ k (verify stmt tr₁) tr₂`.

The completed first-phase state is part of canonical append. The middle disjunct is the additional
escape clause introduced by `doom`. Either fixed disjunct makes the second-phase false-to-true
flip impossible. When both are false, the flip reduces to the second component's event at an
out-of-language seam statement, where its original soundness premise applies.

The proof factors the appended experiment at the seam, transports the right challenge oracle,
and uses the amnesiac second-phase prover. Native `ProbComp` is lossless, so its constant bind
law removes the initial-state average after `Subsingleton` identifies the states. Exact historical
source and the corrected projection interfaces are recorded in
`scripts/integration/append-phase2-carry-migration.json`.
-/

open OracleComp OracleSpec ProtocolSpec SubSpec
open scoped ENNReal NNReal

private local instance (A : Type) : MeasurableSpace A := ⊤
private local instance (A B : Type) : MeasurableSpace (A × B) := ⊤
private local instance (A : Type) : @DiscreteMeasurableSpace A ⊤ := ⟨fun _ => True.intro⟩

universe u v

namespace Verifier

variable {ι : Type} {oSpec : OracleSpec ι} {Stmt₁ Stmt₂ Stmt₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {lang₁ : Set Stmt₁} {lang₂ : Set Stmt₂} {lang₃ : Set Stmt₃}

omit [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)] in
/-- **Dependent congruence for a (plain) state function's `toFun`, statement-aware.** The plain
analogue of `kToFun_congr_stmt`: equal round indices, equal statements, and heterogeneously-equal
transcripts give equal `toFun` propositions. Generic over the protocol, so it serves both the
`pSpec₁` (phase-1 reindex) and `pSpec₂` (phase-2 collapse) transports. -/
theorem sToFun_congr_stmt {N : ℕ} {p : ProtocolSpec N} {Stmt : Type}
    (f : (r : Fin (N + 1)) → Stmt → p.Transcript r → Prop)
    {r₁ r₂ : Fin (N + 1)} (hr : r₁ = r₂) {s₁ s₂ : Stmt} (hs : s₁ = s₂)
    {t₁ : p.Transcript r₁} {t₂ : p.Transcript r₂} (ht : HEq t₁ t₂) :
    f r₁ s₁ t₁ = f r₂ s₂ t₂ := by
  subst hr; subst hs; rw [eq_of_heq ht]

omit [∀ i, SampleableType (pSpec₁.Challenge i)] in
/-- **Doomed-ness crosses the language** (public restatement of the brick used inside
`StateFunction.append`). For a *deterministic* first verifier `V₁ = pure ∘ verify` with a reachable
initial state, if its state function `S₁` is false on a full transcript then the intermediate
statement `verify stmt tr` lies *outside* `lang₂`. This converts the probabilistic `S₁.toFun_full`
into the pointwise membership fact that both the doomed-escape `toFun_next` crossing and the
phase-2 flip-event confinement consume. -/
theorem StateFunction.verify_notMem_lang_of_full_false
    {V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁}
    (S₁ : V₁.StateFunction init impl lang₁ lang₂)
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩)
    (hInit : ∃ s, s ∈ support init)
    (stmt : Stmt₁) (tr : pSpec₁.FullTranscript)
    (hNeg : ¬ S₁ (Fin.last m) stmt tr) :
    verify stmt tr ∉ lang₂ := by
  have hPr := S₁.toFun_full stmt tr hNeg
  rw [OptionT.prEvent_mk_eq_zero_iff] at hPr
  obtain ⟨s, hs⟩ := hInit
  refine hPr (verify stmt tr) ?_
  simp only [OptionT.run_mk, support_bind, Set.mem_iUnion]
  refine ⟨s, hs, ?_⟩
  have hrun : (V₁.run stmt tr) = (pure (verify stmt tr) : OptionT (OracleComp oSpec) Stmt₂) := by
    subst hVerify; rfl
  rw [hrun]
  change some (verify stmt tr) ∈ support
    (StateT.run' (simulateQ impl (pure (some (verify stmt tr)) :
      OracleComp oSpec (Option Stmt₂))) s)
  rw [simulateQ_pure]
  change some (verify stmt tr) ∈ support
    (Prod.fst <$> (pure (some (verify stmt tr)) : StateT σ ProbComp _).run s)
  rw [StateT.run_pure]
  simp [map_pure]


/-- Reindex the complete first transcript without identifying dependent carrier families. -/
private theorem fullPrefix_eq_of_heq {k : Fin (m + n + 1)}
    (hk : m ≤ k.val) (tr : (pSpec₁ ++ₚ pSpec₂).Transcript k)
    (tr₁ : pSpec₁.FullTranscript) (ht : HEq tr.fst tr₁) :
    (fun i : Fin m => tr.fst ⟨i.val, by simpa [min_eq_right hk] using i.isLt⟩) = tr₁ := by
  have hsize : min k.val m = m := min_eq_right hk
  have hh : HEq
      (fun i : Fin m => tr.fst ⟨i.val, by simpa [hsize] using i.isLt⟩) tr.fst := by
    refine Function.hfunext (congrArg Fin hsize.symm) ?_
    intro a b hab
    have hv : a.val = b.val := (Fin.heq_ext_iff hsize.symm).1 hab
    have hi : (⟨a.val, by simpa [hsize] using a.isLt⟩ : Fin (min k.val m)) = b := Fin.ext hv
    cases hi
    rfl
  exact eq_of_heq (hh.trans ht)

/-- **The doomed variant of a state function.** Same verifier, same languages; the state is
additionally *true* whenever the input statement already lies in the input language. All three
state-function laws are inherited from `S` with no transcript-dependent content: the escape
disjunct `stmt ∈ langIn` ignores the transcript entirely, `toFun_empty`'s backward direction is
`S.toFun_empty.mpr` on the second disjunct, and `toFun_full` only ever consumes the negation of the
second disjunct.

Dooming the *second* component before feeding it to the proven `StateFunction.append` yields the
standard round-by-round composition carrier: on phase-2 rounds the composite reads
`verify stmt₁ tr.fst ∈ lang₂ ∨ S₂ … (verify stmt₁ tr.fst) tr.snd`, so a phase-2 flip event records
`verify stmt₁ tr.fst ∉ lang₂` — confining the per-round bound to seam statements where `h₂` has
content — while avoiding entirely the dependent-cast surgery of re-deriving the appended
state-function laws. -/
def StateFunction.doom {N : ℕ} {p : ProtocolSpec N} {StmtIn StmtOut : Type}
    {langIn : Set StmtIn} {langOut : Set StmtOut} {V : Verifier oSpec StmtIn StmtOut p}
    (S : V.StateFunction init impl langIn langOut) :
    V.StateFunction init impl langIn langOut where
  toFun := fun k stmt tr => stmt ∈ langIn ∨ S.toFun k stmt tr
  toFun_empty := fun stmt h => h.elim (fun h => h) (S.toFun_empty stmt)
  toFun_next := fun k hdir stmt tr hneg msg => by
    rintro (hmem | hS)
    · exact hneg (Or.inl hmem)
    · exact S.toFun_next k hdir stmt tr (fun hcs => hneg (Or.inr hcs)) msg hS
  toFun_full := fun stmt tr hneg =>
    S.toFun_full stmt tr (fun hS => hneg (Or.inr hS))

/-- The doomed state function evaluates as the escape disjunction (definitional unfolding,
exposed as a `simp`-friendly equation). -/
theorem StateFunction.doom_toFun {N : ℕ} {p : ProtocolSpec N} {StmtIn StmtOut : Type}
    {langIn : Set StmtIn} {langOut : Set StmtOut} {V : Verifier oSpec StmtIn StmtOut p}
    (S : V.StateFunction init impl langIn langOut)
    (k : Fin (N + 1)) (stmt : StmtIn) (tr : p.Transcript k) :
    (S.doom).toFun k stmt tr = (stmt ∈ langIn ∨ S.toFun k stmt tr) := rfl

/-- **The doomed-escape composite state function**: the proven `StateFunction.append` applied to
`S₁` and the doomed `S₂.doom`. Phase one reads `S₁` on the truncation. Phase two reads the
completed `S₁` state, the seam-language escape clause, or the current `S₂` state. The historical
`hInit` parameter remains in this compatibility interface; canonical append needs no such premise. -/
noncomputable def StateFunction.appendDoomed
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (S₁ : V₁.StateFunction init impl lang₁ lang₂) (S₂ : V₂.StateFunction init impl lang₂ lang₃)
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩)
    (hInit : ∃ s, s ∈ support init) :
    (V₁.append V₂).StateFunction init impl lang₁ lang₃ :=
  StateFunction.append init impl V₁ V₂ S₁ (S₂.doom) verify hVerify

/-- **Phase-1 projection of the doomed composite** — inherited verbatim from
`StateFunction.append_toFun_le`. -/
theorem StateFunction.appendDoomed_toFun_le
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (S₁ : V₁.StateFunction init impl lang₁ lang₂) (S₂ : V₂.StateFunction init impl lang₂ lang₃)
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩) (hInit : ∃ s, s ∈ support init)
    {roundIdx : Fin (m + n + 1)} (h : roundIdx.val ≤ m) (stmt₁ : Stmt₁)
    (transcript : (pSpec₁ ++ₚ pSpec₂).Transcript roundIdx) :
    (StateFunction.appendDoomed V₁ V₂ S₁ S₂ verify hVerify hInit).toFun roundIdx stmt₁ transcript
      = S₁.toFun ⟨roundIdx, by omega⟩ stmt₁ (by simpa [h] using transcript.fst) :=
  StateFunction.append_toFun_le V₁ V₂ S₁ (S₂.doom) verify hVerify hInit h stmt₁ transcript

set_option backward.isDefEq.respectTransparency false in
/-- Phase-two projection including the completed first-phase carry, seam-language escape,
and current second-phase state. -/
theorem StateFunction.appendDoomed_toFun_gt
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (S₁ : V₁.StateFunction init impl lang₁ lang₂) (S₂ : V₂.StateFunction init impl lang₂ lang₃)
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩) (hInit : ∃ s, s ∈ support init)
    {roundIdx : Fin (m + n + 1)} (h : ¬ roundIdx.val ≤ m) (stmt₁ : Stmt₁)
    (transcript : (pSpec₁ ++ₚ pSpec₂).Transcript roundIdx) :
    (StateFunction.appendDoomed V₁ V₂ S₁ S₂ verify hVerify hInit).toFun roundIdx stmt₁ transcript
      = (let tr₁ : pSpec₁.FullTranscript := fun i =>
           transcript.fst ⟨i.val, by simpa [min_eq_right_of_lt (show m < roundIdx.val by omega)] using i.isLt⟩
         S₁.toFun (Fin.last m) stmt₁ tr₁ ∨
           (verify stmt₁ tr₁ ∈ lang₂ ∨
             S₂.toFun ⟨roundIdx - m, by omega⟩ (verify stmt₁ tr₁)
               (by simpa [h] using transcript.snd))) := by
  have hproj := StateFunction.append_toFun_gt_eq_or V₁ V₂ S₁ (S₂.doom) verify hVerify h stmt₁ transcript
  simp only [StateFunction.doom_toFun] at hproj
  convert hproj using 1 <;> rfl

set_option backward.isDefEq.respectTransparency false in
/-- **Soundness-side phase-2 inner seam reconciliation, at the doomed composite.** The plain
(witness-free) analogue of the proven `appendRbrKnowledgePhase2SeamReconcile_proof`: at a fixed
Subsingleton state `s` and a realized `Prover.fst`-output `ctx`, the appended phase-2 inner game —
running `Prover.snd prover` from the realized seam state under the **combined** challenge oracle,
prefixing the phase-2 transcript with the realized phase-1 transcript `ctx.1` via
`Transcript.appendRight`, and reading the per-round flip event through the doomed composite
`StateFunction.append … S₁ (S₂.doom)` — has the same event-probability as the inner `pSpec₂` snd
game (over `pSpec₂`'s **own** challenge oracle), retaining the completed first-phase carry and
the seam-language escape clause in its flip predicate.

Ingredients (all previously proven): body recombination via `simulateQ_run'_bind_of_subsingleton`
(read right-to-left) + `Prover.append_getChallenge_natAdd`; the right challenge-oracle-seam
transfer `OracleReduction.evalDist_run'_challengeSeam_right`; and the gt-event collapse
`StateFunction.append_toFun_gt_eq_or` + `StateFunction.doom_toFun` under the `appendRight ctx.1` prefix
(`appendRight_fst/snd`, `appendRight_concat_fst/snd`). -/
theorem appendDoomed_phase2_seam_reconcile [Subsingleton σ]
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (S₁ : V₁.StateFunction init impl lang₁ lang₂) (S₂ : V₂.StateFunction init impl lang₂ lang₃)
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩) (hInit : ∃ s, s ∈ support init)
    (hDir₂ : ∀ (hn : 0 < n), pSpec₂.dir (⟨0, hn⟩ : Fin n) = .P_to_V)
    {WitIn WitOut : Type}
    (stmtIn : Stmt₁)
    (prover : Prover oSpec Stmt₁ WitIn Stmt₃ WitOut (pSpec₁ ++ₚ pSpec₂))
    (i₂ : pSpec₂.ChallengeIdx) (s : σ)
    (ctx : pSpec₁.FullTranscript ×
      prover.PrvState (Fin.castLE (show m + 1 ≤ m + n + 1 by omega) (Fin.last m)) × Unit) :
    probEvent (fun x =>
        ¬ (StateFunction.append init impl V₁ V₂ S₁ (S₂.doom) verify hVerify).toFun
            (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.castSucc stmtIn x.1 ∧
          (StateFunction.append init impl V₁ V₂ S₁ (S₂.doom) verify hVerify).toFun
            (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.succ stmtIn (x.1.concat x.2)) (((do
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
                × (pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂))))
    = probEvent (fun x =>
          ¬ (S₁.toFun (Fin.last m) stmtIn ctx.1 ∨ verify stmtIn ctx.1 ∈ lang₂ ∨
              S₂.toFun i₂.1.castSucc (verify stmtIn ctx.1) x.1) ∧
            (S₁.toFun (Fin.last m) stmtIn ctx.1 ∨ verify stmtIn ctx.1 ∈ lang₂ ∨
              S₂.toFun i₂.1.succ (verify stmtIn ctx.1) (x.1.concat x.2))) ((simulateQ (impl.addLift challengeQueryImpl
              : QueryImpl (oSpec + [pSpec₂.Challenge]ₒ) (StateT σ ProbComp))
            (do
              let ⟨transcript, _⟩ ← ((Prover.snd prover).runToRound i₂.1.castSucc ctx.2.1 ()
                : OracleComp (oSpec + [pSpec₂.Challenge]ₒ)
                    (pSpec₂.Transcript i₂.1.castSucc × (Prover.snd prover).PrvState i₂.1.castSucc))
              let challenge ← liftComp (pSpec₂.getChallenge i₂)
                (oSpec + [pSpec₂.Challenge]ₒ)
              return (transcript, challenge))).run' s) := by
  classical
  have hn : 0 < n := Fin.pos_iff_nonempty.mpr ⟨i₂.1⟩
  have hpos : 0 < ((i₂.1 : Fin n) : ℕ) :=
    challengeIdx_val_pos_of_seam_msg (i₂ := i₂) hn (hDir₂ hn)
  -- The combined-spec phase-2 per-round event (verbatim from the goal LHS).
  set E : (pSpec₁ ++ₚ pSpec₂).Transcript (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.castSucc
      × (pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂) → Prop :=
    fun x =>
      ¬ (StateFunction.append init impl V₁ V₂ S₁ (S₂.doom) verify hVerify).toFun
          (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.castSucc stmtIn x.1 ∧
        (StateFunction.append init impl V₁ V₂ S₁ (S₂.doom) verify hVerify).toFun
          (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.succ stmtIn (x.1.concat x.2)
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
  show probEvent (E) (_) = _
  -- Reduce the goal's 3-block computation to `(simulateQ impl BODY).run' s` via the subsingleton
  -- split.
  suffices hkey : probEvent (E) ((simulateQ (impl.addLift challengeQueryImpl
        : QueryImpl (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (StateT σ ProbComp)) BODY).run' s)
      = probEvent (fun x =>
          ¬ (S₁.toFun (Fin.last m) stmtIn ctx.1 ∨ verify stmtIn ctx.1 ∈ lang₂ ∨
              S₂.toFun i₂.1.castSucc (verify stmtIn ctx.1) x.1) ∧
            (S₁.toFun (Fin.last m) stmtIn ctx.1 ∨ verify stmtIn ctx.1 ∈ lang₂ ∨
              S₂.toFun i₂.1.succ (verify stmtIn ctx.1) (x.1.concat x.2))) ((simulateQ (impl.addLift challengeQueryImpl
              : QueryImpl (oSpec + [pSpec₂.Challenge]ₒ) (StateT σ ProbComp))
            (do
              let ⟨transcript, _⟩ ← ((Prover.snd prover).runToRound i₂.1.castSucc ctx.2.1 ()
                : OracleComp (oSpec + [pSpec₂.Challenge]ₒ)
                    (pSpec₂.Transcript i₂.1.castSucc × (Prover.snd prover).PrvState i₂.1.castSucc))
              let challenge ← liftComp (pSpec₂.getChallenge i₂)
                (oSpec + [pSpec₂.Challenge]ₒ)
              return (transcript, challenge))).run' s) by
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
  have hEvent := probEvent_congr_heq rfl _
    ((simulateQ (impl.addLift (challengeQueryImpl (pSpec := pSpec₂))
      : QueryImpl _ (StateT σ ProbComp)) INNER).run' s) E E (heq_of_eq hseam) (fun x => Iff.rfl)
  change probEvent _ _ = probEvent _ _ at hEvent
  rw [hEvent]
  -- STEP C: `INNER = wrap <$> RHSbody`; push the map out via native `prEvent_map`.
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
  simp only [probEvent, prEvent_map]
  -- STEP D: the event correspondence `E ∘ wrap = E_inner` (pointwise).
  refine congrArg (fun p => probEvent (p) ((simulateQ (impl.addLift (challengeQueryImpl (pSpec := pSpec₂))
      : QueryImpl _ (StateT σ ProbComp)) RHSbody).run' s)) ?_
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
  -- Transcript projections of `trW = appendRight ctx.1 x.1`.
  have htrW_fst : HEq (Transcript.fst trW) ctx.1 := by
    rw [htrW]; exact Transcript.appendRight_fst ctx.1 x.1
  have htrW_snd : HEq (Transcript.snd trW) x.1 := by
    rw [htrW]; exact Transcript.appendRight_snd ctx.1 x.1
  -- `chW` is the cast of the pSpec₂ message `x.2`; rewrite to the `append_Type_natAdd` cast form
  -- used by the `appendRight_concat` bricks.
  have hchW_eq : chW = cast (append_Type_natAdd i₂.1).symm x.2 := by
    rw [hchW]
  -- The concat'd transcript projections.
  have hconcat_fst : HEq (Transcript.fst (Transcript.concat chW trW)) ctx.1 := by
    rw [htrW, hchW_eq]
    exact Transcript.appendRight_concat_fst ctx.1 x.2 x.1
  have hconcat_snd : HEq (Transcript.snd (Transcript.concat chW trW))
      (Transcript.concat x.2 x.1) := by
    rw [htrW, hchW_eq]
    exact Transcript.appendRight_concat_snd ctx.1 x.2 x.1
  -- The phase-2 reindex of the toFun rounds.
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
  have hfullBefore := fullPrefix_eq_of_heq (by omega) trW ctx.1 htrW_fst
  have hfullAfter := fullPrefix_eq_of_heq (by omega) (trW.concat chW) ctx.1 hconcat_fst
  refine iff_of_eq (congrArg₂ (fun A B => ¬ A ∧ B) ?_ ?_)
  · rw [StateFunction.append_toFun_gt_eq_or V₁ V₂ S₁ (S₂.doom) verify hVerify hcs_gt]
    dsimp only [StateFunction.doom]
    exact congrArg₂ Or (congrArg (S₁.toFun (Fin.last m) stmtIn) hfullBefore)
      (congrArg₂ Or (congrArg (· ∈ lang₂) (congrArg (verify stmtIn) hfullBefore))
        (sToFun_congr_stmt S₂.toFun hidxcs (congrArg (verify stmtIn) hfullBefore)
          (HEq.trans HEq.rfl htrW_snd)))
  · rw [StateFunction.append_toFun_gt_eq_or V₁ V₂ S₁ (S₂.doom) verify hVerify hsu_gt]
    dsimp only [StateFunction.doom]
    exact congrArg₂ Or (congrArg (S₁.toFun (Fin.last m) stmtIn) hfullAfter)
      (congrArg₂ Or (congrArg (· ∈ lang₂) (congrArg (verify stmtIn) hfullAfter))
        (sToFun_congr_stmt S₂.toFun hidxsu (congrArg (verify stmtIn) hfullAfter)
          (HEq.trans HEq.rfl hconcat_snd)))

set_option backward.isDefEq.respectTransparency false in
/-- **Discharge of the phase-2 per-round soundness residual at the doomed composite, under
`Subsingleton σ` (stateless / transparent-oracle regime) and a prover-message seam.**

This proves `appendRbrSoundnessPhase2Residual V₁ V₂ S₁ (S₂.doom) …` — the phase-2 residual of
`append_rbrSoundness_keystone` *instantiated at the doomed second state function* `S₂.doom` — from
the inner per-round bound `hS₂` for `S₂` alone. The doomed escape disjunct confines all flip
mass to out-of-language seam inputs. After seam-factoring
(`phase2_body_heq`), Subsingleton-splitting (`simulateQ_run'_bind_of_subsingleton`), conditioning
on the realized phase-1 output `ctx`, and reconciling the inner game across the right
challenge-oracle seam (`appendDoomed_phase2_seam_reconcile`), the per-realization bound cases on
the fixed completed carry or seam-language disjunction:

* If either the completed `S₁` state or seam-language escape holds, the doomed flip is
  pointwise false and its conditional probability is zero.
* Otherwise the event is exactly `S₂`'s flip at an out-of-language seam statement. Apply
  `hS₂` to `Prover.sndAmnesiac` and remove the constant initial-state bind using native
  `OracleComp.prEvent_bind_const`. The historical `hInitNF` parameter remains available. -/
theorem appendRbrSoundnessPhase2_doomed_subsingleton [Subsingleton σ]
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (S₁ : V₁.StateFunction init impl lang₁ lang₂) (S₂ : V₂.StateFunction init impl lang₂ lang₃)
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩)
    (hInit : ∃ s, s ∈ support init) (hInitNF : probFailure init = 0)
    (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .P_to_V)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .P_to_V)
    {rbrSoundnessError₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (hS₂ : ∀ stmtIn ∉ lang₂, ∀ WitIn WitOut : Type, ∀ witIn : WitIn,
      ∀ prover : Prover oSpec Stmt₂ WitIn Stmt₃ WitOut pSpec₂, ∀ i : pSpec₂.ChallengeIdx,
        probEvent (fun ⟨transcript, challenge⟩ =>
          ¬ S₂ i.1.castSucc stmtIn transcript ∧ S₂ i.1.succ stmtIn (transcript.concat challenge)) (do
          (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
            (do
              let ⟨transcript, _⟩ ← prover.runToRound i.1.castSucc stmtIn witIn
              let challenge ← liftComp (pSpec₂.getChallenge i) _
              return (transcript, challenge))).run' (← init)) ≤ rbrSoundnessError₂ i) :
    appendRbrSoundnessPhase2Residual (init := init) (impl := impl) V₁ V₂ S₁ (S₂.doom)
      verify hVerify hInit (rbrSoundnessError₂ := rbrSoundnessError₂) := by
  intro stmtIn hStmtIn WitIn WitOut witIn prover i₂
  classical
  have hpos : 0 < ((i₂.1 : Fin n) : ℕ) := challengeIdx_val_pos_of_seam_msg (i₂ := i₂) hn hDir₂
  -- The appended phase-2 per-round event.
  set E : (pSpec₁ ++ₚ pSpec₂).Transcript (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.castSucc
      × (pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂) → Prop :=
    fun x =>
      ¬ (StateFunction.append init impl V₁ V₂ S₁ (S₂.doom) verify hVerify).toFun
          (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.castSucc stmtIn x.1 ∧
        (StateFunction.append init impl V₁ V₂ S₁ (S₂.doom) verify hVerify).toFun
          (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.succ stmtIn (x.1.concat x.2) with hE
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
    have heq_evalDist : ∀ {A B : Type} (hAB : A = B) (a : ProbComp A) (b : ProbComp B),
        HEq a b → HEq (𝒟[a]) (𝒟[b]) := by
      intro A B hAB a b hab; subst hAB; rw [eq_of_heq hab]
    have heq_simrun : ∀ {A B : Type} (s : σ) (hAB : A = B)
        (a : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) A)
        (b : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) B), HEq a b →
        HEq ((simulateQ (impl.addLift challengeQueryImpl
              : QueryImpl (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (StateT σ ProbComp)) a).run' s)
            ((simulateQ (impl.addLift challengeQueryImpl
              : QueryImpl (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (StateT σ ProbComp)) b).run' s) := by
      intro A B s hAB a b hab; subst hAB; rw [eq_of_heq hab]
    refine heq_evalDist hResTy _ _ ?_
    refine Prover.bind_heq_congr rfl hResTy HEq.rfl (fun s s' hs => ?_)
    cases eq_of_heq hs
    exact heq_simrun s hResTy _ _ hbody
  have hGame := probEvent_congr_heq hResTy _ _ E (fun x => E (hResTy ▸ x)) hd (fun x => Iff.rfl)
  change probEvent _ _ = probEvent _ _ at hGame
  rw [hGame]
  -- STEP 2: bound the seam-factored game via the Subsingleton bind split.
  simp only [simulateQ_run'_bind_of_subsingleton]
  refine prEvent_bind_le_of_forall_le_of_support _ _ _ (fun s _hs => ?_)
  refine prEvent_bind_le_of_forall_le_of_support _ _ _ (fun ctx hctx => ?_)
  -- Reconcile the appended inner game with the inner `pSpec₂` snd game at the doomed event.
  refine le_trans (le_of_eq (appendDoomed_phase2_seam_reconcile V₁ V₂ S₁ S₂ verify hVerify hInit
    (fun _ => hDir₂) stmtIn prover i₂ s ctx)) ?_
  -- Either completed carry or seam-language membership makes the flip impossible.
  by_cases hmem : S₁.toFun (Fin.last m) stmtIn ctx.1 ∨ verify stmtIn ctx.1 ∈ lang₂
  · -- A fixed disjunct already holds before the challenge, so the flip event is false.
    refine le_trans (le_of_eq ?_) (by exact bot_le)
    apply (OracleComp.prEvent_eq_zero_iff _ _).2
    rintro x _ ⟨hneg, _⟩
    exact hneg (hmem.elim Or.inl (fun h => Or.inr (Or.inl h)))
  · -- Both fixed disjuncts are false, so the doomed event is `S₂`'s flip event at
    -- the seam statement; apply the inner per-round bound `hS₂` to the amnesiac re-injection
    -- prover, collapsing the `init`-average to the fixed Subsingleton state `s`.
    have hb := hS₂ (verify stmtIn ctx.1) (fun h => hmem (Or.inr h)) Unit WitOut ()
      (Prover.sndAmnesiac prover ctx.2.1) i₂
    simp only [Prover.sndAmnesiac_runToRound] at hb
    conv_lhs at hb =>
      arg 2
      arg 2
      intro s'
      rw [Subsingleton.elim s' s]
    simp only [probEvent, map_bind] at hb
    rw [OracleComp.prEvent_bind_const] at hb
    refine le_trans (le_of_eq ?_) hb
    apply congrArg₂ (fun P mx => probEvent P mx) ?_ rfl
    funext x
    apply propext
    constructor
    · rintro ⟨hneg, hpos'⟩
      exact ⟨fun h2 => hneg (Or.inr (Or.inr h2)),
        (hpos'.resolve_left (fun h => hmem (Or.inl h))).resolve_left
          (fun h => hmem (Or.inr h))⟩
    · rintro ⟨hneg, hpos'⟩
      exact ⟨fun h2 => h2.elim (fun h => hmem (Or.inl h))
        (fun h => h.elim (fun h => hmem (Or.inr h)) hneg), Or.inr (Or.inr hpos')⟩

/-- **Round-by-round soundness append keystone, `Subsingleton σ` message-seam case —
UNCONDITIONAL.** From the two components' `rbrSoundness` (`h₁`/`h₂`) alone — plus the standard
structural side conditions of the deterministic-`V₁` message-seam, `Subsingleton σ` regime — the
appended verifier is round-by-round sound with the per-round error routed through
`ChallengeIdx.sumEquiv`.  The composite state function is the **doomed-escape** composite
`StateFunction.append … S₁ (S₂.doom)` (`rbrSoundness` is existential in the state function, so
dooming `S₂` is free); phase 1 is discharged by the proven `append_rbrSoundness_keystone`
internals, and phase 2 by `appendRbrSoundnessPhase2_doomed_subsingleton`. -/
theorem append_rbrSoundness_keystone_subsingleton_unconditional [Subsingleton σ]
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {rbrSoundnessError₁ : pSpec₁.ChallengeIdx → ℝ≥0}
    {rbrSoundnessError₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩)
    (hInit : ∃ s, s ∈ support init) (hInitNF : probFailure init = 0)
    (hNE : Nonempty Stmt₂)
    (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .P_to_V)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .P_to_V)
    (h₁ : V₁.rbrSoundness init impl lang₁ lang₂ rbrSoundnessError₁)
    (h₂ : V₂.rbrSoundness init impl lang₂ lang₃ rbrSoundnessError₂) :
      (V₁.append V₂).rbrSoundness init impl lang₁ lang₃
        (Sum.elim rbrSoundnessError₁ rbrSoundnessError₂ ∘ ChallengeIdx.sumEquiv.symm) := by
  obtain ⟨S₁, hS₁⟩ := h₁
  obtain ⟨S₂, hS₂⟩ := h₂
  exact append_rbrSoundness_keystone V₁ V₂ S₁ hS₁ (S₂.doom) verify hVerify hInit hNE
    (appendRbrSoundnessPhase2_doomed_subsingleton V₁ V₂ S₁ S₂ verify hVerify hInit hInitNF
      hn hDir hDir₂ hS₂)

/-- **Discharge of the named residual `Verifier.appendRbrSoundnessResidual`** (`Append.lean`) in
the deterministic-`V₁` / `Subsingleton σ` / prover-message-seam regime — the exact regime of the
in-tree stateless consumers (transparent-BCS, `oSpec = []ₒ` RingSwitching).  The residual's
conclusion is precisely the keystone's, so this is definitional from
`append_rbrSoundness_keystone_subsingleton_unconditional`. -/
theorem appendRbrSoundnessResidual_msg_subsingleton [Subsingleton σ]
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {rbrSoundnessError₁ : pSpec₁.ChallengeIdx → ℝ≥0}
    {rbrSoundnessError₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩)
    (hInit : ∃ s, s ∈ support init) (hInitNF : probFailure init = 0)
    (hNE : Nonempty Stmt₂)
    (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .P_to_V)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .P_to_V)
    (h₁ : V₁.rbrSoundness init impl lang₁ lang₂ rbrSoundnessError₁)
    (h₂ : V₂.rbrSoundness init impl lang₂ lang₃ rbrSoundnessError₂) :
    appendRbrSoundnessResidual (init := init) (impl := impl) V₁ V₂ h₁ h₂ :=
  append_rbrSoundness_keystone_subsingleton_unconditional V₁ V₂ verify hVerify hInit hInitNF
    hNE hn hDir hDir₂ h₁ h₂

end Verifier

-- Axiom audit: each should report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms Verifier.StateFunction.verify_notMem_lang_of_full_false
#print axioms Verifier.StateFunction.doom
#print axioms Verifier.StateFunction.appendDoomed
#print axioms Verifier.appendDoomed_phase2_seam_reconcile
#print axioms Verifier.appendRbrSoundnessPhase2_doomed_subsingleton
#print axioms Verifier.append_rbrSoundness_keystone_subsingleton_unconditional
#print axioms Verifier.appendRbrSoundnessResidual_msg_subsingleton
