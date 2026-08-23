/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.AppendChallengeSeam
import ArkLib.OracleReduction.Composition.Sequential.AppendRunEvalDistChallenge
import ArkLib.OracleReduction.Composition.Sequential.SeamDecompositionRun

/-!
# Challenge-seam append game-factoring (`hGameFactor` discharge for a `V_to_P` seam)

`AppendChallengeSeam.lean` discharges the completeness `hGameFactor` residual of
`append_completeness_msg_proof` for the **message seam** via `append_game_factor_msg`, whose only
seam-specific step is `append_run_natural_msg` (the *syntactic* run factoring through
`Prover.append_run_msg`). At a **challenge seam** (`pSpec₂`'s round 0 is `V_to_P`) the syntactic run
factoring is *false* — the appended prover samples the seam `getChallenge` before consuming
`P₁.output` — but the appended honest *game* still factors as a distribution: the seam challenge is a
uniform sample that commutes, under the honest state-preserving implementation, past the prover's
`oSpec`-computation (the simulated analogue of the bare `evalDist_bind_comm` used in
`Prover.append_run_evalDist_challenge`, here `RunUnroll.evalDist_simulateQ_swap_prefix`).

`append_game_factor_challenge` discharges `hGameFactor` for the challenge seam; combined with the
(seam-direction-agnostic) bridges in `AppendSeamBridges.lean` it gives challenge-seam append
completeness, the missing keystone for the Spartan composed perfect completeness (#114).
-/

open OracleComp OracleSpec ProtocolSpec OptionTStateT
open scoped ENNReal NNReal

namespace Reduction

variable {ι : Type} {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited]
  {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}

set_option maxHeartbeats 1000000 in
/-- **Simulated analogue of `Prover.append_continueFromTo_seam_start_challenge_evalDist`.** The seam
continuation, simulated under the state-preserving honest implementation, equals the challenge-first
`P₁.output ≫ P₂.processRound` form: the same syntactic challenge-first unroll as the bare lemma, but
the lone distributional commute (`getChallenge` past `liftComp (P₁.output)`) is done at the
`simulateQ` level via `evalDist_simulateQ_swap_prefix` (valid since the honest impl is
state-preserving). -/
private theorem simulateQ_continueFromTo_seam_challenge_evalDist
    (P₁ : Prover oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (P₂ : Prover oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (stmt : Stmt₁) (wit : Wit₁) (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .V_to_P)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .V_to_P)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    [instSC : ∀ i, SampleableType ((pSpec₁ ++ₚ pSpec₂).Challenge i)]
    (T₁ : FullTranscript pSpec₁)
    (rSeam : (pSpec₁ ++ₚ pSpec₂).Transcript (⟨m, by omega⟩ : Fin (m + n)).castSucc
      × (P₁.append P₂).PrvState (⟨m, by omega⟩ : Fin (m + n)).castSucc)
    (hT : rSeam.1 =
      Transcript.appendRight T₁
        (default : pSpec₂.Transcript (⟨0, by omega⟩ : Fin (n + 1))))
    (s : σ) :
    evalDist (StateT.run' (simulateQ (impl.addLift challengeQueryImpl :
        QueryImpl (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (StateT σ ProbComp))
        (Prover.continueFromTo (P₁.append P₂) stmt wit
          (⟨m, by omega⟩ : Fin (m + n)).castSucc
          (⟨m, by omega⟩ : Fin (m + n)).succ rSeam)) s)
      = evalDist (StateT.run' (simulateQ (impl.addLift challengeQueryImpl :
        QueryImpl (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (StateT σ ProbComp))
        ((liftM (P₁.output (cast (Prover.append_PrvState_seam_castSucc hn) rSeam.2)) :
            OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (Stmt₂ × Wit₂)) >>= fun ctxIn₂ =>
        (liftM
          (P₂.processRound (⟨0, hn⟩ : Fin n)
            (pure
              ((default : pSpec₂.Transcript (⟨0, by omega⟩ : Fin (n + 1))),
                P₂.input ctxIn₂))) :
          OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
            (pSpec₂.Transcript (⟨0, hn⟩ : Fin n).succ ×
              P₂.PrvState (⟨0, hn⟩ : Fin n).succ)) >>= fun p =>
        (pure
          (Transcript.appendRight T₁ p.1,
            cast (Prover.append_PrvState_seam_succ (P₁ := P₁) (P₂ := P₂) hn).symm p.2) :
          OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
            ((pSpec₁ ++ₚ pSpec₂).Transcript (⟨m, by omega⟩ : Fin (m + n)).succ
              × (P₁.append P₂).PrvState (⟨m, by omega⟩ : Fin (m + n)).succ)))) s) := by
  rw [eq_of_heq (Prover.append_continueFromTo_seam_start_challenge_split
    (P₁ := P₁) (P₂ := P₂) (stmt := stmt) (wit := wit) hn hDir hDir₂ T₁ rSeam hT)]
  conv_rhs =>
    enter [1, 1, 2, 2, ctxIn₂]
    rw [show (liftM (P₂.processRound (⟨0, hn⟩ : Fin n)
              (pure ((default : pSpec₂.Transcript (⟨0, by omega⟩ : Fin (n + 1))),
                P₂.input ctxIn₂))) :
            OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _)
          = OracleComp.liftComp (P₂.processRound (⟨0, hn⟩ : Fin n)
              (pure ((default : pSpec₂.Transcript (⟨0, by omega⟩ : Fin (n + 1))),
                P₂.input ctxIn₂)))
            (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) from
          (OracleComp.liftComp_eq_liftM _).symm]
    rw [Prover.liftComp_processRound_zero_challenge_appendRight
      (P₁ := P₁) (P₂ := P₂) hn hDir₂ T₁ ctxIn₂]
  rw [Prover.liftM_via_leftChallenge_eq_liftComp
    (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
    (X := P₁.output (cast (Prover.append_PrvState_seam_castSucc hn) rSeam.2))]
  exact evalDist_simulateQ_swap_prefix _ (addLift_state_preserving impl himplSP)
    (pure ())
    (fun _ => (liftM (pSpec₂.getChallenge ⟨⟨0, hn⟩, hDir₂⟩) :
      OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (pSpec₂.Challenge ⟨⟨0, hn⟩, hDir₂⟩)))
    (fun _ => (OracleComp.liftComp (P₁.output (cast (Prover.append_PrvState_seam_castSucc hn) rSeam.2))
      (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) :
      OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (Stmt₂ × Wit₂)))
    (fun _ challenge ctxIn₂ =>
      OracleComp.liftComp
        (P₂.receiveChallenge ⟨⟨0, hn⟩, hDir₂⟩ (P₂.input ctxIn₂))
        (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) >>= fun f =>
      pure (Transcript.appendRight T₁
          (Transcript.concat challenge
            (default : pSpec₂.Transcript (⟨0, by omega⟩ : Fin (n + 1)))),
        cast (Prover.append_PrvState_seam_succ (P₁ := P₁) (P₂ := P₂) hn).symm (f challenge))) s

/-- **`evalDist`-level `run'` bind decomposition under a state-preserving implementation.** When
every query implementation preserves the `σ`-state, the simulated `run'`-distribution of a bind
decomposes as the SPMF bind of the per-stage `run'`-distributions, each from the *same* seed `s`
(state-fixing `simulateQ_run_bind_state_fixed`). This makes any per-stage `evalDist` replacement
(e.g. the seam-challenge swap) compositional: split, rewrite a stage, refold. -/
private theorem evalDist_simulateQ_run'_bind {ιq : Type} {specq : OracleSpec ιq} {τ : Type}
    (so : QueryImpl specq (StateT τ ProbComp))
    (hso : ∀ (t : specq.Domain) (s : τ) (x : specq.Range t × τ),
      x ∈ support ((so t).run s) → x.2 = s)
    {α β : Type} (X : OracleComp specq α) (G : α → OracleComp specq β) (s : τ) :
    evalDist (StateT.run' (simulateQ so (X >>= G)) s)
      = evalDist (StateT.run' (simulateQ so X) s) >>= fun a =>
          evalDist (StateT.run' (simulateQ so (G a)) s) := by
  simp only [StateT.run'_eq, evalDist_map]
  rw [simulateQ_run_bind_state_fixed so hso X G s]
  simp only [evalDist_bind, map_bind, bind_map_left]

set_option maxHeartbeats 1000000 in
/-- **Simulated analogue of `Prover.append_continueFromTo_right_challenge_evalDist`.** The appended
prover's right-block continuation (seam round `⟨m⟩` to the last round), simulated under the
state-preserving honest implementation, has the same per-seed `run'`-distribution as `P₁`'s output
threaded into `P₂`'s full run-to-round (transported via `appendRight`). The lone distributional step
is the seam-start swap `simulateQ_continueFromTo_seam_challenge_evalDist`; the split
(`continueFromTo_trans`) and the post-seam fold (`append_right_block_from_seam_boundary_heq`) are
syntactic, threaded through `evalDist_simulateQ_run'_bind`. -/
private theorem simulateQ_continueFromTo_right_challenge_evalDist
    (P₁ : Prover oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (P₂ : Prover oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (stmt : Stmt₁) (wit : Wit₁) (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .V_to_P)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .V_to_P)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    [instSC : ∀ i, SampleableType ((pSpec₁ ++ₚ pSpec₂).Challenge i)]
    (T₁ : FullTranscript pSpec₁)
    (rSeam : (pSpec₁ ++ₚ pSpec₂).Transcript (⟨m, by omega⟩ : Fin (m + n)).castSucc
      × (P₁.append P₂).PrvState (⟨m, by omega⟩ : Fin (m + n)).castSucc)
    (hT : rSeam.1 =
      Transcript.appendRight T₁
        (default : pSpec₂.Transcript (⟨0, by omega⟩ : Fin (n + 1))))
    (s : σ) :
    evalDist (StateT.run' (simulateQ (impl.addLift challengeQueryImpl :
        QueryImpl (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (StateT σ ProbComp))
        (Prover.continueFromTo (P₁.append P₂) stmt wit
          (⟨m, by omega⟩ : Fin (m + n)).castSucc (Fin.last (m + n)) rSeam)) s)
      = evalDist (StateT.run' (simulateQ (impl.addLift challengeQueryImpl :
        QueryImpl (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (StateT σ ProbComp))
        ((liftM (P₁.output (cast (Prover.append_PrvState_seam_castSucc hn) rSeam.2)) :
            OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (Stmt₂ × Wit₂)) >>= fun ctx =>
          ((fun p => (Transcript.appendRight T₁ p.1,
              cast (Prover.append_PrvState_last (P₁ := P₁) (P₂ := P₂) hn).symm p.2)) <$>
            liftComp (P₂.runToRound (Fin.last n) ctx.1 ctx.2)
              (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) :
            OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
              ((pSpec₁ ++ₚ pSpec₂).Transcript (Fin.last (m + n))
                × (P₁.append P₂).PrvState (Fin.last (m + n)))))) s) := by
  have hso := addLift_state_preserving (pSpec := pSpec₁ ++ₚ pSpec₂) impl himplSP
  rw [Prover.continueFromTo_trans (P₁.append P₂) stmt wit
    (⟨m, by omega⟩ : Fin (m + n)).castSucc (⟨m, by omega⟩ : Fin (m + n)).succ (Fin.last (m + n))
    (by rw [Fin.le_def, Fin.val_castSucc, Fin.val_succ]; omega)
    (by rw [Fin.le_def, Fin.val_succ, Fin.val_last]; omega) rSeam]
  rw [evalDist_simulateQ_run'_bind _ hso,
    simulateQ_continueFromTo_seam_challenge_evalDist P₁ P₂ stmt wit hn hDir hDir₂ himplSP
      T₁ rSeam hT s,
    ← evalDist_simulateQ_run'_bind _ hso]
  exact congrArg (fun X => evalDist (StateT.run'
      (simulateQ (impl.addLift challengeQueryImpl :
        QueryImpl (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (StateT σ ProbComp)) X) s))
    (eq_of_heq (Prover.append_right_block_from_seam_boundary_heq stmt wit hn T₁ rSeam))

set_option maxHeartbeats 1600000 in
/-- **Simulated analogue of `Prover.append_run_evalDist_challenge` (per-seed, under the honest
state-preserving implementation).** The appended prover's run, simulated under
`impl.addLift challengeQueryImpl` from any seed `s`, has the same `run'`-distribution as the
sequential `P₁.run ≫ P₂.run`. Mirrors the bare `appendRunRightDistResidual_holds_challenge`:
the seam-split backbone and the final fold are syntactic; the per-seam right-block replacement is
`simulateQ_continueFromTo_right_challenge_evalDist`, threaded through
`evalDist_simulateQ_run'_bind`. -/
private theorem simulateQ_append_run_challenge_evalDist
    (P₁ : Prover oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (P₂ : Prover oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (stmt : Stmt₁) (wit : Wit₁) (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .V_to_P)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .V_to_P)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    [instSC : ∀ i, SampleableType ((pSpec₁ ++ₚ pSpec₂).Challenge i)]
    (s : σ) :
    evalDist (StateT.run' (simulateQ (impl.addLift challengeQueryImpl :
        QueryImpl (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (StateT σ ProbComp))
        ((P₁.append P₂).run stmt wit)) s)
      = evalDist (StateT.run' (simulateQ (impl.addLift challengeQueryImpl :
        QueryImpl (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (StateT σ ProbComp))
        ((do
          let ⟨transcript₁, stmt₂, wit₂⟩ ← liftM (P₁.run stmt wit)
          let ⟨transcript₂, stmt₃, wit₃⟩ ← liftM (P₂.run stmt₂ wit₂)
          return ⟨transcript₁ ++ₜ transcript₂, stmt₃, wit₃⟩) :
            OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
              (FullTranscript (pSpec₁ ++ₚ pSpec₂) × Stmt₃ × Wit₃))) s) := by
  have hso := addLift_state_preserving (pSpec := pSpec₁ ++ₚ pSpec₂) impl himplSP
  -- Seam-split backbone (syntactic): `run = runToRound (last) ≫ output`, factored at the seam.
  rw [Prover.run_eq_runToRound_last,
    Prover.runToRound_eq_bind_continueFromTo (P₁.append P₂) stmt wit
      (⟨m, by omega⟩ : Fin (m + n + 1)) (Fin.last (m + n))
      (by simp only [Fin.le_def, Fin.val_last]; omega),
    bind_assoc,
    show (⟨m, by omega⟩ : Fin (m + n + 1))
      = (⟨m, by omega⟩ : Fin (m + n)).castSucc from by ext; simp]
  -- Per-seam right-block replacement at the simulated `evalDist` level (the lone distributional
  -- step, one seam-challenge swap per seam value).
  conv_lhs =>
    rw [evalDist_simulateQ_run'_bind _ hso]
    enter [2, rSeam]
    rw [evalDist_simulateQ_run'_bind _ hso,
      simulateQ_continueFromTo_right_challenge_evalDist P₁ P₂ stmt wit hn hDir hDir₂ himplSP
        (cast (Prover.append_Transcript_seam_castSucc hn) rSeam.1) rSeam
        (Prover.seam_transcript_appendRight hn rSeam.1) s,
      ← evalDist_simulateQ_run'_bind _ hso]
  rw [← evalDist_simulateQ_run'_bind _ hso]
  -- The appended LHS is now the message-discharge shape; close by the same syntactic factoring as
  -- the bare `appendRunRightDistResidual_holds_challenge` ending, under the simulated `evalDist`.
  refine congrArg (fun X => evalDist (StateT.run'
      (simulateQ (impl.addLift challengeQueryImpl :
        QueryImpl (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (StateT σ ProbComp)) X) s)) ?_
  apply eq_of_heq
  have hseam : HEq ((P₁.append P₂).runToRound (⟨m, by omega⟩ : Fin (m + n)).castSucc stmt wit)
      (liftM (P₁.runToRound (Fin.last m) stmt wit) :
        OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _) := by
    have := Prover.append_runToRound_seam (P₁ := P₁) (P₂ := P₂) (stmt := stmt) (wit := wit)
    rwa [show ((Fin.last m).castLE (by omega) : Fin (m + n + 1))
        = (⟨m, by omega⟩ : Fin (m + n)).castSucc from by ext; simp] at this
  simp only [Prover.run_eq_runToRound_last, liftM_bind, bind_assoc, liftM_pure, pure_bind,
    bind_map_left]
  refine Prover.bind_heq_congr
    (by rw [Prover.append_Transcript_seam_castSucc hn,
      Prover.append_PrvState_seam_castSucc hn]; rfl) rfl
    hseam (fun rSeam x hr => ?_)
  obtain ⟨ht, hs⟩ := Prover.prod_heq_split (Prover.append_Transcript_seam_castSucc hn)
    (Prover.append_PrvState_seam_castSucc hn) hr
  have hc2 : cast (Prover.append_PrvState_seam_castSucc hn) rSeam.2 = x.2 :=
    eq_of_heq ((cast_heq _ _).trans hs)
  have hc1 : cast (Prover.append_Transcript_seam_castSucc hn) rSeam.1 = x.1 :=
    eq_of_heq ((cast_heq _ _).trans ht)
  rw [hc2, hc1]
  apply heq_of_eq
  simp only [OracleComp.liftComp_eq_liftM, Prover.append_output_last hn,
    Transcript.appendRight_full, cast_cast, cast_eq]
  refine bind_congr fun x_1 => bind_congr fun a => ?_
  simp only [← OracleComp.liftComp_eq_liftM]
  rw [Prover.liftComp_liftComp (spec := oSpec) (midSpec := oSpec + [pSpec₂.Challenge]ₒ)
    (superSpec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (fun t => rfl)]

/-- **Syntactic seam-chain form of the appended reduction run (prover unfactored).** The appended
reduction run is, as an `OptionT` value, the appended prover's run followed by the two verifier legs
on the two transcript halves. Mirror of `append_run_natural_msg`'s refold with the prover-side
factoring *omitted* (it is false at a challenge seam); the verifier-side split is the definitional
`Verifier.append`. -/
theorem append_run_eq_seamChain
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (stmt : Stmt₁) (wit : Wit₁) :
    (R₁.append R₂).run stmt wit
      = ((liftM ((R₁.prover.append R₂.prover).run stmt wit) :
          OptionT (OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ))
            (FullTranscript (pSpec₁ ++ₚ pSpec₂) × Stmt₃ × Wit₃)) >>= fun pr =>
        (MonadLift.monadLift (R₁.verifier.verify stmt pr.1.fst) :
            OptionT (OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)) Stmt₂)
          >>= fun s₂ =>
          (MonadLift.monadLift (R₂.verifier.verify s₂ pr.1.snd) :
              OptionT (OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)) Stmt₃)
            >>= fun s₃ =>
            pure (pr, s₃)) := by
  simp only [Reduction.run, Reduction.append, Verifier.append, Verifier.run,
    liftM_bind, bind_assoc, OptionT.liftM_run_getM_bind, liftM_pure, pure_bind]
  rfl

/-- **The simulated appended honest game factors at a challenge seam (`evalDist`-level).** The
distributional core of completeness `hGameFactor` for a `V_to_P` seam: the simulated honest game of
`R₁.append R₂` — running its rounds under `impl.addLift challengeQueryImpl` — has the same `evalDist`
as the **union-bound order** `appendStage₁ ; appendStage₂` (= `(P₁→V₁) ; (P₂→V₂)`), in the `mx >>= my`
shape `probComp_seam_completeness` consumes.

The natural-order chain `P₁ → P₂ → V₁ → V₂` is reached from the appended run by the simulated seam
swap `evalDist_simulateQ_swap_prefix` (the seam `getChallenge` commutes past `P₁.output` under the
state-preserving `impl.addLift challengeQueryImpl`); the `P₂`-past-`V₁` reorder to the stage chain is
the proven `seam_swap_evalDist_eq`. -/
theorem append_game_factor_challenge
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (stmt : Stmt₁) (wit : Wit₁) (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .V_to_P)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .V_to_P)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0) :
    evalDist (gameOf init impl (R₁.append R₂) stmt wit)
      = evalDist (init >>= fun s =>
          StateT.run' (simulateQ (impl.addLift challengeQueryImpl)
            ((appendStage₁ R₁ R₂ stmt wit) >>= (appendStage₂ R₁ R₂)).run) s) := by
  -- The `P₂`-past-`V₁` reorder (natural-order → stage chain), seam-direction-agnostic. Pin the
  -- seam-swap `spec` (and `challengeQueryImpl`'s `pSpec`) to the combined challenge oracle so every
  -- instance (the combined `SampleableType` for `challengeQueryImpl`, the per-phase `SubSpec` lifts in
  -- `W1`/`W2`) is synthesized the *same* way the goal's are — no `haveI` indirection, no instance-term
  -- mismatch under `Eq.trans`.
  have hswap := seam_swap_evalDist_eq
    (spec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) init
    (impl.addLift (challengeQueryImpl))
    (addLift_state_preserving impl himplSP)
    (liftM (R₁.prover.run stmt wit)) (fun x => liftM (R₂.prover.run x.2.1 x.2.2))
    (fun x => (MonadLift.monadLift (R₁.verifier.verify stmt x.1) :
        OptionT (OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)) Stmt₂))
    (fun x a s₂ => (MonadLift.monadLift (R₂.verifier.verify s₂ a.1) :
          OptionT (OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)) Stmt₃) >>= fun s₃ =>
      pure ((x.1 ++ₜ a.1, a.2.1, a.2.2), s₃))
    (fun x s' => simulateQ_run_neverFail _ (addLift_neverFail impl himplNF) _ s')
  -- Unfold `gameOf` (LHS) and the stage chain (RHS) so the goal's RHS becomes `hswap`'s union-bound
  -- RHS *syntactically*; `appendStageᵢ` unfold to exactly the `liftM FSTᵢ ≫ Wᵢ ≫ pure` legs.
  simp only [gameOf, appendStage₁, appendStage₂]
  -- Bridge to `hswap` (the `P₂`-past-`V₁` reorder). `convert` absorbs the defeq instance-term
  -- differences (the combined-challenge `SampleableType`); the residual goal is the seam-challenge
  -- swap (`appended game = natural-order game`).
  refine Eq.trans ?_ hswap
  -- `gameOf` (`abbrev`) unfolds to `init >>= fun s => (simulateQ so (·.run)).run' s`; pull `evalDist`
  -- through the `init` bind so the residual is the per-seed seam-challenge swap.
  simp only [gameOf]
  rw [evalDist_bind, evalDist_bind]
  refine bind_congr fun s => ?_
  -- The seam-challenge swap under simulation. The appended run's seam `getChallenge` sits before the
  -- `P₁.output` replay; `simulateQ_append_run_challenge_evalDist` (state-preserving) commutes them
  -- to the natural order, matching the bare `Prover.append_run_evalDist_challenge` reorder lifted
  -- through `simulateQ`.
  have hso := addLift_state_preserving (pSpec := pSpec₁ ++ₚ pSpec₂) impl himplSP
  -- Expose the appended run as `liftM (Pa.run) ≫ V₁ ≫ V₂` (prover unfactored), then strip the
  -- `OptionT` layer on both sides so the seam head is a plain `OracleComp` bind.
  rw [append_run_eq_seamChain R₁ R₂ stmt wit]
  simp only [OptionT.run_bind, Option.elimM, lift_run_elim, OptionT.run_pure]
  -- Split off the appended prover head, swap it for the sequential `P₁.run ≫ P₂.run` (the simulated
  -- seam-challenge commute), and refold.
  rw [evalDist_simulateQ_run'_bind _ hso ((R₁.prover.append R₂.prover).run stmt wit),
    simulateQ_append_run_challenge_evalDist R₁.prover R₂.prover stmt wit hn hDir hDir₂ himplSP s,
    ← evalDist_simulateQ_run'_bind _ hso]
  -- Both sides are now the factored chain; the residual is the syntactic verifier-leg relabel
  -- (`(x.1 ++ₜ a.1).fst/.snd = x.1/a.1`).
  refine congrArg (fun X => evalDist (StateT.run'
      (simulateQ (impl.addLift challengeQueryImpl :
        QueryImpl (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (StateT σ ProbComp)) X) s)) ?_
  simp only [bind_assoc, pure_bind, FullTranscript.append_fst, FullTranscript.append_snd]

/-- **Challenge-seam append completeness (`hGameFactor` discharged via the seam-challenge swap).**
The challenge-seam analogue of `append_completeness_msg_via_seamFactor`: threads
`append_game_factor_challenge` into `append_completeness_msg_proof` for the same two-stage
decomposition, leaving only the (seam-direction-agnostic) per-phase challenge-oracle relabel bridges
`hStage1Bridge`/`hStage2Bridge` and the game totality `hTot` (all discharged in
`AppendSeamBridges.lean`). -/
theorem append_completeness_challenge_via_seamFactor
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    {e₁ e₂ : ℝ≥0}
    (h₁ : R₁.completeness init impl rel₁ rel₂ e₁)
    (h₂ : R₂.completeness init impl rel₂ rel₃ e₂)
    (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .V_to_P)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .V_to_P)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    (hStage1Bridge : ∀ stmt wit, (stmt, wit) ∈ rel₁ →
      evalDist (Prod.fst <$> (init >>= fun s =>
          StateT.run (simulateQ (impl.addLift challengeQueryImpl)
            (OptionT.run (appendStage₁ R₁ R₂ stmt wit))) s))
        = evalDist (gameOf init impl R₁ stmt wit))
    (hStage2Bridge : ∀ stmt wit, (stmt, wit) ∈ rel₁ →
      ∀ a s', (some a, s') ∈ support
            (init >>= fun s =>
              StateT.run (simulateQ (impl.addLift challengeQueryImpl)
                (OptionT.run (appendStage₁ R₁ R₂ stmt wit))) s) →
          goodOf m pSpec₁ rel₂ a →
          Pr[fun o => ¬ Option.elim o False (goodOf (m + n) (pSpec₁ ++ₚ pSpec₂) rel₃ ·)
              | (StateT.run' (simulateQ (impl.addLift challengeQueryImpl)
                  (OptionT.run (appendStage₂ R₁ R₂ a))) s' : ProbComp (Option _))]
            ≤ Pr[fun o => ¬ Option.elim o False (goodOf n pSpec₂ rel₃ ·)
              | gameOf init impl R₂ a.2 a.1.2.2])
    (hTot : ∀ stmt wit, (stmt, wit) ∈ rel₁ →
      Pr[⊥ | gameOf init impl (R₁.append R₂) stmt wit] = 0) :
    (R₁.append R₂).completeness init impl rel₁ rel₃ (e₁ + e₂) :=
  append_completeness_msg_proof R₁ R₂ h₁ h₂
    (so := impl.addLift challengeQueryImpl)
    (mx := fun p => appendStage₁ R₁ R₂ p.1 p.2)
    (my := fun p => appendStage₂ R₁ R₂)
    (fun stmt wit _ =>
      append_game_factor_challenge R₁ R₂ stmt wit hn hDir hDir₂ himplSP himplNF)
    hStage1Bridge hStage2Bridge hTot

/-- **Challenge-seam factoring of the *malicious-prover* soundness game (`evalDist`-level,
per-seed).** The soundness analogue of `append_game_factor_challenge`: the simulated run of an
*arbitrary* malicious prover over `pSpec₁ ++ₚ pSpec₂` against the appended verifier `V₁.append V₂`
has, per seed `s` under the state-preserving honest implementation, the same distribution as the
**natural-order seam chain** `fst ≫ snd ≫ V₁ ≫ V₂` — the exact shape the union-bound machinery
(`probComp_seam_swap_union_le`) consumes.

The prover-side factoring is *distributional only* at a challenge seam (the appended prover samples
the seam `getChallenge` before replaying `fst`'s output; syntactic `Prover.run_seam_factor` is
false here): `Prover.merge_run` identifies the malicious prover with `fst ≫ snd` merged, and the
simulated seam-challenge commute `simulateQ_append_run_challenge_evalDist` reorders it. The
verifier-side split is the definitional `Verifier.append`. -/
theorem soundness_game_factor_challenge
    {WitIn WitOut : Type}
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (prover : Prover oSpec Stmt₁ WitIn Stmt₃ WitOut (pSpec₁ ++ₚ pSpec₂))
    (stmt : Stmt₁) (wit : WitIn) (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .V_to_P)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .V_to_P)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (s : σ) :
    evalDist (StateT.run' (simulateQ (impl.addLift challengeQueryImpl :
        QueryImpl (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (StateT σ ProbComp))
        ((Reduction.run stmt wit ⟨prover, V₁.append V₂⟩).run)) s)
      = evalDist (StateT.run' (simulateQ (impl.addLift challengeQueryImpl :
        QueryImpl (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (StateT σ ProbComp))
        ((liftM (liftM (prover.fst.run stmt wit) :
            OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _) >>= fun x =>
          liftM (liftM (prover.snd.run x.2.1 x.2.2) :
            OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _) >>= fun a =>
          (MonadLift.monadLift (V₁.verify stmt x.1) :
            OptionT (OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)) Stmt₂) >>= fun s₂ =>
          (MonadLift.monadLift (V₂.verify s₂ a.1) :
            OptionT (OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)) Stmt₃) >>= fun s₃ =>
          pure ((x.1 ++ₜ a.1, a.2.1, a.2.2), s₃)).run)) s) := by
  have hso := addLift_state_preserving (pSpec := pSpec₁ ++ₚ pSpec₂) impl himplSP
  -- Syntactic seam chain (prover unfactored): mirror of `append_run_eq_seamChain` for the
  -- malicious-prover reduction `⟨prover, V₁.append V₂⟩`.
  have hchain : (Reduction.run stmt wit ⟨prover, V₁.append V₂⟩)
      = ((liftM (prover.run stmt wit) :
          OptionT (OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ))
            (FullTranscript (pSpec₁ ++ₚ pSpec₂) × Stmt₃ × WitOut)) >>= fun pr =>
        (MonadLift.monadLift (V₁.verify stmt pr.1.fst) :
            OptionT (OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)) Stmt₂) >>= fun s₂ =>
        (MonadLift.monadLift (V₂.verify s₂ pr.1.snd) :
            OptionT (OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)) Stmt₃) >>= fun s₃ =>
        pure (pr, s₃)) := by
    simp only [Reduction.run, Verifier.append, Verifier.run, liftM_bind, bind_assoc,
      OptionT.liftM_run_getM_bind, liftM_pure, pure_bind]
    rfl
  rw [hchain]
  -- Strip the `OptionT` layer so the prover prefix is a plain `OracleComp` bind.
  simp only [OptionT.run_bind, Option.elimM, lift_run_elim, OptionT.run_pure]
  -- The simulated seam-challenge swap of the malicious prover's run (via `merge_run`).
  have hPswap : evalDist (StateT.run' (simulateQ (impl.addLift challengeQueryImpl :
        QueryImpl (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (StateT σ ProbComp))
        (prover.run stmt wit)) s)
      = evalDist (StateT.run' (simulateQ (impl.addLift challengeQueryImpl :
        QueryImpl (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (StateT σ ProbComp))
        ((do
          let ⟨transcript₁, stmt₂, wit₂⟩ ← liftM (prover.fst.run stmt wit)
          let ⟨transcript₂, stmt₃, wit₃⟩ ← liftM (prover.snd.run stmt₂ wit₂)
          return ⟨transcript₁ ++ₜ transcript₂, stmt₃, wit₃⟩) :
            OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
              (FullTranscript (pSpec₁ ++ₚ pSpec₂) × Stmt₃ × WitOut))) s) := by
    rw [show prover.run stmt wit
        = ((Prover.fst prover).append (Prover.snd prover)).run stmt wit from
      (Prover.merge_run prover hn stmt wit).symm]
    exact simulateQ_append_run_challenge_evalDist (Prover.fst prover) (Prover.snd prover)
      stmt wit hn hDir hDir₂ himplSP s
  -- Split off the prover head, swap, refold.
  rw [evalDist_simulateQ_run'_bind _ hso (prover.run stmt wit), hPswap,
    ← evalDist_simulateQ_run'_bind _ hso]
  -- Both sides are now the factored chain; the residual is the syntactic verifier-leg relabel.
  refine congrArg (fun X => evalDist (StateT.run'
      (simulateQ (impl.addLift challengeQueryImpl :
        QueryImpl (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (StateT σ ProbComp)) X) s)) ?_
  simp only [OptionT.run_bind, Option.elimM, lift_run_elim, OptionT.run_pure, bind_assoc,
    pure_bind, FullTranscript.append_fst, FullTranscript.append_snd]

end Reduction
