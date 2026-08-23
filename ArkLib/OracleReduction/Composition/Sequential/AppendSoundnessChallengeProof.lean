/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.AppendSoundnessMsgProof
import ArkLib.OracleReduction.Composition.Sequential.AppendChallengeSeamChallenge

/-!
# Binary sequential-composition soundness (challenge seam) — `appendSoundnessResidual` discharge

The challenge-seam (`V_to_P` seam) analogue of `AppendSoundnessMsgProof.lean`: discharges
`Verifier.appendSoundnessResidual` when the second protocol opens with a *verifier challenge*.

The proof replays `append_soundness_msg'`'s canonical chain verbatim — the union-bound machinery
(`probComp_seam_swap_union_le`) and both per-phase bounds (the `fstSound`/`sndSound` provers, the
left/right challenge-oracle-seam transfers, and the state-independence collapse) are seam-type
agnostic — with a single substitution at the head: the *syntactic* prover run factoring
`Prover.run_seam_factor` (false at a challenge seam, where the appended prover samples the seam
`getChallenge` before replaying `fst`'s output) is replaced by the *distributional* factoring
`Reduction.soundness_game_factor_challenge` (built on the proven simulated seam-challenge commute
of `AppendChallengeSeamChallenge.lean`), spliced in at the `evalDist` level via
`probEvent_congr'`.

The extra `[oSpec.Fintype] [oSpec.Inhabited]` instances (inherited from the challenge-seam
factoring toolkit) are the only added side conditions relative to the message-seam case.
-/

open OracleComp OracleSpec ProtocolSpec OptionTStateT
open scoped ENNReal NNReal

universe u

namespace Verifier

variable {ι : Type} {oSpec : OracleSpec ι} {Stmt₁ Stmt₂ Stmt₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- **Binary append-soundness, challenge seam (`V_to_P`), canonical-chain proof.** The verbatim
replay of `append_soundness_msg'` with the syntactic prover run factoring replaced by the
distributional challenge-seam factoring `Reduction.soundness_game_factor_challenge` (spliced in at
the `evalDist` level via `probEvent_congr'`); the union bound and both per-phase
(`fstSound`/`sndSound`) bounds are seam-type agnostic. -/
theorem append_soundness_challenge'
    [oSpec.Fintype] [oSpec.Inhabited] [Inhabited Stmt₂]
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {lang₁ : Set Stmt₁} {lang₂ : Set Stmt₂} {lang₃ : Set Stmt₃} {ε₁ ε₂ : ℝ≥0}
    (h₁ : V₁.soundness init impl lang₁ lang₂ ε₁)
    (h₂ : V₂.soundness init impl lang₂ lang₃ ε₂)
    (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .V_to_P)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .V_to_P)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    (himplVB : ∀ (t : oSpec.Domain) (s s' : σ),
      evalDist ((impl t).run' s) = evalDist ((impl t).run' s')) :
    (V₁.append V₂).soundness init impl lang₁ lang₃ (ε₁ + ε₂) := by
  unfold Verifier.soundness
  intro WitIn WitOut witIn prover stmtIn hstmtIn
  intro pImpl
  rw [probEvent_optionT_mk_eq_elim]
  -- Replace the appended-run game by the natural-order seam chain. At a challenge seam the
  -- prover-side factoring is *distributional only* (`Reduction.soundness_game_factor_challenge`),
  -- so the replacement happens at the `evalDist` level rather than by a syntactic `simp`.
  have hEvalEq : 𝒟[do
        let s ← init
        (simulateQ pImpl (Reduction.run stmtIn witIn ⟨prover, V₁.append V₂⟩).run).run' s]
      = 𝒟[do
        let s ← init
        (simulateQ pImpl ((liftM (liftM (prover.fst.run stmtIn witIn) :
            OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _) >>= fun x =>
          liftM (liftM (prover.snd.run x.2.1 x.2.2) :
            OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _) >>= fun a =>
          (MonadLift.monadLift (V₁.verify stmtIn x.1) :
            OptionT (OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)) Stmt₂) >>= fun s₂ =>
          (MonadLift.monadLift (V₂.verify s₂ a.1) :
            OptionT (OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)) Stmt₃) >>= fun s₃ =>
          pure ((x.1 ++ₜ a.1, a.2.1, a.2.2), s₃)).run)).run' s] := by
    rw [evalDist_bind, evalDist_bind]
    refine bind_congr fun s => ?_
    exact Reduction.soundness_game_factor_challenge V₁ V₂ prover stmtIn witIn hn hDir hDir₂
      himplSP s
  rw [probEvent_congr' (fun _ _ => Iff.rfl) hEvalEq]
  -- Bridge the bad-event predicate `stmtOut ∈ lang₃` to the union-bound `¬·∈lang` form.
  rw [show (fun o : Option ((FullTranscript (pSpec₁ ++ₚ pSpec₂) × Stmt₃ × WitOut) × Stmt₃) =>
        o.elim False fun x => x.2 ∈ lang₃)
      = (fun o => ¬ Option.elim o True
          (fun d : (FullTranscript (pSpec₁ ++ₚ pSpec₂) × Stmt₃ × WitOut) × Stmt₃ =>
            d.2 ∉ lang₃)) from by
        funext o; cases o with
        | none => simp
        | some d => simp only [Option.elim_some, not_not]]
  -- Reorder (`snd` past `V₁`) + two-stage union bound. The goal is in
  -- `probComp_seam_swap_union_le`'s natural order `FST → SND → V₁ → V₂`; `FST`/`SND` are given and
  -- `W1`/`W2` are inferred by higher-order *pattern* (Miller) unification (each applied only to
  -- distinct bound variables), which avoids the `exact`/`apply` defeq blow-up.
  refine probComp_seam_swap_union_le init pImpl (addLift_state_preserving impl himplSP)
    (liftM (prover.fst.run stmtIn witIn))
    (fun x => liftM (prover.snd.run x.2.1 x.2.2))
    _ _ (fun x s' => simulateQ_run_neverFail _ (addLift_neverFail impl himplNF) _ s')
    (fun s₂ => s₂ ∉ lang₂)
    (fun d : (FullTranscript (pSpec₁ ++ₚ pSpec₂) × Stmt₃ × WitOut) × Stmt₃ => d.2 ∉ lang₃)
    (ε₁ : ℝ≥0∞) (ε₂ : ℝ≥0∞) ?_ ?_
  · -- Phase-1 bound: `V₁.soundness ε₁` on the phase-1 soundness prover `prover.fstSound`.
    have h1_bound := h₁ _ _ witIn (Prover.fstSound prover) stmtIn hstmtIn
    -- Avoid the `FreeM.mapM` whnf blow-up: do NOT pass the abstract prover-run do-body explicitly.
    -- `rw` with the predicate's pair type ascribed lets `X` be inferred by structural unification.
    rw [OptionTStateT.probEvent_run_eq_run'_fst (P :=
      fun (o : Option (_ × Stmt₂)) => ¬ Option.elim o True fun p => p.2 ∉ lang₂)]
    refine le_of_eq_of_le ?_ h1_bound
    rw [probEvent_optionT_mk]
    rw [show (fun o : Option ((FullTranscript pSpec₁ × _) × Stmt₂) =>
          ¬ Option.elim o True (fun p => p.2 ∉ lang₂))
        = (fun o => Option.elim o False (fun p => p.2 ∈ lang₂)) from by
          funext o; cases o with | none => simp | some d => simp only [Option.elim_some, not_not]]
    have body_eq : (Prod.snd <$> (liftM (prover.fst.run stmtIn witIn) >>= fun x =>
          liftM (V₁.run stmtIn x.1) >>= fun s₂ =>
            (pure (x, s₂) : OptionT (OracleComp (oSpec + [pSpec₁.Challenge]ₒ)) _)))
        = (Prod.snd <$> (Reduction.run stmtIn witIn
            { prover := prover.fstSound, verifier := V₁ } :
            OptionT (OracleComp (oSpec + [pSpec₁.Challenge]ₒ)) _)) := by
      unfold Reduction.run Prover.run Verifier.run
      simp only [Prover.fstSound_runToRound]
      simp only [Prover.fstSound, Prover.fst, map_bind, map_pure, bind_assoc, bind_pure_comp,
        bind_map_left, Functor.map_map, liftM_bind, liftM_pure, liftM_map, pure_bind, id_map,
        id_map', id_eq, Function.comp_def]
      -- Residual: identical runToRound on both sides; the verifier leg differs only by the
      -- bare getM-cancel (`liftM W = liftM W.run >>= getM`), the `f := pure` case of the lemma.
      refine bind_congr fun a => ?_
      have hgm := OptionT.liftM_run_getM_bind (V₁.verify stmtIn a.1)
        (pure : Stmt₂ → OptionT (OracleComp (oSpec + [pSpec₁.Challenge]ₒ)) Stmt₂)
      simp only [bind_pure] at hgm
      exact hgm.symm
    -- marg (using body_eq) reduces MID = RHS; remaining `?_` is the oracle bridge LHS = MID.
    refine Eq.trans ?_ (marg_het
      (impl.addLift (challengeQueryImpl (pSpec := pSpec₁))) init
      (liftM (prover.fst.run stmtIn witIn) >>= fun x =>
        liftM (V₁.run stmtIn x.1) >>= fun s₂ =>
          (pure (x, s₂) : OptionT (OracleComp (oSpec + [pSpec₁.Challenge]ₒ)) _))
      (Reduction.run stmtIn witIn { prover := prover.fstSound, verifier := V₁ })
      Prod.snd Prod.snd (· ∈ lang₂) body_eq)
    -- Prove `LHS = MID`. Refold the appended phase-1 game's body (run under the *combined* challenge
    -- oracle) as `liftM X`, where `X` is the same phase-1 game over `pSpec₁`'s own challenge oracle.
    -- The seam factoring lifts the `fst` prover's `Prover.run` *across `OracleComp`* first; reconcile
    -- that with `X`'s `OptionT`-first lift via `lift_oc_optionT_coh`, then push the lawful `OptionT`
    -- lift through the bind/pure and cross the `V₁`-leg seam with `OracleReduction.hcoh`.
    -- Transport the body through `ho` at the `evalDist` level (a body `rw`/`simp` trips the
    -- `FreeM.mapM` whnf blow-up), then transfer the combined game over `liftM X` to the
    -- `pSpec₁`-oracle game over `X` via `probEvent_seam_transfer_left`.
    refine Eq.trans ?_ (probEvent_seam_transfer_left (pSpec₂ := pSpec₂)
      (liftM (prover.fst.run stmtIn witIn) >>= fun x =>
        liftM (V₁.run stmtIn x.1) >>= fun s₂ =>
          (pure (x, s₂) : OptionT (OracleComp (oSpec + [pSpec₁.Challenge]ₒ)) _))
      (fun o => o.elim False fun p => p.2 ∈ lang₂))
    apply probEvent_congr' (fun _ _ => Iff.rfl)
    rw [evalDist_bind, evalDist_bind]
    refine bind_congr fun s => ?_
    rw [show pImpl = (impl.addLift (challengeQueryImpl (pSpec := pSpec₁ ++ₚ pSpec₂)) : QueryImpl _ (StateT σ ProbComp)) from rfl]
    apply congrArg (fun (oa : OptionT (OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)) _) =>
        evalDist ((simulateQ (impl.addLift (challengeQueryImpl (pSpec := pSpec₁ ++ₚ pSpec₂)) : QueryImpl _ (StateT σ ProbComp)) oa.run).run' s))
    rw [lift_oc_optionT_coh, liftM_bind]
    refine bind_congr fun x => ?_
    simp only [liftM_bind]
    congr 1
    apply OptionT.ext
    simp only [liftM, MonadLiftT.monadLift, MonadLift.monadLift, OptionT.run_mk]
    rw [← QueryImpl.simulateQ_compose]
    rfl
  · -- Phase-2 bound: `V₂.soundness ε₂` on the phase-2 soundness prover `prover.sndSound`.
    intro p s' _ h_pg
    have h2_bound := h₂ _ _ p.1.2.1 (Prover.sndSound prover) p.2 h_pg
    -- Reformat the bad-event predicate.
    rw [show (fun o : Option ((FullTranscript (pSpec₁ ++ₚ pSpec₂) × Stmt₃ × WitOut) × Stmt₃) =>
          ¬ Option.elim o True (fun d => d.2 ∉ lang₃))
        = (fun o => Option.elim o False (fun d => d.2 ∈ lang₃)) from by
          funext o; cases o with | none => simp | some d => simp only [Option.elim_some, not_not]]
    have body_eq_2 : (Prod.snd <$> (liftM (prover.snd.run p.1.2.1 p.1.2.2) >>= fun a =>
          liftM (V₂.run p.2 a.1) >>= fun s₃ =>
            (pure ((p.1.1 ++ₜ a.1, a.2.1, a.2.2), s₃) : OptionT (OracleComp (oSpec + [pSpec₂.Challenge]ₒ)) _)))
        = (Prod.snd <$> (Reduction.run p.2 p.1.2.1
            { prover := Prover.sndSound prover, verifier := V₂ } :
            OptionT (OracleComp (oSpec + [pSpec₂.Challenge]ₒ)) _)) := by
      unfold Reduction.run Prover.run Verifier.run
      simp only [Prover.sndSound_runToRound]
      simp only [Prover.sndSound, Prover.snd, map_bind, map_pure, bind_assoc, bind_pure_comp,
        bind_map_left, Functor.map_map, liftM_bind, liftM_pure, liftM_map, pure_bind, id_map,
        id_map', id_eq, Function.comp_def]
      refine bind_congr fun a => ?_
      refine bind_congr fun a_out => ?_
      have hgm := OptionT.liftM_run_getM_bind (V₂.verify p.2 a.1)
        (pure : Stmt₃ → OptionT (OracleComp (oSpec + [pSpec₂.Challenge]ₒ)) Stmt₃)
      simp only [bind_pure] at hgm
      exact hgm.symm
    -- Drop `init` from `h₂`'s bound by state-independence, pinning to the seam state `s'`.
    have h2_state_bound : Pr[fun o => Option.elim o False (fun d => d.2 ∈ lang₃) |
        (simulateQ
          (impl.addLift (challengeQueryImpl (pSpec := pSpec₂)) : QueryImpl _ (StateT σ ProbComp))
          (Reduction.run p.2 p.1.2.1 { prover := Prover.sndSound prover, verifier := V₂ }).run).run' s'] ≤ ε₂ := by
      have h2_init : Pr[fun o => Option.elim o False (fun d => d.2 ∈ lang₃) |
          init >>= fun s => (simulateQ
            (impl.addLift (challengeQueryImpl (pSpec := pSpec₂)) : QueryImpl _ (StateT σ ProbComp))
            (Reduction.run p.2 p.1.2.1 { prover := Prover.sndSound prover, verifier := V₂ }).run).run' s] ≤ ε₂ := by
        simp only [Verifier.soundness] at h2_bound
        rw [probEvent_optionT_mk] at h2_bound
        exact h2_bound
      refine le_trans (le_of_eq ?_) h2_init
      -- The per-state game `(...).run' s'` has the same `evalDist` as `(...).run' s` for every `s`
      -- (state independence), so the `init`-averaged game equals the `s'`-pinned one at `probEvent`.
      have heq : Pr[fun o => Option.elim o False (fun d => d.2 ∈ lang₃) |
            init >>= fun s => (simulateQ
              (impl.addLift (challengeQueryImpl (pSpec := pSpec₂)) : QueryImpl _ (StateT σ ProbComp))
              (Reduction.run p.2 p.1.2.1 { prover := Prover.sndSound prover, verifier := V₂ }).run).run' s]
          = Pr[fun o => Option.elim o False (fun d => d.2 ∈ lang₃) |
            init >>= fun _ => (simulateQ
              (impl.addLift (challengeQueryImpl (pSpec := pSpec₂)) : QueryImpl _ (StateT σ ProbComp))
              (Reduction.run p.2 p.1.2.1 { prover := Prover.sndSound prover, verifier := V₂ }).run).run' s'] := by
        have hed : evalDist (init >>= fun s => (simulateQ
              (impl.addLift (challengeQueryImpl (pSpec := pSpec₂)) : QueryImpl _ (StateT σ ProbComp))
              (Reduction.run p.2 p.1.2.1 { prover := Prover.sndSound prover, verifier := V₂ }).run).run' s)
            = evalDist (init >>= fun _ => (simulateQ
              (impl.addLift (challengeQueryImpl (pSpec := pSpec₂)) : QueryImpl _ (StateT σ ProbComp))
              (Reduction.run p.2 p.1.2.1 { prover := Prover.sndSound prover, verifier := V₂ }).run).run' s') := by
          rw [evalDist_bind, evalDist_bind]
          refine bind_congr fun s => ?_
          exact evalDist_simulateQ_run'_state_indep _ (addLift_state_preserving impl himplSP)
            (addLift_value_blind impl himplVB) _ s s'
        unfold probEvent
        rw [hed]
      rw [heq, probEvent_bind_const, probFailure_eq_zero, tsub_zero, one_mul]
    refine le_trans (le_of_eq ?_) h2_state_bound
    -- MID = RHS via marginalization through `body_eq_2`.
    refine Eq.trans ?_ (marg_het_state
      (impl.addLift (challengeQueryImpl (pSpec := pSpec₂))) s'
      (liftM (prover.snd.run p.1.2.1 p.1.2.2) >>= fun a =>
        liftM (V₂.run p.2 a.1) >>= fun s₃ =>
          (pure ((p.1.1 ++ₜ a.1, a.2.1, a.2.2), s₃) : OptionT (OracleComp (oSpec + [pSpec₂.Challenge]ₒ)) _))
      (Reduction.run p.2 p.1.2.1 { prover := Prover.sndSound prover, verifier := V₂ })
      (fun d => d.2) (fun d => d.2) (fun d => d ∈ lang₃) body_eq_2)
    -- MID2 = MID via the phase-2 challenge-seam transfer (combined → pSpec₂ own oracle).
    refine Eq.trans ?_ (probEvent_seam_transfer_right (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
      (liftM (prover.snd.run p.1.2.1 p.1.2.2) >>= fun a =>
        liftM (V₂.run p.2 a.1) >>= fun s₃ =>
          (pure ((p.1.1 ++ₜ a.1, a.2.1, a.2.2), s₃) : OptionT (OracleComp (oSpec + [pSpec₂.Challenge]ₒ)) _))
      (fun o => Option.elim o False (fun d => d.2 ∈ lang₃)) s')
    -- LHS = MID2: the goal's body (combined-oracle, double-lifted `snd` prover) refolds to `liftM`
    -- of the `pSpec₂`-own-oracle phase-2 body, via the double-lift coherence `lift_oc_optionT_coh_right`.
    apply probEvent_congr' (fun _ _ => Iff.rfl)
    rw [show pImpl = (impl.addLift (challengeQueryImpl (pSpec := pSpec₁ ++ₚ pSpec₂)) : QueryImpl _ (StateT σ ProbComp)) from rfl]
    apply congrArg (fun (oa : OptionT (OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)) _) =>
        evalDist ((simulateQ (impl.addLift (challengeQueryImpl (pSpec := pSpec₁ ++ₚ pSpec₂)) : QueryImpl _ (StateT σ ProbComp)) oa.run).run' s'))
    rw [lift_oc_optionT_coh_right, liftM_bind]
    refine bind_congr fun a => ?_
    simp only [liftM_bind]
    congr 1
    apply OptionT.ext
    simp only [liftM, MonadLiftT.monadLift, MonadLift.monadLift, OptionT.run_mk]
    rw [← QueryImpl.simulateQ_compose]
    rfl


/-- **Unconditional discharge of the named append-soundness residual, challenge-seam case.** The
challenge-seam companion of `append_soundness_msg_residual`: for a `V_to_P` seam (the second
protocol opens with a verifier challenge), `Verifier.appendSoundnessResidual V₁ V₂ h₁ h₂` — which is
definitionally `(V₁.append V₂).soundness init impl lang₁ lang₃ (ε₁ + ε₂)` — follows from
`append_soundness_challenge'` under the challenge-seam side conditions. Together with the
message-seam discharge this covers both possible directions of a non-empty second protocol's
opening round. -/
theorem append_soundness_challenge_residual
    [oSpec.Fintype] [oSpec.Inhabited] [Inhabited Stmt₂]
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {lang₁ : Set Stmt₁} {lang₂ : Set Stmt₂} {lang₃ : Set Stmt₃} {ε₁ ε₂ : ℝ≥0}
    (h₁ : V₁.soundness init impl lang₁ lang₂ ε₁)
    (h₂ : V₂.soundness init impl lang₂ lang₃ ε₂)
    (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .V_to_P)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .V_to_P)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    (himplVB : ∀ (t : oSpec.Domain) (s s' : σ),
      evalDist ((impl t).run' s) = evalDist ((impl t).run' s')) :
    Verifier.appendSoundnessResidual (init := init) (impl := impl)
      (lang₁ := lang₁) (lang₂ := lang₂) (lang₃ := lang₃) V₁ V₂ h₁ h₂ :=
  append_soundness_challenge' V₁ V₂ h₁ h₂ hn hDir hDir₂ himplSP himplNF himplVB

/-- **Unconditional binary append-soundness, challenge-seam case** (the conclusion of
`Verifier.append_soundness` with the residual hypothesis *eliminated*), for a `V_to_P` seam. -/
theorem append_soundness_challenge
    [oSpec.Fintype] [oSpec.Inhabited] [Inhabited Stmt₂]
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {lang₁ : Set Stmt₁} {lang₂ : Set Stmt₂} {lang₃ : Set Stmt₃} {ε₁ ε₂ : ℝ≥0}
    (h₁ : V₁.soundness init impl lang₁ lang₂ ε₁)
    (h₂ : V₂.soundness init impl lang₂ lang₃ ε₂)
    (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .V_to_P)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .V_to_P)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    (himplVB : ∀ (t : oSpec.Domain) (s s' : σ),
      evalDist ((impl t).run' s) = evalDist ((impl t).run' s')) :
    (V₁.append V₂).soundness init impl lang₁ lang₃ (ε₁ + ε₂) :=
  Verifier.append_soundness V₁ V₂ h₁ h₂
    (append_soundness_challenge_residual V₁ V₂ h₁ h₂ hn hDir hDir₂ himplSP himplNF himplVB)

end Verifier

-- Axiom audit: the unconditional challenge-seam composition lemmas must not introduce `sorryAx`.
#print axioms Verifier.append_soundness_challenge'
#print axioms Verifier.append_soundness_challenge_residual
#print axioms Verifier.append_soundness_challenge
