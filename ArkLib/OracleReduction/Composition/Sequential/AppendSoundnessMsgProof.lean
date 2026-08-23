/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.AppendSoundnessProof
import ArkLib.OracleReduction.Composition.Sequential.AppendSoundnessSeamTransfer
import ArkLib.OracleReduction.RunUnroll

/-!
# Binary sequential-composition soundness (message seam) — `appendSoundnessResidual` discharge

This file assembles the verified seam-decomposition toolkit into the binary append-soundness
keystone for the **message-first seam** case (the case that arises in the BCS compiler, whose
opening phase opens with a commitment/opening prover message, and in LogUp Protocol 2). It targets
`Verifier.appendSoundnessResidual` — the deep, arbitrary-malicious-prover seam decomposition +
union bound shared across issues #13 / #25 / #62 / #433.

## Proof architecture (all bricks proven upstream)

1. **Run factoring** (verified, this file). `Prover.run_seam_factor` splits the arbitrary malicious
   prover over `pSpec₁ ++ₚ pSpec₂` into `prover.fst` / `prover.snd`; `Verifier.append_run` (`rfl`)
   splits `V₁.run ≫ V₂.run`. With `FullTranscript.append_fst/snd` and `OptionT.liftM_run_getM_bind`
   the appended soundness experiment refolds to the canonical seam chain `liftM FST ≫ liftM SND ≫
   W1 ≫ W2` (provers first, then verifiers).
2. **Reorder + union bound** (verified, this file). The goal is in `probComp_seam_swap_union_le`'s
   natural order; that proven theorem commutes the `snd` prover stage past the `V₁` verifier stage
   (state-preserving ⇒ distributionally independent) and bounds the bad event `stmtOut ∈ lang₃` —
   which factors through the intermediate `stmt₂ ∈ lang₂` — by `ε₁ + ε₂`.
3. **Stage bounds** (the two remaining `sorry`s — the genuine per-phase soundness content). Each is
   `Vᵢ.soundness εᵢ` applied to the phase-`i` seam soundness prover (`prover.fstSound` /
   `prover.sndSound`), modulo the challenge-oracle-seam reconciliation (the appended game runs each
   phase's rounds under the *combined* challenge oracle, whereas `Vᵢ.soundness` runs them under
   `pSpecᵢ`'s own — bridged by `evalDist_challengeSeam_bridge_left/right`) and, for phase 1, the
   marginalization of `fstSound`'s dummy prover output (`probEvent_simQ_run'_congr_marginal`).

The side conditions `himplSP` (state-preserving `impl`) and `himplNF` (never-failing `impl`) are the
soundness analogue of the completeness proof's `hImplSupp` / `hInit`; they are discharged for the
honest interactive implementation `impl.addLift challengeQueryImpl` by `addLift_state_preserving` /
`addLift_neverFail`.
-/

open OracleComp OracleSpec ProtocolSpec OptionTStateT
open scoped ENNReal NNReal

universe u

namespace Verifier

variable {ι : Type} {oSpec : OracleSpec ι} {Stmt₁ Stmt₂ Stmt₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

theorem marg_het_state {ιₛ : Type} {spec : OracleSpec ιₛ} {α₁ α₂ β : Type}
    (so : QueryImpl spec (StateT σ ProbComp)) (s' : σ)
    (X : OptionT (OracleComp spec) α₁) (Y : OptionT (OracleComp spec) α₂)
    (g₁ : α₁ → β) (g₂ : α₂ → β) (q : β → Prop) (h : (g₁ <$> X) = (g₂ <$> Y)) :
    Pr[fun o => Option.elim o False (fun a => q (g₁ a)) |
        (simulateQ so X.run).run' s']
    = Pr[fun o => Option.elim o False (fun a => q (g₂ a)) |
        (simulateQ so Y.run).run' s'] := by
  have h' : Option.map g₁ <$> X.run = Option.map g₂ <$> Y.run := by
    have := congrArg OptionT.run h; simpa only [OptionT.run_map] using this
  have h'' : (Option.map g₁ <$> simulateQ so X.run) = (Option.map g₂ <$> simulateQ so Y.run) := by
    rw [← simulateQ_map, ← simulateQ_map, h']
  have key : (Option.map g₁ <$> (simulateQ so X.run).run' s')
           = (Option.map g₂ <$> (simulateQ so Y.run).run' s') := by
    simp only [StateT.run'_eq]
    have h3 := congrFun (congrArg StateT.run h'') s'
    simp only [StateT.run_map] at h3
    have h4 := congrArg (fun z => Prod.fst <$> z) h3
    simp only [Functor.map_map, Function.comp_def] at h4 ⊢; exact h4
  have hpe1 : (fun o : Option α₁ => Option.elim o False (fun a => q (g₁ a)))
      = (fun ob => Option.elim ob False q) ∘ (Option.map g₁) := by funext o; cases o <;> rfl
  have hpe2 : (fun o : Option α₂ => Option.elim o False (fun a => q (g₂ a)))
      = (fun ob => Option.elim ob False q) ∘ (Option.map g₂) := by funext o; cases o <;> rfl
  rw [hpe1, hpe2, probEvent_comp, probEvent_comp, key]

/-- **Heterogeneous marginalization congruence.** Like `probEvent_simQ_run'_congr_marginal` but the two
computations may have *different* value types `α₁`, `α₂`, projected to a common `β` by `g₁`/`g₂`. Needed
because the phase-1 seam body (`P.fst`'s output `state × Unit`) and `Reduction.run {fstSound}` (output
`Stmt₂ × state`) differ in type, yet share the verifier-output (`Prod.snd`) marginal. Same proof as the
homogeneous version (free-monad/`simulateQ_map`/`StateT.run_map`), just with `g₁`/`g₂`. -/
theorem marg_het {ιₛ : Type} {spec : OracleSpec ιₛ} {α₁ α₂ β : Type}
    (so : QueryImpl spec (StateT σ ProbComp)) (init : ProbComp σ)
    (X : OptionT (OracleComp spec) α₁) (Y : OptionT (OracleComp spec) α₂)
    (g₁ : α₁ → β) (g₂ : α₂ → β) (q : β → Prop) (h : (g₁ <$> X) = (g₂ <$> Y)) :
    Pr[fun o => Option.elim o False (fun a => q (g₁ a)) |
        init >>= fun s => (simulateQ so X.run).run' s]
    = Pr[fun o => Option.elim o False (fun a => q (g₂ a)) |
        init >>= fun s => (simulateQ so Y.run).run' s] := by
  have h' : Option.map g₁ <$> X.run = Option.map g₂ <$> Y.run := by
    have := congrArg OptionT.run h; simpa only [OptionT.run_map] using this
  have h'' : (Option.map g₁ <$> simulateQ so X.run) = (Option.map g₂ <$> simulateQ so Y.run) := by
    rw [← simulateQ_map, ← simulateQ_map, h']
  have key : (Option.map g₁ <$> (init >>= fun s => (simulateQ so X.run).run' s))
           = (Option.map g₂ <$> (init >>= fun s => (simulateQ so Y.run).run' s)) := by
    simp only [map_bind, StateT.run'_eq]
    refine bind_congr (fun s => ?_)
    have h3 := congrFun (congrArg StateT.run h'') s
    simp only [StateT.run_map] at h3
    have h4 := congrArg (fun z => Prod.fst <$> z) h3
    simp only [Functor.map_map, Function.comp] at h4 ⊢; exact h4
  have hpe1 : (fun o : Option α₁ => Option.elim o False (fun a => q (g₁ a)))
      = (fun ob => Option.elim ob False q) ∘ (Option.map g₁) := by funext o; cases o <;> rfl
  have hpe2 : (fun o : Option α₂ => Option.elim o False (fun a => q (g₂ a)))
      = (fun ob => Option.elim ob False q) ∘ (Option.map g₂) := by funext o; cases o <;> rfl
  rw [hpe1, hpe2, probEvent_comp, probEvent_comp, key]

/-- **Lift coherence: `OracleComp`-first vs `OptionT`-first lift of a phase computation.** The seam
factoring lifts the phase-1 prover's `Prover.run` *across `OracleComp`* (pSpec₁ → combined) and then
into `OptionT`; the per-phase soundness game instead lifts it into `OptionT` first and then across.
Both routes (`OracleComp pSpec₁ → OptionT combined`) coincide: each `OptionT.run` reduces to
`some <$> liftM A`, which is definitionally `liftComp A`. This reconciles the goal's
`liftM (liftM A : OracleComp combined)` with the `OptionT`-side form. -/
theorem lift_oc_optionT_coh {α : Type}
    (A : OracleComp (oSpec + [pSpec₁.Challenge]ₒ) α) :
    (liftM (liftM A : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) α)
      : OptionT (OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)) α)
    = (liftM (liftM A : OptionT (OracleComp (oSpec + [pSpec₁.Challenge]ₒ)) α)
      : OptionT (OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)) α) := by
  apply OptionT.ext
  simp only [liftM_OptionT_eq, OptionT.run_mk]
  show OptionT.run (liftM (liftM A : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) α)) = _
  rw [OptionT.run_monadLift]
  simp only [monadLift_eq_self]
  conv_rhs => rw [show (liftM A : OptionT (OracleComp (oSpec + [pSpec₁.Challenge]ₒ)) α)
      = OptionT.lift A from rfl]
  simp only [OptionT.lift, OptionT.mk, simulateQ_map, OptionT.run, map_eq_pure_bind,
    simulateQ_bind, simulateQ_pure]
  rfl

/-- **`(liftM g).run = liftM g.run` across the `pSpec₁` challenge seam.** The `OptionT`-lift of `g`
(`oSpec+[pSpec₁.Challenge]ₒ → combined`) commutes with `OptionT.run`: both reduce to
`liftComp = simulateQ (fun t => liftM (query t))` of the underlying `OracleComp`. Bridges the
`OptionT`-level seam body to the `OracleComp`-level `evalDist_run'_challengeSeam_left`. -/
theorem liftM_optionT_run_eq_seam {α : Type}
    (g : OptionT (OracleComp (oSpec + [pSpec₁.Challenge]ₒ)) α) :
    (liftM g : OptionT (OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)) α).run
    = (liftM (g.run) : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (Option α)) := by
  rw [liftM_OptionT_eq, OptionT.run]
  rw [show (liftM g.run : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (Option α))
      = OracleComp.liftComp g.run _ from (OracleComp.liftComp_eq_liftM _).symm,
    OracleComp.liftComp_def]
  rfl

/-- **Phase-1 challenge-seam transfer, at `probEvent`.** Any event `P` on the appended phase-1 game
(`liftM g` simulated under the *combined* challenge oracle) has the same probability as on `g`
simulated under `pSpec₁`'s own challenge oracle. Lifts `evalDist_run'_challengeSeam_left` (a per-state
`evalDist` equality on the `OracleComp` run) through the `init`-bind and `liftM`/`OptionT.run`
coherence (`liftM_optionT_run_eq_seam`) to the full soundness game. -/
theorem probEvent_seam_transfer_left {α : Type}
    (g : OptionT (OracleComp (oSpec + [pSpec₁.Challenge]ₒ)) α)
    (P : Option α → Prop) :
    Pr[P | init >>= fun s => (simulateQ
        (impl.addLift (challengeQueryImpl (pSpec := pSpec₁ ++ₚ pSpec₂)) :
          QueryImpl _ (StateT σ ProbComp))
        ((liftM g : OptionT (OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)) α)).run).run' s]
    = Pr[P | init >>= fun s => (simulateQ
        (impl.addLift (challengeQueryImpl (pSpec := pSpec₁)) :
          QueryImpl _ (StateT σ ProbComp)) g.run).run' s] := by
  have hed : evalDist (init >>= fun s => (simulateQ
        (impl.addLift (challengeQueryImpl (pSpec := pSpec₁ ++ₚ pSpec₂)) :
          QueryImpl _ (StateT σ ProbComp))
        ((liftM g : OptionT (OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)) α)).run).run' s)
      = evalDist (init >>= fun s => (simulateQ
        (impl.addLift (challengeQueryImpl (pSpec := pSpec₁)) :
          QueryImpl _ (StateT σ ProbComp)) g.run).run' s) := by
    rw [evalDist_bind, evalDist_bind]
    refine bind_congr fun s => ?_
    rw [liftM_optionT_run_eq_seam]
    exact OracleReduction.evalDist_run'_challengeSeam_left impl g.run s
  unfold probEvent
  rw [hed]

theorem lift_oc_optionT_coh_right {α : Type}
    (A : OracleComp (oSpec + [pSpec₂.Challenge]ₒ) α) :
    (liftM (liftM A : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) α)
      : OptionT (OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)) α)
    = (liftM (liftM A : OptionT (OracleComp (oSpec + [pSpec₂.Challenge]ₒ)) α)
      : OptionT (OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)) α) := by
  apply OptionT.ext
  simp only [liftM_OptionT_eq, OptionT.run_mk]
  show OptionT.run (liftM (liftM A : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) α)) = _
  rw [OptionT.run_monadLift]
  simp only [monadLift_eq_self]
  conv_rhs => rw [show (liftM A : OptionT (OracleComp (oSpec + [pSpec₂.Challenge]ₒ)) α)
      = OptionT.lift A from rfl]
  simp only [OptionT.lift, OptionT.mk, simulateQ_map, OptionT.run, map_eq_pure_bind,
    simulateQ_bind, simulateQ_pure]
  rfl

theorem liftM_optionT_run_eq_seam_right {α : Type}
    (g : OptionT (OracleComp (oSpec + [pSpec₂.Challenge]ₒ)) α) :
    (liftM g : OptionT (OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)) α).run
    = (liftM (g.run) : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (Option α)) := by
  rw [liftM_OptionT_eq, OptionT.run]
  rw [show (liftM g.run : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (Option α))
      = OracleComp.liftComp g.run _ from (OracleComp.liftComp_eq_liftM _).symm,
    OracleComp.liftComp_def]
  rfl

theorem probEvent_seam_transfer_right {α : Type}
    (g : OptionT (OracleComp (oSpec + [pSpec₂.Challenge]ₒ)) α)
    (P : Option α → Prop) (s' : σ) :
    Pr[P | (simulateQ
        (impl.addLift (challengeQueryImpl (pSpec := pSpec₁ ++ₚ pSpec₂)) :
          QueryImpl _ (StateT σ ProbComp))
        ((liftM g : OptionT (OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)) α)).run).run' s']
    = Pr[P | (simulateQ
        (impl.addLift (challengeQueryImpl (pSpec := pSpec₂)) :
          QueryImpl _ (StateT σ ProbComp)) g.run).run' s'] := by
  have hed : evalDist ((simulateQ
        (impl.addLift (challengeQueryImpl (pSpec := pSpec₁ ++ₚ pSpec₂)) :
          QueryImpl _ (StateT σ ProbComp))
        ((liftM g : OptionT (OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)) α)).run).run' s')
      = evalDist ((simulateQ
        (impl.addLift (challengeQueryImpl (pSpec := pSpec₂)) :
          QueryImpl _ (StateT σ ProbComp)) g.run).run' s') := by
    rw [liftM_optionT_run_eq_seam_right]
    exact OracleReduction.evalDist_run'_challengeSeam_right impl g.run s'
  unfold probEvent
  rw [hed]

/-- **Binary sequential-composition soundness, message-seam case.** Reduces the appended-verifier
soundness experiment (over an arbitrary malicious prover) to the two per-phase soundness bounds via
the verified seam toolkit. The remaining two goals are exactly `V₁.soundness ε₁` on the phase-1 seam
prover and `V₂.soundness ε₂` on the phase-2 seam prover, modulo the challenge-oracle-seam bridges. -/
theorem append_soundness_msg'
    [Inhabited Stmt₂]
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {lang₁ : Set Stmt₁} {lang₂ : Set Stmt₂} {lang₃ : Set Stmt₃} {ε₁ ε₂ : ℝ≥0}
    (h₁ : V₁.soundness init impl lang₁ lang₂ ε₁)
    (h₂ : V₂.soundness init impl lang₂ lang₃ ε₂)
    (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .P_to_V)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .P_to_V)
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
  simp only [Reduction.run, Prover.run_seam_factor prover hn hDir hDir₂, Verifier.append_run]
  -- Refold to the canonical seam chain `liftM FST ≫ liftM SND ≫ W1 ≫ W2`.
  simp only [liftM_bind, bind_assoc, map_eq_pure_bind, liftM_map, bind_map_left,
    OptionT.liftM_run_getM_bind, liftM_pure, pure_bind,
    FullTranscript.append_fst, FullTranscript.append_snd]
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

/-- **Unconditional discharge of the named append-soundness residual, message-seam case.** The
`Prop` `Verifier.appendSoundnessResidual V₁ V₂ h₁ h₂` is *definitionally*
`(V₁.append V₂).soundness init impl lang₁ lang₃ (ε₁ + ε₂)` — i.e. exactly the conclusion
of `append_soundness_msg'`. Hence for the message-first seam (the case that arises in the BCS
compiler and in LogUp Protocol 2) the residual is no longer an unproved hypothesis: it follows
from `append_soundness_msg'` under the same message-seam side conditions
(`hn`/`hDir`/`hDir₂` pinning the seam round and `pSpec₂`'s opening round to prover messages,
and `himplSP`/`himplNF`/`himplVB` on `impl`). This lets callers that previously had to *assume*
`appendSoundnessResidual` (e.g. `Verifier.append_soundness` and
`BCSCompiledPhases.toReduction_soundness_of_append`) instead *prove* it. -/
theorem append_soundness_msg_residual
    [Inhabited Stmt₂]
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {lang₁ : Set Stmt₁} {lang₂ : Set Stmt₂} {lang₃ : Set Stmt₃} {ε₁ ε₂ : ℝ≥0}
    (h₁ : V₁.soundness init impl lang₁ lang₂ ε₁)
    (h₂ : V₂.soundness init impl lang₂ lang₃ ε₂)
    (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .P_to_V)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .P_to_V)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    (himplVB : ∀ (t : oSpec.Domain) (s s' : σ),
      evalDist ((impl t).run' s) = evalDist ((impl t).run' s')) :
    Verifier.appendSoundnessResidual (init := init) (impl := impl)
      (lang₁ := lang₁) (lang₂ := lang₂) (lang₃ := lang₃) V₁ V₂ h₁ h₂ :=
  append_soundness_msg' V₁ V₂ h₁ h₂ hn hDir hDir₂ himplSP himplNF himplVB

/-- **Unconditional binary append-soundness, message-seam case** (the conclusion of
`Verifier.append_soundness` with the residual hypothesis *eliminated*). This is the drop-in
replacement for `Verifier.append_soundness` whenever the seam is a prover message: it proves
`(V₁.append V₂).soundness init impl lang₁ lang₃ (ε₁ + ε₂)` outright, instead of
assuming the named residual `appendSoundnessResidual`. -/
theorem append_soundness_msg
    [Inhabited Stmt₂]
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {lang₁ : Set Stmt₁} {lang₂ : Set Stmt₂} {lang₃ : Set Stmt₃} {ε₁ ε₂ : ℝ≥0}
    (h₁ : V₁.soundness init impl lang₁ lang₂ ε₁)
    (h₂ : V₂.soundness init impl lang₂ lang₃ ε₂)
    (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .P_to_V)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .P_to_V)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    (himplVB : ∀ (t : oSpec.Domain) (s s' : σ),
      evalDist ((impl t).run' s) = evalDist ((impl t).run' s')) :
    (V₁.append V₂).soundness init impl lang₁ lang₃ (ε₁ + ε₂) :=
  Verifier.append_soundness V₁ V₂ h₁ h₂
    (append_soundness_msg_residual V₁ V₂ h₁ h₂ hn hDir hDir₂ himplSP himplNF himplVB)

end Verifier

-- Axiom audit: the unconditional message-seam composition lemmas must not introduce `sorryAx`.
#print axioms Verifier.append_soundness_msg_residual
#print axioms Verifier.append_soundness_msg
