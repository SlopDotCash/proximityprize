/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.AppendCompletenessNonPerfect
import ArkLib.OracleReduction.Composition.Sequential.AppendRunEvalDist
import ArkLib.OracleReduction.RunUnroll

/-!
# The append challenge-seam: distributional run-factoring for completeness `hGameFactor`

This file attacks the deep distributional challenge-seam residual that is shared between the
error-bearing completeness append (`Reduction.append_completeness_msg_proof`, whose
`hGameFactor`/`hStage1Bridge`/`hStage2Bridge` are taken as named hypotheses) and the soundness
append. The genuinely-deep content is the **run-factoring of the simulated appended honest game at a
message seam, at the `evalDist` (distributional) level**: that
`gameOf init impl (R₁.append R₂) stmt wit` equals the two-stage composite game where stage 1 runs
`R₁` (prover₁ then verifier₁) and stage 2 runs `R₂` (prover₂ then verifier₂), with transcript
concatenation, in exactly the `mx >>= my` shape `OracleReduction.probComp_seam_completeness` consumes.

## What is proven here (no `sorry`)

* `Reduction.append_run_natural_msg` — the **fully proven** natural-order `OptionT` factoring of
  `(R₁.append R₂).run` for a message seam. Combines the proven syntactic prover-side run-factoring
  `Prover.append_run_msg` with the (`rfl`) verifier-side factoring `Verifier.append_run`, threaded
  through `Reduction_run_def`. The appended honest reduction run equals the natural order
  `P₁ → P₂ → V₁ → V₂` (both provers, then both verifiers).

* `Reduction.append_game_factor_msg` — the **fully proven** distributional run-factoring of the
  simulated appended game (the core of `hGameFactor`). Running the natural-order game under the honest
  interactive implementation `impl.addLift challengeQueryImpl` has the same `evalDist` as running the
  **union-bound order** `appendStage₁ ; appendStage₂ = (P₁ → V₁) ; (P₂ → V₂)` — the two-stage
  `R₁.run ; R₂.run` shape. The swap of the `P₂` prover stage past the `V₁` verifier stage is the
  proven distributional commutation `OptionTStateT.seam_swap_evalDist_eq`, whose `hso`/`hB`
  side-conditions are discharged by `addLift_state_preserving` / `addLift_neverFail` (the honest
  interactive implementation is state-preserving and never fails). This discharges the `hGameFactor`
  residual of `append_completeness_msg_proof` outright.

## The residual

`Reduction.append_completeness_msg_via_seamFactor` threads `append_game_factor_msg` into
`append_completeness_msg_proof` for the concrete two-stage decomposition
`so := impl.addLift challengeQueryImpl`, `mx := appendStage₁` (`P₁ → V₁`, intermediate context
carried), `my := appendStage₂` (`P₂ → V₂`, combined transcript). The **only** content not discharged
here is the per-phase challenge-oracle seam relabeling — that each phase, which in the appended game
runs its rounds under the *combined* challenge oracle `[(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ`, agrees
distributionally with the per-phase completeness game `gameOf R₁` / `gameOf R₂` that runs them under
`pSpecᵢ`'s own challenge oracle (the soundness analogue of
`evalDist_run'_challengeSeam_left/right`). That irreducible monad-commutation/relabel core is isolated
as the named hypotheses `hStage1Bridge` / `hStage2Bridge` (plus the game totality `hTot`), exactly
mirroring the named-residual discipline of `Reduction.append_completeness_msg_proof`.
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

/-- The `OptionT`-lift of a `pure` `OracleComp` value, run and `Option.elim`-ed, takes the success
branch unconditionally: it is just `k v`. Used to collapse the prover-output `return ⟨…⟩` step that
`Prover.append_run_msg` introduces (the prover never fails, so its assembled output is a pure lift). -/
private theorem liftM_pure_run_elim {ιₛ : Type} {spec : OracleSpec ιₛ} {α β : Type}
    (v : α) (k : α → OracleComp spec (Option β)) :
    ((liftM (pure v : OracleComp spec α) : OptionT (OracleComp spec) α).run >>= fun o =>
        o.elim (pure none) k) = k v := by
  show (((fun a => some a) <$> (pure v : OracleComp spec α)) >>= fun o => o.elim (pure none) k) = k v
  simp only [map_pure, pure_bind, Option.elim_some]

/-- **Natural-order `OptionT` factoring of the appended reduction run (message seam).** For a message
seam, running `R₁.append R₂` is, as an `OptionT (OracleComp …)` value, exactly the natural order: run
prover₁, then prover₂ (concatenating transcripts), then verifier₁ on the first transcript half, then
verifier₂ on the second half, finally assembling the output. Fully proven: the prover-side factoring
is the proven syntactic keystone `Prover.append_run_msg`, the verifier-side factoring is the (`rfl`)
`Verifier.append_run`, and `Reduction_run_def` exposes the prover→verifier sequencing. -/
theorem append_run_natural_msg
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (stmt : Stmt₁) (wit : Wit₁) (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .P_to_V)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .P_to_V) :
    (R₁.append R₂).run stmt wit
      = ((liftM (liftM (R₁.prover.run stmt wit)
              : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _) >>= fun x =>
          liftM (liftM (R₂.prover.run x.2.1 x.2.2)
              : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _) >>= fun a =>
            (MonadLift.monadLift (R₁.verifier.verify stmt x.1) :
                OptionT (OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)) Stmt₂)
              >>= fun s₂ =>
              (MonadLift.monadLift (R₂.verifier.verify s₂ a.1) :
                  OptionT (OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)) Stmt₃)
                >>= fun s₃ =>
                pure ((x.1 ++ₜ a.1, a.2.1, a.2.2), s₃)) :
          OptionT (OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)) _) := by
  -- Mirror the soundness refold (`AppendSoundnessMsgProof.append_soundness_msg'`): unfold
  -- `Reduction.run`, factor the appended prover with the proven syntactic keystone
  -- `Prover.append_run_msg`, split the appended verifier with the definitional `Verifier.append`,
  -- and refold to the canonical seam chain `liftM FST ≫ liftM SND ≫ V₁ ≫ V₂`. `OptionT.liftM_run_getM_bind`
  -- cancels the `getM` of the verifier leg.
  simp only [Reduction.run, Prover.append_run_msg (P₁ := R₁.prover) (P₂ := R₂.prover)
      stmt wit hn hDir hDir₂, Reduction.append, Verifier.append, Verifier.run,
    liftM_bind, bind_assoc,
    OptionT.liftM_run_getM_bind, liftM_pure, pure_bind,
    FullTranscript.append_fst, FullTranscript.append_snd]
  rfl

/-- **Stage-1 game of the appended honest reduction (message seam): `P₁ → V₁`, carrying the context.**
The phase-1 leg of the union-bound decomposition: run prover₁, then verifier₁ on the first transcript
half, returning the full intermediate context `(proverOut₁, verifierOut₁)`. This is the `mx` consumed
by `OracleReduction.probComp_seam_completeness`; its `Prod.fst`-marginal is the phase-1 completeness
game `gameOf R₁` (modulo the per-phase challenge-oracle seam relabel). -/
def appendStage₁
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (stmt : Stmt₁) (wit : Wit₁) :
    OptionT (OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ))
      ((FullTranscript pSpec₁ × Stmt₂ × Wit₂) × Stmt₂) :=
  liftM (liftM (R₁.prover.run stmt wit)
      : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _) >>= fun x =>
    (MonadLift.monadLift (R₁.verifier.verify stmt x.1) :
        OptionT (OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)) Stmt₂) >>= fun s₂ =>
      pure (x, s₂)

/-- **Stage-2 game of the appended honest reduction (message seam): `P₂ → V₂`, finishing the combined
transcript.** The phase-2 leg of the union-bound decomposition: from a stage-1 success carrying the
intermediate context `p`, run prover₂ (from `p.1`'s witness), then verifier₂ on the second transcript
half, assembling the combined-transcript output. This is the `my` consumed by
`OracleReduction.probComp_seam_completeness`. -/
def appendStage₂
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (p : (FullTranscript pSpec₁ × Stmt₂ × Wit₂) × Stmt₂) :
    OptionT (OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ))
      ((FullTranscript (pSpec₁ ++ₚ pSpec₂) × Stmt₃ × Wit₃) × Stmt₃) :=
  liftM (liftM (R₂.prover.run p.1.2.1 p.1.2.2)
      : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _) >>= fun a =>
    (MonadLift.monadLift (R₂.verifier.verify p.2 a.1) :
        OptionT (OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)) Stmt₃) >>= fun s₃ =>
      pure ((p.1.1 ++ₜ a.1, a.2.1, a.2.2), s₃)

/-- **The simulated appended honest game factors at the seam (`evalDist`-level, message seam).** The
distributional core of completeness `hGameFactor`. The simulated honest game of `R₁.append R₂` —
running the natural order `P₁ → P₂ → V₁ → V₂` under the honest interactive implementation
`impl.addLift challengeQueryImpl` — has the same `evalDist` as the **union-bound order**
`appendStage₁ ; appendStage₂` (= `(P₁→V₁) ; (P₂→V₂)`), in exactly the `mx >>= my` shape
`OracleReduction.probComp_seam_completeness` consumes.

Fully proven: `append_run_natural_msg` rewrites the appended run to the natural-order seam chain; the
`P₂`-past-`V₁` reorder is the proven distributional commutation
`OptionTStateT.seam_swap_evalDist_eq`, whose `hso` / `hB` side-conditions are discharged by
`addLift_state_preserving` / `addLift_neverFail` (the honest interactive implementation is
state-preserving and never fails — provers and the uniform challenge oracle cannot fail or mutate the
shared state). The only inputs are the message-seam directions and the `impl` state-preservation /
non-failure side-conditions. -/
theorem append_game_factor_msg
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (stmt : Stmt₁) (wit : Wit₁) (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .P_to_V)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .P_to_V)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0) :
    evalDist (gameOf init impl (R₁.append R₂) stmt wit)
      = evalDist (init >>= fun s =>
          StateT.run' (simulateQ (impl.addLift challengeQueryImpl)
            ((appendStage₁ R₁ R₂ stmt wit) >>= (appendStage₂ R₁ R₂)).run) s) := by
  -- The natural-order chain is `seam_swap_evalDist_eq`'s LHS; the union-bound order (`appendStage₁ ;
  -- appendStage₂`) is *definitionally* its RHS (the stages are exactly the two union-bound legs).
  have hswap := seam_swap_evalDist_eq init (impl.addLift challengeQueryImpl)
    (addLift_state_preserving impl himplSP)
    (liftM (R₁.prover.run stmt wit)) (fun x => liftM (R₂.prover.run x.2.1 x.2.2))
    (fun x => (MonadLift.monadLift (R₁.verifier.verify stmt x.1) :
        OptionT (OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)) Stmt₂))
    (fun x a s₂ => (MonadLift.monadLift (R₂.verifier.verify s₂ a.1) :
          OptionT (OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)) Stmt₃) >>= fun s₃ =>
      pure ((x.1 ++ₜ a.1, a.2.1, a.2.2), s₃))
    (fun x s' => simulateQ_run_neverFail _ (addLift_neverFail impl himplNF) _ s')
  -- Rewrite the appended honest run as the natural-order seam chain (`seam_swap`'s LHS).
  have hrun := append_run_natural_msg R₁ R₂ stmt wit hn hDir hDir₂
  show evalDist (init >>= fun s =>
      StateT.run' (simulateQ (impl.addLift challengeQueryImpl)
        ((R₁.append R₂).run stmt wit).run) s) = _
  rw [hrun]
  exact hswap

/-- **Non-perfect (error-bearing) message-seam append completeness via the proven seam factoring.**

The `hGameFactor` distributional run-factoring residual of `append_completeness_msg_proof` is
*discharged here* (`append_game_factor_msg`): the concrete two-stage decomposition is
`so := impl.addLift challengeQueryImpl`, `mx := appendStage₁` (`P₁ → V₁`), `my := appendStage₂`
(`P₂ → V₂`), and the appended simulated honest game equals (as an `evalDist`) the two-stage
`mx >>= my` game by the proven `append_run_natural_msg` + `seam_swap_evalDist_eq`. Hence this theorem
needs only the per-phase **challenge-oracle seam relabels** `hStage1Bridge` / `hStage2Bridge` (each
phase's appended-game run under the *combined* challenge oracle agrees distributionally with its own
per-phase completeness game) and the game totality `hTot` — the same irreducible residuals the
soundness append carries (`evalDist_run'_challengeSeam_left/right`). All other content (the deep
prover/verifier seam factoring and the two-stage union bound) is proven.

`himplSP` / `himplNF` (state-preserving / never-failing `impl`) are the completeness analogues of the
soundness append's side conditions; they hold for any honest interactive implementation and are
vacuous when `oSpec = []ₒ`. -/
theorem append_completeness_msg_via_seamFactor
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    {e₁ e₂ : ℝ≥0}
    (h₁ : R₁.completeness init impl rel₁ rel₂ e₁)
    (h₂ : R₂.completeness init impl rel₂ rel₃ e₂)
    (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .P_to_V)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .P_to_V)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    -- Per-phase challenge-oracle seam relabel residuals (the soundness analogue is
    -- `evalDist_run'_challengeSeam_left/right`): the stage-`i` game over the *combined* challenge
    -- oracle agrees distributionally with `gameOf Rᵢ` over `pSpecᵢ`'s own challenge oracle.
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
      append_game_factor_msg R₁ R₂ stmt wit hn hDir hDir₂ himplSP himplNF)
    hStage1Bridge hStage2Bridge hTot

end Reduction

#print axioms Reduction.append_run_natural_msg
#print axioms Reduction.append_game_factor_msg
#print axioms Reduction.append_completeness_msg_via_seamFactor
