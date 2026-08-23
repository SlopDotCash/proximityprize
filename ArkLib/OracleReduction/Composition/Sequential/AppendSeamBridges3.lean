/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.AppendSeamBridges2

/-!
# Assembling the completeness-append keystone from the proven seam bricks (issue #13)

`Reduction.append_completeness_msg_via_seamFactor` (in `AppendChallengeSeam.lean`) closes the
non-perfect (error-bearing) message-seam append completeness from the proven distributional seam
factoring `append_game_factor_msg`, *modulo* three residual hypotheses `hStage1Bridge`,
`hStage2Bridge`, `hTot`. This file discharges all three from the now-proven `OptionT.run`-level seam
bricks `appendStage₁_run_eq_liftM` / `appendStage₂_run_eq_liftM` (`AppendSeamBridges2.lean`) and the
proven challenge-seam `evalDist` transfers `evalDist_run'_challengeSeam_left/right`
(`AppendSoundnessSeamTransfer.lean`), assembling the final
`Reduction.append_completeness_msg`.

## What is proven here (no `sorry`)

* `appendStage1Bridge` — discharges `hStage1Bridge`: the `Prod.fst`-marginal of the state-threaded
  phase-1 stage game (`appendStage₁`, run under the *combined* challenge oracle) has the same
  `evalDist` as `gameOf R₁` (run under `pSpec₁`'s own challenge oracle). Chains
  `appendStage₁_run_eq_liftM` with `evalDist_run'_challengeSeam_left`.

* `appendStage2Bridge` — discharges `hStage2Bridge`: for each phase-1 success `a` with `goodOf rel₂ a`
  (so the merge `a.1.2.1 = a.2` holds), the phase-2 stage game's bad event (over the *combined*
  transcript) equals the phase-2 completeness game's bad event (over `pSpec₂`'s transcript) on the
  intermediate pair. The completeness `goodOf` predicate reads only the statement/witness/output
  marginals — never the merged transcript — so the transcript merge is invisible, and
  `appendStage₂_run_eq_liftM` + `evalDist_run'_challengeSeam_right` reconcile the runs distributionally.

* `append_game_neverFail` — discharges `hTot`: the appended game never *samples* a failure, via
  `simulateQ_run_neverFail` / `addLift_neverFail` (the honest interactive implementation never fails)
  and the non-failing initializer `init`.

* `append_completeness_msg` — feeds the three discharged residuals to
  `append_completeness_msg_via_seamFactor`, concluding `(R₁.append R₂).completeness init impl rel₁ rel₃
  (e₁ + e₂)` from the component completenesses plus the honest-implementation side conditions.
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

/-! ### Stage-1 challenge-seam bridge (discharges `hStage1Bridge`) -/

/-- **Discharged `hStage1Bridge`.** The `Prod.fst`-marginal of the state-threaded phase-1 stage game
(`appendStage₁`, run under the *combined* challenge oracle `[(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ`) has
the same `evalDist` as the phase-1 completeness game `gameOf R₁` (run under `pSpec₁`'s own challenge
oracle). Proof: `appendStage₁_run_eq_liftM` rewrites the stage-1 `OptionT.run` to `liftM` of
`(R₁.run …).run`; the `Prod.fst <$> (init >>= …)` then pushes through `init`-bind to a per-`s`
`run'`, where the proven challenge-seam transfer `evalDist_run'_challengeSeam_left` reconciles the
combined-oracle run with `pSpec₁`'s own-oracle run — which is exactly `gameOf R₁`'s body. -/
theorem appendStage1Bridge
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (stmt : Stmt₁) (wit : Wit₁) :
    evalDist (Prod.fst <$> (init >>= fun s =>
        StateT.run (simulateQ (impl.addLift challengeQueryImpl)
          (OptionT.run (appendStage₁ R₁ R₂ stmt wit))) s))
      = evalDist (gameOf init impl R₁ stmt wit) := by
  rw [appendStage₁_run_eq_liftM R₁ R₂ stmt wit]
  -- Push `Prod.fst <$>` through the `init` bind into a per-`s` `run'`.
  rw [map_bind]
  simp only [← StateT.run'_eq]
  -- `gameOf` unfolds to `init >>= fun s => (…).run' s`.
  show evalDist (init >>= fun s =>
      Prod.fst <$> StateT.run (simulateQ (impl.addLift challengeQueryImpl)
        (liftM (OptionT.run (R₁.run stmt wit)))) s)
    = evalDist (init >>= fun s =>
        StateT.run' (simulateQ (impl.addLift challengeQueryImpl)
          (OptionT.run (R₁.run stmt wit))) s)
  simp only [← StateT.run'_eq]
  -- Per-`s` challenge-seam transfer (left half).
  rw [evalDist_bind, evalDist_bind]
  refine congrArg (fun d => (evalDist init) >>= d) ?_
  funext s
  exact OracleReduction.evalDist_run'_challengeSeam_left impl (OptionT.run (R₁.run stmt wit)) s

/-! ### Game totality (discharges `hTot`) -/

/-- **Discharged `hTot`.** The appended simulated honest game never *samples* a failure: its only
failure mode is the explicit `none` output (folded into the bad event). With a non-failing
initializer `init`, the bind `init >>= fun s => (…).run' s` is failure-free by
`simulateQ_run_neverFail` (the honest interactive implementation `impl.addLift challengeQueryImpl`
never fails, `addLift_neverFail`). -/
theorem append_game_neverFail
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (stmt : Stmt₁) (wit : Wit₁)
    (hInit : Pr[⊥ | init] = 0)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0) :
    Pr[⊥ | gameOf init impl (R₁.append R₂) stmt wit] = 0 := by
  show Pr[⊥ | init >>= fun s =>
      StateT.run' (simulateQ (impl.addLift challengeQueryImpl)
        (OptionT.run ((R₁.append R₂).run stmt wit))) s] = 0
  rw [probFailure_bind_eq_add_tsum, hInit, zero_add, ENNReal.tsum_eq_zero]
  intro s
  rw [mul_eq_zero]
  right
  rw [StateT.run'_eq, probFailure_map]
  exact simulateQ_run_neverFail _ (addLift_neverFail impl himplNF) _ s

/-! ### Stage-2 challenge-seam bridge (discharges `hStage2Bridge`) -/

/-- **The combined-transcript bad event is invisible to the transcript merge.** For any phase-2
output `r`, the completeness `goodOf` predicate over the *combined* transcript, evaluated on the
transcript-merge image `((a.1.1 ++ₜ r.1.1, r.1.2.1, r.1.2.2), r.2)`, agrees with the phase-2
`goodOf` predicate over `pSpec₂`'s transcript on `r`: `goodOf` reads only the statement
(`r.2`), witness (`r.1.2.2`), and the prover/verifier statement agreement (`r.1.2.1 = r.2`) — never
the transcript component (`.1.1`), which is the only field the merge touches. -/
private theorem goodOf_merge_eq
    (a : (FullTranscript pSpec₁ × Stmt₂ × Wit₂) × Stmt₂)
    (r : (FullTranscript pSpec₂ × Stmt₃ × Wit₃) × Stmt₃) :
    goodOf (m + n) (pSpec₁ ++ₚ pSpec₂) rel₃
        ((a.1.1 ++ₜ r.1.1, r.1.2.1, r.1.2.2), r.2)
      = goodOf n pSpec₂ rel₃ r :=
  rfl

/-- **Discharged `hStage2Bridge`.** For each phase-1 success `a` with `goodOf rel₂ a` (which supplies
the merge agreement `a.1.2.1 = a.2`), the phase-2 stage game's bad event over the *combined*
transcript equals — hence is bounded by — the phase-2 completeness game's bad event over `pSpec₂`'s
transcript on the intermediate pair `(a.2, a.1.2.2)`.

Proof: `appendStage₂_run_eq_liftM` rewrites the stage-2 `OptionT.run` to `liftM` of the
transcript-merge-postcomposed `(R₂.run a.2 a.1.2.2).run`; the proven challenge-seam transfer
`evalDist_run'_challengeSeam_right` reconciles the combined-oracle run with `pSpec₂`'s own-oracle run;
the merge `<$>` is pushed out as an `Option.map` post-map (`probEvent_map`), and
`goodOf_merge_eq` collapses the combined `goodOf ∘ merge` to the phase-2 `goodOf`. The resulting
`s'`-pinned phase-2 game has the same bad probability as the `init`-averaged completeness game
`gameOf R₂` by state-independence (`evalDist_simulateQ_run'_state_indep` with the honest
implementation's state-preservation `himplSP` and value-blindness `himplVB`). -/
theorem appendStage2Bridge
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (stmt : Stmt₁) (wit : Wit₁)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplVB : ∀ (t : oSpec.Domain) (s s' : σ),
      evalDist ((impl t).run' s) = evalDist ((impl t).run' s'))
    (a : (FullTranscript pSpec₁ × Stmt₂ × Wit₂) × Stmt₂) (s' : σ)
    (hgood : goodOf m pSpec₁ rel₂ a) :
    Pr[fun o => ¬ Option.elim o False (goodOf (m + n) (pSpec₁ ++ₚ pSpec₂) rel₃ ·)
        | (StateT.run' (simulateQ (impl.addLift challengeQueryImpl)
            (OptionT.run (appendStage₂ R₁ R₂ a))) s' : ProbComp (Option _))]
      ≤ Pr[fun o => ¬ Option.elim o False (goodOf n pSpec₂ rel₃ ·)
        | gameOf init impl R₂ a.2 a.1.2.2] := by
  -- `goodOf` supplies the transcript-merge agreement `a.1.2.1 = a.2`.
  have hag : a.1.2.1 = a.2 := hgood.2
  -- The merge post-map, as a plain function on phase-2 outputs.
  set merge : (FullTranscript pSpec₂ × Stmt₃ × Wit₃) × Stmt₃ →
      (FullTranscript (pSpec₁ ++ₚ pSpec₂) × Stmt₃ × Wit₃) × Stmt₃ :=
    fun r => ((a.1.1 ++ₜ r.1.1, r.1.2.1, r.1.2.2), r.2) with hmerge
  -- Step 1: rewrite the stage-2 `OptionT.run` to `liftM` of the merge-postcomposed `R₂.run`.
  rw [appendStage₂_run_eq_liftM R₁ R₂ a hag]
  -- Step 2: pin the per-`s'` LHS to the `init`-averaged phase-2 completeness game `gameOf R₂`.
  -- First, transfer the combined challenge oracle to `pSpec₂`'s own oracle, then collapse the merge.
  -- The merge-postcomposed phase-2 run (over `pSpec₂`'s own oracle), and its lift to the combined one.
  set Ymerge : OptionT (OracleComp (oSpec + [pSpec₂.Challenge]ₒ)) _ :=
    merge <$> R₂.run a.2 a.1.2.2 with hYmerge
  set Ylift : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (Option _) :=
    liftM (OptionT.run Ymerge) with hYlift
  have hLHS :
      Pr[fun o => ¬ Option.elim o False (goodOf (m + n) (pSpec₁ ++ₚ pSpec₂) rel₃ ·)
          | (StateT.run' (simulateQ (impl.addLift
              (challengeQueryImpl (pSpec := pSpec₁ ++ₚ pSpec₂))) Ylift) s' : ProbComp (Option _))]
        = Pr[fun o => ¬ Option.elim o False (goodOf n pSpec₂ rel₃ ·)
          | (StateT.run' (simulateQ (impl.addLift
              (challengeQueryImpl (pSpec := pSpec₂)))
              (OptionT.run (R₂.run a.2 a.1.2.2))) s' : ProbComp (Option _))] := by
    -- Challenge-seam transfer (right half): combined → pSpec₂ own oracle, at `probEvent`.
    have hed := OracleReduction.evalDist_run'_challengeSeam_right (pSpec₁ := pSpec₁)
      impl (OptionT.run Ymerge) s'
    rw [hYlift]
    -- Step A: transfer the bad event from the combined-oracle game to the `pSpec₂`-own-oracle game on
    -- the merge-postcomposed run, using `hed` at the distribution level.
    have hA : Pr[fun o => ¬ Option.elim o False (goodOf (m + n) (pSpec₁ ++ₚ pSpec₂) rel₃ ·)
          | (StateT.run' (simulateQ (impl.addLift
              (challengeQueryImpl (pSpec := pSpec₁ ++ₚ pSpec₂)))
              (liftM (OptionT.run Ymerge))) s' : ProbComp (Option _))]
        = Pr[fun o => ¬ Option.elim o False (goodOf (m + n) (pSpec₁ ++ₚ pSpec₂) rel₃ ·)
          | (StateT.run' (simulateQ (impl.addLift
              (challengeQueryImpl (pSpec := pSpec₂))) (OptionT.run Ymerge)) s'
            : ProbComp (Option _))] := by
      unfold probEvent; rw [hed]
    -- Step B: push the merge `<$>` out as an `Option.map` post-map and collapse via `goodOf_merge_eq`.
    refine hA.trans ?_
    -- The merge-postcomposed game's distribution is `Option.map merge <$>` the bare phase-2 game.
    have hdist : (StateT.run' (simulateQ (impl.addLift
            (challengeQueryImpl (pSpec := pSpec₂))) (OptionT.run Ymerge)) s' : ProbComp (Option _))
        = (Option.map merge <$> StateT.run' (simulateQ (impl.addLift
            (challengeQueryImpl (pSpec := pSpec₂))) (OptionT.run (R₂.run a.2 a.1.2.2))) s'
          : ProbComp (Option _)) := by
      rw [hYmerge, OptionT.run_map, simulateQ_map, StateT.run'_eq, StateT.run_map, StateT.run'_eq,
        Functor.map_map, Functor.map_map]
    rw [hdist, probEvent_map]
    refine probEvent_congr' (fun o _ => ?_) rfl
    cases o with
    | none => rfl
    | some r =>
      simp only [Function.comp_apply, Option.map_some, Option.elim_some, hmerge,
        goodOf_merge_eq a r]
  rw [hLHS]
  -- Step 3: drop `init` from `gameOf R₂` by state-independence, pinning to `s'`.
  refine le_of_eq ?_
  show Pr[fun o => ¬ Option.elim o False (goodOf n pSpec₂ rel₃ ·)
        | (StateT.run' (simulateQ (impl.addLift challengeQueryImpl)
            (OptionT.run (R₂.run a.2 a.1.2.2))) s' : ProbComp (Option _))]
    = Pr[fun o => ¬ Option.elim o False (goodOf n pSpec₂ rel₃ ·)
        | init >>= fun s => StateT.run' (simulateQ (impl.addLift challengeQueryImpl)
            (OptionT.run (R₂.run a.2 a.1.2.2))) s]
  have hed : evalDist (init >>= fun s => StateT.run' (simulateQ (impl.addLift challengeQueryImpl)
          (OptionT.run (R₂.run a.2 a.1.2.2))) s)
      = evalDist (init >>= fun _ => StateT.run' (simulateQ (impl.addLift challengeQueryImpl)
          (OptionT.run (R₂.run a.2 a.1.2.2))) s') := by
    rw [evalDist_bind, evalDist_bind]
    refine bind_congr fun s => ?_
    exact evalDist_simulateQ_run'_state_indep _ (addLift_state_preserving impl himplSP)
      (addLift_value_blind impl himplVB) _ s s'
  rw [show Pr[fun o => ¬ Option.elim o False (goodOf n pSpec₂ rel₃ ·)
        | init >>= fun s => StateT.run' (simulateQ (impl.addLift challengeQueryImpl)
            (OptionT.run (R₂.run a.2 a.1.2.2))) s]
      = Pr[fun o => ¬ Option.elim o False (goodOf n pSpec₂ rel₃ ·)
        | init >>= fun _ => StateT.run' (simulateQ (impl.addLift challengeQueryImpl)
            (OptionT.run (R₂.run a.2 a.1.2.2))) s'] from by unfold probEvent; rw [hed]]
  rw [probEvent_bind_const, probFailure_eq_zero, tsub_zero, one_mul]

/-! ### Assembled non-perfect message-seam append completeness -/

/-- **Non-perfect (error-bearing) message-seam append completeness — fully discharged.**

From the component completenesses `h₁ : R₁.completeness … e₁` and `h₂ : R₂.completeness … e₂`, the
appended reduction `R₁.append R₂` is complete with the additive error `e₁ + e₂`. This feeds the three
challenge-seam residuals — discharged here as `appendStage1Bridge` (`hStage1Bridge`),
`appendStage2Bridge` (`hStage2Bridge`), and `append_game_neverFail` (`hTot`) — into the proven
`append_completeness_msg_via_seamFactor` (whose `hGameFactor` distributional run-factoring is itself
already proven by `append_game_factor_msg`).

The side conditions are exactly those any honest interactive implementation satisfies and that the
downstream sequential-composition consumers already supply: `hInit` (the initializer never fails) and
the state-preserving / never-failing / value-blind triple `himplSP` / `himplNF` / `himplVB` on `impl`
(vacuous when `oSpec = []ₒ`). They are the completeness analogues of the soundness append's
side conditions (`Verifier.append_soundness_msg`). -/
theorem append_completeness_msg
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    {e₁ e₂ : ℝ≥0}
    (h₁ : R₁.completeness init impl rel₁ rel₂ e₁)
    (h₂ : R₂.completeness init impl rel₂ rel₃ e₂)
    (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .P_to_V)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .P_to_V)
    (hInit : Pr[⊥ | init] = 0)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    (himplVB : ∀ (t : oSpec.Domain) (s s' : σ),
      evalDist ((impl t).run' s) = evalDist ((impl t).run' s')) :
    (R₁.append R₂).completeness init impl rel₁ rel₃ (e₁ + e₂) :=
  append_completeness_msg_via_seamFactor R₁ R₂ h₁ h₂ hn hDir hDir₂ himplSP himplNF
    (fun stmt wit _ => appendStage1Bridge R₁ R₂ stmt wit)
    (fun stmt wit _ a _ _ hgood => appendStage2Bridge R₁ R₂ stmt wit himplSP himplVB a _ hgood)
    (fun stmt wit _ => append_game_neverFail R₁ R₂ stmt wit hInit himplNF)

end Reduction
