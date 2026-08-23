/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.AppendPerfectCompletenessProof
import ArkLib.OracleReduction.Composition.Sequential.SeamCompleteness

/-!
# Non-perfect (error-bearing) message-seam append completeness — discharged

This file proves `Reduction.append_completeness_msg_proof`, the **error-bearing** Reduction-level
append completeness for a *message seam*: from
`R₁.completeness init impl rel₁ rel₂ e₁` and `R₂.completeness init impl rel₂ rel₃ e₂`, it concludes
`(R₁.append R₂).completeness init impl rel₁ rel₃ (e₁ + e₂)`.

It is the additive-error generalization of the perfect (`e₁ = e₂ = 0`) keystone
`Reduction.append_perfectCompleteness_msg_proof`. Where the perfect proof reads completeness as the
*support* statement `Pr[good] = 1` (`probEvent_eq_one_iff`) and decomposes the appended support at
the seam, the error-bearing statement is genuinely probabilistic: completeness is the *bound*
`Pr[good] ≥ 1 - e`, equivalently `Pr[bad] ≤ e` on the simulated honest game (`bad` = failure **or**
`¬ good`, the completeness failure convention — `none` is bad). The combination is the standard
**two-stage success-probability union bound**

  `Pr[append fails] ≤ Pr[stage-1 fails] + Pr[stage-2 fails] ≤ e₁ + e₂`,

discharged by the proven `OracleReduction.probComp_seam_completeness` (in `SeamCompleteness.lean`)
once the appended honest game is factored at the seam into `stage₁ ; stage₂ = R₁.run ; R₂.run`.

## Structure of the proof

`OracleReduction.completenessFromRun_of_bad_le` reduces the completeness *bound* to two run-level
obligations on the simulated honest game `game₃ stmt wit`:

* `hbad`: `Pr[bad₃ | game₃] ≤ e₁ + e₂`;
* `htot`: `Pr[⊥ | game₃] = 0` (the simulated game never *samples* a failure — its only failure mode
  is the explicit `none` output, which is folded into `bad₃`).

Both obligations are read off the seam-factored game via `probComp_seam_completeness`. The
genuinely-deep content — the *distributional* factoring of the simulated appended honest game at the
seam into the two stages in exactly the `mx >>= my` shape `probComp_seam_completeness` consumes — is
isolated as the single named hypothesis `hGameFactor` (per-input). It is the simulated-game form of
the proven prover/verifier run factoring `Prover.append_run_evalDist_msg` + `Verifier.append_run`;
the per-stage bad-event bounds `e₁`/`e₂` and the totality are then obtained mechanically from
`h₁`/`h₂` (via `Verifier.StateFunction.probEvent_optionT_mk_eq_elim` + `probEvent_compl`).
-/

open OracleComp OracleSpec ProtocolSpec
open scoped ENNReal NNReal

namespace Reduction

variable {ι : Type} {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited]
  {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}

/-- **`Pr[good | OptionT.mk ma] ≥ 1 - e ⟹ Pr[bad | ma] ≤ e` (completeness convention).** The
converse of `OracleReduction.probEvent_optionT_mk_ge_of_bad_le`: a completeness *lower bound*
`Pr[good] ≥ 1 - e` on the `OptionT.mk` view yields a *bad-event upper bound* `Pr[bad] ≤ e` on the
underlying `ProbComp`, where `bad o := ¬ Option.elim o False good` (failure `none` **or** `¬ good`).
Valid for any game; it does not need totality, since the `none` failure mass only *helps* the `≤ e`
direction. This is the bridge that turns the per-phase `completeness` hypotheses into the per-stage
bad-event bounds the seam union bound `OracleReduction.probComp_seam_completeness` consumes. -/
theorem bad_le_of_optionT_mk_ge {α : Type} (ma : ProbComp (Option α))
    (good : α → Prop) (e : ℝ≥0∞)
    (hge : Pr[good | (OptionT.mk ma : OptionT ProbComp α)] ≥ 1 - e) :
    Pr[fun o => ¬ Option.elim o False good | ma] ≤ e := by
  classical
  rw [Verifier.StateFunction.probEvent_optionT_mk_eq_elim] at hge
  -- complement identity: `Pr[elim good] + Pr[¬ elim good] = 1 - Pr[⊥] ≤ 1`.
  have hc := probEvent_compl ma (fun o => Option.elim o False good)
  have hsum_le : Pr[fun o => Option.elim o False good | ma]
      + Pr[fun o => ¬ Option.elim o False good | ma] ≤ 1 := hc.le.trans tsub_le_self
  -- `Pr[¬ elim good] ≤ 1 - Pr[elim good] ≤ 1 - (1 - e) ≤ e`.
  have hfin : (1 : ℝ≥0∞) - (1 - e) ≤ e := by
    rw [tsub_le_iff_right]; exact le_tsub_add.trans (by rw [add_comm])
  calc Pr[fun o => ¬ Option.elim o False good | ma]
      ≤ 1 - Pr[fun o => Option.elim o False good | ma] :=
        ENNReal.le_sub_of_add_le_left
          (ne_top_of_le_ne_top ENNReal.one_ne_top probEvent_le_one) hsum_le
    _ ≤ 1 - (1 - e) := by gcongr
    _ ≤ e := hfin

/-- Abbreviation for the simulated honest game of a reduction `R` on `(stmt, wit)`: the underlying
`ProbComp (Option _)` whose `OptionT.mk` view appears in `R.completeness`. The bad-event/failure
probabilities of completeness are read off this game. -/
abbrev gameOf {StmtIn WitIn StmtOut WitOut : Type} {N : ℕ} {pSpec : ProtocolSpec N}
    [∀ i, SampleableType (pSpec.Challenge i)]
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn) :
    ProbComp (Option ((FullTranscript pSpec × StmtOut × WitOut) × StmtOut)) :=
  (do ((simulateQ (impl.addLift challengeQueryImpl) (R.run stmt wit).run :
        StateT σ ProbComp _).run' (← init)))

/-- The completeness "good" predicate of a reduction (output relation membership plus
prover/verifier statement agreement). The transcript-type parameter `N`/`pSpec` is explicit so the
predicate's domain is determined even in `Option.elim`/`·` positions. -/
def goodOf {StmtOut WitOut : Type} (N : ℕ) (pSpec : ProtocolSpec N)
    (relOut : Set (StmtOut × WitOut)) :
    (FullTranscript pSpec × StmtOut × WitOut) × StmtOut → Prop :=
  fun r => (r.2, r.1.2.2) ∈ relOut ∧ r.1.2.1 = r.2

omit [oSpec.Fintype] [oSpec.Inhabited] in
/-- **NON-PERFECT (error-bearing) message-seam append completeness — discharged modulo the named
two-stage seam factoring.**

From the component completenesses `h₁ : R₁.completeness … e₁` and `h₂ : R₂.completeness … e₂`, the
appended reduction is complete with the additive error `e₁ + e₂`. The proof is the standard
two-stage success-probability union bound, discharged by the proven
`OracleReduction.probComp_seam_completeness`:

* the appended simulated honest game factors at the (message) seam as the two-stage game
  `init >>= fun s => (simulateQ so (mx >>= my).run).run' s` — the genuinely-deep distributional
  content, taken as the named hypothesis `hGameFactor` (the simulated-game image of
  `Prover.append_run_evalDist_msg` + `Verifier.append_run`, threaded through the per-phase challenge
  oracles);
* the stage-1 bad event is `≤ e₁` (from `h₁`, named `hStage1`), and for each stage-1 success the
  stage-2 bad event is `≤ e₂` (from `h₂`, named `hStage2`); their sum is the claimed error;
* the simulated game never *samples* a failure (`hTot`), so the only failure folded into the bad
  event is the explicit `none` output.

All probability arithmetic (the union bound, the per-stage `Pr[bad] ≤ e` conversion from the
component completenesses `h₁`/`h₂`, and the `Pr[good] ≥ 1 - e` final conversion) is proven here.
The named residuals `hGameFactor`/`hStage1Bridge`/`hStage2Bridge`/`hTot` isolate exactly the deep
*distributional* run-factoring content (the simulated-game image of `Prover.append_run_evalDist_msg`
+ `Verifier.append_run`, including the per-phase challenge-oracle seam bridges), mirroring the
named-residual pattern of the perfect-case keystone
`Reduction.append_perfectCompleteness_msg_proof`. -/
theorem append_completeness_msg_proof
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    {e₁ e₂ : ℝ≥0}
    (h₁ : R₁.completeness init impl rel₁ rel₂ e₁)
    (h₂ : R₂.completeness init impl rel₂ rel₃ e₂)
    -- The deep two-stage seam factoring: the appended simulated game equals (as a distribution) the
    -- two-stage `mx >>= my` game, with `mx` the phase-1 honest run and `my` the phase-2 honest run.
    {so : QueryImpl (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
            (StateT σ ProbComp)}
    {mx : (Stmt₁ × Wit₁) →
      OptionT (OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ))
        ((FullTranscript pSpec₁ × Stmt₂ × Wit₂) × Stmt₂)}
    {my : (Stmt₁ × Wit₁) → ((FullTranscript pSpec₁ × Stmt₂ × Wit₂) × Stmt₂) →
      OptionT (OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ))
        ((FullTranscript (pSpec₁ ++ₚ pSpec₂) × Stmt₃ × Wit₃) × Stmt₃)}
    (hGameFactor : ∀ stmt wit, (stmt, wit) ∈ rel₁ →
      evalDist (gameOf init impl (R₁.append R₂) stmt wit)
        = evalDist (init >>= fun s =>
            (simulateQ so ((mx (stmt, wit)) >>= (my (stmt, wit))).run).run' s))
    -- Stage-1 evalDist bridge: the (fst-marginal of the) state-threaded phase-1 stage game is the
    -- phase-1 completeness game `gameOf R₁`. Lets `h₁` supply the stage-1 bad bound.
    (hStage1Bridge : ∀ stmt wit, (stmt, wit) ∈ rel₁ →
      evalDist (Prod.fst <$> (init >>= fun s => (simulateQ so (mx (stmt, wit)).run).run s))
        = evalDist (gameOf init impl R₁ stmt wit))
    -- Stage-2 bad-event bridge: from a phase-1 success `a` with `goodOf rel₂ a` (so its statement
    -- pair `(a.2, a.1.2.2) ∈ rel₂`), the phase-2 stage game's bad event (over the *combined*
    -- transcript) is dominated by the phase-2 completeness game's bad event (over `pSpec₂`'s
    -- transcript) on that intermediate pair — the transcript-merge is a relabeling on the
    -- statement/witness marginals the bad event examines. Lets `h₂` supply the stage-2 bad bound.
    (hStage2Bridge : ∀ stmt wit, (stmt, wit) ∈ rel₁ →
      ∀ a s', (some a, s') ∈ support
            (init >>= fun s => (simulateQ so (mx (stmt, wit)).run).run s) →
          goodOf m pSpec₁ rel₂ a →
          Pr[fun o => ¬ Option.elim o False (goodOf (m + n) (pSpec₁ ++ₚ pSpec₂) rel₃ ·)
              | (simulateQ so (my (stmt, wit) a).run).run' s']
            ≤ Pr[fun o => ¬ Option.elim o False (goodOf n pSpec₂ rel₃ ·)
              | gameOf init impl R₂ a.2 a.1.2.2])
    (hTot : ∀ stmt wit, (stmt, wit) ∈ rel₁ →
      Pr[⊥ | gameOf init impl (R₁.append R₂) stmt wit] = 0) :
    (R₁.append R₂).completeness init impl rel₁ rel₃ (e₁ + e₂) := by
  classical
  -- Stage-1 bad bound from `h₁`, transported across the stage-1 bridge.
  have hStage1 : ∀ stmt wit, (stmt, wit) ∈ rel₁ →
      Pr[fun r => ¬ Option.elim r.1 False (goodOf m pSpec₁ rel₂ ·)
          | init >>= fun s => (simulateQ so (mx (stmt, wit)).run).run s] ≤ (e₁ : ℝ≥0∞) := by
    intro stmt wit hRel
    -- bad event sees only the `.1` (option) projection, so it factors through `Prod.fst`.
    have hmap : Pr[fun r : Option _ × σ => ¬ Option.elim r.1 False (goodOf m pSpec₁ rel₂ ·)
          | init >>= fun s => (simulateQ so (mx (stmt, wit)).run).run s]
        = Pr[fun o => ¬ Option.elim o False (goodOf m pSpec₁ rel₂ ·)
          | Prod.fst <$> (init >>= fun s => (simulateQ so (mx (stmt, wit)).run).run s)] := by
      rw [probEvent_map]; rfl
    rw [hmap]
    have hbad₁ := bad_le_of_optionT_mk_ge (gameOf init impl R₁ stmt wit)
      (goodOf m pSpec₁ rel₂) (e₁ : ℝ≥0∞) (h₁ stmt wit hRel)
    calc Pr[fun o => ¬ Option.elim o False (goodOf m pSpec₁ rel₂ ·)
              | Prod.fst <$> (init >>= fun s => (simulateQ so (mx (stmt, wit)).run).run s)]
        = Pr[fun o => ¬ Option.elim o False (goodOf m pSpec₁ rel₂ ·)
              | gameOf init impl R₁ stmt wit] := by
          simp only [probEvent, hStage1Bridge stmt wit hRel]
      _ ≤ (e₁ : ℝ≥0∞) := hbad₁
  -- Stage-2 bad bound from `h₂`, transported across the stage-2 bridge.
  have hStage2 : ∀ stmt wit, (stmt, wit) ∈ rel₁ →
      ∀ a s', (some a, s') ∈ support
            (init >>= fun s => (simulateQ so (mx (stmt, wit)).run).run s) →
          goodOf m pSpec₁ rel₂ a →
          Pr[fun o => ¬ Option.elim o False (goodOf (m + n) (pSpec₁ ++ₚ pSpec₂) rel₃ ·)
              | (simulateQ so (my (stmt, wit) a).run).run' s'] ≤ (e₂ : ℝ≥0∞) := by
    intro stmt wit hRel a s' hsupp hgood₂
    -- `goodOf rel₂ a` gives the intermediate statement-witness pair in `rel₂`.
    have hmem₂ : (a.2, a.1.2.2) ∈ rel₂ := hgood₂.1
    have hbad₂ := bad_le_of_optionT_mk_ge (gameOf init impl R₂ a.2 a.1.2.2)
      (goodOf n pSpec₂ rel₃) (e₂ : ℝ≥0∞) (h₂ a.2 a.1.2.2 hmem₂)
    exact (hStage2Bridge stmt wit hRel a s' hsupp hgood₂).trans hbad₂
  -- Combine via the two-stage seam union bound.
  refine OracleReduction.completenessFromRun_of_bad_le init
    (impl.addLift challengeQueryImpl) rel₁ rel₃ (R₁.append R₂).run (e₁ + e₂) ?_ ?_
  · intro stmt wit hRel
    have hpe : Pr[fun o => ¬ Option.elim o False (goodOf (m + n) (pSpec₁ ++ₚ pSpec₂) rel₃ ·)
          | gameOf init impl (R₁.append R₂) stmt wit]
        = Pr[fun o => ¬ Option.elim o False (goodOf (m + n) (pSpec₁ ++ₚ pSpec₂) rel₃ ·)
          | init >>= fun s =>
              (simulateQ so ((mx (stmt, wit)) >>= (my (stmt, wit))).run).run' s] := by
      simp only [probEvent, hGameFactor stmt wit hRel]
    have hunion := OracleReduction.probComp_seam_completeness init so
      (mx (stmt, wit)) (my (stmt, wit))
      (goodOf m pSpec₁ rel₂)
      (goodOf (m + n) (pSpec₁ ++ₚ pSpec₂) rel₃)
      (e₁ : ℝ≥0∞) (e₂ : ℝ≥0∞)
      (hStage1 stmt wit hRel) (hStage2 stmt wit hRel)
    calc Pr[fun o => ¬ Option.elim o False
              (fun (r : (FullTranscript (pSpec₁ ++ₚ pSpec₂) × Stmt₃ × Wit₃) × Stmt₃) =>
                (r.2, r.1.2.2) ∈ rel₃ ∧ r.1.2.1 = r.2)
            | gameOf init impl (R₁.append R₂) stmt wit]
        = Pr[fun o => ¬ Option.elim o False
              (goodOf (m + n) (pSpec₁ ++ₚ pSpec₂) rel₃ ·)
            | gameOf init impl (R₁.append R₂) stmt wit] := rfl
      _ = _ := hpe
      _ ≤ (e₁ : ℝ≥0∞) + (e₂ : ℝ≥0∞) := hunion
      _ = ((e₁ + e₂ : ℝ≥0) : ℝ≥0∞) := by push_cast; ring
  · intro stmt wit hRel
    exact hTot stmt wit hRel

end Reduction

#print axioms Reduction.bad_le_of_optionT_mk_ge
#print axioms Reduction.append_completeness_msg_proof
