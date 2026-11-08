/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ProximityPrize.Extensions.OracleReduction.Execution
import ProximityPrize.Extensions.OracleReduction.Security.Basic
import ArkLib.ToMathlib.OracleCompEvalDistBindComm
import ProximityPrize.Compatibility.StatePreservingSimulation
import ProximityPrize.Compatibility.DiscreteProbability

/-!
# Unrolled-run form of a reduction, and the ε-completeness characterization

`Reduction.run` is, by construction, "run the prover, then run the verifier". This file exposes the
*unrolled* form — run the prover round-by-round to the last round (`Prover.runToRound (Fin.last n)`),
extract the prover output, then run the verifier — as a plain monadic equality
(`Reduction.run_eq_unrolled`), and rewrites the (general, error-`ε`) completeness predicate through
it (`Reduction.completeness_iff_run_unrolled`).

This is the **`ε`-analogue** of the perfect-completeness unrolling
`unroll_n_message_reduction_perfectCompleteness` (`OracleReduction/Completeness.lean`): the perfect
version converts `Pr[…] = 1` into a *support*-level pure-logic statement (using `NeverFail` + the
implementation support condition), which is only valid at error `0`. The version here keeps the
`simulateQ`/`init` layer intact and merely exposes the round-by-round prover structure, so it applies
at any error `ε` — the form needed to then compute a protocol-specific acceptance probability (e.g.
the LogUp outer-phase pole-rejection bound) without first collapsing to `Pr = 1`.
-/

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal ENNReal

namespace Reduction

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type}

omit [∀ i, SampleableType (pSpec.Challenge i)] in
/-- **Unrolled form of `Reduction.run`.** Running a reduction equals: run the prover round-by-round
to the last round (`runToRound (Fin.last n)`), `liftComp` the prover's output extraction, run the
verifier on the produced transcript, and pair the prover output with the verifier's (extracted)
output statement. A plain monadic equality, independent of any probability assumptions. -/
theorem run_eq_unrolled (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn) :
    reduction.run stmt wit
      = (do
          let ⟨tr, st⟩ ← reduction.prover.runToRound (Fin.last n) stmt wit
          let out ← liftComp (reduction.prover.output st) (oSpec + [pSpec.Challenge]ₒ)
          let vStmt ← liftM (reduction.verifier.run stmt tr).run
          return ((tr, out), ← vStmt.getM)) := by
  unfold Reduction.run Prover.run
  simp only [bind_assoc, liftM_bind, bind_pure_comp, OracleComp.liftComp_eq_liftM,
    liftM_map, bind_map_left]

/-- **`ε`-completeness via the unrolled run.** The general (error-`ε`) completeness predicate of a
reduction is equivalent to the same acceptance-probability bound stated over the *unrolled* run
(prover-to-last-round, output, verifier). Obtained by rewriting `Reduction.run` through
`run_eq_unrolled` inside `completenessFromRun`; the `simulateQ`/`init` execution layer is preserved,
so this holds at every error `ε` (unlike the perfect-only support-collapsing unroll). -/
theorem completeness_iff_run_unrolled
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (completenessError : ℝ≥0) :
    reduction.completeness init impl relIn relOut completenessError ↔
      completenessFromRun init (QueryImpl.addLift impl challengeQueryImpl) relIn relOut
        (fun stmtIn witIn => (do
          let ⟨tr, st⟩ ← reduction.prover.runToRound (Fin.last n) stmtIn witIn
          let out ← liftComp (reduction.prover.output st) (oSpec + [pSpec.Challenge]ₒ)
          let vStmt ← liftM (reduction.verifier.run stmtIn tr).run
          return ((tr, out), ← vStmt.getM) :
            OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ))
              ((FullTranscript pSpec × StmtOut × WitOut) × StmtOut)))
        completenessError := by
  unfold Reduction.completeness completenessFromRun
  simp only [run_eq_unrolled]

#print axioms run_eq_unrolled
#print axioms completeness_iff_run_unrolled

end Reduction

/-! ## Challenge-coherence for the standard interactive challenge oracle

The honest interactive execution answers the verifier's `getChallenge` queries with fresh uniform
samples (`challengeQueryImpl`), routed through `QueryImpl.addLift impl challengeQueryImpl` together
with the shared-oracle implementation `impl`. The two lemmas below push that challenge sampling out
of `simulateQ … |>.run'`, exposing the challenge as a `uniformSample`. This is the reusable
"FS-class" coherence step that downstream completeness/soundness probability computations need (e.g.
the LogUp outer-phase pole event depends only on the sampled challenge `x`). -/

namespace ChallengeCoherence

variable {ι : Type} {oSpec : OracleSpec ι} {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, SampleableType (pSpec.Challenge i)] {σ β : Type}

/-- Simulating a single (lifted) `getChallenge i` under `QueryImpl.addLift impl challengeQueryImpl`
collapses to the lifted uniform sampler `liftM ($ᵗ pSpec.Challenge i)`: the challenge oracle ignores
the shared-oracle implementation and samples uniformly. -/
theorem simulateQ_addLift_getChallenge
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (i : pSpec.ChallengeIdx) :
    (simulateQ (QueryImpl.addLift impl challengeQueryImpl :
        QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp))
        (liftM (getChallenge pSpec i) :
          OracleComp (oSpec + [pSpec.Challenge]ₒ) (pSpec.Challenge i)))
      = (liftM ($ᵗ pSpec.Challenge i) : StateT σ ProbComp (pSpec.Challenge i)) := by
  rw [← OracleComp.liftComp_eq_liftM (mx := getChallenge pSpec i), QueryImpl.addLift]
  rw [QueryImpl.simulateQ_liftComp_right_eq_of_apply
        (QueryImpl.liftTarget (StateT σ ProbComp) impl
          + QueryImpl.liftTarget (StateT σ ProbComp) challengeQueryImpl)
        (QueryImpl.liftTarget (StateT σ ProbComp) challengeQueryImpl)
        (fun t => by rw [QueryImpl.add_apply_inr])]
  show simulateQ (QueryImpl.liftTarget (StateT σ ProbComp) challengeQueryImpl)
      (liftM (([pSpec.Challenge]ₒ).query ⟨i, ()⟩)) = _
  rw [simulateQ_spec_query, QueryImpl.liftTarget_apply]
  rfl

/-- **Challenge-coherence bind-exposure brick.** Running, under `simulateQ (addLift impl
challengeQueryImpl)` with state `s`, a `getChallenge`-then-`k` computation equals: sample the
challenge uniformly, then run `k` from the *same* state `s`. (The challenge oracle samples uniformly
and leaves the `σ`-state untouched.) This exposes the verifier's fresh challenge as a
`uniformSample` for probability computations — the reusable FS-class coherence step. -/
theorem run'_simulateQ_addLift_getChallenge_bind
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (s : σ)
    (i : pSpec.ChallengeIdx)
    (k : pSpec.Challenge i → OracleComp (oSpec + [pSpec.Challenge]ₒ) β) :
    (simulateQ (QueryImpl.addLift impl challengeQueryImpl :
        QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp))
        ((liftM (getChallenge pSpec i) :
            OracleComp (oSpec + [pSpec.Challenge]ₒ) (pSpec.Challenge i)) >>= k)).run' s
      = ($ᵗ pSpec.Challenge i) >>= fun c =>
          (simulateQ (QueryImpl.addLift impl challengeQueryImpl :
            QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp)) (k c)).run' s := by
  rw [simulateQ_bind, simulateQ_addLift_getChallenge]
  rw [StateT.run'_eq, StateT.run_bind, StateT.run_monadLift]
  simp only [bind_assoc, pure_bind, map_bind, StateT.run'_eq, monadLift_self]

/-- Probability form of the challenge-coherence brick: the event probability of a
`getChallenge`-then-`k` run equals the uniform average over the challenge of `k`'s event
probability. This is the form a protocol-specific completeness bound consumes when its acceptance
event depends on a verifier challenge (e.g. the LogUp outer pole event in the sampled `x`). -/
theorem probEvent_run'_simulateQ_addLift_getChallenge_bind
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (s : σ)
    (i : pSpec.ChallengeIdx)
    (k : pSpec.Challenge i → OracleComp (oSpec + [pSpec.Challenge]ₒ) β)
    (p : β → Prop) :
    probEvent (p) ((simulateQ (QueryImpl.addLift impl challengeQueryImpl :
        QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp))
        ((liftM (getChallenge pSpec i) :
            OracleComp (oSpec + [pSpec.Challenge]ₒ) (pSpec.Challenge i)) >>= k)).run' s)
      = ∑' c : pSpec.Challenge i,
          probOutput (($ᵗ pSpec.Challenge i)) (c) *
            probEvent (p) ((simulateQ (QueryImpl.addLift impl challengeQueryImpl :
              QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp)) (k c)).run' s) := by
  rw [run'_simulateQ_addLift_getChallenge_bind]
  exact prEvent_bind_eq_tsum_of_countable _ _ _

#print axioms probEvent_run'_simulateQ_addLift_getChallenge_bind

end ChallengeCoherence

/-! ## `StateT`-valued `OptionT`-bind distribution under `simulateQ`

The codebase has `OptionT.simulateQ_{bind,pure,map,…}` for *`OracleComp`-valued* implementations, but
the interactive-execution semantics (`Reduction.completeness`) simulate with `QueryImpl.addLift impl
challengeQueryImpl`, whose target is `StateT σ ProbComp`. The lemma below is the missing `StateT`-valued
analogue of `OptionT.simulateQ_bind`: it distributes `simulateQ so` over the `OptionT.run` of a bind,
threading the simulation state across the seam. It is the coherence step that lets a completeness run
of the form `mx >>= my` (prover sample → verifier check) be analyzed stage-by-stage at the `run`-level. -/

namespace OptionTStateT

variable {ι : Type} {spec : OracleSpec ι} {σ α β : Type}

/-- **`StateT`-valued `OptionT`-bind distribution under `simulateQ`.** Running `simulateQ so` (for a
`StateT σ ProbComp`-valued `so`) over `(mx >>= my).run` distributes: run the first stage threading
the state, then `Option.elim` into the second stage from the threaded state (or short-circuit to
`none`). -/
theorem simulateQ_run_optionT_bind_run
    (so : QueryImpl spec (StateT σ ProbComp))
    (mx : OptionT (OracleComp spec) α) (my : α → OptionT (OracleComp spec) β) (s : σ) :
    (simulateQ so ((mx >>= my : OptionT (OracleComp spec) β)).run).run s
      = (simulateQ so mx.run).run s >>= fun p =>
          p.1.elim (pure (none, p.2)) (fun a => (simulateQ so (my a).run).run p.2) := by
  have hrun : ((mx >>= my : OptionT (OracleComp spec) β)).run
      = mx.run >>= fun o => match o with | some a => (my a).run | none => pure none := rfl
  rw [hrun, simulateQ_bind, StateT.run_bind]
  refine bind_congr fun p => ?_
  obtain ⟨o, s'⟩ := p
  cases o with
  | none => simp [simulateQ_pure, StateT.run_pure]
  | some a => rfl

#print axioms simulateQ_run_optionT_bind_run

/-- `run'`-level analogue of `simulateQ_run_optionT_bind_run`: distributing `simulateQ so` over the
`OptionT.run` of a bind, dropping the final state (`run'`). Directly matches the soundness/completeness
game shape `(simulateQ so X.run).run' s` (used to split such a game into its two stages for a
`probEvent`/`probFailure` union bound). -/
theorem simulateQ_run'_optionT_bind_run
    (so : QueryImpl spec (StateT σ ProbComp))
    (mx : OptionT (OracleComp spec) α) (my : α → OptionT (OracleComp spec) β) (s : σ) :
    (simulateQ so ((mx >>= my : OptionT (OracleComp spec) β)).run).run' s
      = (simulateQ so mx.run).run s >>= fun p =>
          p.1.elim (pure none) (fun a => (simulateQ so (my a).run).run' p.2) := by
  rw [StateT.run'_eq, simulateQ_run_optionT_bind_run, map_bind]
  refine bind_congr fun p => ?_
  obtain ⟨o, s'⟩ := p
  cases o with
  | none => simp [StateT.run'_eq]
  | some a => simp only [Option.elim_some, StateT.run'_eq]

#print axioms simulateQ_run'_optionT_bind_run

open scoped ENNReal in
/-- **Two-stage seam union bound (`ProbComp` level).** The core union bound for sequential-composition
soundness/completeness. For the game `init >>= fun s => (simulateQ so (mx >>= my).run).run' s`: if the
stage-1 bad event (`¬ Option.elim ·.1 True pg`) on the state-threaded stage-1 run is bounded by `e₁`,
and for every stage-1 success `(some a, s')` with `pg a` the stage-2 bad event (`¬ Option.elim · True qg`)
of `my a` run from `s'` is bounded by `e₂`, then the full game's stage-2 bad event is bounded by
`e₁ + e₂`. Combines `simulateQ_run'_optionT_bind_run` (stage split) with `probEvent_bind_le_add`.
Predicates are in `¬ Option.elim · True ·` (bad-event) form; `none` (failure) is never "bad". -/
theorem probComp_seam_union_le
    (init : ProbComp σ) (so : QueryImpl spec (StateT σ ProbComp))
    (mx : OptionT (OracleComp spec) α) (my : α → OptionT (OracleComp spec) β)
    (pg : α → Prop) (qg : β → Prop) (e₁ e₂ : ℝ≥0∞)
    (h₁ : probEvent (fun r => ¬ Option.elim r.1 True pg) (init >>= fun s => (simulateQ so mx.run).run s) ≤ e₁)
    (h₂ : ∀ a s', (some a, s') ∈ support (init >>= fun s => (simulateQ so mx.run).run s) → pg a →
          probEvent (fun o => ¬ Option.elim o True qg) ((simulateQ so (my a).run).run' s') ≤ e₂) :
    probEvent (fun o => ¬ Option.elim o True qg) (init >>= fun s => (simulateQ so (mx >>= my).run).run' s) ≤ e₁ + e₂ := by
  classical
  have hgame : (init >>= fun s => (simulateQ so ((mx >>= my).run)).run' s)
      = (init >>= fun s => (simulateQ so mx.run).run s) >>= fun r =>
          r.1.elim (pure none) (fun a => (simulateQ so (my a).run).run' r.2) := by
    rw [bind_assoc]
    refine bind_congr fun s => ?_
    rw [simulateQ_run'_optionT_bind_run]
  rw [hgame]
  have hbound := prEvent_bind_le_prEvent_add_of_support
    (init >>= fun s => (simulateQ so mx.run).run s)
    (fun r => r.1.elim (pure none) (fun a => (simulateQ so (my a).run).run' r.2))
    (fun r => ¬ Option.elim r.1 True pg) (fun o => ¬ Option.elim o True qg)
    (ε := e₂) (by
      rintro ⟨o, s'⟩ hmem hp
      have hp' : Option.elim o True pg := not_not.mp hp
      cases o with
      | none => simp
      | some a => exact h₂ a s' hmem hp')
  exact hbound.trans (add_le_add h₁ le_rfl)

#print axioms probComp_seam_union_le

/-- **`.run`-to-`.run'` probEvent bridge (state projection).** `probComp_seam_union_le`'s `h₁` is stated
over the *full* `StateT` result `(simulateQ so X).run` with a predicate reading only the value component
`r.1`, whereas `Verifier.soundness` is stated over the value-only `.run'`. Since `.run' = (·.1) <$> .run`,
a predicate that ignores the state agrees on both: this lemma bridges the two, letting the seam's `h₁`/`h₂`
be discharged directly from `V₁`/`V₂.soundness`. -/
theorem probEvent_run_eq_run'_fst
    (so : QueryImpl spec (StateT σ ProbComp)) (init : ProbComp σ)
    {α : Type} (X : OracleComp spec α) (P : α → Prop) :
    probEvent (fun r => P r.1) (init >>= fun s => (simulateQ so X).run s)
      = probEvent (P) (init >>= fun s => (simulateQ so X).run' s) := by
  simp only [probEvent, StateT.run'_eq, ← map_bind, prEvent_map]

#print axioms probEvent_run_eq_run'_fst

/-- **Marginalization congruence for seam `probEvent`s.** Two `OptionT`-valued computations `X`, `Y`
that agree after projecting their value through `g` (`g <$> X = g <$> Y`) yield the *same* probability
for any event that reads only `g` of the (successful) result. This is the device that turns the seam's
phase-1 game (built over the prover's full output `(transcript, state, ())`) into `V₁.soundness`'s game
(built over `Reduction.run`, whose prover output is a dummy `Stmt₂`): both share the *verifier-output
marginal* (`Prod.snd`), so the differing — and irrelevant — prover output is averaged away. -/
theorem probEvent_simQ_run'_congr_marginal
    (so : QueryImpl spec (StateT σ ProbComp)) (init : ProbComp σ)
    (X Y : OptionT (OracleComp spec) α) (g : α → β) (q : β → Prop)
    (h : (g <$> X) = (g <$> Y)) :
    probEvent (fun o => Option.elim o False (fun a => q (g a))) (init >>= fun s => (simulateQ so X.run).run' s)
    = probEvent (fun o => Option.elim o False (fun a => q (g a))) (init >>= fun s => (simulateQ so Y.run).run' s) := by
  have h' : Option.map g <$> X.run = Option.map g <$> Y.run := by
    have := congrArg OptionT.run h
    simpa only [OptionT.run_map] using this
  have h'' : (Option.map g <$> simulateQ so X.run) = (Option.map g <$> simulateQ so Y.run) := by
    rw [← simulateQ_map, ← simulateQ_map, h']
  have key : (Option.map g <$> (init >>= fun s => (simulateQ so X.run).run' s))
           = (Option.map g <$> (init >>= fun s => (simulateQ so Y.run).run' s)) := by
    simp only [map_bind, StateT.run'_eq]
    refine bind_congr (fun s => ?_)
    have h3 := congrFun (congrArg StateT.run h'') s
    simp only [StateT.run_map] at h3
    have h4 := congrArg (fun z => Prod.fst <$> z) h3
    simp only [Functor.map_map] at h4 ⊢
    exact h4
  have hpe : (fun o : Option α => Option.elim o False (fun a => q (g a)))
      = (fun ob => Option.elim ob False q) ∘ (Option.map g) := by funext o; cases o <;> rfl
  rw [hpe]
  simpa only [probEvent, Functor.map_map, Function.comp_def] using
    congrArg (probEvent (fun ob => Option.elim ob False q)) key

#print axioms probEvent_simQ_run'_congr_marginal

/-- **Two-handler `liftComp` simulation bridge.** A computation `oa` over a *sub*-oracle `I₀` can be
either (i) lifted into a larger oracle `M₀` and simulated by a handler `h` there, or (ii) simulated
directly by a handler `h₁` on `I₀`. If the two handlers agree *per lifted query* (`hquery`), they
agree on *all* computations. This is the device that reconciles the message-seam phase-1 game — which
runs the malicious prover's `pSpec₁` half under the *combined* challenge oracle
`[(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ` (the seam factoring lifts via `OracleComp.liftComp`) — with
`V₁.soundness`, which runs it under `pSpec₁`'s own challenge oracle. The entire (cast-heavy) content
of that reconciliation is concentrated into the single hypothesis `hquery`; this lemma discharges the
free-monad induction once and for all. -/
theorem simulateQ_liftComp_run_eq_of_query
    {ιᵢ ιₘ : Type} {I₀ : OracleSpec ιᵢ} {M₀ : OracleSpec ιₘ} {σ' : Type}
    [MonadLiftT (OracleQuery I₀) (OracleQuery M₀)]
    (h : QueryImpl M₀ (StateT σ' ProbComp)) (h₁ : QueryImpl I₀ (StateT σ' ProbComp))
    (hquery : ∀ (t : I₀.Domain) (s : σ'),
      (simulateQ h (OracleComp.liftComp (liftM (I₀.query t) : OracleComp I₀ (I₀.Range t)) M₀)).run s
        = (h₁ t).run s)
    {γ : Type} (oa : OracleComp I₀ γ) (s : σ') :
    (simulateQ h (OracleComp.liftComp oa M₀)).run s = (simulateQ h₁ oa).run s := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x => simp [simulateQ_pure, StateT.run_pure, OracleComp.liftComp_pure]
  | query_bind t k ih =>
      have hq1 : simulateQ h₁ (liftM (I₀.query t) : OracleComp I₀ (I₀.Range t)) = h₁ t := by
        simp [simulateQ_query]
      rw [OracleComp.liftComp_bind, simulateQ_bind, StateT.run_bind, hquery t s,
          simulateQ_bind, StateT.run_bind, hq1]
      refine bind_congr ?_
      rintro ⟨a, s'⟩
      exact ih a s'

#print axioms simulateQ_liftComp_run_eq_of_query

/-- **`evalDist` two-handler `liftComp` simulation bridge.** The `evalDist`-level analogue of
`simulateQ_liftComp_run_eq_of_query`, needed when the per-query agreement holds only as a
*distribution* equality (e.g. the seam's challenge oracle, where the two handlers sample uniformly
from types that are equal only *propositionally* — `(pSpec₁ ++ₚ pSpec₂).Challenge (inl c) = pSpec₁.Challenge c`
— so their `SampleableType` instances differ syntactically). `probEvent` is defined through `evalDist`,
so this still feeds the downstream `probEvent` reconciliation. -/
theorem evalDistEq_simulateQ_liftComp_run_eq_of_query
    {ιᵢ ιₘ : Type} {I₀ : OracleSpec ιᵢ} {M₀ : OracleSpec ιₘ} {σ' : Type}
    [MonadLiftT (OracleQuery I₀) (OracleQuery M₀)]
    (h : QueryImpl M₀ (StateT σ' ProbComp)) (h₁ : QueryImpl I₀ (StateT σ' ProbComp))
    (hquery : ∀ (t : I₀.Domain) (s : σ'),
      (simulateQ h (OracleComp.liftComp
        (liftM (I₀.query t) : OracleComp I₀ (I₀.Range t)) M₀)).run s =ᵈ (h₁ t).run s)
    {γ : Type} (oa : OracleComp I₀ γ) (s : σ') :
    (simulateQ h (OracleComp.liftComp oa M₀)).run s =ᵈ (simulateQ h₁ oa).run s := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x => simp [simulateQ_pure, StateT.run_pure, OracleComp.liftComp_pure]
  | query_bind t k ih =>
      have hq1 : simulateQ h₁ (liftM (I₀.query t) : OracleComp I₀ (I₀.Range t)) = h₁ t := by
        simp [simulateQ_query]
      rw [OracleComp.liftComp_bind, simulateQ_bind, StateT.run_bind,
        simulateQ_bind, StateT.run_bind, hq1]
      exact (hquery t s).bind (fun p => ih p.1 p.2)

/-- Full per-query discrete distribution equality determines every output observation. -/
theorem evalDist_simulateQ_liftComp_run_eq_of_query
    {ιᵢ ιₘ : Type} {I₀ : OracleSpec ιᵢ} {M₀ : OracleSpec ιₘ} {σ' : Type}
    [MonadLiftT (OracleQuery I₀) (OracleQuery M₀)]
    (h : QueryImpl M₀ (StateT σ' ProbComp)) (h₁ : QueryImpl I₀ (StateT σ' ProbComp))
    (hquery : ∀ (t : I₀.Domain) (s : σ'),
      letI : MeasurableSpace (I₀.Range t × σ') := ⊤
      evalDist ((simulateQ h (OracleComp.liftComp
        (liftM (I₀.query t) : OracleComp I₀ (I₀.Range t)) M₀)).run s)
        = evalDist ((h₁ t).run s))
    {γ : Type} [MeasurableSpace (γ × σ')] (oa : OracleComp I₀ γ) (s : σ') :
    evalDist ((simulateQ h (OracleComp.liftComp oa M₀)).run s)
      = evalDist ((simulateQ h₁ oa).run s) := by
  apply EvalDistEq.evalDist_eq
  apply evalDistEq_simulateQ_liftComp_run_eq_of_query h h₁
  intro t s
  let : MeasurableSpace (I₀.Range t × σ') := ⊤
  exact EvalDistEq.of_evalDist_eq (hquery t s)

#print axioms evalDistEq_simulateQ_liftComp_run_eq_of_query
#print axioms evalDist_simulateQ_liftComp_run_eq_of_query

/-- **Transport of uniform sampling along a type equality.** If `α = β` (propositionally), the
uniform sample on `α`, cast to `β`, has the same distribution as the uniform sample on `β` — even
though the two `SampleableType` instances are independent. The cast is a bijection, so every output
has equal probability on both sides. This is the arithmetic kernel of the seam's challenge-oracle
restriction: `(pSpec₁ ++ₚ pSpec₂).Challenge (inl c)` and `pSpec₁.Challenge c` are equal types sampled
by distinct instances, reconciled here. -/
theorem evalDist_cast_uniformSample {α β : Type} [SampleableType α] [SampleableType β]
    [Finite α] [MeasurableSpace β]
    (h : α = β) :
    evalDist ((fun x => (h ▸ x : β)) <$> ($ᵗ α : ProbComp α)) = evalDist ($ᵗ β : ProbComp β) := by
  have hbij : Function.Bijective (fun x => (h ▸ x : β)) := by
    subst h
    exact Function.bijective_id
  exact (SampleableType.map_uniformSample_evalDistEq_of_bijective hbij).evalDist_eq

#print axioms evalDist_cast_uniformSample

/-- **Uniform sampling pushed along a bijection.** Generalizes `evalDist_cast_uniformSample` from a
type-equality cast to an arbitrary bijection `f : α → β`. For the seam's challenge-oracle restriction
this is what's actually needed: the challenge `SubSpec`'s response map (`(liftM q).cont`) is a bijection
by `LawfulSubSpec`, so the combined-oracle uniform challenge maps onto `pSpec₁`'s uniform challenge
*without* ever naming the underlying (private) `range_challenge_append_inl` cast. -/
theorem evalDist_map_bijective_uniformSample {α β : Type}
    [SampleableType α] [SampleableType β] [Finite α] [MeasurableSpace β]
    (f : α → β) (hf : Function.Bijective f) :
    evalDist (f <$> ($ᵗ α : ProbComp α)) = evalDist ($ᵗ β : ProbComp β) := by
  exact (SampleableType.map_uniformSample_evalDistEq_of_bijective hf).evalDist_eq

#print axioms evalDist_map_bijective_uniformSample

/-- **`OptionT.mk`-to-`ProbComp` `probEvent` bridge.** The soundness game is phrased as a
`probEvent` over an `OptionT ProbComp` (the verifier may reject = fail), while the union-bound
toolkit (`probComp_seam_union_le`) is stated at the bare `ProbComp` level with a `none`-as-failure
predicate. This lemma converts between them: a `probEvent` of `p` over `OptionT.mk PROG` equals the
`probEvent` over the underlying `PROG` of the lifted predicate `Option.elim · False p` (which scores
`none`/failure as `False`). This is the first wiring step of the `appendSoundness` connect: it brings
the soundness goal to the `ProbComp` level where `probComp_seam_union_le` applies. -/
theorem probEvent_optionT_mk {α : Type} (PROG : ProbComp (Option α)) (p : α → Prop) :
    probEvent (p) ((OptionT.mk PROG : OptionT ProbComp α))
      = probEvent (fun o => Option.elim o False p) (PROG) := by
  exact OptionT.prEvent_mk PROG p

#print axioms probEvent_optionT_mk

/-- **`simulateQ` of a lifted pure value is `pure (some ·)`.** Collapses the deterministic seam
"combine" stage (which just pairs the two phases' transcripts/outputs via `pure`) so that the `snd`
prover stage and the `V₁` verifier stage become adjacent — a single `evalDist_simulateQ_swap`
then suffices for the `appendSoundness` reorder. Connect brick. -/
theorem simQ_liftM_pure {ι : Type} {spec : OracleSpec ι} {γ τ : Type}
    (so : QueryImpl spec (StateT τ ProbComp)) (W : γ) :
    simulateQ so (liftM (pure W : OracleComp spec γ) : OptionT (OracleComp spec) γ).run
      = pure (some W) := by simp

/-- **`Option.elimM` on a `pure (some ·)` scrutinee reduces to the success branch.** The companion
collapse to `simQ_liftM_pure`: once the combine stage is `pure (some W)`, its `elimM` short-circuit
selects the continuation at `W`. Connect brick. -/
theorem elimM_pure_some {M : Type → Type _} [Monad M] [LawfulMonad M] {α β : Type}
    (a : α) (y : M (Option β)) (f : α → M (Option β)) :
    Option.elimM (pure (some a)) y f = f a := by
  rw [Option.elimM, pure_bind]; rfl

#print axioms simQ_liftM_pure
#print axioms elimM_pure_some

/-- **Lifted never-failing stage collapses its `Option`-elim.** A prover phase enters the seam chain
as `liftM X` for a plain (never-failing) `X : OracleComp`; running its `OptionT.run` and then
`Option.elim`-ing always takes the success branch, so the whole `liftM`/elim layer is just `X >>= k`.
This is what lets the two *prover* stages (`fst`, `snd`) be treated as plain `OracleComp` binds in the
seam swap (`evalDist_simulateQ_swap_prefix`), while the *verifier* stages keep their genuine
short-circuit. -/
theorem lift_run_elim {ι : Type} {spec : OracleSpec ι} {α β : Type}
    (X : OracleComp spec α) (k : α → OracleComp spec (Option β)) :
    ((liftM X : OptionT (OracleComp spec) α).run >>= fun o => o.elim (pure none) k)
      = X >>= k := by
  simp only [OptionT.run, OptionT.lift, OptionT.mk, liftM, monadLift, MonadLift.monadLift,
    bind_assoc, pure_bind, Option.elim]

#print axioms lift_run_elim

/-- **Never-failing stage marginalizes in a discarded-constant bind.** If `X` never fails
(`Pr[⊥|X]=0`), then running it and discarding its result to return a fixed `c` is distributionally
just `pure c` — its randomness washes out. This is the probabilistic heart of the seam elim-commute:
when the verifier `V₁` rejects (the failure branch), whether the *next* prover stage `snd` was already
run (natural order) or skipped (union-bound order) cannot change the outcome distribution, because
`snd` never fails and so marginalizes away. -/
theorem evalDist_bind_const {γ δ : Type} [MeasurableSpace δ] (X : ProbComp γ) (c : δ) (hX : probFailure (X) = 0) :
    evalDist (X >>= fun _ => (pure c : ProbComp δ)) = MeasureTheory.Measure.dirac c := by
  let : MeasurableSpace γ := ⊤
  have htotal : 𝒟[X] Set.univ = 1 := by
    rw [← prEvent_true_eq_evalDist_apply_univ]
    exact (prFail_eq_zero_iff X).mp hX
  rw [_root_.evalDist_bind_const, htotal, one_smul, evalDist_pure]

#print axioms evalDist_bind_const

/-- **`simulateQ` never fails when every query implementation never fails.** If `so` answers every
query with a never-failing `StateT σ ProbComp` computation, then simulating any `OracleComp` under `so`
never fails. This discharges the `hB` side-condition of the `appendSoundness` seam swap: the malicious
prover stage, run under the honest interactive implementation (`addLift impl challengeQueryImpl`), never
fails — provers contain no `failure`, and the challenge oracle samples uniformly. -/
theorem simulateQ_run_neverFail
    (so : QueryImpl spec (StateT σ ProbComp))
    (hnf : ∀ (t : spec.Domain) (s : σ), probFailure ((so t).run s) = 0)
    {α : Type} (X : OracleComp spec α) (s : σ) :
    probFailure ((simulateQ so X).run s) = 0 := by
  induction X using OracleComp.inductionOn generalizing s with
  | pure a => simp [probFailure, simulateQ_pure, StateT.run_pure]
  | query_bind t oa ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind]
    refine (ProximityPrize.Compatibility.prFail_bind_eq_zero_iff _ _).2 ⟨hnf t s, ?_⟩
    rintro ⟨u, s'⟩ _
    exact ih u s'

#print axioms simulateQ_run_neverFail



/-- A total `ProbComp` stage can cross an optional short-circuit under a common prefix. -/
theorem evalDistEq_elim_comm_prefix
    (so : QueryImpl spec (StateT σ ProbComp))
    (hso : ∀ (t : spec.Domain) (s : σ) (x : spec.Range t × σ),
      x ∈ support ((so t).run s) → x.2 = s)
    {α₀ γ β δ : Type}
    (PRE : OracleComp spec α₀) (mO : α₀ → OracleComp spec (Option γ))
    (Bb : α₀ → OracleComp spec β) (C : α₀ → β → γ → OracleComp spec (Option δ))
    (hB : ∀ (x : α₀) (s' : σ), probFailure ((simulateQ so (Bb x)).run s') = 0)
    (s : σ) :
    (simulateQ so (PRE >>= fun x => mO x >>= fun o => Bb x >>= fun b =>
        o.elim (pure none) (fun c => C x b c))).run' s =ᵈ
      (simulateQ so (PRE >>= fun x => mO x >>= fun o =>
        o.elim (pure none) (fun c => Bb x >>= fun b => C x b c))).run' s := by
  rw [StateT.run'_eq, StateT.run'_eq]
  have h :
      (simulateQ so (PRE >>= fun x => mO x >>= fun o => Bb x >>= fun b =>
        o.elim (pure none) (fun c => C x b c))).run s =ᵈ
      (simulateQ so (PRE >>= fun x => mO x >>= fun o =>
        o.elim (pure none) (fun c => Bb x >>= fun b => C x b c))).run s := by
    simp only [simulateQ_run_bind_state_fixed so hso]
    apply EvalDistEq.bind_right
    intro p
    apply EvalDistEq.bind_right
    intro q
    cases q.1 with
    | some c =>
      simp only [Option.elim_some, simulateQ_run_bind_state_fixed so hso]
      exact EvalDistEq.rfl
    | none =>
      simp only [Option.elim_none, simulateQ_pure, StateT.run_pure]
      let : MeasurableSpace (Option δ × σ) := ⊤
      apply evalDistEq_iff_evalDist_eq.mpr
      rw [evalDist_bind_const _ (none, s) (hB p.1 s), evalDist_pure]
  exact h.map Prod.fst

/-- The historical short-circuit commute observed in any output measurable structure. -/
theorem elim_comm_prefix
    (so : QueryImpl spec (StateT σ ProbComp))
    (hso : ∀ (t : spec.Domain) (s : σ) (x : spec.Range t × σ),
      x ∈ support ((so t).run s) → x.2 = s)
    {α₀ γ β δ : Type} [MeasurableSpace (Option δ)]
    (PRE : OracleComp spec α₀) (mO : α₀ → OracleComp spec (Option γ))
    (Bb : α₀ → OracleComp spec β) (C : α₀ → β → γ → OracleComp spec (Option δ))
    (hB : ∀ (x : α₀) (s' : σ), probFailure ((simulateQ so (Bb x)).run s') = 0)
    (s : σ) :
    evalDist ((simulateQ so (PRE >>= fun x => mO x >>= fun o => Bb x >>= fun b =>
        o.elim (pure none) (fun c => C x b c))).run' s)
      = evalDist ((simulateQ so (PRE >>= fun x => mO x >>= fun o =>
        o.elim (pure none) (fun c => Bb x >>= fun b => C x b c))).run' s) :=
  (evalDistEq_elim_comm_prefix so hso PRE mO Bb C hB s).evalDist_eq

#print axioms evalDistEq_elim_comm_prefix
#print axioms elim_comm_prefix

/-- **Elim-stage commute (bad-event level).** A never-failing plain stage `B` may be moved across an
`Option`-elim short-circuit without changing the probability of a `none`-false event `badpred`: running
`B` before the elim (always) vs inside the `some`-branch (only on success) agree on `badpred`, since the
`none` branch outputs `none` either way (where `badpred` is false). Bridges the full-evalDist stage swap
(`evalDist_simulateQ_swap`) to `probComp_seam_union_le`'s short-circuiting `mx >>= my` for
`appendSoundness`. -/
theorem probEvent_elim_comm {α γ β : Type}
    (mO : ProbComp (Option α)) (B : ProbComp γ)
    (C : α → γ → ProbComp (Option β)) (badpred : Option β → Prop) (hnone : ¬ badpred none) :
    probEvent (badpred) (mO >>= fun o => B >>= fun b => o.elim (pure none) (fun a => C a b))
      = probEvent (badpred) (mO >>= fun o => o.elim (pure none) (fun a => B >>= fun b => C a b)) := by
  unfold probEvent
  refine prEvent_bind_congr mO _ _ badpred badpred ?_
  intro o
  cases o with
  | none => simp [hnone]
  | some a => rfl

#print axioms probEvent_elim_comm

/-- **Value-state-independence of a simulated run.** If every query implementation both preserves the
state (`hso`) and produces a value-distribution independent of the input state (`hvb`), then the whole
simulated computation's value-distribution (`run'`) is independent of the starting state. Holds for
`challengeQueryImpl` (uniform sample, `σ` untouched) and empty `oSpec`. Lets `probComp_seam_union_le`'s
per-threaded-state `h₂` be discharged by the verifier's (state-averaged) soundness, since every threaded
state gives the same value-distribution. -/
theorem evalDistEq_simulateQ_run'_state_indep
    (so : QueryImpl spec (StateT σ ProbComp))
    (hso : ∀ (t : spec.Domain) (s : σ) (x : spec.Range t × σ),
      x ∈ support ((so t).run s) → x.2 = s)
    (hvb : ∀ (t : spec.Domain) (s s' : σ), (so t).run' s =ᵈ (so t).run' s')
    {α : Type} (X : OracleComp spec α) (s s' : σ) :
    (simulateQ so X).run' s =ᵈ (simulateQ so X).run' s' := by
  induction X using OracleComp.inductionOn generalizing s s' with
  | pure a => simp [simulateQ_pure, StateT.run'_eq, StateT.run_pure]
  | query_bind t oa ih =>
    have hq : ∀ r : σ, (simulateQ so (liftM (OracleSpec.query t))).run r = (so t).run r := by
      intro r
      simp only [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map]
    have key : ∀ r : σ,
        (simulateQ so (liftM (OracleSpec.query t) >>= oa)).run' r =
        (so t).run' r >>= fun a => (simulateQ so (oa a)).run' r := by
      intro r
      rw [StateT.run'_eq, simulateQ_run_bind_state_fixed so hso, hq r]
      simp only [StateT.run'_eq, map_bind, bind_map_left]
    rw [key s, key s']
    exact (hvb t s s').bind (fun a => ih a s s')

/-- Value-state blindness, with full discrete query laws and arbitrary output observations. -/
theorem evalDist_simulateQ_run'_state_indep
    (so : QueryImpl spec (StateT σ ProbComp))
    (hso : ∀ (t : spec.Domain) (s : σ) (x : spec.Range t × σ),
      x ∈ support ((so t).run s) → x.2 = s)
    (hvb : ∀ (t : spec.Domain) (s s' : σ),
      letI : MeasurableSpace (spec.Range t) := ⊤
      evalDist ((so t).run' s) = evalDist ((so t).run' s'))
    {α : Type} [MeasurableSpace α] (X : OracleComp spec α) (s s' : σ) :
    evalDist ((simulateQ so X).run' s) = evalDist ((simulateQ so X).run' s') := by
  apply EvalDistEq.evalDist_eq
  apply evalDistEq_simulateQ_run'_state_indep so hso
  intro t s s'
  let : MeasurableSpace (spec.Range t) := ⊤
  exact EvalDistEq.of_evalDist_eq (hvb t s s')

#print axioms evalDistEq_simulateQ_run'_state_indep
#print axioms evalDist_simulateQ_run'_state_indep

/-- **Seam swap as a bare `evalDist` equality (the reorder, packaged for `rw`).** The natural-order
seam distribution `FST → SND → W1 → W2` equals the union-bound-order distribution `(FST→W1) ; (SND→W2)`.
Unlike `probComp_seam_swap_union_le` (a `≤` whose `exact`/`apply` against a *concrete* prover/verifier
chain triggers a `PFunctor.FreeM.mapM` `isDefEq` blow-up), this is an *equality* and so can be applied
to a concrete goal with `rw` — keyed matching sidesteps the defeq wall. Proof: `lift_run_elim` exposes
the run-forms, then `evalDist_simulateQ_swap_prefix` (swap `SND` past `W1`) + `elim_comm_prefix` (move
`SND` inside `W1`'s accept branch). -/
theorem seam_swap_evalDist_eq
    (init : ProbComp σ) (so : QueryImpl spec (StateT σ ProbComp))
    (hso : ∀ (t : spec.Domain) (s : σ) (x : spec.Range t × σ),
      x ∈ support ((so t).run s) → x.2 = s)
    {A B C D : Type} [MeasurableSpace (Option D)]
    (FST : OracleComp spec A) (SND : A → OracleComp spec B)
    (W1 : A → OptionT (OracleComp spec) C) (W2 : A → B → C → OptionT (OracleComp spec) D)
    (hB : ∀ (x : A) (s' : σ), probFailure ((simulateQ so (SND x)).run s') = 0) :
    𝒟[init >>= fun s => (simulateQ so
        (liftM FST >>= fun x => liftM (SND x) >>= fun a => W1 x >>= fun s₂ =>
          W2 x a s₂).run).run' s]
    = 𝒟[init >>= fun s => (simulateQ so
        ((liftM FST >>= fun x => W1 x >>= fun s₂ =>
            (pure (x, s₂) : OptionT (OracleComp spec) (A × C)))
          >>= fun p => liftM (SND p.1) >>= fun a => W2 p.1 a p.2).run).run' s] := by
  have h1 : (liftM FST >>= fun x => liftM (SND x) >>= fun a => W1 x >>= fun s₂ =>
      W2 x a s₂ : OptionT (OracleComp spec) D).run
    = FST >>= fun x => SND x >>= fun a => (W1 x).run >>= fun o₁ =>
        o₁.elim (pure none) (fun s₂ => (W2 x a s₂).run) := by
    simp only [OptionT.run_bind, Option.elimM, lift_run_elim]
  have h2 : (((liftM FST >>= fun x => W1 x >>= fun s₂ =>
        (pure (x, s₂) : OptionT (OracleComp spec) (A × C)))
      >>= fun p => liftM (SND p.1) >>= fun a => W2 p.1 a p.2) : OptionT (OracleComp spec) D).run
    = FST >>= fun x => (W1 x).run >>= fun o₁ =>
        o₁.elim (pure none) (fun s₂ => SND x >>= fun a => (W2 x a s₂).run) := by
    simp only [OptionT.run_bind, Option.elimM, lift_run_elim, bind_assoc, pure_bind]
  rw [h1, h2]
  apply EvalDistEq.evalDist_eq
  apply EvalDistEq.bind_right
  intro s
  exact (evalDistEq_simulateQ_swap_prefix so hso FST SND (fun x => (W1 x).run)
    (fun x a o₁ => o₁.elim (pure none) (fun s₂ => (W2 x a s₂).run)) s).trans
    (evalDistEq_elim_comm_prefix so hso FST (fun x => (W1 x).run) SND
      (fun x a s₂ => (W2 x a s₂).run) hB s)

#print axioms seam_swap_evalDist_eq

/-- **Seam swap as a `probEvent` equality (the `rw`/`simp`-usable form for the concrete goal).** The
`probEvent`-level companion to `seam_swap_evalDist_eq`: any event `p` has the same probability under the
natural-order seam chain and the union-bound-order chain. This is the form actually applied to the
concrete `appendSoundness` goal — via `simp only [seam_swap_probEvent_eq …]` (so the higher-order
`W2 x a s₂` is beta-reduced to match the goal's body), turning the soundness goal into
`probComp_seam_union_le`'s shape without ever triggering the `exact`-defeq blow-up. -/
theorem seam_swap_probEvent_eq
    (init : ProbComp σ) (so : QueryImpl spec (StateT σ ProbComp))
    (hso : ∀ (t : spec.Domain) (s : σ) (x : spec.Range t × σ),
      x ∈ support ((so t).run s) → x.2 = s)
    {A B C D : Type}
    (FST : OracleComp spec A) (SND : A → OracleComp spec B)
    (W1 : A → OptionT (OracleComp spec) C) (W2 : A → B → C → OptionT (OracleComp spec) D)
    (hB : ∀ (x : A) (s' : σ), probFailure ((simulateQ so (SND x)).run s') = 0)
    (p : Option D → Prop) :
    probEvent (p) (init >>= fun s => (simulateQ so
        (liftM FST >>= fun x => liftM (SND x) >>= fun a => W1 x >>= fun s₂ =>
          W2 x a s₂).run).run' s)
    = probEvent (p) (init >>= fun s => (simulateQ so
        ((liftM FST >>= fun x => W1 x >>= fun s₂ =>
            (pure (x, s₂) : OptionT (OracleComp spec) (A × C)))
          >>= fun p => liftM (SND p.1) >>= fun a => W2 p.1 a p.2).run).run' s) := by
  let : MeasurableSpace (Option D) := ⊤
  exact (EvalDistEq.of_evalDist_eq
    (seam_swap_evalDist_eq init so hso FST SND W1 W2 hB)).prEvent_eq p

#print axioms seam_swap_probEvent_eq

/-- **Two-phase seam soundness with the snd↔V₁ reorder built in.** This is the abstract heart of
`appendSoundness`: a malicious-prover seam chain runs the two prover phases `FST`, `SND` and the two
verifier phases `W1` (`= V₁`), `W2` (`= V₂`) in the *natural* order `FST → SND → W1 → W2`, but the
union bound needs the `(FST→W1) ; (SND→W2)` factorization. This lemma performs that reorder internally
(`lift_run_elim` collapses the never-failing prover lifts; `evalDist_simulateQ_swap_prefix` swaps `SND`
past `W1`; `elim_comm_prefix` moves `SND` inside `W1`'s accept-branch), then applies
`probComp_seam_union_le`. The caller supplies only the two per-phase bounds `h₁` (on `FST→W1`) and
`h₂` (on `SND→W2`) — which are exactly `V₁`/`V₂`'s soundness against the seam-restricted provers — plus
the state-preservation `hso` and the prover-never-fails side-condition `hB` (both hold for the
interactive challenge oracle over an empty shared spec). The result is the additive bound `e₁ + e₂`. -/
theorem probComp_seam_swap_union_le
    (init : ProbComp σ) (so : QueryImpl spec (StateT σ ProbComp))
    (hso : ∀ (t : spec.Domain) (s : σ) (x : spec.Range t × σ),
      x ∈ support ((so t).run s) → x.2 = s)
    {A B C D : Type}
    (FST : OracleComp spec A) (SND : A → OracleComp spec B)
    (W1 : A → OptionT (OracleComp spec) C) (W2 : A → B → C → OptionT (OracleComp spec) D)
    (hB : ∀ (x : A) (s' : σ), probFailure ((simulateQ so (SND x)).run s') = 0)
    (pg : C → Prop) (qg : D → Prop) (e₁ e₂ : ℝ≥0∞)
    (h₁ : probEvent (fun r => ¬ Option.elim r.1 True (fun p : A × C => pg p.2)) (init >>= fun s => (simulateQ so
              (liftM FST >>= fun x => W1 x >>= fun s₂ =>
                (pure (x, s₂) : OptionT (OracleComp spec) (A × C))).run).run s) ≤ e₁)
    (h₂ : ∀ (p : A × C) (s' : σ),
          (some p, s') ∈ support (init >>= fun s => (simulateQ so
              (liftM FST >>= fun x => W1 x >>= fun s₂ =>
                (pure (x, s₂) : OptionT (OracleComp spec) (A × C))).run).run s) → pg p.2 →
          probEvent (fun o => ¬ Option.elim o True qg) ((simulateQ so (liftM (SND p.1) >>= fun a => W2 p.1 a p.2).run).run' s') ≤ e₂) :
    probEvent (fun o => ¬ Option.elim o True qg) (init >>= fun s => (simulateQ so
            (liftM FST >>= fun x => liftM (SND x) >>= fun a => W1 x >>= fun s₂ =>
              W2 x a s₂).run).run' s) ≤ e₁ + e₂ := by
  have key := seam_swap_probEvent_eq init so hso FST SND W1 W2 hB
    (fun o => ¬ Option.elim o True qg)
  have hmain := probComp_seam_union_le init so
    (liftM FST >>= fun x => W1 x >>= fun s₂ => (pure (x, s₂) : OptionT (OracleComp spec) (A × C)))
    (fun p => liftM (SND p.1) >>= fun a => W2 p.1 a p.2)
    (fun p : A × C => pg p.2) qg e₁ e₂ h₁ h₂
  rw [key]
  exact hmain

#print axioms probComp_seam_swap_union_le

section AddLiftBridges
open ProtocolSpec
variable {ι : Type} {oSpec : OracleSpec ι} {σ : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, SampleableType (pSpec.Challenge i)]

/-- **`addLift impl challengeQueryImpl` is state-preserving when `impl` is.** The challenge half is a
`liftM` of a `ProbComp` (state untouched: `(liftM mx).run s = (·, s) <$> mx`); the `oSpec` half is `impl`
(state-preserving by hypothesis; vacuous when `oSpec = []ₒ`). Discharges the `hso` side-condition of the
seam toolkit for the actual soundness/completeness implementation `impl.addLift challengeQueryImpl`. -/
theorem addLift_state_preserving (impl : QueryImpl oSpec (StateT σ ProbComp))
    (himpl : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s) :
    ∀ (t : (oSpec + [pSpec.Challenge]ₒ).Domain) (s : σ) (x : _ × σ),
      x ∈ support (((impl.addLift challengeQueryImpl :
        QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp)) t).run s) → x.2 = s := by
  rintro (t | t) s x hx
  · simp only [QueryImpl.addLift_def, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply,
      monadLift_self] at hx
    exact himpl t s x hx
  · simp only [QueryImpl.addLift_def, QueryImpl.add_apply_inr, QueryImpl.liftTarget_apply] at hx
    simp only [StateT.run_liftM, MonadAttach.support_bind, Set.mem_iUnion,
      MonadAttach.support_pure, Set.mem_singleton_iff] at hx
    obtain ⟨a, _, rfl⟩ := hx
    rfl

/-- **`addLift impl challengeQueryImpl` never fails when `impl` never fails.** The shared-oracle half
(`inl`) inherits `impl`'s non-failure; the challenge half (`inr`) is a uniform sample (`$ᵗ`), which
never fails. Combined with `simulateQ_run_neverFail`, this discharges the `hB` side-condition of
`appendSoundness` for the honest interactive implementation (vacuous when `oSpec = []ₒ`). -/
theorem addLift_neverFail (impl : QueryImpl oSpec (StateT σ ProbComp))
    (himpl : ∀ (t : oSpec.Domain) (s : σ), probFailure ((impl t).run s) = 0) :
    ∀ (t : (oSpec + [pSpec.Challenge]ₒ).Domain) (s : σ),
      probFailure (((impl.addLift challengeQueryImpl :
        QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp)) t).run s) = 0 := by
  rintro (t | t) s
  · simp only [QueryImpl.addLift_def, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply,
      monadLift_self]
    exact himpl t s
  · exact OracleComp.prFail_eq_zero _

/-- **`addLift impl challengeQueryImpl` is value-state-blind when `impl` is.** Discharges `hvb`. -/
theorem addLift_value_blind (impl : QueryImpl oSpec (StateT σ ProbComp))
    (himpl : ∀ (t : oSpec.Domain) (s s' : σ),
      letI : MeasurableSpace (oSpec.Range t) := ⊤
      evalDist ((impl t).run' s) = evalDist ((impl t).run' s')) :
    ∀ (t : (oSpec + [pSpec.Challenge]ₒ).Domain) (s s' : σ),
      letI : MeasurableSpace ((oSpec + [pSpec.Challenge]ₒ).Range t) := ⊤
      evalDist (((impl.addLift challengeQueryImpl :
        QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp)) t).run' s)
        = evalDist (((impl.addLift challengeQueryImpl :
        QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp)) t).run' s') := by
  rintro (t | t) s s'
  · simp only [QueryImpl.addLift_def, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply,
      monadLift_self]
    exact himpl t s s'
  · have h : ∀ r : σ, ((impl.addLift challengeQueryImpl :
        QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp)) (Sum.inr t)).run' r
        = challengeQueryImpl t := by
      intro r
      simp only [QueryImpl.addLift_def, QueryImpl.add_apply_inr, QueryImpl.liftTarget_apply,
        StateT.run'_eq, StateT.run_liftM, bind_pure_comp, Functor.map_map]
      exact id_map _
    exact congrArg (@evalDist ProbComp _ _ ⊤) ((h s).trans (h s').symm)

#print axioms addLift_state_preserving
#print axioms addLift_neverFail
#print axioms addLift_value_blind

end AddLiftBridges

end OptionTStateT
