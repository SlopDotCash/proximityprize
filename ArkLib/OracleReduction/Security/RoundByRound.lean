/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.Security.Basic
import ArkLib.ToVCVio.OracleComp.SimSemantics.SimulateQ

/-!
  # Round-by-Round Security Definitions

  This file defines round-by-round security notions for (oracle) reductions.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

namespace Extractor

/-- A **one-shot** round-by-round extractor is a function that:
- Takes in index `m : Fin (n + 1)`
- Takes in the input statement `stmtIn : StmtIn`
- Takes in a partial transcript up to round `m`
- Takes in the prover's query log (planned refinement: include the verifier's query log as well)

and returns an input witness `witIn : WitIn`.

This is the old definition of round-by-round extractor, which is less general than the new
definition (i.e. the input witness is extracted immediately, "in one shot", unlike the general
definition where the input witness is derived via intermediate witnesses). -/
def RoundByRoundOneShot
    (oSpec : OracleSpec ι) (StmtIn WitIn : Type) {n : ℕ} (pSpec : ProtocolSpec n) :=
  (m : Fin (n + 1)) → StmtIn → Transcript m pSpec → QueryLog oSpec → WitIn

-- STATEMENT REPAIR (2026-06-04): completed the `IsMonotone` statement.
--
-- The previous body was an explicit query-log extension condition
-- (`proveQueryLog₁.Sublist proveQueryLog₂`). That condition is *inert*: it is exactly what
-- `toKnowledgeStateFunction` below needs, but only after we identify the *transcript-prefix*
-- (round) direction along which monotonicity must hold. We derive the real content directly from
-- where the conversion fails (the round-`m+1 → m` step of `KnowledgeStateFunction.toFun_next`): the
-- one-shot extractor, run at round `m.succ` on a transcript `tr.concat msg`, when it lands inside
-- `relIn`, must also land inside `relIn` when run at the prefix round `m.castSucc` on `tr`. This is
-- the precise (and only) ingredient the converter is missing — see
-- `toKnowledgeStateFunction` and docs/kb/audits/gh-issues-campaign-2026-06-04.md (Blocker-C).
/-- A one-shot round-by-round extractor is **monotone** (with respect to an input relation `relIn`)
  if, whenever the extracted input witness at round `m.succ` on a transcript `tr.concat msg` is
  valid for `relIn`, then the extracted input witness at the prefix round `m.castSucc` on `tr` is
  also
  valid for `relIn`.

  This is the round-by-round (transcript-prefix) monotonicity that the conversion
  `KnowledgeStateFunctionOneShot.toKnowledgeStateFunction` requires: the general round-by-round
  knowledge state function processes rounds in decreasing order `n → 0`, extracting the input
  witness from each round's transcript, and its `toFun_next` obligation is exactly that validity at
  round `m.succ` descends to validity at round `m.castSucc`. -/
class RoundByRoundOneShot.IsMonotone (E : RoundByRoundOneShot oSpec StmtIn WitIn pSpec)
    (relIn : Set (StmtIn × WitIn)) where
  is_monotone : ∀ (m : Fin n) (stmtIn : StmtIn) (tr : Transcript m.castSucc pSpec)
      (msg : pSpec.Type m),
    (stmtIn, E m.succ stmtIn (tr.concat msg) default) ∈ relIn →
      (stmtIn, E m.castSucc stmtIn tr default) ∈ relIn

/-- A **round-by-round extractor** is a tuple of algorithms that iteratively extracts the input
  witness from the output witness, through a series of intermediate witnesses
  (indexed by `m : Fin (n + 1)`). Formally, it contains the following components:

  - A proof `eqIn : WitMid 0 = WitIn` that the first intermediate witness type is equal to the
    input witness type
  - A function `extractMid : (m : Fin n) → StmtIn → Transcript m.succ pSpec`
    `→ WitMid m.succ → WitMid m.castSucc` that extracts the intermediate witness for round `m`
    from the intermediate witness for round `m+1`, using the transcript up to round `m+1` and
    the intermediate witness for round `m+1`
  - A function `extractOut : StmtIn → FullTranscript pSpec → WitOut → WitMid (.last n)` that
    constructs the intermediate witness for the final round from the output witness

  The extractor processes rounds in decreasing order: `n → n-1 → ... → 1 → 0`, using
  intermediate witness types `WitMid m` for each round `m`.
-/
structure RoundByRound
    (oSpec : OracleSpec ι) (StmtIn WitIn WitOut : Type) {n : ℕ} (pSpec : ProtocolSpec n)
    (WitMid : Fin (n + 1) → Type) where
  /-- The first intermediate witness type is equal to the input witness type -/
  eqIn : WitMid 0 = WitIn
  /-- Extract intermediate witness for round `m` from intermediate witness for round `m+1`,
    using the transcript up to round `m+1` -/
  extractMid : (m : Fin n) → StmtIn → Transcript m.succ pSpec → WitMid m.succ → WitMid m.castSucc
  /-- Construct the intermediate witness for the final round from the output witness -/
  extractOut : StmtIn → FullTranscript pSpec → WitOut → WitMid (.last n)

namespace RoundByRoundOneShot

/-- A one-shot round-by-round extractor can be converted to the general round-by-round extractor
  format, where all intermediate witness types are equal to the input witness type.

  Note that the converse is _not_ true: it's not possible in general to convert a general
  round-by-round extractor to a one-shot one. -/
def toRoundByRound (E : RoundByRoundOneShot oSpec StmtIn WitIn pSpec) :
    RoundByRound oSpec StmtIn WitIn WitOut pSpec (fun _ => WitIn) where
  eqIn := rfl
  -- STATEMENT REPAIR (2026-06-04): drop the `if m.castSucc = 0 then witIn` special case.
  -- The previous definition returned the *threaded* intermediate witness `witIn` at the round-0
  -- step, which made `KnowledgeStateFunction.toFun_next` unprovable: that obligation demands
  -- `(stmtIn, extractMid 0 stmtIn (tr.concat msg) witIn) ∈ relIn` for an *arbitrary* `witIn`, while
  -- the round-`m.succ` knowledge-state predicate is witness-independent (the round-0 extractor
  -- mismatch documented in the audit, Blocker-C). Always extracting via `E` on the transcript
  -- prefix `Fin.init tr` unifies every round under the single `IsMonotone` bridge.
  extractMid := fun m stmtIn tr _ => E m.castSucc stmtIn (Fin.init tr) default
  extractOut := fun stmtIn tr _ => E (.last n) stmtIn tr default

end RoundByRoundOneShot

end Extractor

namespace Verifier

section RoundByRound

/-- A (deterministic) state function for a verifier, with respect to input language `langIn` and
  output language `langOut`. This is used to define round-by-round soundness. -/
structure StateFunction
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    where
  toFun : (m : Fin (n + 1)) → StmtIn → Transcript m pSpec → Prop
  /-- For all input statement not in the language, the state function is false for that statement
    and the empty transcript -/
  toFun_empty : ∀ stmt, stmt ∈ langIn ↔ toFun 0 stmt default
  /-- If the state function is false for a partial transcript, and the next message is from the
    prover to the verifier, then the state function is also false for the new partial transcript
    regardless of the message -/
  toFun_next : ∀ m, pSpec.dir m = .P_to_V →
    ∀ stmt tr, ¬ toFun m.castSucc stmt tr →
    ∀ msg, ¬ toFun m.succ stmt (tr.concat msg)
  /-- If the state function is false for a full transcript, the verifier will not output a statement
    in the output language -/
  toFun_full : ∀ stmt tr, ¬ toFun (.last n) stmt tr →
    Pr[(· ∈ langOut) | OptionT.mk do (simulateQ impl (verifier.run stmt tr)).run' (← init)] = 0

namespace StateFunction

/-! ### Reusable combinatorial / union-bound backbone for round-by-round soundness

These lemmas isolate the two protocol-independent ingredients of the
`rbrSoundness → soundness` implication (and its knowledge variant):

* a *first-crossing* (pigeonhole) argument: a Prop-valued sequence over the `Fin (n + 1)` rounds
  that is `false` at round `0` and `true` at the last round must *flip* `false → true` at some
  round, and — given the `toFun_next` semantics that forbid flips at prover-to-verifier rounds —
  that flipping round is a *challenge* round; and
* a *finite union bound* over the (finite) set of challenge rounds.

Composing these reduces the soundness error to `∑ i, rbrSoundnessError i`, once the realized run is
related to the per-round partial-run marginals.  The two lemmas below are fully general (they make
no reference to the probabilistic execution), so they are directly reusable for both the plain and
the knowledge variants. -/

omit [∀ i, SampleableType (pSpec.Challenge i)] init impl in
/-- **First-crossing / pigeonhole over rounds.**  If a `Prop`-valued sequence indexed by the
`Fin (n + 1)` rounds is `false` at round `0` and `true` at the last round, then there is some round
`j : Fin n` at which it flips from `false` (at `j.castSucc`) to `true` (at `j.succ`).

This is the protocol-independent core of the union bound that turns round-by-round soundness into
plain soundness: a run that ends accepting on a bad statement (state `true` at the end) but starts
rejecting (state `false` at the start) must cross at some first round, and the per-round crossing
events are exactly what `rbrSoundnessError` bounds. -/
theorem exists_flip_of_false_zero_true_last
    (P : Fin (n + 1) → Prop) [DecidablePred P]
    (h0 : ¬ P 0) (hlast : P (Fin.last n)) :
    ∃ j : Fin n, ¬ P j.castSucc ∧ P j.succ := by
  by_contra hcon
  push Not at hcon
  have key : ∀ k : Fin (n + 1), ¬ P k := by
    intro k
    induction k using Fin.induction with
    | zero => exact h0
    | succ i ih => exact hcon i ih
  exact key (Fin.last n) hlast

omit [∀ i, SampleableType (pSpec.Challenge i)] init impl in
/-- **First-crossing landing on a challenge round.**  Strengthening of
`exists_flip_of_false_zero_true_last`: if, in addition, `P` cannot flip `false → true` at any
prover-to-verifier round (the property guaranteed by `StateFunction.toFun_next`), then the crossing
round is a *challenge* round `j : pSpec.ChallengeIdx`.

This is the exact shape consumed by the union bound over challenge rounds: the resulting
`pSpec.ChallengeIdx` matches the index type of `rbrSoundnessError`. -/
theorem exists_challenge_flip_of_false_zero_true_last
    (P : Fin (n + 1) → Prop) [DecidablePred P]
    (h0 : ¬ P 0) (hlast : P (Fin.last n))
    (hPtoV : ∀ j : Fin n, pSpec.dir j = .P_to_V → ¬ P j.castSucc → ¬ P j.succ) :
    ∃ j : pSpec.ChallengeIdx, ¬ P j.1.castSucc ∧ P j.1.succ := by
  obtain ⟨j, hcast, hsucc⟩ := exists_flip_of_false_zero_true_last P h0 hlast
  cases hdir : pSpec.dir j with
  | P_to_V => exact absurd hsucc (hPtoV j hdir hcast)
  | V_to_P => exact ⟨⟨j, hdir⟩, hcast, hsucc⟩

omit [∀ i, SampleableType (pSpec.Challenge i)] init impl in
/-- **Union bound over a finset of indices.**  The probability that *some* index in a finset `s`
satisfies its event is at most the sum, over `s`, of the per-index probabilities.  Proved by
iterating the binary union bound `probEvent_or_le`. -/
theorem probEvent_exists_mem_le_sum {m : Type → Type*} [Monad m] [HasEvalSPMF m] {α : Type}
    {κ : Type} [DecidableEq κ] (mx : m α) (p : κ → α → Prop) (s : Finset κ) :
    Pr[fun x => ∃ i ∈ s, p i x | mx] ≤ ∑ i ∈ s, Pr[fun x => p i x | mx] := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty]
    rw [nonpos_iff_eq_zero, probEvent_eq_zero_iff]
    rintro x _ ⟨i, hi, _⟩
    simp at hi
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have hor : Pr[fun x => (∃ i ∈ insert a s, p i x) | mx]
        ≤ Pr[p a | mx] + Pr[fun x => ∃ i ∈ s, p i x | mx] := by
      refine le_trans (le_of_eq ?_) (probEvent_or_le mx (p a) (fun x => ∃ i ∈ s, p i x))
      congr 1
      funext x
      simp only [Finset.mem_insert, eq_iff_iff]
      constructor
      · rintro ⟨i, (rfl | hi), hpi⟩
        · exact Or.inl hpi
        · exact Or.inr ⟨i, hi, hpi⟩
      · rintro (hpa | ⟨i, hi, hpi⟩)
        · exact ⟨a, Or.inl rfl, hpa⟩
        · exact ⟨i, Or.inr hi, hpi⟩
    calc Pr[fun x => (∃ i ∈ insert a s, p i x) | mx]
        ≤ Pr[p a | mx] + Pr[fun x => ∃ i ∈ s, p i x | mx] := hor
      _ ≤ Pr[p a | mx] + ∑ i ∈ s, Pr[fun x => p i x | mx] := by gcongr

omit [∀ i, SampleableType (pSpec.Challenge i)] init impl in
/-- **Union bound over a fintype of indices.**  Specialization of `probEvent_exists_mem_le_sum` to
the full (finite) index type, e.g. `pSpec.ChallengeIdx`.  The probability that *some* index
satisfies its event is at most the total sum of per-index probabilities — the form used to bound a
soundness error by `∑ i, rbrSoundnessError i`. -/
theorem probEvent_exists_le_sum {m : Type → Type*} [Monad m] [HasEvalSPMF m] {α : Type}
    {κ : Type} [Fintype κ] [DecidableEq κ] (mx : m α) (p : κ → α → Prop) :
    Pr[fun x => ∃ i, p i x | mx] ≤ ∑ i : κ, Pr[fun x => p i x | mx] := by
  have := probEvent_exists_mem_le_sum mx p Finset.univ
  simpa using this

omit [∀ i, SampleableType (pSpec.Challenge i)] init impl in
/-- **Union bound via implication.**  Combines `probEvent_mono` with `probEvent_exists_le_sum`: if
on the support of `mx` the target event `q` implies that *some* index satisfies its per-index event
`p i`, then the probability of `q` is bounded by the total sum of per-index probabilities.

This is the reusable shape consumed by `rbrSoundness → soundness`: the target event (the verifier
accepts a bad statement) implies, on the support, that the round-by-round state function flips at
*some* challenge round (the combinatorial first-crossing core), and the per-round flip probabilities
are exactly `rbrSoundnessError i`. -/
theorem probEvent_le_sum_of_imp_exists {m : Type → Type*} [Monad m] [HasEvalSPMF m] {α : Type}
    {κ : Type} [Fintype κ] [DecidableEq κ] (mx : m α) (q : α → Prop) (p : κ → α → Prop)
    (himp : ∀ x ∈ support mx, q x → ∃ i, p i x) :
    Pr[q | mx] ≤ ∑ i : κ, Pr[fun x => p i x | mx] := by
  refine le_trans (probEvent_mono ?_) (probEvent_exists_le_sum mx p)
  exact himp

/-- **Failure-monotone trailing bind.**  Appending a (possibly-failing) computation `gb x` *before*
returning a value `h x` that does not depend on `gb x`'s output can only *decrease* the probability
of any event: the trailing computation contributes only extra failure mass.

This is the reusable probabilistic core of the `rbrSoundness → soundness` marginal bridge: the full
prover run threads the trailing `receiveChallenge`/`sendMessage`/`output` and verifier steps, which
the round-by-round game omits; since the per-round flip event depends only on the transcript prefix
(already determined before those steps), dropping them can only raise the event probability —
turning the marginal relation into the `≤` direction needed to chain to `rbrSoundnessError`. -/
theorem probEvent_bind_trailing_le {m : Type → Type*} [Monad m] [LawfulMonad m] [HasEvalSPMF m]
    {α β γ : Type} (mx : m α) (gb : α → m γ) (h : α → β) (p : β → Prop) :
    Pr[p | mx >>= fun x => gb x >>= fun _ => pure (h x)] ≤ Pr[p | mx >>= fun x => pure (h x)] := by
  refine probEvent_bind_mono (fun x _ => ?_)
  rw [probEvent_bind_const]
  calc (1 - Pr[⊥ | gb x]) * Pr[p | (pure (h x) : m β)]
      ≤ 1 * Pr[p | (pure (h x) : m β)] := by
        gcongr; exact tsub_le_self
    _ = Pr[p | (pure (h x) : m β)] := one_mul _

/-- **`OptionT` probEvent as a success-conjunction on the underlying computation.**  An
`OptionT ProbComp` event probability equals the probability, on the underlying
`ProbComp (Option α)`, of *succeeding with* a value satisfying `p` (failure `none` does NOT count
toward the event).  This is the characterization the `rbrSoundness → soundness` per-round bound
consumes: the soundness game's
flip event must hold on a genuine (non-failing) verifier accept, so failure mass introduced by
trailing computations only *lowers* the event probability (the failure-monotone direction). -/
theorem probEvent_optionT_mk_eq_elim {α : Type}
    (ma : ProbComp (Option α)) (p : α → Prop) :
    Pr[p | (OptionT.mk ma : OptionT ProbComp α)] = Pr[fun o => o.elim False p | ma] := by
  classical
  have hdiff : Pr[fun o => Option.all (fun b => decide (p b)) o = true | ma]
      = Pr[fun o => o.elim False p | ma] + Pr[= none | ma] := by
    rw [probEvent_eq_tsum_indicator, probEvent_eq_tsum_indicator,
        tsum_option _ ENNReal.summable, tsum_option _ ENNReal.summable]
    have e1 : ({x : Option α | Option.all (fun b => decide (p b)) x = true}.indicator
        (fun x => Pr[= x | ma]) none) = Pr[= none | ma] := by simp
    have e2 : ({x : Option α | x.elim False p}.indicator (fun x => Pr[= x | ma]) none)
        = 0 := by simp
    rw [e1, e2, zero_add, add_comm]
    refine congrArg (· + Pr[= none | ma]) (tsum_congr (fun x => ?_))
    by_cases hx : p x <;> simp [hx]
  have h := OptionT.probEvent_eq (OptionT.mk ma : OptionT ProbComp α) p
  simp only [OptionT.run_mk] at h
  rw [hdiff] at h
  exact WithTop.add_right_cancel probOutput_ne_top h

/-- **Heterogeneous bind-monotone over a shared prefix.**  A `probEvent_bind_mono` variant that
allows the post-bind events to differ (different result types `β`, `β'` and predicates `q`, `q'`):
if on the support of the shared prefix `mx` each per-element event probability of `q` under `my x`
is
bounded by that of `q'` under `oc x`, then so are the bound probabilities.  Used to chain the
soundness game's flip event (on the `Option`-wrapped full result) to the round-by-round game's flip
event (on the `(transcript, challenge)` pair), both threaded over the shared `init` sample. -/
theorem probEvent_bind_mono_heteroEvent {m : Type → Type*} [Monad m] [HasEvalSPMF m]
    {α β β' : Type} {mx : m α} {my : α → m β} {oc : α → m β'} {q : β → Prop} {q' : β' → Prop}
    (h : ∀ x ∈ support mx, Pr[q | my x] ≤ Pr[q' | oc x]) :
    Pr[q | mx >>= my] ≤ Pr[q' | mx >>= oc] := by
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  refine ENNReal.tsum_le_tsum (fun x => ?_)
  by_cases hx : x ∈ support mx
  · exact mul_le_mul' le_rfl (h x hx)
  · simp [probOutput_eq_zero_of_not_mem_support hx]

section StateTTransport

variable {ι : Type} {spec : OracleSpec ι} {σ : Type}

/-- **State-aware failure-monotone trailing bind, transported across `simulateQ … |>.run'`.**
For an *arbitrary* stateful query implementation `so : QueryImpl spec (StateT σ ProbComp)` and start
state `s`, running `simulateQ so` on a computation that, after producing `a`, executes a trailing
(possibly-failing) `gb a` and then returns `h a`, has event probability at most that of the
computation that skips the trailing step.  The trailing `gb a` threads the simulation state and can
only add failure mass, which only lowers the event probability.

This is the missing connective of the `rbrSoundness → soundness` marginal bridge: it lets the
trailing `receiveChallenge`/`sendMessage`/`output`/verifier steps of the full run be dropped (one
`probEvent ≤` at a time) while keeping the same arbitrary `impl`/state thread that both the
soundness game and the round-by-round game share. -/
theorem probEvent_simulateQ_run'_bind_trailing_le {α β γ : Type}
    (so : QueryImpl spec (StateT σ ProbComp)) (s : σ)
    (mx : OracleComp spec α) (gb : α → OracleComp spec γ) (h : α → β) (p : β → Prop) :
    Pr[p | (simulateQ so (mx >>= fun a => gb a >>= fun _ => (pure (h a) : OracleComp spec β))).run' s]
      ≤ Pr[p | (simulateQ so (mx >>= fun a => (pure (h a) : OracleComp spec β))).run' s] := by
  simp only [simulateQ_bind]
  rw [StateT.run'_eq, StateT.run'_eq, StateT.run_bind, StateT.run_bind]
  rw [probEvent_map, probEvent_map]
  refine probEvent_bind_mono (fun pr _ => ?_)
  obtain ⟨a, s'⟩ := pr
  simp only [simulateQ_pure, StateT.run_pure, StateT.run_bind]
  -- Goal: `Pr[p∘fst | gb-run >>= fun q => pure (h a, q.2)] ≤ Pr[p∘fst | pure (h a, s')]`.
  -- The event `(p∘fst)(h a, q.2) = p (h a)` does not depend on `q`, so the trailing `gb`-run only
  -- adds failure mass: apply `probEvent_bind_of_const` and drop the `(1 - Pr[⊥]) ≤ 1` factor.
  have hconst : Pr[(p ∘ fun x => x.1) | (simulateQ so (gb a)).run s' >>=
        fun q => (pure (h a, q.2) : ProbComp (β × σ))]
      = (1 - Pr[⊥ | (simulateQ so (gb a)).run s'])
        * Pr[(p ∘ fun x => x.1) | (pure (h a, s') : ProbComp (β × σ))] :=
    probEvent_bind_of_const _ (fun q _ => by
      rw [probEvent_pure_eq_indicator, probEvent_pure_eq_indicator]
      simp only [Set.indicator, Set.mem_setOf_eq, Function.comp, Function.const]
      rfl)
  calc Pr[(p ∘ fun x => x.1) | (simulateQ so (gb a)).run s' >>=
          fun q => (pure (h a, q.2) : ProbComp (β × σ))]
      = (1 - Pr[⊥ | (simulateQ so (gb a)).run s'])
          * Pr[(p ∘ fun x => x.1) | (pure (h a, s') : ProbComp (β × σ))] := hconst
    _ ≤ 1 * Pr[(p ∘ fun x => x.1) | (pure (h a, s') : ProbComp (β × σ))] := by
        gcongr; exact tsub_le_self
    _ = Pr[(p ∘ fun x => x.1) | (pure (h a, s') : ProbComp (β × σ))] := one_mul _

/-- **Failure-monotone drop of an arbitrary `Option`-valued trailing continuation.**  The most
general `Option`-level trailing drop: after `ma` produces `some a`, the soundness game runs an
*arbitrary* trailing continuation `cont a : OracleComp spec (Option β)` (which may itself fail,
return `none`, or succeed) whose output is the final result; we replace it by
`pure (Option.map h oa)`.  The
only hypothesis is that on the (raw) support of `cont a`, every *successful* output `some b` that
satisfies the event `p` forces `p (h a)` too — i.e. `cont a` cannot manufacture a `p`-satisfying
success that the prefix value `h a` does not already witness.  Then dropping `cont a` (whose success
mass is `≤ 1`) only raises the prefix event probability.  (The verifier-verdict/`getM` tail of
`Reduction.run` satisfies the hypothesis with equality: it returns `(pr, verdict)` whose
transcript-reading event value equals that of `h pr = pr`.) -/
theorem probEvent_simulateQ_run'_optionBind_trailing_le {α β : Type}
    (so : QueryImpl spec (StateT σ ProbComp)) (s : σ)
    (ma : OracleComp spec (Option α)) (cont : α → OracleComp spec (Option β))
    (h : α → β) (p : β → Prop)
    (hcont : ∀ a, ∀ b ∈ support (cont a), ∀ b', b = some b' → p b' → p (h a)) :
    Pr[fun o => o.elim False p |
        (simulateQ so (ma >>= fun oa => Option.elimM (pure oa) (pure none) cont)).run' s]
      ≤ Pr[fun o => o.elim False p |
          (simulateQ so (ma >>= fun oa => pure (Option.map h oa))).run' s] := by
  simp only [simulateQ_bind]
  rw [StateT.run'_eq, StateT.run'_eq, StateT.run_bind, StateT.run_bind, probEvent_map,
    probEvent_map]
  refine probEvent_bind_mono (fun pr _ => ?_)
  obtain ⟨oa, s'⟩ := pr
  cases oa with
  | none =>
      simp only [Option.elimM, Option.elim_none, simulateQ_pure, StateT.run_pure,
        pure_bind, Option.map_none, le_refl]
  | some a =>
      simp only [Option.elimM, Option.elim_some, simulateQ_pure, StateT.run_pure, pure_bind,
        Option.map_some]
      -- RHS: `Pr[(·.elim False p)∘fst | pure (some (h a), s')]` = indicator of `p (h a)`.
      by_cases hpha : p (h a)
      · -- RHS = 1, so the bound is trivial.
        rw [probEvent_pure_eq_indicator]
        simp only [Set.indicator, Set.mem_setOf_eq, Function.comp, Option.elim_some, hpha,
          if_true]
        exact probEvent_le_one
      · -- ¬ p (h a): show LHS = 0 (no success of `cont a` satisfies `p`).
        rw [probEvent_pure_eq_indicator]
        simp only [Set.indicator, Set.mem_setOf_eq, Function.comp, Option.elim_some, hpha,
          if_false, nonpos_iff_eq_zero]
        rw [probEvent_eq_zero_iff]
        intro o ho
        -- `o` is a successful run of `cont a`; by `hcont`, its event value forces `p (h a)`.
        rw [Function.comp]
        cases o' : o.1 with
        | none => simp
        | some b =>
            simp only [Option.elim_some]
            intro hpb
            -- `o.1 = some b` is in the support of `(simulateQ so (cont a)).run' s'`,
            -- hence in `support (cont a)`.
            have hb_supp : o.1 ∈ support ((simulateQ so (cont a)).run' s') := by
              rw [StateT.run'_eq, support_map, Set.mem_image]
              exact ⟨o, ho, rfl⟩
            rw [o'] at hb_supp
            have hb_raw : some b ∈ support (cont a) :=
              _root_.support_simulateQ_run'_subset so (cont a) s' hb_supp
            exact hpha (hcont a (some b) hb_raw b rfl hpb)

/-- **Failure-monotone trailing `Option.elimM` drop, transported across `simulateQ … |>.run'`.**
A specialization of the trailing-bind transport to the `OptionT`/`Option.elimM` shape of
`Reduction.run`: after producing `some a` from `ma`, the soundness game runs a trailing
(possibly-failing, possibly-`none`-returning) `Option.elimM`-continuation whose result is the final
output, but the flip event reads only `h a` (a function of the *prefix* `a`).  Replacing the entire
continuation by `pure (some (h a))` (always success) can only *raise* the event probability of an
event that is `False` on `none`: every failure / `none` outcome of the continuation makes the event
`False`, so dropping it only adds success mass.  This is the `Option`-level analogue of
`probEvent_simulateQ_run'_bind_trailing_le`, used to peel the verifier/`getM`/later-round tail off
the soundness game while keeping the shared `impl`/state thread. -/
theorem probEvent_simulateQ_run'_elimM_trailing_le {α β γ : Type}
    (so : QueryImpl spec (StateT σ ProbComp)) (s : σ)
    (ma : OracleComp spec (Option α)) (k : α → OracleComp spec (Option γ))
    (h : α → β) (p : β → Prop) :
    Pr[fun o => o.elim False p |
        (simulateQ so (ma >>= fun oa => Option.elimM (pure oa) (pure none)
          (fun a => k a >>= fun _ => pure (some (h a))))).run' s]
      ≤ Pr[fun o => o.elim False p |
          (simulateQ so (ma >>= fun oa => pure (Option.map h oa))).run' s] := by
  simp only [simulateQ_bind]
  rw [StateT.run'_eq, StateT.run'_eq, StateT.run_bind, StateT.run_bind, probEvent_map,
    probEvent_map]
  refine probEvent_bind_mono (fun pr _ => ?_)
  obtain ⟨oa, s'⟩ := pr
  cases oa with
  | none =>
      simp only [Option.elimM, Option.elim_none, simulateQ_pure, StateT.run_pure,
        pure_bind, Option.map_none, le_refl]
  | some a =>
      simp only [Option.elimM, Option.elim_some, simulateQ_bind, simulateQ_pure, StateT.run_pure,
        StateT.run_bind, pure_bind, Option.map_some]
      -- LHS: run `k a`, discard, return `some (h a)`. RHS: `pure (some (h a))`.
      -- The event `(·.elim False p ∘ fst)` reads `h a` (constant in `k a`'s output), so the
      -- trailing `k a`-run only adds failure mass.
      have hconst : Pr[(fun o => Option.elim o False p) ∘ (fun x => x.1) |
            (simulateQ so (k a)).run s' >>= fun q => (pure (some (h a), q.2) : ProbComp (Option β × σ))]
          = (1 - Pr[⊥ | (simulateQ so (k a)).run s'])
            * Pr[(fun o => Option.elim o False p) ∘ (fun x => x.1) |
                (pure (some (h a), s') : ProbComp (Option β × σ))] :=
        probEvent_bind_of_const _ (fun q _ => by
          rw [probEvent_pure_eq_indicator, probEvent_pure_eq_indicator]
          simp only [Set.indicator, Set.mem_setOf_eq, Function.comp]
          rfl)
      calc Pr[(fun o => Option.elim o False p) ∘ (fun x => x.1) |
              (simulateQ so (k a)).run s' >>= fun q => (pure (some (h a), q.2) : ProbComp (Option β × σ))]
          = (1 - Pr[⊥ | (simulateQ so (k a)).run s'])
              * Pr[(fun o => Option.elim o False p) ∘ (fun x => x.1) |
                  (pure (some (h a), s') : ProbComp (Option β × σ))] := hconst
        _ ≤ 1 * Pr[(fun o => Option.elim o False p) ∘ (fun x => x.1) |
                  (pure (some (h a), s') : ProbComp (Option β × σ))] := by
              gcongr; exact tsub_le_self
        _ = Pr[(fun o => Option.elim o False p) ∘ (fun x => x.1) |
                  (pure (some (h a), s') : ProbComp (Option β × σ))] := one_mul _

end StateTTransport

omit [∀ i, SampleableType (pSpec.Challenge i)] init impl in
/-- **Prefix step of a full transcript.**  Restating `Fin.take_succ_eq_snoc` in `Transcript`/
`FullTranscript` language: the round-`j.succ` prefix of a full transcript is the round-`j.castSucc`
prefix with the round-`j` entry concatenated.  This is the geometric ingredient that lets the
combinatorial first-crossing argument (over transcript prefixes of the *realized* full run) feed the
round-by-round soundness game, which speaks about `transcript.concat challenge`. -/
theorem take_succ_eq_concat {pSpec : ProtocolSpec n} (tr : pSpec.FullTranscript) (j : Fin n) :
    (tr.take j.succ.val j.succ.is_le : Transcript j.succ pSpec)
      = Transcript.concat (tr j) (tr.take j.castSucc.val j.castSucc.is_le) := by
  have hlt : j.val < n := j.isLt
  have hsnoc := Fin.take_succ_eq_snoc j.val hlt tr
  -- `Transcript.concat (tr j) T = Fin.snoc T (tr j)`, and `j.succ.val = j.val.succ`,
  -- `j.castSucc.val = j.val`.
  simp only [FullTranscript.take, Transcript.concat, Fin.val_succ, Fin.val_castSucc]
  rw [hsnoc]
  rfl

omit [∀ i, SampleableType (pSpec.Challenge i)] in
/-- **State-function first-crossing on the realized transcript.**  Specialization of
`exists_challenge_flip_of_false_zero_true_last` to a `StateFunction`: if the input statement is
*not* in `langIn` (so the state function is `false` on the empty round-`0` prefix) and the state
function
is `true` on the *full* transcript `tr` (round `last n`), then there is a challenge round `i` at
which the state function flips on prefixes of `tr` — in the exact `(prefix, prefix.concat (tr i))`
shape consumed by the round-by-round soundness game.

The `toFun_next` field of `StateFunction` supplies the no-flip-at-prover-rounds hypothesis, and
`toFun_empty` together with `stmtIn ∉ langIn` supplies the `false`-at-`0` base; this lemma bundles
both with the pure pigeonhole core and the prefix-step geometry `take_succ_eq_concat`. -/
theorem exists_challenge_flip_of_full {langIn : Set StmtIn} {langOut : Set StmtOut}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    (sf : verifier.StateFunction init impl langIn langOut)
    (stmtIn : StmtIn) (hStmtIn : stmtIn ∉ langIn) (tr : pSpec.FullTranscript)
    (hlast : sf.toFun (Fin.last n) stmtIn (tr.take (Fin.last n).val (Fin.last n).is_le)) :
    ∃ i : pSpec.ChallengeIdx,
      ¬ sf.toFun i.1.castSucc stmtIn (tr.take i.1.castSucc.val i.1.castSucc.is_le) ∧
        sf.toFun i.1.succ stmtIn
          (Transcript.concat (tr i.1) (tr.take i.1.castSucc.val i.1.castSucc.is_le)) := by
  classical
  -- The Prop-valued sequence: state function on the round-`k` prefix of the realized transcript.
  set P : Fin (n + 1) → Prop :=
    fun k => sf.toFun k stmtIn (tr.take k.val k.is_le) with hP
  have h0 : ¬ P 0 := by
    -- At round 0 the prefix is the empty transcript and `toFun 0 = (· ∈ langIn)`.
    have hempty : (tr.take (0 : Fin (n + 1)).val (0 : Fin (n + 1)).is_le)
        = (default : Transcript 0 pSpec) := Subsingleton.elim _ _
    simp only [hP, hempty]
    exact fun h => hStmtIn ((sf.toFun_empty stmtIn).mpr h)
  have hlast' : P (Fin.last n) := hlast
  -- No flip at prover-to-verifier rounds, supplied by `toFun_next`.
  have hPtoV : ∀ j : Fin n, pSpec.dir j = .P_to_V → ¬ P j.castSucc → ¬ P j.succ := by
    intro j hdir hcast
    have hnext := sf.toFun_next j hdir stmtIn (tr.take j.castSucc.val j.castSucc.is_le) hcast (tr j)
    simp only [hP]
    rw [take_succ_eq_concat tr j]
    exact hnext
  obtain ⟨i, hcast, hsucc⟩ :=
    exists_challenge_flip_of_false_zero_true_last P h0 hlast' hPtoV
  refine ⟨i, hcast, ?_⟩
  rw [← take_succ_eq_concat tr i.1]
  exact hsucc

end StateFunction

/-- A knowledge state function for a verifier, with respect to input relation `relIn`, output
  relation `relOut`, and intermediate witness types `WitMid`. This is used to define
  round-by-round knowledge soundness. -/
structure KnowledgeStateFunction
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    {WitMid : Fin (n + 1) → Type}
    (extractor : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid)
    where
  /-- The knowledge state function: takes in round index, input statement, transcript up to that
      round, and intermediate witness of that round, and returns True/False. -/
  toFun : (m : Fin (n + 1)) → StmtIn → Transcript m pSpec → WitMid m → Prop
  /-- The input statement and witness are in the input relation if and only if the state function is
      true for the empty transcript and the input witness -/
  toFun_empty : ∀ stmtIn witMid,
    ⟨stmtIn, cast extractor.eqIn witMid⟩ ∈ relIn ↔ toFun 0 stmtIn default witMid
  /-- If the state function is true for a partial transcript extended with a prover message, then
    the state function is also true for the original partial transcript with the extracted
    intermediate witness -/
  toFun_next : ∀ m, pSpec.dir m = .P_to_V →
    ∀ stmtIn tr msg witMid, toFun m.succ stmtIn (tr.concat msg) witMid →
      toFun m.castSucc stmtIn tr (extractor.extractMid m stmtIn (tr.concat msg) witMid)
  /-- If the verifier can output a statement `stmtOut` that is in the output relation with some
    output witness `witOut`, then the state function is true for the full transcript and the
    extracted last middle witness. -/
  toFun_full : ∀ stmtIn tr witOut,
    Pr[fun stmtOut => (stmtOut, witOut) ∈ relOut
    | OptionT.mk do (simulateQ impl (verifier.run stmtIn tr)).run' (← init)] > 0 →
    toFun (.last n) stmtIn tr (extractor.extractOut stmtIn tr witOut)

/-- A knowledge state function gives rise to a state function via quantifying over the witness -/
def KnowledgeStateFunction.toStateFunction
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec} {WitMid : Fin (n + 1) → Type}
    {extractor : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid}
    (kSF : KnowledgeStateFunction init impl relIn relOut verifier extractor) :
      verifier.StateFunction init impl relIn.language relOut.language where
  toFun := fun m stmtIn tr => ∃ witMid, kSF.toFun m stmtIn tr witMid
  toFun_empty := by
    intro stmtIn
    simp only [Set.mem_image, Prod.exists, exists_and_right, exists_eq_right]
    constructor
    · intro ⟨witIn, h⟩
      have := kSF.toFun_empty stmtIn (cast extractor.eqIn.symm witIn)
      simp at this
      refine ⟨_, this.mp h⟩
    · intro ⟨witMid, h⟩
      exact ⟨_, (kSF.toFun_empty stmtIn witMid).mpr h⟩
  toFun_next := fun m hDir stmtIn tr hToFunNext msg => by
    simp only [not_exists]
    intro witMid hToFunNext
    have := kSF.toFun_next m hDir stmtIn tr msg witMid hToFunNext
    simp_all
  toFun_full := fun stmtIn tr hToFunFull => by
    simp only [Fin.val_last, Set.mem_image, Prod.exists, exists_and_right, exists_eq_right,
      probEvent_eq_zero_iff, not_exists]
    intro stmtOut hStmtOut witOut hRelOut
    have hProb :
        Pr[fun stmtOut ↦ (stmtOut, witOut) ∈ relOut
        | OptionT.mk do (simulateQ impl (verifier.run stmtIn tr)).run' (← init)] > 0 := by
      simp only [Fin.val_last, gt_iff_lt, probEvent_pos_iff]
      exact ⟨stmtOut, hStmtOut, hRelOut⟩
    have := kSF.toFun_full stmtIn tr witOut hProb
    simp_all

/-- A (deterministic) knowledge state function for a verifier, with respect to input language
  `langIn` and output language `langOut`. This is used to define one-shot round-by-round knowledge
  soundness. Note the different condition for the empty transcript: `toFun 0` is supposed to be
  always zero. -/
structure KnowledgeStateFunctionOneShot
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    where
  toFun : (m : Fin (n + 1)) → StmtIn → Transcript m pSpec → Prop
  /-- For all input statement not in the language, the state function is false for the empty
    transcript -/
  toFun_empty : ∀ stmtIn, ¬ toFun 0 stmtIn default
  /-- If the state function is false for a partial transcript, and the next message is from the
    prover to the verifier, then the state function is also false for the new partial transcript
    regardless of the message -/
  toFun_next : ∀ m, pSpec.dir m = .P_to_V →
    ∀ stmt tr msg, ¬ toFun m.castSucc stmt tr → ¬ toFun m.succ stmt (tr.concat msg)
  /-- If the state function is false for a full transcript, the verifier will not output a statement
    in the output language -/
  toFun_full : ∀ stmt tr, ¬ toFun (.last n) stmt tr →
    Pr[(· ∈ langOut) | OptionT.mk do (simulateQ impl (verifier.run stmt tr)).run' (← init)] = 0

/-- A state function & a one-shot round-by-round extractor gives rise to a knowledge state function
  where the intermediate witness types are all equal to the input witness type -/
def KnowledgeStateFunctionOneShot.toKnowledgeStateFunction
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    (stF : KnowledgeStateFunctionOneShot init impl relIn.language relOut.language verifier)
    (oneShotE : Extractor.RoundByRoundOneShot oSpec StmtIn WitIn pSpec)
    [hMono : oneShotE.IsMonotone relIn] :
    verifier.KnowledgeStateFunction init impl relIn relOut oneShotE.toRoundByRound where
  toFun := fun m stmtIn tr witIn => if m = 0 then (stmtIn, witIn) ∈ relIn else
    stF.toFun m stmtIn tr ∨ (stmtIn, oneShotE m stmtIn tr default) ∈ relIn
  toFun_empty := fun stmtIn witIn => by
    have := stF.toFun_empty stmtIn
    simp_all
  -- STATEMENT REPAIR (2026-06-04): closed both `toFun_next` field sorries (Blocker-C).
  -- The proof now requires the `[oneShotE.IsMonotone relIn]` instance (added above), whose real
  -- content — round-prefix monotonicity of relation-extraction — is exactly the descent
  -- `(stmtIn, oneShotE m.succ stmtIn (tr.concat msg) default) ∈ relIn`
  --   → `(stmtIn, oneShotE m.castSucc stmtIn tr default) ∈ relIn`.
  -- With the unified `extractMid := E m.castSucc stmtIn (Fin.init tr) default` (see
  -- `toRoundByRound`), the round-0 and round-`>0` cases collapse to this single bridge: the left
  -- disjunct (`stF.toFun`) descends by `stF.toFun_next`, the right disjunct by `IsMonotone`; at
  -- round 0 the left disjunct is impossible because `stF.toFun 0 stmtIn default` is `False`.
  toFun_next := fun m hDir stmtIn tr msg witIn h => by
    simp only [Fin.succ_ne_zero, reduceIte] at h
    have stF_next := stF.toFun_next m hDir stmtIn tr msg
    have hmono := hMono.is_monotone m stmtIn tr msg
    simp only [Extractor.RoundByRoundOneShot.toRoundByRound, Transcript.concat, Fin.init_snoc]
    by_cases hm : m.castSucc = 0
    · rw [if_pos hm]
      rcases h with hstF | hrel
      · exfalso
        -- At round 0 the `stF.toFun` disjunct is impossible: generalize the index to expose the
        -- `Transcript 0` subsingleton, then `stF.toFun 0 stmtIn default` is `False` by
        -- `toFun_empty`.
        have h0 : ¬ stF.toFun m.castSucc stmtIn tr := by
          have key : ∀ (k : Fin (n + 1)), k = 0 → ∀ (t : Transcript k pSpec),
              ¬ stF.toFun k stmtIn t := by
            intro k hk t; subst hk
            have ht : t = default := Subsingleton.elim _ _
            rw [ht]; exact stF.toFun_empty stmtIn
          exact key m.castSucc hm tr
        exact (stF_next h0) hstF
      · exact hmono hrel
    · rw [if_neg hm]
      rcases h with hstF | hrel
      · exact Or.inl (by by_contra hc; exact (stF_next hc) hstF)
      · exact Or.inr (hmono hrel)
  toFun_full := fun stmtIn tr witOut h => by
    let oa : OptionT ProbComp StmtOut := OptionT.mk do
      (simulateQ impl (verifier.run stmtIn tr)).run' (← init)
    have hLangPos : Pr[(· ∈ relOut.language) | oa] > 0 := by
      exact lt_of_lt_of_le h
        (probEvent_mono (mx := oa)
          (p := fun stmtOut => (stmtOut, witOut) ∈ relOut)
          (q := fun stmtOut => stmtOut ∈ relOut.language)
          (fun stmtOut _ hRel => (Set.mem_language_iff relOut stmtOut).2 ⟨witOut, hRel⟩))
    have hstF : stF.toFun (.last n) stmtIn tr := by
      by_contra hnot
      have hzero := stF.toFun_full stmtIn tr hnot
      rw [hzero] at hLangPos
      exact (lt_irrefl 0) hLangPos
    simp only [Extractor.RoundByRoundOneShot.toRoundByRound]
    by_cases hlast0 : (.last n : Fin (n + 1)) = 0
    · rw [if_pos hlast0]
      exfalso
      have hnot : ¬ stF.toFun (.last n) stmtIn tr := by
        have key : ∀ (k : Fin (n + 1)), k = 0 → ∀ (t : Transcript k pSpec),
            ¬ stF.toFun k stmtIn t := by
          intro k hk t
          subst hk
          have ht : t = default := Subsingleton.elim _ _
          rw [ht]
          exact stF.toFun_empty stmtIn
        exact key (.last n) hlast0 tr
      exact hnot hstF
    · rw [if_neg hlast0]
      exact Or.inl hstF

/-- Coercion to the underlying function of a state function -/
instance {langIn : Set StmtIn} {langOut : Set StmtOut}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec} :
    CoeFun (verifier.StateFunction init impl langIn langOut)
    (fun _ => (m : Fin (n + 1)) → StmtIn → Transcript m pSpec → Prop) := ⟨fun f => f.toFun⟩

instance {langIn : Set StmtIn} {langOut : Set StmtOut}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec} :
    CoeFun (KnowledgeStateFunctionOneShot init impl langIn langOut verifier)
    (fun _ => (m : Fin (n + 1)) → StmtIn → Transcript m pSpec → Prop) := ⟨fun f => f.toFun⟩

instance {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec} {WitMid : Fin (n + 1) → Type}
    {extractor : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid} :
    CoeFun (verifier.KnowledgeStateFunction init impl relIn relOut extractor)
    (fun _ => (m : Fin (n + 1)) → StmtIn → Transcript m pSpec → WitMid m → Prop) :=
      ⟨fun f => f.toFun⟩

/-- A protocol with `verifier` satisfies round-by-round soundness with respect to input language
  `langIn`, output language `langOut`, and error `rbrSoundnessError` if:

  - there exists a state function `stateFunction` for the verifier and the input/output languages,
    such that
  - for all initial statement `stmtIn` not in `langIn`,
  - for all initial witness `witIn`,
  - for all provers `prover`,
  - for all `i : Fin n` that is a round corresponding to a challenge,

  the probability that:
  - the state function is false for the partial transcript output by the prover
  - the state function is true for the partial transcript appended by next challenge (chosen
    randomly)

  is at most `rbrSoundnessError i`.
-/
def rbrSoundness (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (rbrSoundnessError : pSpec.ChallengeIdx → ℝ≥0) : Prop :=
  ∃ stateFunction : verifier.StateFunction init impl langIn langOut,
  ∀ stmtIn ∉ langIn,
  ∀ WitIn WitOut : Type,
  ∀ witIn : WitIn,
  ∀ prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec,
  ∀ i : pSpec.ChallengeIdx,
    Pr[fun ⟨transcript, challenge⟩ =>
      ¬ stateFunction i.1.castSucc stmtIn transcript ∧
        stateFunction i.1.succ stmtIn (transcript.concat challenge)
    | do
      (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
        (do
          let ⟨transcript, _⟩ ← prover.runToRound i.1.castSucc stmtIn witIn
          let challenge ← liftComp (pSpec.getChallenge i) _
          return (transcript, challenge))).run' (← init)] ≤
      rbrSoundnessError i

/-- Type class for round-by-round soundness for a verifier

Note that we put the error as a field in the type class to make it easier for synthesization
(often the rbr error will need additional simplification / proof) -/
class IsRBRSound (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec) where
  rbrSoundnessError : pSpec.ChallengeIdx → ℝ≥0
  is_rbr_sound : rbrSoundness init impl langIn langOut verifier rbrSoundnessError

/-- A protocol with `verifier` satisfies round-by-round knowledge soundness with respect to input
  relation `relIn`, output relation `relOut`, and error `rbrKnowledgeError` if:

  - there exists a state function `stateFunction` for the verifier and the languages of the
    input/output relations, such that
  - for all initial statement `stmtIn` not in the language of `relIn`,
  - for all initial witness `witIn`,
  - for all provers `prover`,
  - for all `i : Fin n` that is a round corresponding to a challenge,

  the probability that:
  - the state function is false for the partial transcript output by the prover
  - the state function is true for the partial transcript appended by next challenge (chosen
    randomly)

  is at most `rbrKnowledgeError i`.
-/
-- STATEMENT REPAIR (2026-06-04): bundle the extractor's `IsMonotone` witness into the existential.
-- The conversion to the general `rbrKnowledgeSoundness` (via
-- `KnowledgeStateFunctionOneShot.toKnowledgeStateFunction`) requires the one-shot extractor to be
-- round-prefix monotone (Blocker-C); a one-shot extractor that is *not* monotone does not give rise
-- to a well-formed general knowledge state function, so requiring monotonicity here is the faithful
-- statement of "one-shot rbr knowledge soundness".
def rbrKnowledgeSoundnessOneShot (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0) : Prop :=
  ∃ stateFunction : verifier.KnowledgeStateFunctionOneShot init impl relIn.language relOut.language,
  ∃ extractor : Extractor.RoundByRoundOneShot oSpec StmtIn WitIn pSpec,
  ∃ _ : extractor.IsMonotone relIn,
  ∀ stmtIn : StmtIn,
  ∀ witIn : WitIn,
  ∀ prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec,
  ∀ i : pSpec.ChallengeIdx,
    Pr[fun ⟨transcript, challenge, proveQueryLog⟩ =>
      letI extractedWitIn := extractor i.1.castSucc stmtIn transcript proveQueryLog.fst
      (stmtIn, extractedWitIn) ∉ relIn ∧
        ¬ stateFunction i.1.castSucc stmtIn transcript ∧
          stateFunction i.1.succ stmtIn (transcript.concat challenge)
    | do
      (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
        (do
          let ⟨⟨transcript, _⟩, proveQueryLog⟩ ← prover.runWithLogToRound i.1.castSucc stmtIn witIn
          let challenge ← liftComp (pSpec.getChallenge i) _
          return (transcript, challenge, proveQueryLog))).run' (← init)] ≤
      rbrKnowledgeError i

-- New definition of rbr knowledge soundness, using the knowledge state function
def rbrKnowledgeSoundness (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0) : Prop :=
  ∃ WitMid : Fin (n + 1) → Type,
  ∃ extractor : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid,
  ∃ kSF : verifier.KnowledgeStateFunction init impl relIn relOut extractor,
  ∀ stmtIn : StmtIn,
  ∀ witIn : WitIn,
  ∀ prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec,
  ∀ i : pSpec.ChallengeIdx,
    Pr[fun ⟨transcript, challenge, _proveQueryLog⟩ =>
      ∃ witMid,
        ¬ kSF i.1.castSucc stmtIn transcript
          (extractor.extractMid i.1 stmtIn (transcript.concat challenge) witMid) ∧
          kSF i.1.succ stmtIn (transcript.concat challenge) witMid
    | do
      (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
        (do
          let ⟨⟨transcript, _⟩, proveQueryLog⟩ ← prover.runWithLogToRound i.1.castSucc stmtIn witIn
          let challenge ← liftComp (pSpec.getChallenge i) _
          return (transcript, challenge, proveQueryLog))).run' (← init)] ≤
      rbrKnowledgeError i

/-- Type class for round-by-round knowledge soundness for a verifier

Note that we put the error as a field in the type class to make it easier for synthesization
(often the rbr error will need additional simplification / proof)
-/
class IsRBRKnowledgeSound (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec) where
  rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0
  is_rbr_knowledge_sound : rbrKnowledgeSoundness init impl relIn relOut verifier rbrKnowledgeError

end RoundByRound

end Verifier

open Verifier

section OracleProtocol

variable
  {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type}
  {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type}
  [Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)]
  [∀ i, OracleInterface (pSpec.Message i)]

namespace OracleVerifier

@[reducible, simp]
def StateFunction
    (langIn : Set (StmtIn × ∀ i, OStmtIn i))
    (langOut : Set (StmtOut × ∀ i, OStmtOut i))
    (verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec) :=
  verifier.toVerifier.StateFunction init impl langIn langOut

@[reducible, simp]
def KnowledgeStateFunction
    (relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn))
    (relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut))
    (verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec)
    {WitMid : Fin (n + 1) → Type}
    (extractor : Extractor.RoundByRound oSpec
      (StmtIn × (∀ i, OStmtIn i)) WitIn WitOut pSpec WitMid) :=
  verifier.toVerifier.KnowledgeStateFunction init impl relIn relOut extractor

/-- Round-by-round soundness of an oracle reduction is the same as for non-oracle reductions. -/
def rbrSoundness
    (langIn : Set (StmtIn × ∀ i, OStmtIn i))
    (langOut : Set (StmtOut × ∀ i, OStmtOut i))
    (verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec)
    (rbrSoundnessError : pSpec.ChallengeIdx → ℝ≥0) : Prop :=
  verifier.toVerifier.rbrSoundness init impl langIn langOut rbrSoundnessError

/-- Round-by-round knowledge soundness of an oracle reduction is the same as for non-oracle
reductions. -/
def rbrKnowledgeSoundness
    (relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn))
    (relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut))
    (verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec)
    (rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0) : Prop :=
  verifier.toVerifier.rbrKnowledgeSoundness init impl relIn relOut rbrKnowledgeError

end OracleVerifier

end OracleProtocol

variable {Statement : Type} {ιₛ : Type} {OStatement : ιₛ → Type} {Witness : Type}
  [∀ i, OracleInterface (OStatement i)]
  [∀ i, OracleInterface (pSpec.Message i)]

namespace Proof

@[reducible, simp]
def rbrSoundness (langIn : Set Statement)
    (verifier : Verifier oSpec Statement Bool pSpec)
    (rbrSoundnessError : pSpec.ChallengeIdx → ℝ≥0) : Prop :=
  verifier.rbrSoundness init impl langIn acceptRejectRel.language rbrSoundnessError

@[reducible, simp]
def rbrKnowledgeSoundness (relation : Set (Statement × Bool))
    (verifier : Verifier oSpec Statement Bool pSpec)
    (rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0) : Prop :=
  verifier.rbrKnowledgeSoundness init impl relation acceptRejectRel rbrKnowledgeError

end Proof

namespace OracleProof

/-- Round-by-round soundness of an oracle reduction is the same as for non-oracle reductions. -/
@[reducible, simp]
def rbrSoundness
    (langIn : Set (Statement × ∀ i, OStatement i))
    (verifier : OracleVerifier oSpec Statement OStatement Bool (fun _ : Empty => Unit) pSpec)
    (rbrSoundnessError : pSpec.ChallengeIdx → ℝ≥0) : Prop :=
  verifier.rbrSoundness init impl langIn acceptRejectOracleRel.language rbrSoundnessError

/-- Round-by-round knowledge soundness of an oracle reduction is the same as for non-oracle
reductions. -/
def rbrKnowledgeSoundness
    (relIn : Set ((Statement × ∀ i, OStatement i) × Witness))
    (verifier : OracleVerifier oSpec Statement OStatement Bool (fun _ : Empty => Unit) pSpec)
    (rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0) : Prop :=
  verifier.rbrKnowledgeSoundness init impl relIn acceptRejectOracleRel rbrKnowledgeError

end OracleProof

section Trivial

/-- The state function for the identity / trivial verifier, which just returns whether the
  statement is in the language. -/
def Verifier.StateFunction.id {lang : Set Statement} :
    (Verifier.id : Verifier oSpec Statement _ _).StateFunction init impl lang lang where
  toFun | ⟨0, _⟩ => fun stmtIn _ => stmtIn ∈ lang
  toFun_empty := fun _ => by simp
  toFun_next := fun i => Fin.elim0 i
  toFun_full := fun stmt tr h => by
    simp only [Verifier.id, Verifier.run]
    rw [probEvent_eq_zero_iff]
    intro x hx
    rw [OptionT.mem_support_iff] at hx
    simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hx
    obtain ⟨s, _, hx⟩ := hx
    have key : (simulateQ impl (pure stmt : OptionT (OracleComp oSpec) Statement)).run' s =
        pure (some stmt) := by
      change (simulateQ impl (pure (some stmt) : OracleComp oSpec (Option Statement))).run' s = _
      rw [simulateQ_pure]
      change Prod.fst <$> (pure (some stmt) : StateT σ ProbComp _).run s = _
      rw [StateT.run_pure]; simp [map_pure]
    rw [key] at hx
    simp only [support_pure, Set.mem_singleton_iff] at hx
    cases hx; exact h

/-- The identity / trivial verifier is perfectly round-by-round sound. -/
@[simp]
lemma Verifier.id_rbrSoundness {lang : Set Statement} :
    (Verifier.id : Verifier oSpec Statement _ _).rbrSoundness init impl lang lang 0 := by
  refine ⟨Verifier.StateFunction.id init impl, ?_⟩
  simp [Verifier.id]

/-- The round-by-round extractor for the identity / trivial verifier, which just returns the
  input witness. -/
def Extractor.RoundByRound.id :
    Extractor.RoundByRound oSpec Statement Witness Witness !p[] (fun _ => Witness) where
  eqIn := rfl
  extractMid := fun i => Fin.elim0 i
  extractOut := fun _ _ => _root_.id

/-- The knowledge state function for the identity / trivial verifier, which just returns whether
  the statement is in the relation. -/
def Verifier.KnowledgeStateFunction.id {rel : Set (Statement × Witness)} :
    (Verifier.id : Verifier oSpec Statement _ _).KnowledgeStateFunction init impl rel rel
      (Extractor.RoundByRound.id) where
  toFun | ⟨0, _⟩ => fun stmtIn _ witIn => (stmtIn, witIn) ∈ rel
  toFun_empty := fun _ => by simp
  toFun_next := fun i => Fin.elim0 i
  toFun_full := fun stmtIn tr witOut h => by
    simp only [Verifier.id, Verifier.run] at h
    rw [gt_iff_lt, probEvent_pos_iff] at h
    obtain ⟨x, hx, hrel⟩ := h
    rw [OptionT.mem_support_iff] at hx
    simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hx
    obtain ⟨s, _, hx⟩ := hx
    have key : (simulateQ impl (pure stmtIn : OptionT (OracleComp oSpec) Statement)).run' s =
        pure (some stmtIn) := by
      change (simulateQ impl (pure (some stmtIn) : OracleComp oSpec (Option Statement))).run' s = _
      rw [simulateQ_pure]
      change Prod.fst <$> (pure (some stmtIn) : StateT σ ProbComp _).run s = _
      rw [StateT.run_pure]; simp [map_pure]
    rw [key] at hx
    simp only [support_pure, Set.mem_singleton_iff] at hx
    cases (Option.some.inj hx)
    exact hrel

/-- The identity / trivial verifier is perfectly round-by-round knowledge sound. -/
@[simp]
lemma Verifier.id_rbrKnowledgeSoundness {rel : Set (Statement × Witness)} :
    (Verifier.id : Verifier oSpec Statement _ _).rbrKnowledgeSoundness
      init impl rel rel 0 := by
  refine ⟨_, _, Verifier.KnowledgeStateFunction.id init impl, ?_⟩
  intro stmtIn witIn prover i
  exact Fin.elim0 i.1

/-- The identity / trivial oracle verifier is perfectly round-by-round knowledge sound. -/
@[simp]
lemma OracleVerifier.id_rbrKnowledgeSoundness
    {rel : Set ((Statement × ∀ i, OStatement i) × Witness)} :
    (OracleVerifier.id : OracleVerifier oSpec Statement OStatement _ _ _).rbrKnowledgeSoundness
      init impl rel rel 0 := by
  convert Verifier.id_rbrKnowledgeSoundness init impl (rel := rel)

end Trivial
