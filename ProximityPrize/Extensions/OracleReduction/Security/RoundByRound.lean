/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ProximityPrize.Compatibility.DiscreteProbability
import ArkLib.OracleReduction.Security.RoundByRound

/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ProximityPrize.Extensions.OracleReduction.Security.Basic
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

namespace RoundByRoundOneShot

end RoundByRoundOneShot

end Extractor

namespace Verifier

section RoundByRound

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
theorem probEvent_exists_mem_le_sum {m : Type → Type*} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] {α : Type}
    {κ : Type} [DecidableEq κ] (mx : m α) (p : κ → α → Prop) (s : Finset κ) :
    probEvent (fun x => ∃ i ∈ s, p i x) (mx) ≤ ∑ i ∈ s, probEvent (fun x => p i x) (mx) := by
  exact prEvent_exists_finset_le s mx p

/-- **Union bound over a fintype of indices.**  Specialization of `probEvent_exists_mem_le_sum` to
the full (finite) index type, e.g. `pSpec.ChallengeIdx`.  The probability that *some* index
satisfies its event is at most the total sum of per-index probabilities — the form used to bound a
soundness error by `∑ i, rbrSoundnessError i`. -/
theorem probEvent_exists_le_sum {m : Type → Type*} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] {α : Type}
    {κ : Type} [Fintype κ] [DecidableEq κ] (mx : m α) (p : κ → α → Prop) :
    probEvent (fun x => ∃ i, p i x) (mx) ≤ ∑ i : κ, probEvent (fun x => p i x) (mx) := by
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
theorem probEvent_le_sum_of_imp_exists {m : Type → Type*} [Monad m] [LawfulMonad m]
    [MonadAttach m] [ExactMonadAttach m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] {α : Type}
    {κ : Type} [Fintype κ] [DecidableEq κ] (mx : m α) (q : α → Prop) (p : κ → α → Prop)
    (himp : ∀ x ∈ support mx, q x → ∃ i, p i x) :
    probEvent (q) (mx) ≤ ∑ i : κ, probEvent (fun x => p i x) (mx) := by
  exact (prEvent_mono_of_support mx q (fun x => ∃ i, p i x) himp).trans
    (prEvent_exists_le mx p)

/-- **Failure-monotone trailing bind.**  Appending a (possibly-failing) computation `gb x` *before*
returning a value `h x` that does not depend on `gb x`'s output can only *decrease* the probability
of any event: the trailing computation contributes only extra failure mass.

This is the reusable probabilistic core of the `rbrSoundness → soundness` marginal bridge: the full
prover run threads the trailing `receiveChallenge`/`sendMessage`/`output` and verifier steps, which
the round-by-round game omits; since the per-round flip event depends only on the transcript prefix
(already determined before those steps), dropping them can only raise the event probability —
turning the marginal relation into the `≤` direction needed to chain to `rbrSoundnessError`. -/
theorem probEvent_bind_trailing_le {m : Type → Type*} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α β γ : Type} (mx : m α) (gb : α → m γ) (h : α → β) (p : β → Prop) :
    probEvent (p) (mx >>= fun x => gb x >>= fun _ => pure (h x)) ≤ probEvent (p) (mx >>= fun x => pure (h x)) := by
  exact prEvent_bind_mono_of_forall_le mx _ _ p p fun x =>
    prEvent_bind_le_of_forall_le (gb x) _ p fun _ => le_rfl

/-- **`OptionT` probEvent as a success-conjunction on the underlying computation.**  An
`OptionT ProbComp` event probability equals the probability, on the underlying
`ProbComp (Option α)`, of *succeeding with* a value satisfying `p` (failure `none` does NOT count
toward the event).  This is the characterization the `rbrSoundness → soundness` per-round bound
consumes: the soundness game's
flip event must hold on a genuine (non-failing) verifier accept, so failure mass introduced by
trailing computations only *lowers* the event probability (the failure-monotone direction). -/
theorem probEvent_optionT_mk_eq_elim {α : Type}
    (ma : ProbComp (Option α)) (p : α → Prop) :
    probEvent (p) ((OptionT.mk ma : OptionT ProbComp α)) = probEvent (fun o => o.elim False p) (ma) := by
  exact OptionT.prEvent_eq_run (OptionT.mk ma) p

/-- **Heterogeneous bind-monotone over a shared prefix.**  A `probEvent_bind_mono_heteroEvent` variant that
allows the post-bind events to differ (different result types `β`, `β'` and predicates `q`, `q'`):
if on the support of the shared prefix `mx` each per-element event probability of `q` under `my x`
is
bounded by that of `q'` under `oc x`, then so are the bound probabilities.  Used to chain the
soundness game's flip event (on the `Option`-wrapped full result) to the round-by-round game's flip
event (on the `(transcript, challenge)` pair), both threaded over the shared `init` sample. -/
theorem probEvent_bind_mono_heteroEvent {m : Type → Type*} [Monad m] [LawfulMonad m]
    [MonadAttach m] [ExactMonadAttach m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α β β' : Type} {mx : m α} {my : α → m β} {oc : α → m β'} {q : β → Prop} {q' : β' → Prop}
    (h : ∀ x ∈ support mx, probEvent (q) (my x) ≤ probEvent (q') (oc x)) :
    probEvent (q) (mx >>= my) ≤ probEvent (q') (mx >>= oc) := by
  exact prEvent_bind_mono_of_forall_le_of_support mx my oc q q' h

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
    probEvent (p) ((simulateQ so (mx >>= fun a => gb a >>= fun _ => (pure (h a) : OracleComp spec β))).run' s)
      ≤ probEvent (p) ((simulateQ so (mx >>= fun a => (pure (h a) : OracleComp spec β))).run' s) := by
  simp only [simulateQ_bind]
  rw [StateT.run'_eq, StateT.run'_eq, StateT.run_bind, StateT.run_bind]
  simp only [probEvent, prEvent_map]
  refine probEvent_bind_mono_heteroEvent (fun pr _ => ?_)
  obtain ⟨a, s'⟩ := pr
  simp only [simulateQ_pure, StateT.run_pure, StateT.run_bind]
  apply prEvent_bind_le_of_forall_le
  intro q
  simp only [probEvent, map_pure, le_refl]

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
    probEvent (fun o => o.elim False p) ((simulateQ so (ma >>= fun oa => Option.elimM (pure oa) (pure none) cont)).run' s)
      ≤ probEvent (fun o => o.elim False p) ((simulateQ so (ma >>= fun oa => pure (Option.map h oa))).run' s) := by
  classical
  simp only [simulateQ_bind]
  rw [StateT.run'_eq, StateT.run'_eq, StateT.run_bind, StateT.run_bind]
  simp only [probEvent, prEvent_map]
  refine probEvent_bind_mono_heteroEvent (fun pr _ => ?_)
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
        simp only [probEvent, map_pure, prEvent_pure_prop, Option.elim_some, hpha,
          ite_true]
        exact prEvent_le_one _
      · -- ¬ p (h a): show LHS = 0 (no success of `cont a` satisfies `p`).
        simp only [probEvent, map_pure, prEvent_pure_prop, Option.elim_some, hpha,
          ite_false, nonpos_iff_eq_zero]
        apply prEvent_eq_zero_of_forall_mem_support
        intro o ho
        -- `o` is a successful run of `cont a`; by `hcont`, its event value forces `p (h a)`.
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
    probEvent (fun o => o.elim False p) ((simulateQ so (ma >>= fun oa => Option.elimM (pure oa) (pure none)
          (fun a => k a >>= fun _ => pure (some (h a))))).run' s)
      ≤ probEvent (fun o => o.elim False p) ((simulateQ so (ma >>= fun oa => pure (Option.map h oa))).run' s) := by
  apply probEvent_simulateQ_run'_optionBind_trailing_le so s ma
    (fun a => k a >>= fun _ => pure (some (h a))) h p
  intro a b hb b' hbb hp
  rcases _root_.support_bind_exists hb with ⟨c, _, hc⟩
  have hbval : b = some (h a) := _root_.eq_of_mem_support_pure hc
  have heq : b' = h a := Option.some.inj (hbb.symm.trans hbval)
  simpa only [heq] using hp

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
    exact fun h => hStmtIn (sf.toFun_empty stmtIn h)
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

end OracleVerifier

end OracleProtocol

variable {Statement : Type} {ιₛ : Type} {OStatement : ιₛ → Type} {Witness : Type}
  [∀ i, OracleInterface (OStatement i)]
  [∀ i, OracleInterface (pSpec.Message i)]

namespace Proof

end Proof

namespace OracleProof

end OracleProof

section Trivial

end Trivial
