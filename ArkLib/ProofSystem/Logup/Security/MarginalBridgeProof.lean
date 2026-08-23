/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Security.RbrToSoundBridge
import ArkLib.OracleReduction.RunUnroll
import ArkLib.OracleReduction.ProcessRoundSupport

/-!
# Discharging the MarginalBridge residual (issue #13)

Proof of `Verifier.MarginalBridge` (the rbr→soundness per-round marginal domination) from the
proven trailing-drop + union-bound infrastructure in `Security/RoundByRound.lean`, under the
single **state-preservation side condition** `hso` on the shared-oracle implementation (the same
side condition the sequential-composition seam toolkit `probComp_seam_swap_union_le` consumes,
dischargeable for the LogUp instantiations via `OptionTStateT.addLift_state_preserving`).

## Why `hso` is necessary (the statement is FALSE without it)

`StateFunction.toFun_full` bounds the verifier-accept probability only over runs started from a
*fresh* `init` state.  The full soundness run threads the implementation state from the prover
interaction into the verifier.  For a state-*mutating* `impl` the two need not agree: take
`σ := Bool`, `init := pure false`, an oracle answering with its current state and setting it to
`true`, a verifier accepting iff the answer is `true`, and a 1-round (`P_to_V`-only) protocol
whose malicious prover queries the oracle once.  Then the all-false state function satisfies
every `StateFunction` field (from `init` the verifier always rejects), `pSpec.ChallengeIdx` is
empty so `∑ i, rbrGameFlipProb … i = 0`, yet the full run accepts with probability `1`.  Hence
the unconditional `MarginalBridge` is false, and `hso` (every query implementation returns the
state it was given, on its support) is the honest minimal repair: it pins the post-prover state
back to the `init` sample, which is exactly the seam `toFun_full` needs.

## Structure

* `probEvent_simulateQ_run'_optionMap_const_trailing_le` — trailing drop for an `Option`-valued
  trailing stage whose successful value is constant in the trailing output (the verifier/`getM`
  tail of the soundness run, after marginalizing the event to the transcript).
* `Prover.continueFromTo_take_support` — the rounds after `k` preserve the round-`k` transcript
  prefix on the support (folds `processRound_support_restrict`).
* `Transcript.concat_take_eq` — taking back the length-`k` prefix of `concat` returns the input.
* `Verifier.reduction_run_run_nf` — `(Reduction.run …).run` in prover-stage/verifier-stage
  normal form with the only genuine `Option` short-circuit absorbed into an `Option.map`.
* `Verifier.fullRun_flip_marginal_le_rbrGameFlipProb` — the per-round trailing-drop core: the
  full-run flip marginal is dominated by the round-by-round game's flip probability
  (unconditional; no `hso` needed).
* `Verifier.marginalBridge_holds` — the assembly: union bound + first-crossing pigeonhole + the
  `hso`-gated `toFun_full` contradiction.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal ENNReal

section Bricks

variable {ι' : Type} {spec : OracleSpec ι'} {σ' : Type}

/-- **Trailing drop for an `Option`-valued trailing stage with prefix-constant success value.**
After the prefix `mx` produces `a`, the run executes a trailing (possibly-failing,
possibly-`none`-returning) `gb a` whose output is kept only through `Option.map (fun _ => h a)` —
i.e. the final *success* value is the prefix-determined `h a`, and the trailing stage contributes
only its success/failure verdict.  Dropping the trailing stage (and the `Option` layer) can only
raise the probability of an event that is `False` on `none`. -/
theorem probEvent_simulateQ_run'_optionMap_const_trailing_le {α β γ : Type}
    (so : QueryImpl spec (StateT σ' ProbComp)) (s : σ')
    (mx : OracleComp spec α) (gb : α → OracleComp spec (Option γ)) (h : α → β) (p : β → Prop) :
    Pr[fun o : Option β => o.elim False p |
        (simulateQ so (mx >>= fun a => gb a >>= fun og =>
          (pure (Option.map (fun _ => h a) og) : OracleComp spec (Option β)))).run' s]
      ≤ Pr[p | (simulateQ so (mx >>= fun a => (pure (h a) : OracleComp spec β))).run' s] := by
  classical
  simp only [simulateQ_bind]
  rw [StateT.run'_eq, StateT.run'_eq, StateT.run_bind, StateT.run_bind]
  rw [probEvent_map, probEvent_map]
  refine Verifier.StateFunction.probEvent_bind_mono_heteroEvent (fun pr _ => ?_)
  obtain ⟨a, s'⟩ := pr
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure]
  by_cases hpa : p (h a)
  · refine le_trans probEvent_le_one (le_of_eq ?_)
    rw [probEvent_pure_eq_indicator]
    simp [Set.indicator, Function.comp, hpa]
  · rw [probEvent_pure_eq_indicator]
    simp only [Set.indicator, Set.mem_setOf_eq, Function.comp_apply, hpa, if_false,
      nonpos_iff_eq_zero]
    rw [probEvent_eq_zero_iff]
    rintro ⟨o, s''⟩ ho
    rw [mem_support_bind_iff] at ho
    obtain ⟨q, _, hq⟩ := ho
    simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hq
    obtain ⟨rfl, rfl⟩ := hq
    cases hq1 : q.1 with
    | none => simp [hq1]
    | some c => simp [hq1, hpa]

/-- **Trailing drop for an arbitrary `Option`-valued trailing stage under a prefix-stable event.**
After the prefix `mx` produces `a`, the run executes a trailing (arbitrary, possibly-failing,
possibly-`none`-returning) `gb a` whose *successful* output `b` is the final result.  The final event
`p` on the trailing output need not be constant, but it is **prefix-stable**: any successful trailing
output `b` that satisfies `p` forces the prefix-determined event `q (g a)` (`hstable`).  Dropping the
trailing stage entirely (and projecting to the prefix value `g a`) can therefore only raise the
event probability.  This is the failure/prefix-monotone trailing drop the full-run flip marginal
needs: the round-`i` flip event reads only the round-`i.succ` transcript prefix, which is fixed by
`(rk, c)` before the trailing rounds run. -/
theorem probEvent_simulateQ_run'_trailing_eventStable_le {α β ρ : Type}
    (so : QueryImpl spec (StateT σ' ProbComp)) (s : σ')
    (mx : OracleComp spec α) (gb : α → OracleComp spec (Option β))
    (g : α → ρ) (p : β → Prop) (q : ρ → Prop)
    (hstable : ∀ a, ∀ o ∈ support (gb a), ∀ b, o = some b → p b → q (g a)) :
    Pr[fun o : Option β => o.elim False p |
        (simulateQ so (mx >>= fun a => gb a)).run' s]
      ≤ Pr[q | (simulateQ so (mx >>= fun a => (pure (g a) : OracleComp spec ρ))).run' s] := by
  classical
  simp only [simulateQ_bind]
  rw [StateT.run'_eq, StateT.run'_eq, StateT.run_bind, StateT.run_bind]
  rw [probEvent_map, probEvent_map]
  refine Verifier.StateFunction.probEvent_bind_mono_heteroEvent (fun pr _ => ?_)
  obtain ⟨a, s'⟩ := pr
  simp only [simulateQ_pure, StateT.run_pure]
  by_cases hqa : q (g a)
  · refine le_trans probEvent_le_one (le_of_eq ?_)
    rw [probEvent_pure_eq_indicator]
    simp [Set.indicator, Function.comp, hqa]
  · rw [probEvent_pure_eq_indicator]
    simp only [Set.indicator, Set.mem_setOf_eq, Function.comp_apply, hqa, if_false,
      nonpos_iff_eq_zero]
    rw [probEvent_eq_zero_iff]
    rintro ⟨o, s''⟩ ho
    rw [Function.comp]
    cases o' : o with
    | none => simp
    | some b =>
      simp only [Option.elim_some]
      intro hpb
      -- `some b` is a successful output of `(simulateQ so (gb a)).run s'`, hence of `gb a`.
      have hb_supp : o ∈ support ((simulateQ so (gb a)).run' s') := by
        rw [StateT.run'_eq, support_map, Set.mem_image]
        exact ⟨(o, s''), ho, rfl⟩
      rw [o'] at hb_supp
      have hb_raw : some b ∈ support (gb a) :=
        _root_.support_simulateQ_run'_subset so (gb a) s' hb_supp
      exact hqa (hstable a (some b) hb_raw b rfl hpb)

end Bricks

namespace Prover

variable {ι : Type} {oSpec : OracleSpec ι} {n : ℕ} {pSpec : ProtocolSpec n}
  {StmtIn WitIn StmtOut WitOut : Type}

/-- **The rounds after `k` preserve the round-`k` transcript prefix on the support.**  Folded
version of `processRound_support_restrict`: every support output of the continuation
`continueFromTo k j` (for `k ≤ j`) restricts, on the first `k` rounds, to the input transcript. -/
theorem continueFromTo_take_support
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn) (k j : Fin (n + 1)) (hkj : k ≤ j)
    (a : pSpec.Transcript k × prover.PrvState k)
    (b : pSpec.Transcript j × prover.PrvState j)
    (hb : b ∈ support (prover.continueFromTo stmt wit k j a)) :
    (b.1.take k.val (by exact_mod_cast hkj) : pSpec.Transcript k) = a.1 := by
  induction j using Fin.induction with
  | zero =>
    have hk0 : k = 0 := le_antisymm hkj (Fin.zero_le _)
    subst hk0
    exact Subsingleton.elim (α := pSpec.Transcript 0) _ _
  | succ m ih =>
    by_cases hk : k = m.succ
    · subst hk
      rw [continueFromTo_self, support_pure, Set.mem_singleton_iff] at hb
      subst hb
      rfl
    · have hk' : k ≤ m.castSucc := by
        rw [Fin.le_castSucc_iff]
        exact lt_of_le_of_ne hkj hk
      rw [continueFromTo_succ_of_ne prover stmt wit k m hk a] at hb
      obtain ⟨ts, hts, hpres⟩ := processRound_support_restrict m prover _ b hb
      have hIH := ih hk' ts hts
      funext jj
      have hidx := hpres (Fin.castLE (by exact_mod_cast hk') jj)
      have hIH' := congrFun hIH jj
      exact hidx.trans hIH'

end Prover

namespace ProtocolSpec.Transcript

variable {n : ℕ} {pSpec : ProtocolSpec n}

/-- Taking back the length-`i.castSucc` prefix of `concat` recovers the input transcript. -/
theorem concat_take_eq (i : Fin n) (t : Transcript i.castSucc pSpec) (ch : pSpec.«Type» i) :
    (((t.concat ch : Transcript i.succ pSpec)).take i.castSucc.val
        (by simp [Fin.le_def]) : Transcript i.castSucc pSpec) = t := by
  funext j
  exact Fin.snoc_castSucc (α := fun k : Fin (i.1 + 1) =>
    pSpec.«Type» (Fin.castLE i.succ.is_le k)) ch t j

end ProtocolSpec.Transcript

namespace Verifier

open StateFunction OptionTStateT Prover

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn StmtOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

omit [∀ i, SampleableType (pSpec.Challenge i)] in
/-- **`(Reduction.run …).run` in two-stage normal form.**  The full soundness run is: the prover's
(plain, never-failing) run, then the (lifted) verifier run, with the only genuine `Option`
short-circuit (`getM`) absorbed into an `Option.map` of the final pairing. -/
theorem reduction_run_run_nf {WitIn WitOut : Type}
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn) :
    ((Reduction.mk prover verifier).run stmtIn witIn).run
      = prover.run stmtIn witIn >>= fun pr =>
          (OracleComp.liftComp ((verifier.run stmtIn pr.1).run) (oSpec + [pSpec.Challenge]ₒ))
            >>= fun o =>
          (pure (o.map (fun v => (pr, v))) :
            OracleComp (oSpec + [pSpec.Challenge]ₒ)
              (Option ((FullTranscript pSpec × StmtOut × WitOut) × StmtOut))) := by
  rw [Reduction_run_def]
  simp only [OptionT.run_bind, Option.elimM, OptionTStateT.lift_run_elim, OptionT.run_pure]
  refine bind_congr fun x => bind_congr fun o => ?_
  cases o <;> rfl

variable {WitIn WitOut : Type}

/-- **Per-round trailing-drop core (per state).**  Fix an `init` sample `s` and a challenge round
`i`.  The full soundness run's round-`i` flip marginal (the event that `sf` is false on the round-`i`
transcript prefix but true once the round-`i` challenge is appended) is dominated by the
round-by-round game's flip probability run from the same state `s`.

The full run factors as `runToRound i.castSucc >>= fun rk => getChallenge i >>= fun c => TRAILING`,
where `TRAILING` threads `receiveChallenge`, rounds `i+1 .. last`, the prover output, and the
verifier; the flip event reads only the round-`i.castSucc` prefix and the round-`i` challenge `c`
(transcript-prefix stability via `continueFromTo_take_support` / `concat_take_eq`), so the trailing
steps (failure-monotone) only raise the event probability. -/
theorem fullRun_flip_marginal_le_rbrGameFlipProb
    {langIn : Set StmtIn} {langOut : Set StmtOut}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    (sf : verifier.StateFunction init impl langIn langOut)
    (witIn : WitIn) (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmtIn : StmtIn) (i : pSpec.ChallengeIdx) (s : σ) :
    Pr[fun o : Option ((FullTranscript pSpec × StmtOut × WitOut) × StmtOut) => o.elim False
        (fun x => ¬ sf i.1.castSucc stmtIn (x.1.1.take i.1.castSucc.val i.1.castSucc.is_le) ∧
          sf i.1.succ stmtIn (x.1.1.take i.1.succ.val i.1.succ.is_le))
        | (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
            (Reduction.run stmtIn witIn { prover := prover, verifier := verifier }).run).run' s]
      ≤ Pr[fun p : pSpec.Transcript i.1.castSucc × pSpec.Challenge i =>
          ¬ sf i.1.castSucc stmtIn p.1 ∧ sf i.1.succ stmtIn (p.1.concat p.2)
        | (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
            (do
              let ⟨transcript, _⟩ ← prover.runToRound i.1.castSucc stmtIn witIn
              let challenge ← liftComp (pSpec.getChallenge i) _
              return (transcript, challenge))).run' s] := by
  -- Decompose `prover.run` to expose `runToRound i.castSucc >>= processRound i`.
  have hle₁ : i.1.castSucc ≤ Fin.last n := Fin.le_last _
  have hdecomp :
      ((Reduction.run stmtIn witIn { prover := prover, verifier := verifier }).run)
        = prover.runToRound i.1.castSucc stmtIn witIn >>= fun rk =>
            (continueFromTo prover stmtIn witIn i.1.castSucc (Fin.last n) rk >>= fun rl =>
              liftM (prover.output rl.2) >>= fun out =>
                (liftM ((verifier.run stmtIn rl.1).run) >>= fun o =>
                  pure (o.map (fun v => ((rl.1, out), v))))) := by
    rw [reduction_run_run_nf, run_eq_runToRound_last,
      runToRound_eq_bind_continueFromTo prover stmtIn witIn i.1.castSucc (Fin.last n) hle₁]
    simp only [bind_assoc, pure_bind, OracleComp.liftComp_eq_liftM]
    rfl
  -- Expose the round-`i` challenge: `continueFromTo i.castSucc (last n) rk` factors (via
  -- `continueFromTo_trans` + `continueFromTo_succ_of_ne` + `processRound_challenge`) as
  -- `getChallenge i >>= receiveChallenge >>= continueFromTo i.succ (last n)`.
  have hsucc_le : i.1.succ ≤ Fin.last n := by
    rw [Fin.le_def, Fin.val_succ, Fin.val_last]; exact i.1.isLt
  have hcs_le_succ : i.1.castSucc ≤ i.1.succ := by
    rw [Fin.le_def, Fin.val_castSucc, Fin.val_succ]; omega
  have hne : (i.1.castSucc : Fin (n + 1)) ≠ i.1.succ := by
    rw [Ne, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]; omega
  have hcft : ∀ rk : pSpec.Transcript i.1.castSucc × prover.PrvState i.1.castSucc,
      continueFromTo prover stmtIn witIn i.1.castSucc (Fin.last n) rk
        = (prover.processRound i.1 (pure rk) >>=
            continueFromTo prover stmtIn witIn i.1.succ (Fin.last n)) := by
    intro rk
    rw [continueFromTo_trans prover stmtIn witIn i.1.castSucc i.1.succ (Fin.last n)
      hcs_le_succ hsucc_le rk]
    rw [continueFromTo_succ_of_ne prover stmtIn witIn i.1.castSucc i.1 hne rk,
      continueFromTo_self]
  -- TRAILING-DROP residual: with `hdecomp` (run = `runToRound i.castSucc >>= continueFromTo …`) and
  -- `hcft` (`continueFromTo i.castSucc = processRound i >>= continueFromTo i.succ`), and
  -- `processRound_challenge` exposing `getChallenge i`, the round-`i` flip event reads only the
  -- round-`i.castSucc` prefix + round-`i` challenge — fixed before the trailing
  -- (receiveChallenge / rounds `i+1..last` / output / verifier) steps, which are stable on the
  -- prefix by `continueFromTo_take_support` / `concat_take_eq`. The failure-monotone trailing drop
  -- `probEvent_simulateQ_run'_optionMap_const_trailing_le` then bounds the full-run marginal by the
  -- game's, with the round-`i` challenge matched via the challenge-coherence
  -- `ChallengeCoherence.run'_simulateQ_addLift_getChallenge_bind`.
  rw [hdecomp]
  simp only [hcft, processRound_challenge, bind_assoc, pure_bind, OracleComp.liftComp_eq_liftM]
  have hbrick := probEvent_simulateQ_run'_trailing_eventStable_le
      (so := impl.addLift challengeQueryImpl) (s := s)
      (mx := prover.runToRound i.1.castSucc stmtIn witIn >>= fun rk =>
        (liftM (pSpec.getChallenge i) : OracleComp _ _) >>= fun c => pure (rk, c))
      (gb := fun a : (pSpec.Transcript i.1.castSucc × prover.PrvState i.1.castSucc) × pSpec.Challenge i =>
        liftM (prover.receiveChallenge i a.1.2) >>= fun rcv =>
          continueFromTo prover stmtIn witIn i.1.succ (Fin.last n)
              (Transcript.concat a.2 a.1.1, rcv a.2) >>= fun rl =>
            liftM (prover.output rl.2) >>= fun out =>
              liftM ((verifier.run stmtIn rl.1).run) >>= fun o =>
                pure (Option.map (fun v => ((rl.1, out), v)) o))
      (g := fun a => (a.1.1, a.2))
      (p := fun x => ¬ sf i.1.castSucc stmtIn (x.1.1.take i.1.castSucc.val i.1.castSucc.is_le) ∧
        sf i.1.succ stmtIn (x.1.1.take i.1.succ.val i.1.succ.is_le))
      (q := fun pp => ¬ sf i.1.castSucc stmtIn pp.1 ∧ sf i.1.succ stmtIn (Transcript.concat pp.2 pp.1))
      ?hstable
  simp only [bind_assoc, pure_bind] at hbrick
  refine le_trans hbrick ?rhseq
  case rhseq => exact le_refl _
  case hstable =>
    rintro ⟨rk, c⟩ o ho b hob hpb
    simp only at ho hpb ⊢
    -- Chase the support membership down to `rl ∈ support (continueFromTo i.succ last (concat c rk.1, …))`
    rw [mem_support_bind_iff] at ho
    obtain ⟨rcv, _hrcv, ho⟩ := ho
    rw [mem_support_bind_iff] at ho
    obtain ⟨rl, hrl, ho⟩ := ho
    rw [mem_support_bind_iff] at ho
    obtain ⟨out, _hout, ho⟩ := ho
    rw [mem_support_bind_iff] at ho
    obtain ⟨vo, _hvo, ho⟩ := ho
    rw [support_pure, Set.mem_singleton_iff] at ho
    -- `o = some b` with `o = Option.map (fun v => ((rl.1, out), v)) vo`.
    subst hob
    -- so `vo = some v` and `b = ((rl.1, out), v)`, hence `b.1.1 = rl.1`.
    cases hvocase : vo with
    | none => rw [hvocase, Option.map_none] at ho; exact absurd ho.symm (by simp)
    | some v =>
      rw [hvocase, Option.map_some, Option.some.injEq] at ho
      subst ho
      -- round-`i.succ` prefix of `rl.1` equals the continueFromTo input `concat c rk.1`.
      have hsucc_pref := Prover.continueFromTo_take_support prover stmtIn witIn
        i.1.succ (Fin.last n) hsucc_le (Transcript.concat c rk.1, rcv c) rl hrl
      simp only at hsucc_pref hpb ⊢
      -- The round-`i.succ` prefix of `rl.1`.
      have hsucc_eq : (FullTranscript.take i.1.succ.val i.1.succ.is_le rl.1
            : Transcript i.1.succ pSpec) = Transcript.concat c rk.1 := hsucc_pref
      -- The round-`i.castSucc` prefix of `rl.1` (read off pointwise from the `i.succ` prefix).
      have hcs_eq : (FullTranscript.take i.1.castSucc.val i.1.castSucc.is_le rl.1
            : Transcript i.1.castSucc pSpec) = rk.1 := by
        -- Pointwise: the cs-prefix of `rl.1` is the cs-prefix of its succ-prefix `concat c rk.1`,
        -- which is `rk.1` (concat back to length cs recovers the input).
        have hconcat := ProtocolSpec.Transcript.concat_take_eq i.1 rk.1 c
        funext j
        have hj := congrFun hsucc_eq (Fin.castLE (by simp [Fin.le_def]) j)
        have hjc := congrFun hconcat j
        simp only [FullTranscript.take, Fin.take] at hj hjc ⊢
        rw [← hjc]
        exact hj
      exact ⟨hcs_eq ▸ hpb.1, hsucc_eq ▸ hpb.2⟩

/-- **The `MarginalBridge` residual of the rbr→soundness bridge (issue #13).**  Under the
state-preservation / non-failure / value-blindness side conditions on the shared-oracle
implementation (the standard honest-`impl` conditions, supplied by the downstream consumer
`Logup.issue13_soundness_msgSeam`), the full honest soundness run's accept probability is dominated
by the sum, over challenge rounds, of the round-by-round game's per-round flip probabilities.

The proof is the union bound: the first-crossing pigeonhole (`exists_challenge_flip_of_full`) shows
an accepting run on a bad statement must flip the state function `false → true` at some challenge
round (the `false`-at-`0` base is `stmtIn ∉ langIn`; the `true`-at-last is forced by the
contrapositive of `toFun_full`, whose verifier-marginal-positivity contradiction is discharged by
state-independence from the threaded post-prover state back to the `init` sample — the role of
`himplSP`/`himplVB`); and each per-round full-run flip marginal is dominated by the game's flip
probability via the trailing-drop `fullRun_flip_marginal_le_rbrGameFlipProb`. -/
theorem marginalBridge_holds {langIn : Set StmtIn} {langOut : Set StmtOut}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {rbrSoundnessError : pSpec.ChallengeIdx → ℝ≥0}
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    (himplVB : ∀ (t : oSpec.Domain) (s s' : σ),
      evalDist ((impl t).run' s) = evalDist ((impl t).run' s')) :
    MarginalBridge init impl langIn langOut verifier rbrSoundnessError := by
  classical
  intro sf hPerRound WitIn WitOut witIn prover stmtIn hStmtIn
  show fullRunAcceptProb init impl langOut verifier witIn prover stmtIn ≤
    ∑ i : pSpec.ChallengeIdx, rbrGameFlipProb init impl sf witIn prover stmtIn i
  refine le_trans
    (probEvent_le_sum_of_imp_exists _ _
      (fun (i : pSpec.ChallengeIdx) (x : (FullTranscript pSpec × StmtOut × WitOut) × StmtOut) =>
        ¬ sf i.1.castSucc stmtIn (x.1.1.take i.1.castSucc.val i.1.castSucc.is_le) ∧
          sf i.1.succ stmtIn (x.1.1.take i.1.succ.val i.1.succ.is_le))
      ?himp)
    (Finset.sum_le_sum (fun i _ => ?trailing))
  case himp =>
    intro x _hx hAccept
    have hlast : sf.toFun (Fin.last n) stmtIn
        (x.1.1.take (Fin.last n).val (Fin.last n).is_le) := by
      by_contra hns
      have hzero := sf.toFun_full stmtIn (x.1.1.take (Fin.last n).val (Fin.last n).is_le) hns
      -- Decompose the full-run support membership `_hx`.
      rw [OptionT.mem_support_iff, OptionT.run_mk, mem_support_bind_iff] at _hx
      obtain ⟨s, hs, hxs⟩ := _hx
      set soL : QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp) :=
        impl.addLift challengeQueryImpl with hsoL
      -- View `Reduction.run` (via `Reduction_run_def`) as the prover stage bound to the verifier
      -- check `verifier.verify` (the `getM` is already cancelled by `Reduction_run_def`).
      rw [Reduction_run_def] at hxs
      rw [OptionTStateT.simulateQ_run'_optionT_bind_run, mem_support_bind_iff] at hxs
      obtain ⟨pr, hpr, hxpr⟩ := hxs
      -- `some x` came from the success branch, so the prover produced `some a`.
      obtain ⟨po, sp⟩ := pr
      cases hpo : po with
      | none => rw [hpo] at hxpr; simp only [Option.elim_none, support_pure] at hxpr; simp at hxpr
      | some a =>
        rw [hpo] at hxpr
        simp only [Option.elim_some] at hxpr
        -- The verifier stage is `(fun v => (a, v)) <$> liftM (verifier.verify stmtIn a.1)`.
        have hverEq :
            ((liftM (verifier.verify stmtIn a.1) :
                  OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ)) StmtOut) >>= fun vOut =>
                (pure (a, vOut) : OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ)) _))
            = ((fun v => (a, v)) <$> (liftM (verifier.verify stmtIn a.1) :
                  OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ)) StmtOut)) := by
          simp only [bind_pure_comp]
        rw [hverEq] at hxpr
        -- Reduce the lifted-verifier simulation to the bare-`impl` verifier marginal.
        rw [hsoL] at hxpr
        rw [OptionT.run_map, simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map] at hxpr
        -- `(liftM X).run = liftM X.run`, then the lifted simulation reduces to `simulateQ impl`.
        rw [show ((liftM (verifier.verify stmtIn a.1) :
              OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ)) StmtOut)).run
            = (liftM ((verifier.verify stmtIn a.1).run) :
              OracleComp (oSpec + [pSpec.Challenge]ₒ) (Option StmtOut)) from rfl] at hxpr
        rw [QueryImpl.addLift_def, QueryImpl.liftTarget_self,
          simulateQ_addLift_liftM] at hxpr
        -- Extract: the verifier marginal at state `sp` produces `some sout` with `x = (a, sout)`.
        rw [support_map, Set.mem_image] at hxpr
        obtain ⟨⟨vo, sv⟩, hvo, hxeq⟩ := hxpr
        simp only at hxeq
        -- `some x = Option.map (a, ·) vo`, so `vo = some sout` and `x = (a, sout)`.
        cases hvocase : vo with
        | none => rw [hvocase] at hxeq; simp at hxeq
        | some sout =>
          rw [hvocase] at hxeq hvo
          simp only [Option.map_some, Option.some.injEq] at hxeq
          -- `hxeq : (a, sout) = x`, `hvo : (some sout, sv) ∈ verifier marginal at sp`.
          have hxa : x.1.1 = a.1 := by rw [← hxeq]
          have hAccept' : x.2 ∈ langOut := hAccept
          have hsoutLang : sout ∈ langOut := by
            have hx2 : x.2 = sout := by rw [← hxeq]
            rwa [hx2] at hAccept'
          -- The verifier marginal at `sp` produces `some sout ∈ langOut`, so its `langOut`-prob > 0.
          set evP : Option StmtOut → Prop := fun o => Option.elim o False (· ∈ langOut) with hevP
          have hpos_sp : 0 < Pr[evP
              | (simulateQ impl (verifier.verify stmtIn a.1).run).run' sp] := by
            rw [probEvent_pos_iff]
            refine ⟨some sout, ?_, hsoutLang⟩
            rw [StateT.run'_eq, support_map, Set.mem_image]
            exact ⟨(some sout, sv), hvo, rfl⟩
          -- State-independence: the verifier value-distribution at `sp` equals that at `s`.
          have hstateIndep := evalDist_simulateQ_run'_state_indep impl himplSP himplVB
            (verifier.verify stmtIn a.1).run sp s
          have hpos_s : 0 < Pr[evP
              | (simulateQ impl (verifier.verify stmtIn a.1).run).run' s] := by
            have heq : Pr[evP | (simulateQ impl (verifier.verify stmtIn a.1).run).run' sp]
                = Pr[evP | (simulateQ impl (verifier.verify stmtIn a.1).run).run' s] := by
              unfold probEvent; rw [hstateIndep]
            rwa [heq] at hpos_sp
          -- The take-form transcript in `hzero` equals `x.1.1 = a.1`; `verifier.run = verifier.verify`.
          have htake : (FullTranscript.take (Fin.last n).val (Fin.last n).is_le x.1.1
                : Transcript (Fin.last n) pSpec) = x.1.1 := by
            simp only [FullTranscript.take, Fin.val_last]; exact Fin.take_eq_self _
          rw [htake] at hzero
          rw [Verifier.run, hxa, probEvent_optionT_mk] at hzero
          rw [show (fun o => Option.elim o False (· ∈ langOut)) = evP from rfl] at hzero
          -- `hzero` averages over `init`; the `s`-contribution is positive, contradiction.
          have hpos_init : 0 < Pr[evP
              | init >>= fun s' => (simulateQ impl (verifier.verify stmtIn a.1).run).run' s'] := by
            rw [probEvent_bind_eq_tsum]
            refine lt_of_lt_of_le ?_ (ENNReal.le_tsum s)
            have hsval : 0 < Pr[= s | init] := by rw [probOutput_pos_iff]; exact hs
            exact ENNReal.mul_pos (ne_of_gt hsval) (ne_of_gt hpos_s)
          exact absurd hzero (ne_of_gt hpos_init)
    obtain ⟨i, hcast, hsucc⟩ := exists_challenge_flip_of_full init impl sf stmtIn hStmtIn x.1.1 hlast
    exact ⟨i, hcast, by rw [take_succ_eq_concat]; exact hsucc⟩
  case trailing =>
    -- Reduce the LHS to the `run'`/`Option.elim` shape; unfold the game on the RHS; then apply the
    -- per-round trailing-drop core.
    rw [probEvent_optionT_mk, rbrGameFlipProb]
    refine probEvent_bind_mono_heteroEvent (fun s _hs => ?_)
    exact fullRun_flip_marginal_le_rbrGameFlipProb sf witIn prover stmtIn i s

end Verifier
