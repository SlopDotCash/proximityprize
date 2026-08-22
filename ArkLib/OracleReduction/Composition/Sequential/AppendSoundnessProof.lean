/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.SeamDecompositionRun
import ArkLib.OracleReduction.Composition.Sequential.ChallengeSeamBridge
import ArkLib.OracleReduction.Composition.Sequential.SeamCompleteness

/-!
# Sequential-composition soundness: the seam stage-swap under a leading bind

This file builds toward `Verifier.append_soundness` (the soundness half of the #433 keystone). The
soundness experiment runs the malicious prover fully first (`fst` then `snd`), then the composed
verifier (`V₁` then `V₂`): order `fst, snd, V₁, V₂`. To apply the two-stage union bound
`probComp_seam_union_le` (the bad event `stmtOut ∈ lang₃` factors through the intermediate
`stmt₂ ∈ lang₂`) the experiment must be regrouped as `(fst ≫ V₁) ≫ (snd ≫ V₂)`: the `snd`
prover stage and the `V₁` verifier stage must be swapped.

Under a **state-preserving** oracle implementation (`hso`; the soundness analogue of the
completeness proof's `hImplSupp`, discharged for `impl.addLift challengeQueryImpl` by
`OptionTStateT.addLift_state_preserving`), the two stages are distributionally independent and
commute. `OptionTStateT.evalDist_simulateQ_swap` performs the top-level swap; this file lifts it
to a swap **under a leading bind** (the `fst` stage), which is the shape the appended run has.

## Verified reduction recipe (toward `Verifier.append_soundness`)

The appended soundness run reduces to the exact swap-canonical form. With
`so := impl.addLift challengeQueryImpl` and `hso := addLift_state_preserving impl himplSP`:

1. **Run factoring** (verified): for the malicious prover `prover` over `pSpec₁ ++ₚ pSpec₂`,
   `((Reduction.mk prover (V₁.append V₂)).run stmtIn witIn).run` rewrites — via
   `Reduction.run`, `Prover.run_seam_factor prover hn hDir hDir₂`, `Verifier.append_run`, and the
   `simp only` set
   `[OptionT.run_bind, bind_assoc, Option.elimM, map_bind, OptionT.run_liftM_run,
     OptionT.run_pure, Option.getM, liftM_bind, Option.elim_some, OptionT.run_mk, bind_pure_comp,
     OptionT.run_lift, OptionT.run_monadLift, monadLift_eq_self, bind_map_left, Functor.map_map,
     FullTranscript.append_fst, FullTranscript.append_snd]`
   — to the plain `OracleComp` chain
   `P >>= fun x => A x >>= fun a => B x >>= fun b => k x a b`, where
   `P = liftM (prover.fst.run stmtIn witIn)`, `A x = liftM (prover.snd.run x.2.1 x.2.2)`,
   `B x = simulateQ idLift (V₁.run stmtIn x.1).run` (the `Option Stmt₂` from `V₁`), and `k`
   short-circuits on `b`, runs `V₂`, and assembles the output. (The `append_fst`/`append_snd`
   rewrites make `B` depend only on `x`, the shape `evalDist_simulateQ_swap_under` requires.)
2. **Swap** (this file): `evalDist_simulateQ_swap_under so hso P A B k s` commutes `A` (snd) and `B`
   (V₁), giving `P >>= fun x => B x >>= fun b => A x >>= fun a => k x a b` — the clean
   `fst, V₁, snd, V₂` order.
3. **Elim-commute**: `OptionTStateT.probEvent_elim_comm` moves the never-failing `snd` stage into
   the `some`-branch of `V₁`'s short-circuit, matching `(mxClean >>= myClean).run` for
   `mxClean = fst ≫ V₁`, `myClean = snd ≫ V₂`.
4. **Union bound**: `OracleReduction.probComp_seam_union_le` on `mxClean >>= myClean` with
   `pg = (· ∉ lang₂)`, `qg = (· ∉ lang₃)`, reducing the two stage hypotheses to soundness
   (`h₁`/`h₂`) on `prover.fst`/`prover.snd` via the proven challenge-seam bridges.

Steps 1–2 are verified; 3–4 plus the two stage-soundness bounds remain. The deliverable carries
the state-preservation/value-blind `impl` side-conditions (`himplSP`, discharged for the actual
`impl.addLift challengeQueryImpl` by `addLift_state_preserving`) — the soundness analogue of the
completeness proof's `hImplSupp`.
-/

open OracleComp OracleSpec ProtocolSpec OptionTStateT
open scoped ENNReal

universe u v

/-- **`OptionT.mk` event = `Option.elim`-bad event on the underlying computation.** Bridges the
soundness goal `Pr[p | OptionT.mk M]` (a `probEvent` over `OptionT m`) to the `ProbComp (Option _)`
form `Pr[fun o => Option.elim o False p | M]` consumed by `probComp_seam_union_le` (whose bad-event
predicate is `¬ Option.elim · True qg = Option.elim · False (¬qg)`). `none` (failure) does not
satisfy `p`, matching the soundness convention. -/
lemma probEvent_optionT_mk_eq_elim {m : Type u → Type v} [Monad m] [HasEvalSPMF m] {α : Type u}
    (M : m (Option α)) (p : α → Prop) :
    Pr[p | (OptionT.mk M : OptionT m α)] = Pr[fun o => Option.elim o False p | M] := by
  classical
  rw [probEvent_eq_tsum_indicator, probEvent_eq_tsum_indicator, tsum_option _ ENNReal.summable]
  simp only [Set.indicator_apply, Set.mem_setOf_eq, Option.elim_none, Option.elim_some,
    if_false, zero_add]
  refine tsum_congr fun a => ?_
  simp only [OptionT.probOutput_eq, OptionT.run_mk]
  split_ifs <;> rfl

namespace OptionTStateT

variable {ι : Type} {spec : OracleSpec ι} {σ : Type}

/-- **Seam stage swap under a leading bind.** Generalises `evalDist_simulateQ_swap` to swap the two
inner stages `A`, `B` that sit underneath a leading stage `P` whose output `r` both inner stages may
depend on. Under state-preservation (`hso`) every stage runs from the same starting state, so the
`A`/`B` binds commute (`SPMF.bind_comm`). This is the exact shape of the appended soundness run:
`P = fst` prover, `A = snd` prover, `B = V₁`, and `k` finishes with `V₂` and the output. -/
theorem evalDist_simulateQ_swap_under
    (so : QueryImpl spec (StateT σ ProbComp))
    (hso : ∀ (t : spec.Domain) (s : σ) (x : spec.Range t × σ),
      x ∈ support ((so t).run s) → x.2 = s)
    {ρ α β γ : Type}
    (P : OracleComp spec ρ)
    (A : ρ → OracleComp spec α) (B : ρ → OracleComp spec β)
    (k : ρ → α → β → OracleComp spec γ) (s : σ) :
    evalDist ((simulateQ so (P >>= fun r => A r >>= fun a => B r >>= fun b => k r a b)).run' s)
      = evalDist ((simulateQ so (P >>= fun r => B r >>= fun b => A r >>= fun a => k r a b)).run' s)
        := by
  rw [StateT.run'_eq, StateT.run'_eq, evalDist_map, evalDist_map]
  congr 1
  simp only [simulateQ_run_bind_state_fixed so hso, evalDist_bind]
  refine bind_congr fun p => ?_
  exact SPMF.bind_comm _ _ _

end OptionTStateT

namespace Prover

variable {ι : Type} {oSpec : OracleSpec ι}
  {Stmt₁ Wit₁ Stmt₂ Stmt₃ Wit₃ : Type} {m n : ℕ}
  {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

/-- **Phase-1 soundness prover.** `Prover.fst P` re-typed so its output *statement* is `Stmt₂`
(the type `V₁` outputs, junk value `default`) and its output *witness* carries the seam state
(needed to resume in phase 2). Shares the interaction fields with `Prover.fst P`, so it reproduces
the phase-1 transcript exactly (`runToRound` is definitionally equal). The re-typing is needed
because `Reduction.mk (Prover.fst P) V₁` is ill-typed — a `Reduction` forces the prover and
verifier output statements to coincide, but `Prover.fst P` outputs the seam state. Soundness sees
only the *verifier's* output, so the junk prover statement is harmless. -/
def fstSound [Inhabited Stmt₂]
    (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂)) :
    Prover oSpec Stmt₁ Wit₁ Stmt₂
      (P.PrvState (Fin.castLE (show m + 1 ≤ m + n + 1 by omega) (Fin.last m))) pSpec₁ where
  PrvState := (Prover.fst P).PrvState
  input := (Prover.fst P).input
  sendMessage := (Prover.fst P).sendMessage
  receiveChallenge := (Prover.fst P).receiveChallenge
  output := fun state => pure (default, state)

/-- **Phase-2 soundness prover.** `Prover.snd P` re-typed so its input *statement* is `Stmt₂` (the
type `V₂` takes, ignored) and the real seam state is the input *witness*. Shares the interaction
with `Prover.snd P`, so it reproduces `P`'s phase-2 transcript exactly. Used with `V₂` soundness
per seam-state value (the `∀ a ∈ support` slot of `probComp_seam_union_le`). -/
def sndSound
    (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂)) :
    Prover oSpec Stmt₂
      (P.PrvState (Fin.castLE (show m + 1 ≤ m + n + 1 by omega) (Fin.last m)))
      Stmt₃ Wit₃ pSpec₂ where
  PrvState := (Prover.snd P).PrvState
  input := fun p => (Prover.snd P).input ⟨p.2, ()⟩
  sendMessage := (Prover.snd P).sendMessage
  receiveChallenge := (Prover.snd P).receiveChallenge
  output := (Prover.snd P).output

/-- `fstSound` reproduces `Prover.fst`'s per-round run (same interaction fields). -/
@[simp] theorem fstSound_runToRound [Inhabited Stmt₂]
    (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂)) (i) (stmt : Stmt₁) (wit : Wit₁) :
    (fstSound (Stmt₂ := Stmt₂) P).runToRound i stmt wit = (Prover.fst P).runToRound i stmt wit :=
  rfl

/-- `sndSound` reproduces `Prover.snd`'s per-round run, on the seam state supplied as witness. -/
@[simp] theorem sndSound_runToRound
    (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂)) (i) (stmt : Stmt₂)
    (wit : P.PrvState (Fin.castLE (show m + 1 ≤ m + n + 1 by omega) (Fin.last m))) :
    (sndSound (Stmt₂ := Stmt₂) P).runToRound i stmt wit = (Prover.snd P).runToRound i wit () :=
  rfl

end Prover
