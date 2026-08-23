/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToVCVio.OracleComp.SimSemantics.SimulateQ

/-!
# `simulateQ` over a subsingleton state distributes over bind

When the simulator state type `σ` is a `Subsingleton` (e.g. `Unit`), the threaded state is forced
equal at every step, so the final-value projection `StateT.run'` of a bind splits into a bind of the
projections. Consequently `simulateQ impl` of a bind, evaluated with `run'`, distributes over the
bind — there is no state-ordering dependence between the two halves.

This is the key fact that makes sequential-composition completeness reasoning tractable for
stateless / public-coin simulators: the obstruction to commuting an intervening computation past a
later one vanishes when the carried state is a subsingleton.
-/

open OracleComp

/-- For a `Subsingleton` state, `StateT.run'` of a bind splits into a bind of the projections. -/
theorem StateT.run'_bind_of_subsingleton {σ : Type} [Subsingleton σ] {M : Type → Type}
    [Monad M] [LawfulMonad M] {α β : Type} (ma : StateT σ M α) (g : α → StateT σ M β) (s : σ) :
    (ma >>= g).run' s = ma.run' s >>= fun x => (g x).run' s := by
  simp only [StateT.run'_eq, StateT.run_bind, map_bind, bind_map_left]
  refine bind_congr fun p => ?_
  rw [Subsingleton.elim p.2 s]

/-- For a `Subsingleton` state, `simulateQ impl` evaluated with `run'` distributes over bind. -/
theorem simulateQ_run'_bind_of_subsingleton {ι σ α β : Type} {spec : OracleSpec ι}
    [Subsingleton σ] (impl : QueryImpl spec (StateT σ ProbComp))
    (a : OracleComp spec α) (b : α → OracleComp spec β) (s : σ) :
    (simulateQ impl (a >>= b)).run' s
      = (simulateQ impl a).run' s >>= fun x => (simulateQ impl (b x)).run' s := by
  rw [simulateQ_bind]
  exact StateT.run'_bind_of_subsingleton _ _ s
