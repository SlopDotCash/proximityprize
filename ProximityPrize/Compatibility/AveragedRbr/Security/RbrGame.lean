/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.OracleReduction.Security.RbrGame

/-!
# Historical prover-averaged round-by-round contracts

These declarations preserve downstream proofs of the prover-averaged game.
They come from ArkLib 1040ed0e6f208de9afd1a1aa56888ccd830c0964 before #1421.
-/

section

open OracleComp OracleSpec ProtocolSpec ProbabilityTheory

open scoped ENNReal

open Probability

namespace ProtocolSpec

variable {n : ℕ} {pSpec : ProtocolSpec n} [∀ j, SampleableType (pSpec.Challenge j)]
  {ι : Type} {oSpec : OracleSpec ι} {σ : Type}

/-- **Master mixture bound for the rbr game shape.** If, for every *fixed* output `tr` of the
(adversarial, arbitrary) simulated prover run `oa`, the event holds over a fresh uniform
challenge with probability at most `ε`, then the whole game probability — initial state
sampled from `init`, prover run simulated under `impl.addLift challengeQueryImpl`, challenge
obtained via `liftComp (pSpec.getChallenge i) _` — is at most `ε`.

`f` packages the game's `return` expression (e.g. `fun tr c ↦ (tr.1.1, c, tr.2)` for
`rbrKnowledgeSoundnessAveraged`); when applying this lemma to a game whose `do`-block destructures
the prover output, pass `f` explicitly and use `exact` (the match-lambdas agree only up to
definitional structure eta). -/
theorem prEvent_simulateQ_addLift_getChallenge_bind_le
    {T β : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (oa : OracleComp (oSpec + [pSpec.Challenge]ₒ) T) (i : pSpec.ChallengeIdx)
    (f : T → pSpec.Challenge i → β) (E : β → Prop) {ε : ℝ≥0∞}
    (h : ∀ tr : T, Pr{let c ← $ᵗ (pSpec.Challenge i)}[E (f tr c)] ≤ ε) :
    Pr{let x ← (do
      (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
        (do
          let tr ← oa
          let challenge ← liftComp (pSpec.getChallenge i) (oSpec + [pSpec.Challenge]ₒ)
          return f tr challenge)).run' (← init))}[E x] ≤ ε := by
  refine prEvent_bind_le_of_forall_le init _ E fun s ↦ ?_
  rw [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  refine prEvent_bind_le_of_forall_le _ _ E fun x ↦ ?_
  rw [prEvent_map, simulateQ_bind, simulateQ_addLift_challengeQueryImpl_getChallenge,
    StateT.run_bind]
  simpa only [simulateQ_pure, StateT.run_monadLift, StateT.run_pure, bind_pure_comp,
    Functor.map_map, monadLift_self] using h x.1

end ProtocolSpec

end
