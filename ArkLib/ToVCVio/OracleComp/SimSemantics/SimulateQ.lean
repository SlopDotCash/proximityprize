/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import VCVio.OracleComp.SimSemantics.StateT.Measure
import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
import VCVio.OracleComp.SimSemantics.StateT.Basic

/-!
# Additions to VCV-io's `OracleComp.SimSemantics.SimulateQ`
-/

open OracleSpec OracleComp

universe u v

lemma support_simulateQ_run'_subset
    {ι σ α : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT σ ProbComp)) (oa : OracleComp spec α) (s : σ) :
    support ((simulateQ impl oa).run' s) ⊆ support oa :=
  OracleComp.support_simulateQ_run'_subset impl oa s

/-- If all outputs of the original `OracleComp` are successful and satisfy `P`, then the
    simulated `OptionT` computation satisfies `P` with probability one. -/
lemma OptionT.probEvent_eq_one_of_simulateQ_support
    {ι σ α : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT σ ProbComp))
    (oa : OracleComp spec (Option α)) (s₀ : σ) (P : α → Prop)
    (h : ∀ x ∈ support oa, ∃ a, x = some a ∧ P a) :
    Pr{let a ← OptionT.mk ((simulateQ impl oa).run' s₀)}[P a] = 1 := by
  simpa using OptionT.prEvent_mk_simulateQ_run'_eq_one_of_support (pure s₀) impl oa P h

/-- **`simulateQ` fusion.** Simulating an `OracleComp spec₁` through an intermediate implementation
`R : QueryImpl spec₁ (OracleComp spec₂)` and then simulating the result through
`S : QueryImpl spec₂ m` equals simulating directly through the *composed* per-query handler
`fun q => simulateQ S (R q)`. This is functoriality of `simulateQ` in its implementation argument —
the universal-fold fusion law for the free monad `OracleComp`. It is the key step that lets a
two-stage routed run (e.g. the appended `OracleVerifier.Append.verify`, which is
`simulateQ router₁ … >>= simulateQ (router₂ …) …`) be re-expressed as a single direct simulation,
collapsing the outer-oracle simulation through the routers. -/
theorem simulateQ_simulateQ {ι₁ ι₂ : Type*}
    {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {m : Type u → Type v} [Monad m] [LawfulMonad m]
    (R : QueryImpl spec₁ (OracleComp spec₂)) (S : QueryImpl spec₂ m)
    {α : Type u} (c : OracleComp spec₁ α) :
    simulateQ S (simulateQ R c) = simulateQ (fun q => simulateQ S (R q)) c := by
  exact QueryImpl.simulateQ_simulateQ_eq_of_apply (fun _ => rfl) c
