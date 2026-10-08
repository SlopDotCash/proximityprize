/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ToVCVio.EvalDist.Instances.OptionT
import ArkLib.ToVCVio.OracleComp.Coercions.SubSpec
import ArkLib.ToVCVio.ToMathlib.Control.StateT
import VCVio.EvalDist.Defs.NeverFails
import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
import VCVio.OracleComp.SimSemantics.StateT.Basic

/-!
# Additions to VCV-io's `OracleComp.SimSemantics.SimulateQ`
-/

open OracleSpec OracleComp

universe u v

-- `simulateQ_randomOracle_map_uniformFin` is provided by the pinned VCVio dependency.

lemma support_simulateQ_run'_subset
    {ι σ α : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT σ ProbComp)) (oa : OracleComp spec α) (s : σ) :
    support ((simulateQ impl oa).run' s) ⊆ support oa := by
  intro y hy
  induction oa using OracleComp.inductionOn generalizing y s with
  | pure x =>
      simpa [simulateQ_pure, StateT.run'_eq, StateT.run_pure] using hy
  | query_bind t oa ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, StateT.run'_eq, StateT.run_bind, support_map,
        Set.mem_image, support_bind, Set.mem_iUnion] at hy ⊢
      aesop

-- OptionT support/probability transport and StateT map/bind transport now come from VCVio.

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
  induction c using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t oa ih =>
    simp only [simulateQ_bind, simulateQ_spec_query]
    exact bind_congr ih
