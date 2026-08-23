/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import VCVio.OracleComp.SimSemantics.SimulateQ
import VCVio.OracleComp.SimSemantics.Append

/-!
# Query Simulation Functoriality and Routing in Nested Oracle Specifications

This module establishes key distributive and routing properties of query simulation
(`simulateQ`) over monadic structures. Specifically:

1. **Multi-Stage Query Routing**: `simulateQ_addLift_add_liftM_left` and
   `simulateQ_addLift_add_liftM_right` analyze the behavior of `simulateQ` under nested
   direct-sum oracle specifications of the form `spec + (spec₁ + spec₂)`. They prove that
   queries double-lifted from a component specification route directly to the corresponding
   sub-implementation under the target monad `m`, bypassing intermediate lift layers.
-/

open OracleComp OracleSpec

/-- Commute query simulation with double-lifting in a nested oracle sum:
`spec + (spec₁ + spec₂)`. A computation originating in `spec₁` that is double-lifted
routes directly to the left sub-implementation `impl₁` under the query implementation
`QueryImpl.addLift impl (QueryImpl.add impl₁ impl₂)`. -/
lemma simulateQ_addLift_add_liftM_left
    {ι ι₁ ι₂ : Type} {spec : OracleSpec ι} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {m : Type → Type} [Monad m] [LawfulMonad m]
    {n : Type → Type} [Monad n] [LawfulMonad n] [MonadLiftT n m] [LawfulMonadLiftT n m]
    (impl : QueryImpl spec m) (impl₁ : QueryImpl spec₁ n) (impl₂ : QueryImpl spec₂ n)
    {α : Type} (x : OracleComp spec₁ α) :
    simulateQ (QueryImpl.addLift impl (QueryImpl.add impl₁ impl₂)
        : QueryImpl (spec + (spec₁ + spec₂)) m)
      (liftM (liftM x : OracleComp (spec₁ + spec₂) α) : OracleComp (spec + (spec₁ + spec₂)) α)
      = (liftM (simulateQ impl₁ x) : m α) := by
  rw [show QueryImpl.add impl₁ impl₂ = impl₁ + impl₂ from rfl,
    ← OracleComp.liftComp_eq_liftM, ← OracleComp.liftComp_eq_liftM,
    QueryImpl.addLift_def, QueryImpl.simulateQ_add_liftComp_right,
    simulateQ_liftTarget, QueryImpl.simulateQ_add_liftComp_left]

/-- Commute query simulation with double-lifting in a nested oracle sum:
`spec + (spec₁ + spec₂)`. A computation originating in `spec₂` that is double-lifted
routes directly to the right sub-implementation `impl₂` under the query implementation
`QueryImpl.addLift impl (QueryImpl.add impl₁ impl₂)`. -/
lemma simulateQ_addLift_add_liftM_right
    {ι ι₁ ι₂ : Type} {spec : OracleSpec ι} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {m : Type → Type} [Monad m] [LawfulMonad m]
    {n : Type → Type} [Monad n] [LawfulMonad n] [MonadLiftT n m] [LawfulMonadLiftT n m]
    (impl : QueryImpl spec m) (impl₁ : QueryImpl spec₁ n) (impl₂ : QueryImpl spec₂ n)
    {α : Type} (x : OracleComp spec₂ α) :
    simulateQ (QueryImpl.addLift impl (QueryImpl.add impl₁ impl₂)
        : QueryImpl (spec + (spec₁ + spec₂)) m)
      (liftM (liftM x : OracleComp (spec₁ + spec₂) α) : OracleComp (spec + (spec₁ + spec₂)) α)
      = (liftM (simulateQ impl₂ x) : m α) := by
  rw [show QueryImpl.add impl₁ impl₂ = impl₁ + impl₂ from rfl,
    ← OracleComp.liftComp_eq_liftM, ← OracleComp.liftComp_eq_liftM,
    QueryImpl.addLift_def, QueryImpl.simulateQ_add_liftComp_right,
    simulateQ_liftTarget, QueryImpl.simulateQ_add_liftComp_right]
