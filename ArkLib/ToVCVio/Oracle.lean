/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import VCVio.OracleComp.QueryTracking.CachingOracle

/-!
# Deterministic Query Implementations

This module formalizes deterministic query implementations for oracle specifications.
Specifically, it defines:

1. `OracleSpec.FunctionType`: A query implementation `QueryImpl spec Id` that resolves
   queries in `spec` without invoking any further interactive steps (i.e., mapping queries
   directly to values in the identity monad `Id`).

2. `runWithOracle`: A evaluation function that runs an oracle computation `OracleComp spec α`
   against a deterministic oracle implementation `f`, producing a pure value of type `α`.
   This is equivalent to simulating the computation in `Id` and running the identity monad.
-/

open OracleSpec OracleComp

universe u v

variable {ι : Type} {α β γ : Type} {spec : OracleSpec ι}

/-- A deterministic implementation of the oracle interface specified by `spec`,
mapping queries directly to responses without invoking further oracles. -/
def OracleSpec.FunctionType (spec : OracleSpec ι) := QueryImpl spec Id

/-- Evaluate an oracle computation `OracleComp spec α` against a deterministic oracle
implementation `f : spec.FunctionType`, returning the final result of type `α`. -/
def runWithOracle (f : spec.FunctionType) : OracleComp spec α → α :=
  fun mx => Id.run <| simulateQ f mx

/-- The empty oracle spec is (vacuously) inhabited: it has no oracles, hence no domains. -/
instance : OracleSpec.Inhabited []ₒ where
  inhabited_B := fun t => PEmpty.elim t
