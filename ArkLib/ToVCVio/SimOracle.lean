/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import VCVio

/-!
# Formalization of Simulation Oracles and Query Transformations

In interactive proof systems and cryptographic reductions, a *simulation oracle*
mediates between two query-response interfaces by translating queries from a source
specification to actions within a target computational monad.

This module provides support for structured query transformations, represented via
`QueryImpl`. Specifically, it handles cases where the target monad is itself an
`OracleComp` (possibly state-passing via `StateT`), capturing the algebraic structure
of game-theoretic security reductions (e.g., simulating a random oracle or a
protocol adversary).
-/

universe u v

open OracleComp OracleSpec

variable {ι ι' ιₜ : Type*} {spec : OracleSpec ι}
    {spec' : OracleSpec ι'} {specₜ : OracleSpec ιₜ}
    {m : Type u → Type v} {α β γ σ : Type u}
