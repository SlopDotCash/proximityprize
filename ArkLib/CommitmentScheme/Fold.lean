/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Commitments.Functional.Basic
import Batteries.Data.Vector.Basic
import ArkLib.OracleReduction.OracleInterface
import Mathlib.Data.FinEnum
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import ArkLib.Data.CodingTheory.ProximityGap.Basic

/-!
# Folding-based Polynomial Commitment Schemes

This module is the commitment-scheme namespace for IOP-based polynomial folding frameworks such
as FRI, Circle-FRI, Binius, and BaseFold. ArkLib currently develops the concrete protocol objects
and proofs for those systems under `ProofSystem`; this file intentionally stays as the
commitment-layer import surface until a shared folding-commitment API is factored out of those
protocol-specific developments.
-/
