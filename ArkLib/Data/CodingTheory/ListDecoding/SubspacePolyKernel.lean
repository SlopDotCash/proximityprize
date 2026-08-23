/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ListDecoding.SubspacePolyLinearMap

/-!
# Kernel of the linearized subspace-polynomial map

The 𝔽_q-linear map `subspacePolyLinearMap W` (`x ↦ P_W(x)`) has kernel exactly `W`: its roots are
precisely the subspace.  This packages "P_W vanishes exactly on W" as the linear-algebra statement
`ker (subspacePolyLinearMap W) = W` — the linearized polynomial whose root space is `W`.
-/

open Polynomial BigOperators

namespace BKR06

variable {F : Type*} [Field F] [Fintype F]
variable {K : Type*} [Field K] [DecidableEq K] [Algebra F K]

/-- **The kernel of the linearized subspace-polynomial map is `W`.** -/
theorem ker_subspacePolyLinearMap (W : Submodule F K) [Fintype W] :
    LinearMap.ker (subspacePolyLinearMap W) = W := by
  ext x
  simp only [LinearMap.mem_ker, subspacePolyLinearMap_apply]
  constructor
  · intro h
    exact mem_subFinset.mp ((subspacePoly_isRoot_iff (subFinset W) x).mp h)
  · intro h
    exact (subspacePoly_isRoot_iff (subFinset W) x).mpr (mem_subFinset.mpr h)

end BKR06

-- Axiom audit.
#print axioms BKR06.ker_subspacePolyLinearMap
