/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ListDecoding.SubspacePolyKernel

/-!
# Rank of the linearized subspace-polynomial map

By rank–nullity and `ker (subspacePolyLinearMap W) = W`, the 𝔽_q-linear map `x ↦ P_W(x)` has
`rank = dim_𝔽 K − dim_𝔽 W`.  For `K = 𝔽_{q^m}` and `dim W = v`, the image is an `(m − v)`-dimensional
𝔽_q-subspace — the linearized polynomial's range.
-/

open Polynomial BigOperators

namespace BKR06

variable {F : Type*} [Field F] [Fintype F]
variable {K : Type*} [Field K] [DecidableEq K] [Algebra F K] [FiniteDimensional F K]

/-- **Rank of the linearized subspace-polynomial map.** `dim (range P_W) = dim K − dim W`. -/
theorem finrank_range_subspacePolyLinearMap (W : Submodule F K) [Fintype W] :
    Module.finrank F (LinearMap.range (subspacePolyLinearMap W))
      = Module.finrank F K - Module.finrank F W := by
  have h := (subspacePolyLinearMap W).finrank_range_add_finrank_ker
  rw [ker_subspacePolyLinearMap] at h
  omega

end BKR06

-- Axiom audit.
#print axioms BKR06.finrank_range_subspacePolyLinearMap
