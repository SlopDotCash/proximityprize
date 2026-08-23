/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ListDecoding.SubspacePolyGeneralSupport
import ArkLib.ToMathlib.LinearizedHomogeneous

/-!
# The subspace-polynomial evaluation map is 𝔽_q-linear

The repo's `subspacePolyHom` packages `x ↦ P_W(x)` as an additive map.  With the general
linearized-support theorem (`isQPowSupported_subspacePoly'`) and q-power-support ⟹ homogeneity
(`isQPowSupported_eval_smul`), the map is in fact **𝔽_q-linear** — the full statement that `P_W`
is a linearized polynomial (additive *and* 𝔽_q-homogeneous).
-/

open Polynomial BigOperators

namespace BKR06

variable {F : Type*} [Field F] [Fintype F]
variable {K : Type*} [Field K] [DecidableEq K] [Algebra F K]

/-- **The subspace-polynomial evaluation map is 𝔽_q-linear.** `x ↦ P_W(x)` as a `K →ₗ[F] K`,
upgrading `subspacePolyHom` (additivity) with 𝔽_q-homogeneity from the linearized-support theorem. -/
noncomputable def subspacePolyLinearMap (W : Submodule F K) [Fintype W] : K →ₗ[F] K where
  toFun x := (subspacePoly (subFinset W)).eval x
  map_add' x y := subspacePoly_eval_add_submodule W x y
  map_smul' c x := by
    simp only [RingHom.id_apply]
    rw [Algebra.smul_def, Algebra.smul_def]
    exact ArkLib.LinearizedKernel.isQPowSupported_eval_smul
      (isQPowSupported_subspacePoly' W) c x

@[simp] lemma subspacePolyLinearMap_apply (W : Submodule F K) [Fintype W] (x : K) :
    subspacePolyLinearMap W x = (subspacePoly (subFinset W)).eval x := rfl

end BKR06

-- Axiom audit.
#print axioms BKR06.subspacePolyLinearMap
