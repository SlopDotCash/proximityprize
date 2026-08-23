/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ListDecoding.SubspacePolyKernel

/-!
# The subspace polynomial is a faithful invariant of 𝔽_q-subspaces

Distinct finite `𝔽_q`-subspaces have distinct subspace polynomials: `subspacePoly ∘ subFinset` is
injective on subspaces.  Immediate from `ker (subspacePolyLinearMap W) = W` — the polynomial
determines the linearized map, whose kernel recovers `W`.
-/

open Polynomial BigOperators

namespace BKR06

variable {F : Type*} [Field F] [Fintype F]
variable {K : Type*} [Field K] [DecidableEq K] [Algebra F K]

/-- **Faithfulness.** Equal subspace polynomials ⇒ equal subspaces. -/
theorem subspacePoly_subFinset_inj {W₁ W₂ : Submodule F K} [Fintype W₁] [Fintype W₂]
    (h : subspacePoly (subFinset W₁) = subspacePoly (subFinset W₂)) : W₁ = W₂ := by
  have hmap : subspacePolyLinearMap W₁ = subspacePolyLinearMap W₂ := by
    ext x; simp only [subspacePolyLinearMap_apply, h]
  rw [← ker_subspacePolyLinearMap W₁, ← ker_subspacePolyLinearMap W₂, hmap]

end BKR06

-- Axiom audit.
#print axioms BKR06.subspacePoly_subFinset_inj
