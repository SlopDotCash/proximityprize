/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Spartan.Basic

/-!
# First sum-check (zero-check) virtual-polynomial degree bound (issue #114)

The Spartan first phase reduces the R1CS zero-check to a sum-check over the virtual polynomial
`zeroCheckVirtualPolynomial = ∑ₓ eqPolynomial(x) · C(A𝕫·B𝕫−C𝕫 value)`. This module proves it is
multilinear (degree ≤ 1 in each variable): each summand is a scalar multiple of a multilinear
`eqPolynomial`, and `R⦃≤1⦄[X _]` is a submodule. This is the first-phase analogue of
`secondSCVP_mem_restrictDegree`, packaging the virtual polynomial as a degree-≤1 sum-check oracle —
a construction ingredient for the first sum-check oracle reduction.
-/

open MvPolynomial

namespace Spartan.Spec

variable {R : Type} [CommRing R] (pp : Spartan.PublicParams)

/-- **First sum-check (zero-check) virtual polynomial degree bound.** The zero-check virtual
polynomial is multilinear (degree ≤ 1 per variable). -/
theorem zeroCheckVirtualPolynomial_mem_restrictDegree
    (𝕩 : Statement.AfterFirstMessage R pp)
    (oStmt : ∀ i, OracleStatement.AfterFirstMessage R pp i) :
    zeroCheckVirtualPolynomial R pp 𝕩 oStmt ∈ R⦃≤ 1⦄[X Fin pp.ℓ_m] := by
  unfold zeroCheckVirtualPolynomial
  apply Submodule.sum_mem
  intro x _
  rw [mul_comm, C_mul']
  exact Submodule.smul_mem _ _ (eqPolynomial_mem_restrictDegree _)

end Spartan.Spec
