/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Spartan.Basic

/-!
# Zero-check completeness: `𝒢 = 0` on R1CS-satisfying instances (issue #114)

The Spartan first sum-check tests whether the virtual zero-check polynomial
`𝒢 = zeroCheckVirtualPolynomial = ∑_x eq(x) · C((A𝕫)(x)·(B𝕫)(x) − (C𝕫)(x))` is identically zero.
This module proves the *completeness* direction: on any instance satisfying the R1CS relation
`(A *ᵥ 𝕫) * (B *ᵥ 𝕫) = (C *ᵥ 𝕫)` (Hadamard product), every summand's `C`-argument vanishes, so
`𝒢 = 0`.

This is the algebraic core of the `proj_complete` obligation for the first-phase `liftContext`'s
`IsComplete`: an honest (R1CS-satisfying) outer instance projects to a `RandomQuery` inner instance
whose two virtual oracles `(𝒢, 0)` are equal — which is exactly `𝒢 = 0`.
-/

open MvPolynomial Matrix

namespace Spartan.Spec

variable {R : Type} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R]
    (pp : Spartan.PublicParams) [SampleableType R]

/-- **Zero-check completeness (pointwise form).** If the matrix-vector products satisfy the R1CS
Hadamard identity, the zero-check polynomial is identically zero. -/
theorem zeroCheckVirtualPolynomial_eq_zero_of_relation
    (𝕩 : Statement.AfterFirstMessage R pp)
    (oStmt : ∀ i, OracleStatement.AfterFirstMessage R pp i)
    (h : (oStmt (.inl .A) *ᵥ R1CS.𝕫 𝕩 (oStmt (.inr 0)))
          * (oStmt (.inl .B) *ᵥ R1CS.𝕫 𝕩 (oStmt (.inr 0)))
        = (oStmt (.inl .C) *ᵥ R1CS.𝕫 𝕩 (oStmt (.inr 0)))) :
    zeroCheckVirtualPolynomial R pp 𝕩 oStmt = 0 := by
  unfold zeroCheckVirtualPolynomial
  apply Finset.sum_eq_zero
  intro x _
  have hx := congrFun h x
  rw [Pi.mul_apply] at hx
  rw [hx, sub_self, map_zero, mul_zero]

/-- **Zero-check completeness (R1CS relation form).** The zero-check polynomial vanishes on any
instance satisfying the R1CS relation. -/
theorem zeroCheckVirtualPolynomial_eq_zero_of_satisfied
    (𝕩 : Statement.AfterFirstMessage R pp)
    (oStmt : ∀ i, OracleStatement.AfterFirstMessage R pp i)
    (h : R1CS.relation R pp.toSizeR1CS 𝕩 (fun idx => oStmt (.inl idx)) (oStmt (.inr 0))) :
    zeroCheckVirtualPolynomial R pp 𝕩 oStmt = 0 :=
  zeroCheckVirtualPolynomial_eq_zero_of_relation pp 𝕩 oStmt h

end Spartan.Spec
