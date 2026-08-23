/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# R398: the period-square recursion as a quadratic-regression Stein identity

The period-square recursion becomes a Markov regression after grouping frequencies by
multiplicative cosets.  If `X` is the period coordinate and `K` is the walk obtained by multiplying
the frequency by a uniformly chosen class of `v-1`, then

`(n-1) KX = X^2-n`.

For a reversible kernel this implies an exact integration-by-parts identity.  It is the natural
entry point for an exchangeable-pairs concentration argument: the left side contains the restoring
drift `(n-X)(X+1)`, while the right side is the Dirichlet jump form.  This file proves the abstract
finite identity; obtaining a sharp conditional jump-energy estimate for the cyclotomic kernel is
the remaining arithmetic question.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.R398QuadraticRegressionSteinIdentity

open Finset

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- A symmetric row-stochastic kernel on a finite state space. -/
structure ReversibleKernel (K : Ω → Ω → ℝ) : Prop where
  symmetric : ∀ i j, K i j = K j i
  row_sum : ∀ i, ∑ j, K i j = 1

/-- Exact quadratic regression supplied by the period-square recursion. -/
def QuadraticRegression (K : Ω → Ω → ℝ) (X : Ω → ℝ) (n : ℝ) : Prop :=
  ∀ i, (n - 1) * (∑ j, K i j * X j) = X i ^ 2 - n

/-- Symmetry and row-stochasticity also give column-stochasticity. -/
theorem ReversibleKernel.column_sum {K : Ω → Ω → ℝ} (hK : ReversibleKernel K) (j : Ω) :
    ∑ i, K i j = 1 := by
  calc
    ∑ i, K i j = ∑ i, K j i := by
      apply Finset.sum_congr rfl
      intro i _
      exact hK.symmetric i j
    _ = 1 := hK.row_sum j

/-- The standard reversible-kernel Dirichlet integration-by-parts identity. -/
theorem dirichlet_identity {K : Ω → Ω → ℝ} (hK : ReversibleKernel K)
    (X f : Ω → ℝ) :
    ∑ i, (X i - ∑ j, K i j * X j) * f i =
      (1 / 2 : ℝ) * ∑ i, ∑ j, K i j * (X i - X j) * (f i - f j) := by
  have hleft : ∑ i, X i * f i = ∑ i, (∑ j, K i j) * (X i * f i) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [hK.row_sum i, one_mul]
  have hright : ∑ i, X i * f i = ∑ j, (∑ i, K i j) * (X j * f j) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [hK.column_sum j, one_mul]
  have hcross : ∑ i, ∑ j, K i j * X i * f j = ∑ i, ∑ j, K i j * X j * f i := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hK.symmetric j i]
  have hrow : ∑ i, ∑ j, K i j * X i * f i = ∑ i, X i * f i := by
    calc
      ∑ i, ∑ j, K i j * X i * f i = ∑ i, (∑ j, K i j) * (X i * f i) := by
        apply Finset.sum_congr rfl
        intro i _
        calc
          ∑ j, K i j * X i * f i = ∑ j, K i j * (X i * f i) := by
            apply Finset.sum_congr rfl
            intro j _
            ring
          _ = (∑ j, K i j) * (X i * f i) := by rw [Finset.sum_mul]
      _ = ∑ i, X i * f i := hleft.symm
  have hcol : ∑ i, ∑ j, K i j * X j * f j = ∑ j, X j * f j := by
    rw [Finset.sum_comm]
    calc
      ∑ j, ∑ i, K i j * X j * f j = ∑ j, (∑ i, K i j) * (X j * f j) := by
        apply Finset.sum_congr rfl
        intro j _
        calc
          ∑ i, K i j * X j * f j = ∑ i, K i j * (X j * f j) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
          _ = (∑ i, K i j) * (X j * f j) := by rw [Finset.sum_mul]
      _ = ∑ j, X j * f j := hright.symm
  simp_rw [sub_mul, mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
  simp_rw [sub_mul, Finset.sum_sub_distrib]
  rw [hcross]
  rw [hrow, hcol]
  ring

/-- **Quadratic-regression Stein identity.**  The restoring drift is exactly the reversible
Dirichlet jump form:

`Σ (n-X)(X+1)f(X) = (n-1)/2 · Σ K(i,j)(X_i-X_j)(f_i-f_j)`.
-/
theorem quadratic_regression_stein_identity {K : Ω → Ω → ℝ}
    (hK : ReversibleKernel K) {X : Ω → ℝ} {n : ℝ}
    (hreg : QuadraticRegression K X n) (f : Ω → ℝ) :
    ∑ i, (n - X i) * (X i + 1) * f i =
      (n - 1) / 2 * ∑ i, ∑ j, K i j * (X i - X j) * (f i - f j) := by
  have hdrift : ∀ i, (n - X i) * (X i + 1) =
      (n - 1) * (X i - ∑ j, K i j * X j) := by
    intro i
    have hi := hreg i
    linear_combination hi
  simp_rw [hdrift, mul_assoc, ← Finset.mul_sum]
  rw [dirichlet_identity hK X f]
  ring

end ArkLib.ProximityGap.Frontier.R398QuadraticRegressionSteinIdentity

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R398QuadraticRegressionSteinIdentity.quadratic_regression_stein_identity
