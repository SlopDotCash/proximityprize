/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Tactic

/-!
# The dyadic tower moment recursion, expanded (#407)

For the dyadic tower the real periods split `η_b^{(μ)} = u_b + v_b` (`u_b = η_b^{(μ-1)}`,
`v_b = η_{bω}^{(μ-1)}`; `DyadicTowerRecursion.sum_tower_split`). The `R = 2r`-th moment therefore
expands by the binomial theorem into the cross-moments `T_j = ∑_b u_b^j v_b^{R-j}`:

> **`tower_moment_binomial`** — `∑_b (u_b + v_b)^R = ∑_{j=0}^{R} C(R,j)·(∑_b u_b^j·v_b^{R-j})`.

This is the exact char-free recursion the dyadic-tower attacks rest on. Empirically (workflow av6,
verified `μ∈{2..5}`, `r≤12`) the cross terms `0<j<R` DOMINATE the diagonal (ratio/2^r ∈ [1.03, 7.1] > 1
everywhere), so there is no naive decorrelation closure — the cross-coset additive energy IS the open
content, not these recursions.

Issue #407.
-/

open Finset

namespace ArkLib.ProximityGap.TowerMomentBinomial

variable {ι : Type*} [Fintype ι]

/-- **Tower moment binomial recursion.** The `R`-th moment of a sum splits into cross-moments:
`∑_b (u_b + v_b)^R = ∑_{j≤R} C(R,j)·∑_b u_b^j v_b^{R-j}`. With `u = η^{(μ-1)}`, `v = η^{(μ-1)}∘(·ω)`,
`R = 2r`, this is the exact dyadic-tower second-moment recursion `A_r^{(μ)} = ∑_j C(2r,j) T_j`. -/
theorem tower_moment_binomial (u v : ι → ℝ) (R : ℕ) :
    ∑ b, (u b + v b) ^ R
      = ∑ j ∈ Finset.range (R + 1), (R.choose j : ℝ) * ∑ b, u b ^ j * v b ^ (R - j) := by
  have hpt : ∀ b, (u b + v b) ^ R
      = ∑ j ∈ Finset.range (R + 1), u b ^ j * v b ^ (R - j) * (R.choose j : ℝ) := by
    intro b; rw [add_pow]
  simp_rw [hpt]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by ring

end ArkLib.ProximityGap.TowerMomentBinomial

#print axioms ArkLib.ProximityGap.TowerMomentBinomial.tower_moment_binomial
