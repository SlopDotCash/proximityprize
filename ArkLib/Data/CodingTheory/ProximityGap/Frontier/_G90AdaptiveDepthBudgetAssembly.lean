/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G83FreeOrbitEnergyBridge

/-!
# G90: adaptive all-depth Wick budgets

G89 assembles depth sectors by splitting the Wick budget evenly into `r + 1` shares.  That is a
convenient sufficient condition, but it is not a necessary production target: shallow sectors can
consume much less than one full share, leaving their unused mass for the first difficult depths.

This file supplies the lossless assembly interface.  Give every depth an arbitrary budget `B s`;
if the sector at `s` fits `B s` and the sum of assigned budgets fits Wick, then the total sector
mass fits Wick.  A second theorem isolates one live depth against the exact residual after all
other depths have been paid.  Consequently an equal `111`-way split must not be used to infer an
intrinsic factor-`111` strengthening of the depth-five target.  Issue #466/#505.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G90AdaptiveDepthBudgetAssembly

/-- **Lossless adaptive assembly.**  Per-depth budgets may be allocated arbitrarily; only their
total matters. -/
theorem allDepth_le_fullWick_of_adaptiveBudgets
    {n r : ℕ} {W B : ℕ → ℕ}
    (hWB : ∀ s ∈ Finset.range (r + 1), W s ≤ B s)
    (hB : ∑ s ∈ Finset.range (r + 1), B s ≤
      Nat.doubleFactorial (2 * r - 1) * n ^ r) :
    ∑ s ∈ Finset.range (r + 1), W s ≤
      Nat.doubleFactorial (2 * r - 1) * n ^ r := by
  exact (Finset.sum_le_sum hWB).trans hB

/-- A depth may use the exact Wick residual after all other depths have been paid.  This is the
correct interface for concentrating the unused shallow budget on the first open sector. -/
theorem distinguishedDepth_le_fullWick_of_residual
    {n r live : ℕ} {W : ℕ → ℕ}
    (hlive : live ∈ Finset.range (r + 1))
    (hfit : W live + ∑ s ∈ (Finset.range (r + 1)).erase live, W s ≤
      Nat.doubleFactorial (2 * r - 1) * n ^ r) :
    ∑ s ∈ Finset.range (r + 1), W s ≤
      Nat.doubleFactorial (2 * r - 1) * n ^ r := by
  rw [← Finset.add_sum_erase _ _ hlive]
  exact hfit

/-- A convenient residual consumer: pay a certified aggregate `other` for every non-live depth,
then give the live depth everything left in the full budget. -/
theorem distinguishedDepth_le_fullWick_of_other_le
    {n r live other : ℕ} {W : ℕ → ℕ}
    (hlive : live ∈ Finset.range (r + 1))
    (hother : ∑ s ∈ (Finset.range (r + 1)).erase live, W s ≤ other)
    (hfit : W live + other ≤ Nat.doubleFactorial (2 * r - 1) * n ^ r) :
    ∑ s ∈ Finset.range (r + 1), W s ≤
      Nat.doubleFactorial (2 * r - 1) * n ^ r := by
  apply distinguishedDepth_le_fullWick_of_residual hlive
  exact (Nat.add_le_add_left hother _).trans hfit

/-- The equal-split hypothesis from G89 implies an adaptive allocation, confirming that G90 is a
strictly more flexible consumer rather than a competing normalization. -/
theorem adaptive_of_evenSplit
    {n r : ℕ} {W : ℕ → ℕ}
    (hW : ∀ s ∈ Finset.range (r + 1),
      (r + 1) * W s ≤ Nat.doubleFactorial (2 * r - 1) * n ^ r) :
    ∑ s ∈ Finset.range (r + 1), W s ≤
      Nat.doubleFactorial (2 * r - 1) * n ^ r := by
  have hsum : (r + 1) * ∑ s ∈ Finset.range (r + 1), W s ≤
      (r + 1) * (Nat.doubleFactorial (2 * r - 1) * n ^ r) := by
    rw [Finset.mul_sum]
    calc
      ∑ s ∈ Finset.range (r + 1), (r + 1) * W s ≤
          ∑ _s ∈ Finset.range (r + 1),
            Nat.doubleFactorial (2 * r - 1) * n ^ r :=
        Finset.sum_le_sum hW
      _ = (r + 1) * (Nat.doubleFactorial (2 * r - 1) * n ^ r) := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  exact Nat.le_of_mul_le_mul_left hsum (Nat.succ_pos r)

end ArkLib.ProximityGap.Frontier.G90AdaptiveDepthBudgetAssembly

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.G90AdaptiveDepthBudgetAssembly.allDepth_le_fullWick_of_adaptiveBudgets
#print axioms
  ArkLib.ProximityGap.Frontier.G90AdaptiveDepthBudgetAssembly.distinguishedDepth_le_fullWick_of_residual
#print axioms
  ArkLib.ProximityGap.Frontier.G90AdaptiveDepthBudgetAssembly.distinguishedDepth_le_fullWick_of_other_le
#print axioms
  ArkLib.ProximityGap.Frontier.G90AdaptiveDepthBudgetAssembly.adaptive_of_evenSplit
