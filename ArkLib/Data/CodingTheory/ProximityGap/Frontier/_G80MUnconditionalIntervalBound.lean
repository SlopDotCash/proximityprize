/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G80OProductDivisorInterval
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G80NDivisorFourthPowerBound

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# LANE G80M (#466, 2026-07-10): the UNCONDITIONAL Cilleruelo–Garaev-type interval bound —
  `T(W)⁸ ≤ 19680·W²·n⁴` for every multiplicative `H` and every `W` below `√p`
  (axiom-clean, ZERO named hypotheses; G80O × G80N joined).

## The theorem

`intervalCount_pow_eight_le` : for any prime `p`, any multiplicatively closed
`H ⊆ ZMod p` and any `W` with `W² < p`:

  `T(W)⁸ ≤ 19680 · W² · |H|⁴`,  where `T(W) = #{s ∈ [1,W] : s mod p ∈ H}`.

Equivalently `T(W) = O(|H|^{1/2}·W^{1/4})` — strictly below the trivial `min(|H|, W)`
throughout `|H|^{2/3} ≪ W ≪ |H|²` (e.g. `T(n) = O(n^{3/4})` at `W = n = |H|`). To our
knowledge the FIRST machine-checked nontrivial concentration bound for multiplicative
subgroups in intervals, with all constants explicit and no named hypotheses: the G80O
product/rigidity skeleton fired by the G80N divisor bound `d(y)⁴ ≤ 19680·y` (the uniform
`D` is realized as the maximum divisor count over `[1, W²]`).

## Honest scope

The regime `W < √p` is fenced from the prize saddle (`W = p/K ≫ √p`) by G80P regime
disjointness — this theorem advances the interval face (classical β < 3 territory), NOT the
wall. It is the k = 2 rung of the k-fold ladder whose limit is the BGK bootstrap. CORE
remains OPEN / ON-BGK.

Issue #466. Axiom-clean.
-/

open Finset

namespace ArkLib.ProximityGap.Frontier.G80MUnconditionalIntervalBound

open ArkLib.ProximityGap.Frontier.G80OProductDivisorInterval
open ArkLib.ProximityGap.Frontier.G80NDivisorFourthPowerBound

variable {p : ℕ} [Fact p.Prime] [NeZero p]

/-- **The unconditional CG-type interval bound**: `T(W)⁸ ≤ 19680·W²·|H|⁴` whenever
`W² < p` and `H` is multiplicatively closed. No named hypotheses. -/
theorem intervalCount_pow_eight_le
    (H : Finset (ZMod p)) (hmul : ∀ x ∈ H, ∀ y ∈ H, x * y ∈ H)
    {W : ℕ} (hW : W * W < p) :
    intervalCount p H W ^ 8 ≤ 19680 * (W * W) * H.card ^ 4 := by
  classical
  rcases Nat.eq_zero_or_pos W with rfl | hWpos
  · -- W = 0 : interval empty
    have hT : intervalCount p H 0 = 0 := by
      rw [intervalCount]
      simp
    rw [hT]
    simp
  -- D := max divisor count over [1, W²]
  have hIcc : (Finset.Icc 1 (W * W)).Nonempty := by
    rw [Finset.nonempty_Icc]
    nlinarith
  have hne : ((Finset.Icc 1 (W * W)).image (fun y => y.divisors.card)).Nonempty :=
    hIcc.image _
  set D : ℕ := ((Finset.Icc 1 (W * W)).image (fun y => y.divisors.card)).max' hne with hD
  -- DivisorBound holds at D by maximality
  have hDB : DivisorBound (W * W) D := by
    intro y hy
    exact Finset.le_max' _ _ (Finset.mem_image_of_mem (fun y => y.divisors.card) hy)
  -- D⁴ ≤ 19680·W² since the max is attained
  have hD4 : D ^ 4 ≤ 19680 * (W * W) := by
    have hmem := Finset.max'_mem _ hne
    rw [Finset.mem_image] at hmem
    obtain ⟨y₀, hy₀, hDy⟩ := hmem
    rw [Finset.mem_Icc] at hy₀
    have hy0ne : y₀ ≠ 0 := by omega
    have hDy' : y₀.divisors.card = D := by rw [hD]; exact hDy
    calc D ^ 4 = y₀.divisors.card ^ 4 := by rw [hDy']
      _ ≤ 19680 * y₀ := card_divisors_pow_four_le hy0ne
      _ ≤ 19680 * (W * W) := Nat.mul_le_mul_left _ hy₀.2
  -- fire G80O and raise to the fourth power
  have hsq : intervalCount p H W * intervalCount p H W ≤ D * H.card :=
    intervalCount_sq_le_of_divisorBound H hmul hW hDB
  calc intervalCount p H W ^ 8
      = (intervalCount p H W * intervalCount p H W) ^ 4 := by ring
    _ ≤ (D * H.card) ^ 4 := Nat.pow_le_pow_left hsq 4
    _ = D ^ 4 * H.card ^ 4 := by ring
    _ ≤ (19680 * (W * W)) * H.card ^ 4 := Nat.mul_le_mul_right _ hD4
    _ = 19680 * (W * W) * H.card ^ 4 := by ring

end ArkLib.ProximityGap.Frontier.G80MUnconditionalIntervalBound

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.G80MUnconditionalIntervalBound.intervalCount_pow_eight_le
