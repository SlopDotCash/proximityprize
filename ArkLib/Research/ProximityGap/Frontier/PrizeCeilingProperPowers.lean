/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.Algebra.IsPrimePow
import Mathlib.Data.Nat.NthRoot.Defs
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

/-! # The final prime powers below the 256-bit field-size ceiling

For every possible exponent from two through 255, two consecutive integer
bases bracket the entire interval. Newton iteration supplies a candidate base;
the finite certificate checks its bounding powers directly.
-/

namespace ProximityGap.PrizeCeilingProperPowers

private def base (e : ℕ) : ℕ :=
  Nat.nthRoot.go (e - 2) (2 ^ 256 - 1) 256 (2 ^ (255 / e + 1))

set_option maxRecDepth 4096 in
private theorem brackets : ∀ e : Fin 256, 2 ≤ e.val →
    base e.val ^ e.val < 2 ^ 256 - 2063 ∧ 2 ^ 256 ≤ (base e.val + 1) ^ e.val := by
  decide

/-- Every prime-power field order in the final 2,063 positions below 2²⁵⁶ is prime. -/
theorem prime_of_isPrimePow {q : ℕ} (hq : IsPrimePow q) (low : 2 ^ 256 - 2063 ≤ q)
    (high : q < 2 ^ 256) : Nat.Prime q := by
  obtain ⟨p, k, hp, hk, rfl⟩ := hq
  have prime := Nat.prime_iff.mpr hp
  by_cases one : k = 1
  · simpa [one] using prime
  have hk' : k < 256 := by
    by_contra! e
    exact high.not_ge ((Nat.pow_le_pow_right (by decide : 0 < 2) e).trans
      (Nat.pow_le_pow_left prime.two_le k))
  have bound : base k ^ k < 2 ^ 256 - 2063 ∧ 2 ^ 256 ≤ (base k + 1) ^ k :=
    brackets ⟨k, hk'⟩ (show 2 ≤ k by omega)
  by_cases hl : p ≤ base k
  · exact False.elim (bound.1.not_ge (low.trans (Nat.pow_le_pow_left hl k)))
  · have next : base k + 1 ≤ p := Nat.succ_le_of_lt (lt_of_not_ge hl)
    exact False.elim (high.not_ge (bound.2.trans (Nat.pow_le_pow_left next k)))

end ProximityGap.PrizeCeilingProperPowers
