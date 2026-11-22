/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.FieldTheory.Finite.Basic

/-! # Ruling out larger prime fields in the admissible residue classes

Write a candidate field size as 2²⁵⁶ − d. The congruences n ∣ q−1 for
n = 2, 4, 8, 16 leave 358 distinct candidate integers q above the proposed
maxima and below 2²⁵⁶. Every one fails the base-two Fermat test. -/

namespace ProximityGap.PrizeFieldCeiling

/-- The candidate largest field cardinality for each dimension-one domain length. -/
def maxCard (n : ℕ) : ℕ := 2 ^ 256 - (if n = 2 then 189 else if n = 4 then 435 else 2063)

private def relevant (d : ℕ) : Bool :=
  (d % 2 == 1 && d < 189) || (d % 4 == 3 && d < 435) || (d % 8 == 7 && d < 2063)

private def passes (d : ℕ) : Bool :=
  let q := 2 ^ 256 - d
  !relevant d || Nat.powMod 2 (q - 1) q != 1

set_option maxRecDepth 50000 in
set_option maxHeartbeats 3200000 in
-- Each of the relevant offsets requires a modular power with a 256-bit exponent.
private theorem screen : (List.range 2063).all passes = true := by decide

/-- Every prime strictly below 2²⁵⁶ satisfying the specified subgroup divisibility
is at most the stated residue-class maximum. -/
theorem prime_le {n q : ℕ} (hn : n = 2 ∨ n = 4 ∨ n = 8 ∨ n = 16)
    (prime : q.Prime) (high : q < 2 ^ 256) (div : n ∣ q - 1) : q ≤ maxCard n := by
  by_contra! large
  let d := 2 ^ 256 - q
  have rel : relevant d = true := by
    rcases hn with rfl | rfl | rfl | rfl <;>
      simp [relevant, maxCard, d] at large ⊢ <;> omega
  have low : 2 ^ 256 - 2063 < q := by
    rcases hn with rfl | rfl | rfl | rfl <;> simp [maxCard] at large ⊢ <;> omega
  have hq : 2 < q := lt_trans (by decide) low
  have hd : d < 2063 := by dsimp [d]; omega
  have hit : passes d = true := List.all_eq_true.mp screen d (List.mem_range.mpr hd)
  have complement : 2 ^ 256 - d = q := by dsimp [d]; omega
  have fails : Nat.powMod 2 (q - 1) q ≠ 1 := by
    simp only [passes, rel, complement] at hit
    simpa using hit
  apply fails
  rw [Nat.powMod_def]
  have cop := (prime.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by decide) hq)).symm
  simpa [Nat.ModEq, Nat.mod_eq_of_lt prime.one_lt] using
    (Nat.ModEq.pow_card_sub_one_eq_one prime cop)

end ProximityGap.PrizeFieldCeiling
