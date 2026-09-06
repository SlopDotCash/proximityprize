/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# G169: the Stepanov thin-subgroup hypotheses are empty at production thickness

G169's double-deletion refinement can use the in-tree Stepanov collision theorem only when a
parameter `B` satisfies both

* `2 * |G| ≤ B^3`, the Stepanov multiplicity-size lower condition, and
* `|G| * B ≤ p`, the field-size upper condition.

At the production shape `p = 3 * |G| + 1`, the second inequality forces `B ≤ 3` once
`|G| ≥ 2`, while the first forces `B^3 ≥ 2 |G|`.  For `|G| ≥ 32` these are incompatible.
This file records the pure arithmetic fence so the Stepanov weld cannot be cited as an
`|G|^(1/3)` saving in the thick index-three production regime.  It does not touch the valid
thin-subgroup theorem; it only fences off the production instantiation.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G169StepanovThicknessFence

/-- At production shape `p = 3*m + 1`, the G169 Stepanov hypotheses are incompatible for
all `m ≥ 32`.  The argument is only arithmetic: `m*B ≤ 3m+1` gives `B ≤ 3`, hence
`B^3 ≤ 27`, contradicting `2m ≤ B^3` and `m ≥ 32`. -/
theorem no_stepanov_B_at_index_three_production (m B : ℕ) (hm : 32 ≤ m)
    (hB3 : 2 * m ≤ B ^ 3) (hp : m * B ≤ 3 * m + 1) : False := by
  have hB_le_three : B ≤ 3 := by
    by_contra hnot
    have hB4 : 4 ≤ B := Nat.succ_le_of_lt (Nat.lt_of_not_ge hnot)
    have hmul : 4 * m ≤ m * B := by
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using Nat.mul_le_mul_left m hB4
    have hstrict : 3 * m + 1 < 4 * m := by omega
    exact (not_lt_of_ge (le_trans hmul hp)) hstrict
  have hcube : B ^ 3 ≤ 27 := by
    calc
      B ^ 3 ≤ 3 ^ 3 := Nat.pow_le_pow_left hB_le_three 3
      _ = 27 := by norm_num
  have hlarge : 27 < 2 * m := by omega
  exact (not_lt_of_ge (le_trans hB3 hcube)) hlarge

/-- Production specialization for the certified subgroup size `m = 2^30`. -/
theorem no_stepanov_B_at_two_pow_thirty (B : ℕ)
    (hB3 : 2 * 2 ^ 30 ≤ B ^ 3) (hp : 2 ^ 30 * B ≤ 3 * 2 ^ 30 + 1) : False := by
  exact no_stepanov_B_at_index_three_production (2 ^ 30) B (by norm_num) hB3 hp

end ArkLib.ProximityGap.Frontier.G169StepanovThicknessFence

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.G169StepanovThicknessFence.no_stepanov_B_at_index_three_production
#print axioms
  ArkLib.ProximityGap.Frontier.G169StepanovThicknessFence.no_stepanov_B_at_two_pow_thirty
