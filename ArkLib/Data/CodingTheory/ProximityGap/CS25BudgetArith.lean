/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.HammingBallVolume

/-!
# CS25 count-budget arithmetic (toward T4.17, #82)

The CS25 breakdown count budget (`sum_far_plus_jointProx_lt_of_close_ge`) needs the strict
inequality `q^{n+1}·#{far} + #{jointProx} < #stacks` with `#stacks = q^{2n}` (the `Fin 2` stacks over
a size-`q` field). This file supplies the pure-arithmetic closer: it holds as soon as the two
entropy bounds give `#{far} ≤ q^{n−2}` (coverage) and `#{jointProx} ≤ q^{2n−2}` (the jointProx
sub-band bound), for any `q ≥ 2`:

  `q^{n+1}·q^{n−2} + q^{2n−2} = q^{2n−1} + q^{2n−2} = q^{2n−2}·(q+1) < q^{2n−2}·q² = q^{2n}`  (`q+1 < q²`).
-/

namespace ProximityGap

/-- **CS25 count-budget closer.** If `#{far} ≤ q^{n−2}` and `#{jointProx} ≤ q^{2n−2}` with `q ≥ 2`
and `n ≥ 2`, the breakdown count budget `q^{n+1}·#{far} + #{jointProx} < q^{2n}` holds. -/
theorem count_budget_lt (q n f j : ℕ) (hq : 2 ≤ q) (hn : 2 ≤ n)
    (hf : f ≤ q ^ (n - 2)) (hj : j ≤ q ^ (2 * n - 2)) :
    q ^ (n + 1) * f + j < q ^ (2 * n) := by
  have hpos : 0 < q ^ (2 * n - 2) := pow_pos (by omega) _
  have hqlt : q + 1 < q ^ 2 := by nlinarith [hq]
  calc q ^ (n + 1) * f + j
      ≤ q ^ (n + 1) * q ^ (n - 2) + q ^ (2 * n - 2) := by
        exact Nat.add_le_add (Nat.mul_le_mul_left _ hf) hj
    _ = q ^ (2 * n - 1) + q ^ (2 * n - 2) := by rw [← pow_add]; congr 2; omega
    _ = q ^ (2 * n - 2) * q + q ^ (2 * n - 2) := by
        rw [show 2 * n - 1 = (2 * n - 2) + 1 by omega, pow_succ]
    _ = q ^ (2 * n - 2) * (q + 1) := by ring
    _ < q ^ (2 * n - 2) * q ^ 2 := by exact mul_lt_mul_of_pos_left hqlt hpos
    _ = q ^ (2 * n) := by rw [← pow_add]; congr 1; omega

end ProximityGap
