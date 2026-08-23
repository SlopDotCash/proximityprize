/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
Contributor: Shane Coy - github.com/shane9coy - shanec.dev@gmail.com
-/
import Mathlib
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G316DyadicWallFloorDepth3

/-! # G324: the depth-4 dyadic wall floor under the naive cap extension

A depth-4 numerical sanity check extending G316 from {1, 2, 3} partitions
to {1, 2, 3, 4}. The closed form:

    depth-4 floor = 8m - 7               (UNIVERSAL, for all m >= 2)

This is strictly above G316's depth-3 floor (`6m - 5` main / `6m - 3` at
`m mod 3 == 2`) at every `m >= 3` (equal at `m = 2` since `4 > n - 1 = 3`
forbids any 4s), and strictly above G215's depth-2 floor of `4m - 3` at
every `m >= 2`.

## Why `8m - 7` is universal (no `m mod 4` split)

The max of `a + 4b + 9c + 16d` subject to `a + 2b + 3c + 4d = 2m - 1` and
`a + b + c + d <= m` is achieved by using as many 4s as possible: the
efficiency `i^2 / i = i` is dominated by `4` (efficiency 4 vs. 3 for 3s,
2 for 2s, 1 for 1s). With `a_4 = floor((2m-1)/4)` and remainder
`r = (2m-1) mod 4` (always in `{1, 3}` since `2m-1` is odd), both
`r = 1` (use one 1, value 1) and `r = 3` (use one 3, value 9) give the
same total: `16 * floor((2m-1)/4) + r^2 = 8m - 7` for all `m >= 2`.
The count constraint `floor((2m-1)/4) + 1 <= m` is satisfied for all
`m >= 2`.

## Pattern across depths

  depth 2: 4m - 3   (= 2*2*(m-1) + 1)
  depth 3: 6m - 5   (= 2*3*(m-1) + 1)  -- or 6m-3 at m mod 3 == 2
  depth 4: 8m - 7   (= 2*4*(m-1) + 1)  -- UNIVERSAL (no m mod 4 split needed)

## THINNESS-ESSENTIAL.

This is a numerical sanity check of the NAIVE cap extension: the G206
class-count cap `a+b+c+d <= m` is held fixed while the k-value range
is extended from `{1, 2, 3}` to `{1, 2, 3, 4}`. The Lean side does NOT
claim that the cap and partition machinery extend to depth-4; this
file only states the integer-arithmetic closed form. The kernel-side
upgrade of the dyadic involution (G206) and the partition engine (G209)
to depth-4 partitions is open work; in particular the cap
`a+b+c+d <= m` might not extend to depth-4 unchanged. A kernel-side
refutation of the naive extension at some specific (n, m) would be a
more interesting result than a clean pin.

## SCOPE / no prize claim.

As with G215/G316, this sharpens a wall-floor lower bound at the
depth-4 partition level. It does NOT bound the signed simultaneous
cyclotomic-class covariance, does NOT bound higher-depth partitions,
and does NOT close the prize. CORE remains OPEN / ON-BGK.

## KERNEL SCOPE.

This file pins the closed form at specific m values via `decide`
(a kernel-blessed tactic for `ℕ`/`ℤ` literal equality -- NOT
`native_decide`/`bv_decide`, which the campaign's
`scripts/forbidden_tokens.py` precheck rejects as kernel-bypassing).
The general statement (closed form holds for all m) is proven
computationally in `scripts/probes/g324_dyadic_wall_floor_depth4.py`
(brute force + closed form, 198 m values, no `float`, stdlib only).
-/

namespace ArkLib.ProximityGap.Frontier.G324

open ArkLib.ProximityGap.Frontier.G316

/-- The depth-4 floor integer at n = 2m, under the naive cap extension.
UNIVERSAL closed form: `8m - 7` for all `m >= 2`. -/
def depth4Floor (m : ℕ) : ℕ := 8 * m - 7

/-- Specific-m sanity checks. The probe proves the general claim; this
file pins the closed form at the small and large endpoints. All proofs
are `decide` (kernel-blessed, no `native_decide`, no `bv_decide`,
no `sorry`). -/
theorem depth4Floor_2_eq_9     : depth4Floor 2   = 9     := by decide
theorem depth4Floor_3_eq_17    : depth4Floor 3   = 17    := by decide
theorem depth4Floor_4_eq_25    : depth4Floor 4   = 25    := by decide
theorem depth4Floor_5_eq_33    : depth4Floor 5   = 33    := by decide
theorem depth4Floor_6_eq_41    : depth4Floor 6   = 41    := by decide
theorem depth4Floor_7_eq_49    : depth4Floor 7   = 49    := by decide
theorem depth4Floor_8_eq_57    : depth4Floor 8   = 57    := by decide
theorem depth4Floor_16_eq_121  : depth4Floor 16  = 121   := by decide
theorem depth4Floor_32_eq_249  : depth4Floor 32  = 249   := by decide
theorem depth4Floor_64_eq_505  : depth4Floor 64  = 505   := by decide
theorem depth4Floor_160_eq_1273 : depth4Floor 160 = 1273 := by decide
theorem depth4Floor_199_eq_1585 : depth4Floor 199 = 1585 := by decide

/-- Cross-floor comparisons. depth2Floor < depth4Floor at every m >= 2
covered by the probe; depth3Floor <= depth4Floor at every m >= 2 with
strict inequality for m >= 3 (the regime where 4s can appear). -/
theorem depth2_lt_depth4_at_2   : depth2Floor 2   < depth4Floor 2   := by decide
theorem depth2_lt_depth4_at_3   : depth2Floor 3   < depth4Floor 3   := by decide
theorem depth2_lt_depth4_at_160 : depth2Floor 160 < depth4Floor 160 := by decide
theorem depth2_lt_depth4_at_199 : depth2Floor 199 < depth4Floor 199 := by decide

/-- `depth3Floor m <= depth4Floor m` (non-strict; equality at m=2 since
4 > 2m-1=3 forbids any 4s in the partition, so the depth-4 extension
collapses to the depth-3 value there). -/
theorem depth3_le_depth4_at_2   : depth3Floor 2   <= depth4Floor 2   := by decide
theorem depth3_le_depth4_at_3   : depth3Floor 3   <= depth4Floor 3   := by decide
theorem depth3_le_depth4_at_160 : depth3Floor 160 <= depth4Floor 160 := by decide
theorem depth3_le_depth4_at_199 : depth3Floor 199 <= depth4Floor 199 := by decide

/-- Strict `depth3 < depth4` for m >= 3 (the regime where 4s can appear
in the partition). -/
theorem depth3_lt_depth4_at_3   : depth3Floor 3   < depth4Floor 3   := by decide
theorem depth3_lt_depth4_at_160 : depth3Floor 160 < depth4Floor 160 := by decide
theorem depth3_lt_depth4_at_199 : depth3Floor 199 < depth4Floor 199 := by decide

end ArkLib.ProximityGap.Frontier.G324
