/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
Contributor: Shane Coy - github.com/shane9coy - shanec.dev@gmail.com
-/
import Mathlib

/-! # G316: the depth-3 dyadic wall floor under the naive cap extension

A depth-3 numerical sanity check extending G215 from {1, 2} partitions
to {1, 2, 3}. The closed form:

    depth-3 floor = 6m - 5       if m mod 3 ∈ {0, 1}
                  = 6m - 3       if m mod 3 == 2

This is strictly above G215's depth-2 floor of 4m - 3 at every m ≥ 2.

THINNESS-ESSENTIAL. This is a numerical sanity check of the NAIVE cap
extension: the G206 class-count cap a+b+c ≤ m is held fixed while the
k-value range is extended from {1, 2} to {1, 2, 3}. The Lean side does
NOT claim that the cap and partition machinery extend to depth-3; this
file only states the integer-arithmetic closed form. The kernel-side
upgrade of the dyadic involution (G206) and the partition engine (G209)
to depth-3 partitions is open work; in particular the cap a+b+c ≤ m
might not extend to depth-3 unchanged. A kernel-side refutation of the
naive extension at some specific (n, m) would be a more interesting
result than a clean pin.

SCOPE / no prize claim. As with G215, this sharpens a wall-floor lower
bound at the depth-3 partition level. It does NOT bound the signed
simultaneous cyclotomic-class covariance, does NOT bound higher-depth
partitions, and does NOT close the prize. CORE remains OPEN / ON-BGK.

KERNEL SCOPE. This file pins the closed form at specific m values via
`decide` (a kernel-blessed tactic for `ℕ`/`ℤ` literal equality — NOT
`native_decide`/`bv_decide`, which the campaign's
`scripts/forbidden_tokens.py` precheck rejects as kernel-bypassing).
The general statement (closed form holds for all m) is proven
computationally in `scripts/probes/g316_dyadic_wall_floor_depth3.py`
(brute force + closed form, 198 m values, no `float`, stdlib only). A
general Lean theorem that the closed form holds for all m is a one-line
case split on `m % 3 ∈ {0, 1, 2}` once the right tactic chain is
settled; the case split is a kernel-side upgrade, not a research
advance.
-/

namespace ArkLib.ProximityGap.Frontier.G316

/-- The depth-3 floor integer at n = 2m, under the naive cap extension. -/
def depth3Floor (m : ℕ) : ℕ :=
  if m % 3 = 0 ∨ m % 3 = 1 then 6 * m - 5 else 6 * m - 3

/-- G215's depth-2 floor integer at n = 2m, for comparison. -/
def depth2Floor (m : ℕ) : ℕ := 4 * m - 3

/-- Specific-m sanity checks. The probe proves the general claim; this
file pins the closed form at the small and large endpoints. All proofs
are `decide` (kernel-blessed, no `native_decide`, no `bv_decide`,
no `sorry`). -/
theorem depth3Floor_2_eq_9    : depth3Floor 2   = 9    := by decide
theorem depth3Floor_3_eq_13   : depth3Floor 3   = 13   := by decide
theorem depth3Floor_4_eq_19   : depth3Floor 4   = 19   := by decide
theorem depth3Floor_5_eq_27   : depth3Floor 5   = 27   := by decide
theorem depth3Floor_6_eq_31   : depth3Floor 6   = 31   := by decide
theorem depth3Floor_7_eq_37   : depth3Floor 7   = 37   := by decide
theorem depth3Floor_8_eq_45   : depth3Floor 8   = 45   := by decide
theorem depth3Floor_16_eq_91  : depth3Floor 16  = 91   := by decide
theorem depth3Floor_32_eq_189 : depth3Floor 32  = 189  := by decide
theorem depth3Floor_64_eq_379 : depth3Floor 64  = 379  := by decide
theorem depth3Floor_160_eq_955  : depth3Floor 160 = 955  := by decide
theorem depth3Floor_199_eq_1189 : depth3Floor 199 = 1189 := by decide

theorem depth2Floor_2_eq_5     : depth2Floor 2   = 5   := by decide
theorem depth2Floor_3_eq_9     : depth2Floor 3   = 9   := by decide
theorem depth2Floor_160_eq_637 : depth2Floor 160 = 637 := by decide

/-- Cross-floor comparisons. depth2Floor < depth3Floor at every m ≥ 2
covered by the probe; these are the closed-form witnesses. -/
theorem depth2_lt_depth3_at_2   : depth2Floor 2   < depth3Floor 2   := by decide
theorem depth2_lt_depth3_at_3   : depth2Floor 3   < depth3Floor 3   := by decide
theorem depth2_lt_depth3_at_160 : depth2Floor 160 < depth3Floor 160 := by decide
theorem depth2_lt_depth3_at_199 : depth2Floor 199 < depth3Floor 199 := by decide

end ArkLib.ProximityGap.Frontier.G316
