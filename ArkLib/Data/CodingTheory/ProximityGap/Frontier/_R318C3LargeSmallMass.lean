/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# R318 (#466): large + small `c = 3` mass already beats exact Wick

The full R310 histogram has three strata, but the explicit large fibers and
the raw two-parameter small family are sufficient by themselves.  If the
remaining finite-combinatorial classification proves

* `n` large fibers, each contributing `24n - 18`, and
* `n(n - 7)` pairwise-distinct small fibers, each contributing `36`,

then their mass is already greater than the depth-3 exact-Wick headroom for
every `n >= 16`.  This arithmetic socket deliberately does not assert that the
field identities construct those fibers with the stated multiplicities; R317
and the R318 probe isolate that remaining task.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.R318C3LargeSmallMass

/-- Collision mass from the large and small `c = 3` strata alone. -/
def c3LargeSmallMass (n : ℤ) : ℤ :=
  n * (24 * n - 18) + n * (n - 7) * 36

/-- The depth-3 exact-Wick headroom above the char-zero baseline. -/
def depth3Headroom (n : ℤ) : ℤ :=
  45 * n * n - 40 * n

/-- Large plus small mass simplifies without using the middle stratum. -/
theorem c3LargeSmallMass_eq (n : ℤ) :
    c3LargeSmallMass n = 60 * n * n - 270 * n := by
  unfold c3LargeSmallMass
  ring

/-- The surplus over the exact-Wick headroom has a positive factorization. -/
theorem c3LargeSmallMass_sub_headroom (n : ℤ) :
    c3LargeSmallMass n - depth3Headroom n = 5 * n * (3 * n - 46) := by
  rw [c3LargeSmallMass_eq]
  unfold depth3Headroom
  ring

/-- Any large-plus-small realization forces a depth-3 exact-Wick violation at
every dyadic production size `n >= 16`. -/
theorem depth3Headroom_lt_c3LargeSmallMass {n : ℤ} (hn : 16 ≤ n) :
    depth3Headroom n < c3LargeSmallMass n := by
  have hn0 : 0 < n := by omega
  have hfactor : 0 < 3 * n - 46 := by nlinarith
  have hdiff : 0 < c3LargeSmallMass n - depth3Headroom n := by
    rw [c3LargeSmallMass_sub_headroom]
    exact mul_pos (mul_pos (by norm_num) hn0) hfactor
  exact sub_pos.mp hdiff

end ArkLib.ProximityGap.Frontier.R318C3LargeSmallMass

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.R318C3LargeSmallMass.c3LargeSmallMass_eq
#print axioms ArkLib.ProximityGap.Frontier.R318C3LargeSmallMass.c3LargeSmallMass_sub_headroom
#print axioms ArkLib.ProximityGap.Frontier.R318C3LargeSmallMass.depth3Headroom_lt_c3LargeSmallMass
