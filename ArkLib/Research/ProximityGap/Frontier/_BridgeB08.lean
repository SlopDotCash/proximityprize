/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Bridge B08 — graded bin index halves under doubling (target E6)

The E6 self-similarity `#bad_{2n}(k, 2m') = #bad_n(k/2, m')` and `#bad_{2n}(k, odd) = 0`
rests on a purely arithmetic fact about the doubling map `a ↦ 2·a` on `ℤ/2n` and the
"graded bin index" map `ℤ/2n → ℤ/n` (reduction of a frequency mod the half-modulus).

This file isolates and proves that arithmetic kernel:

* `bin` is the canonical ring hom `ℤ/2n → ℤ/n` (`ZMod.castHom`, valid since `n ∣ 2n`); it
  records the `n`-bin a level-`2n` frequency lands in.
* **`bin_doubling`** — the bin index of `2·a` is twice the bin index of `a`: doubling
  commutes with binning (`bin (2·a) = 2·(bin a)`). This is the "halving" arithmetic: the
  level-`2n` doubled frequency `2a` is graded by the level-`n` frequency `2·bin a`, so the
  doubling map folds the `2n`-grading onto the `n`-grading.
* **`bin_antipodal`** — the antipodal element `n` (the order-2 element `-1 ∈ μ_{2n}`) bins to
  `0`: `bin (n) = 0`. This is the antipodal-involution vanishing that kills odd graded pieces.
* **`antipodal_period_two`** — `2·(n : ℤ/2n) = 0`: the antipode has order dividing 2.

These are char-free residue identities; they are the exact arithmetic substrate the E6
bijection (subset folding) and the odd-piece vanishing are built on.

Issue #444 (bridge B08, target E6).
-/

namespace ArkLib.ProximityGap.BridgeB08

open ZMod

variable (n : ℕ)

/-- The graded **bin index** map `ℤ/2n → ℤ/n`: the canonical reduction of a level-`2n`
frequency to the level-`n` grading. It is a ring hom because `n ∣ 2n`. -/
noncomputable def bin : ZMod (2 * n) →+* ZMod n :=
  ZMod.castHom ⟨2, by ring⟩ (ZMod n)

/-- **Doubling halves the bin (the E6 folding kernel).** The bin index of the doubled
frequency `2·a` is `2·(bin a)`: doubling on `ℤ/2n` projects to doubling on the `ℤ/n`
grading. Equivalently, the level-`2n` frequency `2a` is governed by the level-`n` frequency
`2·bin a`, which is what folds the `2n`-graded obstruction onto the `n`-graded one. -/
theorem bin_doubling (a : ZMod (2 * n)) : bin n (2 * a) = 2 * bin n a := by
  simp [bin, map_mul, map_ofNat]

/-- **Antipodal vanishing.** The antipode `(n : ℤ/2n)` (the order-2 element `-1 ∈ μ_{2n}`)
bins to `0`. This is the involution that annihilates the odd graded pieces in E6. -/
theorem bin_antipodal : bin n (n : ZMod (2 * n)) = 0 := by
  have : bin n (n : ZMod (2 * n)) = ((n : ℕ) : ZMod n) := by
    simp [bin]
  rw [this, ZMod.natCast_self]

/-- The antipode has additive order dividing `2`: `2·(n : ℤ/2n) = 0`. -/
theorem antipodal_period_two : (2 : ZMod (2 * n)) * (n : ZMod (2 * n)) = 0 := by
  have h : (2 : ZMod (2 * n)) * (n : ZMod (2 * n)) = ((2 * n : ℕ) : ZMod (2 * n)) := by
    push_cast; ring
  rw [h, ZMod.natCast_self]

end ArkLib.ProximityGap.BridgeB08

#print axioms ArkLib.ProximityGap.BridgeB08.bin_doubling
#print axioms ArkLib.ProximityGap.BridgeB08.bin_antipodal
#print axioms ArkLib.ProximityGap.BridgeB08.antipodal_period_two
