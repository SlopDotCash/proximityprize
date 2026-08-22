/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.CharZeroEnergyFourExact

/-!
# AVENUE A continued: the exact char-0 depth-5 additive energy
# `E₅(μ_n) = 945n⁵ − 9450n⁴ + 39375n³ − 77175n² + 57456n`

`CharZeroEnergyFourExact.lean` solved the depth-4 zero-sum count `B 8 m = E₄(μ_n)` from the
add-one-class recursion. This file extends the SAME machinery ONE rung further to the depth-5 count
`B 10 m = E₅(μ_n)`, the next producer in the char-0 energy ladder (it feeds the exact `E₅` input of
`CrossStepRungFour.lean`, the `r = 4` analog of how `E₄` feeds `CrossStepRungThree`).

## The recursion (same Lam–Leung balance + add-one-class principle)

For the depth-10 zero-sum count, the new antipodal class occupies an even number `2j` of the `10`
positions with `j` `+`'s and `j` `−`'s:

  `B 10 (m+1) = Σ_{j=0}^{5} C(10,2j)·C(2j,j)·B (10−2j) m`
            `= B 10 m + 90·B 8 m + 1260·B 6 m + 4200·B 4 m + 3150·B 2 m + 252`,

since `C(10,2)C(2,1)=90`, `C(10,4)C(4,2)=1260`, `C(10,6)C(6,3)=4200`, `C(10,8)C(8,4)=3150`,
`C(10,10)C(10,5)·(B 0 m=1)=252`. Carried as the new named field `rec10` (the depth-10 instance of the
same add-one-class fact), NOT silently discharged. Probe-verified EXACT at m=1,2,4,8
(`B10 = 252, 63504, 7939008, 514031616 = E₅` at `n = 2,4,8,16`), matching the in-tree closed form
`_AvGER_CharZeroEnergyRecursion.E5`.

## What THIS file proves (axiom-clean; reuses the proven B2/B4/B6/B8 closed forms)

Modeling the balanced count by a carrier `B` satisfying `BalancedCount8 B` (giving `B2/B4/B6/B8`
closed forms) PLUS the new `rec10` field, we solve the depth-10 recursion in closed form by induction:

* `B10_closed` : `B 10 m = 30240m⁵ − 151200m⁴ + 315000m³ − 308700m² + 114912m`,  i.e. with `n = 2m`,
* `B10_eq_E5`  : `B 10 m = 945(2m)⁵ − 9450(2m)⁴ + 39375(2m)³ − 77175(2m)² + 57456(2m)`
                `= 945n⁵−9450n⁴+39375n³−77175n²+57456n`.

## Honest status (a REDUCTION of the open `E₅` input, not a CORE closure)

Same scope as the `E₃`/`E₄` files: replaces the open exact-`E₅` closed-form producer by a proof from
the recursion, relative to the SAME two elementary named inputs (Lam–Leung balance + add-one-class
recursion), now at depth 5. Does NOT touch the deep BGK/Paley wall (depth `r ≈ log m`, not `r = 5`),
makes NO CORE/cancellation/completion/moment-saving/anti-concentration/capacity claim; prize CORE stays
OPEN. The `rec10` field is a named `Prop` field, not discharged.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`. Issue #444 / #389.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.CharZeroEnergyFive

open ArkLib.ProximityGap.Frontier.CharZeroEnergyThree (B2_closed B4_closed B6_closed)
open ArkLib.ProximityGap.Frontier.CharZeroEnergyFour (BalancedCount8 B8_closed)

/-- **The depth-≤5 balanced-class-count carrier.** Extends `BalancedCount8 B` by the depth-10
add-one-class recursion field, the depth-5 instance of the same elementary counting principle. -/
structure BalancedCount10 (B : ℕ → ℕ → ℤ) : Prop extends BalancedCount8 B where
  /-- The length-10 add-one-class recursion: new class takes `0,2,4,6,8,10` positions
      (`+ C(10,2)C(2,1)·B 8 m + C(10,4)C(4,2)·B 6 m + C(10,6)C(6,3)·B 4 m +
        C(10,8)C(8,4)·B 2 m + C(10,10)C(10,5)`). -/
  rec10 : ∀ m, B 10 (m + 1)
      = B 10 m + 90 * B 8 m + 1260 * B 6 m + 4200 * B 4 m + 3150 * B 2 m + 252

variable {B : ℕ → ℕ → ℤ}

/-- **`B 10 m = 30240m⁵ − 151200m⁴ + 315000m³ − 308700m² + 114912m`** — the depth-5 zero-sum count
`E₅(μ_{2m})`, solving `rec10` by induction with the proven lower closed forms `B8/B6/B4/B2`. -/
theorem B10_closed (h : BalancedCount10 B) (m : ℕ) :
    B 10 m = 30240 * (m : ℤ) ^ 5 - 151200 * (m : ℤ) ^ 4 + 315000 * (m : ℤ) ^ 3
        - 308700 * (m : ℤ) ^ 2 + 114912 * m := by
  induction m with
  | zero => simpa using h.base0 10 (by norm_num)
  | succ k ih =>
      rw [h.rec10 k, ih, B8_closed h.toBalancedCount8 k,
        B6_closed h.toBalancedCount8.toBalancedCount k,
        B4_closed h.toBalancedCount8.toBalancedCount k,
        B2_closed h.toBalancedCount8.toBalancedCount k]
      push_cast; ring

/-- **AVENUE A `r = 5` target: `E₅(μ_n) = 945n⁵−9450n⁴+39375n³−77175n²+57456n`** for `n = 2m`.
The depth-5 additive-energy zero-sum count `B 10 m` equals `E₅`. Derived from `B10_closed` by pure
algebra (`30240m⁵−... = 945(2m)⁵−...`). -/
theorem B10_eq_E5 (h : BalancedCount10 B) (m : ℕ) :
    B 10 m = 945 * (2 * (m : ℤ)) ^ 5 - 9450 * (2 * (m : ℤ)) ^ 4
        + 39375 * (2 * (m : ℤ)) ^ 3 - 77175 * (2 * (m : ℤ)) ^ 2 + 57456 * (2 * (m : ℤ)) := by
  rw [B10_closed h]; ring

/-- **The exact anchor `E₅(μ_16) = 514031616`** (`m = 8`), matching the closed form + probe. -/
theorem B10_eq_E5_anchor (h : BalancedCount10 B) : B 10 8 = 514031616 := by
  rw [B10_closed h]; norm_num

end ArkLib.ProximityGap.Frontier.CharZeroEnergyFive

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.CharZeroEnergyFive.B10_closed
#print axioms ArkLib.ProximityGap.Frontier.CharZeroEnergyFive.B10_eq_E5
#print axioms ArkLib.ProximityGap.Frontier.CharZeroEnergyFive.B10_eq_E5_anchor
