/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.CharZeroEnergySixExact
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvL2_E7ClosedForm

/-!
# AVENUE A continued: the exact char-0 depth-7 additive energy `E₇(μ_n)` from the recursion

`CharZeroEnergySixExact.lean` solved `B 12 m = E₆(μ_n)`. This file extends the SAME machinery to the
depth-7 count `B 14 m = E₇(μ_n)`, and proves it equals the in-tree `E₇` closed form
`_AvL2_E7ClosedForm.E7` (which was previously only `def`'d + `decide`-anchored, never recursion-proven).
This discharges the open exact-`E₇` producer of `CrossStepRungSix` (the `r = 6` cross-step rung).

## The recursion (same Lam–Leung balance + add-one-class principle)

  `B 14 (m+1) = Σ_{j=0}^{7} C(14,2j)·C(2j,j)·B (14−2j) m`
            `= B 14 m + 182·B 12 m + 6006·B 10 m + 60060·B 8 m + 210210·B 6 m
               + 252252·B 4 m + 84084·B 2 m + 3432`,

(`C(14,2)C(2,1)=182`, `C(14,4)C(4,2)=6006`, `C(14,6)C(6,3)=60060`, `C(14,8)C(8,4)=210210`,
`C(14,10)C(10,5)=252252`, `C(14,12)C(12,6)=84084`, `C(14,14)C(14,7)·(B 0 m=1)=3432`). Carried as the
new named field `rec14`. Probe-verified EXACT at m=1,2,3,4,8
(`B14 = 3432, 11778624, 936369720, 16993726464, 9071319628800 = E₇` at `n = 2,4,6,8,16`), matching
ALL the in-tree `decide`-anchors `_AvL2_E7ClosedForm.E7_two/four/six/eight`.

## What THIS file proves (axiom-clean; reuses the proven B2…B12 closed forms)

* `B14_closed` : `B 14 m = 17297280m⁷ − 181621440m⁶ + 857656800m⁵ − 2270268000m⁴ + 3469810344m³
                 − 2835985152m² + 943113600m`,
* `B14_eq_E7`  : `B 14 m = E7 (2m)` (the in-tree closed form), i.e. with `n = 2m`,
  `B 14 m = 135135n⁷ − 2837835n⁶ + 26801775n⁵ − 141891750n⁴ + 433726293n³ − 708996288n² + 471556800n`.

## Honest status

Same scope as the `E₃…E₆` files: replaces the open exact-`E₇` closed-form producer by a proof from the
recursion, relative to the SAME two elementary named inputs (Lam–Leung balance + add-one-class
recursion), now at depth 7. Does NOT touch the deep BGK/Paley wall (depth `r ≈ log m`, not `r = 7`);
makes NO CORE/cancellation/completion/moment-saving/anti-concentration/capacity claim; prize CORE stays
OPEN. The `rec14` field is a named `Prop` field, NOT discharged.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`. Issue #444 / #389.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.CharZeroEnergySeven

open ArkLib.ProximityGap.Frontier.CharZeroEnergyThree (B2_closed B4_closed B6_closed)
open ArkLib.ProximityGap.Frontier.CharZeroEnergyFour (B8_closed)
open ArkLib.ProximityGap.Frontier.CharZeroEnergyFive (B10_closed)
open ArkLib.ProximityGap.Frontier.CharZeroEnergySix (BalancedCount12 B12_closed)
open ProximityGap.Frontier.E7ClosedForm (E7)

/-- **The depth-≤7 balanced-class-count carrier.** Extends `BalancedCount12 B` by the depth-14
add-one-class recursion field, the depth-7 instance of the same elementary counting principle. -/
structure BalancedCount14 (B : ℕ → ℕ → ℤ) : Prop extends BalancedCount12 B where
  /-- The length-14 add-one-class recursion: new class takes `0,2,…,14` positions. -/
  rec14 : ∀ m, B 14 (m + 1)
      = B 14 m + 182 * B 12 m + 6006 * B 10 m + 60060 * B 8 m + 210210 * B 6 m
          + 252252 * B 4 m + 84084 * B 2 m + 3432

variable {B : ℕ → ℕ → ℤ}

/-- **`B 14 m = 17297280m⁷ − 181621440m⁶ + 857656800m⁵ − 2270268000m⁴ + 3469810344m³ − 2835985152m²
+ 943113600m`** — the depth-7 zero-sum count `E₇(μ_{2m})`, solving `rec14` by induction. -/
theorem B14_closed (h : BalancedCount14 B) (m : ℕ) :
    B 14 m = 17297280 * (m : ℤ) ^ 7 - 181621440 * (m : ℤ) ^ 6 + 857656800 * (m : ℤ) ^ 5
        - 2270268000 * (m : ℤ) ^ 4 + 3469810344 * (m : ℤ) ^ 3 - 2835985152 * (m : ℤ) ^ 2
        + 943113600 * m := by
  induction m with
  | zero => simpa using h.base0 14 (by norm_num)
  | succ k ih =>
      rw [h.rec14 k, ih, B12_closed h.toBalancedCount12 k,
        B10_closed h.toBalancedCount12.toBalancedCount10 k,
        B8_closed h.toBalancedCount12.toBalancedCount10.toBalancedCount8 k,
        B6_closed h.toBalancedCount12.toBalancedCount10.toBalancedCount8.toBalancedCount k,
        B4_closed h.toBalancedCount12.toBalancedCount10.toBalancedCount8.toBalancedCount k,
        B2_closed h.toBalancedCount12.toBalancedCount10.toBalancedCount8.toBalancedCount k]
      push_cast; ring

/-- **AVENUE A `r = 7` target: `B 14 m = E7 (2m)`** — the depth-7 additive-energy zero-sum count
equals the in-tree closed form `_AvL2_E7ClosedForm.E7` at `n = 2m`. Derived from `B14_closed` by pure
algebra (`17297280m⁷−… = E7(2m)`). Discharges the open exact-`E₇` producer of `CrossStepRungSix`. -/
theorem B14_eq_E7 (h : BalancedCount14 B) (m : ℕ) :
    B 14 m = E7 (2 * (m : ℤ)) := by
  rw [B14_closed h]; simp only [E7]; ring

/-- **The exact anchor `E₇(μ_16) = 9071319628800`** (`m = 8`, `n = 2m = 16`), matching the recursion
and `E7 16` of the in-tree closed form. (The in-tree `decide`-anchor `E7_eight : E7 8 = 16993726464`
is the `n = 8`, i.e. `m = 4`, value, which the recursion also reproduces via `B14_closed` at `m = 4`.) -/
theorem B14_anchor (h : BalancedCount14 B) : B 14 8 = 9071319628800 := by
  rw [B14_closed h]; norm_num

end ArkLib.ProximityGap.Frontier.CharZeroEnergySeven

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.CharZeroEnergySeven.B14_closed
#print axioms ArkLib.ProximityGap.Frontier.CharZeroEnergySeven.B14_eq_E7
#print axioms ArkLib.ProximityGap.Frontier.CharZeroEnergySeven.B14_anchor
