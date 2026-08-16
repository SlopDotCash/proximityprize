/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.CharZeroEnergyThreeExact

/-!
# AVENUE A continued: the exact char-0 depth-4 additive energy `E₄(μ_n) = 105n⁴−630n³+1435n²−1155n`

`CharZeroEnergyThreeExact.lean` solved the depth-≤3 zero-sum counts (`B 2, B 4, B 6 m`) from the
add-one-class recursion, giving `E₃(μ_n) = 15n³−45n²+40n` (`n = 2m`) axiom-clean relative to two
elementary named inputs. This file extends the SAME recursion machinery ONE rung further to the
depth-4 count `B 8 m = E₄(μ_n)`, discharging the **only producer input still open at the `r = 3`
cross-step rung** (`CrossStepRungThree.lean` line: "The ONLY producer input still open is the exact
`E₄` closed form itself — the `r = 4` analog of `E₃`").

## The object and the recursion

`E₄(μ_n) = #{(x₁,…,x₄,y₁,…,y₄) ∈ μ_n⁸ : Σ xᵢ = Σ yᵢ}`, the depth-4 additive energy = depth-8
zero-sum count `B 8 m` (`n = 2m`). By the SAME Lam–Leung depth-≤4 balance characterization and the
SAME add-one-class counting principle as depth ≤3, the new class occupies an even number `2j` of the
`8` positions with `j` `+`'s and `j` `−`'s, giving

  `B 8 (m+1) = Σ_{j=0}^{4} C(8,2j)·C(2j,j)·B (8−2j) m`
            `= B 8 m + 56·B 6 m + 420·B 4 m + 560·B 2 m + 70`,

since `C(8,2)C(2,1)=56`, `C(8,4)C(4,2)=420`, `C(8,6)C(6,3)=560`, `C(8,8)C(8,4)·(B 0 m=1)=70`. We carry
this as the new elementary named field `rec8` (the depth-8 instance of the same add-one-class fact
that produced `rec2/rec4/rec6` in `BalancedCount`), NOT silently discharged. The probe
`probe_e4_closedform.py` / inline check confirmed the closed form is EXACT at m=1,2,4,8
(B8 = 70, 4900, 190120, 4649680 = E₄ at n = 2,4,8,16), and B8(16)=E₄(16)=4649680 matches the in-tree
anchor `_AvGER_CharZeroEnergyRecursion.E4_sixteen`.

## What THIS file proves (axiom-clean; reuses the proven B2/B4/B6 closed forms)

Modeling the balanced count by a carrier `B` satisfying `BalancedCount B` (giving `B2/B4/B6` closed
forms from `CharZeroEnergyThreeExact`) PLUS the new `rec8` field, we solve the depth-8 recursion in
closed form by induction on `m`:

* `B8_closed` : `B 8 m = 1680m⁴ − 5040m³ + 5740m² − 2310m`,  i.e. with `n = 2m`,
* `B8_eq_E4`  : `B 8 m = 105(2m)⁴ − 630(2m)³ + 1435(2m)² − 1155(2m) = 105n⁴−630n³+1435n²−1155n`.

This unconditionalizes the `r = 3` cross-step rung *relative to the same two elementary inputs* that
`CharZeroEnergyThreeExact` already rests on (Lam–Leung balance + add-one-class recursion), now at
depth 4. The recursion-solution is `sorry`-free and axiom-clean.

## Honest status (a REDUCTION of the open `E₄` input, not a CORE closure)

Same scope as `CharZeroEnergyThreeExact`: this replaces the open "exact `E₄` closed form" producer of
`CrossStepRungThree` by a PROOF from the recursion, relative to the elementary named inputs. It does
NOT touch the deep BGK / Paley wall (which lives at depth `r ≈ log m`, not `r = 4`), makes NO
CORE/cancellation/completion/moment-saving/anti-concentration/capacity claim, and the prize CORE stays
OPEN. The `rec8` field is a named `Prop` field, not silently discharged.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`. Issue #444 / #389.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.CharZeroEnergyFour

open ArkLib.ProximityGap.Frontier.CharZeroEnergyThree
  (BalancedCount B2_closed B4_closed B6_closed)

/-- **The depth-≤4 balanced-class-count carrier.** Extends `BalancedCount B` (the depth-≤3 base
cases + `rec2/rec4/rec6`) by the depth-8 add-one-class recursion. As with the lower rungs, this is the
elementary combinatorial fact (a new antipodal class occupies `2j` of the `8` positions with `j` `+`'s
and `j` `−`'s), carried as a named field, NOT discharged. -/
structure BalancedCount8 (B : ℕ → ℕ → ℤ) : Prop extends BalancedCount B where
  /-- The length-8 add-one-class recursion: new class takes `0,2,4,6,8` positions
      (`+ C(8,2)C(2,1)·B 6 m + C(8,4)C(4,2)·B 4 m + C(8,6)C(6,3)·B 2 m + C(8,8)C(8,4)`). -/
  rec8 : ∀ m, B 8 (m + 1) = B 8 m + 56 * B 6 m + 420 * B 4 m + 560 * B 2 m + 70

variable {B : ℕ → ℕ → ℤ}

/-- **`B 8 m = 1680m⁴ − 5040m³ + 5740m² − 2310m`** — the depth-4 zero-sum count
`E₄(μ_{2m})`, solving `rec8` by induction with the proven lower closed forms `B6/B4/B2`. -/
theorem B8_closed (h : BalancedCount8 B) (m : ℕ) :
    B 8 m = 1680 * (m : ℤ) ^ 4 - 5040 * (m : ℤ) ^ 3 + 5740 * (m : ℤ) ^ 2 - 2310 * m := by
  induction m with
  | zero => simpa using h.base0 8 (by norm_num)
  | succ k ih =>
      rw [h.rec8 k, ih, B6_closed h.toBalancedCount k, B4_closed h.toBalancedCount k,
        B2_closed h.toBalancedCount k]
      push_cast; ring

/-- **AVENUE A `r = 4` target: `E₄(μ_n) = 105n⁴ − 630n³ + 1435n² − 1155n`** for `n = 2m`. The depth-4
additive-energy zero-sum count `B 8 m` equals `105n⁴−630n³+1435n²−1155n`. Derived from the recursion
solution `B8_closed` by pure algebra (`1680m⁴−5040m³+5740m²−2310m = 105(2m)⁴−630(2m)³+1435(2m)²−1155(2m)`). -/
theorem B8_eq_E4 (h : BalancedCount8 B) (m : ℕ) :
    B 8 m = 105 * (2 * (m : ℤ)) ^ 4 - 630 * (2 * (m : ℤ)) ^ 3
        + 1435 * (2 * (m : ℤ)) ^ 2 - 1155 * (2 * (m : ℤ)) := by
  rw [B8_closed h]; ring

/-- **The exact anchor `E₄(μ_16) = 4649680`** (`m = 8`), matching the in-tree decidable anchor
`_AvGER_CharZeroEnergyRecursion.E4_sixteen` and the probe. Confirms the closed form on a concrete
prize-regime cardinality. -/
theorem B8_eq_E4_anchor (h : BalancedCount8 B) : B 8 8 = 4649680 := by
  rw [B8_closed h]; norm_num

end ArkLib.ProximityGap.Frontier.CharZeroEnergyFour

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.CharZeroEnergyFour.B8_closed
#print axioms ArkLib.ProximityGap.Frontier.CharZeroEnergyFour.B8_eq_E4
#print axioms ArkLib.ProximityGap.Frontier.CharZeroEnergyFour.B8_eq_E4_anchor
