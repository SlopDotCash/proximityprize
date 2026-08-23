/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (lane pow2dip)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.CrossingDepthLinearTracking

/-!
# The `_Close27_PlateauWidthDecision` prize-FAILS input is FALSIFIED on the prize 2-power tower
#444

## What this constrains (refutation-with-mechanism, rule 4, NOT a CORE closure)

`_Close27_PlateauWidthDecision` records a "decision" for the over-determined far-line face:
`m*` grows LINEARLY, so the plateau-width route is the **MULTIPLICATIVE / prize-FAILS** horn.  Its
single load-bearing input (`mStar_linear_drives_decision`) takes the linear law
`m*(n) = c*(n) = n/4 - 1` as **GIVEN** and concludes unboundedness.  The "decision" therefore lives
entirely in the *truth of that input on the prize regime*.

The prize regime is the THIN 2-power subgroup `mu_n` with `n = 2^a` (issue #444 CORE).  This file
proves, over the tree's OWN authoritative worst-direction data
(`CrossingDepthLinearTracking.cStarFull`, from the exhaustive GPU cascade `rho4.out`), that:

* the linear input `c*(n) = n/4 - 1` is **FALSE at `n = 32`**, the binding 2-power-tower point
  (`c*(32) = 5 != 7 = 32/4 - 1`);
* the 2-adic dip `(n/4 - 1) - c*(n)` is `0` at `n = 16` but `2` at `n = 32`: the deviation **grows**
  along the tower, so it is not a one-off rounding artifact;
* the law holds **EXACTLY** only on the mid-range `{16,20,24,28}`, which is **OFF** the 2-power
  tower (`20,24,28` are not powers of two).

## The constraint (the mechanism)

The `_Close27_PlateauWidthDecision` "prize-FAILS" reading is **regime-restricted to the off-tower
mid-range** and is **NOT established on the prize 2-power tower**: at the tower point `n = 32` where
the decision must apply, its own linear input is contradicted by the tree's measured `c*`.  This is
exactly the `CrossingDepthLinearTracking` "2-adic dip below the line" already noted for `c*`, here
turned into the explicit statement that *the dip lands on the prize regime and invalidates the
FAILS-horn input there*.  So the prize-FAILS horn is **NOT decided** for `mu_n`, `n = 2^a`.

Symmetrically, `_Close27_ImprimitivePlateauExcess`'s prize-HOLDS horn is conditional on the unproven
persistence hypothesis `hOconst` (`O = 1` for all `n = 2^a`).  Neither horn is established on the
prize tower; the dichotomy is genuinely OPEN, and this file pins the precise reason the FAILS
side is not closed: its input is finitely false on the regime it must govern.

## Honest scope (rules 3, 6, ASYMPTOTIC-CLAIM GUARD)

This makes NO capacity / beyond-Johnson / sub-linear / growth-law claim about `c*/n`: it does NOT
assert `c*/n -> 0` (that would trip the cliff-at-`n/2` guard, and `CrossingDepthLinearTracking`
already refutes it on the mid-range).  It is a **FINITE** refutation of one named input at one exact
measured datum (`n = 32`).  Pure `Nat` arithmetic over the in-tree `cStarFull`; thinness enters only
via the 2-power tower being the prize regime.  EXTENDS `CrossingDepthLinearTracking` (whose dip
lemma `pow2_values_are_dip_below_line` it consumes) by drawing the decision-theoretic consequence
the `_Close27_PlateauWidthDecision` file's prose did not formalize.  CORE
`M(mu_n) <= C sqrt(n log(p/n))` stays **OPEN**.

All results `decide`/`rfl`-checked, axioms `subseteq {propext, Classical.choice, Quot.sound}`.
-/

namespace ArkLib.ProximityGap.Frontier.Close27DecisionInputRegimeRestricted

open ArkLib.ProximityGap.Frontier.CrossingDepthLinearTracking

/-- The set of 2-power tower levels present in the authoritative `cStarFull` data (the prize regime
`mu_n`, `n = 2^a`). -/
def towerLevels : Finset ℕ := {8, 16, 32}

/-- The off-tower mid-range on which `CrossingDepthLinearTracking` shows the linear law is exact. -/
def midRange : Finset ℕ := {16, 20, 24, 28}

/-- The 2-adic dip of the worst-direction crossing depth below the linear envelope `n/4 - 1`. -/
def dip (n : ℕ) : ℕ := (n / 4 - 1) - cStarFull n

/-! ### The prize-FAILS input is FALSE at the binding tower point `n = 32`. -/

/-- **The linear input `c*(n) = n/4 - 1` is FALSE at `n = 32`**, the binding 2-power-tower point.
`c*(32) = 5`, but `32/4 - 1 = 7`.  The `_Close27_PlateauWidthDecision` "prize-FAILS" decision takes
`m* = c* = n/4 - 1` as its load-bearing input; here that input is contradicted by the tree's own
authoritative worst-direction datum exactly on the prize regime. -/
theorem decision_input_false_at_32 : cStarFull 32 ≠ 32 / 4 - 1 := by decide

/-- **There is a prize-tower level where the linear FAILS-horn input does NOT hold.**  Witnessed by
`n = 32 ∈ towerLevels`: the input `c*(n) = n/4 - 1` fails there.  So the linear law is NOT a valid
input for the decision on the 2-power tower. -/
theorem exists_tower_level_input_fails :
    ∃ n ∈ towerLevels, cStarFull n ≠ n / 4 - 1 :=
  ⟨32, by decide, by decide⟩

/-! ### The dip lands on the prize regime and GROWS along the tower. -/

/-- **The dip is `0` at `n = 16` and `2` at `n = 32`**: it is strictly positive at the upper tower
point and GROWS, so the deviation of `c*` from the linear envelope is a genuine tower phenomenon,
not a single-point artifact. -/
theorem dip_grows_on_tower : dip 16 = 0 ∧ dip 32 = 2 ∧ dip 16 < dip 32 := by
  refine ⟨by decide, by decide, by decide⟩

/-- **`c*` sits strictly below the linear envelope at `n = 32`** (the dip is positive there). -/
theorem cStar_lt_linear_at_32 : cStarFull 32 < 32 / 4 - 1 := by decide

/-! ### The linear law is exact ONLY on the off-tower mid-range. -/

/-- **The linear law is EXACT on the mid-range `{16,20,24,28}`**, re-exposing
`CrossingDepthLinearTracking.cStar_eq_linear_midrange` as the precise valid regime of the input. -/
theorem input_valid_on_midrange :
    ∀ n ∈ midRange, cStarFull n = n / 4 - 1 := by decide

/-- **The mid-range where the input is valid is OFF the 2-power tower.**  `20,24,28 ∈ midRange`
are not powers of two: the linear-law-valid regime and the prize 2-power tower are distinct (meet
only at the boundary point `n = 16`, where the dip is still `0`). -/
theorem midrange_offtower :
    (20 ∈ midRange ∧ 20 ∉ towerLevels) ∧
    (24 ∈ midRange ∧ 24 ∉ towerLevels) ∧
    (28 ∈ midRange ∧ 28 ∉ towerLevels) := by
  refine ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩

/-! ### Consolidated constraint: the prize-FAILS horn is NOT established on the prize tower. -/

/-- **The `_Close27_PlateauWidthDecision` prize-FAILS decision is regime-restricted** (consolidated)
statement.
(1) Its linear input `c*(n) = n/4 - 1` is FALSE at the binding tower point `n = 32`;
(2) the dip below the envelope grows along the tower (`0` at `16`, `2` at `32`);
(3) the input is exact ONLY on the off-tower mid-range `{16,20,24,28}`.
Together: the linear-`m*` "prize-FAILS" reading holds on the off-tower mid-range but is contradicted
on the prize 2-power tower, so the FAILS horn is NOT established for `mu_n`, `n = 2^a`.  (The
prize-HOLDS horn is likewise conditional on `_Close27_ImprimitivePlateauExcess`'s unproven `O = 1`
persistence; the dichotomy is genuinely open.)  This is a FINITE constraint, NOT a capacity claim;
cliff-at-`n/2` untouched.  CORE stays OPEN. -/
theorem fails_horn_not_established_on_tower :
    (cStarFull 32 ≠ 32 / 4 - 1) ∧
    (dip 16 < dip 32) ∧
    (∀ n ∈ midRange, cStarFull n = n / 4 - 1) ∧
    (∃ n ∈ towerLevels, cStarFull n ≠ n / 4 - 1) := by
  refine ⟨by decide, by decide, by decide, ⟨32, by decide, by decide⟩⟩

-- Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}):
#print axioms decision_input_false_at_32
#print axioms exists_tower_level_input_fails
#print axioms dip_grows_on_tower
#print axioms cStar_lt_linear_at_32
#print axioms input_valid_on_midrange
#print axioms midrange_offtower
#print axioms fails_horn_not_established_on_tower

end ArkLib.ProximityGap.Frontier.Close27DecisionInputRegimeRestricted
