/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVShawValueSharpFloor

/-!
# Lane-2: the FAMILY-LEVEL sharpened Shaw-value floor `c₀/√Lᵢ` (#444)

`_DoorIVShawValueSharpFloor` proved the *pointwise* sharpened floor: a single-instance super-diagonal
period floor `c₀·√n ≤ M` (with `c₀ = (5/4)^{1/4} ≈ 1.0574 > 1`, the proven Wick-permutation /
additive-energy lower bound `BGKFloorSharp.worstPeriod_ge_const_sqrt`) pushes to the strictly-sharper
Shaw-value floor `c₀/√L ≤ Sh(M)`, narrowing the trivial window from `√n` to `√n/c₀`.

But the Lane-2 reduction chain is used over an *admissible family* of thin prize instances, and only
the **bare** family bracket (`ShawValueCapstone.shawValueFamily_bracket`, lower endpoint `1/√Lᵢ`) was
wired in.  The sharpened constant `c₀` was never lifted to the family level: there was no statement
that a *uniform* super-diagonal floor over a family pushes to a *uniform* sharpened Shaw-value floor,
nor that the family window narrows uniformly to `√nᵢ/c₀`.

This module closes that one rung — the family companion of `_DoorIVShawValueSharpFloor`.  It chains the
**already-proven** pointwise sharpened floor over an `ι`-indexed family, giving:

* `shawValueFamily_ge_superDiagonal_floor` — pointwise `c₀/√Lᵢ ≤ Sh(Mᵢ)` under a uniform super-diagonal
  family floor;
* `shawValueFamily_sharpened_strictly_above_bare` — every member's sharpened floor strictly exceeds the
  bare `1/√Lᵢ`;
* `shawValueFamily_refined_window_width_eq` / `..._lt_sqrt` — the refined family window is `√nᵢ/c₀` at
  every instance, strictly below the bare `√nᵢ`.

## Scope (honesty)

Lane-2 normalization infrastructure ONLY.  It is a pure pointwise lift of the established
single-instance sharpened floor (`shawValue_ge_superDiagonal_floor`, `refined_window_width_eq`,
`refined_window_width_lt_sqrt`) to an `ι`-indexed family.  It proves no prize inequality, gives no
anti-concentration / cancellation estimate, and does not change the *upper* bracket endpoint
(still the trivial `√(nᵢ/Lᵢ)`).  The open door-(iv) problem is exactly as open as before.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.ShawValueCapstone

variable {ι : Type*} {M n L : ι → ℝ}

/-- **Family sharpened Shaw-value floor.**  If every member of an admissible prize family satisfies the
proven super-diagonal period floor `c₀·√nᵢ ≤ Mᵢ` (the conclusion-shape of
`BGKFloorSharp.worstPeriod_ge_const_sqrt`, with `c₀ = (5/4)^{1/4}`), then every normalized Shaw value
is bounded below by the sharpened constant `c₀/√Lᵢ` — pointwise across the family.  This is the
family companion of `shawValue_ge_superDiagonal_floor`. -/
theorem shawValueFamily_ge_superDiagonal_floor
    (hn : ∀ i, 0 < n i) (hL : ∀ i, 0 < L i)
    (hfloor : ∀ i, superDiagonalFloorConst * Real.sqrt (n i) ≤ M i) :
    ∀ i, superDiagonalFloorConst / Real.sqrt (L i) ≤ shawValue (M i) (n i) (L i) := by
  intro i
  exact shawValue_ge_superDiagonal_floor (hn i) (hL i) (hfloor i)

/-- The family sharpened floor strictly exceeds the bare Plancherel floor at every instance:
`1/√Lᵢ < c₀/√Lᵢ`.  So the super-diagonal lower bound genuinely raises the Shaw-value lower bracket
uniformly across the family, not merely pointwise at one instance. -/
theorem shawValueFamily_sharpened_strictly_above_bare (hL : ∀ i, 0 < L i) :
    ∀ i, 1 / Real.sqrt (L i) < superDiagonalFloorConst / Real.sqrt (L i) := by
  intro i
  exact bare_floor_lt_superDiagonal_floor (hL i)

/-- **Family refined window width.**  Replacing the bare lower endpoint `1/√Lᵢ` by the proven sharpened
endpoint `c₀/√Lᵢ` narrows the window the prize must collapse to `√nᵢ/c₀` at every instance — strictly
below the bare `√nᵢ` (since `c₀ > 1`).  The family companion of `refined_window_width_eq`. -/
theorem shawValueFamily_refined_window_width_eq
    (hn : ∀ i, 0 < n i) (hL : ∀ i, 0 < L i) :
    ∀ i, Real.sqrt (n i / L i) / (superDiagonalFloorConst / Real.sqrt (L i))
      = Real.sqrt (n i) / superDiagonalFloorConst := by
  intro i
  exact refined_window_width_eq (hn i) (hL i)

/-- The refined family window width `√nᵢ/c₀` is strictly below the bare width `√nᵢ` at every
nontrivial instance (`0 < nᵢ`).  So the super-diagonal floor narrows the trivial Shaw-value window by
the constant factor `c₀` uniformly across the family.  The family companion of
`refined_window_width_lt_sqrt`. -/
theorem shawValueFamily_refined_window_width_lt_sqrt (hn : ∀ i, 0 < n i) :
    ∀ i, Real.sqrt (n i) / superDiagonalFloorConst < Real.sqrt (n i) := by
  intro i
  exact refined_window_width_lt_sqrt (hn i)

/-- **Family sharpened floor + refined window, packaged.**  Under a uniform super-diagonal family
floor, at every instance: (a) the Shaw value clears `c₀/√Lᵢ`, (b) that floor strictly exceeds the bare
`1/√Lᵢ`, and (c) the refined window width `√nᵢ/c₀` is strictly below the bare `√nᵢ`.  One citable
family statement of the sharpened-floor improvement. -/
theorem shawValueFamily_sharpened_floor_package
    (hn : ∀ i, 0 < n i) (hL : ∀ i, 0 < L i)
    (hfloor : ∀ i, superDiagonalFloorConst * Real.sqrt (n i) ≤ M i) :
    ∀ i, superDiagonalFloorConst / Real.sqrt (L i) ≤ shawValue (M i) (n i) (L i) ∧
      1 / Real.sqrt (L i) < superDiagonalFloorConst / Real.sqrt (L i) ∧
      Real.sqrt (n i) / superDiagonalFloorConst < Real.sqrt (n i) := by
  intro i
  exact ⟨shawValueFamily_ge_superDiagonal_floor hn hL hfloor i,
    shawValueFamily_sharpened_strictly_above_bare hL i,
    shawValueFamily_refined_window_width_lt_sqrt hn i⟩

end ArkLib.ProximityGap.Frontier.ShawValueCapstone
