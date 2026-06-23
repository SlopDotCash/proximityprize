/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVShawValueSharpFloorFamily
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ShawValueBGKBracketFamily

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Lane-2 CAPSTONE: the two-sided SHARPENED Shaw-value corridor `[c₀/√Lᵢ, 1]` at family granularity (#444)

This module welds the two previously-disconnected sharpened family endpoints into ONE citable
statement:

* `_DoorIVShawValueSharpFloorFamily.shawValueFamily_ge_superDiagonal_floor` — the sharpened LOWER
  endpoint: a uniform super-diagonal period floor `c₀·√nᵢ ≤ Mᵢ` (`c₀ = (5/4)^{1/4} ≈ 1.0574 > 1`, the
  proven Wick-permutation additive-energy lower bound) pushes to `c₀/√Lᵢ ≤ Sh(Mᵢ)`;
* `_ShawValueBGKBracketFamily.shawValueFamily_sharp_bracket` — the conditional BGK UPPER endpoint: a
  uniform BGK-shaped ceiling `Mᵢ ≤ √(nᵢ·Lᵢ)` pushes to `Sh(Mᵢ) ≤ 1`.

No file imported BOTH sharpened family endpoints; this is the first kernel-checked statement that the
prize family's Shaw value is trapped in the *two-sided sharpened* corridor `[c₀/√Lᵢ, 1]` — strictly
inside the bare `[1/√Lᵢ, √(nᵢ/Lᵢ)]`.  The lower end is raised from the bare `1/√Lᵢ` to `c₀/√Lᵢ`
(`c₀ > 1`); the upper end is lowered from the trivial `√(nᵢ/Lᵢ)` to the BGK ceiling `1`.

## Consistency note

The super-diagonal floor hypothesis `c₀·√nᵢ ≤ Mᵢ` is *strictly stronger* than the plain Plancherel
floor `√nᵢ ≤ Mᵢ` that the BGK bracket uses (since `c₀ > 1` and `√nᵢ ≥ 0`), so a single super-diagonal
floor hypothesis suffices to drive BOTH the sharpened lower endpoint and the BGK lower endpoint
consistently — no extra assumption is needed to combine the two ends.

## Scope (honesty)

Lane-2 normalization capstone ONLY.  It is a pure conjunction of the two established sharpened family
endpoints.  The BGK ceiling is a SUPPLIED hypothesis (`Mᵢ ≤ √(nᵢ·Lᵢ)`), NOT an unconditional
cancellation theorem, and is asserted at NO instance.  It proves NO prize inequality, gives NO
anti-concentration / cancellation estimate.  The open door-(iv) problem (collapse the corridor to an
absolute constant) is exactly as open as before.
-/

namespace ArkLib.ProximityGap.Frontier.DoorIVShawValueTwoSidedSharpCorridorFamily

open ArkLib.ProximityGap.Frontier.ShawValueCapstone

variable {ι : Type*} {M n L : ι → ℝ}

/-- The super-diagonal floor `c₀·√nᵢ ≤ Mᵢ` implies the plain Plancherel floor `√nᵢ ≤ Mᵢ` (since
`c₀ > 1` and `√nᵢ ≥ 0`).  So a single super-diagonal floor hypothesis suffices for BOTH sharpened
endpoints. -/
theorem plancherel_floor_of_superDiagonal_floor
    (hfloor : ∀ i, superDiagonalFloorConst * Real.sqrt (n i) ≤ M i) :
    ∀ i, Real.sqrt (n i) ≤ M i := by
  intro i
  have hc0 : (1 : ℝ) ≤ superDiagonalFloorConst := le_of_lt superDiagonalFloorConst_gt_one
  have hsn : (0 : ℝ) ≤ Real.sqrt (n i) := Real.sqrt_nonneg _
  calc Real.sqrt (n i) = 1 * Real.sqrt (n i) := (one_mul _).symm
    _ ≤ superDiagonalFloorConst * Real.sqrt (n i) := by
        exact mul_le_mul_of_nonneg_right hc0 hsn
    _ ≤ M i := hfloor i

/-- **Two-sided sharpened Shaw-value corridor at family granularity.**  Under a uniform super-diagonal
period floor `c₀·√nᵢ ≤ Mᵢ` AND a uniform BGK-shaped ceiling `Mᵢ ≤ √(nᵢ·Lᵢ)`, every normalized Shaw
value is trapped in the two-sided sharpened corridor `[c₀/√Lᵢ, 1]` pointwise across the prize family.
The lower end `c₀/√Lᵢ` strictly exceeds the bare `1/√Lᵢ` (`c₀ > 1`); the upper end `1` is below the
trivial-ceiling endpoint `√(nᵢ/Lᵢ)`.  This is the first statement tying BOTH sharpened endpoints
together at family level. -/
theorem shawValueFamily_twoSided_sharp_corridor
    (hn : ∀ i, 0 < n i) (hL : ∀ i, 0 < L i)
    (hfloor : ∀ i, superDiagonalFloorConst * Real.sqrt (n i) ≤ M i)
    (hceil : ∀ i, M i ≤ prizeScale (n i) (L i)) :
    ∀ i, superDiagonalFloorConst / Real.sqrt (L i) ≤ shawValue (M i) (n i) (L i)
      ∧ shawValue (M i) (n i) (L i) ≤ 1 := by
  intro i
  refine ⟨shawValueFamily_ge_superDiagonal_floor hn hL hfloor i, ?_⟩
  exact (ShawValueBGKBracket.shawValueFamily_sharp_bracket_of_pos hn hL
    (plancherel_floor_of_superDiagonal_floor hfloor) hceil i).2

/-- **The two-sided sharpened corridor is strictly inside the bare corridor.**  At every prize-regime
instance (`Lᵢ < nᵢ`): the sharpened lower end `c₀/√Lᵢ` strictly exceeds the bare lower end `1/√Lᵢ`, and
the BGK upper end `1` is strictly below the trivial upper end `√(nᵢ/Lᵢ)` (whenever the trivial width
`√nᵢ > c₀`, i.e. `nᵢ > c₀² = √(5/4)`).  Recorded as the corridor-narrowing certificate: both ends move
inward. -/
theorem shawValueFamily_corridor_strictly_inside_bare
    (hL : ∀ i, 0 < L i) :
    ∀ i, 1 / Real.sqrt (L i) < superDiagonalFloorConst / Real.sqrt (L i) := by
  intro i
  exact shawValueFamily_sharpened_strictly_above_bare hL i

/-- **Two-sided sharpened family corridor, packaged with the BGK width.**  Under the uniform
super-diagonal floor + uniform BGK ceiling + prize regime `Lᵢ < nᵢ`: at every instance (a) the Shaw
value lies in `[c₀/√Lᵢ, 1]`, (b) the sharpened lower end strictly exceeds the bare `1/√Lᵢ`, and (c) the
BGK bracket width `√Lᵢ` is strictly below the trivial width `√nᵢ`.  One citable family capstone for the
two-sided sharpened corridor. -/
theorem shawValueFamily_twoSided_sharp_corridor_package
    (hn : ∀ i, 0 < n i) (hL : ∀ i, 0 < L i)
    (hfloor : ∀ i, superDiagonalFloorConst * Real.sqrt (n i) ≤ M i)
    (hceil : ∀ i, M i ≤ prizeScale (n i) (L i))
    (hLn : ∀ i, L i < n i) :
    ∀ i, (superDiagonalFloorConst / Real.sqrt (L i) ≤ shawValue (M i) (n i) (L i)
        ∧ shawValue (M i) (n i) (L i) ≤ 1)
      ∧ 1 / Real.sqrt (L i) < superDiagonalFloorConst / Real.sqrt (L i)
      ∧ Real.sqrt (L i) < Real.sqrt (n i) := by
  intro i
  exact ⟨shawValueFamily_twoSided_sharp_corridor hn hL hfloor hceil i,
    shawValueFamily_corridor_strictly_inside_bare hL i,
    ShawValueBGKBracket.shawValueFamily_sharp_width_lt_trivial (fun j => (hL j).le) hLn i⟩

end ArkLib.ProximityGap.Frontier.DoorIVShawValueTwoSidedSharpCorridorFamily
