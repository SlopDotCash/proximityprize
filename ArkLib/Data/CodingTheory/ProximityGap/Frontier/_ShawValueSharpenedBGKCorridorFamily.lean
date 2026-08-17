/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVShawValueSharpFloorFamily
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ShawValueBGKBracketFamily

/-!
# Lane-2: family sharpened-BGK Shaw-value corridor (#444)

This module composes two already-proven family rungs:

* `_DoorIVShawValueSharpFloorFamily`: a uniform super-diagonal floor gives
  `c₀ / √Lᵢ ≤ Sh(Mᵢ)`;
* `_ShawValueBGKBracketFamily`: a supplied BGK-shaped ceiling gives `Sh(Mᵢ) ≤ 1`.

The result is the family-level conditional corridor `[c₀/√Lᵢ, 1]`, whose width is `√Lᵢ/c₀`, strictly
narrower than the conditional BGK `[1/√Lᵢ, 1]` width `√Lᵢ`.  This is normalization bookkeeping only:
the BGK ceiling remains an explicit hypothesis, and no CORE cancellation or anti-concentration bound is
proved.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.ShawValueSharpenedBGKCorridorFamily

open ArkLib.ProximityGap.Frontier.ShawValueCapstone
open ArkLib.ProximityGap.Frontier.ShawValueBGKBracket

variable {ι : Type*} {M n L : ι → ℝ}

/-- **Family sharpened-BGK corridor.**  A uniform super-diagonal lower floor and a supplied BGK-shaped
ceiling put every family Shaw value in `[c₀/√Lᵢ, 1]`.  The upper endpoint is conditional on `hceil`;
this theorem does not assert any cancellation estimate. -/
theorem shawValueFamily_sharpened_bgk_corridor
    (hn : ∀ i, 0 < n i) (hL : ∀ i, 0 < L i)
    (hfloor : ∀ i, superDiagonalFloorConst * Real.sqrt (n i) ≤ M i)
    (hceil : ∀ i, M i ≤ prizeScale (n i) (L i)) :
    ∀ i, superDiagonalFloorConst / Real.sqrt (L i) ≤ shawValue (M i) (n i) (L i)
      ∧ shawValue (M i) (n i) (L i) ≤ 1 := by
  intro i
  exact ⟨shawValueFamily_ge_superDiagonal_floor hn hL hfloor i,
    (shawValueFamily_sharp_bracket_of_pos hn hL
      (fun j => by
        calc Real.sqrt (n j)
            ≤ superDiagonalFloorConst * Real.sqrt (n j) := by
                have hs : 0 ≤ Real.sqrt (n j) := Real.sqrt_nonneg (n j)
                have hc : 1 ≤ superDiagonalFloorConst := le_of_lt superDiagonalFloorConst_gt_one
                calc Real.sqrt (n j) = 1 * Real.sqrt (n j) := by ring
                  _ ≤ superDiagonalFloorConst * Real.sqrt (n j) := mul_le_mul_of_nonneg_right hc hs
          _ ≤ M j := hfloor j)
      hceil i).2⟩

/-- **Sharpened conditional BGK width.**  The ratio of the conditional upper endpoint `1` to the
sharpened lower endpoint `c₀/√Lᵢ` is exactly `√Lᵢ/c₀`. -/
theorem shawValueFamily_sharpened_bgk_width (hL : ∀ i, 0 < L i) :
    ∀ i, (1 : ℝ) / (superDiagonalFloorConst / Real.sqrt (L i))
      = Real.sqrt (L i) / superDiagonalFloorConst := by
  intro i
  have hsL : Real.sqrt (L i) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (hL i))
  have hc0 : superDiagonalFloorConst ≠ 0 := by
    have h : (0 : ℝ) < superDiagonalFloorConst := lt_trans zero_lt_one superDiagonalFloorConst_gt_one
    exact ne_of_gt h
  field_simp

/-- The sharpened conditional BGK corridor is strictly narrower than the bare conditional BGK corridor:
`√Lᵢ/c₀ < √Lᵢ`. -/
theorem shawValueFamily_sharpened_bgk_width_lt_bgk_width (hL : ∀ i, 0 < L i) :
    ∀ i, Real.sqrt (L i) / superDiagonalFloorConst < Real.sqrt (L i) := by
  intro i
  have hsL : 0 < Real.sqrt (L i) := Real.sqrt_pos.2 (hL i)
  calc Real.sqrt (L i) / superDiagonalFloorConst < Real.sqrt (L i) / 1 :=
        div_lt_div_of_pos_left hsL (by norm_num) superDiagonalFloorConst_gt_one
    _ = Real.sqrt (L i) := by rw [div_one]

/-- Packaged family corridor: under the super-diagonal floor, supplied BGK ceiling, and prize-regime
`Lᵢ < nᵢ`, every instance has the sharpened bracket `[c₀/√Lᵢ, 1]`, width `√Lᵢ/c₀`, and this width is
strictly below both the BGK width `√Lᵢ` and the trivial width `√nᵢ`. -/
theorem shawValueFamily_sharpened_bgk_corridor_package
    (hn : ∀ i, 0 < n i) (hL : ∀ i, 0 < L i)
    (hfloor : ∀ i, superDiagonalFloorConst * Real.sqrt (n i) ≤ M i)
    (hceil : ∀ i, M i ≤ prizeScale (n i) (L i))
    (hLn : ∀ i, L i < n i) :
    ∀ i, (superDiagonalFloorConst / Real.sqrt (L i) ≤ shawValue (M i) (n i) (L i)
        ∧ shawValue (M i) (n i) (L i) ≤ 1)
      ∧ (1 : ℝ) / (superDiagonalFloorConst / Real.sqrt (L i))
        = Real.sqrt (L i) / superDiagonalFloorConst
      ∧ Real.sqrt (L i) / superDiagonalFloorConst < Real.sqrt (L i)
      ∧ Real.sqrt (L i) / superDiagonalFloorConst < Real.sqrt (n i) := by
  intro i
  have hwL : Real.sqrt (L i) / superDiagonalFloorConst < Real.sqrt (L i) :=
    shawValueFamily_sharpened_bgk_width_lt_bgk_width hL i
  have hLn_sqrt : Real.sqrt (L i) < Real.sqrt (n i) :=
    shawValueFamily_sharp_width_lt_trivial (fun j => (hL j).le) hLn i
  exact ⟨shawValueFamily_sharpened_bgk_corridor hn hL hfloor hceil i,
    shawValueFamily_sharpened_bgk_width hL i,
    hwL,
    lt_trans hwL hLn_sqrt⟩

end ArkLib.ProximityGap.Frontier.ShawValueSharpenedBGKCorridorFamily
