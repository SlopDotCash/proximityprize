/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ShawValueBGKBracket

/-!
# Lane-2: the FAMILY-LEVEL conditional BGK sharp Shaw-value bracket `[1/√Lᵢ, 1]` (#444)

`_ShawValueBGKBracket` proved the *pointwise* conditional BGK sharp bracket: under the proven
Plancherel/RMS floor `√n ≤ M` and a BGK-shaped upper hypothesis `M ≤ √(n·L) = prizeScale n L`, the
normalized Shaw value is sandwiched in `[1/√L, 1]`, of width `√L` — strictly narrower (in the prize
regime `L < n`) than the trivial-ceiling bracket `[1/√L, √(n/L)]` of width `√n`.

This is the UPPER-END companion of `_DoorIVShawValueSharpFloorFamily` (which lifted the *sharpened
lower* endpoint `c₀/√Lᵢ` to the prize family).  But the *conditional BGK upper* bracket was only proved
pointwise; the Lane-2 reduction chain over an `ι`-indexed prize family had no family-level statement
that a uniform BGK-shaped ceiling collapses the trivial `√nᵢ`-wide window to the sharp `√Lᵢ`-wide window
at every instance.

This module closes that one rung — the family companion of the conditional BGK bracket.  It chains the
**already-proven** pointwise bracket (`shawValue_sharp_bracket`, `shawValue_sharp_bracket_width`,
`sharp_width_lt_trivial_width`) over an `ι`-indexed family, giving:

* `shawValueFamily_sharp_bracket` — pointwise `[1/√Lᵢ-floor, 1]` sandwich under a uniform Plancherel
  floor + uniform BGK-shaped ceiling;
* `shawValueFamily_sharp_bracket_width` — the sharp family bracket has width `√Lᵢ` at every instance;
* `shawValueFamily_sharp_width_lt_trivial` — that sharp width `√Lᵢ` is strictly below the trivial
  width `√nᵢ` at every prize-regime instance (`Lᵢ < nᵢ`).

Together with `_DoorIVShawValueSharpFloorFamily`, the prize family now has a kernel-checked TWO-SIDED
sharpened corridor at family granularity: lower end `c₀/√Lᵢ` (super-diagonal), upper end `1` (BGK), in
place of the bare `[1/√Lᵢ, √(nᵢ/Lᵢ)]`.

## Scope (honesty)

Lane-2 normalization infrastructure ONLY.  It is a pure pointwise lift of the established
single-instance conditional BGK bracket to an `ι`-indexed family.  The BGK ceiling here is a SUPPLIED
hypothesis `Mᵢ ≤ √(nᵢ·Lᵢ)` (the BGK-shaped normalizer), NOT an unconditional cancellation theorem; the
file proves NO prize inequality, gives NO anti-concentration / cancellation estimate, and asserts the
BGK ceiling holds at NO instance.  The open door-(iv) problem (push the Shaw value from the BGK ceiling
`1` down to the genuine prize threshold `C/√Lᵢ`) is exactly as open as before.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.ShawValueBGKBracket

open ArkLib.ProximityGap.Frontier.ShawValueCapstone

variable {ι : Type*} {M n L : ι → ℝ}

/-- **Family conditional BGK sharp bracket.**  If every member of an admissible prize family has a
positive prize scale, the proven Plancherel/RMS floor `√nᵢ ≤ Mᵢ`, and a uniform BGK-shaped ceiling
`Mᵢ ≤ √(nᵢ·Lᵢ) = prizeScale nᵢ Lᵢ`, then every normalized Shaw value is sandwiched in
`[√nᵢ/prizeScale nᵢ Lᵢ, 1]` (= `[1/√Lᵢ, 1]`) pointwise across the family.  Family companion of
`shawValue_sharp_bracket`. -/
theorem shawValueFamily_sharp_bracket
    (hs : ∀ i, 0 < prizeScale (n i) (L i))
    (hfloor : ∀ i, Real.sqrt (n i) ≤ M i)
    (hceil : ∀ i, M i ≤ prizeScale (n i) (L i)) :
    ∀ i, Real.sqrt (n i) / prizeScale (n i) (L i) ≤ shawValue (M i) (n i) (L i)
      ∧ shawValue (M i) (n i) (L i) ≤ 1 := by
  intro i
  exact shawValue_sharp_bracket (hs i) (hfloor i) (hceil i)

/-- Pointwise-positive parameter wrapper for the family BGK sharp bracket. -/
theorem shawValueFamily_sharp_bracket_of_pos
    (hn : ∀ i, 0 < n i) (hL : ∀ i, 0 < L i)
    (hfloor : ∀ i, Real.sqrt (n i) ≤ M i)
    (hceil : ∀ i, M i ≤ prizeScale (n i) (L i)) :
    ∀ i, Real.sqrt (n i) / prizeScale (n i) (L i) ≤ shawValue (M i) (n i) (L i)
      ∧ shawValue (M i) (n i) (L i) ≤ 1 :=
  shawValueFamily_sharp_bracket (fun i => prizeScale_pos (hn i) (hL i)) hfloor hceil

/-- **Family conditional BGK bracket width is `√Lᵢ`.**  At every admissible instance, the ratio of the
BGK-normalized upper endpoint `1` to the lower Plancherel endpoint `√nᵢ/prizeScale nᵢ Lᵢ = 1/√Lᵢ`
equals `√Lᵢ`.  So the open prize, in family Shaw-value language, is to collapse a pointwise `√Lᵢ`-wide
bracket throughout the family.  Family companion of `shawValue_sharp_bracket_width`. -/
theorem shawValueFamily_sharp_bracket_width (hn : ∀ i, 0 < n i) :
    ∀ i, (1 : ℝ) / (Real.sqrt (n i) / prizeScale (n i) (L i)) = Real.sqrt (L i) := by
  intro i
  exact shawValue_sharp_bracket_width (hn i)

/-- **Family BGK sharp width is strictly below the trivial width.**  At every prize-regime instance
(`Lᵢ < nᵢ`, always true at the prize where `Lᵢ = log(p/nᵢ) ≪ nᵢ`), the sharp BGK width `√Lᵢ` is
strictly below the trivial-ceiling width `√nᵢ`.  So the uniform BGK-shaped ceiling is a genuine
family-level improvement, not a restatement.  Family companion of `sharp_width_lt_trivial_width`. -/
theorem shawValueFamily_sharp_width_lt_trivial
    (hL0 : ∀ i, 0 ≤ L i) (hLn : ∀ i, L i < n i) :
    ∀ i, Real.sqrt (L i) < Real.sqrt (n i) := by
  intro i
  exact sharp_width_lt_trivial_width (hL0 i) (hLn i)

/-- **Family BGK sharp bracket + width improvement, packaged.**  Under a uniform Plancherel floor, a
uniform BGK-shaped ceiling, and the prize regime `Lᵢ < nᵢ`, at every instance: (a) the Shaw value lies
in `[1/√Lᵢ, 1]`, (b) that bracket has width `√Lᵢ`, and (c) `√Lᵢ < √nᵢ`, i.e. the sharp bracket is
strictly narrower than the trivial one.  One citable family statement of the conditional BGK
improvement. -/
theorem shawValueFamily_sharp_bracket_package
    (hn : ∀ i, 0 < n i) (hL : ∀ i, 0 < L i)
    (hfloor : ∀ i, Real.sqrt (n i) ≤ M i)
    (hceil : ∀ i, M i ≤ prizeScale (n i) (L i))
    (hLn : ∀ i, L i < n i) :
    ∀ i, (Real.sqrt (n i) / prizeScale (n i) (L i) ≤ shawValue (M i) (n i) (L i)
        ∧ shawValue (M i) (n i) (L i) ≤ 1)
      ∧ (1 : ℝ) / (Real.sqrt (n i) / prizeScale (n i) (L i)) = Real.sqrt (L i)
      ∧ Real.sqrt (L i) < Real.sqrt (n i) := by
  intro i
  exact ⟨shawValueFamily_sharp_bracket_of_pos hn hL hfloor hceil i,
    shawValueFamily_sharp_bracket_width hn i,
    shawValueFamily_sharp_width_lt_trivial (fun j => (hL j).le) hLn i⟩

end ArkLib.ProximityGap.Frontier.ShawValueBGKBracket
