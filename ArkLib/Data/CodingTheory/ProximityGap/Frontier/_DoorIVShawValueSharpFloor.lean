/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.ShawValueCapstone

/-!
# Lane-2: the SHARPENED Shaw-value floor `c/√L` (#444)

`ShawValueCapstone.floor_bracket_eq` records the *bare* Plancherel/RMS floor in Shaw-value units:
the bound `√n ≤ M` pushes to `1/√L ≤ Sh(M)`.  But the repository proves a strictly stronger
*unconditional* floor on the worst Gauss period:

> `BGKFloorSharp.worstPeriod_ge_const_sqrt` : `(5/4)^{1/4}·√n ≤ ‖η_b‖` for some `b ≠ 0`
> (super-diagonal / Wick-permutation additive-energy lower bound, `q ≥ 2n²`, `n ≥ 8`),

with the explicit constant `c₀ := (5/4)^{1/4} ≈ 1.0574 > 1`.  No file fed that *sharpened* floor into
the Shaw value: the Shaw-value lower bracket was left at the bare `1/√L`.

This module closes that one rung.  It proves the **general sharpened-floor implication** — a floor
`c·√n ≤ M` (any `c`) pushes to `c/√L ≤ Sh(M)` — and instantiates it at the proven super-diagonal
constant `c₀ = (5/4)^{1/4}`, giving the citable

> `(5/4)^{1/4} / √L ≤ Sh(M)`     (whenever `√n` is the floor scale and `c₀·√n ≤ M`).

So the Shaw value is bounded *below* by a constant strictly larger than the bare `1/√L`: the prize's
`O(1)` target must clear not merely `1/√L` but `(5/4)^{1/4}/√L`.

## Scope (honesty)

This is Lane-2 normalization infrastructure ONLY.  It chains the **already-proven** super-diagonal
period floor (`worstPeriod_ge_const_sqrt`, elsewhere) through the **already-proven** Shaw-value
floor equivalence (`rawLowerBound_iff_shawValue_floor`).  It proves the implication and evaluates
the constant; it does **not** prove the prize inequality, gives **no** anti-concentration estimate,
and does **not** change the *upper* bracket endpoint (still the trivial `√(n/L)`).  The open
door-(iv) problem is exactly as open as before.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.ShawValueCapstone

variable {M n L : ℝ}

/-- **General sharpened Shaw-value floor.**  A floor on the worst period of the form `c·√n ≤ M`
pushes, under a positive prize scale, to the normalized floor `c/√L ≤ Sh(M)`.  This generalizes
`floor_bracket_eq` (the `c = 1` case) to an arbitrary multiplicative constant `c`, so any improved
unconditional period floor (constant `> 1`) immediately improves the Shaw-value lower bracket. -/
theorem shawValue_floor_of_const_sqrt_floor (hn : 0 < n) (hL : 0 < L) {c : ℝ}
    (hfloor : c * Real.sqrt n ≤ M) :
    c / Real.sqrt L ≤ shawValue M n L := by
  have hs : 0 < prizeScale n L := prizeScale_pos hn hL
  -- push the floor `c·√n ≤ M` through the Shaw-value floor equivalence
  have hpush : (c * Real.sqrt n) / prizeScale n L ≤ shawValue M n L :=
    (rawLowerBound_iff_shawValue_floor (B := c * Real.sqrt n) (M := M)
      (n := n) (L := L) hs).1 hfloor
  -- evaluate the constant: (c·√n)/√(n·L) = c·(√n/√(n·L)) = c·(1/√L) = c/√L
  have heval : (c * Real.sqrt n) / prizeScale n L = c / Real.sqrt L := by
    rw [mul_div_assoc, floor_bracket_eq hn, mul_one_div]
  rwa [heval] at hpush

/-- **The super-diagonal sharpened constant `c₀ = (5/4)^{1/4}`** (≈ 1.0574), the unconditional
period-floor constant proven by `BGKFloorSharp.worstPeriod_ge_const_sqrt`.  Recorded here as a named
real so the Shaw-value floor can cite the exact value. -/
noncomputable def superDiagonalFloorConst : ℝ := (5 / 4 : ℝ) ^ ((1 : ℝ) / 4)

/-- `c₀ > 1`: the super-diagonal floor constant strictly exceeds the bare Parseval scale, so the
sharpened Shaw-value floor is strictly stronger than the bare `1/√L`. -/
theorem superDiagonalFloorConst_gt_one : 1 < superDiagonalFloorConst := by
  unfold superDiagonalFloorConst
  exact Real.one_lt_rpow (by norm_num) (by norm_num)

/-- **Sharpened Shaw-value floor at the proven super-diagonal constant.**  Whenever the proven
unconditional floor `(5/4)^{1/4}·√n ≤ M` holds (this is exactly the conclusion-shape of
`BGKFloorSharp.worstPeriod_ge_const_sqrt`), the Shaw value is at least `(5/4)^{1/4}/√L`, which is
strictly above the bare bracket floor `1/√L`.  This is the citable Shaw-value form of the
super-diagonal lower bound. -/
theorem shawValue_ge_superDiagonal_floor (hn : 0 < n) (hL : 0 < L)
    (hfloor : superDiagonalFloorConst * Real.sqrt n ≤ M) :
    superDiagonalFloorConst / Real.sqrt L ≤ shawValue M n L :=
  shawValue_floor_of_const_sqrt_floor hn hL hfloor

/-- The sharpened floor is strictly larger than the bare floor `1/√L`: `1/√L < c₀/√L`.  So the
super-diagonal lower bound genuinely raises the Shaw-value lower bracket. -/
theorem bare_floor_lt_superDiagonal_floor (hL : 0 < L) :
    1 / Real.sqrt L < superDiagonalFloorConst / Real.sqrt L := by
  have hsL : 0 < Real.sqrt L := Real.sqrt_pos.2 hL
  exact div_lt_div_of_pos_right superDiagonalFloorConst_gt_one hsL

/-- **Refined window width under the sharpened floor.**  The bare two-sided window has width
`bracket_width_eq_sqrt = √n` (upper `√(n/L)` over lower `1/√L`).  Replacing the bare lower end
`1/√L` by the proven sharpened lower end `c₀/√L` narrows the window the prize must collapse to
`(√(n/L)) / (c₀/√L) = √n / c₀`, strictly below the bare `√n` (since `c₀ > 1`).  So the
super-diagonal floor shrinks the trivial Shaw-value window by the constant factor `c₀`. -/
theorem refined_window_width_eq (hn : 0 < n) (hL : 0 < L) :
    Real.sqrt (n / L) / (superDiagonalFloorConst / Real.sqrt L)
      = Real.sqrt n / superDiagonalFloorConst := by
  have hsn : (0:ℝ) ≤ n := le_of_lt hn
  have hsLp : Real.sqrt L ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hL)
  have hc0 : superDiagonalFloorConst ≠ 0 := by
    have := superDiagonalFloorConst_gt_one; positivity
  rw [Real.sqrt_div hsn]
  field_simp

/-- The refined window width `√n/c₀` is strictly below the bare window width `√n` whenever the
subgroup is nontrivial (`0 < n`): the sharpened floor genuinely narrows the trivial window. -/
theorem refined_window_width_lt_sqrt (hn : 0 < n) :
    Real.sqrt n / superDiagonalFloorConst < Real.sqrt n := by
  have hsnpos : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
  have hc0 : 1 < superDiagonalFloorConst := superDiagonalFloorConst_gt_one
  calc Real.sqrt n / superDiagonalFloorConst < Real.sqrt n / 1 :=
        div_lt_div_of_pos_left hsnpos (by norm_num) hc0
    _ = Real.sqrt n := by rw [div_one]

end ArkLib.ProximityGap.Frontier.ShawValueCapstone
