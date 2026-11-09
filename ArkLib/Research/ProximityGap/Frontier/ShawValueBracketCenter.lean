/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Geometric center of the Shaw-value prize bracket (#444)

`ShawValueCapstone.lean` records that the normalized Shaw-value prize bracket is `sqrt n` **wide**:
the trivial-ceiling endpoint divided by the Plancherel-floor endpoint equals `sqrt n`
(`bracket_width_eq_sqrt`).  This file adds the **geometric center** of that bracket and the three
harmless facts about it:

* `geomCenter n L = sqrt (floorEndpoint · ceilingEndpoint)` is the geometric mean of the two
  bracket endpoints, with closed form `n^{1/4} / sqrt L` (`geomCenter_eq`).
* `ratio_symmetric`: the center is the **ratio-midpoint** — `ceiling / center = center / floor`
  (each ratio is `n^{1/4}`); the open prize is exactly the demand to descend `n^{1/4}` below this
  geometric center to an absolute constant.
* `center_between`: for `1 ≤ n` the center genuinely lies inside the bracket,
  `floor ≤ center ≤ ceiling`.

Scope: this is Lane-2 normalization infrastructure only, the geometric-center companion to the
`sqrt n`-width statement.  It hides **no** anti-concentration or cancellation estimate — every
theorem is reversible arithmetic on the two already-identified bracket endpoints.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.ShawValueBracketCenter

/-- The square-root target scale in the prize normalization (same object as
`ShawValueCapstone.prizeScale`); `n` is the subgroup size and `L` the logarithmic thinness
parameter such as `log (p / n)`. -/
noncomputable def prizeScale (n L : ℝ) : ℝ :=
  Real.sqrt (n * L)

/-- The Plancherel/RMS-floor endpoint of the normalized bracket, `sqrt n / prizeScale n L`. -/
noncomputable def floorEndpoint (n L : ℝ) : ℝ :=
  Real.sqrt n / prizeScale n L

/-- The trivial-ceiling endpoint of the normalized bracket, `n / prizeScale n L`. -/
noncomputable def ceilingEndpoint (n L : ℝ) : ℝ :=
  n / prizeScale n L

/-- The geometric center of the prize bracket: the geometric mean of the two bracket endpoints. -/
noncomputable def geomCenter (n L : ℝ) : ℝ :=
  Real.sqrt (floorEndpoint n L * ceilingEndpoint n L)

/-- Positivity of the prize scale. -/
theorem prizeScale_pos {n L : ℝ} (hn : 0 < n) (hL : 0 < L) : 0 < prizeScale n L :=
  Real.sqrt_pos.2 (mul_pos hn hL)

/-- Positivity of the floor endpoint. -/
theorem floorEndpoint_pos {n L : ℝ} (hn : 0 < n) (hL : 0 < L) : 0 < floorEndpoint n L :=
  div_pos (Real.sqrt_pos.2 hn) (prizeScale_pos hn hL)

/-- Positivity of the ceiling endpoint. -/
theorem ceilingEndpoint_pos {n L : ℝ} (hn : 0 < n) (hL : 0 < L) : 0 < ceilingEndpoint n L :=
  div_pos hn (prizeScale_pos hn hL)

/-- Positivity of the geometric center. -/
theorem geomCenter_pos {n L : ℝ} (hn : 0 < n) (hL : 0 < L) : 0 < geomCenter n L :=
  Real.sqrt_pos.2 (mul_pos (floorEndpoint_pos hn hL) (ceilingEndpoint_pos hn hL))

/-- **Endpoint product.**  The product of the two bracket endpoints has closed form `sqrt n / L`. -/
theorem endpoint_product {n L : ℝ} (hn : 0 < n) (hL : 0 < L) :
    floorEndpoint n L * ceilingEndpoint n L = Real.sqrt n / L := by
  unfold floorEndpoint ceilingEndpoint prizeScale
  have hnL : (0 : ℝ) ≤ n * L := le_of_lt (mul_pos hn hL)
  have hs2 : Real.sqrt (n * L) * Real.sqrt (n * L) = n * L := Real.mul_self_sqrt hnL
  rw [div_mul_div_comm, hs2, mul_comm (Real.sqrt n) n,
    mul_div_mul_left (Real.sqrt n) L (ne_of_gt hn)]

/-- **Geometric-center defining identity.**  The center squared (as `center * center`) is exactly the
product of the two endpoints — the geometric-mean property. -/
theorem geomCenter_mul_self {n L : ℝ} (hn : 0 < n) (hL : 0 < L) :
    geomCenter n L * geomCenter n L = floorEndpoint n L * ceilingEndpoint n L := by
  unfold geomCenter
  exact Real.mul_self_sqrt
    (le_of_lt (mul_pos (floorEndpoint_pos hn hL) (ceilingEndpoint_pos hn hL)))

/-- **Closed form of the geometric center:** `geomCenter n L = n^{1/4} / sqrt L`, written with the
fourth root as `sqrt (sqrt n)`.  This is the geometric midpoint of the bracket whose floor endpoint
is `1 / sqrt L` and whose ceiling endpoint is `sqrt (n / L)`. -/
theorem geomCenter_eq {n L : ℝ} (hn : 0 < n) (hL : 0 < L) :
    geomCenter n L = Real.sqrt (Real.sqrt n) / Real.sqrt L := by
  unfold geomCenter
  rw [endpoint_product hn hL, Real.sqrt_div (Real.sqrt_nonneg n) L]

/-- **The center is the ratio-midpoint.**  `ceiling / center = center / floor`: the geometric center
is equidistant *in ratio* from both endpoints (each ratio equals `n^{1/4}`).  Collapsing the prize to
an `O(1)` constant is therefore the demand to descend a further `n^{1/4}` factor below this geometric
center.  Pure arithmetic — derived only from the geometric-mean identity. -/
theorem ratio_symmetric {n L : ℝ} (hn : 0 < n) (hL : 0 < L) :
    ceilingEndpoint n L / geomCenter n L = geomCenter n L / floorEndpoint n L := by
  rw [div_eq_div_iff (ne_of_gt (geomCenter_pos hn hL)) (ne_of_gt (floorEndpoint_pos hn hL))]
  rw [geomCenter_mul_self hn hL]
  ring

/-- **The center lies inside the bracket.**  For `1 ≤ n` the geometric center sits between the floor
and ceiling endpoints, `floor ≤ center ≤ ceiling`.  Together with `ratio_symmetric` this confirms the
center is an honest interior point of the `sqrt n`-wide prize bracket. -/
theorem center_between {n L : ℝ} (hn : 1 ≤ n) (hL : 0 < L) :
    floorEndpoint n L ≤ geomCenter n L ∧ geomCenter n L ≤ ceilingEndpoint n L := by
  have hn0 : 0 < n := lt_of_lt_of_le one_pos hn
  have hsL : 0 < Real.sqrt L := Real.sqrt_pos.2 hL
  -- Floor and ceiling in `· / sqrt L` form.
  have hfloor : floorEndpoint n L = 1 / Real.sqrt L := by
    unfold floorEndpoint prizeScale
    rw [Real.sqrt_mul (le_of_lt hn0), div_mul_eq_div_div,
      div_self (ne_of_gt (Real.sqrt_pos.2 hn0))]
  have hceil : ceilingEndpoint n L = Real.sqrt n / Real.sqrt L := by
    unfold ceilingEndpoint prizeScale
    rw [Real.sqrt_mul (le_of_lt hn0),
      div_eq_div_iff (ne_of_gt (mul_pos (Real.sqrt_pos.2 hn0) hsL)) (ne_of_gt hsL),
      ← mul_assoc, Real.mul_self_sqrt (le_of_lt hn0)]
  have hcenter : geomCenter n L = Real.sqrt (Real.sqrt n) / Real.sqrt L := geomCenter_eq hn0 hL
  -- `1 ≤ sqrt n` and `sqrt (sqrt n) ≤ sqrt n`, hence `1 ≤ sqrt (sqrt n) ≤ sqrt n`.
  have h1n : (1 : ℝ) ≤ Real.sqrt n := by
    rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
    exact Real.sqrt_le_sqrt hn
  have h1q : (1 : ℝ) ≤ Real.sqrt (Real.sqrt n) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
    exact Real.sqrt_le_sqrt h1n
  have hqn : Real.sqrt (Real.sqrt n) ≤ Real.sqrt n := by
    have : Real.sqrt n ≤ Real.sqrt n * Real.sqrt n := by
      nlinarith [Real.sqrt_nonneg n, h1n]
    calc Real.sqrt (Real.sqrt n)
        ≤ Real.sqrt (Real.sqrt n * Real.sqrt n) := Real.sqrt_le_sqrt this
      _ = Real.sqrt n := by rw [Real.sqrt_mul_self (Real.sqrt_nonneg n)]
  refine ⟨?_, ?_⟩
  · rw [hfloor, hcenter]
    exact div_le_div_of_nonneg_right h1q (le_of_lt hsL)
  · rw [hcenter, hceil]
    exact div_le_div_of_nonneg_right hqn (le_of_lt hsL)

end ArkLib.ProximityGap.Frontier.ShawValueBracketCenter

#print axioms ArkLib.ProximityGap.Frontier.ShawValueBracketCenter.prizeScale_pos
#print axioms ArkLib.ProximityGap.Frontier.ShawValueBracketCenter.endpoint_product
#print axioms ArkLib.ProximityGap.Frontier.ShawValueBracketCenter.geomCenter_mul_self
#print axioms ArkLib.ProximityGap.Frontier.ShawValueBracketCenter.geomCenter_eq
#print axioms ArkLib.ProximityGap.Frontier.ShawValueBracketCenter.ratio_symmetric
#print axioms ArkLib.ProximityGap.Frontier.ShawValueBracketCenter.center_between
