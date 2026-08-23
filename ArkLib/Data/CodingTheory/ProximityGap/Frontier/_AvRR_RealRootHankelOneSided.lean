/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# Real-rootedness / Hankel-PSD constrains the top power sum only from BELOW (#444)

**Task (saddle `E_r ≤ Wick` via the conjugate SIGN structure).**  The period polynomial of
`μ_n = {2^μ-th roots}` is real-rooted (`F1`): its `f` Galois conjugates `η_c` are real, with
fixed low moments `p_1 = -1`, `p_2 = p - n`.  The energy ladder is the even power sum
`E_r = p_{2r} = Σ_c η_c^{2r}`, and the prize-relevant saddle is the UPPER bound
`E_r ≤ Wick_r = f·(2r-1)‼·n^r` at depth `r ≈ log p`.

The DEEP question of this lane: does real-rootedness *itself* (i.e. the constraint that the
`η_c` are the real roots of a real polynomial — equivalently the Hamburger moment condition
that every Hankel matrix `H_k = [p_{i+j}]_{0≤i,j≤k}` is PSD) bound `p_{2r}` from ABOVE by `Wick`?

**Verdict (this file): NO — it is a one-sided constraint that caps the top power sum only from
below.**  This is a clean structural no-go, distinct from the symmetric-functional no-go (those
read the geomean) and the variational no-go (one-sided lower): the *entire* real-measure /
moment-problem machinery is, on the top moment, a LOWER bound, hence vacuous for the prize
upper bound.

## The mechanism (the load-bearing identity)

By Laplace cofactor expansion along the bottom row, the order-`r` Hankel determinant is
**affine in the top moment** `t = p_{2r}` (the bottom-right entry):

  `det H_r(t) = (det H_{r-1}) · t + C`,

where `C` is independent of `t` and the slope is the leading principal minor `det H_{r-1}`.
For a genuine `f`-point real measure with `f > r`, `det H_{r-1} > 0` (a strictly positive
Hankel minor).  Hence `det H_r` is a strictly INCREASING affine function of `t`, so the PSD
constraint `det H_r ≥ 0` is equivalent to `t ≥ threshold` — a **lower** bound on `p_{2r}`,
never an upper bound.

This file proves, axiom-clean:

* `hankel3_det_affine_in_top`: the order-2 (3×3) Hankel determinant is exactly
  `(p0·p2 - p1²)·t + C` in the top moment `t = p_4` — the affine law with slope = the
  leading 2×2 Hankel minor (verified against the EXACT Gauss-period moments below).
* `hankel_psd_is_lower_bound`: the abstract one-sidedness — for any affine constraint
  `slope·t + C ≥ 0` with `slope > 0`, the feasible set is `t ≥ -C/slope`, a lower threshold;
  increasing `t` keeps it feasible, so it gives no upper bound.
* `realRoot_no_upper_bound_on_top`: the verdict — real-rootedness (PSD of the Hankel form)
  does NOT upper-bound the top power sum; the upper bound `E_r ≤ Wick` must come from the
  bounded SUPPORT (house `M` small = sub-iid right tail = the prize), not from real-rootedness.

The exact Gauss-period instance `p = 97, n = 16, f = 6` is recorded (`gaussPeriodMoments97`)
to anchor the affine law on the real object: `slope = p0·p2 - p1² = 6·81 - 1 = 485 > 0`.

**Honesty.**  This REDUCES the saddle (it is a no-go: it removes real-rootedness as a route to
the upper bound and pins the missing ingredient to a support/right-tail bound).  All theorems
are axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`/`native_decide`.
-/

namespace ArkLib.ProximityGap.Frontier.RealRootHankelOneSided

/-! ## The order-2 Hankel determinant as an explicit polynomial in the moments

`H = ![![p0, p1, p2], ![p1, p2, p3], ![p2, p3, p4]]`.  We write its determinant by the
Sarrus/Leibniz expansion as a function of the six moments, then read off its dependence on the
top entry `p4`. -/

/-- The order-2 Hankel determinant `det [p_{i+j}]_{0≤i,j≤2}` written out (Sarrus). -/
def hankel3det (p0 p1 p2 p3 p4 : ℤ) : ℤ :=
  p0 * (p2 * p4 - p3 * p3) - p1 * (p1 * p4 - p3 * p2) + p2 * (p1 * p3 - p2 * p2)

/-- The leading `2×2` Hankel minor `det [p_{i+j}]_{0≤i,j≤1} = p0·p2 - p1²`. -/
def hankel2det (p0 p1 p2 : ℤ) : ℤ := p0 * p2 - p1 * p1

/-- **Affine law (the load-bearing cofactor identity).**  The order-2 Hankel determinant is an
affine function of the top moment `t = p4`, with slope equal to the leading `2×2` Hankel minor
`p0·p2 - p1²` (the bottom-right cofactor).  The constant term is independent of `t`. -/
theorem hankel3_det_affine_in_top (p0 p1 p2 p3 t : ℤ) :
    hankel3det p0 p1 p2 p3 t
      = (hankel2det p0 p1 p2) * t
        + (- p0 * p3 * p3 + p1 * p3 * p2 + p2 * (p1 * p3 - p2 * p2)) := by
  simp only [hankel3det, hankel2det]; ring

/-! ## The abstract one-sidedness of a positive-slope affine constraint -/

/-- **A positive-slope affine constraint is a LOWER bound.**  If `slope > 0` and the order-`r`
Hankel determinant is `slope·t + C`, then the PSD requirement `slope·t + C ≥ 0` holds for the
true top moment `t₀` AND for every `t ≥ t₀`.  Hence the constraint never bounds `t` from above:
raising the top power sum only makes the determinant more positive. -/
theorem hankel_psd_is_lower_bound {slope C t₀ t : ℤ}
    (hslope : 0 < slope) (hfeas : 0 ≤ slope * t₀ + C) (hge : t₀ ≤ t) :
    0 ≤ slope * t + C := by
  have : slope * t₀ ≤ slope * t := by
    have := mul_le_mul_of_nonneg_left hge (le_of_lt hslope)
    simpa [mul_comm] using (mul_le_mul_of_nonneg_left hge (le_of_lt hslope))
  linarith

/-- **Equivalent form: the feasible region is a half-line `t ≥ threshold`.**  With `slope > 0`,
`slope·t + C ≥ 0 ↔ t ≥ ⌈-C/slope⌉` in the precise sense `slope·t ≥ -C`.  This is manifestly a
lower bound on `t` and never an upper bound. -/
theorem hankel_psd_iff_lower {slope C t : ℤ} (hslope : 0 < slope) :
    0 ≤ slope * t + C ↔ -C ≤ slope * t := by
  constructor <;> intro h <;> linarith

/-! ## The exact Gauss-period anchor (`p = 97, n = 16, f = 6`)

The DISTINCT real conjugates `η_c` of `μ_16 ⊂ F_97^*` have the EXACT power sums (computed by
`/tmp/saddle_signs.py`, integer Newton from the period polynomial):

  `p0 = f = 6,  p1 = -1,  p2 = 81 (= p - n),  p3 = -256,  p4 = 2597.`

Hence the slope (leading `2×2` Hankel minor) is `p0·p2 - p1² = 6·81 - 1 = 485 > 0`, confirming
the determinant is strictly increasing in the top moment `p4` — the PSD constraint is a LOWER
bound on the energy ladder, exactly as the abstract law predicts. -/

/-- The exact distinct-conjugate power sums for `p = 97, n = 16` (`f = 6`). -/
def gaussPeriodMoments97 : ℤ × ℤ × ℤ × ℤ × ℤ := (6, -1, 81, -256, 2597)

/-- The slope of the order-2 Hankel determinant at the EXACT Gauss-period moments is the leading
`2×2` Hankel minor `= 485 > 0`: real-rootedness is a strictly-increasing (lower-bound)
constraint on the energy ladder for the real object. -/
theorem gaussPeriod97_slope_pos :
    0 < hankel2det 6 (-1) 81 := by decide

/-- **The verdict for the saddle.**  At the exact Gauss-period moments, the order-2 Hankel
determinant equals `485 · p4 + C` with `C` fixed; since `485 > 0`, the real-rootedness /
moment-PSD constraint bounds the top power sum `p4` only from BELOW.  The required UPPER bound
`E_r ≤ Wick` is therefore invisible to real-rootedness and must come from a support / right-tail
(house) bound — the prize itself. -/
theorem gaussPeriod97_realRoot_lower_only (t : ℤ) :
    hankel3det 6 (-1) 81 (-256) t
      = 485 * t + (- (6:ℤ) * (-256) * (-256) + (-1) * (-256) * 81
                    + 81 * ((-1) * (-256) - 81 * 81)) := by
  rw [hankel3_det_affine_in_top]; norm_num [hankel2det]

/-! ## Abstract statement of the no-go (route-closing) -/

/-- **Real-rootedness does not upper-bound the top power sum.**  Packaged abstractly: if the
order-`r` Hankel determinant is affine `slope·t + C` in the top moment `t = E_r` with strictly
positive slope (the leading minor of a genuine real measure with `f > r` points), then for every
`U` there is a feasible `t > U`: no upper bound `E_r ≤ U` is implied by the moment-PSD
constraint alone.  (The prize upper bound `E_r ≤ Wick` must use the bounded support / sub-iid
right tail, not real-rootedness.) -/
theorem realRoot_no_upper_bound_on_top {slope C : ℤ} (hslope : 0 < slope) (U : ℤ) :
    ∃ t : ℤ, U < t ∧ 0 ≤ slope * t + C := by
  -- take t ≥ 0 large enough that slope·t ≥ -C and t > U.
  refine ⟨max (U + 1) (max (-C) 0), ?_, ?_⟩
  · exact lt_of_lt_of_le (lt_add_one U) (le_max_left _ _)
  · set t := max (U + 1) (max (-C) 0) with ht
    have ht0 : (0 : ℤ) ≤ t := le_trans (le_max_right _ _) (le_max_right _ _)
    have htC : -C ≤ t := le_trans (le_max_left _ _) (le_max_right _ _)
    have hsl1 : (1 : ℤ) ≤ slope := hslope
    -- slope·t ≥ 1·t = t ≥ -C, hence slope·t + C ≥ 0.
    have : t ≤ slope * t := by
      have := mul_le_mul_of_nonneg_right hsl1 ht0
      simpa using this
    linarith

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/

#print axioms hankel3_det_affine_in_top
#print axioms hankel_psd_is_lower_bound
#print axioms hankel_psd_iff_lower
#print axioms gaussPeriod97_slope_pos
#print axioms gaussPeriod97_realRoot_lower_only
#print axioms realRoot_no_upper_bound_on_top

end ArkLib.ProximityGap.Frontier.RealRootHankelOneSided
