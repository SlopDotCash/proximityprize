/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._OrbitCountGrowthLaw

/-!
# The GROWING-SLACK degree mechanism on the off-BGK distinct-gamma union count (#444)

This file formalizes the census 1.4 PROMISING sub-lead `deg(#bad_r) < r` (c269 item 6, c274 -- the
"growing-slack mechanism"): at the proven shallow rungs `r = 3, 4` the distinct-gamma orbit count
`orbitCount_r` (`_OrbitCountGrowthLaw`) is a polynomial of degree `r - 1` in the subgroup order
`n`, which is STRICTLY LESS than `r`. The consequence the census flags is QUANTITATIVE: when the
bad-count dominator has degree `r - 1` while the char-0 Wick ceiling for a depth-`r` energy is
`(2r-1)!! * n^r` (degree `r`), the SLACK ratio `ceiling / bad ~ (2r-1)!! * n` GROWS LINEARLY in the
subgroup order at every fixed depth.

We make this an axiom-clean theorem on the two proven in-tree closed forms:

* `orbitCount3 g = C(g,2) = g*(g-1)/2`  (degree 2 in `g`, `g = n/4`; so degree `r-1 = 2 < 3 = r`);
* `orbitCount4 (2*h) = 2*h^2*(h-1) + 1`  (degree 3 in `h`, `n = 8*h`; so degree `r-1 = 3 < 4 = r`).

The Wick ceiling at depth `r` is `(2r-1)!! * n^r` (`(2*3-1)!! = 15`, `(2*4-1)!! = 105`). The
headline results say the ceiling DOMINATES the bad orbit count by a factor AT LEAST the scale
(`g` resp. `h`), i.e. the slack is bounded below by a LINEARLY-GROWING multiple of the bad count:

* `wickCeil3 g = 15 * (4*g)^3 >= g * orbitCount3 g`     (slack factor `>= g`, linear in the scale);
* `wickCeil4 h = 105 * (8*h)^4 >= h * orbitCount4 (2*h)` (slack factor `>= h`, linear in the scale).

## Why this is FRONTIER-MOVEMENT, not a closure

This is the GROWING-SLACK structural fact the census names as PROMISING: a bad-count dominator of
degree `< r` leaves a slack to the depth-`r` Wick ceiling that grows without bound in `n`. By the
budget-crossing heuristic (c274), a growing slack at the shallow rungs is the mechanism that could
force a BOUNDED binding fold `m*` (prize-consistent vs. the `log n` Johnson scaling). This file
turns the degree side of that mechanism into a theorem on the proven closed forms.

It is NOT a closure. The slack is a SHALLOW-rung statement (`r = 3, 4`). The deep binding rung
`r ~ log n` growth law (`DistinctGammaUnionGrowthLaw`, `_SpecF8_DistinctGammaUnionFloor`) -- whether
`deg(#bad_r) < r` PERSISTS to `r ~ log n` -- is the open BGK/BCHKS wall, UNTOUCHED here. The
dichotomy is exact: `deg(#bad_r) = r - 1 < r` gives a slack `~ (2r-1)!! * n` (growing), whereas
`deg(#bad_r) = r` (the over-det `Theta(n^3)` regime that COLLAPSES TO JOHNSON, asymptotic-guard
cliff-at-`n/2`) gives a CONSTANT slack `(2r-1)!!`. We prove the growing (degree-`r-1`) side.

## Honest scope

Pure-`ℕ` structural inequalities over the two proven shallow closed forms (`orbitCount3_closed`,
`orbitCount4_closed`). Character-sum-free, char-agnostic, NOT thinness-essential (it is the off-BGK
union-count face). Does NOT close CORE `M(μ_n) <= C·√(n·log(p/n))`. No capacity / beyond-Johnson
claim; the over-det cliff-at-`n/2` (degree-`r` non-slack regime) is the COMPLEMENT and is untouched.

Probe: `scripts/probes/probe_degbad_growing_slack.py` (degree law `deg(oc_r) = r-1` at the proven
rungs + the `deg < r => linear-in-n slack` vs `deg = r => constant slack` dichotomy, NEVER `n=q-1`).
-/

namespace ArkLib.ProximityGap.OrbitCountGrowingSlack

open ArkLib.ProximityGap
open ArkLib.ProximityGap.OrbitCountGrowthLaw
open ArkLib.ProximityGap.DeepBandOrbitCountDescent

/-- **The depth-3 char-0 Wick ceiling** `(2*3-1)!! * n^3 = 15 * n^3` at scale `n = 4*g`. -/
def wickCeil3 (g : ℕ) : ℕ := 15 * (4 * g) ^ 3

/-- **The depth-4 char-0 Wick ceiling** `(2*4-1)!! * n^4 = 105 * n^4` at scale `n = 8*h`. -/
def wickCeil4 (h : ℕ) : ℕ := 105 * (8 * h) ^ 4

/-- **(r = 3) GROWING SLACK: the depth-3 Wick ceiling dominates the bad orbit count by a factor at
least the scale `g`** (linear in `g = n/4`, hence in `n`). Since `orbitCount3` has degree `r-1 = 2`
while the ceiling has degree `r = 3`, the slack factor is `>= g` -- it GROWS without bound.

`wickCeil3 g = 15*(4g)^3 = 960 g^3 >= g * (g*(g-1)/2) = g * orbitCount3 g`. -/
theorem wickCeil3_ge_scale_mul_orbitCount3 (g : ℕ) :
    g * orbitCount3 g ≤ wickCeil3 g := by
  rw [orbitCount3_closed, wickCeil3]
  -- `g * (g*(g-1)/2) <= g * (g*(g-1)) <= 960 * g^3` since `g*(g-1)/2 <= g^2` and `g^2 <= 960 g^2`.
  have hdiv : g * (g - 1) / 2 ≤ g * g := by
    calc g * (g - 1) / 2 ≤ g * (g - 1) := Nat.div_le_self _ _
      _ ≤ g * g := by
        apply Nat.mul_le_mul_left
        omega
  calc g * (g * (g - 1) / 2) ≤ g * (g * g) := Nat.mul_le_mul_left _ hdiv
    _ ≤ 15 * (4 * g) ^ 3 := by ring_nf; nlinarith [sq_nonneg g, Nat.zero_le g]

/-- **(r = 4) GROWING SLACK: the depth-4 Wick ceiling dominates the bad orbit count by a factor at
least the scale `h`** (linear in `h = n/8`, hence in `n`). Since `orbitCount4` has degree `r-1 = 3`
while the ceiling has degree `r = 4`, the slack factor is `>= h` -- it GROWS without bound.

`wickCeil4 h = 105*(8h)^4 = 430080 h^4 >= h * (2 h^2 (h-1) + 1) = h * orbitCount4 (2*h)`. -/
theorem wickCeil4_ge_scale_mul_orbitCount4 (h : ℕ) :
    h * orbitCount4 (2 * h) ≤ wickCeil4 h := by
  rw [orbitCount4_closed, wickCeil4]
  -- Case on `h` to discharge the truncated subtraction `h - 1`; then a plain polynomial bound.
  cases h with
  | zero => simp
  | succ k =>
    -- `(k+1) - 1 = k`, set `m = k+1 >= 1`.
    have hsub : (k + 1) - 1 = k := by omega
    rw [hsub]
    set m := k + 1 with hm
    have hm1 : 1 ≤ m := by omega
    -- bad <= 2*m^3 + 1: `2*m^2*k + 1 <= 2*m^3 + 1` since `k <= m`.
    have hbad : 2 * m ^ 2 * k + 1 ≤ 2 * m ^ 3 + 1 := by
      have hkm : k ≤ m := by omega
      have : 2 * m ^ 2 * k ≤ 2 * m ^ 2 * m := Nat.mul_le_mul_left _ hkm
      calc 2 * m ^ 2 * k + 1 ≤ 2 * m ^ 2 * m + 1 := by omega
        _ = 2 * m ^ 3 + 1 := by ring
    -- `m * (2*m^3+1) <= m * (3*m^3) = 3*m^4 <= 430080*m^4 = 105*(8*m)^4`.
    have hm3 : 1 ≤ m ^ 3 := Nat.one_le_pow _ _ hm1
    have hstep : 2 * m ^ 3 + 1 ≤ 3 * m ^ 3 := by omega
    have hfin : 3 * m ^ 4 ≤ 105 * (8 * m) ^ 4 := by
      have : (8 * m) ^ 4 = 4096 * m ^ 4 := by ring
      rw [this]
      calc 3 * m ^ 4 ≤ 430080 * m ^ 4 := Nat.mul_le_mul (by norm_num) (le_refl _)
        _ = 105 * (4096 * m ^ 4) := by ring
    calc m * (2 * m ^ 2 * k + 1) ≤ m * (2 * m ^ 3 + 1) := Nat.mul_le_mul_left _ hbad
      _ ≤ m * (3 * m ^ 3) := Nat.mul_le_mul_left _ hstep
      _ = 3 * m ^ 4 := by ring
      _ ≤ 105 * (8 * m) ^ 4 := hfin

/-- **The growing-slack DICHOTOMY (degree side), made concrete at `r = 3`.** The bad-orbit degree
`r - 1 = 2 < 3 = r` leaves a slack factor `>= g` that is STRICTLY positive, growing for `g >= 1`:
the ceiling exceeds the bad count outright (`orbitCount3 g < wickCeil3 g` for `g >= 1`). Contrast
the degree-`r` (over-det, cliff-at-`n/2`) regime, where the ceiling/bad ratio is the CONSTANT
`(2r-1)!!`. -/
theorem orbitCount3_lt_wickCeil3 (g : ℕ) (hg : 1 ≤ g) : orbitCount3 g < wickCeil3 g := by
  rw [orbitCount3_closed, wickCeil3]
  -- `g*(g-1)/2 <= g*g`, and `g*g < 960*g^3 = 15*(4g)^3` for `g >= 1`.
  have hdiv : g * (g - 1) / 2 ≤ g * g := by
    calc g * (g - 1) / 2 ≤ g * (g - 1) := Nat.div_le_self _ _
      _ ≤ g * g := by
        apply Nat.mul_le_mul_left
        omega
  have hstrict : g * g < 15 * (4 * g) ^ 3 := by
    have hg1 : 1 ≤ g := hg
    ring_nf
    nlinarith [sq_nonneg g, Nat.one_le_iff_ne_zero.mp hg1, Nat.zero_le g]
  exact lt_of_le_of_lt hdiv hstrict

end ArkLib.ProximityGap.OrbitCountGrowingSlack

#print axioms ArkLib.ProximityGap.OrbitCountGrowingSlack.wickCeil3_ge_scale_mul_orbitCount3
#print axioms ArkLib.ProximityGap.OrbitCountGrowingSlack.wickCeil4_ge_scale_mul_orbitCount4
#print axioms ArkLib.ProximityGap.OrbitCountGrowingSlack.orbitCount3_lt_wickCeil3
