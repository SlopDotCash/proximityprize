/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.DeepBandOrbitCountDescent

/-!
# The GROWTH LAW of the deep-band distinct-gamma ORBIT count at the shallow rungs (#444)

`DeepBandOrbitCountDescent` pins the deep-band orbit counts at the shallow rungs `r = 3, 4` as
closed forms via the 2-adic self-similar descent, but ONLY certifies the numerical rungs
`n = 16..128` by `decide` (no general-`g` growth law) and never states how the orbit count
COMPARES to the union-count floor `O <= 1` that `ThreadD` (`_ThreadD_UnionCountFloor`) needs at
binding.

This file extends that descent with the GENERAL-`g` growth law and the resulting strict
super-linearity, which is the precise QUANTITATIVE obstruction to the union-count floor:

* `orbitCount3 g = g*(g-1)/2`  (`= C(g,2)`, quadratic in `g = n/4`, so `~ n^2/32`);
* `orbitCount4 (2*h) = 2*h^2*(h-1) + 1`  (cubic in `g`, so `~ n^3/512`);
* both are STRICTLY super-linear: `orbitCount3 g > g` for `g >= 4` and
  `orbitCount4 (2*h) > 2*h` (`= g/... `; `> g/2`) growing without bound.

## Why this is a `ThreadD` obstruction, not a closure

`ThreadD` reduces the prize floor `hfloor` to the union-count `UnionCountBadStacks _ _ n`, i.e. to
the distinct-gamma ORBIT count being `<= 1` at the binding rung (orbit-collapse `O -> 1`).  At the
SHALLOW rungs `r = 3, 4` the orbit count is the polynomial-in-`n` quantity pinned here, which is
super-linear (`>= C(g,2) >> 1` and `>= 2*h^2*(h-1)+1 >> 1`).  So the union-count floor is
FALSE at the shallow rungs by a wide and GROWING margin; the collapse to `O = 1` can only happen
AT the deep binding rung `r ~ log n` (= the open growth law `DstarPlateauLeBudget` = the
BGK/BCHKS wall).  This file makes the obstruction QUANTITATIVE: it lower-bounds the gap
`orbitCount - 1` that the descent must close between the shallow rung and binding.

## Honest scope

Pure-`ℕ` structural growth law over the two proven in-tree shallow closed forms (`orbitCount3`,
`orbitCount4` of `DeepBandOrbitCountDescent`).  It is NOT a bound on the deep rung `r ~ log n` (=
`|Σ_r(μ_s)|` = BCHKS 1.12 = the BGK wall, untouched).  Character-sum-free, char-agnostic, NOT
thinness-essential.  Does NOT close CORE `M(μ_n) <= C·√(n·log(p/n))`.  It quantifies the GAP the
open growth law must cross, it does not cross it.

Probe: `scripts/probes/probe_orbit_count_growth_law.py` (the closed forms + strict super-linearity +
the blowing-up gap to the `O <= 1` floor, exact `n = 16..512`, NEVER `n = q-1`).
-/

namespace ArkLib.ProximityGap.OrbitCountGrowthLaw

open ArkLib.ProximityGap
open ArkLib.ProximityGap.DeepBandOrbitCountDescent

/-- **The depth-3 orbit count is the quadratic `g*(g-1)/2`** (`= C(g,2)`, `g = n/4`). -/
theorem orbitCount3_closed (g : ℕ) : orbitCount3 g = g * (g - 1) / 2 := by
  rw [orbitCount3, Nat.choose_two_right]

/-- **The depth-4 orbit count is the cubic `2*h^2*(h-1) + 1`** at scale `n = 8*h` (`g = 2*h`):
`orbitCount4 (2*h) = DeepBandR3.deepBandBadCount h = 2*h^2*(h-1) + 1`. -/
theorem orbitCount4_closed (h : ℕ) :
    orbitCount4 (2 * h) = 2 * h ^ 2 * (h - 1) + 1 := by
  rw [orbitCount4]
  have hh : (2 * h) / 2 = h := by omega
  rw [hh, DeepBandR3.deepBandBadCount]

/-- **The depth-3 orbit count is STRICTLY super-linear** (`> g` for `g >= 4`, i.e. `n >= 16`).
`orbitCount3 g = C(g,2) = g*(g-1)/2 > g` once `g - 1 > 2`, i.e. `g >= 4`. -/
theorem orbitCount3_gt_self (g : ℕ) (hg : 4 ≤ g) : g < orbitCount3 g := by
  rw [orbitCount3_closed]
  -- g < g*(g-1)/2  ⟺  2*g < g*(g-1)  (since 2 ∣ g*(g-1)), which holds for g ≥ 4.
  obtain ⟨e, rfl⟩ : ∃ e, g = e + 4 := ⟨g - 4, by omega⟩
  have he : e + 4 - 1 = e + 3 := by omega
  rw [he]
  -- (e+3)*(e+4) is a product of consecutive naturals, hence even.
  have hdvd : 2 ∣ (e + 4) * (e + 3) := by
    have := Nat.even_mul_succ_self (e + 3)
    rw [mul_comm]
    simpa using this.two_dvd
  obtain ⟨c, hc⟩ := hdvd
  rw [hc, Nat.mul_div_cancel_left _ (by norm_num)]
  nlinarith [hc]

/-- **The depth-4 orbit count is STRICTLY super-linear** (`> 2*h` for `h >= 2`, i.e. `g >= 4`,
`n >= 16`).  `orbitCount4 (2*h) = 2*h^2*(h-1) + 1 > 2*h` once `h^2*(h-1) >= h`, i.e. `h >= 2`. -/
theorem orbitCount4_gt_self (h : ℕ) (hh : 2 ≤ h) : 2 * h < orbitCount4 (2 * h) := by
  rw [orbitCount4_closed]
  obtain ⟨e, rfl⟩ : ∃ e, h = e + 2 := ⟨h - 2, by omega⟩
  have he : e + 2 - 1 = e + 1 := by omega
  rw [he]
  nlinarith []

/-- **The gap to the `ThreadD` `O <= 1` union-count floor is STRICTLY increasing in `h`** at the
depth-4 shallow rung: `orbitCount4 (2*h) - 1 = 2*h^2*(h-1)` and this is strictly monotone for
`h >= 2`.  The union-count floor (`ThreadD.UnionCountBadStacks _ _ n`, needing `O <= 1`) is missed
at the shallow rung by `2*h^2*(h-1)`, which blows up: the descent to binding `r ~ log n` must cross
a GROWING gap.  This is the quantitative obstruction, NOT a closure. -/
theorem orbitCount4_gap_strict_mono (h : ℕ) (hh : 2 ≤ h) :
    orbitCount4 (2 * h) - 1 < orbitCount4 (2 * (h + 1)) - 1 := by
  rw [orbitCount4_closed, orbitCount4_closed]
  have e1 : 2 * h ^ 2 * (h - 1) + 1 - 1 = 2 * h ^ 2 * (h - 1) := by omega
  have e2 : 2 * (h + 1) ^ 2 * (h + 1 - 1) + 1 - 1 = 2 * (h + 1) ^ 2 * h := by
    have : h + 1 - 1 = h := by omega
    rw [this]; omega
  rw [e1, e2]
  obtain ⟨e, rfl⟩ : ∃ e, h = e + 2 := ⟨h - 2, by omega⟩
  have he : e + 2 - 1 = e + 1 := by omega
  rw [he]
  nlinarith []

/-- **Headline: the shallow-rung orbit-count growth law obstructs the `O <= 1` floor.**
For every prize-tower step `h >= 2` (`n = 8*h >= 16`):
the depth-3 orbit count is the quadratic `C(g,2) > g`, the depth-4 orbit count is the cubic
`2*h^2*(h-1)+1 > 2*h`, and the gap `orbitCount4 - 1` to the `ThreadD` union-count floor `O <= 1` is
strictly increasing.  So the union-count floor is FALSE at the shallow rungs by a strictly growing
margin; the `O -> 1` collapse lives only at binding `r ~ log n` (the open growth law = the wall). -/
theorem orbit_count_growth_obstructs_union_floor (h : ℕ) (hh : 2 ≤ h) :
    orbitCount3 (2 * h) = (2 * h) * (2 * h - 1) / 2 ∧
    (2 * h) < orbitCount3 (2 * h) ∧
    orbitCount4 (2 * h) = 2 * h ^ 2 * (h - 1) + 1 ∧
    (2 * h) < orbitCount4 (2 * h) ∧
    orbitCount4 (2 * h) - 1 < orbitCount4 (2 * (h + 1)) - 1 :=
  ⟨orbitCount3_closed (2 * h),
   orbitCount3_gt_self (2 * h) (by omega),
   orbitCount4_closed h,
   orbitCount4_gt_self h hh,
   orbitCount4_gap_strict_mono h hh⟩

/-! ## Numerical rungs (must reproduce the data; `n = 4*g = 8*h`). -/

/-- `n = 16` (`h = 2`): `orbitCount4 = 9`, gap to the `O<=1` floor `= 8 = 2*2^2*(2-1)`. -/
theorem rung_n16 : orbitCount4 4 = 9 ∧ orbitCount4 4 - 1 = 8 := ⟨by decide, by decide⟩

/-- `n = 32` (`h = 4`): `orbitCount4 = 97`, gap `= 96`. -/
theorem rung_n32 : orbitCount4 8 = 97 ∧ orbitCount4 8 - 1 = 96 := ⟨by decide, by decide⟩

/-- `n = 64` (`h = 8`): `orbitCount4 = 897`, gap `= 896`. -/
theorem rung_n64 : orbitCount4 16 = 897 ∧ orbitCount4 16 - 1 = 896 := ⟨by decide, by decide⟩

/-- `n = 128` (`h = 16`): `orbitCount4 = 7681`, gap `= 7680`. -/
theorem rung_n128 : orbitCount4 32 = 7681 ∧ orbitCount4 32 - 1 = 7680 := ⟨by decide, by decide⟩

/-- Depth-3 super-linearity at the tower: `orbitCount3 (2*h) > 2*h` reproduced at `n = 16..128`. -/
theorem rung_oc3_superlinear :
    4 < orbitCount3 4 ∧ 8 < orbitCount3 8 ∧ 16 < orbitCount3 16 ∧ 32 < orbitCount3 32 :=
  ⟨by decide, by decide, by decide, by decide⟩

end ArkLib.ProximityGap.OrbitCountGrowthLaw

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.OrbitCountGrowthLaw.orbitCount3_closed
#print axioms ArkLib.ProximityGap.OrbitCountGrowthLaw.orbitCount4_closed
#print axioms ArkLib.ProximityGap.OrbitCountGrowthLaw.orbitCount3_gt_self
#print axioms ArkLib.ProximityGap.OrbitCountGrowthLaw.orbitCount4_gt_self
#print axioms ArkLib.ProximityGap.OrbitCountGrowthLaw.orbitCount4_gap_strict_mono
#print axioms ArkLib.ProximityGap.OrbitCountGrowthLaw.orbit_count_growth_obstructs_union_floor
