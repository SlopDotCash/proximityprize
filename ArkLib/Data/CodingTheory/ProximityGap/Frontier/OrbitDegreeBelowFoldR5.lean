/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.OrbitCount5GeneralNormalForm

/-!
# The `OrbitDegreeBelowFold` obligation, CERTIFIED at `r = 5` (#444)

`_OffBGK_DegBadRGrowingSlack` settled sub-lead (A) — the growing-slack mechanism — at the order-2
rungs `r = 3, 4`: the distinct-γ ORBIT count `O_r` grows one polynomial degree SLOWER than the raw
`#bad_r`, `deg(O_r) = r − 1 < r = deg(#bad_r)`, the one-degree gap being the orbit-size-`n`
equivariance slack.  It named the all-`r` form `OrbitDegreeBelowFold` as the OPEN obligation and
explicitly recorded that the order-2 parity descent **stops at `r = 4`** (at `r = 5` the maximizing
line flips to the half-order `d = n/2` resonance, invisible to the order-2 character), so
`deg(O_r) = r − 1` was **NOT certified for `r ≥ 5`**.

This file discharges the `r = 5` instance, using the PROVEN `r = 5` half-order orbit closed form
(`DeepBandR5Bound`, `OrbitCount5GeneralNormalForm.twentyfour_mul_fullOrb_even`):

  `deepBandFullOrb (2h) = (4(2h)³ + 3(2h)² − 10(2h)) / 24`,
  i.e. `24·O₅ + 10g = 4g³ + 3g²` (even `g`).

The degree is **EXACTLY 3** in `g = n/4`:

* **upper** `O₅(g) ≤ g³` (`orbit5_le_g_cubed`, all `g`): `deg(O₅) ≤ 3`;
* **lower** `g³ ≤ 12·O₅(g)` for even `g ≥ 4` (`g_cubed_le_twelve_orbit5_even`): `deg(O₅) ≥ 3`.

So `deg(O₅) = 3`.  Since the fold is `r = 5`, this is `deg(O₅) = r − 2`, which is `< r − 1 = 4` —
i.e. the half-order rung gives an EXTRA degree of growing slack beyond the `r = 3, 4` order-2 rungs
(`orbit5_degree_strictly_below_fold_minus_one` records `3 < 4` concretely).  Mechanism: the `r = 5`
maximizer is the half-order `d = n/2` line, whose orbit size is `n/2` (not the full `n` of the
order-2 rungs), and the raw `#bad₅` itself already dropped to degree 4 (`< r = 5`); dividing by the
orbit size `n/2 ∼ g` removes one more degree, landing `O₅` at degree `r − 2`.

(Numeric anchor: at `n = 16`, `g = 4`, `O₅ = 11`, and `4³ = 64 ≤ 12·11 = 132`, `11 ≤ 64`.)

## Honest scope (NOT a δ* pin)

This CERTIFIES the `r = 5` rung of the named-open `OrbitDegreeBelowFold` obligation — one more rung
than `_OffBGK_DegBadRGrowingSlack` reached — and shows the slack is STRONGER (by one degree) at the
half-order rung.  It is NOT a δ* pin and does NOT close the prize.  Per that file's own caveat 2:
even `deg(O_r) < r` for ALL `r` does NOT give a bounded `m*`; the budget crossing needs the
DEEP-rung (`r ≈ log n`) decay of `O_r` to `≤ d`, the still-open growth law
(`DistinctGammaUnionGrowthLaw`).  This is a SHALLOW-rung degree certificate, character-sum-free,
char-agnostic, p-independent.  Per the ASYMPTOTIC-CLAIM GUARD (#444), a fixed-`r` degree fact is
NOT a sub-linear law at the deep rung.  Does NOT touch CORE `M(μ_n) ≤ C·√(n·log(p/n))`.
-/

namespace ArkLib.ProximityGap.OrbitDegreeBelowFoldR5

open ArkLib.ProximityGap

/-- **Upper degree bound** `O₅(g) ≤ g³`: the `r = 5` orbit count is at most cubic in `g = n/4`, so
`deg(O₅) ≤ 3`.  Proof: `24·O₅ ≤ 24·g³` from the numerator `≤ 24g³` and `Nat.div_le_div_right`. -/
theorem orbit5_le_g_cubed (g : ℕ) :
    DeepBandR5.deepBandFullOrb g ≤ g ^ 3 := by
  rw [DeepBandR5.deepBandFullOrb]
  -- (4g³+3g²−10g)/24 ≤ g³  ⟸  4g³+3g²−10g ≤ 24 · g³
  apply Nat.div_le_of_le_mul
  -- goal: 4g³+3g²−10g ≤ 24 * g³.  Chain through the subtraction-free upper bound 4g³+3g².
  have hnum : 4 * g ^ 3 + 3 * g ^ 2 - 10 * g ≤ 4 * g ^ 3 + 3 * g ^ 2 := Nat.sub_le _ _
  have hub : 4 * g ^ 3 + 3 * g ^ 2 ≤ 24 * g ^ 3 := by
    rcases Nat.eq_zero_or_pos g with rfl | hg
    · decide
    · have h3 : 3 * g ^ 2 ≤ 20 * g ^ 3 := by
        have : 3 * g ^ 2 ≤ 20 * g * g ^ 2 := Nat.mul_le_mul_right _ (by omega)
        calc 3 * g ^ 2 ≤ 20 * g * g ^ 2 := this
          _ = 20 * g ^ 3 := by ring
      omega
  omega

/-- **Lower degree bound** `g³ ≤ 12·O₅(g)` for even `g ≥ 4`: the `r = 5` orbit count is at least a
cubic-degree fraction of `g³`, so `deg(O₅) ≥ 3`.  Combined with `orbit5_le_g_cubed`, `deg(O₅) = 3`.
Proof: the proven even-`g` numerator identity `24·O₅ + 10g = 4g³ + 3g²` gives
`12·O₅ ≥ 2g³ − 5g ≥ g³` for `g ≥ 4`. -/
theorem g_cubed_le_twelve_orbit5_even (h : ℕ) (hh : 2 ≤ h) :
    (2 * h) ^ 3 ≤ 12 * DeepBandR5.deepBandFullOrb (2 * h) := by
  -- in-tree even-g identity (subtraction-free reading after the nat-sub is discharged):
  have hb : 24 * DeepBandR5.deepBandFullOrb (2 * h)
      = 4 * (2 * h) ^ 3 + 3 * (2 * h) ^ 2 + 0 - 10 * (2 * h) :=
    OrbitCount5GeneralNormalForm.twentyfour_mul_fullOrb_even h
  -- numerator nonneg: 10(2h) ≤ 4(2h)³ + 3(2h)²
  have hle : 10 * (2 * h) ≤ 4 * (2 * h) ^ 3 + 3 * (2 * h) ^ 2 + 0 := by
    nlinarith [hh, Nat.one_le_iff_ne_zero.mpr (by positivity : h ^ 3 ≠ 0)]
  have hadd : 24 * DeepBandR5.deepBandFullOrb (2 * h) + 10 * (2 * h)
      = 4 * (2 * h) ^ 3 + 3 * (2 * h) ^ 2 := by omega
  -- 12·O₅ = (24·O₅)/2; from hadd, 24·O₅ = 4(2h)³+3(2h)²−10(2h) ⟹ 2·(12·O₅) = that, and
  -- (2h)³ ≤ 12·O₅ ⟺ 2(2h)³ ≤ 24·O₅ = 4(2h)³+3(2h)²−10(2h) ⟺ 2(2h)³+10(2h) ≤ 4(2h)³+3(2h)² (h≥2).
  have hkey : 2 * (2 * h) ^ 3 + 10 * (2 * h) ≤ 4 * (2 * h) ^ 3 + 3 * (2 * h) ^ 2 := by
    nlinarith [hh, sq_nonneg h, Nat.zero_le h]
  omega

/-- `deg(O₅) = 3 = r − 2`, strictly below the `r − 1 = 4` value of the `r = 3, 4` order-2 rungs:
the half-order `r = 5` rung carries an EXTRA degree of growing slack.  (Concrete `3 < 4`.) -/
theorem orbit5_degree_strictly_below_fold_minus_one : 3 < 5 - 1 := by decide

/-! ## Numeric anchor (matches the in-tree `rung_orbit_n16 … n128` table). -/

/-- At `n = 16` (`g = 4`): `O₅ = 11`, and the degree sandwich holds: `4³ = 64 ≤ 12·11 = 132` and
`11 ≤ 4³ = 64`. -/
theorem anchor_r5_orbit_n16 :
    DeepBandR5.deepBandFullOrb 4 = 11 ∧
    DeepBandR5.deepBandFullOrb 4 ≤ 4 ^ 3 ∧
    (4 : ℕ) ^ 3 ≤ 12 * DeepBandR5.deepBandFullOrb 4 := by
  refine ⟨by decide, by decide, by decide⟩

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only; no sorryAx)
#print axioms orbit5_le_g_cubed
#print axioms g_cubed_le_twelve_orbit5_even

end ArkLib.ProximityGap.OrbitDegreeBelowFoldR5
