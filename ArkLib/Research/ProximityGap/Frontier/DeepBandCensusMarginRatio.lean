/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DeepBandR3Bound
import ArkLib.Data.CodingTheory.ProximityGap.DeepBandR4Bound

/-!
# The deep-band census MARGIN RATIO at the order-2 rungs `r = 3, 4` (#444)

`DeepBandR3Bound` / `DeepBandR4Bound` proved (axiom-clean) the deep-band `#bad`-scalar closed
forms and the qualitative domination `deepBandBadCount ≤ deepBandBudget`
(`deepBandBadCount_le_budget`, `deepBandBadCount4_le_budget`).  Those are PASS/FAIL margin
statements (count ≤ budget).  This file QUANTIFIES the margin by an EXACT division-free integer
identity, and reads off the asymptotic count/budget ratio.

With `g = n/4`:

* **`r = 3`** (`16·bad₃ = 3·budget₃ + 16(g²−g+1)`): the bad-count is a `3/16`-fraction of the
  budget in the limit (`budget₃ = 2³·C(2g,3) ∼ (32/3)g³`, `bad₃ ∼ 2g³`, ratio `∼ 2/(32/3) = 3/16`),
  approached strictly from ABOVE by a degree-2 correction.

* **`r = 4`** (`32·bad₄ = 3·budget₄ + (32g³−88g²+152g+32)`): the bad-count is a `3/32`-fraction of
  the budget in the limit (`budget₄ = 2⁴·C(2g,4) ∼ (32/3)g⁴`, `bad₄ ∼ g⁴`, ratio `∼ 1/(32/3) = 3/32`).

The two limiting fractions `3/16` and `3/32` are related by EXACTLY a factor of two
(`r4_limit = r3_limit / 2`): the budget leading coefficient is the SAME `32/3` at both rungs (the
maximum of `4^r/r!`, attained at `r = 3, 4`), so the ratio halves precisely because the bad-count
leading coefficient halves (`2` at `r = 3` → `1` at `r = 4`).  This is the order-2-rung companion of
the `r = 5` degree-DROP (`OrbitCount5GeneralNormalForm`: at `r = 5` the bad-count drops to degree 4
while the budget is degree 5, so the ratio → 0).

## Mechanism (pure-ℕ, NOT a moment / energy method)

Everything is an exact integer-polynomial identity in `g`, discharged by the in-tree
choose-expansion lemmas (`DeepBandR3.six_mul_choose_three`, `DeepBandR4.choose_four_expand`) plus
`nlinarith`/`omega`.  No spectral object, no character sum — this is the combinatorial census face.

## Honest scope

This is a QUANTITATIVE refinement of the already-proven shallow-rung domination, extending the
proven closed forms with the exact asymptotic margin ratio.  It is a statement about the FIXED
order-2 rungs `r = 3, 4` only.

It says NOTHING about the prize wall.  The prize binds the DEEP rung `r ≈ log n`
(`= |Σ_r(μ_s)|` = BCHKS 1.12 = the BGK wall), where the count/budget behaviour is NOT governed by
these fixed-rung leading terms.  Per the ASYMPTOTIC-CLAIM GUARD (#444), a bounded margin at the
shallow rungs is NOT a sub-budget claim at the deep rung; the over-determined/combinatorial face is
known to collapse to Johnson (cliff-at-n/2), and `Char0CountExplodes` already exhibits the char-0
incidence EXPLODING super-budget two rungs past Johnson.  This file makes NO capacity /
beyond-Johnson / decay-law claim.  CORE `M(μ_n) ≤ C·√(n·log(p/n))` with absolute `C` remains OPEN.
-/

namespace ArkLib.ProximityGap.DeepBandCensusMargin

open ArkLib.ProximityGap

/-! ## `r = 3`: exact margin identity and the `3/16` ratio. -/

/-- **The `r = 3` census margin identity.** For `g ≥ 1` (so the closed-form nat-subtraction
`g - 1` is honest), `16·deepBandBadCount = 3·deepBandBudget + 16(g² − g + 1)`.  The correction term
`16(g² − g + 1)` is degree 2, strictly below the degree-3 leading terms, so the ratio
`bad₃/budget₃ → 3/16` from above. -/
theorem r3_margin_identity (g : ℕ) (hg : 1 ≤ g) :
    16 * DeepBandR3.deepBandBadCount g
      = 3 * DeepBandR3.deepBandBudget g + 16 * (g ^ 2 - g + 1) := by
  obtain ⟨e, rfl⟩ : ∃ e, g = e + 1 := ⟨g - 1, by omega⟩
  have hc : 6 * (2 * (e + 1)).choose 3 = (2 * (e + 1)) * (2 * (e + 1) - 1) * (2 * (e + 1) - 2) :=
    DeepBandR3.six_mul_choose_three (e + 1) (by omega)
  have e1 : 2 * (e + 1) - 1 = 2 * e + 1 := by omega
  have e2 : 2 * (e + 1) - 2 = 2 * e := by omega
  have e3 : (e + 1) - 1 = e := by omega
  rw [e1, e2] at hc
  rw [DeepBandR3.deepBandBudget, DeepBandR3.deepBandBadCount, e3]
  set Ch := (2 * (e + 1)).choose 3 with hChdef
  -- 3 * (2^3 * Ch) = 8 * (6 * Ch) ... rewrite via 6*Ch = product
  have hRHS : 3 * (2 ^ 3 * Ch) = 4 * (6 * Ch) := by ring
  rw [hRHS, hc]
  -- now both sides are polynomials in e; clear the degree-2 nat-sub `(e+1)^2 - (e+1) + 1`
  have hsub : (e + 1) ^ 2 - (e + 1) + 1 = e ^ 2 + e + 1 := by
    have : (e + 1) ^ 2 = e ^ 2 + 2 * e + 1 := by ring
    omega
  rw [hsub]
  ring

/-- The `r = 3` census margin is STRICTLY positive and bounded: `3·budget₃ < 16·bad₃` for `g ≥ 1`
(equivalently `bad₃/budget₃ > 3/16`). -/
theorem r3_three_budget_lt_sixteen_badCount (g : ℕ) (hg : 1 ≤ g) :
    3 * DeepBandR3.deepBandBudget g < 16 * DeepBandR3.deepBandBadCount g := by
  have h := r3_margin_identity g hg
  have hpos : 0 < 16 * (g ^ 2 - g + 1) := by positivity
  omega

/-! ## `r = 4`: exact margin identity and the `3/32` ratio. -/

/-- **The `r = 4` census margin identity.** For `g ≥ 2` (so the closed-form nat-subtraction is
honest), `32·deepBandBadCount4 + 88g² = 3·deepBandBudget4 + (32g³ + 152g + 32)`, i.e.
`32·bad₄ − 3·budget₄ = 32g³ − 88g² + 152g + 32` (degree 3, strictly below the degree-4 leading
terms), so the ratio `bad₄/budget₄ → 3/32` from above.  Stated subtraction-free to stay in ℕ. -/
theorem r4_margin_identity (g : ℕ) (hg : 2 ≤ g) :
    32 * DeepBandR4.deepBandBadCount4 g + 88 * g ^ 2
      = 3 * DeepBandR4.deepBandBudget4 g + (32 * g ^ 3 + 152 * g + 32) := by
  -- in-tree: 24 * C(2g,4) + (48 g^3 + 12 g) = 16 g^4 + 44 g^2   (subtraction-free reading)
  have hpoly : 24 * (2 * g).choose 4 + (48 * g ^ 3 + 12 * g) = 16 * g ^ 4 + 44 * g ^ 2 :=
    DeepBandR4.twentyfour_choose_poly g hg
  -- in-tree additive closed form: bad4 + 2g^3 = g^4 + 4g + 1 (eliminates the nat-subtraction)
  have hadd : DeepBandR4.deepBandBadCount4 g + 2 * g ^ 3 = g ^ 4 + 4 * g + 1 :=
    DeepBandR4.deepBandBadCount4_add g hg
  rw [DeepBandR4.deepBandBudget4]
  set C := (2 * g).choose 4 with hCdef
  set B := DeepBandR4.deepBandBadCount4 g with hBdef
  -- Linear elimination over the two proven facts (omega handles ℕ, no subtraction):
  have h48 : 48 * C + (96 * g ^ 3 + 24 * g) = 32 * g ^ 4 + 88 * g ^ 2 := by omega
  have h32 : 32 * B + 64 * g ^ 3 = 32 * g ^ 4 + 128 * g + 32 := by omega
  -- goal: 32B + 88g² = 48C + (32g³ + 152g + 32); both sides = 32g⁴ − 64g³ + 88g² + 128g + 64
  omega

/-- The `r = 4` census margin is STRICTLY positive: `3·budget₄ < 32·bad₄` for `g ≥ 2`
(equivalently `bad₄/budget₄ > 3/32`). -/
theorem r4_three_budget_lt_thirtytwo_badCount (g : ℕ) (hg : 2 ≤ g) :
    3 * DeepBandR4.deepBandBudget4 g < 32 * DeepBandR4.deepBandBadCount4 g := by
  have h := r4_margin_identity g hg
  -- 32*bad4 + 88g^2 = 3*bud4 + (32g^3 + 152g + 32);  need 3*bud4 < 32*bad4,
  -- i.e. 32g^3 + 152g + 32  >  88g^2 for g ≥ 2.
  have hg3 : 88 * g ^ 2 < 32 * g ^ 3 + 152 * g + 32 := by
    rcases Nat.lt_or_ge g 3 with hlt | hge
    · interval_cases g
      decide
    · -- g ≥ 3 ⇒ 32g³ = 32g·g² ≥ 96g² > 88g²
      have hge' : 96 * g ^ 2 ≤ 32 * g ^ 3 := by
        have : 96 * g ^ 2 ≤ 32 * g * g ^ 2 := Nat.mul_le_mul_right _ (by omega)
        calc 96 * g ^ 2 ≤ 32 * g * g ^ 2 := this
          _ = 32 * g ^ 3 := by ring
      nlinarith [hge']
  omega

/-! ## The cross-rung halving of the limiting ratio.

The limiting fractions are `3/16` (`r = 3`) and `3/32` (`r = 4`).  We record the exact factor-of-two
relation in cleared-denominator integer form: the `r = 4` limit `3/32` is half the `r = 3` limit
`3/16`.  (The mechanism: the budget leading coefficient `4^r/r!` is EQUAL at `r = 3, 4` (both `32/3`,
the maximum of `4^r/r!`), so the ratio halves exactly because the bad-count leading coefficient
halves, `2 → 1`.) -/
theorem limit_ratio_halves : (3 : ℚ) / 32 = (3 / 16) / 2 := by norm_num

/-- The budget leading coefficient `4^r / r!` is EQUAL at `r = 3` and `r = 4` (both `32/3`): this is
why the two rung ratios share a common budget scale and differ only through the bad-count leading
coefficient.  (`4³/3! = 64/6 = 32/3` and `4⁴/4! = 256/24 = 32/3`.) -/
theorem budget_leadCoeff_r3_eq_r4 :
    (4 ^ 3 : ℚ) / Nat.factorial 3 = (4 ^ 4 : ℚ) / Nat.factorial 4 := by
  norm_num [Nat.factorial]

/-- The budget leading coefficient `4^r/r!` is maximized at `r = 3, 4`: it strictly DECREASES at
`r = 5` (`4⁵/5! = 128/15 < 32/3`).  Past `r = 4` the budget scale falls, while the bad-count drops a
full degree at `r = 5`, together driving the `r = 5` ratio to `0` (`OrbitCount5GeneralNormalForm`). -/
theorem budget_leadCoeff_r5_lt_r4 :
    (4 ^ 5 : ℚ) / Nat.factorial 5 < (4 ^ 4 : ℚ) / Nat.factorial 4 := by
  norm_num [Nat.factorial]

/-! ## Numeric anchors (sanity, matching the in-tree rung tables). -/

theorem anchor_r3_n16 : DeepBandR3.deepBandBadCount 4 = 97 ∧ DeepBandR3.deepBandBudget 4 = 448 :=
  ⟨by decide, by decide⟩

theorem anchor_r4_n16 :
    DeepBandR4.deepBandBadCount4 4 = 145 ∧ DeepBandR4.deepBandBudget4 4 = 1120 :=
  ⟨by decide, by decide⟩

/-- The `r = 3` margin identity, checked at the `n = 16` anchor (`g = 4`):
`16·97 = 3·448 + 16·(16−4+1) = 1344 + 208 = 1552`. -/
theorem anchor_r3_margin_n16 :
    16 * DeepBandR3.deepBandBadCount 4
      = 3 * DeepBandR3.deepBandBudget 4 + 16 * (4 ^ 2 - 4 + 1) := by
  decide

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only; no sorryAx)
#print axioms r3_margin_identity
#print axioms r4_margin_identity
#print axioms r3_three_budget_lt_sixteen_badCount
#print axioms r4_three_budget_lt_thirtytwo_badCount

end ArkLib.ProximityGap.DeepBandCensusMargin
