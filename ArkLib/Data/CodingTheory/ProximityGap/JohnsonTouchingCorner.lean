/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26WitnessSpread
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The Johnson-touching corner (#357 round 2): δ* squeezed to within `2⁻³⁰` of Johnson at a
production-shape rate-1/4 instance

**The free-split observation.** The hypotheses of the proven [KKH26] ceiling
`kkh26_mcaDeltaStar_le` (`KKH26WitnessSpread.lean`) require only `1 ≤ m` — `m` need **not**
be odd. So the split parameters `(μ, m)` of the smooth domain `n = 2^μ·m` may be chosen with
`m` itself a 2-power. At

  `μ = 3, r = 4, m = 2²⁷`  ⟹  `n = 2³⁰`, degree `d = (r−2)·m = 2²⁸`,

the instance is *production-shaped*: a rate-`(2²⁸+1)/2³⁰ = 1/4 + 2⁻³⁰` smooth-domain
evaluation code on `n = 2³⁰` points, challenge error exactly `ε* = 2⁻¹²⁸`, over any prime
field with an order-`2³⁰` element and `p < 2¹³²` (the window `(2¹²⁸, 2¹³²)` contains the
production field sizes; any prime `p ≡ 1 mod 2³⁰` in it qualifies — `p` is kept abstract,
no concrete prime is certified here).

**What the ceiling gives at these parameters.** `1 − r/2^μ = 1 − 4/8 = 1/2`, and the
bad-scalar mass is `2⁴·C(4,4)/p = 16/p > 2⁻¹²⁸` exactly because `p < 2¹³² = 16·2¹²⁸`.
The prime threshold `(2³)^(2²) = 4096 < p` is automatic from the order-`2³⁰` element.
Hence **unconditionally**

  `δ*(C, 2⁻¹²⁸) ≤ 1/2`.

**Why this is a corner.** At rate `ρ = 1/4 + 2⁻³⁰` the Johnson radius satisfies

  `1 − √ρ < 1/2 < (1 − √ρ) + 2⁻³⁰`,

so the proven ceiling sits within `2⁻³⁰` *above* Johnson: the entire interior window
`(1 − √ρ, 1 − ρ − o(1))` is excluded at this instance except for a `2⁻³⁰`-sliver. In
particular the candidate interior law `δ* = 1 − ρ^{2/3}` (≈ 0.603 here) is excluded:
`δ* ≤ 1/2 < 1 − ρ^{2/3}`.

**Honesty.** This does NOT pin `δ*` (no matching lower bound at this instance is in-tree;
the Johnson floor remains gated on the named `CellPackageSupply` residual), and it does not
touch the production core at field sizes `q ≥ n²·2¹²⁸` (here `p < 2¹³² < 2⁶⁰·2¹²⁸ = n²·2¹²⁸`).
It is the second corner of the round-1 synthesis: wherever the current brackets decide, the
answer is Johnson-or-below — never an interior constant.

## Main results

* `corner_mcaDeltaStar_le_half` — the instantiated ceiling: `δ*(C, 2⁻¹²⁸) ≤ 1/2`.
* `johnson_sandwich_cornerRate` — `1 − √ρ < 1/2 < (1 − √ρ) + 2⁻³⁰` at `ρ = 1/4 + 2⁻³⁰`.
* `half_lt_one_sub_cornerRate_rpow` — `1/2 < 1 − ρ^{2/3}` (the interior candidate beaten).
* `johnsonTouchingCorner` — the package: `δ* ≤ (1 − √ρ) + 2⁻³⁰` and `δ* < 1 − ρ^{2/3}`.

## References

* [KKH26] D. Krachun, S. Kazanin, U. Haböck, *Failure of proximity gaps close to capacity*,
  ePrint 2026/782.
* [ABF26] G. Arnon, D. Boneh, G. Fenzi, *Open Problems in List Decoding and Correlated
  Agreement*, ePrint 2026/680.
-/

set_option autoImplicit false

open scoped NNReal ENNReal
open ProximityGap ProximityGap.MCAThresholdLedger

namespace ArkLib.ProximityGap.KKH26.JohnsonTouchingCorner

/-! ## The rate of the corner instance -/

/-- The rate of the corner instance: dimension `(r−2)·m + 1 = 2²⁸ + 1` over length
`n = 2³⁰` (the dimension convention of `kkh26_gap_identity`). -/
noncomputable def cornerRate : ℝ := (2 ^ 28 + 1) / 2 ^ 30

/-- `ρ = 1/4 + 2⁻³⁰`: the corner instance is a rate-1/4 code up to a `2⁻³⁰` excess. -/
theorem cornerRate_eq : cornerRate = 1 / 4 + 1 / 2 ^ 30 := by
  unfold cornerRate; norm_num

/-- The rate is the [KKH26] dimension-over-length of the instantiated code:
`((r−2)·m + 1)/n` at `r = 4`, `m = 2²⁷`, `n = 2³⁰`. -/
theorem cornerRate_eq_dim_div_length :
    cornerRate = (((4 - 2) * 2 ^ 27 + 1 : ℕ) : ℝ) / ((2 ^ 30 : ℕ) : ℝ) := by
  unfold cornerRate; norm_num

/-! ## Part (a): the instantiated ceiling `δ* ≤ 1/2` -/

/-- **The corner ceiling.** For any prime `p < 2¹³²` whose field carries an element of
multiplicative order `2³⁰` (e.g. any prime `p ≡ 1 mod 2³⁰` in `(2³⁰, 2¹³²)`), the
[KKH26] ceiling at the free-split parameters `μ = 3, r = 4, m = 2²⁷` gives, at the literal
challenge error `ε* = 2⁻¹²⁸`:

  `δ*(evalCode g 2³⁰ 2²⁸, 2⁻¹²⁸) ≤ 1/2`.

Pure instantiation of `kkh26_mcaDeltaStar_le`; the prime threshold `4096 < p` is derived
from the order-`2³⁰` element. -/
theorem corner_mcaDeltaStar_le_half {p n : ℕ} [Fact p.Prime] [NeZero n] {g : ZMod p}
    (hn : n = 2 ^ 30) (hg : orderOf g = 2 ^ 30) (hp : p < 2 ^ 132) :
    mcaDeltaStar (F := ZMod p) (evalCode g n (2 ^ 28)) (((2 : ℝ≥0∞) ^ 128)⁻¹)
      ≤ 1 / 2 := by
  have h2ne0 : ((2 : ℝ≥0∞) ^ 128) ≠ 0 := pow_ne_zero _ (by norm_num)
  have h2neT : ((2 : ℝ≥0∞) ^ 128) ≠ ⊤ := ENNReal.pow_ne_top (by norm_num)
  -- the prime threshold `(2^3)^(2^2) = 4096 < p` from the order-2³⁰ element
  have hcard : orderOf g ≤ Nat.card (ZMod p) := orderOf_le_card
  have hple : 2 ^ 30 ≤ p := by rwa [hg, Nat.card_zmod] at hcard
  have hp_low : ((2 : ℕ) ^ 3) ^ 2 ^ (3 - 1) < p :=
    lt_of_lt_of_le (by norm_num) hple
  -- the challenge error sits below the bad-scalar mass `16/p` since `p < 2¹³²`
  have hp0 : (p : ℝ≥0∞) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.Prime.pos (Fact.out (p := p.Prime))).ne'
  have hpT : (p : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top p
  have hplt : (p : ℝ≥0∞) < (2 : ℝ≥0∞) ^ 132 := by exact_mod_cast hp
  have hcount : ((2 ^ 4 * (2 ^ (3 - 1)).choose 4 : ℕ) : ℝ≥0∞) = 16 := by
    norm_num [Nat.choose_self]
  have hval : ((2 : ℝ≥0∞) ^ 128)⁻¹ * 2 ^ 132 = 16 := by
    rw [show ((2 : ℝ≥0∞) ^ 132) = 2 ^ 128 * 2 ^ 4 by rw [← pow_add],
      ← mul_assoc, ENNReal.inv_mul_cancel h2ne0 h2neT, one_mul]
    norm_num
  have hεstar : (((2 : ℝ≥0∞) ^ 128)⁻¹ : ℝ≥0∞)
      < ((2 ^ 4 * (2 ^ (3 - 1)).choose 4 : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) := by
    rw [hcount, ENNReal.lt_div_iff_mul_lt (Or.inl hp0) (Or.inl hpT)]
    calc ((2 : ℝ≥0∞) ^ 128)⁻¹ * (p : ℝ≥0∞)
        < ((2 : ℝ≥0∞) ^ 128)⁻¹ * 2 ^ 132 :=
          ENNReal.mul_lt_mul_right (ENNReal.inv_ne_zero.mpr h2neT)
            (ENNReal.inv_ne_top.mpr h2ne0) hplt
      _ = 16 := hval
  -- instantiate the proven ceiling at μ = 3, r = 4, m = 2²⁷
  have h := kkh26_mcaDeltaStar_le (p := p) (n := n) (μ := 3) (m := 2 ^ 27) (r := 4)
    (by norm_num) (g := g) (by norm_num) (by rw [hn]; norm_num) (by rw [hg]; norm_num)
    hp_low (by norm_num) (by norm_num) (((2 : ℝ≥0∞) ^ 128)⁻¹) hεstar
  have hd : (4 - 2) * 2 ^ 27 = (2 : ℕ) ^ 28 := by norm_num
  rw [hd] at h
  refine le_trans h ?_
  -- `1 − 4/2³ = 1/2` in `ℝ≥0` (truncated subtraction via coercion)
  rw [← NNReal.coe_le_coe, NNReal.coe_sub (by norm_num)]
  push_cast
  norm_num

/-! ## Part (b): the ceiling touches Johnson at this rate -/

/-- `1/2 < √ρ`: squaring, `1/4 < 1/4 + 2⁻³⁰`. -/
theorem half_lt_sqrt_cornerRate : (1 / 2 : ℝ) < Real.sqrt cornerRate := by
  rw [Real.lt_sqrt (by norm_num)]
  unfold cornerRate
  norm_num

/-- `√ρ < 1/2 + 2⁻³⁰`: squaring, `1/4 + 2⁻³⁰ < 1/4 + 2⁻³⁰ + 2⁻⁶⁰`. -/
theorem sqrt_cornerRate_lt : Real.sqrt cornerRate < 1 / 2 + 1 / 2 ^ 30 := by
  rw [Real.sqrt_lt' (by norm_num)]
  unfold cornerRate
  norm_num

/-- **The Johnson sandwich.** At rate `ρ = 1/4 + 2⁻³⁰`, the Johnson radius `1 − √ρ`
brackets the proven ceiling `1/2` from below to within `2⁻³⁰`:
`1 − √ρ < 1/2 < (1 − √ρ) + 2⁻³⁰`. -/
theorem johnson_sandwich_cornerRate :
    1 - Real.sqrt cornerRate < (1 / 2 : ℝ)
      ∧ (1 / 2 : ℝ) < (1 - Real.sqrt cornerRate) + 1 / 2 ^ 30 :=
  ⟨by linarith [half_lt_sqrt_cornerRate], by linarith [sqrt_cornerRate_lt]⟩

/-- `ρ^{2/3} < 1/2` at `ρ = 1/4 + 2⁻³⁰`: cubing both sides, `ρ² < 1/8`. -/
theorem cornerRate_rpow_two_thirds_lt_half : cornerRate ^ ((2 : ℝ) / 3) < 1 / 2 := by
  have h0 : (0 : ℝ) ≤ cornerRate := by unfold cornerRate; positivity
  have hcube : (cornerRate ^ ((2 : ℝ) / 3)) ^ (3 : ℕ) = cornerRate ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast (cornerRate ^ ((2 : ℝ) / 3)) 3, ← Real.rpow_mul h0,
      show ((2 : ℝ) / 3) * ((3 : ℕ) : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
  refine lt_of_pow_lt_pow_left₀ 3 (by norm_num) ?_
  rw [hcube]
  unfold cornerRate
  norm_num

/-- **The interior window is excluded.** `1/2 < 1 − ρ^{2/3}`: the candidate interior law
`δ* = 1 − ρ^{2/3}` (≈ 0.603 at this rate) lies strictly above the proven ceiling. -/
theorem half_lt_one_sub_cornerRate_rpow :
    (1 / 2 : ℝ) < 1 - cornerRate ^ ((2 : ℝ) / 3) := by
  linarith [cornerRate_rpow_two_thirds_lt_half]

/-! ## The package -/

/-- **The Johnson-touching corner (#357 round 2).** At the free-split parameters
`μ = 3, r = 4, m = 2²⁷` (rate `ρ = 1/4 + 2⁻³⁰`, `n = 2³⁰`, `ε* = 2⁻¹²⁸`, any prime
`p < 2¹³²` with an order-`2³⁰` element), the proven [KKH26] ceiling squeezes the MCA
threshold to within `2⁻³⁰` of the Johnson radius — **unconditionally**:

  `δ* ≤ (1 − √ρ) + 2⁻³⁰`   and   `δ* < 1 − ρ^{2/3}`.

The entire interior window above Johnson + `2⁻³⁰` is excluded at this production-shape
rate-1/4 instance; in particular the `1 − ρ^{2/3}` interior candidate is beaten. No
matching lower bound is claimed (the Johnson floor stays gated on `CellPackageSupply`). -/
theorem johnsonTouchingCorner {p n : ℕ} [Fact p.Prime] [NeZero n] {g : ZMod p}
    (hn : n = 2 ^ 30) (hg : orderOf g = 2 ^ 30) (hp : p < 2 ^ 132) :
    ((mcaDeltaStar (F := ZMod p) (evalCode g n (2 ^ 28)) (((2 : ℝ≥0∞) ^ 128)⁻¹) : ℝ≥0) : ℝ)
        ≤ (1 - Real.sqrt cornerRate) + 1 / 2 ^ 30
      ∧ ((mcaDeltaStar (F := ZMod p) (evalCode g n (2 ^ 28))
            (((2 : ℝ≥0∞) ^ 128)⁻¹) : ℝ≥0) : ℝ)
        < 1 - cornerRate ^ ((2 : ℝ) / 3) := by
  have h := corner_mcaDeltaStar_le_half hn hg hp
  have hc : ((mcaDeltaStar (F := ZMod p) (evalCode g n (2 ^ 28))
      (((2 : ℝ≥0∞) ^ 128)⁻¹) : ℝ≥0) : ℝ) ≤ 1 / 2 := by
    exact_mod_cast h
  exact ⟨le_trans hc (le_of_lt johnson_sandwich_cornerRate.2),
    lt_of_le_of_lt hc half_lt_one_sub_cornerRate_rpow⟩

end ArkLib.ProximityGap.KKH26.JohnsonTouchingCorner

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.KKH26.JohnsonTouchingCorner.corner_mcaDeltaStar_le_half
#print axioms ArkLib.ProximityGap.KKH26.JohnsonTouchingCorner.johnson_sandwich_cornerRate
#print axioms
  ArkLib.ProximityGap.KKH26.JohnsonTouchingCorner.half_lt_one_sub_cornerRate_rpow
#print axioms ArkLib.ProximityGap.KKH26.JohnsonTouchingCorner.johnsonTouchingCorner
