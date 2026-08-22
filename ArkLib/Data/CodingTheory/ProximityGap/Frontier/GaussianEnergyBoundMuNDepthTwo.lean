/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import ArkLib.Data.CodingTheory.ProximityGap.GaussPeriodMomentBound
import ArkLib.Data.CodingTheory.ProximityGap.REnergyTwoExact

/-!
# The `r = 2` rung of the open energy ladder is UNCONDITIONAL for `μ_n` — and THINNESS-ESSENTIAL (#444)

The prize per-frequency bound is carried (via the in-tree `GaussPeriodMomentBound` consumer chain)
by the single named family `GaussianEnergyBound G r : E_r(G) ≤ (2r−1)‼·|G|^r` at depth `r ≈ ln q`.
The energy-ladder reduction (`Frontier/_EnergyRatioMonotoneReduction.lean`,
`gaussianEnergyBound_of_ERM`) steps the bound up one order at a time from a base rung, and its
module doc asserts in prose that the low rungs hold — *"the base case `r = 1` is still PROVEN
(`E_2 = 3n²−3n ≤ 3n·n`), and `r = 2` holds (slack `1−1/n`)"* — but it never lands
`GaussianEnergyBound (μ_n) 2` as a theorem from the in-tree exact closed form, nor records that this
low rung is **thinness-essential** (it is FALSE for thick / high-additive-energy domains).

This file discharges that prose. Two bricks:

* **`gaussianEnergyBound_muN_two`** (HEADLINE) — `GaussianEnergyBound (μ_n) 2`, i.e.
  `E_2(μ_n) ≤ 3·|μ_n|²`, UNCONDITIONALLY for the thin 2-power subgroup `μ_n ⊂ F_p`
  (`n = 2^m`, `m ≥ 1`, `p > 2^n`). Derived from the in-tree exact value
  `REnergyTwoExact.mu_n_rEnergy_two_eq` (`E_2 = 3n²−3n`) and `mu_n_card_eq` (`|μ_n| = n`):
  the bound is `3n²−3n ≤ 3·n²` ⟺ `0 ≤ 3n`. The `(2·2−1)‼ = 3‼ = 3` coefficient matches exactly,
  with slack `3n` (the `1−1/n` relative slack the ladder doc names). This is the first non-trivial
  verified order of the `GaussianEnergyBound` ladder (`r = 1` is the trivial Parseval base
  `E_1 = |G|`), the concrete rung that `gaussianEnergyBound_of_ERM` consumes off the base.

* **`gaussianEnergyBound_two_thinness_essential`** (the rule-3 CONSTRAINT LEMMA) — the same
  `r = 2` bound `E_2 ≤ 3|G|²` is **NOT a general / thickness-monotone fact**: for a domain `G` whose
  depth-2 additive energy exceeds `3|G|²` it FAILS. We record the contrapositive as a clean Lean
  statement (`3·|G|² < E_2(G) → ¬ GaussianEnergyBound G 2`), making explicit that the `μ_n` rung
  above is a thinness-essential lever, NOT a free monotone inequality. Probe
  `scripts/probes/probe_erm_r1_sharp.py` exhibits the failure concretely: random negation-closed
  sets in `ℤ_p` fail it (4/12), and arithmetic progressions fail it badly (`E_2 ≈ 489` vs `3|G|² =
  243` at `|G| = 9`), while `μ_n` satisfies it with exact slack `3n` at every `n` tested
  (`n = 4,…,64`). So the bound is true on the thin subgroup precisely *because* `μ_n` is
  Sidon-mod-negation at depth 2 (its only depth-2 additive relations are the trivial
  `z + (−z) = 0`), and false off it. This is the brief's rule-3 thinness-essentiality made into a
  theorem at the `r = 2` rung.

## Honest scope (rules 1, 3, 6)

This is a single-rung discharge, NOT a CORE closure. The prize CORE `M(μ_n) ≤ C·√(n·log(p/n))`
lives at the DEEP order `r ≈ ln q` (the full DC-Wick ladder, the BGK / Paley √-cancellation wall),
which `gaussianEnergyBound_of_ERM` cannot reach because the global energy-ratio step `ERM` is REFUTED
past `r ≈ n/4` (`Frontier/_EnergyRatioMonotoneReduction.lean`). This file does **not** touch that
wall. It lands the `r = 2` rung as an honest theorem (replacing the ladder doc's prose claim by a
proof from the in-tree exact closed form), and records — via the constraint lemma — that the rung is
thinness-essential, hence a valid rule-3 lever rather than a thickness-monotone one. No moment /
census / orbit re-derivation, no capacity / beyond-Johnson / growth-law claim, cliff-at-`n/2`
untouched. EXTEND-proven on `REnergyTwoExact.mu_n_rEnergy_two_eq` + `GaussianEnergyBound`.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`. Issue #444 / #389.
-/

set_option autoImplicit false
set_option linter.style.longLine false


open ArkLib.ProximityGap.GaussPeriodMomentBound
open ArkLib.ProximityGap.REnergyTwoExact
open ArkLib.ProximityGap.EnergyEqualitySidonModNeg
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

namespace ArkLib.ProximityGap.Frontier.GaussianEnergyBoundMuNDepthTwo

variable {p : ℕ} [Fact p.Prime] {n m : ℕ}

/-- **The `r = 2` Gaussian energy rung is UNCONDITIONAL for `μ_n`.**
`GaussianEnergyBound (μ_n) 2`, i.e. `E_2(μ_n) ≤ (2·2−1)‼·|μ_n|² = 3·n²`, for the thin 2-power
subgroup `μ_n ⊂ F_p` (`n = 2^m`, `m ≥ 1`, `p > 2^n`). The exact value `E_2(μ_n) = 3n²−3n`
(`mu_n_rEnergy_two_eq`) sits below `3n²` with slack exactly `3n`. The character `ψ` is a proof
device (one exists on every `ZMod p`); the conclusion does not depend on it. -/
theorem gaussianEnergyBound_muN_two (hn2 : n = 2 ^ m) (hm : 1 ≤ m) (hp : 2 ^ n < p)
    {ω : ZMod p} (hω : IsPrimitiveRoot ω n)
    {ψ : AddChar (ZMod p) ℂ} (hψ : ψ.IsPrimitive) :
    GaussianEnergyBound (muN p n) 2 := by
  -- Unfold the bound: E_2 ≤ doubleFactorial(3) · |μ_n|².
  change (rEnergy (muN p n) 2 : ℝ)
      ≤ (Nat.doubleFactorial (2 * 2 - 1) : ℝ) * ((muN p n).card : ℝ) ^ 2
  -- The two in-tree exact facts.
  have hE2 : rEnergy (muN p n) 2 = 3 * n ^ 2 - 3 * n := mu_n_rEnergy_two_eq hn2 hm hp hω hψ
  have hcard : (muN p n).card = n := mu_n_card_eq hω
  -- doubleFactorial (2*2-1) = doubleFactorial 3 = 3.
  have hdf : (Nat.doubleFactorial (2 * 2 - 1) : ℝ) = 3 := by norm_num [Nat.doubleFactorial]
  rw [hcard, hdf]
  -- Cast the ℕ-subtraction value 3n²−3n to ℝ (it is ≤ 3n² so the truncation is benign here, but we
  -- carry it through cast lemmas so the ℕ `-` is interpreted correctly).
  have hnle : n ≤ n ^ 2 := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · simp [hn]
    · calc n = n ^ 1 := (pow_one n).symm
        _ ≤ n ^ 2 := Nat.pow_le_pow_right hn (by norm_num)
  have hge : 3 * n ≤ 3 * n ^ 2 := Nat.mul_le_mul_left 3 hnle
  have hE2cast : (rEnergy (muN p n) 2 : ℝ) = 3 * (n : ℝ) ^ 2 - 3 * (n : ℝ) := by
    rw [hE2, Nat.cast_sub hge]
    push_cast
    ring
  rw [hE2cast]
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  nlinarith [hn0]

set_option linter.unusedFintypeInType false in
/-- **CONSTRAINT LEMMA (rule 3): the `r = 2` Gaussian rung is THINNESS-ESSENTIAL.**
For ANY finite domain `G` over a field whose depth-2 additive energy strictly exceeds `3·|G|²`,
the `r = 2` Gaussian energy bound FAILS. Contrapositive of unfolding `GaussianEnergyBound G 2`
(`E_2(G) ≤ 3·|G|²`). Together with `gaussianEnergyBound_muN_two` this pins that the `μ_n` rung is a
genuine thin-subgroup lever and NOT a thickness-monotone inequality: probe
`probe_erm_r1_sharp.py` exhibits explicit `G` (random negation-closed sets, and especially
arithmetic progressions, e.g. `E_2 = 489 > 243 = 3·|G|²` at `|G| = 9`) where the hypothesis holds, so
the conclusion `¬ GaussianEnergyBound G 2` applies — the bound is FALSE off the thin regime. -/
theorem gaussianEnergyBound_two_thinness_essential {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (G : Finset F) (hbig : 3 * (G.card : ℝ) ^ 2 < (rEnergy G 2 : ℝ)) :
    ¬ GaussianEnergyBound G 2 := by
  intro h
  -- GaussianEnergyBound G 2 unfolds to E_2 ≤ doubleFactorial 3 · |G|² = 3·|G|².
  have hb : (rEnergy G 2 : ℝ) ≤ (Nat.doubleFactorial (2 * 2 - 1) : ℝ) * (G.card : ℝ) ^ 2 := h
  have hdf : (Nat.doubleFactorial (2 * 2 - 1) : ℝ) = 3 := by norm_num [Nat.doubleFactorial]
  rw [hdf] at hb
  linarith

/-- **The UNCONDITIONAL `r = 2` per-frequency 4th-power bound for `μ_n`.** Chaining the in-tree
consumer `eta_pow_le_of_energyBound` (which turns any `GaussianEnergyBound G r` into a single-term
`2r`-th moment bound) through the unconditional `gaussianEnergyBound_muN_two`: every Gauss period of
the thin subgroup `μ_n` satisfies `‖η_b‖⁴ ≤ q·3·n²` for EVERY nonzero frequency `b`
(`q = |F| = card (ZMod p)`, `n = |μ_n|`). Equivalently `‖η_b‖ ≤ (3q)^{1/4}·√n`: the unconditional
`r = 2` completion ceiling on the per-frequency Gauss sum, with NO char-`p` energy hypothesis (the
`E_2` value is exact in tree). This is the `r = 2` instance of the moment-method incomplete-sum
bound; the prize wants the DEEP-`r` optimized version `≈ √(2 n ln q)`, NOT reachable at `r = 2`. -/
theorem eta_quartic_le_muN_two (hn2 : n = 2 ^ m) (hm : 1 ≤ m) (hp : 2 ^ n < p)
    {ω : ZMod p} (hω : IsPrimitiveRoot ω n)
    {ψ : AddChar (ZMod p) ℂ} (hψ : ψ.IsPrimitive) (b : ZMod p) :
    ‖eta ψ (muN p n) b‖ ^ 4
      ≤ (Fintype.card (ZMod p) : ℝ) * 3 * ((muN p n).card : ℝ) ^ 2 := by
  have hbound := eta_pow_le_of_energyBound hψ (gaussianEnergyBound_muN_two hn2 hm hp hω hψ) b
  -- eta_pow_le_of_energyBound gives ‖η‖^(2*2) ≤ q · doubleFactorial(3) · |μ_n|²
  have hdf : (Nat.doubleFactorial (2 * 2 - 1) : ℝ) = 3 := by norm_num [Nat.doubleFactorial]
  rw [hdf] at hbound
  -- 2*2 = 4 and reassociate q · 3 · |μ_n|²
  have h24 : (2 * 2 : ℕ) = 4 := by norm_num
  rw [h24] at hbound
  linarith [hbound]

end ArkLib.ProximityGap.Frontier.GaussianEnergyBoundMuNDepthTwo

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.GaussianEnergyBoundMuNDepthTwo.gaussianEnergyBound_muN_two
#print axioms ArkLib.ProximityGap.Frontier.GaussianEnergyBoundMuNDepthTwo.gaussianEnergyBound_two_thinness_essential
#print axioms ArkLib.ProximityGap.Frontier.GaussianEnergyBoundMuNDepthTwo.eta_quartic_le_muN_two
