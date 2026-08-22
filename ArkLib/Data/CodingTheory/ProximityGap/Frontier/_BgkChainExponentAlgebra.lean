/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# BGK chain made EXPLICIT: the exact exponent identity and the `o(1)` location (#444)

Attack `[bgk-chain-explicit]`: make the Bourgain–Glibichuk–Konyagin / di Benedetto
sum-product → character-sum chain explicit at `β = 4`, identify the exact step where the
`o(1)` enters, and pin precisely how far the exponent can be pushed toward the prize `1/2`.

## The proven in-tree chain (recap, NOT re-proved here)

`BGKEnergyCharacterSum.bgk_character_sum_bound` proves, axiom-clean:

> `‖η_b‖ ≤ n^{(θ + D)/(2r)}`     whenever `E_r(μ_n) ≤ n^θ` and `q ≤ n^D`,

with `η_b = Σ_{x∈μ_n} ψ(b·x)`, `n = |μ_n|`, `q = |F_p|`, `D = β` (the field-size exponent,
`= 4` at the prize). The single open input is the energy exponent `θ`: the sum-product output
`E_r(μ_n) ≤ n^{2r-1-κ_r}` with cancellation GAIN `κ_r ≥ 0` over the trivial Sidon ceiling
`E_r ≤ n^{2r-1}` (`MaximalEnergyUniformBound.rEnergy_le_card_pow`, also proven in-tree).

## What THIS file adds: the exact exponent algebra (the explicit BGK chain)

The whole point of "making BGK explicit" is to write the realised exponent as a transparent
function of the sum-product gain `κ_r` and the field exponent `β`, and read off exactly where
`o(1)` lives and what `κ_r` must do.

Substituting `θ = 2r - 1 - κ_r`, `D = β` into the in-tree exponent `(θ + D)/(2r)`:

> **`bgkExponent_eq`** —  `(θ + β)/(2r) = 1 + (β - 1 - κ_r)/(2r)`   (with `θ = 2r-1-κ_r`).

This is the **explicit BGK exponent identity**. Three consequences, each an exact statement:

* **`bgkExponent_lt_one_iff`** — the chain beats the trivial `‖η_b‖ ≤ n` exponent
  (`α(r) < 1`) **iff** `κ_r > β - 1`.  *This is exactly where `o(1)` enters*: BGK / di Benedetto
  supply only `κ_r` marginally above (or, at the prize point `β = 4`, NOT above) `β - 1 = 3`, so
  `α(r) → 1⁻` (or `α(r) ≥ 1`) — the `o(1)` IS the slack `κ_r - (β-1)` divided by `2r`.

* **`bgkExponent_eq_half_iff`** — within the pure-`n`-power chain, the prize exponent
  `α(r) = 1/2` holds **iff** `κ_r = r + β - 1`, i.e. **iff** `θ = r - β` (a per-band energy
  bound *below* the Wick-leading order `nʳ`). This makes the gap quantitative: the prize wants the
  energy to drop a full extra factor `n^{r-1}` below the maximal-energy ceiling AND `n^β` below
  Wick-leading.

* **`bgkExponent_ge_one_of_smallGain`** — at the prize point, if `κ_r ≤ β - 1` (the honest state:
  di Benedetto's power-saving vanishes exactly at `β = 4`), then `α(r) ≥ 1`: the pure-`n`-power
  chain gives NOTHING below trivial. Proven.

## Why the pure-`n`-power chain cannot reach the prize, and what replaces it

The Wick / Gaussian energy bound is `E_r ≤ (2r-1)‼·nʳ`, i.e. `θ = r + log_n((2r-1)‼)` — NOT a
pure `n`-power (the `(2r-1)‼` is a `polylog(q)` factor at the saddle `r ≈ ln q`). The pure-`n`-power
identity above *forces* the prize to demand `θ = r - β < r`, which is BELOW the Wick value `≈ r`:
the pure-`n`-power chain literally cannot see the `√(log q)` polylog that turns Wick into the prize.

* **`wickExponent_vs_prizeNPower`** — the Wick exponent `θ_Wick(r) = r + s` (`s = log_n((2r-1)‼) ≥ 0`)
  is STRICTLY ABOVE the n-power prize requirement `θ_prize(r) = r - β` by `β + s`. So feeding the
  TRUE Wick energy into the pure-`n`-power chain gives `α > 1/2`; the correct route is the saddle
  `rpow` optimization (`_AvPrize_MomentToSupCapstone`), which keeps the polylog and reaches
  `√(2e·n·log q)`. This file makes that separation EXACT.

## Honesty

Everything here is unconditional REAL-ANALYSIS algebra on the exponent, proven axiom-clean. It does
NOT supply `κ_r` (that is the open sum-product/Paley input). It makes the BGK chain explicit and
pins the `o(1)` to the single scalar `κ_r - (β-1)`. The exponent the explicit chain *rigorously*
reaches at `β = 4` with the best PROVEN gain is `α = 1` (κ_r ≤ β-1 at the prize point) — i.e. the
trivial `‖η_b‖ ≤ n`; any `α < 1` requires `κ_r > 3`, which is open. Issue #444.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ProximityGap.Frontier.BGKExplicit

open Real

/-! ## 1. The explicit BGK exponent identity. -/

/-- **The realised BGK exponent** as a function of the moment depth `r`, the sum-product gain
`κ` (energy `E_r ≤ n^{2r-1-κ}`), and the field-size exponent `β` (`q ≤ n^β`). This is exactly the
exponent appearing in the in-tree `bgk_character_sum_bound` conclusion `‖η_b‖ ≤ n^{(θ+β)/(2r)}`
with `θ = 2r - 1 - κ`. -/
noncomputable def bgkExponent (r β κ : ℝ) : ℝ := ((2 * r - 1 - κ) + β) / (2 * r)

/-- **The explicit BGK exponent identity.** With energy exponent `θ = 2r - 1 - κ` and field
exponent `β`, the realised character-sum exponent is
`(θ + β)/(2r) = 1 + (β - 1 - κ)/(2r)`. Pure algebra; `r ≠ 0`. This is the heart of the explicit
chain: the deviation from the trivial exponent `1` is exactly `(β - 1 - κ)/(2r)`. -/
theorem bgkExponent_eq {r β κ : ℝ} (hr : r ≠ 0) :
    bgkExponent r β κ = 1 + (β - 1 - κ) / (2 * r) := by
  unfold bgkExponent
  have h2r : (2 : ℝ) * r ≠ 0 := by simp [hr]
  field_simp
  ring

/-! ## 2. Where the `o(1)` enters: the sub-trivial threshold `κ > β - 1`. -/

/-- **The sub-trivial threshold.** The explicit BGK exponent is `< 1` (the character sum beats the
trivial `‖η_b‖ ≤ n`) **iff** the sum-product gain exceeds `β - 1`: `α(r) < 1 ⟺ κ > β - 1`. At the
prize `β = 4` this is `κ > 3`. The `o(1)` of "BGK gives `n^{1-o(1)}`" is *exactly* the quantity
`(κ - (β-1))/(2r) ≥ 0` — it is positive but tends to `0` because the proven gain `κ` only marginally
exceeds `β - 1` (and at the exact prize point does not exceed it at all). -/
theorem bgkExponent_lt_one_iff {r β κ : ℝ} (hr : 0 < r) :
    bgkExponent r β κ < 1 ↔ β - 1 < κ := by
  rw [bgkExponent_eq hr.ne']
  have h2r : (0 : ℝ) < 2 * r := by linarith
  constructor
  · intro h
    have : (β - 1 - κ) / (2 * r) < 0 := by linarith
    have := (div_neg_iff.mp this)
    rcases this with ⟨h1, _⟩ | ⟨h1, h2⟩
    · linarith
    · linarith
  · intro h
    have hnum : β - 1 - κ < 0 := by linarith
    have : (β - 1 - κ) / (2 * r) < 0 := div_neg_of_neg_of_pos hnum h2r
    linarith

/-- **At the prize point, a sub-threshold gain gives nothing below trivial.** If `κ ≤ β - 1`
(the honest state at `β = 4`: di Benedetto's power saving vanishes, so no proven `κ > 3` exists),
then `α(r) ≥ 1`: the pure-`n`-power BGK chain delivers `‖η_b‖ ≤ n^{α(r)}` with `α(r) ≥ 1`, i.e. no
improvement over the trivial `‖η_b‖ ≤ n`. This is the rigorous statement of the `β = 4` wall for the
explicit chain. -/
theorem bgkExponent_ge_one_of_smallGain {r β κ : ℝ} (hr : 0 < r) (h : κ ≤ β - 1) :
    1 ≤ bgkExponent r β κ := by
  rw [bgkExponent_eq hr.ne']
  have h2r : (0 : ℝ) < 2 * r := by linarith
  have hnum : (0 : ℝ) ≤ β - 1 - κ := by linarith
  have : (0 : ℝ) ≤ (β - 1 - κ) / (2 * r) := div_nonneg hnum h2r.le
  linarith

/-! ## 3. The prize exponent `1/2` within the pure-`n`-power chain. -/

/-- **The prize requirement within the pure-`n`-power chain.** The explicit BGK exponent equals the
prize value `1/2` **iff** `κ = r + β - 1`, equivalently `θ = 2r - 1 - κ = r - β`. So to reach the
prize via this chain the per-band energy must satisfy `E_r ≤ n^{r-β}` — a full factor `n^{r-1}` below
the maximal-energy ceiling `n^{2r-1}` AND `n^β` below the Wick-leading order `nʳ`. This makes the gap
exact and shows it grows linearly in the gain `κ` required. -/
theorem bgkExponent_eq_half_iff {r β κ : ℝ} (hr : 0 < r) :
    bgkExponent r β κ = 1 / 2 ↔ κ = r + β - 1 := by
  rw [bgkExponent_eq hr.ne']
  have h2r : (2 : ℝ) * r ≠ 0 := by positivity
  constructor
  · intro h
    have h1 : (β - 1 - κ) / (2 * r) = -(1 / 2) := by linarith
    have h2 : β - 1 - κ = -(1 / 2) * (2 * r) := by
      field_simp at h1 ⊢; linarith [h1]
    have : β - 1 - κ = -r := by rw [h2]; ring
    linarith
  · intro h
    subst h
    rw [show (β - 1 - (r + β - 1)) = -r by ring]
    rw [show -r / (2 * r) = -(1/2) by field_simp]
    norm_num

/-! ## 4. The Wick / polylog separation: why pure-`n`-power cannot reach the prize. -/

/-- **The Wick energy exponent** `θ_Wick(r) = r + s`, where `s = log_n((2r-1)‼) ≥ 0` is the
polylog factor. (The Wick bound is `E_r ≤ (2r-1)‼·nʳ`; in `n`-power form its exponent is `r + s`.) -/
noncomputable def wickEnergyExponent (r s : ℝ) : ℝ := r + s

/-- **The pure-`n`-power prize requirement** `θ_prize(r) = r - β` (from `bgkExponent_eq_half_iff`:
`κ = r+β-1 ⟺ θ = 2r-1-κ = r-β`). -/
noncomputable def prizeNPowerExponent (r β : ℝ) : ℝ := r - β

/-- **The exact Wick-vs-prize separation (`n`-power form).** The Wick energy exponent exceeds the
pure-`n`-power prize requirement by exactly `β + s ≥ β > 0`:
`θ_Wick(r) - θ_prize(r) = β + s`. Hence feeding the TRUE Wick energy `E_r ≤ (2r-1)‼·nʳ` into the
pure-`n`-power chain gives an exponent STRICTLY above `1/2` — the pure-`n`-power chain cannot express
the prize, because it cannot see the `(2r-1)‼ = polylog(q)` factor that the saddle `rpow`
optimization (`_AvPrize_MomentToSupCapstone`) keeps. This pins the prize's reliance on the
archimedean `√(log q)` cancellation, not on a pure `n`-power energy drop. -/
theorem wickExponent_vs_prizeNPower (r β s : ℝ) :
    wickEnergyExponent r s - prizeNPowerExponent r β = β + s := by
  unfold wickEnergyExponent prizeNPowerExponent; ring

/-- **The Wick energy through the pure-`n`-power chain overshoots `1/2`.** With energy exponent
`θ = θ_Wick(r) = r + s` (`s ≥ 0`, the genuine Wick value) and `β ≥ 0`, the realised pure-`n`-power
exponent `α = (θ+β)/(2r)` satisfies `α ≥ 1/2 + β/(2r) > 1/2` whenever `β > 0`. So even the proven
char-0 Wick energy, fed into the *pure-`n`-power* BGK chain, lands above the prize — the
`√(log q)` improvement comes only from the saddle `rpow` route. (`α = 1/2` exactly when `β = 0` and
`s = 0`.) -/
theorem wickThroughNPower_ge_half {r β s : ℝ} (hr : 0 < r) (hβ : 0 ≤ β) (hs : 0 ≤ s) :
    1 / 2 + β / (2 * r) ≤ (wickEnergyExponent r s + β) / (2 * r) := by
  have h2r : (0 : ℝ) < 2 * r := by linarith
  have hgap : (wickEnergyExponent r s + β) / (2 * r) - (1 / 2 + β / (2 * r))
      = s / (2 * r) := by
    unfold wickEnergyExponent
    field_simp
    ring
  have hpos : (0 : ℝ) ≤ s / (2 * r) := div_nonneg hs h2r.le
  have : (0 : ℝ) ≤ (wickEnergyExponent r s + β) / (2 * r) - (1 / 2 + β / (2 * r)) := by
    rw [hgap]; exact hpos
  linarith

/-! ## 5. The combined explicit-chain headline. -/

/-- **The explicit BGK chain headline (algebraic).** The realised exponent of the proven in-tree
chain `‖η_b‖ ≤ n^{bgkExponent r β κ}` decomposes exactly as `1 + (β-1-κ)/(2r)`, so:
* it is `< 1` iff `κ > β-1` (the `o(1)` lives in `(κ-(β-1))/(2r)`);
* it equals the prize `1/2` iff `κ = r+β-1` (energy `θ = r-β`);
* at the prize point `β=4` with the proven gain `κ ≤ 3`, it is `≥ 1` (no gain).
This packages the three exact facts; it is the explicit, optimized form of the BGK chain at `β=4`.
-/
theorem bgk_explicit_headline {r β κ : ℝ} (hr : 0 < r) :
    bgkExponent r β κ = 1 + (β - 1 - κ) / (2 * r)
      ∧ (bgkExponent r β κ < 1 ↔ β - 1 < κ)
      ∧ (bgkExponent r β κ = 1 / 2 ↔ κ = r + β - 1) := by
  exact ⟨bgkExponent_eq hr.ne', bgkExponent_lt_one_iff hr, bgkExponent_eq_half_iff hr⟩

end ProximityGap.Frontier.BGKExplicit

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ProximityGap.Frontier.BGKExplicit.bgkExponent_eq
#print axioms ProximityGap.Frontier.BGKExplicit.bgkExponent_lt_one_iff
#print axioms ProximityGap.Frontier.BGKExplicit.bgkExponent_ge_one_of_smallGain
#print axioms ProximityGap.Frontier.BGKExplicit.bgkExponent_eq_half_iff
#print axioms ProximityGap.Frontier.BGKExplicit.wickExponent_vs_prizeNPower
#print axioms ProximityGap.Frontier.BGKExplicit.wickThroughNPower_ge_half
#print axioms ProximityGap.Frontier.BGKExplicit.bgk_explicit_headline
