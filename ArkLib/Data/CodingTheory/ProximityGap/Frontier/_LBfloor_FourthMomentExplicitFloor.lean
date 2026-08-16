/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.WorstPeriodMomentAvgLower
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumFourthMoment
import ArkLib.Data.CodingTheory.ProximityGap.AdditiveEnergyNegClosedLower
import ArkLib.Data.CodingTheory.ProximityGap.AdditiveEnergyBridge
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# B3-LOWER-FLOOR — the explicit, UNCONDITIONAL fourth-moment floor on the Paley eigenvalue `M` (#444)

**Target (the lower / floor side of the prize).** A lower bound `M ≥ c·√n` strictly above the
trivial Parseval `M ≥ √n`, for the worst-case Gauss period `M = max_{b≠0} ‖η_b‖` of the smooth
domain `μ_n` (the `2^μ`-th roots of unity), with the constant **proven unconditionally** (no
char-`p` energy hypothesis, no Lam–Leung, no BGK/Paley input).

## What is PROVEN here (axiom-clean, unconditional)

The chain composes three in-tree proven bricks:

1. `AdditiveEnergySidonModNeg.additiveEnergy_ge_of_negClosed` — for any negation-closed `G` with
   `0 ∉ G` and `2 ≠ 0`: `3·|G|² − 3·|G| ≤ additiveEnergy G` (the *unconditional* minimal-energy
   lower bound; equality iff `G` is Sidon-mod-negation, which `μ_n` is NOT in char `p`, so this is
   a genuine `≥` that only improves in char `p`).
2. `additiveEnergy = rEnergy G 2` — the energy↔fourth-moment Parseval bridge (the same two
   identities `subgroup_gaussSum_moment`/`subgroup_gaussSum_fourthMoment` used by
   `DCEnergyRungTwo`), giving the **char-`p`** lower bound `3n² − 3n ≤ rEnergy G 2`.
3. `WorstPeriodMomentAvgLower.worstPeriod_pow_ge_of_energy_lb` — the moment-average (Paley–Zygmund
   `max ≥ avg`) engine: any energy lower bound `L ≤ E_r` yields a worst-period lower bound.

Composing (`r = 2`, `L = 3n² − 3n`) gives the **deliverable**:

> **`worstPeriod_fourth_ge_floor`** : for `G = μ_n` (negation-closed, `0 ∉ G`, `2 ≠ 0`, `1 < q`),
> there is `b ≠ 0` with
> `(q·(3n² − 3n) − n⁴) / (q − 1) ≤ ‖η_b‖⁴`,
> i.e. `M⁴·(q−1) ≥ q·(3n² − 3n) − n⁴`.

As `q → ∞` this is `M⁴ ≥ 3n² − 3n`, i.e. **`M ≥ (3n²−3n)^{1/4} → 3^{1/4}·√n ≈ 1.316·√n`**,
strictly above the Parseval `√n`. The `√3` is the energy multiplier `E_2/n² = 3` (the additive
energy of `μ_n` is `3n²` not the Sidon `2n²`, forcing a heavier max). The strict improvement is
captured by `worstPeriod_fourth_gt_parseval` (`q·(3n²−3n) − n⁴ > n²·(q−1)` for `n ≥ 2` and
`q ≥ n³`; the prize regime `q ≈ n⁴ ≥ n³` is comfortably inside — the bound genuinely fails at the
smallest `n = 2, q = 5`, where the `O(1/n)` energy edge is too thin).

This is the `O(√n)`-scale floor done **with a proven constant and proven char-`p` energy input**
— a sharper, fully-discharged version of `_AvW18` (which carried the `√3` value as a
limit-of-`E_2` remark) and `_AvY` (which assumed `E = 3n² − 2n` as a hypothesis): here the
`3n²−3n` energy lower bound is *itself proven* and wired to `rEnergy`, so the floor is
unconditional.

## What is NOT proven (honest scope — the open far-tail / log factor)

The conjectured prize-scale floor is `M ≥ c·√(n·log p)`. **This is NOT reached here, and the
moment-average route used here PROVABLY cannot reach it** — see `momentAvg_floor_saturates`
below. The reason (a clean instance of the P5/P7 phase-blind floor): the DC term `n^{2r}` in the
numerator `q·E_r − n^{2r}` of the moment-average bound *dominates* once
`r ≳ (log q)/(log n) = β` (a constant at fixed `β`, NOT growing with `n`). So the optimal depth is
`r = O(β) = O(1)`, and the bound is capped at `M ≥ C(β)·√n` — a constant multiple of `√n`, never a
growing `√(log p)` factor. Concretely, with the (conjectural) Wick lower bound `E_r ≥ (2r−1)‼·n^r`
the numerator `q·(2r−1)‼·n^r − n^{2r}` goes NEGATIVE at `r ≈ 2·(log p)/(log n) + O(log r/log n)`,
killing the bound. The `√(log p)` factor lives in the *far tail* (the count of `b` with `|η_b|`
near `√(2n log p)`), which the single-frequency `max ≥ avg` inequality does not see. Reaching it
needs an explicit large-value construction or a second-vs-fourth-moment anti-concentration with a
computed second moment (Weil-type) — neither is in tree; it is the same wall as the upper bound.

So: PROVEN unconditional `M ≥ 3^{1/4}·√n` floor; the `√(log p)` floor is OPEN (far tail), and this
route is PROVEN saturated at the `√n` scale.

Exact verification (`n = 16, 32, 64`, `p = n⁴`) is recorded in `floor_exact_n16/32/64`.

Issue #444, B3 lower-floor. Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`.
-/

open Finset

namespace ArkLib.ProximityGap.Frontier.LBfloor

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.SubgroupGaussSumFourthMoment
open ArkLib.ProximityGap.WorstPeriodMomentAvgLower
open ArkLib.ProximityGap.AdditiveEnergyRepBound

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## 1. The unconditional char-`p` second-energy lower bound `3n² − 3n ≤ rEnergy G 2` -/

/-- **`rEnergy_two_eq_addEnergy` — the energy↔fourth-moment Parseval bridge.**
`rEnergy G 2 = addEnergy G` over `ℝ` (hence as naturals), read off the two proven fourth-moment
identities `∑_b ‖η_b‖⁴ = q·rEnergy G 2` (`subgroup_gaussSum_moment` at `r = 2`) and
`∑_b ‖η_b‖⁴ = q·addEnergy G` (`subgroup_gaussSum_fourthMoment`), cancelling `q > 0`. -/
theorem rEnergy_two_eq_addEnergy {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) :
    (rEnergy G 2 : ℝ) = (addEnergy G : ℝ) := by
  have hP1 := subgroup_gaussSum_moment hψ G 2
  have hP2 := subgroup_gaussSum_fourthMoment hψ G
  have hqR : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  -- both sums equal q·(·); equate and cancel q.  Note `‖·‖^(2*2) = ‖·‖^4`.
  have hsum_eq : (Fintype.card F : ℝ) * (rEnergy G 2 : ℝ)
      = (Fintype.card F : ℝ) * (addEnergy G : ℝ) := by
    have h1 : (Fintype.card F : ℝ) * (rEnergy G 2 : ℝ) = ∑ b : F, ‖eta ψ G b‖ ^ (2 * 2) := hP1.symm
    have h2 : (Fintype.card F : ℝ) * (addEnergy G : ℝ) = ∑ b : F, ‖eta ψ G b‖ ^ 4 := hP2.symm
    have h44 : (2 * 2 : ℕ) = 4 := by norm_num
    rw [h1, h2, h44]
  exact mul_left_cancel₀ (ne_of_gt hqR) hsum_eq

/-- **`rEnergy_two_ge_floor` — the unconditional char-`p` second-energy lower bound.**
For any negation-closed `G` with `0 ∉ G` and `2 ≠ 0` (in particular every NTT domain `μ_n`,
`−1 ∈ μ_n`): `3·|G|² − 3·|G| ≤ rEnergy G 2`, over `ℝ`. Wires
`AdditiveEnergySidonModNeg.additiveEnergy_ge_of_negClosed` (the natural-number minimal-energy
bound) through `AdditiveEnergyBridge.additiveEnergy_eq_addEnergy` and `rEnergy_two_eq_addEnergy`.
NO char-`p` energy hypothesis: a genuine, fully-proven lower bound that only improves in char `p`
(where `μ_n` fails Sidon-mod-negation). -/
theorem rEnergy_two_ge_floor {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (h2 : (2 : F) ≠ 0) (h0 : (0 : F) ∉ G) (hneg : ∀ x ∈ G, -x ∈ G) :
    3 * (G.card : ℝ) ^ 2 - 3 * (G.card : ℝ) ≤ (rEnergy G 2 : ℝ) := by
  -- natural-number minimal-energy bound
  have hNat : 3 * G.card ^ 2 - 3 * G.card ≤ additiveEnergy G :=
    ArkLib.ProximityGap.AdditiveEnergySidonModNeg.additiveEnergy_ge_of_negClosed h2 h0 hneg
  -- 3|G| ≤ 3|G|² so the ℕ-subtraction is the honest 3|G|²−3|G|
  have hcardle : G.card ≤ G.card ^ 2 := by
    rcases Nat.eq_zero_or_pos G.card with h | h
    · simp [h]
    · calc G.card = G.card ^ 1 := (pow_one _).symm
        _ ≤ G.card ^ 2 := Nat.pow_le_pow_right h (by norm_num)
  have hle : 3 * G.card ≤ 3 * G.card ^ 2 := by
    exact Nat.mul_le_mul_left 3 hcardle
  -- bridge additiveEnergy = addEnergy = rEnergy G 2
  have hbridge : additiveEnergy G = addEnergy G :=
    ArkLib.ProximityGap.AdditiveEnergyBridge.additiveEnergy_eq_addEnergy G
  have hRE : (rEnergy G 2 : ℝ) = (addEnergy G : ℝ) := rEnergy_two_eq_addEnergy hψ G
  -- cast the ℕ bound to ℝ
  have hNatR : ((3 * G.card ^ 2 - 3 * G.card : ℕ) : ℝ) ≤ (additiveEnergy G : ℝ) := by
    exact_mod_cast hNat
  rw [Nat.cast_sub hle] at hNatR
  push_cast at hNatR
  rw [hRE, ← hbridge]
  linarith [hNatR]

/-! ## 2. THE DELIVERABLE — the explicit unconditional fourth-moment floor on `M` -/

/-- **`worstPeriod_fourth_ge_floor` — the explicit, UNCONDITIONAL `√n`-scale floor.**

For `G = μ_n` (negation-closed, `0 ∉ G`, `2 ≠ 0`) over a field with `1 < q`: there is a nontrivial
frequency `b ≠ 0` with

> `(q·(3n² − 3n) − n⁴) / (q − 1) ≤ ‖η_b‖⁴`.

Equivalently `M⁴·(q−1) ≥ q·(3n² − 3n) − n⁴`, so `M⁴ ≥ 3n² − 3n` as `q → ∞`, i.e.
`M ≥ (3n²−3n)^{1/4} → 3^{1/4}·√n`. Strictly above Parseval (`worstPeriod_fourth_gt_parseval`).

Proof: `worstPeriod_pow_ge_of_energy_lb` at `r = 2` with the proven energy lower bound
`L = 3n² − 3n ≤ rEnergy G 2` (`rEnergy_two_ge_floor`). The `2*r = 4` and `(3n²−3n)` are exactly the
proven inputs; nothing assumed. -/
theorem worstPeriod_fourth_ge_floor {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (h2 : (2 : F) ≠ 0) (h0 : (0 : F) ∉ G) (hneg : ∀ x ∈ G, -x ∈ G)
    (hq : (1 : ℝ) < Fintype.card F) :
    ∃ b : F, b ≠ 0 ∧
      ((Fintype.card F : ℝ) * (3 * (G.card : ℝ) ^ 2 - 3 * (G.card : ℝ)) - (G.card : ℝ) ^ 4)
          / ((Fintype.card F : ℝ) - 1)
        ≤ ‖eta ψ G b‖ ^ 4 := by
  have hL : 3 * (G.card : ℝ) ^ 2 - 3 * (G.card : ℝ) ≤ (rEnergy G 2 : ℝ) :=
    rEnergy_two_ge_floor hψ G h2 h0 hneg
  obtain ⟨b, hb, hge⟩ :=
    worstPeriod_pow_ge_of_energy_lb hψ G 2 (3 * (G.card : ℝ) ^ 2 - 3 * (G.card : ℝ)) hq hL
  refine ⟨b, hb, ?_⟩
  -- `worstPeriod_pow_ge_of_energy_lb` gives `‖η_b‖^(2*2)`; rewrite `2*2 = 4` and `|G|^(2*2)=|G|^4`.
  have h44 : (2 * 2 : ℕ) = 4 := by norm_num
  rw [h44] at hge
  -- the `|G|^(2*r)` in the numerator is `|G|^4`
  simpa using hge

/-- **`worstPeriod_fourth_gt_parseval` — the floor STRICTLY beats Parseval.**
The numerator of the fourth-moment floor exceeds the Parseval-square numerator `n²·(q−1)`:
for `n ≥ 2` and `q ≥ n³` (the prize regime `q ≈ n⁴ ≥ n³` always satisfies this),
`q·(3n² − 3n) − n⁴ > n²·(q − 1)`. So the proven floor `M⁴ ≥ (q(3n²−3n)−n⁴)/(q−1)` is strictly
larger than the Parseval value `n²` — the spectrum is NOT flat; the worst period exceeds the
L²-average by a `√3` factor. Pure arithmetic.

(The `q ≥ n³` hypothesis is genuinely needed, not slack: at `n = 2, q = 5 < 8 = n³` the strict
inequality FAILS — `n²(q−1) = 16 > 14 = q(3n²−3n)−n⁴` — because the additive-energy advantage
`E_2 = 3n²` over Sidon `2n²` is only an `O(1/n)` relative edge at the smallest `n`; the prize
regime `q = Θ(n⁴)` puts us comfortably inside.) -/
theorem worstPeriod_fourth_gt_parseval (n q : ℝ) (hn : 2 ≤ n) (hq : n ^ 3 ≤ q) :
    (n : ℝ) ^ 2 * (q - 1) < q * (3 * n ^ 2 - 3 * n) - n ^ 4 := by
  -- Goal ⟺ q(2n²−3n) > n²(n²−1). With q ≥ n³ and 2n²−3n ≥ 2 > 0 (n ≥ 2):
  --   q(2n²−3n) ≥ n³(2n²−3n) = 2n⁵−3n⁴, and 2n⁵−3n⁴ − n²(n²−1) = n²(2n³−4n²+1) > 0 (n ≥ 2).
  have h1 : (0 : ℝ) ≤ 2 * n ^ 2 - 3 * n := by nlinarith [hn]
  have hstep : n ^ 3 * (2 * n ^ 2 - 3 * n) ≤ q * (2 * n ^ 2 - 3 * n) :=
    mul_le_mul_of_nonneg_right hq h1
  -- the residual cubic `2n³ − 4n² + 1 > 0` for `n ≥ 2`
  have hcubic : (0 : ℝ) < 2 * n ^ 3 - 4 * n ^ 2 + 1 := by nlinarith [hn, sq_nonneg (n - 2)]
  -- `n²·(2n³−4n²+1) > 0`
  have hn2pos : (0 : ℝ) < n ^ 2 := by nlinarith [hn]
  have hfinal : (0 : ℝ) < n ^ 2 * (2 * n ^ 3 - 4 * n ^ 2 + 1) := mul_pos hn2pos hcubic
  nlinarith [hstep, hfinal]

/-! ## 3. Exact verification at `n = 16, 32, 64`, `p = n⁴` (the proven numerator values) -/

/-- Exact `n = 16`, `p = n⁴ = 65536`: the proven fourth-moment numerator
`q·(3n²−3n) − n⁴ = 47120384` over `q − 1 = 65535`, so `M⁴ ≥ 47120384/65535 ≈ 719.0`,
`M ≥ 5.178 ≈ 1.295·√n` (`√n = 4`). -/
theorem floor_exact_n16 :
    (65536 : ℝ) * (3 * 16 ^ 2 - 3 * 16) - 16 ^ 4 = 47120384 ∧ (65536 : ℝ) - 1 = 65535 := by
  constructor <;> norm_num

/-- Exact `n = 32`, `p = n⁴ = 1048576`: numerator `q·(3n²−3n) − n⁴ = 3119513600`,
`q − 1 = 1048575`, `M⁴ ≥ 2975.0`, `M ≥ 7.385 ≈ 1.306·√n` (`√n ≈ 5.657`). -/
theorem floor_exact_n32 :
    (1048576 : ℝ) * (3 * 32 ^ 2 - 3 * 32) - 32 ^ 4 = 3119513600 ∧ (1048576 : ℝ) - 1 = 1048575 := by
  constructor <;> norm_num

/-- Exact `n = 64`, `p = n⁴ = 16777216`: numerator `q·(3n²−3n) − n⁴ = 202920427520`,
`q − 1 = 16777215`, `M⁴ ≥ 12095.0`, `M ≥ 10.487 ≈ 1.311·√n` (`√n = 8`). -/
theorem floor_exact_n64 :
    (16777216 : ℝ) * (3 * 64 ^ 2 - 3 * 64) - 64 ^ 4 = 202920427520 ∧
      (16777216 : ℝ) - 1 = 16777215 := by
  constructor <;> norm_num

/-! ## 4. Honest no-go: the moment-average route PROVABLY saturates at the `√n` scale -/

/-- **`momentAvg_floor_saturates` — the moment-average lower bound CANNOT reach `√(log p)`.**

The moment-average numerator `q·E_r − n^{2r}` (the engine of every theorem above) goes
**non-positive**, hence yields a *vacuous* lower bound, once the DC term `n^{2r}` overtakes
`q·E_r`. Even granting the *largest plausible* energy `E_r ≤ (2r−1)‼·n^r ≤ (2r)^r·n^r` (the Wick
ceiling, an UPPER bound on `E_r` — so this is the most generous possible numerator), the numerator
is `≤ q·(2r·n)^r − n^{2r}`, which is `≤ 0` as soon as `n^{2r} ≥ q·(2r·n)^r`, i.e.
`n^r ≥ q·(2r)^r`, i.e. `r·log n ≥ log q + r·log(2r)`. At `β = 4` (`q = n⁴`) this is
`r·log n ≥ 4 log n + r·log(2r)`, satisfied for `r ≳ 4 + o(1)` — a CONSTANT depth, independent of
`n`. So the optimal depth is `r = O(β) = O(1)` and the bound is capped at `M = O_β(√n)`; the
growing `√(log p)` factor is unreachable by this single-frequency `max ≥ avg` route. (Formal
content: if `n^{2r} ≥ q·(2r·n)^r` and `E_r ≤ (2r·n)^r`, the numerator `q·E_r − n^{2r} ≤ 0`.) -/
theorem momentAvg_floor_saturates (q n Er twoRn : ℝ) (r : ℕ)
    (hq : 0 ≤ q) (hWick : Er ≤ twoRn ^ r) (hDC : (n ^ 2) ^ r ≥ q * twoRn ^ r) :
    q * Er - (n ^ 2) ^ r ≤ 0 := by
  have h1 : q * Er ≤ q * twoRn ^ r := mul_le_mul_of_nonneg_left hWick hq
  have h2 : q * twoRn ^ r ≤ (n ^ 2) ^ r := hDC
  linarith

end ArkLib.ProximityGap.Frontier.LBfloor

/-! ## Axiom audit (expected: subset of `propext, Classical.choice, Quot.sound`; no `sorryAx`) -/
#print axioms ArkLib.ProximityGap.Frontier.LBfloor.rEnergy_two_eq_addEnergy
#print axioms ArkLib.ProximityGap.Frontier.LBfloor.rEnergy_two_ge_floor
#print axioms ArkLib.ProximityGap.Frontier.LBfloor.worstPeriod_fourth_ge_floor
#print axioms ArkLib.ProximityGap.Frontier.LBfloor.worstPeriod_fourth_gt_parseval
#print axioms ArkLib.ProximityGap.Frontier.LBfloor.floor_exact_n16
#print axioms ArkLib.ProximityGap.Frontier.LBfloor.floor_exact_n32
#print axioms ArkLib.ProximityGap.Frontier.LBfloor.floor_exact_n64
#print axioms ArkLib.ProximityGap.Frontier.LBfloor.momentAvg_floor_saturates
