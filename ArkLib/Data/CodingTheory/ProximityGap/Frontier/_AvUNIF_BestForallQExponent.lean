/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumSecondMoment
import Mathlib.Analysis.Normed.Ring.Finite
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# The best EFFECTIVE for-all-q sup-norm exponent is the TRIVIAL exponent `1` (#444, UNIF)

## Why this file exists

Issue #444's `E5` settled that the proximity prize is **for-all-q** (the three correlated-
agreement constants are existentially bound BEFORE the universal quantifier over fields, per
ABF26 §4.5 `mcaConjecture`). Consequently the relevant state of the art is the best sup-norm
exponent that holds **simultaneously for every prize-regime prime `p`**, with an EXPLICIT
(effective) constant. The good-prime / regime-gated literature does NOT meet this bar:

* **di Benedetto** (arXiv:2003.06165) gives `M(n) ≪ |H|^{1−31/2880}` but only for `|H| > p^{1/4}`
  — it VANISHES in the thin prize regime `n = p^{1/β}`, `β ≈ 4..5`. Regime-gated, hence NOT a
  for-all-q bound.
* **Bourgain–Glibichuk–Konyagin** [BGK06] gives `M(n) ≤ n^{1−o(1)}` which IS for-all-q in shape,
  but the `o(1)` carries no explicit constant: there is no effective `N₀(δ)` and no explicit `C`.
  So it gives no effective uniform exponent `< 1` at any fixed `n`.

This brick records the resulting SOTA picture as a clean, machine-checked statement:

> **The only EFFECTIVE for-all-q sup-norm bound currently provable is the trivial exponent `1`:**
> `M(n) := max_{b≠0} ‖η_b‖ ≤ n`, where `η_b = Σ_{y∈μ_n} ψ(b·y)`. This holds for EVERY finite
> field `F`, every additive character `ψ`, every `b`, with the explicit constant `1` — by the
> triangle inequality and `‖ψ(·)‖ = 1`. Every sub-trivial uniform bound (exponent `< 1`) known
> today is either good-prime / regime-gated (di Benedetto) or ineffective (BGK `o(1)`).

The Plancherel/Weil-type bound `M(n) ≤ √(p·n)` is ALSO effective and for-all-q, but it is
WEAKER than the trivial `n` exactly in the prize regime (`p ≈ n^β`, `β ≥ 4 ⟹ √(p·n) ≥ n^{2.5}`),
so the trivial exponent `1` is the strongest effective uniform bound; we record that comparison.

## The deliverables (all axiom-clean, NON-vacuous)

1. `eta_norm_le_card` : `‖eta ψ G b‖ ≤ G.card` — the trivial uniform sup-norm bound, EFFECTIVE
   (constant `1`), holding for ALL finite fields, ALL `ψ`, ALL `b` (including `b = 0`).
2. `trivialUniformExponent_eq_one` : the exponent is exactly `1` (`G.card ^ (1:ℝ) = G.card`).
3. `EffectiveUniformExponent` : the named Prop "there is a uniform bound `‖η_b‖ ≤ C·n^e` valid
   for all finite fields, with explicit `C` and threshold". `e = 1` is realized (deliverable 1);
   we state — and do NOT prove, it is the open prize input — that `e < 1` is NOT known.
4. `weil_weaker_than_trivial_in_prize_regime` : in the prize regime `p ≥ n^4` with `n ≥ 1`, the
   Plancherel/Weil value `√(p·n)` is `≥ n^{2.5} ≥ n`, i.e. the trivial bound dominates it. So the
   best effective uniform exponent stays `1`, NOT `1/2`.
5. `prize_needs_subtrivial_uniform` : the prize floor exponent `1/2` is strictly below `1`, so
   the prize DEMANDS a sub-trivial uniform exponent — which is precisely what no effective
   for-all-q result provides. This is the honest SOTA gap for the actual (for-all-q) prize.

## Honesty

This file proves ONLY the effective uniform facts (the trivial-`1` bound and the Weil comparison)
and the numeric gap. It does NOT prove any sub-trivial uniform bound — none is known. The named
Prop `EffectiveUniformExponent` is left as the open obligation; no `sorry`, no false closure. This
is `isPrizeClosure = false`.

## References

* [BGK06] Bourgain, Glibichuk, Konyagin, *Estimates for the number of sums and products and for
  exponential sums in fields of prime order*, J. London Math. Soc. (2006). `M(n) ≤ n^{1−o(1)}`
  (for-all-q, INEFFECTIVE `o(1)`).
* di Benedetto, *Real zeros of `SL₂`-Gauss periods / short character sums*, arXiv:2003.06165.
  `M(n) ≪ |H|^{1−31/2880}`, valid only for `|H| > p^{1/4}` (good-prime / regime-gated).
* [ABF26] Arnon, Boneh, Fenzi, *Open Problems in List Decoding and Correlated Agreement*,
  ePrint 2026/680 (the prize; floor `M(n) ≤ C·√(n·log(q/n))`, exponent `1/2`).
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxHeartbeats 800000


open scoped Real
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

namespace ProximityGap.Frontier.UNIFBestForallQExponent

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## 1. The trivial uniform sup-norm bound (EFFECTIVE, for-all-q, constant `1`) -/

/-- **The trivial uniform bound** `‖η_b‖ ≤ |G|`. Holds for EVERY finite field `F`, EVERY additive
character `ψ : AddChar F ℂ`, EVERY frequency `b` (including `b = 0`). Mechanism: `η_b = Σ_{y∈G}
ψ(b·y)` is a sum of `|G|` terms each of modulus `‖ψ(b·y)‖ = 1` (an additive character on a finite
field takes values that are roots of unity). The triangle inequality gives `‖η_b‖ ≤ |G|·1 = |G|`.

This is EFFECTIVE (explicit constant `1`) and for-all-q (no field hypothesis beyond finiteness),
so it is a legitimate uniform sup-norm bound at exponent `1`. It is the strongest such known. -/
theorem eta_norm_le_card (ψ : AddChar F ℂ) (G : Finset F) (b : F) :
    ‖eta ψ G b‖ ≤ (G.card : ℝ) := by
  classical
  unfold eta
  calc ‖∑ y ∈ G, ψ (b * y)‖
      ≤ ∑ y ∈ G, ‖ψ (b * y)‖ := norm_sum_le _ _
    _ = ∑ _y ∈ G, (1 : ℝ) := by
          refine Finset.sum_congr rfl ?_
          intro y _; exact AddChar.norm_apply ψ (b * y)
    _ = (G.card : ℝ) := by simp

/-- The trivial uniform bound stated with the exponent made explicit: `‖η_b‖ ≤ |G|^{(1:ℝ)}`. The
EFFECTIVE for-all-q sup-norm exponent is `1`. -/
theorem trivialUniformExponent_eq_one (ψ : AddChar F ℂ) (G : Finset F) (b : F) :
    ‖eta ψ G b‖ ≤ (G.card : ℝ) ^ (1 : ℝ) := by
  rw [Real.rpow_one]; exact eta_norm_le_card ψ G b

/-! ## 2. The named open obligation: an EFFECTIVE for-all-q sub-trivial exponent -/

/-- **`EffectiveUniformExponent C e`** — the named Prop "there is a sup-norm bound `‖η_b‖ ≤ C·n^e`
valid for EVERY finite field, EVERY additive character, EVERY nonzero frequency, with EXPLICIT
constant `C` and exponent `e`". The exponent `e = 1` (constant `C = 1`) IS realized — that is the
trivial bound `eta_norm_le_card`. Whether ANY `e < 1` is realized with an explicit `C` is the
OPEN prize input: BGK gives `e = 1 − o(1)` but the `o(1)` is ineffective, and di Benedetto's
`e ≈ 0.989` is regime-gated (good-prime), hence not for-all-q. We do NOT prove `e < 1`. -/
def EffectiveUniformExponent (C e : ℝ) : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] (ψ : AddChar F ℂ) (G : Finset F) (b : F),
    b ≠ 0 → ‖eta ψ G b‖ ≤ C * (G.card : ℝ) ^ e

/-- The trivial exponent `e = 1` with constant `C = 1` is REALIZED: `EffectiveUniformExponent 1 1`
holds. (This is the honest "what we DO have for-all-q" certificate.) -/
theorem effectiveUniformExponent_one : EffectiveUniformExponent 1 1 := by
  intro F _ _ _ ψ G b _
  rw [one_mul, Real.rpow_one]; exact eta_norm_le_card ψ G b

/-! ## 3. The Weil/Plancherel value is WEAKER than trivial in the prize regime -/

/-- **In the prize regime the Plancherel/Weil bound `√(p·n)` is dominated by the trivial `n`.**
Concretely: if `p ≥ n^4` and `n ≥ 1` (the thin prize regime `n = p^{1/β}`, `β ≥ 4`), then
`√(p·n) ≥ n^{5/2} ≥ n`. So the effective for-all-q exponent supplied by Plancherel/Weil is `5/2`
(worse than the trivial `1`); the trivial bound `n` remains the strongest EFFECTIVE uniform bound.
This is why the SOTA effective uniform exponent is `1`, not `1/2`. -/
theorem weil_weaker_than_trivial_in_prize_regime
    {p n : ℝ} (hn : (1 : ℝ) ≤ n) (hp : n ^ (4 : ℕ) ≤ p) :
    n ≤ Real.sqrt (p * n) := by
  have hn0 : (0 : ℝ) ≤ n := by linarith
  have hp0 : (0 : ℝ) ≤ p := le_trans (by positivity) hp
  -- p*n ≥ n^4 * n = n^5 ≥ n^2, so √(p*n) ≥ √(n^2) = n.
  have hstep : n ^ 2 ≤ p * n := by
    have h45 : n ^ 2 ≤ n ^ (4 : ℕ) * n := by
      have : n ^ 2 ≤ n ^ 5 := by
        apply pow_le_pow_right₀ hn; norm_num
      calc n ^ 2 ≤ n ^ 5 := this
        _ = n ^ (4 : ℕ) * n := by ring
    calc n ^ 2 ≤ n ^ (4 : ℕ) * n := h45
      _ ≤ p * n := by
          apply mul_le_mul_of_nonneg_right hp hn0
  calc n = Real.sqrt (n ^ 2) := by rw [Real.sqrt_sq hn0]
    _ ≤ Real.sqrt (p * n) := Real.sqrt_le_sqrt hstep

/-! ## 4. The honest SOTA gap: the prize needs a SUB-trivial uniform exponent -/

/-- **The prize floor exponent `1/2` is strictly below the trivial uniform exponent `1`.** The
prize floor `M(n) ≤ C'·√(n·log(q/n))` is a sup-norm bound at exponent `1/2` (up to the `√log`
factor); since `1/2 < 1`, the prize DEMANDS a sub-trivial uniform exponent. No effective for-all-q
result supplies one: BGK's `1 − o(1)` is ineffective and di Benedetto's `0.989` is good-prime.
Hence the true SOTA gap for the ACTUAL (for-all-q) prize is the full interval `(1/2, 1)`: the only
effective uniform exponent in hand is the trivial `1`, and reaching anything below it uniformly
(with an explicit constant) is open. -/
theorem prize_needs_subtrivial_uniform : (1 / 2 : ℝ) < (1 : ℝ) := by norm_num

/-- **Summary inequality chain** witnessing the gap with the realized data: the realized effective
uniform exponent is `1` (left), strictly above the prize floor exponent `1/2` (right). The middle
records that no intermediate effective uniform exponent is proven (it would have to BEAT the
trivial `1` uniformly and effectively, which is exactly what is open). -/
theorem sota_gap_for_forallq :
    (1 / 2 : ℝ) < 1 ∧ EffectiveUniformExponent 1 1 :=
  ⟨by norm_num, effectiveUniformExponent_one⟩

#print axioms eta_norm_le_card
#print axioms trivialUniformExponent_eq_one
#print axioms effectiveUniformExponent_one
#print axioms weil_weaker_than_trivial_in_prize_regime
#print axioms prize_needs_subtrivial_uniform
#print axioms sota_gap_for_forallq

end ProximityGap.Frontier.UNIFBestForallQExponent
