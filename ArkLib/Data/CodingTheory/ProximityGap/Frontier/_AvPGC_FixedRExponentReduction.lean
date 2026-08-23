/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# Fixed-`r₀` effective-exponent reduction for the Paley/BGK sup-norm (#444)

This brick records, axiom-clean, the EXACT arithmetic of the "best effective exponent via a fixed
moment depth `r₀`" route for the thin (`β = 4`, `p = n⁴`) Paley/BGK sup-norm
`M(μₙ) = max_{b≠0} |ηₙ(b)|`, and pins precisely where uniformity-in-`p` is — and is NOT — proven.

## The route (all steps below the headline are elementary / in-tree)

For any depth `r₀ ≥ 1`:
`M^{2r₀} ≤ Σ_{b≠0} |ηₙ(b)|^{2r₀} = p·E_{r₀}^{F_p} − n^{2r₀} ≤ p·E_{r₀}^{F_p}`   (moment ≤ energy, in-tree)

If `E_{r₀}^{F_p} ≤ K·(2r₀−1)‼·nʳ⁰` UNIFORMLY in `p`, then at `p = n⁴`:
`M ≤ (n⁴ · K·(2r₀−1)‼·nʳ⁰)^{1/(2r₀)} = C · n^{(4+r₀)/(2r₀)} = C · n^{1/2 + 2/r₀}`,
with `C = (K·(2r₀−1)‼)^{1/(2r₀)}` an absolute constant.

So the effective exponent of the fixed-`r₀` route is `θ(r₀) = 1/2 + 2/r₀` (NOT `1/2 + 1/r₀`).

## The headline `effectiveExponent` and `beatsTrivial_iff`

`θ(r₀) = 1/2 + 2/r₀`.  Since `M ≤ n = n¹` is trivial, the route is SUBTRIVIAL (`θ < 1`)
iff `2/r₀ < 1/2` iff `r₀ ≥ 5`.  The prize exponent `θ = 1/2` is the `r₀ → ∞` limit.

This is proven below as exact rational arithmetic (`beatsTrivial_iff_five_le`,
`prize_is_limit`).

## Where uniformity-in-`p` is / is NOT proven (HONEST SCOPE — exact-integer verified)

The char-0 reference is proven `r`-uniform with `K = 1`
(`Frontier/_AvW0_BesselWickDomination.charZeroWick_bound_allR`):
`E_{r₀}^{char0}(μₙ) ≤ (2r₀−1)‼·nʳ⁰`.  Hence the route closes at depth `r₀` IFF
`W_{r₀} := E_{r₀}^{F_p} − E_{r₀}^{char0}` is bounded by `(K−1)·(2r₀−1)‼·nʳ⁰` uniformly in thin `p`.

EXACT-INTEGER FACTS (no floats; scripts/probes recompute, `μ_n` over the smallest thin primes and
full thin-band scans `[n⁴, 1.5·n⁴)`):
* `W_2 = 0` for ALL thin `p` (Sidon: the only nontrivial additive quadruple of `μ_{2^μ}` is
  antipodal).  `θ(2) = 3/2`. PROVEN uniform, but supratrivial.
* `W_3 = 0` for `n = 8, 16` over the whole scanned thin band, BUT `W_3 ≠ 0` at 61 of 2333 thin
  primes for `n = 32`.  So `W_3 = 0` is NOT uniform in thin `p`.  Even so, the worst measured
  `E_3^{F_p}/Wick = 0.9401 < 1` (n=32).  `θ(3) = 7/6`, still supratrivial.
* `W_4 > 0` already at the Fermat prime `p = n⁴+1` (`n = 16, 32`); worst `E_4/Wick = 0.6764`.
  `θ(4) = 1`, exactly trivial.
* `r₀ = 5` is the FIRST subtrivial depth (`θ = 9/10 < 1`).  Worst measured `E_5/Wick = 0.5217`
  (n=16) — comfortably `< 1` — but at `r₀ = 5` the wraparound `W_5` is genuinely active and
  bounding it uniformly in thin `p` is exactly the open Lam–Leung / cyclotomic minimal-weight wall
  (`Frontier/_NoExcessOnsetThreshold.OnsetExceedsSaddle`, NOT discharged).

CONCLUSION (honest): the fully-PROVEN-uniform facts (`W_2 = 0`, char-0 Bessel `K = 1`) reach only
`r₀ = 2`, `θ = 3/2`.  An effective `θ < 1` requires `r₀ ≥ 5`, which requires a uniform `W_5` bound
that does NOT exist — it is the prize wall.  This brick lands the EXACT arithmetic of the route and
names the gap; it does NOT prove `θ < 1`.

**Axiom target:** `[propext, Classical.choice, Quot.sound]`; no `sorry`, no `native_decide`.
-/

namespace ArkLib.ProximityGap.Frontier.FixedRExponentReduction

/-- The effective exponent of the fixed-depth-`r₀` route at `β = 4` (`p = n⁴`):
`θ(r₀) = 1/2 + 2/r₀`, derived from `M ≤ (p · K (2r₀−1)‼ nʳ⁰)^{1/(2r₀)}` with `p = n⁴`. -/
def effectiveExponent (r₀ : ℕ) : ℚ := 1 / 2 + 2 / r₀

/-- At `r₀ = 4` the route exponent is exactly `1`, i.e. the TRIVIAL bound `M ≤ n`. -/
theorem exponent_at_four : effectiveExponent 4 = 1 := by
  unfold effectiveExponent; norm_num

/-- At `r₀ = 5` the route exponent is `9/10 < 1` — the first SUBTRIVIAL depth. -/
theorem exponent_at_five : effectiveExponent 5 = 9 / 10 := by
  unfold effectiveExponent; norm_num

/-- At `r₀ = 8`: `θ = 3/4`. -/
theorem exponent_at_eight : effectiveExponent 8 = 3 / 4 := by
  unfold effectiveExponent; norm_num

/-- **The route is subtrivial (`θ < 1`) at depth `r₀ ≥ 1` iff `r₀ ≥ 5`.**
Beating the trivial bound `M ≤ n` via a fixed moment depth requires `r₀ ≥ 5`. -/
theorem beatsTrivial_iff_five_le {r₀ : ℕ} (hr : 1 ≤ r₀) :
    effectiveExponent r₀ < 1 ↔ 5 ≤ r₀ := by
  unfold effectiveExponent
  have hr0 : (0 : ℚ) < r₀ := by exact_mod_cast hr
  rw [show (1 : ℚ) / 2 + 2 / r₀ < 1 ↔ 2 / (r₀ : ℚ) < 1 / 2 by constructor <;> intro h <;> linarith]
  rw [div_lt_div_iff₀ hr0 (by norm_num : (0:ℚ) < 2)]
  constructor
  · intro h
    have h4 : (4 : ℚ) < r₀ := by linarith
    have : (4 : ℕ) < r₀ := by exact_mod_cast h4
    omega
  · intro h
    have : (5 : ℚ) ≤ r₀ := by exact_mod_cast h
    linarith

/-- The prize exponent `1/2` is the `r₀ → ∞` limit of `θ(r₀)`: for every `ε > 0` there is a depth
`r₀` with `θ(r₀) < 1/2 + ε`. (Tendsto-free elementary witness.) -/
theorem prize_is_limit {ε : ℚ} (hε : 0 < ε) :
    ∃ r₀ : ℕ, 1 ≤ r₀ ∧ effectiveExponent r₀ < 1 / 2 + ε := by
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / ε)
  refine ⟨N + 1, by omega, ?_⟩
  unfold effectiveExponent
  have hpos : (0 : ℚ) < (N : ℚ) + 1 := by positivity
  have hcast : ((N + 1 : ℕ) : ℚ) = (N : ℚ) + 1 := by push_cast; ring
  rw [hcast]
  have h2 : 2 / ((N : ℚ) + 1) < ε := by
    rw [div_lt_iff₀ hpos]
    have h3 : 2 / ε < (N : ℚ) + 1 := by linarith
    rw [div_lt_iff₀ hε] at h3
    nlinarith [h3]
  linarith

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms exponent_at_four
#print axioms exponent_at_five
#print axioms beatsTrivial_iff_five_le
#print axioms prize_is_limit

end ArkLib.ProximityGap.Frontier.FixedRExponentReduction
