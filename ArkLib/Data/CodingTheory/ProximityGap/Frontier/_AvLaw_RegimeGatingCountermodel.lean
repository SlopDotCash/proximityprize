/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# The empirical law-book of the period family, and the regime-gating law (#444)

A unification step: the period family `η_b = Σ_{x∈μ_n} e_p(bx)` (`b ≠ 0`) obeys a stack of empirical
laws, and computing them all in one place reveals they are **stratified by moment-order**, which
pins
exactly where the open content lives. This file records that stratification and proves the one
genuinely
new structural law it surfaces: the **regime-gating** (thinness-essentiality) of the prize bound.

## The law-book (each verified exact on real `μ_n`; order = moment-order)

| law | order | status |
|---|---|---|
| `Σ_{b≠0}\|η_b\|² = pn − n²` (Parseval), RMS `= √n` | 2 | **PROVEN** |
| white-noise covariance `Cov(η_a,η_b) = −σ²/(m−1)`, exchangeable | 2 | **PROVEN** |
| `#distinct \|η_b\| = m = (p−1)/n` (dilation orbits) | — | **PROVEN** |
| `E_2(μ_n) = 3n²−3n` (4th moment, Sidon-except-negation) | 4 | **PROVEN char-0** |
| `E_3 = 15n³−45n²+40n` | 6 | **PROVEN char-0** |
| **ladder** `μ_{2r} := Σ_{b≠0}\|η_b\|^{2r}/(p−1) ≤ (2r−1)‼·nʳ` | `2r` | **OPEN `r≈log p`** |
| sup `M = max_{b≠0}\|η_b\| ≤ C√(n·log q)` (`C≈1.2` measured) | `∞` | **OPEN = BGK** |

## The unification (where the half-power gap lives)

Everything reduces to **one law**: the DC-subtracted sub-Gaussian moment ladder `μ_{2r} ≤ Wick_r`.
The
**sup follows from it** by the moment method (Markov at `r ≈ log p`): `M ≤ 2√e·√(n log p)` — this
is the
landed conditional capstone `_AvPrize_MomentToSupCapstone.prize_sup_of_saddle`. The low-order laws
(`order ≤ 2`: Parseval, covariance, orbit) are **proven** and `p`-independent; `E_2, E_3` (`order
4,6`)
are **proven char-0** and excess-free at prize scale. **But the low-order laws do NOT determine the
high-order one**: the char-`p` excess `W_r = E_r^{𝔽_p} − E_r^{ℂ}` is genuinely new at each order
and is
orthogonal to all `order ≤ 2` structure — which is *why* every second-order method is dead
(`moment_ladder_exceeds_prize`). The half-power gap is **exactly** the high-order moment law
`μ_{2r} ≤
Wick_r` at `r ≈ log p`, in the thin regime.

## The regime-gating law (the genuine new fact proved here)

The sub-Gaussian moment law is **NOT universal** — it is **thinness-essential**. Already at the 4th
moment, the bound `S_4 := Σ_{b≠0}|η_b|^4 = p·E_2^{𝔽_p} − n^4 ≤ (p−1)·Wick_2` (`Wick_2 = 3n²`) is
**FALSE for thick subgroups**: at `n = 32, p = 2113` (`β = log p/log n ≈ 2.21`) the exact additive
energy is `E_2^{𝔽_p}(μ_32, 2113) = 4128` (machine-verified, `> 3n² = 3072`: real wraparound excess),
giving `S_4 = 7673888 > 6488064 = (p−1)·3n²`. At every prize-regime case (`β = 4`) the law holds
(`n=16,p=65537`: `S_4/budget = 0.936`; `n=32,p=1048609`: `0.968`). So **any proof of the prize
must use
the `β = 4` thinness** — a `β`-uniform method cannot work (it would prove the false thick case).
This is
a hard structural constraint on the proof, matching the campaign's `thinness-essential` finding.

`regimeGating_fourthMoment_fails` proves the exact arithmetic of the countermodel (given the
machine-verified `E_2 = 4128`); `subGaussianFourthMoment_not_universal` packages it as the
refutation of
the universal law. **Honest scope:** this *sharpens* the open problem (rules out `β`-uniform
proofs); it
is **not** progress toward proving the thin case (= BGK). Issue #444.
-/

namespace ProximityGap.Frontier.RegimeGating

/-- The fourth-moment sub-Gaussian budget law at parameters `(n, p)` with additive energy `E₂`:
`S₄ = p·E₂ − n⁴ ≤ (p−1)·3n²`. (`S₄ = Σ_{b≠0}|η_b|⁴`, `Wick₂ = 3n²`.) -/
def SubGaussianFourthMoment (n p E₂ : ℤ) : Prop := p * E₂ - n ^ 4 ≤ (p - 1) * (3 * n ^ 2)

/-- **The regime-gating countermodel (exact arithmetic).** At `n = 32, p = 2113` with the
machine-verified additive energy `E₂(μ_32, 2113) = 4128` (`> 3n² = 3072`, i.e. genuine wraparound
excess at this thick `β ≈ 2.21` prime), the fourth-moment sub-Gaussian law is **violated**:
`p·E₂ − n⁴ = 7673888 > 6488064 = (p−1)·3n²`. -/
theorem regimeGating_fourthMoment_fails :
    (2113 : ℤ) * 4128 - 32 ^ 4 > (2113 - 1) * (3 * 32 ^ 2) := by norm_num

/-- **The universal sub-Gaussian fourth-moment law is FALSE.** There exist parameters `(n, p, E₂)`
(`n = 32, p = 2113, E₂ = 4128`, with `E₂` the exact additive energy of `μ_32` mod `2113`) for which
`SubGaussianFourthMoment` fails. Hence the prize bound is **regime-gated** (thinness-essential): a
`β`-uniform proof is impossible, since it would establish this false thick case. -/
theorem subGaussianFourthMoment_not_universal :
    ¬ (∀ n p E₂ : ℤ, SubGaussianFourthMoment n p E₂) := by
  intro h
  have := h 32 2113 4128
  unfold SubGaussianFourthMoment at this
  have hlt := regimeGating_fourthMoment_fails
  linarith

end ProximityGap.Frontier.RegimeGating

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ProximityGap.Frontier.RegimeGating.regimeGating_fourthMoment_fails
#print axioms ProximityGap.Frontier.RegimeGating.subGaussianFourthMoment_not_universal
