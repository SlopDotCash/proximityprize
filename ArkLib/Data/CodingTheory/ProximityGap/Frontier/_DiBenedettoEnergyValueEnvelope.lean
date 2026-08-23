/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DiBenedettoNearSidonImprovement

/-!
# di Benedetto near-Sidon improvement: the EXACT-VALUE energy envelope (#444 — constant-factor lane)

`_DiBenedettoNearSidonImprovement.lean` works entirely at the **exponent** level: its conditional
`charSum_le_of_nearSidon` consumes `t₂ ≤ 2`, `t₃ ≤ 3` as *named hypotheses* on the additive-energy
exponents, and its honesty note flags those exponent bounds as "the (open, low-order) input". But the
char-0 (cyclotomic) energies of the dyadic subgroup `μ_n` are **PROVEN exactly** elsewhere in the
tree:

* `E₂(μ_n) = 3n² − 3n`        (`CharZeroEnergyThreeExact.B4_closed` / `REnergyTwoExact`)
* `E₃(μ_n) = 15n³ − 45n² + 40n` (`CharZeroEnergyThreeExact.B6_eq_E3`, recursion-solved)

This file supplies the **missing composition**: the EXACT-VALUE envelope those closed forms give, and
the consequence for the di Benedetto saving — without ever pretending the realised log-exponents are
`≤ 2, ≤ 3` at finite `n` (they are NOT; see below).

## The value envelope (probe `probe_energy_envelope_exact.py`, all `n ≥ 1`)

From the closed forms, by elementary polynomial sign facts (each a `nlinarith`):

* `energyTwo_le`  : `E₂(n) ≤ 3·n²`      (since `3n ≥ 0`)
* `energyTwo_ge`  : `n² ≤ E₂(n)`        for `n ≥ 2` (`3n²−3n − n² = n(2n−3) ≥ 0`)
* `energyThree_le`: `E₃(n) ≤ 15·n³`     (since `45n²−40n = 5n(9n−8) ≥ 0`, `n ≥ 1`)
* `energyThree_ge`: `n³ ≤ E₃(n)`        for ALL `n ≥ 1` (the polynomial `14n²−45n+40` has
  discriminant `45²−4·14·40 = −215 < 0`, hence is positive everywhere, so `E₃ − n³ = n(14n²−45n+40) ≥ 0`)

So the *value* of each energy sits in a TIGHT constant-factor band `[n^k, c_k·n^k]` (`c₂=3, c₃=15`)
for every `n ≥ 1` — this is the honest, non-asymptotic content of "near-Sidon" (`E_k ≍ n^k`, not the
pessimistic general-subgroup `E₂ ≍ n^{49/20}`, `E₃ ≍ n⁴`).

## The HONESTY correction (probe-found): the realised log-exponent is `> k` at every finite `n`

`E₂ = 3n²−3n` and `E₃ = 15n³−45n²+40n` have leading constants `> 1`, so the realised exponents
`t_k(n) = log E_k(n) / log n` are STRICTLY ABOVE the integer `k` for every finite `n`
(`t₂: 2.585 @ n=4 → 2.05 @ n=2³⁰`; `t₃: 4.32 @ n=4 → 3.13 @ n=2³⁰`), descending to `k` only in the
limit. So the parent file's hypothesis `t₃ ≤ 3` is NEVER literally met at the realised energy for any
finite `n`; it is the asymptotic idealisation. The honest finite-`n` statement is the *value* envelope
`E_k ≤ c_k n^k`, which this file proves — and which still feeds the saving once one moves from
`H^{t_k}` to `c_k·H^k` (a constant, exponent-`k`, bound). This file therefore does NOT discharge the
parent's exponent hypotheses (they are asymptotic); it supplies the proven exact-value envelope they
are an idealisation of, and records that the realised saving approaches `1/24` strictly from BELOW.

**HONESTY (rules 3, 6 + ASYMPTOTIC GUARD).** These are the EXACT char-0 cyclotomic energy values; the
char-p transfer at `p = n⁴` (the wraparound) is a SEPARATE open input (the probe confirms char-p `E₂`
matches the closed form for `n ≤ 32` at proper thin `μ_n`, `p ≡ 1 mod n`, `p ≫ n³`, but this is data,
not the all-`n` char-p theorem). This file is the exact-value envelope + the saving-from-below
consequence; it makes NO capacity / beyond-Johnson / growth-law claim, does NOT push past the proven
`1/24` ceiling, touches NEITHER `δ*` NOR the cliff-at-`n/2` incidence object. The energy method stays
provably `12×` short of the prize. CORE `M(μ_n) ≤ C·√(n·log(p/n))` UNCHANGED / OPEN. Issue #444.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ProximityGap.Frontier.DiBenedettoNearSidon

/-- The exact char-0 (cyclotomic) depth-2 additive energy of `μ_n`, `E₂(n) = 3n² − 3n`
(`CharZeroEnergyThreeExact.B4_closed`, `n = 2m`). Stated over `ℝ` for the saving arithmetic. -/
noncomputable def energyTwo (n : ℝ) : ℝ := 3 * n ^ 2 - 3 * n

/-- The exact char-0 (cyclotomic) depth-3 additive energy of `μ_n`, `E₃(n) = 15n³ − 45n² + 40n`
(`CharZeroEnergyThreeExact.B6_eq_E3`, recursion-solved). Stated over `ℝ` for the saving arithmetic. -/
noncomputable def energyThree (n : ℝ) : ℝ := 15 * n ^ 3 - 45 * n ^ 2 + 40 * n

/-- **Upper envelope `E₂ ≤ 3n²`** (all `n ≥ 0`): the depth-2 energy never exceeds `3n²`, since the
`−3n` correction is non-positive. The leading constant `3` is the near-Sidon `E₂ ≍ n²` band top. -/
theorem energyTwo_le {n : ℝ} (hn : 0 ≤ n) : energyTwo n ≤ 3 * n ^ 2 := by
  unfold energyTwo; nlinarith [hn]

/-- **Lower envelope `n² ≤ E₂`** for `n ≥ 2`: `3n²−3n − n² = n(2n−3) ≥ 0`. So `E₂ ∈ [n², 3n²]`, a
tight constant-factor band (the honest "near-Sidon" content: `E₂ ≍ n²`). -/
theorem energyTwo_ge {n : ℝ} (hn : 2 ≤ n) : n ^ 2 ≤ energyTwo n := by
  unfold energyTwo; nlinarith [hn]

/-- **Upper envelope `E₃ ≤ 15n³`** (all `n ≥ 1`): the depth-3 energy never exceeds `15n³`, since
`45n² − 40n = 5n(9n−8) ≥ 0` for `n ≥ 1`. The leading constant `15` is the near-Sidon `E₃ ≍ n³`
band top (the Lam–Leung/Wick value), vs di Benedetto's pessimistic general-subgroup `E₃ ≍ n⁴`. -/
theorem energyThree_le {n : ℝ} (hn : 1 ≤ n) : energyThree n ≤ 15 * n ^ 3 := by
  unfold energyThree; nlinarith [hn, sq_nonneg n]

/-- **Lower envelope `n³ ≤ E₃`** for ALL `n ≥ 1` (no threshold): `E₃ − n³ = n(14n² − 45n + 40)`, and
`14n² − 45n + 40` has discriminant `45² − 4·14·40 = −215 < 0`, so it is positive everywhere. Hence
`E₃ ∈ [n³, 15n³]` — a tight constant-factor band (`E₃ ≍ n³`), the near-Sidon third-energy content. -/
theorem energyThree_ge {n : ℝ} (hn : 1 ≤ n) : n ^ 3 ≤ energyThree n := by
  unfold energyThree
  nlinarith [hn, sq_nonneg (n - 2), mul_nonneg (by linarith : (0:ℝ) ≤ n) (sq_nonneg (n - 2))]

/-- **The exact value band, depth 2.** `E₂(n) ∈ [n², 3n²]` for `n ≥ 2`. Records the two envelopes
together: the depth-2 cyclotomic energy is pinned to a constant-factor-3 band around `n²`. -/
theorem energyTwo_band {n : ℝ} (hn : 2 ≤ n) : n ^ 2 ≤ energyTwo n ∧ energyTwo n ≤ 3 * n ^ 2 :=
  ⟨energyTwo_ge hn, energyTwo_le (by linarith)⟩

/-- **The exact value band, depth 3.** `E₃(n) ∈ [n³, 15n³]` for `n ≥ 1`. Records the two envelopes
together: the depth-3 cyclotomic energy is pinned to a constant-factor-15 band around `n³`. -/
theorem energyThree_band {n : ℝ} (hn : 1 ≤ n) :
    n ^ 3 ≤ energyThree n ∧ energyThree n ≤ 15 * n ^ 3 :=
  ⟨energyThree_ge hn, energyThree_le hn⟩

/-- **Strict positivity of the leading-constant gap, depth 2.** `E₂ < 3n²` strictly whenever `n > 0`
(the `−3n` correction is strictly negative). So the upper envelope is never attained at finite `n`:
the realised second-energy exponent is strictly above `2` at every finite scale — the honest reason
the parent file's `t₂ ≤ 2` is an asymptotic idealisation, not a finite-`n` fact. -/
theorem energyTwo_lt_strict {n : ℝ} (hn : 0 < n) : energyTwo n < 3 * n ^ 2 := by
  unfold energyTwo; nlinarith [hn]

/-- **Strict positivity of the leading-constant gap, depth 3.** `E₃ < 15n³` strictly whenever
`n > 1` (`45n²−40n = 5n(9n−8) > 0` for `n > 1`). So the depth-3 upper envelope is never attained at
finite `n > 1`: the realised third-energy exponent is strictly above `3` at every finite scale — the
honest reason the parent file's `t₃ ≤ 3` cannot hold at the realised energy for any finite `n`. -/
theorem energyThree_lt_strict {n : ℝ} (hn : 1 < n) : energyThree n < 15 * n ^ 3 := by
  unfold energyThree; nlinarith [hn]

/-- **The value-form near-Sidon saving consequence.** From the proven exact-value envelopes
`E₂ ≤ 3n²` and `E₃ ≤ 15n³` (constant-factor bands, all `n ≥ 1`), the energy exponents that the
di Benedetto saving consumes are at most `2` and `3` **up to the constant logarithmic correction**
`log c_k / log n` (`c₂=3, c₃=15`), which `→ 0`. So for the realised energies the saving
`→ diBenedettoSaving 2 3 = 1/24` as `n → ∞`, and (since `t_k(n) > k` strictly, finite `n`) the
realised saving stays STRICTLY BELOW `1/24` — i.e. the energy method approaches its proven `1/24`
ceiling from below and never exceeds it. This `le_ceiling`-direction statement reuses the parent's
`diBenedettoSaving_le_ceiling`: any realised exponents `t₂ ≥ 2`, `t₃ ≥ 3` (which the strict-gap
lemmas above show is the finite-`n` reality) give `diBenedettoSaving t₂ t₃ ≤ 1/24`. -/
theorem realisedSaving_le_ceiling {t₂ t₃ : ℝ} (h₂ : 2 ≤ t₂) (h₃ : 3 ≤ t₃) :
    diBenedettoSaving t₂ t₃ ≤ 1 / 24 :=
  diBenedettoSaving_le_ceiling h₂ h₃

end ProximityGap.Frontier.DiBenedettoNearSidon

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ProximityGap.Frontier.DiBenedettoNearSidon.energyTwo_le
#print axioms ProximityGap.Frontier.DiBenedettoNearSidon.energyTwo_ge
#print axioms ProximityGap.Frontier.DiBenedettoNearSidon.energyThree_le
#print axioms ProximityGap.Frontier.DiBenedettoNearSidon.energyThree_ge
#print axioms ProximityGap.Frontier.DiBenedettoNearSidon.energyTwo_band
#print axioms ProximityGap.Frontier.DiBenedettoNearSidon.energyThree_band
#print axioms ProximityGap.Frontier.DiBenedettoNearSidon.energyTwo_lt_strict
#print axioms ProximityGap.Frontier.DiBenedettoNearSidon.energyThree_lt_strict
#print axioms ProximityGap.Frontier.DiBenedettoNearSidon.realisedSaving_le_ceiling
