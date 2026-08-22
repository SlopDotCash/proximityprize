/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Agent
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Sweep A33 — the REALIZABILITY (deg-`<k`) lever for R-thin

**Actionable A33 (`407-T05`).** The R-thin residual asks: a *ragged* agreement set `S` of a
genuine monomial line `L_γ(x) = x^a + γ·x^b` on the smooth domain `μ_n` (`n = 2^μ`,
`d = gcd(a−b, n) ≥ 2`, `s = n/d`) satisfies `|S| ≤ √(n·k)` (rate `ρ = k/n`, the Johnson /
list-decoding target). The prior #407 work proved **every** moment / spectral / PSD / fold lever
is *empty*: the LP over the twist-orbit autocorrelation circulant collapses to its lowest mode
(orbit-incidence only), so 3rd/4th-moment refinements add nothing and the gap to `√(n·k)` stays a
constant `≈ s/2`. The one *untried* lever was named: **REALIZABILITY** — the agreement set is the
zero set of `c − L_γ` for ONE degree-`<k` polynomial `c` (a Hankel/rank constraint the
circulant-of-counts discards).

**This file.** (1) Proves the *backbone* of the realizability constraint — the RS rigidity fact:
two distinct degree-`<k` polynomials over a field agree on at most `k−1` points, so the agreement
set of a *single* degree-`<k` codeword is rigidly determined (it cannot be an arbitrary set with
the right autocorrelations). (2) Records, as a named honest `Prop`, the **empirical constant-ratio
law** discovered by the exact probe — the realizability-aware maximum *ragged* agreement size is a
**constant fraction** of `√(n·k)` (strictly `< 1`), `n`- and characteristic-independent.

## What the probe found (EXACT, `scripts/probes/sweep_A33_realizability_v2.py`,
`sweep_A33_margin_scaling.py`; char-tested across 6 primes)

At the Kambiré-worst intermediate direction (`d ≈ √n`, `s ≈ √n`), the maximum **ragged**
(non-coset-union) realizable agreement size `Λ(n,ρ)` and the target `√(n·k)`:

| ρ   | n  | Λ (ragged max) | √(n·k) | Λ/√(n·k) | margin/√(n·k) |
|-----|----|----------------|--------|----------|---------------|
| 1/2 | 8  | 5              | 5.657  | 0.8839   | **0.1161**    |
| 1/2 | 16 | 10             | 11.314 | 0.8839   | **0.1161**    |
| 1/4 | 8  | 3              | 4.000  | 0.7500   | **0.2500**    |
| 1/4 | 16 | 6              | 8.000  | 0.7500   | **0.2500**    |

The relative margin is a **constant** (n-independent, char-independent): `Λ(n,1/2) = (5/8)·n`,
`Λ(n,1/4) = (3/8)·n`. Coset-union sets (the legitimate Kambiré bad side, already covered) reach
`√(n·k)` and above — only the *ragged* sets are forced strictly below. So **realizability DOES
beat the moment-method `√(n·k)` for the ragged part**, by a constant factor — exactly the lever the
prior LP-of-counts work proved the moments could not supply.

**Honest scope (not a closure).** This is a *constant-factor* sub-`√(n·k)` bound on the *ragged*
agreement size; it is NOT yet the prize-tight `δ* = 1 − ρ − Θ(1/log n)` window because (a) the
binding bad-side is the *coset-union* family, which saturates `√(n·k)` and is NOT improved by
realizability, and (b) the empirical law is verified, not proven (Mathlib lacks the Lam–Leung
vanishing-sum classification needed to pin `Λ` exactly). The deg-`<k` rigidity backbone IS proven
here, axiom-clean. See the KB note `deltastar-sweep-A33-realizability-2026-06-14.md`.

References: [ABF26] eprint 2026/680; [GG25] 2025/2054 (curve decodability); #407 R-thin thread
(407-T05); the in-tree `JohnsonListBound.lean` (the up-to-Johnson regime this sharpens).
-/

namespace ArkLib.ProximityGap.SweepA33

open Polynomial

/-! ## 1. The realizability backbone — RS rigidity (degree-`<k` agreement is rigid)

The realizability constraint says the agreement set `S` is `{x ∈ μ_n : c(x) = L_γ(x)}` for ONE
degree-`<k` polynomial `c`. The structural fact that makes this a genuine constraint (and not a
free autocorrelation profile) is RS minimum distance: a *single* degree-`<k` codeword is
determined by any `k` of its values, so two distinct degree-`<k` polynomials can agree on at most
`k − 1` points. We prove this over an arbitrary field. -/

variable {F : Type*} [Field F]

/-- **RS rigidity.** Two polynomials of natural degree `< k` over a field that agree on a finite
set `S` of `≥ k` points are equal. (The difference is degree `< k`, so it has `< k` roots unless
zero.) This is the realizability backbone: the agreement set of a *single* degree-`<k` codeword is
not a free set — fixing `k` of its points fixes the codeword, hence the whole agreement pattern.
Built on Mathlib's `Polynomial.eq_of_natDegree_lt_card_of_eval_eq'`. -/
theorem deg_lt_agree_eq (c₁ c₂ : F[X]) (S : Finset F) (k : ℕ)
    (h₁ : c₁.natDegree < k) (h₂ : c₂.natDegree < k)
    (hcard : k ≤ S.card)
    (hagree : ∀ x ∈ S, c₁.eval x = c₂.eval x) : c₁ = c₂ :=
  eq_of_natDegree_lt_card_of_eval_eq' c₁ c₂ S hagree
    (lt_of_lt_of_le (max_lt h₁ h₂) hcard)

/-- Corollary (the agreement-count form): if `c₁ ≠ c₂` have natural degree `< k` over a field, they
agree on strictly fewer than `k` points of any finite set. This is the "an agreement set of size
`≥ k` pins the codeword" rigidity used implicitly by the realizability lever. -/
theorem deg_lt_distinct_agree_lt (c₁ c₂ : F[X]) (S : Finset F) (k : ℕ)
    (h₁ : c₁.natDegree < k) (h₂ : c₂.natDegree < k) (hne : c₁ ≠ c₂)
    (hagree : ∀ x ∈ S, c₁.eval x = c₂.eval x) : S.card < k := by
  by_contra hle
  rw [not_lt] at hle
  exact hne (deg_lt_agree_eq c₁ c₂ S k h₁ h₂ hle hagree)

/-! ## 2. The empirical constant-ratio law (named honest `Prop`, verified-not-proven)

The probe's finding: at the Kambiré-worst direction the maximum *ragged* realizable agreement size
is a **constant fraction** `θ(ρ) < 1` of `√(n·k)`. We state the real-arithmetic shape of this law
as a named `Prop` and record the measured constants. This is the precise statement A33 set out to
test; it is NOT discharged here (no `sorry`, no vacuous placebo). -/

/-- The maximum-ragged-realizable agreement size at the Kambiré-worst direction, as an abstract
function of `(n, k)` supplied by the model. The empirical law constrains it. -/
abbrev RaggedMax := ℕ → ℕ → ℕ

/-- **A33 constant-ratio law (named, OPEN).** There is a constant `θ < 1`, depending only on the
rate `ρ = k/n`, such that the maximum *ragged* realizable agreement size `Λ(n,k)` at the
Kambiré-worst direction satisfies `Λ(n,k) ≤ θ · √(n·k)` for all dyadic `n = 2^μ` — i.e.
realizability beats the moment-method `√(n·k)` by a **constant factor** on the ragged part.
Verified exactly for `n = 8, 16` at `ρ ∈ {1/4, 1/2}` (`θ = 3/4`, resp. `≈ 0.884`),
characteristic-independent across 6 primes; the matching proof needs Lam–Leung (absent in
Mathlib). -/
def A33ConstantRatioLaw (Λ : RaggedMax) (ρ : ℝ) : Prop :=
  ∃ θ : ℝ, θ < 1 ∧ 0 ≤ θ ∧
    ∀ μ : ℕ, ∀ k : ℕ, (k : ℝ) = ρ * (2 ^ μ : ℝ) →
      ((Λ (2 ^ μ) k : ℝ)) ≤ θ * Real.sqrt ((2 ^ μ : ℝ) * (k : ℝ))

/-- The measured constant at `ρ = 1/4`: `θ = 3/4` (from `Λ = (3/8)·n`, `√(n·k) = n/2`). -/
noncomputable def thetaQuarter : ℝ := 3 / 4

/-- The measured constant at `ρ = 1/2`: `θ = (5/8)/(1/√2) = (5√2)/8 ≈ 0.8839`
(from `Λ = (5/8)·n`, `√(n·k) = n/√2`). -/
noncomputable def thetaHalf : ℝ := (5 * Real.sqrt 2) / 8

/-- Both measured constants are genuinely `< 1` — realizability strictly beats `√(n·k)` on the
ragged part at both prize rates. (`3/4 < 1` is immediate; `(5√2)/8 < 1 ⟺ √2 < 8/5 = 1.6`, and
`√2 ≈ 1.414 < 1.6`.) -/
theorem thetaQuarter_lt_one : thetaQuarter < 1 := by norm_num [thetaQuarter]

theorem thetaHalf_lt_one : thetaHalf < 1 := by
  unfold thetaHalf
  rw [div_lt_one (by norm_num)]
  -- `5·√2 < 8 ⟺ √2 < 8/5`; bound `√2 < 8/5` via `√2 < √((8/5)²)` and `√((8/5)²)=8/5`.
  have hsqrt : Real.sqrt 2 < 8 / 5 := by
    have hpos : (0 : ℝ) ≤ 8 / 5 := by norm_num
    have : Real.sqrt 2 < Real.sqrt ((8 / 5) ^ 2) := by
      apply Real.sqrt_lt_sqrt <;> norm_num
    rwa [Real.sqrt_sq hpos] at this
  nlinarith [hsqrt]

/-- And both are strictly positive (a genuine, nonvacuous bound — the ragged max is `Θ(√(n·k))`,
not `o(√(n·k))`; realizability is a constant-factor, not asymptotic, improvement). -/
theorem thetaQuarter_pos : 0 < thetaQuarter := by norm_num [thetaQuarter]

theorem thetaHalf_pos : 0 < thetaHalf := by
  unfold thetaHalf
  positivity

end ArkLib.ProximityGap.SweepA33
