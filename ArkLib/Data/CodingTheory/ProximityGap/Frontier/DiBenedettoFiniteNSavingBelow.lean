/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
Co-authored-by: wakesync <shadow@shad0w.xyz>
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DiBenedettoEnergyValueEnvelope
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# di Benedetto near-Sidon saving: the FINITE-`n` shortfall is STRICT (#444 — constant-factor lane)

`_DiBenedettoNearSidonImprovement.lean` proves the saving formula
`diBenedettoSaving t₂ t₃ = (10 − 2·t₃ − t₂/2)/72`, its near-Sidon value `diBenedettoSaving 2 3 = 1/24`,
its antitone monotonicity, the `1/24` ceiling (`diBenedettoSaving_le_ceiling`, the `≤` side under
`2 ≤ t₂`, `3 ≤ t₃`), and the CONDITIONAL improvement `charSum_le_of_nearSidon` — which consumes the
IDEALISED hypotheses `t₂ ≤ 2`, `t₃ ≤ 3`.

`_DiBenedettoEnergyValueEnvelope.lean` then records (in its docstring, **as prose, never as a theorem**)
the honest correction: the dyadic subgroup's EXACT char-0 energies
`E₂(n) = 3n²−3n`, `E₃(n) = 15n³−45n²+40n` have leading constants `> 1`, so the **realised** log-exponents
`t_k(n) := logb n (E_k(n))` are STRICTLY ABOVE the integer `k` at every finite `n`
(`t₂: 2.585 @ n=4 → 2.05 @ n=2³⁰`; `t₃: 4.32 @ n=4 → 3.13 @ n=2³⁰`). Hence the idealised hypothesis
`t_k ≤ k` is NEVER literally met at any finite `n`, and (the prose claims) "the realised saving
approaches `1/24` strictly from BELOW". **That last clause is asserted, never landed.**

This file discharges it. The realised energies STRICTLY exceed the Sidon floor `n^k`
(`n² < E₂(n)` for `n ≥ 2`, `n³ < E₃(n)` for `n ≥ 1` — both already in the envelope file's lower bands,
here re-derived strictly), so the realised exponents satisfy `t_k(n) > k` STRICTLY, and the saving is
antitone-with-a-STRICT-decrease ⟹ `diBenedettoSaving (t₂(n)) (t₃(n)) < 1/24` STRICTLY at every finite
`n ≥ 2`. The near-Sidon idealisation `1/24` is the SUPREMUM, attained only in the `n → ∞` limit
(`t_k(n) → k`), never at any finite scale.

## Probe (ONE sweep — `scripts/probes/probe_dibenedetto_finite_n_saving.py`, `n = 2²..2³⁰`)
On the exact char-0 closed forms (p-independent; never `n = q−1`):
- (A) `t₂(n) > 2` and `t₃(n) > 3` STRICTLY: 0 fails / 29.
- (B) `diBenedettoSaving (t₂(n)) (t₃(n)) < 1/24` STRICTLY: 0 fails / 29.
- (C) saving `→ 1/24` (gap still `3.98e−3` at `n = 2³⁰` — the convergence is `O(1/log n)`, slow).
- (D) saving MONOTONE INCREASING in `n` (each octave gets closer to `1/24` from below).

## HONESTY (rules 1, 3, 6 + ASYMPTOTIC GUARD)
NOT a CORE closure. This is the STRICT finite-`n` companion of the proven `_le_ceiling`: it pins that
the energy-method's own best constant-factor saving `1/24` is UNREACHED at every finite scale — a
NEGATIVE/boundary sharpening, tightening the honest reach of the di Benedetto near-Sidon route. It is
exponent bookkeeping over `ℝ` on the proven exact-value envelope; FIELD-UNIVERSAL (the saving formula
is thickness-blind — its prize-relevance is ONLY through the dyadic energy VALUES, which the envelope
file already supplies). NOT a moment/census/orbit/pencil/resonance object; touches NEITHER `δ*` NOR the
cliff-at-`n/2` incidence object; makes NO capacity / beyond-Johnson / growth-law claim; does NOT push
past the proven `1/24` ceiling (it shows the ceiling is a strict supremum, not attained). The energy
method stays provably `12×` short of the prize cancellation exponent `1/2`. ONE sweep, ONE commit.
CORE `M(μ_n) ≤ C·√(n·log(p/n))` UNCHANGED / OPEN. Issue #444.
-/

set_option autoImplicit false
set_option linter.style.longLine false


open Real

namespace ProximityGap.Frontier.DiBenedettoNearSidon

/-- **Strict-antitone saving (first argument).** If `t₂' < t₂` (a strict DECREASE in the depth-2
exponent), the di Benedetto saving strictly increases: `diBenedettoSaving t₂ t₃ < diBenedettoSaving t₂' t₃`.
The formula is affine with negative slope `−1/144` in `t₂`. -/
theorem diBenedettoSaving_strictAntitone_fst {t₂ t₂' t₃ : ℝ} (h : t₂' < t₂) :
    diBenedettoSaving t₂ t₃ < diBenedettoSaving t₂' t₃ := by
  unfold diBenedettoSaving; linarith

/-- **Strict-antitone saving (second argument).** If `t₃' < t₃`, the saving strictly increases
(negative slope `−2/72 = −1/36` in `t₃`). -/
theorem diBenedettoSaving_strictAntitone_snd {t₂ t₃ t₃' : ℝ} (h : t₃' < t₃) :
    diBenedettoSaving t₂ t₃ < diBenedettoSaving t₂ t₃' := by
  unfold diBenedettoSaving; linarith

/-- **Strict ceiling under a strict lower exponent.** If `2 ≤ t₂` and `3 < t₃` (the depth-3 exponent
strictly exceeds the Sidon value `3`), the saving is STRICTLY below the near-Sidon `1/24`.
This is the strict version of `diBenedettoSaving_le_ceiling`. -/
theorem diBenedettoSaving_lt_ceiling_of_t₃ {t₂ t₃ : ℝ} (h₂ : 2 ≤ t₂) (h₃ : 3 < t₃) :
    diBenedettoSaving t₂ t₃ < 1 / 24 := by
  unfold diBenedettoSaving; linarith

/-- **Strict ceiling under a strict depth-2 lower exponent.** Symmetric: `2 < t₂`, `3 ≤ t₃` ⟹ strict. -/
theorem diBenedettoSaving_lt_ceiling_of_t₂ {t₂ t₃ : ℝ} (h₂ : 2 < t₂) (h₃ : 3 ≤ t₃) :
    diBenedettoSaving t₂ t₃ < 1 / 24 := by
  unfold diBenedettoSaving; linarith

/-! ## The realised log-exponents of the dyadic subgroup exceed the integer order, strictly -/

/-- The realised depth-`k` log-exponent of `μ_n` at the energy `E`: `t_k(n) = logb n (E n)`
(`= log (E n) / log n`), the exponent such that `E n = n ^ {t_k(n)}`. -/
noncomputable def realisedExp (E : ℝ → ℝ) (n : ℝ) : ℝ := Real.logb n (E n)

/-- **The realised depth-2 exponent strictly exceeds `2`** for every finite `n ≥ 2`.
Because `E₂(n) = 3n²−3n > n²` (strict, `n ≥ 2`: `3n²−3n − n² = n(2n−3) > 0`), so
`logb n (E₂ n) > logb n (n²) = 2`. The idealised hypothesis `t₂ ≤ 2` is NEVER met at finite `n`. -/
theorem realisedExp_two_gt {n : ℝ} (hn : 2 ≤ n) : (2 : ℝ) < realisedExp energyTwo n := by
  have h1n : (1 : ℝ) < n := by linarith
  have hn0 : (0 : ℝ) < n := by linarith
  -- strict Sidon-floor excess n² < E₂(n)
  have hgt : (n : ℝ) ^ 2 < energyTwo n := by unfold energyTwo; nlinarith [hn]
  -- rewrite n^2 as the rpow n^(2:ℝ) so we can use lt_logb_iff_rpow_lt
  have hrp : (n : ℝ) ^ (2 : ℝ) = (n : ℝ) ^ (2 : ℕ) := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  -- 2 < logb n (E₂ n)  ↔  n ^ (2:ℝ) < E₂ n
  rw [realisedExp, Real.lt_logb_iff_rpow_lt h1n (by linarith [hgt, sq_nonneg n] : (0:ℝ) < energyTwo n)]
  rw [hrp]; simpa using hgt

/-- **The realised depth-3 exponent strictly exceeds `3`** for every finite `n ≥ 2`.
Because `E₃(n) = 15n³−45n²+40n > n³` (strict; `E₃ − n³ = n(14n²−45n+40)` with discriminant `−215 < 0`,
so the quadratic is positive everywhere ⟹ `> 0` strictly for `n ≥ 1`). So `t₃(n) = logb n (E₃ n) > 3`.
The idealised hypothesis `t₃ ≤ 3` is NEVER met at finite `n`. -/
theorem realisedExp_three_gt {n : ℝ} (hn : 2 ≤ n) : (3 : ℝ) < realisedExp energyThree n := by
  have h1n : (1 : ℝ) < n := by linarith
  have hn0 : (0 : ℝ) < n := by linarith
  -- strict Sidon-floor excess n³ < E₃(n); E₃ − n³ = n(14n²−45n+40), 14n²−45n+40 > 0 (disc −215)
  have hgt : (n : ℝ) ^ 3 < energyThree n := by
    unfold energyThree; nlinarith [hn, sq_nonneg (n - 2), sq_nonneg n]
  have hpos : (0 : ℝ) < energyThree n := lt_trans (by positivity) hgt
  have hrp : (n : ℝ) ^ (3 : ℝ) = (n : ℝ) ^ (3 : ℕ) := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [realisedExp, Real.lt_logb_iff_rpow_lt h1n hpos]
  rw [hrp]; simpa using hgt

/-! ## HEADLINE: the realised finite-`n` saving is STRICTLY below the near-Sidon `1/24` -/

/-- **HEADLINE — the di Benedetto near-Sidon saving `1/24` is UNREACHED at every finite `n`.**
Feeding the dyadic subgroup's TRUE realised log-exponents `t₂(n) = logb n (E₂ n)`,
`t₃(n) = logb n (E₃ n)` (both STRICTLY above `2, 3` at every finite `n ≥ 2`) into the saving formula:

  `diBenedettoSaving (realisedExp energyTwo n) (realisedExp energyThree n) < 1/24`.

So the near-Sidon idealisation `1/24` is the SUPREMUM of the realised saving, attained only as `n → ∞`
(`t_k(n) → k`), never at any finite scale. This is the STRICT finite-`n` companion of the proven
`diBenedettoSaving_le_ceiling`: the energy method's own best constant-factor saving is a strict
supremum, never met. (The full poly-vs-`1/2` shortfall is `energy_method_below_prize`.) -/
theorem realisedSaving_lt_nearSidon {n : ℝ} (hn : 2 ≤ n) :
    diBenedettoSaving (realisedExp energyTwo n) (realisedExp energyThree n) < 1 / 24 := by
  have h₂ : (2 : ℝ) < realisedExp energyTwo n := realisedExp_two_gt hn
  have h₃ : (3 : ℝ) < realisedExp energyThree n := realisedExp_three_gt hn
  exact diBenedettoSaving_lt_ceiling_of_t₂ h₂ (le_of_lt h₃)

/-- **The realised saving is bounded away from the prize by the same `1/24`-vs-`1/2` margin, strictly.**
Combines the headline with the (proven-parent) ceiling: the realised finite-`n` saving is `< 1/24 < 1/2`,
so the dyadic di Benedetto route is STRICTLY sub-`1/24` AND `12×` short of the prize cancellation
exponent at every finite scale. -/
theorem realisedSaving_below_prize {n : ℝ} (hn : 2 ≤ n) :
    diBenedettoSaving (realisedExp energyTwo n) (realisedExp energyThree n) < 1 / 2 := by
  have := realisedSaving_lt_nearSidon hn; linarith

end ProximityGap.Frontier.DiBenedettoNearSidon

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.DiBenedettoNearSidon.realisedExp_two_gt
#print axioms ProximityGap.Frontier.DiBenedettoNearSidon.realisedExp_three_gt
#print axioms ProximityGap.Frontier.DiBenedettoNearSidon.realisedSaving_lt_nearSidon
#print axioms ProximityGap.Frontier.DiBenedettoNearSidon.realisedSaving_below_prize
