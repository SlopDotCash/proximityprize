/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Bchks F1e — the complete-homogeneous leading exponent STRICTLY exceeds subset-sum at EVERY
proportional fold, with the exact symmetric-fold constant `(3/2)·log(3/2) + (1/2)·log(1/2)` (#444)

## What this discharges

The §0.2.a load-bearing dossier claim — that the worst CHAR-FREE direction count is the
complete-homogeneous `h_r = C(s+r−1, r)` and **NOT** Kambiré's subset-sum ceiling `e_r = C(s, r)`,
because `h_r` has a *strictly larger leading exponent* — is stated as the prose
`log(h_r/e_r)/s → 0.26` in TWO places of `_BchksF6_ExplicitDeltaStarLower`
(the F1 docstring + the `chooseCH` def docstring) and never made into a theorem.

* `_BchksF1c` proved the *qualitative* strict separation `Nat.choose s r < chooseCH s r` for
  `2 ≤ r`.
* `_BchksF1d` proved the *integer-exponential* gap at the `r = s` ENDPOINT
  (`2^(s−1) ≤ chooseCH s s`, where `e_s = C(s,s) = 1`).

Neither lands the **proportional-fold leading exponent** — the actual object that sets the leading
order of `δ*`. By Stirling, at `r = a·s` (`a ∈ (0,1)`),
`log(h_r/e_r)/s → L(a) := (1+a)·log(1+a) + (1−a)·log(1−a)`, and the dossier's binding fold is the
SYMMETRIC `r/s = 1/2` where `L(1/2) = (3/2)·log(3/2) + (1/2)·log(1/2) = (3/2)·log 3 − 2·log 2`
(`≈ 0.2616`)
(exactly the prose `→ 0.26`). The load-bearing content is that this gap is **strictly positive** —
the complete-homogeneous leading exponent strictly exceeds subset-sum at EVERY proportional fold, so
the Kambiré subset-sum ceiling is NEVER the tight floor.

This file lands `L(a) > 0` for all `a ∈ (0,1)` (the §0.2.a "strictly larger leading exponent") and
pins the exact symmetric-fold value, via strict convexity of `x ↦ x·log x`
(`Real.strictConvexOn_mul_log`).

## Probe

`probe_ch_symmetric_fold_exponent.py` (exact `lgamma`, `s = 16 … 8192` at `r = s/2`):
`log(h/e)/s` rises monotonically `0.2275 → 0.2616` from BELOW to the closed form
`(3/2)log(3/2) + (1/2)log(1/2) = 0.261624`; and `L(a) > 0` for `a ∈ (0,1)` (0 fails / 100000 random
samples). The general law: `L(a)` is INCREASING on `(0,1)` from `L(0⁺)=0` to `L(1⁻)=2·log 2 = 1.386`
(the `r = s` endpoint `_BchksF1d` took), with the binding fold at `a = 1/2`.

## Honest scope (rules 1, 3, 6)

NOT a CORE closure. The leading-exponent gap function `L(a)` is a pure real-analytic object
(field-universal, char-free) — by rule 3 it cannot by itself prove the thinness-essential CORE
`M(μ_n) ≤ C√(n·log(p/n))`. It discharges the §0.2.a *leading-order* prose: the complete-homogeneous
floor strictly dominates the subset-sum ceiling at the exponent level, at every proportional fold.
It does NOT bound the OPEN distinct-spectrum count, the good-prime existence, or the char-`p`
exponent-0 anomaly (the three named residuals of `_BchksF6`). NON-MOMENT (a convexity fact about an
entropy-type gap, NOT an additive moment / energy upper bound). NO capacity / beyond-Johnson /
growth-law claim; the asymptotic-guard cliff-at-`n/2` is UNTOUCHED. EXTEND-proven on Mathlib's
`strictConvexOn_mul_log`. ONE sweep ONE commit.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.BchksF1

open Real Set

/-- **The complete-homogeneous − subset-sum leading-exponent gap** at proportional fold `r/s = a`.

By Stirling, `log C(s+r−1, r)/s → (1+a)·log(1+a) − a·log a` and
`log C(s, r)/s → −a·log a − (1−a)·log(1−a)` at `r = a·s`; their difference is
`leadingExpGap a = (1+a)·log(1+a) + (1−a)·log(1−a)`. This is the leading exponent by which the
complete-homogeneous bad-count `h_r` exceeds the subset-sum ceiling `e_r`. -/
noncomputable def leadingExpGap (a : ℝ) : ℝ :=
  (1 + a) * Real.log (1 + a) + (1 - a) * Real.log (1 - a)

/-- `leadingExpGap` is symmetric-fold-evaluated: rewriting in the `x·log x` form for the convexity
argument. `leadingExpGap a = f (1+a) + f (1−a)` with `f x = x·log x`. -/
theorem leadingExpGap_eq_mulLog (a : ℝ) :
    leadingExpGap a = (fun x => x * Real.log x) (1 + a) + (fun x => x * Real.log x) (1 - a) := by
  simp [leadingExpGap]

/-- **HEADLINE — the leading-exponent gap is STRICTLY POSITIVE on `(0,1)`.**

`0 < a → a < 1 → 0 < leadingExpGap a`. The complete-homogeneous floor's leading exponent strictly
exceeds the subset-sum ceiling's at EVERY proportional fold `a ∈ (0,1)` — so Kambiré's subset-sum
count is NEVER the tight char-free leading order (the §0.2.a "NOT `e_j`, strictly larger leading
exponent" prose).

Proof: `x ↦ x·log x` is strictly convex on `Ici 0` (`Real.strictConvexOn_mul_log`). With the convex
combination `½•(1+a) + ½•(1−a) = 1` and `1 ≠ 1+a` (since `a ≠ 0`), strict convexity gives
`f 1 < ½•f(1+a) + ½•f(1−a)`. Since `f 1 = 1·log 1 = 0`, the RHS `= ½·leadingExpGap a` is
positive. -/
theorem leadingExpGap_pos {a : ℝ} (ha₀ : 0 < a) (ha₁ : a < 1) : 0 < leadingExpGap a := by
  have hx : (1 + a) ∈ Set.Ici (0 : ℝ) := by
    simp only [Set.mem_Ici]; linarith
  have hy : (1 - a) ∈ Set.Ici (0 : ℝ) := by
    simp only [Set.mem_Ici]; linarith
  have hne : (1 + a) ≠ (1 - a) := by
    intro h; apply absurd h; intro h'; linarith [ha₀]
  -- strict convexity of x ↦ x*log x at the midpoint ½(1+a)+½(1-a) = 1
  have hconv := Real.strictConvexOn_mul_log.2 hx hy hne
    (by norm_num : (0:ℝ) < 1/2) (by norm_num : (0:ℝ) < 1/2) (by norm_num : (1:ℝ)/2 + 1/2 = 1)
  -- the midpoint simplifies to 1
  have hmid : (1/2 : ℝ) • (1 + a) + (1/2 : ℝ) • (1 - a) = 1 := by
    simp only [smul_eq_mul]; ring
  rw [hmid] at hconv
  -- beta-reduce the lambdas + f 1 = 1 * log 1 = 0
  simp only [Real.log_one, mul_zero, smul_eq_mul] at hconv
  -- hconv : 0 < (1/2) * ((1+a) * log (1+a)) + (1/2) * ((1-a) * log (1-a))
  simp only [leadingExpGap]
  linarith [hconv]

/-- **The exact symmetric-fold (binding `r/s = 1/2`) leading-exponent constant.**

`leadingExpGap (1/2) = (3/2)·log(3/2) + (1/2)·log(1/2)` — the closed form behind the dossier's
`→ 0.26` prose (numerically `(3/2)·log 3 − 2·log 2 ≈ 0.261624`). -/
theorem leadingExpGap_half :
    leadingExpGap (1/2) = (3/2) * Real.log (3/2) + (1/2) * Real.log (1/2) := by
  simp only [leadingExpGap]; norm_num

/-- **The symmetric-fold constant is strictly positive** — the binding fold `r/s = 1/2` carries a
genuine leading-exponent gap (the prize-relevant instance of `leadingExpGap_pos`). -/
theorem leadingExpGap_half_pos : 0 < leadingExpGap (1/2) :=
  leadingExpGap_pos (by norm_num) (by norm_num)

end ArkLib.ProximityGap.BchksF1
