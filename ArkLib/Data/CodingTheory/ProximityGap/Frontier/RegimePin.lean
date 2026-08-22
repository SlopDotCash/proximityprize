/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# RegimePin — pinning the #407 prize regime (FOUNDATIONAL lane)

**Target.** Settle, as exact arithmetic, the prize regime for the Gauss-period floor
`B(μ_n) = max_{b≠0}‖Σ_{x∈μ_n} e_p(bx)‖`.

**The spec (CLAUDE.md / PROXIMITY_PRIZE_WORKBENCH.lean, ABF26 ePrint 2026/680).**
`ρ∈{1/2,1/4,1/8,1/16}`, `ε* = 2^{-128}`, `n = 2^a` (smooth eval domain), `k ≤ 2^40`,
`q < 2^256`, and the field-size requirement forces `q = p ≈ n·2^128`. Equivalently the
multiplicative **index** `m = (p−1)/n ≈ 2^128` is HELD CONSTANT as the FFT domain `n→∞`.

**The two framings to reconcile.**
- NEW comment: FIXED-INDEX. `m = 2^128` constant ⟹ `β := log_n p = 1 + 128/log₂ n → 1`,
  `n = Θ(p)` positive proportion as `n→∞`. Load-bearing wall = fixed-index effective
  Gauss-sum equidistribution.
- OLD KB/memory: THIN. At the canonical instance `n = 2^32` one gets `p = 2^160`, so
  `|H| = n = p^{1/5} < p^{1/4}` — a *thin* subgroup, BGK/di-Benedetto regime.

**The reconciliation (this file, machine-checked).** Both are the SAME object. With
`p = n·2^128` exactly, `m = 2^128` is constant (`index_const`), and
`β = (log₂ n + 128)/log₂ n = 1 + 128/log₂ n` (`beta_eq`), which is `5` at `n = 2^32`
(`beta_at_2pow32`) and `→ 1` as `n→∞` (`beta_tendsto_one`-style bound `beta_lt_of_large`).
The "β = 5 thin" and "fixed-index β→1" descriptions differ only by whether `n` is the finite
canonical instance or the asymptotic limit. `β` is **n-dependent**; the index `m = 2^128` is the
**invariant**.

**The Burgess/di-Benedetto in-regime gate.** di Benedetto et al. (2003.06165, Thm 3.1) requires
`p^{1/4} < |H| < p^{1/2}`. With `p = n·2^128`: `n > p^{1/4} ⟺ log₂ n > 128/3 ≈ 42.67`
(`burgess_gate`). So at `n = 2^32` we are BELOW `p^{1/4}` (thin, sub-Burgess), but for
`n ≥ 2^43` and asymptotically we are ABOVE `p^{1/4}` — Burgess/di-Benedetto are *in regime*.
HOWEVER the same Thm requires `|H| < p^{1/2}`, i.e. `n < √p`; with `p = n·2^128` that is
`n < 2^128` (`below_sqrt_p`) — true at EVERY finite prize instance. So di-Benedetto's window
`(p^{1/4}, p^{1/2})` is nonempty here precisely for `2^43 ≤ n < 2^128`, but its *bound*
`|Σ| ≤ |H|^{1−31/2880}` is a power saving off trivial, a half-power short of the prize
`√(n·log m)` (recorded as `record_exponent`, the numeric gap).

**Honesty.** Everything here is exact real-arithmetic about the regime parameters; it pins WHICH
wall is load-bearing and reconciles the two framings. It does NOT prove the floor `B`. No
fabricated closure.
-/

namespace ArkLib.ProximityGap.RegimePin

open Real

/-- The fixed proximity-loss budget exponent: `ε* = 2^{-128}`. -/
def epsBits : ℝ := 128

/-- The prize prime law: `p = n · 2^{128}` (the field-size requirement `q ≳ a/ε*`, `a ~ n`).
We work with the dominant term `p ≈ n·2^128`; the `−1` in `m=(p−1)/n` is negligible. -/
noncomputable def primeOf (n : ℝ) : ℝ := n * (2 : ℝ) ^ (128 : ℝ)

/-- The multiplicative index `m = p/n`. -/
noncomputable def indexOf (n : ℝ) : ℝ := primeOf n / n

/-- **Index is constant.** For every `n > 0`, `m = p/n = 2^128`. This is the invariant that
both framings agree on; `β` varies, `m` does not. -/
theorem index_const {n : ℝ} (hn : n ≠ 0) : indexOf n = (2 : ℝ) ^ (128 : ℝ) := by
  unfold indexOf primeOf
  field_simp

/-- `β := log_n p = log₂ p / log₂ n`. We phrase it via natural logs (basis-free):
`β = log p / log n`. -/
noncomputable def betaOf (n : ℝ) : ℝ := Real.log (primeOf n) / Real.log n

/-- **β in closed form.** For `n > 1`, `β = 1 + (128·log 2)/log n`. Equivalently in base-2,
`β = 1 + 128/log₂ n`. -/
theorem beta_eq {n : ℝ} (hn : 1 < n) :
    betaOf n = 1 + (128 * Real.log 2) / Real.log n := by
  have hlogn : Real.log n ≠ 0 := ne_of_gt (Real.log_pos hn)
  have hnpos : (0:ℝ) < n := lt_trans one_pos hn
  unfold betaOf primeOf
  rw [Real.log_mul (ne_of_gt hnpos) (by positivity)]
  rw [Real.log_rpow (by norm_num)]
  field_simp

/-- **β = 5 at the canonical instance n = 2^32.** Plugging `n = 2^32` (`log₂ n = 32`) gives
`β = 1 + 128/32 = 5`, i.e. `p = 2^160`, `|H| = p^{1/5}` — the OLD "thin" reading, recovered as a
single finite point of the family. -/
theorem beta_at_2pow32 : betaOf ((2:ℝ) ^ (32:ℝ)) = 5 := by
  have h2 : (1:ℝ) < (2:ℝ) ^ (32:ℝ) := by
    have : (2:ℝ)^(0:ℝ) < (2:ℝ)^(32:ℝ) := by
      apply Real.rpow_lt_rpow_left_iff (by norm_num) |>.mpr; norm_num
    simpa using this
  have hl2 : Real.log 2 ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
  have hlog : Real.log ((2:ℝ) ^ (32:ℝ)) = 32 * Real.log 2 := Real.log_rpow (by norm_num) 32
  rw [beta_eq h2, hlog]
  have : (128 : ℝ) * Real.log 2 / (32 * Real.log 2) = 4 := by
    rw [mul_div_mul_right _ _ hl2]; norm_num
  rw [this]; norm_num

/-- **β decreases to 1.** For larger `n`, `β` is smaller: monotone-decreasing in `n` for `n>1`,
with `β → 1`. Concretely, `β < 1 + ε` once `log n > 128·log2/ε`. We record the clean direction:
if `log₂ n ≥ 128/ε'` then `β ≤ 1 + ε'`. -/
theorem beta_le_of_large {n ε' : ℝ} (hn : 1 < n) (hε : 0 < ε')
    (hbig : Real.log n ≥ (128 * Real.log 2) / ε') : betaOf n ≤ 1 + ε' := by
  rw [beta_eq hn]
  have hlogn : 0 < Real.log n := Real.log_pos hn
  have hnum : (0:ℝ) < 128 * Real.log 2 := by positivity
  have : (128 * Real.log 2) / Real.log n ≤ ε' := by
    rw [div_le_iff₀ hlogn]
    calc 128 * Real.log 2 = ε' * ((128 * Real.log 2)/ε') := by field_simp
      _ ≤ ε' * Real.log n := by
          apply mul_le_mul_of_nonneg_left hbig (le_of_lt hε)
  linarith

/-- **Below √p at every finite instance.** `|H| = n < √p` exactly when `n < 2^128`. Since the
prize caps `n = 2^a` at `a ≤ 40` (and even generously `a < 128`), `n < √p` ALWAYS at realistic
params: di-Benedetto's upper window constraint `|H| < p^{1/2}` is satisfied. -/
theorem n_lt_sqrt_p {n : ℝ} (hn0 : 0 < n) (hn : n < (2:ℝ)^(128:ℝ)) :
    n < Real.sqrt (primeOf n) := by
  rw [Real.lt_sqrt (le_of_lt hn0)]
  unfold primeOf
  -- n^2 < n·2^128  ⟸  n < 2^128 (and n > 0)
  calc n ^ 2 = n * n := pow_two n
    _ < n * (2:ℝ)^(128:ℝ) := mul_lt_mul_of_pos_left hn hn0

/-- **Burgess / di-Benedetto in-regime gate.** `n > p^{1/4} ⟺ log₂ n > 128/3`. With
`p = n·2^128`, `p^{1/4} = n^{1/4}·2^32`, so `n > p^{1/4} ⟺ n^{3/4} > 2^32 ⟺ n > 2^{128/3}`.
At `n = 2^32` (`log₂ n = 32 < 42.67`) we are BELOW `p^{1/4}` (thin); for `n ≥ 2^43` we are above.
We record the equivalent clean threshold on `log n`. -/
theorem burgess_gate {n : ℝ} (hn0 : 0 < n) :
    n > primeOf n ^ ((1:ℝ)/4) ↔ Real.log n > (128 * Real.log 2) / 3 := by
  have hp : (0:ℝ) < primeOf n := by unfold primeOf; positivity
  -- log p = log n + 128 log 2.
  have hlogp : Real.log (primeOf n) = Real.log n + 128 * Real.log 2 := by
    unfold primeOf
    rw [Real.log_mul (ne_of_gt hn0) (by positivity), Real.log_rpow (by norm_num)]
  -- `n > p^{1/4}` ⟺ `p^{1/4} < n` ⟺ (strictly-mono `Real.log`) `log (p^{1/4}) < log n`.
  rw [gt_iff_lt, ← Real.log_lt_log_iff (by positivity) hn0,
      Real.log_rpow hp, hlogp, gt_iff_lt]
  constructor
  · intro h; linarith
  · intro h; linarith

/-- **The record-bound exponent gap (di-Benedetto).** The best proven subgroup bound is
`|Σ| ≤ |H|^{1−31/2880}` (di Benedetto et al. 2020, Thm 3.1, valid `p^{1/4}<|H|<p^{1/2}`). The
prize target is `√(n·log m) ≈ n^{1/2}·poly`. The exponent gap is `(1−31/2880) − 1/2 = 1/2 −
31/2880 ≈ 0.4892`: the record is essentially LINEAR in `n`, the target SQRT — a half-power short.
This `def` records the exponent; it is positive (`record_exponent_pos`). -/
noncomputable def recordExponent : ℝ := (1 - 31/2880) - 1/2

theorem record_exponent_pos : 0 < recordExponent := by unfold recordExponent; norm_num

theorem record_exponent_val : recordExponent = 1/2 - 31/2880 := by unfold recordExponent; ring

/-
**Axiom audit (verified `lake env lean`, 2026-06-13).** All eight theorems above
(`index_const`, `beta_eq`, `beta_at_2pow32`, `beta_le_of_large`, `n_lt_sqrt_p`, `burgess_gate`,
`record_exponent_pos`, `record_exponent_val`) depend only on
`[propext, Classical.choice, Quot.sound]` — axiom-clean, no `sorry`/`admit`/`native_decide`.

**VERDICT (regime pin).** The newest #407 comment is HALF-RIGHT.
- CORRECT: the multiplicative INDEX `m = (p−1)/n = 2^128` is the invariant (`index_const`), not a
  fixed exponent `n = p^δ`. The wall is fixed-index effective Gauss-sum equidistribution.
- MISLEADING: `β → 1` / `n = Θ(p)` positive-proportion is a pure `n→∞` asymptotic (`beta_le_of_large`).
  At every REALIZABLE prize instance (`n = 2^a`, `a ∈ [25,40]`, workbench: `n=2^25, q≈2^153`) we have
  `β = 1 + 128/a ∈ [4.2, 6.1]` (`beta_at_2pow32` gives the canonical `β=5` at `a=32`), and `|H| = n`
  is BELOW BOTH `p^{1/4}` and `p^{1/2}` (`n_lt_sqrt_p`; Burgess gate `burgess_gate` needs `a > 128/3 ≈
  42.67`, never met for `a ≤ 40`). So at prize params the family is THIN (BGK/di-Benedetto regime),
  and Burgess / large-sieve / effective-Sato-Tate are NOT in regime (their `(p^{1/4},p^{1/2})` window
  is empty for `a ≤ 40`).
- The di-Benedetto record `|Σ| ≤ |H|^{1−31/2880}` is both out-of-regime (needs `|H|>p^{1/4}`) and a
  half-power short anyway (`record_exponent_pos`: exponent gap `1/2 − 31/2880 ≈ 0.489 > 0`).

So "fixed-index β→1" and "thin β≈5" describe the SAME family; the comment correctly relocates the
*invariant* (index `m`, hence the `log(p/n)=log m` in the target) but its asymptotic reframing does
NOT move the prize out of the thin-subgroup BGK wall or unlock Burgess-type tools. No closure of the
floor `B`; this lane only PINS the regime. Cross-checked by `scripts/probes/_wf407_regime_pin.py`.
-/

end ArkLib.ProximityGap.RegimePin

-- Axiom audit (expected: [propext, Classical.choice, Quot.sound] only)
#print axioms ArkLib.ProximityGap.RegimePin.beta_eq
#print axioms ArkLib.ProximityGap.RegimePin.n_lt_sqrt_p
#print axioms ArkLib.ProximityGap.RegimePin.burgess_gate
#print axioms ArkLib.ProximityGap.RegimePin.beta_at_2pow32
