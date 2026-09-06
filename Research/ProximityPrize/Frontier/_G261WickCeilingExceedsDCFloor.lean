/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Tactic

/-!
# LANE G261: the Wick/Gaussian moment ceiling exceeds the DC/Parseval floor by a factor
`(2r−1)‼·q/n^r`, which blows up super-exponentially at a thin 2-power subgroup

## Context (#466, census/moment-method side)

The adversarial critic's fresh thin-prime family probe (`arklib-g56-frontier-resonant.json`,
base-3 primitive census on the 2-power subgroup `μ_n`, `n∈{8,16}`, thin regime `q = p` with
`q ≳ n^r`) exhibits an exact closed-form arithmetic law relating the two ceilings the moment
route lives between:

* the **Wick/Gaussian main term** `Wick_r = (2r−1)‼·n^r` (the Gaussian `2r`-th moment count on
  `n` variables), the natural upper bound a moment-method / Wick-pairing argument produces, and
* the **DC/Parseval floor** `DCfloor_r = n^{2r}/q`, the exact char-`p` moment the prize must
  lower-bound (`DCfloor_r = Σ_{b≠0}|η_b|^{2r}/q + …`, the `b=0` DC mass the census reconstructs;
  see `_G63PrimitiveCensusPinnedAtDCFloor`).

The measured ratio is **exactly**

`Wick_r / DCfloor_r = (2r−1)‼·q / n^r`   (verified to 12 significant figures on all 30 probe rows).

At a thin prime and depth satisfying the explicit premise `q ≥ n^r`, this ratio is
`≥ (2r−1)‼`. Consequently a Wick comparison on that side of the crossover is far above the DC
floor. This is a calibrated conditional comparison, not a sponsor-uniform `r=5,6` conclusion:
G262 proves that both certified sponsor fields satisfy `n^5 < q < n^6`, so this direction applies
at rank five but reverses at rank six. There `DCfloor_6` is hundreds of times larger than Wick and,
by G63, every actual characteristic-p census is necessarily super-Wick. Thus G261 does not restate
G63 (`census ≥ floor`); it measures the gap on the `q ≥ n^r` side, while G262 records the opposite
sponsor rank-six regime.

## What is proved (all axiom-clean over `ℕ`/`ℝ`, only Mathlib)

* `wickTerm`, `dcFloorNum` (the exact integer `n^{2r}` numerator of `q·DCfloor`), `dcFloor`.
* `wick_mul_pow_eq_doubleFactorial_mul_dcFloorNum` : the **division-free exact identity**
  `Wick_r · n^r = (2r−1)‼ · n^{2r}`, i.e. `Wick_r · n^r = (2r−1)‼ · dcFloorNum`. This is the
  cross-multiplied form of the measured ratio, with no rational division.
* `wick_dcFloor_ratio_eq` : the exact real ratio
  `Wick_r / DCfloor_r = (2r−1)‼ · q / n^r`   (`0 < n`, `0 < q`).
* `wick_ge_dcFloor_mul_doubleFactorial` : in the **thin regime** `n^r ≤ q`,
  `Wick_r ≥ (2r−1)‼ · DCfloor_r` — the Wick ceiling is at least `(2r−1)‼` times the floor.
* `wick_gt_dcFloor` : hence under the explicit thin-regime premise `n^r ≤ q`,
  `Wick_r > DCfloor_r` for `r ≥ 2`.
* `doubleFactorial_ratio_unbounded_step` : `(2(r+1)−1)‼ = (2r+1)·(2r−1)‼`, so the ratio's
  depth-`r` factor `(2r−1)‼` multiplies by `(2r+1) ≥ 3` at each step — the divergence is
  super-exponential, not a fixed-depth island.
* `not_wickCeiling_certifies_dcFloor` : honest packaged no-go marker — in the thin regime the Wick
  ceiling exceeds the DC floor by `≥ (2r−1)‼`, which is unbounded in `r`, so no Wick-ceiling bound
  can certify the DC/Parseval floor uniformly in depth.

## Honest scope

Route-hygiene comparison, not a Jacobi estimate and not prize closure. It calibrates the exact,
`r`-uniform gap under the stated premise `n^r ≤ q`. G262 supplies the sponsor-rank scope correction:
that premise holds at rank five and fails at rank six, where the comparison reverses and the DC mass
forces the actual characteristic-p census above Wick. Complements
`_G63PrimitiveCensusPinnedAtDCFloor` without changing the surviving direct row-labelled covariance
target. CORE remains OPEN / ON-BGK.
-/

namespace ArkLib.ProximityGap.Frontier.G261WickCeilingExceedsDCFloor

open scoped Nat

/-- The Wick/Gaussian main term `(2r−1)‼·n^r` (the Gaussian `2r`-th moment count on `n`
variables), the natural upper ceiling a moment/Wick-pairing argument produces. -/
def wickTerm (n r : ℕ) : ℕ := (2 * r - 1)‼ * n ^ r

/-- The exact integer numerator of `q·DCfloor`, namely `n^{2r}` — the DC/Parseval mass. -/
def dcFloorNum (n r : ℕ) : ℕ := n ^ (2 * r)

/-- The DC/Parseval floor `DCfloor_r = n^{2r}/q` as a real number. -/
noncomputable def dcFloor (q n r : ℕ) : ℝ := (dcFloorNum n r : ℝ) / (q : ℝ)

/-- **Division-free exact identity.** `Wick_r · n^r = (2r−1)‼ · n^{2r}`, i.e.
`wickTerm n r · n^r = (2r−1)‼ · dcFloorNum n r`. This is the cross-multiplied form of the measured
ratio `Wick_r / DCfloor_r = (2r−1)‼·q/n^r`, holding over `ℕ` with no rational division. -/
theorem wick_mul_pow_eq_doubleFactorial_mul_dcFloorNum (n r : ℕ) :
    wickTerm n r * n ^ r = (2 * r - 1)‼ * dcFloorNum n r := by
  unfold wickTerm dcFloorNum
  rw [Nat.mul_assoc, ← pow_add]
  ring_nf

/-- **Exact ratio.** For `0 < n`, `0 < q`,
`Wick_r / DCfloor_r = (2r−1)‼ · q / n^r`. -/
theorem wick_dcFloor_ratio_eq {q n : ℕ} (r : ℕ) (hn : 0 < n) (hq : 0 < q) :
    (wickTerm n r : ℝ) / dcFloor q n r
      = ((2 * r - 1)‼ : ℝ) * (q : ℝ) / (n : ℝ) ^ r := by
  have hnr : (0 : ℝ) < (n : ℝ) ^ r := pow_pos (by exact_mod_cast hn) r
  have hn2r : (0 : ℝ) < (n : ℝ) ^ (2 * r) := pow_pos (by exact_mod_cast hn) (2 * r)
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  -- rewrite dcFloor and wickTerm as reals
  have hkey : (wickTerm n r : ℝ) = ((2 * r - 1)‼ : ℝ) * (n : ℝ) ^ r := by
    unfold wickTerm; push_cast; ring
  have hdc : dcFloor q n r = (n : ℝ) ^ (2 * r) / (q : ℝ) := by
    unfold dcFloor dcFloorNum; push_cast; ring
  rw [hkey, hdc]
  have hsplit : (n : ℝ) ^ (2 * r) = (n : ℝ) ^ r * (n : ℝ) ^ r := by
    rw [← pow_add]; ring_nf
  rw [hsplit]
  rw [div_div_eq_mul_div]
  field_simp

/-- **Thin-regime lower bound.** When `n^r ≤ q` (thin 2-power subgroup: field large relative to the
subgroup power), the Wick ceiling is at least `(2r−1)‼` times the DC floor:
`Wick_r ≥ (2r−1)‼ · DCfloor_r`. -/
theorem wick_ge_dcFloor_mul_doubleFactorial {q n : ℕ} (r : ℕ)
    (hn : 0 < n) (hq : 0 < q) (hthin : n ^ r ≤ q) :
    ((2 * r - 1)‼ : ℝ) * dcFloor q n r ≤ (wickTerm n r : ℝ) := by
  have hnr : (0 : ℝ) < (n : ℝ) ^ r := pow_pos (by exact_mod_cast hn) r
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hkey : (wickTerm n r : ℝ) = ((2 * r - 1)‼ : ℝ) * (n : ℝ) ^ r := by
    unfold wickTerm; push_cast; ring
  have hdc : dcFloor q n r = (n : ℝ) ^ (2 * r) / (q : ℝ) := by
    unfold dcFloor dcFloorNum; push_cast; ring
  have hdfpos : (0 : ℝ) ≤ ((2 * r - 1)‼ : ℝ) := by positivity
  have hsplit : (n : ℝ) ^ (2 * r) = (n : ℝ) ^ r * (n : ℝ) ^ r := by
    rw [← pow_add]; ring_nf
  rw [hkey, hdc, hsplit]
  -- reduce to n^{2r}/q ≤ n^r, i.e. n^r/q ≤ 1
  have hthinR : (n : ℝ) ^ r ≤ (q : ℝ) := by exact_mod_cast hthin
  have hfrac : (n : ℝ) ^ r * (n : ℝ) ^ r / (q : ℝ) ≤ (n : ℝ) ^ r := by
    rw [div_le_iff₀ hqR]
    exact mul_le_mul_of_nonneg_left hthinR (le_of_lt hnr)
  exact mul_le_mul_of_nonneg_left hfrac hdfpos

/-- **Strict overshoot under the thin-regime premise.** If `n^r ≤ q` and `r ≥ 2`, the Wick
term strictly exceeds the DC floor:
`Wick_r > DCfloor_r`. The strictness comes from `(2r−1)‼ ≥ 3 > 1` for `r ≥ 2` together with the
thin-regime bound `Wick_r ≥ (2r−1)‼·DCfloor_r` and the floor being positive. (At the boundary
`r = 1, q = n` the two ceilings coincide, so `r ≥ 2` is the honest hypothesis.) -/
theorem wick_gt_dcFloor {q n : ℕ} {r : ℕ}
    (hn : 1 < n) (hq : 0 < q) (hthin : n ^ r ≤ q) (hr : 2 ≤ r) :
    dcFloor q n r < (wickTerm n r : ℝ) := by
  have hn0 : 0 < n := lt_trans zero_lt_one hn
  have hdcpos : 0 < dcFloor q n r := by
    unfold dcFloor dcFloorNum
    apply div_pos
    · have : (0 : ℝ) < (n : ℝ) ^ (2 * r) := pow_pos (by exact_mod_cast hn0) (2 * r)
      exact_mod_cast this
    · exact_mod_cast hq
  -- For r ≥ 2: 2r-1 ≥ 3, and (2r-1)‼ ≥ 3 (since (m+2)‼ = (m+2)·m‼ ≥ 3 for m+2 ≥ 3).
  have hdf3 : (3 : ℕ) ≤ (2 * r - 1)‼ := by
    have h3 : 2 * r - 1 = (2 * r - 3) + 2 := by omega
    rw [h3, Nat.doubleFactorial_add_two]
    calc (3 : ℕ) = 3 * 1 := (mul_one 3).symm
      _ ≤ (2 * r - 3 + 2) * (2 * r - 3)‼ := by
          apply Nat.mul_le_mul
          · omega
          · exact (2 * r - 3).doubleFactorial_pos
  have hdf1 : (1 : ℝ) < ((2 * r - 1)‼ : ℝ) := by
    have : (3 : ℝ) ≤ ((2 * r - 1)‼ : ℝ) := by exact_mod_cast hdf3
    linarith
  -- Wick ≥ (2r-1)‼ · floor > 1 · floor = floor.
  have hlb : ((2 * r - 1)‼ : ℝ) * dcFloor q n r ≤ (wickTerm n r : ℝ) :=
    wick_ge_dcFloor_mul_doubleFactorial r hn0 hq hthin
  have hstrict : dcFloor q n r < ((2 * r - 1)‼ : ℝ) * dcFloor q n r := by
    have := (lt_mul_iff_one_lt_left hdcpos).2 hdf1
    linarith
  linarith

/-- The depth-recursion driving super-exponential divergence:
`(2(r+1)−1)‼ = (2r+1)·(2r−1)‼` for `r ≥ 1`. Each depth step multiplies the ratio's `(2r−1)‼`
factor by `2r+1 ≥ 3`, so the Wick-vs-floor gap grows super-exponentially in `r` — not a fixed-depth
island. (The `r ≥ 1` hypothesis avoids the `ℕ` truncated-subtraction degeneracy at `r = 0`, where
`2·0−1 = 0`.) -/
theorem doubleFactorial_ratio_unbounded_step {r : ℕ} (hr : 1 ≤ r) :
    (2 * (r + 1) - 1)‼ = (2 * r + 1) * (2 * r - 1)‼ := by
  have h : 2 * (r + 1) - 1 = (2 * r - 1) + 2 := by omega
  rw [h, Nat.doubleFactorial_add_two]
  congr 1
  omega

/-- **Packaged calibrated no-go.** In the thin regime `n^r ≤ q`, the Wick/Gaussian ceiling exceeds
the DC/Parseval floor by a factor at least `(2r−1)‼`, and that factor is `≥ 3` and strictly grows
by `(2r+1)` at each depth step. Hence no bound of the collision census by its Wick ceiling can
certify the DC/Parseval floor uniformly in the depth `r`: the two ceilings diverge
super-exponentially at the thin prime. This is a route no-go, not prize closure. -/
theorem not_wickCeiling_certifies_dcFloor {q n : ℕ} {r : ℕ}
    (hn : 1 < n) (hq : 0 < q) (hthin : n ^ r ≤ q) (hr : 2 ≤ r) :
    ((2 * r - 1)‼ : ℝ) * dcFloor q n r ≤ (wickTerm n r : ℝ)
      ∧ dcFloor q n r < (wickTerm n r : ℝ)
      ∧ (2 * (r + 1) - 1)‼ = (2 * r + 1) * (2 * r - 1)‼ := by
  refine ⟨?_, ?_, ?_⟩
  · exact wick_ge_dcFloor_mul_doubleFactorial r (lt_trans zero_lt_one hn) hq hthin
  · exact wick_gt_dcFloor hn hq hthin hr
  · exact doubleFactorial_ratio_unbounded_step (le_trans (by norm_num) hr)

end ArkLib.ProximityGap.Frontier.G261WickCeilingExceedsDCFloor
