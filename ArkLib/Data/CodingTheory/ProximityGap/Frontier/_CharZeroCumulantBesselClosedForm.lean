/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._CharZeroMGFBesselBound
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The char-0 cumulant generating function: closed form and its sub-Gaussian envelope (#389, T4)

This file records the **closed form of the per-class cumulant generating function** of the char-0
additive energy ladder of the 2-power subgroup `μ_n`, and the global sub-Gaussian envelope that
closes the char-0 floor.

## The arithmetic behind the definition (probe-established, not re-derived in Lean here)

Write `E_r(ℂ)` for the char-0 `2r`-fold additive energy of `μ_n` and `κ_{2r}` for its `2r`-th
cumulant (moment→cumulant inversion of the even-moment sequence). Three independently verified
probes (`probe_T4_cr_genfunc_growth.py`, `probe_dcwick_ladder_closure_char0.py`,
`probe_T4_cr_bruteforce_xcheck.py` — the last a brute-force char-0 energy count at `n = 4, 8`) give:

* **Linearity.** `κ_{2r} = c_r · n` for all `r = 1 … 16`, with the integer sequence
  `c_r = 1, −3, 40, −1155, 57456, −4370520, 471556800, −68492499075, …`
  (cumulants are connected balanced-config counts; antipodal-pair connectedness over `μ_{2^μ}`
  is `O(n)` — hence exact linearity in `n`).

* **Closed form (the T4 deliverable).** The *per-class* cumulant generating function
  `g(t) = Σ_{r≥1} c_r t^{2r}/(2r)!` is **exactly**
  `g(t) = ½ · log I₀(2t)`, where `I₀(2t) = Σ_k t^{2k}/(k!)²` is the modified Bessel function;
  the per-class moment generating function is `exp g(t) = √(I₀(2t))`. All 16 computed `c_r` match
  `(2r)!·[t^{2r}] ½ log I₀(2t)` exactly. Hence the **total** char-0 cumulant generating function is
  `G_n(t) = n·g(t) = (n/2)·log I₀(2t)`, matching `κ_{2r} = c_r·n`.

* **Radius / growth (closed form).** From the Hadamard product `I₀(z) = ∏_k (1 + z²/j_{0,k}²)`
  (`j_{0,k}` = positive zeros of `J₀`), `g(t) = ½ Σ_k log(1 + 4t²/j_{0,k}²)`, so
  `c_r = (−1)^{r+1}·(2r)!·(2^{2r−1}/r)·σ_{2r}` with `σ_{2r} = Σ_k j_{0,k}^{−2r}` the Rayleigh sum.
  `g` is analytic for `|t| < R := j_{0,1}/2 = 1.20241…`; the MGF coefficients
  `a_r := |c_r|/(2r)! = (2^{2r−1}/r)·σ_{2r} ∼ (1/2r)·R^{−2r}`, so
  `L := lim a_{r+1}/a_r = R^{−2} = 4/j_{0,1}² = 0.69166… < 1` **strictly** — the cumulant series
  converges out to `|t| = R > 1`, comfortably past the floor-closing saddle `t* ∼ √(2 log m / n) → 0`.

## What is proved here (axiom-clean, Lean)

The single load-bearing analytic fact, at the **cumulant** level, is the **global** sub-Gaussian
envelope of `g`: `g(t) = ½ log I₀(2t) ≤ ½ t²` for all `t`, equivalently the per-class moment
generating function obeys `√(I₀(2t)) ≤ exp(t²/2)` (a variance-1 Gaussian envelope). This is the log
of the already-proven termwise Bessel inequality `I₀(2t) ≤ exp(t²)`
(`_CharZeroMGFBesselBound.besselI0Two_le_exp_sq`, from `(k!)² ≥ k!`). Because the envelope is
**global** (every `t`, no radius caveat), the floor-closing saddle needs no convergence-radius
bookkeeping — the radius computation above is a sharper companion fact, not a prerequisite.

* `besselI0Two_pos` : `0 < I₀(2t)` (the `k = 0` term is `1`);
* `cumulantGenFn` : `g(t) = ½ Real.log (I₀(2t))`;
* `cumulantGenFn_le_half_sq` : `g(t) ≤ t²/2` for all `t` (**the sub-Gaussian envelope**);
* `mgf_le_exp_half_sq` : `√(I₀(2t)) ≤ exp(t²/2)` (the per-class MGF form).

**HONESTY (scope).** This is the *char-0* cumulant generating function. The prize needs the
*char-p* MGF; the open core is the char-p excess `E_r^{F_p} − E_r(ℂ) ≥ 0` re-entering past the
anomaly depth (see `_CharZeroMGFBesselBound` header and `EnergyCharacterTransport`). This file
closes the char-0 cumulant face and pins the closed form `g = ½ log I₀(2t)`; it does **not** cross
the char-p wall. Issue #389, thread T4-cr-genfunc-growth.
-/

namespace ProximityGap.Frontier.CharZeroMGFBessel

open scoped Nat

/-- The general term `t^{2k}/(k!)²` is nonnegative (the exponent `2k` is even: `t^{2k}=(t²)^k`). -/
theorem bessel_term_nonneg (t : ℝ) (k : ℕ) :
    0 ≤ t ^ (2 * k) / (k.factorial : ℝ) ^ 2 := by
  have ht : (0 : ℝ) ≤ t ^ (2 * k) := by
    rw [pow_mul]; positivity
  positivity

/-- `0 < I₀(2t)`: the `k = 0` term of `Σ_k t^{2k}/(k!)²` is `1 > 0` and all terms are `≥ 0`. -/
theorem besselI0Two_pos (t : ℝ) : 0 < besselI0Two t := by
  -- summability on the whole line: dominate `t^{2k}/(k!)²` by `|t|^{2k}/(k!)²` ≤ `|t|^{2k}/k!`.
  have hsum : Summable (fun k : ℕ => t ^ (2 * k) / (k.factorial : ℝ) ^ 2) := by
    refine Summable.of_nonneg_of_le (fun k => bessel_term_nonneg t k) (fun k => ?_)
      (summable_exp_terms |t|)
    have hkpos : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast k.factorial_pos
    have hk1 : (1 : ℝ) ≤ (k.factorial : ℝ) := by exact_mod_cast k.factorial_pos
    have hle : (k.factorial : ℝ) ≤ (k.factorial : ℝ) ^ 2 := by nlinarith [hk1, hkpos]
    have habs : t ^ (2 * k) ≤ |t| ^ (2 * k) := by
      rw [← abs_pow]; exact le_abs_self _
    have habsnn : (0 : ℝ) ≤ |t| ^ (2 * k) := by positivity
    calc t ^ (2 * k) / (k.factorial : ℝ) ^ 2
        ≤ |t| ^ (2 * k) / (k.factorial : ℝ) ^ 2 := by gcongr
      _ ≤ |t| ^ (2 * k) / (k.factorial : ℝ) :=
          div_le_div_of_nonneg_left habsnn hkpos hle
  have h0 : (0 : ℝ) < t ^ (2 * 0) / ((0 : ℕ).factorial : ℝ) ^ 2 := by norm_num
  exact hsum.tsum_pos (fun k => bessel_term_nonneg t k) 0 h0

/-- **The per-class char-0 cumulant generating function** `g(t) = ½ · log I₀(2t)`. Probe-pinned
closed form: `Σ_{r≥1} c_r t^{2r}/(2r)! = ½ log I₀(2t)`, equivalently per-class MGF `= √(I₀(2t))`. -/
noncomputable def cumulantGenFn (t : ℝ) : ℝ := (1 / 2) * Real.log (besselI0Two t)

/-- **The sub-Gaussian envelope of the cumulant generating function (the char-0 floor face).**
`g(t) = ½ log I₀(2t) ≤ ½ t²` for **all** `t`. This is the log of the termwise Bessel inequality
`I₀(2t) ≤ exp(t²)`; its global validity (no radius caveat) is what makes the floor-closing saddle
`t* ∼ √(2 log m / n)` automatic. -/
theorem cumulantGenFn_le_half_sq (t : ℝ) : cumulantGenFn t ≤ (1 / 2) * t ^ 2 := by
  have hpos : 0 < besselI0Two t := besselI0Two_pos t
  have hposabs : 0 < besselI0Two |t| := besselI0Two_pos |t|
  have hle : besselI0Two |t| ≤ Real.exp (|t| ^ 2) := besselI0Two_le_exp_sq |t| (abs_nonneg t)
  -- `besselI0Two` is even (only `t^{2k}` appears), so `besselI0Two t = besselI0Two |t|`.
  have heven : besselI0Two t = besselI0Two |t| := by
    unfold besselI0Two
    refine tsum_congr (fun k => ?_)
    rw [(even_two_mul k).pow_abs t]
  have hsq : |t| ^ 2 = t ^ 2 := by rw [sq_abs]
  have hlog : Real.log (besselI0Two t) ≤ t ^ 2 := by
    rw [heven]
    calc Real.log (besselI0Two |t|)
        ≤ Real.log (Real.exp (|t| ^ 2)) := Real.log_le_log hposabs hle
      _ = |t| ^ 2 := Real.log_exp _
      _ = t ^ 2 := hsq
  unfold cumulantGenFn
  linarith

/-- **The per-class moment generating function form:** `√(I₀(2t)) = exp(g(t)) ≤ exp(t²/2)`. The
per-class char-0 MGF is dominated by a variance-1 Gaussian MGF, globally. -/
theorem mgf_le_exp_half_sq (t : ℝ) :
    Real.sqrt (besselI0Two t) ≤ Real.exp ((1 / 2) * t ^ 2) := by
  have hpos : 0 < besselI0Two t := besselI0Two_pos t
  -- `√(I₀(2t)) = exp(½ log I₀(2t)) = exp(g(t)) ≤ exp(t²/2)`.
  have hsqrt : Real.sqrt (besselI0Two t) = Real.exp (cumulantGenFn t) := by
    unfold cumulantGenFn
    rw [mul_comm, Real.exp_mul, Real.exp_log hpos, ← Real.sqrt_eq_rpow]
  rw [hsqrt]
  exact Real.exp_le_exp.mpr (cumulantGenFn_le_half_sq t)

end ProximityGap.Frontier.CharZeroMGFBessel

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.CharZeroMGFBessel.besselI0Two_pos
#print axioms ProximityGap.Frontier.CharZeroMGFBessel.cumulantGenFn_le_half_sq
#print axioms ProximityGap.Frontier.CharZeroMGFBessel.mgf_le_exp_half_sq
