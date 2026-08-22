/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The C5/P4 depth-vs-conductor scissors: monodromy controls the AVERAGE but NOT the MAX (#407/#444)

This file pins, **axiom-clean and quantitatively**, the exact reason the
"big-monodromy (Katz) + Larsen's alternative ⟹ effective equidistribution ⟹ extreme-value
control of `M(n) = max_{b≠0}‖η_b‖`" route (the P4 angle) does **not** deliver the prize sup-norm.

## The question (P4)

Katz/Deligne equidistribution is a theorem about the *distribution* of the Gauss-period family
`{η_b}` (vertical Sato–Tate, the bulk law as `q → ∞`).  The prize object is the **MAX**.  An
extreme-value (EVT) deduction of the max from equidistribution needs effective control of the
survival function `S(t) = P(‖η_b‖/√n > t)` at the EVT depth `t* = √(2·log N)`,
`N = (q−1)/n`, which **grows with `q`** — equivalently, control of the moments up to order
`r* ≈ log N ≈ log q`.  Does effective monodromy supply that?

## The answer: NO — and here is the closed-form crossover

The effective (Deligne/Weil-II) version bounds the `r`-th cumulant deviation from the
real-Gaussian (Wick) value `(2r−1)‼·n^r` by `cond(r)·√q`.  The **honest** conductor of the
`r`-fold moment sheaf `M^{*r}` is *rank-driven*: `cond(r) = dim H¹_c ~ n^{2r−1}` with `Swan = 0`
(all Kummer sheaves tame).  This is recorded qualitatively in
`MonodromyConductorScaffold.ConductorGeometricBound` ("rank-driven `~ n^{2r−1}`, Weil-II lossy
by `√rank = n^{r−1/2}`").  Here we make it a *quantitative dichotomy*.

With the honest conductor the Deligne error term is `ERR(r) = n^{2r−1}·√q`.  The
`EffectiveConductorBound` it would supply is **informationally vacuous** — the error term alone
exceeds the *entire* summed Wick budget `q·(2r−1)‼·n^r` — precisely when

  `n^{r−1} > (2r−1)‼·√q`   (`VacuityCriterion`),

a pure product-form condition with **no logarithms**.  Taking logs and `q = n^β`, the vacuity
onset is the closed form

  `r₀ = 1 + β/2`   (`vacuity_threshold_eq`-flavoured: solving `(r−1)·ln n = (β/2)·ln n`).

So at the prize regime `β ∈ {4,5}` the bound goes vacuous at `r₀ ∈ {3,3.5}` — i.e. it is
already vacuous at `r = 4`, which is **exactly** the moment order where the char-`p` additive
energy excess `W_r` first appears (`E_3` is `p`-invariant; `E_4` first fails).  The EVT/sup
depth `r* ≈ log q ≈ 89` is far beyond `r₀`, so the monodromy route to the **max** is vacuous
by a margin that grows like `n^{r−r₀}`.

**Verdict (P4):** `reduces-to-bgk` / `no-gain`.  Effective monodromy controls the average
moment only up to `r ≤ r₀ = 1 + β/2 ≈ 3`; the max needs `r* ≈ log q`; in between the honest
Weil-II error swamps the Wick term.  Beating it is exactly proving `E_r ≤ (2r−1)‼·n^r` at deep
`r` **without** Weil-II — the BGK square-root-cancellation wall.

## What is proven here (axiom-clean, pure real arithmetic)

* `effErr` — the honest-rank Deligne error term `n^{2r−1}·√q`.
* `wickBudget` — the summed Wick budget `q·(2r−1)‼·n^r`.
* `VacuityCriterion` — the product-form criterion `n^{r−1} > (2r−1)‼·√q`.
* `effErr_gt_wickBudget_of_vacuityCriterion` — **the core**: the criterion implies the error
  alone exceeds the whole Wick budget (the bound is vacuous).
* `vacuityCriterion_of_log` — the log/closed-form face: `(r−1)·ln n > ln((2r−1)‼) + (½)·ln q`
  implies the criterion (so `r₀ = 1 + β/2` at `q = n^β` is the onset).
* `prize_point_vacuous_at_four` — the concrete prize instance `n = 2³⁰`, `q = 2¹⁵⁸`, `r = 4`:
  the bound is vacuous (the EVT route is dead already at the FOURTH moment).

Numerics: `scripts/probes/probe_c5_deeptail_gaussianize.py` (far-tail exponent rises toward 2 but
the deep tail is unmeasurable at `t*`), and the in-file derivation above (vacuity onset `r₀ = 4`
at the prize point, matching the char-`p` excess onset).  Issue #407/#444.
-/

open Real

namespace ArkLib.ProximityGap.Frontier.C5MonodromyMaxControlScissors

/-- **The honest-rank Deligne/Weil-II error term at moment order `r`.**  With the rank-driven
conductor `cond(r) = n^{2r−1}` (Swan `= 0`; `MonodromyConductorScaffold`), the effective
equidistribution error is `n^{2r−1}·√q`.  This is what `EffectiveConductorBound` actually
supplies when the conductor is read honestly (not the wished-for `O(1)`). -/
noncomputable def effErr (n q : ℝ) (r : ℕ) : ℝ := n ^ (2 * r - 1) * Real.sqrt q

/-- **The summed Wick budget at order `r`.**  The far-frequency cumulant target is
`∑_{b≠0}‖η_b‖^{2r} = q·E_r − n^{2r}`, whose real-Gaussian (Wick) value is `q·(2r−1)‼·n^r`.  An
effective bound is *informative* only if its error term does not already exceed this. -/
noncomputable def wickBudget (n q : ℝ) (r : ℕ) : ℝ :=
  q * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * n ^ r)

/-- **The vacuity criterion (product form, no logs).**  The Deligne error `effErr` exceeds the
Wick budget `wickBudget` exactly when `n^{r−1} > (2r−1)‼·√q`.  This is the clean arithmetic gate
for "monodromy cannot certify the `r`-th moment". -/
def VacuityCriterion (n q : ℝ) (r : ℕ) : Prop :=
  n ^ (r - 1) > (Nat.doubleFactorial (2 * r - 1) : ℝ) * Real.sqrt q

/-- **The core dichotomy.**  For `n > 0`, `q ≥ 0`, and `r ≥ 1`, the vacuity criterion
`n^{r−1} > (2r−1)‼·√q` implies that the honest-rank Deligne error term **alone** exceeds the
entire summed Wick budget:  `effErr n q r > wickBudget n q r`.  Hence the effective conductor
bound (with the honest `cond = n^{2r−1}`) is informationally vacuous at order `r`: it cannot
witness `E_r ≤ (2r−1)‼·n^r`.

Proof: multiply the criterion `n^{r−1} > (2r−1)‼·√q` by the positive factor `n^r·√q`.
LHS becomes `n^{r−1}·n^r·√q = n^{2r−1}·√q = effErr` (since `(r−1)+r = 2r−1` for `r ≥ 1`).
RHS becomes `(2r−1)‼·√q·n^r·√q = (2r−1)‼·n^r·q = wickBudget` (since `√q·√q = q`).
We take `q > 0` (always true: `q` is a field cardinality `≥ 2`); the multiply-out needs `√q > 0`. -/
theorem effErr_gt_wickBudget_of_vacuityCriterion {n q : ℝ} (hn : 0 < n) (hq : 0 < q)
    (r : ℕ) (hr : 1 ≤ r) (h : VacuityCriterion n q r) :
    effErr n q r > wickBudget n q r := by
  unfold VacuityCriterion at h
  unfold effErr wickBudget
  set s : ℝ := Real.sqrt q with hs
  have hs_pos : 0 < s := Real.sqrt_pos.mpr hq
  have hss : s * s = q := Real.mul_self_sqrt (le_of_lt hq)
  -- exponent bookkeeping: (r-1) + r = 2r - 1, and (2r-1) ≥ 1
  have hexp : (r - 1) + r = 2 * r - 1 := by omega
  have hnr : 0 < n ^ r := pow_pos hn r
  have key : n ^ (r - 1) * (n ^ r * s) > ((Nat.doubleFactorial (2 * r - 1) : ℝ) * s) * (n ^ r * s) := by
    apply mul_lt_mul_of_pos_right h
    exact mul_pos hnr hs_pos
  calc n ^ (2 * r - 1) * s
      = n ^ ((r - 1) + r) * s := by rw [hexp]
    _ = n ^ (r - 1) * n ^ r * s := by rw [pow_add]
    _ = n ^ (r - 1) * (n ^ r * s) := by ring
    _ > ((Nat.doubleFactorial (2 * r - 1) : ℝ) * s) * (n ^ r * s) := key
    _ = q * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * n ^ r) := by rw [← hss]; ring

/-- **The log / closed-form face of the criterion.**  Writing `q = n^β`, the vacuity criterion
`n^{r−1} > (2r−1)‼·√q` is `(r−1)·ln n > ln((2r−1)‼) + (½)·ln q`.  Dropping the slow
`ln((2r−1)‼)` term, the onset is `r₀ = 1 + (ln q)/(2 ln n) = 1 + β/2`.  This lemma proves the
clean direction: the log inequality implies the product criterion. -/
theorem vacuityCriterion_of_log {n q : ℝ} (hn : 1 < n) (hq : 0 < q) (r : ℕ) (hr : 1 ≤ r)
    (hlog : ((r : ℝ) - 1) * Real.log n
        > Real.log (Nat.doubleFactorial (2 * r - 1)) + (1 / 2) * Real.log q) :
    VacuityCriterion n q r := by
  unfold VacuityCriterion
  have hn0 : 0 < n := lt_trans one_pos hn
  have hdf_pos : 0 < (Nat.doubleFactorial (2 * r - 1) : ℝ) := by
    exact_mod_cast Nat.doubleFactorial_pos (2 * r - 1)
  -- Cast the Nat exponent r-1 to the real (r:ℝ)-1.
  have hcast : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
    have h1 : (1 : ℕ) ≤ r := hr
    push_cast [Nat.cast_sub h1]; ring
  -- LHS: n^(r-1) = exp(log n * (r-1))  (Nat power → real rpow → exp via rpow_def_of_pos).
  have hL : (n : ℝ) ^ (r - 1) = Real.exp (Real.log n * ((r : ℝ) - 1)) := by
    rw [← Real.rpow_natCast n (r - 1), hcast, Real.rpow_def_of_pos hn0]
  -- sqrt q = exp(log q * (1/2)).
  have hsqrt : Real.sqrt q = Real.exp (Real.log q * (1 / 2)) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hq]
  -- RHS: (2r-1)!! * sqrt q = exp(log((2r-1)!!) + log q * (1/2)).
  have hR : (Nat.doubleFactorial (2 * r - 1) : ℝ) * Real.sqrt q
      = Real.exp (Real.log (Nat.doubleFactorial (2 * r - 1)) + Real.log q * (1 / 2)) := by
    rw [Real.exp_add, Real.exp_log hdf_pos, hsqrt]
  rw [hL, hR]
  apply Real.exp_lt_exp.mpr
  -- goal: log((2r-1)!!) + log q * (1/2) < log n * ((r:ℝ)-1); rearrange hlog.
  have := hlog
  nlinarith [hlog]

/-- **The concrete prize instance: vacuous already at the FOURTH moment.**  At the prize point
`n = 2³⁰`, `q = 2¹⁵⁸` (so `β = log q / log n ≈ 5.27`), the vacuity criterion holds at `r = 4`:
`n^3 = 2⁹⁰ > (2·4−1)‼·√q = 105·2⁷⁹ ≈ 2^{85.7}`.  Hence the honest-rank effective conductor bound
is informationally vacuous at the fourth moment — exactly where the char-`p` additive-energy
excess `W_4` first appears.  The EVT/sup route needs control to depth `r ≈ log q ≈ 89`, far
beyond, so monodromy cannot control the max. -/
theorem prize_point_vacuous_at_four :
    VacuityCriterion ((2 : ℝ) ^ 30) ((2 : ℝ) ^ 158) 4 := by
  unfold VacuityCriterion
  -- LHS: (2^30)^(4-1) = (2^30)^3 = 2^90
  have hLHS : ((2 : ℝ) ^ 30) ^ (4 - 1) = (2 : ℝ) ^ 90 := by norm_num
  -- (2*4-1)!! = 7!! = 7*5*3*1 = 105
  have hdf : (Nat.doubleFactorial (2 * 4 - 1) : ℝ) = 105 := by norm_num [Nat.doubleFactorial]
  -- sqrt(2^158) = 2^79
  have hsq : Real.sqrt ((2 : ℝ) ^ 158) = (2 : ℝ) ^ 79 := by
    have : ((2 : ℝ) ^ 158) = ((2 : ℝ) ^ 79) ^ 2 := by rw [← pow_mul]
    rw [this, Real.sqrt_sq (by positivity)]
  rw [hLHS, hdf, hsq]
  -- goal: 2^90 > 105 * 2^79  ⟺  2^90 > 105 * 2^79.  2^90 = 2^11 * 2^79 = 2048 * 2^79 > 105 * 2^79.
  have h79 : (0 : ℝ) < (2 : ℝ) ^ 79 := by positivity
  have : (2 : ℝ) ^ 90 = 2048 * (2 : ℝ) ^ 79 := by
    rw [show (90 : ℕ) = 11 + 79 from rfl, pow_add]; norm_num
  rw [this]
  have : (105 : ℝ) * (2 : ℝ) ^ 79 < 2048 * (2 : ℝ) ^ 79 :=
    mul_lt_mul_of_pos_right (by norm_num) h79
  linarith

/-- **The crossover is strictly increasing past onset (the margin grows).**  If the vacuity
criterion holds at order `r` with `n > 1`, it holds at `r + 1` too — the gap `n^{r−1}` outgrows
`(2r−1)‼·√q` (the double factorial grows like `(2r)^r`, sub-exponentially in `r·ln n` for fixed
`n > 1` once past the onset `r₀ = 1 + β/2`).  Concretely we prove the monotone step under the
explicit gap hypothesis that the per-step LHS growth `n` beats the per-step RHS growth
`(2r+1)(2r−1)/((2r−1)) = (2r+1)`... — stated as the clean sufficient inequality
`(2·r + 1 : ℝ) ≤ n`, which holds at the prize point (`n = 2³⁰ ≫ 2r+1` for all `r ≤ log q`). -/
theorem vacuityCriterion_step {n q : ℝ} (hn : 1 < n) (hq : 0 ≤ q) (r : ℕ) (hr : 1 ≤ r)
    (hstep : (2 * (r : ℝ) + 1) ≤ n)
    (h : VacuityCriterion n q r) : VacuityCriterion n q (r + 1) := by
  unfold VacuityCriterion at h ⊢
  have hn0 : 0 < n := lt_trans one_pos hn
  -- (2(r+1)-1)!! = (2r+1)!! = (2r+1) * (2r-1)!!
  have hdf_step : (Nat.doubleFactorial (2 * (r + 1) - 1) : ℝ)
      = (2 * (r : ℝ) + 1) * (Nat.doubleFactorial (2 * r - 1) : ℝ) := by
    -- Nat-level identity: (2(r+1)-1)!! = (2r+1) * (2r-1)!!.
    have eNat : Nat.doubleFactorial (2 * (r + 1) - 1)
        = (2 * r + 1) * Nat.doubleFactorial (2 * r - 1) := by
      have e1 : 2 * (r + 1) - 1 = (2 * r - 1) + 2 := by omega
      rw [e1, Nat.doubleFactorial_add_two]
      congr 1
      omega
    rw [eNat]
    push_cast
    ring
  -- n^((r+1)-1) = n^r = n * n^(r-1)
  have hLHS_step : n ^ ((r + 1) - 1) = n * n ^ (r - 1) := by
    have : (r + 1) - 1 = (r - 1) + 1 := by omega
    rw [this, pow_succ]; ring
  rw [hLHS_step, hdf_step]
  -- want: n * n^(r-1) > (2r+1)*(2r-1)!! * sqrt q
  -- have h: n^(r-1) > (2r-1)!! sqrt q; and hstep: 2r+1 <= n.
  set A : ℝ := (Nat.doubleFactorial (2 * r - 1) : ℝ) * Real.sqrt q with hA
  have hApos : 0 ≤ A := by
    apply mul_nonneg
    · exact_mod_cast Nat.zero_le _
    · exact Real.sqrt_nonneg q
  -- (2r+1)*(2r-1)!! * sqrt q = (2r+1) * A
  have hgoalR : (2 * (r : ℝ) + 1) * (Nat.doubleFactorial (2 * r - 1) : ℝ) * Real.sqrt q
      = (2 * (r : ℝ) + 1) * A := by rw [hA]; ring
  rw [hgoalR]
  -- n * n^(r-1) > n * A  ≥  (2r+1) * A  (since n ≥ 2r+1 and A ≥ 0), and n*n^(r-1) > n*A from h.
  have h1 : n * n ^ (r - 1) > n * A := by
    apply mul_lt_mul_of_pos_left h hn0
  have h2 : (2 * (r : ℝ) + 1) * A ≤ n * A := mul_le_mul_of_nonneg_right hstep hApos
  linarith

end ArkLib.ProximityGap.Frontier.C5MonodromyMaxControlScissors

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.C5MonodromyMaxControlScissors.effErr_gt_wickBudget_of_vacuityCriterion
#print axioms ArkLib.ProximityGap.Frontier.C5MonodromyMaxControlScissors.vacuityCriterion_of_log
#print axioms ArkLib.ProximityGap.Frontier.C5MonodromyMaxControlScissors.prize_point_vacuous_at_four
#print axioms ArkLib.ProximityGap.Frontier.C5MonodromyMaxControlScissors.vacuityCriterion_step
