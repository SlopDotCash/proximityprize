/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (wf-K2)
-/
import Mathlib

/-!
# K2 — the Katz–Sarnak symmetry-type / extreme-value-statistics route returns the OPEN object (#444)

**NEGATIVE / guardrail brick (an honest reduction, NOT a closure).** Lane K2 asks whether the
Katz–Sarnak symmetry type of the Gauss-period family `{η_b}_{b ∈ F_p^*}`, together with the
extreme-value statistics of its random-matrix / Sato–Tate law, controls the prize sup

  `M(n) = max_{b ∈ F_p^*} |η_b|`,   `η_b = Σ_{x ∈ μ_n} e_p(b x)`,   `n = 2^μ`, `p ≡ 1 (mod n)`,

via the largest-eigenvalue law of the symmetry group (CUE/USp/SO), à la the maxima of `L`-functions.

## The honest verdict: REDUCES-TO-FENCE F0/F11 (extreme-value of the iid-Gaussian law = the open BGK target)

The research and the exact-arithmetic probe (`probe_wfHK2_logcorr_field.rs`, integer phase
accumulation, NOT float-FFT; multi-prime, prize-faithful `p ≡ 1 mod n`, `μ_n` proper, `β ≈ 4`)
settle it through three established facts, two of which are *new measurements* for this lane:

1. **The symmetry type is the COMPLEX GAUSSIAN with NO compact support edge** (already pinned by
   `probe_c31_satotate_support_edge.py`, DISPROOF_LOG C31): the normalized period `η_b/√n`
   equidistributes to the standard complex Gaussian as `p → ∞`. The probe confirms it: the excess
   kurtosis of `Re η_b` tends to `0` (`-0.10` at n=32 → `-0.035` at n=128). A Gaussian Sato–Tate
   law has **support all of `ℂ`** — there is no compact edge `[-2√n, 2√n]` to read a deterministic
   max off of, unlike a `USp`/`SO`/`SU(2)` semicircle. So "the symmetry-group edge bounds the max"
   is a *category error*: the law is unbounded; its "edge" is its **extreme value**, which is the
   open object, not a bound on it.

2. **The field `b ↦ log|η_b|` is WHITE NOISE, not log-correlated** (NEW, this lane). For the maxima
   of `ζ`/`L`-functions and the CUE characteristic polynomial, the *sharp* extreme-value law
   `max ≈ log N − (3/4)log log N` (Fyodorov–Hiary–Keating; Arguin–Belius–Bourgade
   arXiv:1602.08875; Paquette–Zeitouni) is **strictly sub-Gaussian** and is available **only
   because the field is log-correlated** (`Cov(log|P(θ)|, log|P(θ')|) ∼ −log|θ−θ'|`). The probe
   measures `Cov(log|η_b|, log|η_{b'}|)/Var` at archimedean lags `d = 1..256` **and** at 2-adic
   lags `v₂(b−b') = 0..7`: **all are `≈ 0`** (`|cov/var| < 0.04`, no `−ln d` slope) for every
   generic prime at n=32,64,128. The Gauss-period field carries **no log-correlation** (archimedean
   *or* 2-adic), so the FHK/ABB log-correlated-field machinery — the *only* route to a max sharper
   than the iid-Gaussian one — **does not apply**. (The lone exception, `p = 2^16+1` a Fermat
   prime, shows spurious correlation; it is non-generic and excluded by a second prime.)

3. **A white-noise Gaussian field over `m = (p−1)/n` cosets has extreme value `√(2n·log m)` —
   which IS the open BGK/Paley target.** With no log-correlation, the best available
   extreme-value prediction is the iid one: `max_b |η_b| ≈ √n · √(2 log m) = √(2n·log(p/n))`. The
   probe confirms the empirical max tracks `√(2n ln m)` (ratio `0.78–0.89`, rising with n) and
   *not* the FHK value (ratio falling, `0.35`). But `√(2n·log(p/n))` is precisely the
   conjectured prize floor `M(n) ≲ C√(n·log(p/n))`. **The extreme-value heuristic reproduces the
   open statement; it does not prove it.**

The decisive logical gap is the **upper-vs-lower asymmetry of extreme-value theory** (researched):
the resonance method (Soundararajan; Bober–Goldmakher arXiv:1109.1786 for character sums;
Bondarenko–Seip arXiv:1507.05840 for `ζ`) produces **LOWER** bounds on maxima (exhibits large
values) — it is *constructive*. There is **no** analogous *upper*-bound technique for the maximum
over a deterministic family; an iid-Gaussian-model upper bound (`P(max > t) ≤ m·P(|Z| > t/√n)`,
union/first-moment) is a **probabilistic** statement that holds *for a random field*, and turning
it into a deterministic bound for the *specific* arithmetic family `{η_b}` requires *exactly* the
quantitative `√q`-cancellation in short subgroup character sums that is the open BGK wall (fence
F0: 2nd-order arithmetic caps at Johnson `√n`; the `√log` excess is the rare-event tail invisible
to it). Equidistribution (Katz Sato–Tate, F-fence on C13/C14) is a `q → ∞` *averaged* limit for a
*fixed* sheaf; it gives the typical value, never the deterministic `max_b` over a *thin designed*
subgroup at *fixed* `q` (HORN-EFF, DISPROOF_LOG C13/C14/C31).

So K2 is **REDUCES-TO-FENCE F0/F11**: the symmetry-type extreme-value prediction *equals* the open
BGK object (F11 object-change synonym), and the only one-sided bound it could supply is the
union-bound upper tail of an *iid model*, whose transfer to the arithmetic family is the
2nd-order-blind Johnson wall (F0).

## What is proven here (axiom-clean)

The mathematical content that *is* a theorem — and the precise reason it does not close the prize —
is the **extreme-value reduction itself**, formalized abstractly over `ℝ`:

* `union_bound_extreme` — the iid/union (first-moment) extreme-value upper bound: if `m` values
  each exceed a threshold `t` with "probability" (normalized count) `≤ ρ`, the chance the max
  exceeds `t` is `≤ m·ρ`. This is the ONLY one-sided EVT handle, and it is a *probabilistic* (model)
  statement, not a bound on a fixed family.
* `gaussian_tail_threshold_is_sqrt_2logm` — solving `m·exp(−t²/(2σ²)) = 1` gives the iid-Gaussian
  extreme threshold `t = σ√(2 log m)`; with `σ² = n` (the second moment `Σ_x e_p(bx)` has variance
  `n`) this is `√(2n·log m)` — verbatim the open BGK target. The optimizer of the union bound IS
  the conjectured floor.
* `no_log_correlation_no_fhk_gain` — the structural gate: the FHK sub-Gaussian refinement
  (`max < σ√(2 log m)` by the `(3/4)log log` correction) requires a *strictly negative*
  log-covariance slope; under the measured white-noise hypothesis (covariance `0`) the refinement
  is unavailable and the iid threshold is the best the method gives. (Stated as: a field whose
  log-covariance is `0` at all nonzero lags admits no covariance-driven reduction below the iid
  extreme value.)

NONE of these is a bound on `M(n)`; together they show the route's *only* output is the open target.
All results `#print axioms ⊆ {propext, Classical.choice, Quot.sound}`; no `sorry`.

Issue #444 (lane K2). Probe: `scripts/probes/rust/probe_wfHK2_logcorr_field.rs`.
-/

open Finset

namespace ProximityGap.Frontier.K2KatzSarnakExtremeValue

/-! ### 1. The union / first-moment extreme-value bound — the ONLY one-sided EVT handle. -/

/--
**Union-bound extreme value (the iid first-moment upper tail).** Model the family `{η_b}` by `m`
"frequencies" `b : ι` (`|ι| = m`) and a per-frequency exceedance indicator `over b = 1` iff
`|η_b| > t`. If each exceedance "mass" is `≤ ρ` (the Gaussian tail at threshold `t`), then the
total exceedance count is `≤ m·ρ`. This is the entire one-sided content of extreme-value theory
applied to the family: `P(max_b |η_b| > t) ≤ m · P(|Z| > t/√n)`. It is a *probabilistic / model*
statement — the masses `ρ` are the model tail, not the deterministic arithmetic of `{η_b}`.

`gaussian_tail_threshold_is_sqrt_2logm` shows its optimizer is the open prize floor; this is the
formal core of why the EVT route returns the open object. -/
theorem union_bound_extreme {ι : Type*} [Fintype ι] (mass : ι → ℝ) (ρ : ℝ)
    (hmass : ∀ b, mass b ≤ ρ) :
    ∑ b, mass b ≤ (Fintype.card ι : ℝ) * ρ := by
  calc ∑ b, mass b ≤ ∑ _b : ι, ρ := Finset.sum_le_sum (fun b _ => hmass b)
    _ = (Fintype.card ι : ℝ) * ρ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/--
**The union-bound optimizer is the open BGK floor.** The iid-Gaussian extreme-value threshold is
the `t` solving `m · exp(−t²/(2σ²)) = 1`, i.e. `t = σ·√(2 log m)`. We verify the algebra: at
`t = σ·√(2 log m)` with `σ² = n` and `m ≥ 1`, the union-bound mass `m · exp(−t²/(2n))` equals `1`,
so the predicted max is exactly `√(2n·log m) = √(2n·log(p/n))` — verbatim the conjectured prize
floor. The "extreme-value statistics of the symmetry group" therefore output the open object. -/
theorem gaussian_tail_threshold_is_sqrt_2logm (m n : ℝ) (hm : 1 ≤ m) (hn : 0 < n) :
    m * Real.exp (-(Real.sqrt (2 * n * Real.log m))^2 / (2 * n)) = 1 := by
  have hlogm : 0 ≤ Real.log m := Real.log_nonneg hm
  have harg : 0 ≤ 2 * n * Real.log m := by positivity
  rw [Real.sq_sqrt harg]
  have h2n : (2 : ℝ) * n ≠ 0 := by positivity
  rw [show -(2 * n * Real.log m) / (2 * n) = -Real.log m by
        rw [neg_div]; congr 1; rw [mul_comm 2 n, mul_assoc, mul_div_assoc]
        rw [mul_div_assoc]; field_simp]
  rw [Real.exp_neg, Real.exp_log (by linarith : (0:ℝ) < m)]
  field_simp

/-! ### 2. The structural gate: no log-correlation ⟹ no FHK sub-Gaussian refinement. -/

/--
**White noise ⟹ no covariance-driven reduction below the iid extreme value.** The Fyodorov–Hiary–
Keating / Arguin–Belius–Bourgade sub-Gaussian max law (the only route to `max < σ√(2 log m)`)
requires a *strictly negative* log-covariance slope `Cov(log|η_b|, log|η_{b'}|) ∼ −log|b−b'| < 0`.
We abstract the available covariance information as a function `cov : ℕ → ℝ` of the lag, and the
"FHK reduction is available" hypothesis as `∃ d ≠ 0, cov d < 0` (a genuinely negative
correlation). The probe measures `cov d = 0` (white noise) at every nonzero lag, archimedean and
2-adic. Under that measured hypothesis, no negative-covariance lag exists, so the FHK reduction
premise fails: the method cannot beat the iid threshold. Formally: if `cov d = 0` for all `d ≠ 0`,
then there is no `d ≠ 0` with `cov d < 0`. -/
theorem no_log_correlation_no_fhk_gain (cov : ℕ → ℝ) (hwhite : ∀ d, d ≠ 0 → cov d = 0) :
    ¬ ∃ d, d ≠ 0 ∧ cov d < 0 := by
  rintro ⟨d, hd, hneg⟩
  rw [hwhite d hd] at hneg
  exact lt_irrefl 0 hneg

/--
**The lane verdict as a single implication.** Granting the measured structure (white-noise log-field,
Gaussian symmetry type), the extreme-value route offers exactly one one-sided handle — the iid
union bound — whose optimizer is the open floor. Concretely: the union-bound exceedance total over
`m` frequencies is `≤ m·ρ` (`union_bound_extreme`); balancing it to `1` at the Gaussian tail forces
the threshold `√(2n·log m)` (`gaussian_tail_threshold_is_sqrt_2logm`); and the only sharper
alternative (FHK) is gated off by the absence of negative log-correlation
(`no_log_correlation_no_fhk_gain`). So the method's sole quantitative output is the conjectured
floor `√(2n·log(p/n))` — the OPEN BGK object — never a proof of it. -/
theorem k2_route_returns_open_object {ι : Type*} [Fintype ι]
    (mass : ι → ℝ) (ρ : ℝ) (hmass : ∀ b, mass b ≤ ρ)
    (m n : ℝ) (hm : 1 ≤ m) (hn : 0 < n)
    (cov : ℕ → ℝ) (hwhite : ∀ d, d ≠ 0 → cov d = 0) :
    (∑ b, mass b ≤ (Fintype.card ι : ℝ) * ρ) ∧
    (m * Real.exp (-(Real.sqrt (2 * n * Real.log m))^2 / (2 * n)) = 1) ∧
    (¬ ∃ d, d ≠ 0 ∧ cov d < 0) :=
  ⟨union_bound_extreme mass ρ hmass,
   gaussian_tail_threshold_is_sqrt_2logm m n hm hn,
   no_log_correlation_no_fhk_gain cov hwhite⟩

#print axioms ProximityGap.Frontier.K2KatzSarnakExtremeValue.union_bound_extreme
#print axioms ProximityGap.Frontier.K2KatzSarnakExtremeValue.gaussian_tail_threshold_is_sqrt_2logm
#print axioms ProximityGap.Frontier.K2KatzSarnakExtremeValue.no_log_correlation_no_fhk_gain
#print axioms ProximityGap.Frontier.K2KatzSarnakExtremeValue.k2_route_returns_open_object

end ProximityGap.Frontier.K2KatzSarnakExtremeValue
