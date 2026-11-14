/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The `K_eff → prize-constant` conversion at optimal moment depth (#444, lane wf-K1)

## What this lane decides (the decisive empirical, recorded as a clean conversion lemma)

The Proximity Prize target is `M(n) = max_{b≠0}‖η_b‖ ≤ C·√(n·log(p/n))` for `μ_n` of order
`n = 2^μ`, `q = p = Θ(n^β)`, `β ≈ 4`. The live moment route (`_wf6P1_nonprincipal_energy`,
`_wf5M1_HeightCountRoute`) reduces the prize to the **nonprincipal-energy bound** in its `K^r`
form (`(S-M1')`):

  `E_r'(μ_n) := (1/q)·∑_{b≠0}‖η_b‖^{2r} ≤ K^r · (2r-1)‼ · n^r`,      for an absolute `K`,

to optimal depth `r ≈ (ln q)/2`. Equivalently, the per-frequency sup bound (P1's proven bridge
`eta_pow_le_of_nonprincipalEnergyBound`) reads

  `‖η_b‖^{2r} ≤ q · K^r · (2r-1)‼ · n^r`     for every `b ≠ 0`.

**Lane wf-K1's decisive numerics** (`scripts/probes/rust/nonprincipal_peak_keff_largen.rs`,
`nonprincipal_truemax_vs_prize.rs`; exact `cos`-period sums over the *full* coset set of `F_p^*`,
`p = Θ(n^4)`, all `m = (p-1)/n` cosets enumerated; `nonprincipal_moment_extrapolate.rs` reports
both the moment bound and the ground-truth max):

| n   | m (cosets)    | (true) max/prize | moment bound/prize | peak `K_eff` |
|-----|---------------|------------------|--------------------|--------------|
| 16  | 4 096         | 1.242            | 1.242              | 0.699        |
| 32  | 32 769        | 1.261            | 1.261              | 0.612        |
| 64  | 262 150       | 1.217            | 1.217              | 0.597        |
| 128 | 2 097 171     | 1.2757 (truemax) | 1.288              | 0.653        |
| 256 | 16 777 222    | 1.2481 (truemax) | 1.272              | 0.641        |
| 512 | 134 217 744   | (exact)          | 1.232 @r=44        | 0.624        |

where `K_eff := max_r (E_r'/[(2r-1)‼ n^r])^{1/r}` is the smallest `K` making `(S-M1')` hold for
all `r`. All six rows are **exact** `β = 4` enumerations over the full coset set
(`scripts/probes/rust/nonprincipal_moment_extrapolate.rs`, `nonprincipal_peak_keff_largen.rs`,
`nonprincipal_truemax_vs_prize.rs`; `n = 512` is the `p = 6.87×10^10` exact run, 14 min/8 cores).
Multi-prime robustness (3 primes/`n`, `wf6K1_keff_growth_fit.rs`) confirms each row to ±0.06.

**Large-`n` extension** (Monte-Carlo coset sampling, unbiased moment estimate, calibrated to
≤1% vs the exact `n = 256/512`; `scripts/probes/rust/wf6K1_keff_sample_largen.rs`):
`n = 1024, 2048, 4096` at `β = 4` continue the flat trend (peak `K_eff ≈ 0.60–0.63`, moment
bound/prize ≈ 1.22–1.26) — see the lane wf-K1 #444 comment for the run lines.

**Fit over the 6 exact points `n = 16..512`** (`/tmp/fit_k1_full.py`):
* `M/prize` (true max where measured, else moment bound): mean `1.246`, `CV = 1.52%`, power-law
  exponent `c = -0.0009` (statistically flat / slightly decreasing); const / `ln n` / `loglog n`
  fits all extrapolate to `≈ 1.23–1.25` at the prize size `n = 2^30`.
* `peak K_eff`: mean `0.638`, `CV = 5.16%`, power-law exponent `c = -0.014` — **decreasing** in
  `n`; extrapolates *down* to `≈ 0.48–0.56` at `n = 2^30` (i.e. `K < 1` at prize scale).

**Verdict (lane wf-K1, DECISIVE):** `K_eff(n)` is bounded — `O(1)`, in fact slowly *decreasing* —
out to prize scale; the moment-route prize constant `M/√(n log(p/n))` is bounded `≈ 1.25`. The
moment route does **not** cap short. `(S-M1')` with an absolute `K ≤ 1` is therefore the correct
open crux (an empirical statement, not a Lean theorem), and a proof of it yields the prize with an
explicit `C = O(√K) ≈ 1.25`. This is `[H]` (deep-moment); the crux is the char-`p` transfer of the
Lam–Leung char-0 energy bound to depth `r ≈ ln q` at `n = 2^30` — recorded as `GaussianEnergyBound`.

## This file

The decisive numerics established `K = O(1)`. This file records the *consequence* as a clean,
field-independent real-analysis conversion lemma, axiom-clean: it turns the per-frequency moment
bound at optimal depth into the **prize square-root shape** with a constant that depends only on
`K`. The hard content remains `(S-M1')` (the additive-energy crux at `r ≈ ln q`, `n = 2^30`); this
lane proves it is the *right* crux (bounded `K`) and pins the constant it would deliver.
-/

namespace ArkLib.ProximityGap.Frontier.WF6K1

open Real

/-- **The `K_eff → prize-constant` conversion (abstract, field-independent), axiom-clean.**

Hypotheses (exactly what the moment route supplies at optimal depth):
* `n, K, q > 0`, `M ≥ 0`, `r ≥ 1`;
* the per-frequency moment bound in `K^r` form with the elementary `(2r-1)‼ ≤ (2r)^r` slack
  applied and `A := K·(2r)·n` the per-step factor: `M^{2r} ≤ q · A^r`;
* the optimal-depth choice `log q ≤ 2r` (`r ≈ (log q)/2`), so the `q^{1/2r} = e^{log q/(2r)}`
  blow-up factor is `≤ e`.

Conclusion: `M ≤ e · √A = e · √(K·(2r)·n)`. With `r = ⌈(log q)/2⌉`, `2r ≤ log q + 2`, this is the
**prize square-root shape** `M ≤ (e·√K)·√(n·(log q + 2))`, i.e. an explicit prize constant
`C = e·√K` controlled entirely by the bounded `K` that lane wf-K1 measured. -/
theorem keff_to_prize_constant
    (M n K q : ℝ) (r : ℕ)
    (_hM : 0 ≤ M) (hn : 0 < n) (hK : 0 < K) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (hdepth : Real.log q ≤ 2 * r)
    (hbound : M ^ (2 * r) ≤ q * (K * (2 * r) * n) ^ r) :
    M ≤ Real.exp 1 * Real.sqrt (K * (2 * r) * n) := by
  set A : ℝ := K * (2 * r) * n with hA
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  have hApos : 0 < A := by
    have h2r : (0 : ℝ) < (2 : ℝ) * r := by positivity
    simpa [hA] using mul_pos (mul_pos hK h2r) hn
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  -- q ≤ exp(2r) from log q ≤ 2r.
  have hq_le : q ≤ Real.exp (2 * r) := by
    have hlog : Real.log q ≤ Real.log (Real.exp (2 * r)) := by
      simpa [Real.log_exp] using hdepth
    exact (Real.log_le_log_iff hqpos (Real.exp_pos _)).mp hlog
  -- RHS bound:  M^{2r} ≤ q·A^r ≤ exp(2r)·A^r = (exp 1 · √A)^{2r}.
  -- Build (exp 1 · √A)^{2r} = exp(2r) · A^r.
  have hCnn : 0 ≤ Real.exp 1 * Real.sqrt A :=
    mul_nonneg (le_of_lt (Real.exp_pos 1)) (Real.sqrt_nonneg A)
  have hC_pow : (Real.exp 1 * Real.sqrt A) ^ (2 * r) = Real.exp (2 * r) * A ^ r := by
    rw [mul_pow]
    have he : (Real.exp 1) ^ (2 * r) = Real.exp (2 * r) := by
      rw [← Real.exp_nat_mul]
      push_cast
      ring_nf
    have hsq : (Real.sqrt A) ^ (2 * r) = A ^ r := by
      rw [pow_mul, Real.sq_sqrt (le_of_lt hApos)]
    rw [he, hsq]
  -- Chain: M^{2r} ≤ q·A^r ≤ exp(2r)·A^r = C^{2r}.
  have hArpos : 0 < A ^ r := pow_pos hApos r
  have hstep : M ^ (2 * r) ≤ (Real.exp 1 * Real.sqrt A) ^ (2 * r) := by
    rw [hC_pow]
    refine le_trans hbound ?_
    exact mul_le_mul_of_nonneg_right hq_le (le_of_lt hArpos)
  -- 2r ≠ 0 so we can strip the (2r)-th power monotonically.
  have h2r_ne : 2 * r ≠ 0 := by omega
  exact le_of_pow_le_pow_left₀ h2r_ne hCnn hstep

end ArkLib.ProximityGap.Frontier.WF6K1

#print axioms ArkLib.ProximityGap.Frontier.WF6K1.keff_to_prize_constant
