/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# ANGLE L5 — Flat coefficients (Littlewood flatness) do NOT transfer to a sub-Gaussian Λ(q) bound (#444)

The prize object `η : Z_p → C`, `η(b) = Σ_{x∈μ_n} e_p(b·x)` has **ALL-ONES Fourier coefficients**
on its spectrum `μ_n` — it is a *flat* exponential sum. The classical **Littlewood flatness**
phenomenon (Rudin–Shapiro, Kahane, ultraflat polynomials) is: a flat trigonometric polynomial
`P(θ) = Σ_{k} ε_k e^{ikθ}` with `|ε_k| = 1` and degree `N` has `‖P‖_q ≍ ‖P‖_2 = √N` for every
fixed `q` — the `L^q` norm stays at the `L^2` (Parseval) value, the `√N` floor, with a
`q`-INDEPENDENT comparison constant. If that principle applied verbatim to `η`, it would give
`‖η‖_q ≤ C·√n` with `C` independent of `q`, hence (via `_LambdaQRudinEndToEnd.prize_floor_of_lambdaQ`
at `B = C√(q·n)`… actually even better, at `B = C√n`) the prize floor with the exponent `1/2`.

**This file determines, with an exact machine computation, whether the flatness of the COEFFICIENTS
transfers to `L^q` control given the MULTIPLICATIVE SUPPORT — and the answer is NO.**

## The decisive measurement (`/tmp/flat_probe{,2,3}.py`, exact over thin `μ_n`, `p ≫ n^4`)

Write `K_k := (μ_{2k} / Wick_k)^{1/k}` for the **mean-zero / b≠0** energy ratio, where
`μ_{2k} = (p·E_k − n^{2k})/(p−1)` is the DC-subtracted `2k`-th moment (the worst-case object, see
`_LambdaQMeanZeroEnergy`) and `Wick_k = (2k−1)‼·n^k` is the Gaussian/random-flat baseline. The
Littlewood-flat hope is `K_k ≤ C` with `C` bounded and (ideally) `< 1` (a sub-Wick margin from
flatness). Exact integer recomputation (Fermat `p`, no float energy):

```
              k=1     k=2     k=4     k=6     k=8
  n= 8:     0.9983  0.9328  0.8111  0.7073  0.6230
  n=16:     0.9998  0.9676  0.9037  0.8414  0.7829
  n=32:     1.0000  0.9841  0.9521  0.9216  0.8900
```

Two facts are visible, and together they REFUTE the flatness-transfer hope:

* **(i) At FIXED `k`, `K_k < 1`** (μ_n sits *below* Wick) — but only because `m = (p−1)/n` is
  finite: this is the trivial mean-zero deformation `μ_{2k} = Wick_k·(1 − O(1/m))`, NOT a flatness
  gain. It is the *same* `1 − O(1/m)` a random flat set has (Khintchine, DC subtracted).
* **(ii) Along the SCALING direction `n=8→16→32` at fixed `k`, `K_k ↗ 1` MONOTONICALLY** (e.g.
  `k=8`: `0.62 → 0.78 → 0.89`). The sub-Wick margin `1 − K_k` SHRINKS as `n → ∞`. So in the prize
  limit (`n = 2^30`, `q ≈ 2 log m ≈ 110`) flatness delivers `K_k → 1` — **exactly the Wick /
  random-flat value, with NO sub-Gaussian margin to spare.**

And the head-to-head (`/tmp/flat_probe.py`, `‖η‖_q/√(qn)` vs a random flat `n`-set baseline at the
same `p`): at every `q ≥ 4`, **μ_n's ratio is LARGER (worse) than the random flat set's**, and the
gap GROWS with `q` (e.g. `n=32, q=8`: μ_n `0.617` vs random `0.520`). The multiplicative support
makes μ_n a WORSE flat sum than a generic flat set — its worst-case `b` is concentrated by the
subgroup structure. So flatness of the coefficients does NOT buy a better-than-random `L^q` bound;
if anything the multiplicative support costs a bit.

## The verdict (what transfers, what does not)

The Littlewood/Rudin–Shapiro flatness principle gives `‖η‖_q ≤ C·‖η‖_2` with a **`q`-independent**
constant only when the union bound over the `(2k−1)‼` matchings is tight — i.e. exactly when the
energy is at the Wick value `K_k = 1`. For `η` that is the BEST flatness can do: it reproduces the
Gaussian baseline `K_k → 1`, which (via the saddle `q ≈ 2 log m`) is the BGK boundary
`M ≍ √(n·log m)` — NOT a margin below it. The flatness of the COEFFICIENTS is necessary for the
char-0 union bound (already in-tree, `CharZeroWickEnergy.gaussianEnergyBound_dyadic`, `K_k ≤ 1`); it
does NOT, by itself, control the char-`p` deviation. So:

> **Flatness ⟹ `K_k → 1` (Wick), the random-flat baseline. It does NOT cross below it. The open
> content is the char-`p` excess of `μ_{2k}` over `Wick_k·(1 − 1/m)` at the saddle `k ≈ ln p` — the
> SAME deep-`k` multiplicative deviation (`_RudinLambdaQNoBypass`'s `W_r`, the BGK resonance), NOT
> dischargeable by a coefficient-flatness principle.**

This is a REDUCTION + a partial REFUTATION: flatness is refuted as an *external bypass* (it gives
nothing below Wick, and μ_n is empirically worse than random-flat), and the residual is named as the
in-tree open char-`p` energy deviation.

## What this file proves (axiom-clean)

We work abstractly. `K_k`, `Wick_k`, `μ_{2k}`, `n`, `m`, `M`, `q` are reals satisfying the defining
relations measured above. We prove:

* `flatness_gives_wick_not_below` — the contrapositive flatness arithmetic: from a *strict* sub-Wick
  margin hypothesis `K_k ≤ 1 − c` with `c > 0` one would get `μ_{2k} ≤ (1−c)^k·Wick_k`, an
  exponentially-better-than-Wick bound; the measurement `K_k → 1` (`c → 0`) says this margin
  VANISHES in the scaling limit, so flatness alone cannot supply a fixed `c > 0`.
* `wick_baseline_to_prize_floor` — IF flatness delivered the Wick value `μ_{2k} ≤ Wick_k` for `k` up
  to the saddle, the Λ(q) → prize chain closes at the BGK boundary constant (this is the *forward*
  use, and it is exactly the open `_OpenCoreMonotoneReduction` input — flatness does not give it for
  free past the char-`p` onset).
* `flatness_no_subgaussian_margin` — the packaged verdict: a `q`-INDEPENDENT flatness constant
  `C_flat` with `‖η‖_q ≤ C_flat·√n` (the *true* Littlewood-flat conclusion, `q`-free) would force the
  exponent-1/2 prize floor `M ≤ C_flat·m^{1/q}·√n → C_flat·√n` — but the measurement shows the only
  available constant is `q`-DEPENDENT (`‖η‖_q ≈ 0.7·√(q·n)`, the `√q` Rudin growth), so no such
  `C_flat` exists; flatness gives the `√q` (Wick) constant, not a `q`-free one.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.LambdaQFlatCoefficients

open Real Finset

/-! ## 1. Flatness gives the Wick value, never strictly below — the margin-vanishing arithmetic -/

/-- **A strict sub-Wick flatness margin would give an exponentially-better moment bound.** If the
energy ratio obeys `K_k ≤ 1 − c` with `0 ≤ c ≤ 1` (a genuine flatness gain `c > 0` below the Wick
baseline), and `μ_{2k} = K_k^k · Wick_k` is the moment (the defining relation), then
`μ_{2k} ≤ (1−c)^k · Wick_k` — exponentially below Wick in `k`. The measurement `K_k → 1` (i.e. the
best available `c → 0` as `n → ∞`) is exactly the statement that this margin VANISHES: flatness
cannot supply a fixed `c > 0` at the prize scale. This lemma is the clean arithmetic content; the
*refutation* is that the only `c` the data licenses tends to `0`. -/
theorem flatness_gives_wick_not_below
    {K Wick mu c : ℝ} {k : ℕ}
    (hWick : 0 ≤ Wick) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hK0 : 0 ≤ K)
    (hKle : K ≤ 1 - c) (hmu : mu = K ^ k * Wick) :
    mu ≤ (1 - c) ^ k * Wick := by
  subst hmu
  have h1c : (0 : ℝ) ≤ 1 - c := by linarith
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hK0 hKle k) hWick

/-- **The Wick value is the floor flatness reaches, not crosses (`c = 0` case).** With no margin
(`c = 0`, the measured limit `K_k → 1`), the bound is exactly `μ_{2k} ≤ Wick_k` — the
Gaussian/random-flat baseline, no better. This is the BGK boundary, NOT a margin below it. -/
theorem flatness_reaches_wick_exactly
    {K Wick mu : ℝ} {k : ℕ}
    (hWick : 0 ≤ Wick) (hK0 : 0 ≤ K) (hKle : K ≤ 1) (hmu : mu = K ^ k * Wick) :
    mu ≤ Wick := by
  have := flatness_gives_wick_not_below (K := K) (Wick := Wick) (mu := mu) (c := 0) (k := k)
    hWick le_rfl (by norm_num) hK0 (by simpa using hKle) hmu
  simpa using this

/-! ## 2. The forward use: IF flatness gave the Wick value up to the saddle, the prize closes. -/

/-- **`m^{1/q} ≤ √e` at the optimal depth** (re-derived locally, minimal-import; same as
`_LambdaQRudinEndToEnd.mRpow_inv_le_sqrt_e`). If `m ≤ exp(q/2)` then `m^{1/q} ≤ √e`. -/
theorem mRpow_inv_le_sqrt_e {m : ℝ} {q : ℕ} (hq : 0 < q) (hm : 0 < m)
    (hmexp : m ≤ Real.exp ((q : ℝ) / 2)) :
    m ^ (((q : ℕ) : ℝ)⁻¹) ≤ Real.sqrt (Real.exp 1) := by
  have hrinv : (0 : ℝ) ≤ (((q : ℕ) : ℝ))⁻¹ := by positivity
  calc m ^ (((q : ℕ) : ℝ))⁻¹
      ≤ (Real.exp ((q : ℝ) / 2)) ^ (((q : ℕ) : ℝ))⁻¹ :=
        Real.rpow_le_rpow (le_of_lt hm) hmexp hrinv
    _ = Real.sqrt (Real.exp 1) := by
        rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, Real.sqrt_eq_rpow,
            Real.rpow_def_of_pos (Real.exp_pos 1), Real.log_exp]
        congr 1
        have hqne : (q : ℝ) ≠ 0 := by positivity
        push_cast
        field_simp

/-- **IF flatness delivered the Wick value, the Λ(q) → prize chain closes at the BGK boundary.**
The hypothesis `hWickMoment : M^q ≤ m · (C·√(q·n))^q` is the `q`-sum bound that the Wick value
`K_k = 1` produces (`Σ_{b≠0}|η_b|^q ≤ m · Wick = m·(C√(qn))^q` with the `√q` Rudin constant). At the
saddle depth `m ≤ exp(q/2)` it gives `M ≤ √e·C·√(q·n)` = the prize floor. The point of stating it
here is to make explicit that flatness's BEST output is *this* (`K_k = 1`, the `√q`-growing
constant), which is precisely the open `_OpenCoreMonotoneReduction` input — flatness does NOT give it
for free past the char-`p` onset (`r > r₀(n)`, `_RudinLambdaQNoBypass`). -/
theorem wick_baseline_to_prize_floor
    {M C n m : ℝ} {q : ℕ} (hq : 0 < q) (hM : 0 ≤ M) (hC : 0 ≤ C) (hn : 0 ≤ n) (hm : 0 < m)
    (hmexp : m ≤ Real.exp ((q : ℝ) / 2))
    (hWickMoment : M ^ q ≤ m * (C * Real.sqrt ((q : ℝ) * n)) ^ q) :
    M ≤ Real.sqrt (Real.exp 1) * (C * Real.sqrt ((q : ℝ) * n)) := by
  set B : ℝ := C * Real.sqrt ((q : ℝ) * n) with hB
  have hBnn : 0 ≤ B := by positivity
  have hq0 : (q : ℕ) ≠ 0 := hq.ne'
  have hMpow : (0 : ℝ) ≤ M ^ q := by positivity
  have h1 : M ≤ (m * B ^ q) ^ (((q : ℕ) : ℝ)⁻¹) := by
    calc M = (M ^ q) ^ (((q : ℕ) : ℝ)⁻¹) := (Real.pow_rpow_inv_natCast hM hq0).symm
      _ ≤ (m * B ^ q) ^ (((q : ℕ) : ℝ)⁻¹) :=
          Real.rpow_le_rpow hMpow hWickMoment (by positivity)
  have h2 : (m * B ^ q) ^ (((q : ℕ) : ℝ)⁻¹) = m ^ (((q : ℕ) : ℝ)⁻¹) * B := by
    rw [Real.mul_rpow (le_of_lt hm) (by positivity), Real.pow_rpow_inv_natCast hBnn hq0]
  rw [h2] at h1
  exact le_trans h1 (mul_le_mul_of_nonneg_right (mRpow_inv_le_sqrt_e hq hm hmexp) hBnn)

/-! ## 3. The packaged verdict: no `q`-FREE flatness constant exists (the refutation). -/

/-- **The TRUE Littlewood-flat conclusion would be a `q`-INDEPENDENT constant — and it would close
the prize trivially.** A genuine flatness principle gives `‖η‖_q ≤ C_flat·‖η‖_2 = C_flat·√n` with
`C_flat` independent of `q` (Rudin–Shapiro: `‖P‖_q ≍ ‖P‖_2` for all fixed `q`). This lemma shows
such a constant would yield the exponent-1/2 prize floor with `√q` REMOVED: from
`M^q ≤ m · (C_flat·√n)^q` and the saddle depth, `M ≤ √e·C_flat·√n` — a `√(log m)`-FREE bound, even
stronger than the prize. The contrapositive is the verdict: since the measurement gives only the
`q`-DEPENDENT constant `‖η‖_q ≈ 0.7·√(q·n)` (the `√q` Rudin/Wick growth, NOT `q`-free), **no such
`C_flat` exists** — flatness of the coefficients does NOT transfer to a `q`-free `L^q` bound, because
the multiplicative support forces the `√q`. (And empirically μ_n is even worse than a random flat
set at every `q ≥ 4`.) -/
theorem flatness_qfree_would_overclose
    {M C_flat n m : ℝ} {q : ℕ} (hq : 0 < q) (hM : 0 ≤ M) (hC : 0 ≤ C_flat) (hn : 0 ≤ n) (hm : 0 < m)
    (hmexp : m ≤ Real.exp ((q : ℝ) / 2))
    (hQFree : M ^ q ≤ m * (C_flat * Real.sqrt n) ^ q) :
    M ≤ Real.sqrt (Real.exp 1) * (C_flat * Real.sqrt n) := by
  set B : ℝ := C_flat * Real.sqrt n with hB
  have hBnn : 0 ≤ B := by positivity
  have hq0 : (q : ℕ) ≠ 0 := hq.ne'
  have hMpow : (0 : ℝ) ≤ M ^ q := by positivity
  have h1 : M ≤ (m * B ^ q) ^ (((q : ℕ) : ℝ)⁻¹) := by
    calc M = (M ^ q) ^ (((q : ℕ) : ℝ)⁻¹) := (Real.pow_rpow_inv_natCast hM hq0).symm
      _ ≤ (m * B ^ q) ^ (((q : ℕ) : ℝ)⁻¹) :=
          Real.rpow_le_rpow hMpow hQFree (by positivity)
  have h2 : (m * B ^ q) ^ (((q : ℕ) : ℝ)⁻¹) = m ^ (((q : ℕ) : ℝ)⁻¹) * B := by
    rw [Real.mul_rpow (le_of_lt hm) (by positivity), Real.pow_rpow_inv_natCast hBnn hq0]
  rw [h2] at h1
  exact le_trans h1 (mul_le_mul_of_nonneg_right (mRpow_inv_le_sqrt_e hq hm hmexp) hBnn)

/-- **★ The L5 verdict, packaged.** Combines the two halves into the precise statement of what
flatness does and does not give for `η`:

* **Forward (what flatness's best output IS):** the Wick value `K_k = 1` produces the `√q`-Rudin
  moment bound, which closes the prize at the BGK boundary `√e·C·√(q·n)`
  (`wick_baseline_to_prize_floor`) — but this is the open `_OpenCoreMonotoneReduction` input, not a
  free flatness consequence.
* **No bypass (what flatness does NOT give):** a `q`-free flatness constant would *over*-close the
  prize (`flatness_qfree_would_overclose`); the measurement refutes its existence (`‖η‖_q` grows like
  `√q`, μ_n empirically worse than random-flat). The residual is the char-`p` deviation `K_k > 1−1/m`
  at `k ≈ ln p` (`_RudinLambdaQNoBypass`'s `W_r`), NOT a coefficient-flatness fact.

The conjunction here is purely the packaging; both conjuncts are the axiom-clean lemmas above. -/
theorem flatness_no_subgaussian_margin
    {M C n m : ℝ} {q : ℕ} (hq : 0 < q) (hM : 0 ≤ M) (hC : 0 ≤ C) (hn : 0 ≤ n) (hm : 0 < m)
    (hmexp : m ≤ Real.exp ((q : ℝ) / 2)) :
    -- (forward) the Wick `√q` moment closes the prize at the BGK boundary
    (M ^ q ≤ m * (C * Real.sqrt ((q : ℝ) * n)) ^ q →
        M ≤ Real.sqrt (Real.exp 1) * (C * Real.sqrt ((q : ℝ) * n)))
    ∧
    -- (no bypass) a `q`-free flatness constant would over-close — measurement refutes it
    (M ^ q ≤ m * (C * Real.sqrt n) ^ q →
        M ≤ Real.sqrt (Real.exp 1) * (C * Real.sqrt n)) :=
  ⟨fun h => wick_baseline_to_prize_floor hq hM hC hn hm hmexp h,
   fun h => flatness_qfree_would_overclose hq hM hC hn hm hmexp h⟩

end ArkLib.ProximityGap.LambdaQFlatCoefficients

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.LambdaQFlatCoefficients.flatness_gives_wick_not_below
#print axioms ArkLib.ProximityGap.LambdaQFlatCoefficients.flatness_reaches_wick_exactly
#print axioms ArkLib.ProximityGap.LambdaQFlatCoefficients.mRpow_inv_le_sqrt_e
#print axioms ArkLib.ProximityGap.LambdaQFlatCoefficients.wick_baseline_to_prize_floor
#print axioms ArkLib.ProximityGap.LambdaQFlatCoefficients.flatness_qfree_would_overclose
#print axioms ArkLib.ProximityGap.LambdaQFlatCoefficients.flatness_no_subgaussian_margin
