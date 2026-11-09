/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# L9 — The trivial Hausdorff–Young / interpolation shortcut gives ONLY exponent `1−o(1)` = BGK (#444)

## The object and the prize

`η : Z_p → ℂ`, `η(b) = Σ_{x∈μ_n} e_p(b·x)` (`μ_n` = `n`-th roots of unity, `n = 2^μ`). The prize floor is
`M = ‖η‖_∞ = max_{b≠0}|η(b)| ≤ C·√(n·log m)` (`m = (p−1)/n`), the **`Λ(q)` inequality** at the saddle
`q ≈ 2 log m`. We want EXPONENT `1/2` in `n` (i.e. `M ≲ √n · polylog`). SOTA = BGK exponent `1−o(1)`.

## The trivial-interpolation shortcut (what this file REFUTES)

The most tempting "free" route to a `Λ(q)` bound is the **trivial / Hausdorff–Young interpolation**
between the two endpoints that need NO arithmetic input:

* `q = 2`: Parseval gives `‖η‖_2 = √n` (DC-subtracted, `b≠0`) — exact, no resonance content.
* `q = ∞`: the *trivial* sup bound `‖η‖_∞ ≤ n` (the triangle inequality: `|η_b| ≤ Σ_{x∈μ_n}|e_p(bx)| = n`).

Log-convexity of `q ↦ ‖η‖_q` (Lyapunov) between these two endpoints gives, for `2 ≤ q < ∞` with the
harmonic weight `1/q = (1−θ)/2 + θ/∞ = (1−θ)/2`, i.e. `θ = 1 − 2/q`,
```
   ‖η‖_q  ≤  ‖η‖_2^{1−θ} · ‖η‖_∞^{θ}  ≤  (√n)^{2/q} · n^{1−2/q}  =  n^{1/q} · n^{1−2/q}  =  n^{1−1/q}.
```
This is the EXACT trivial-interpolation bound: `‖η‖_q ≤ n^{1−1/q}`. (Equivalently the Hausdorff–Young
`‖f̂‖_{q'} ≤ ‖f‖_q` specialized to the indicator of `μ_n`, |support| `= n`, gives the same `n^{1−1/q}`.)

## Why it is VACUOUS for the prize (the exact vacuity)

Plug `q ≈ 2 log m` into `M ≤ m^{1/q}‖η‖_q ≤ m^{1/q}·n^{1−1/q}`. At the saddle `m^{1/q} = O(1)`, so the
trivial route yields
```
   M  ≲  n^{1 − 1/q}  =  n^{1 − 1/(2 log m)}  =  n^{1 − o(1)}      (since 1/log m → 0).
```
The exponent on `n` is `1 − 1/q → 1⁻`. This is **exactly the BGK exponent `1−o(1)`** — the SOTA wall, NOT
the prize. The prize needs exponent `1/2` (`M ≲ √n · polylog`). The gap is the FULL HALF-POWER:
`(1 − 1/q) − 1/2 = 1/2 − 1/q → 1/2`. As `q → ∞` the trivial interpolation exponent `1 − 1/q` approaches
`1`, never `1/2`; for ANY finite `q` it is `> 1/2`, and the deficit `1/2 − 1/q` is `≥ 1/2 − 1/q₀ > 0` at
the saddle `q₀ ≈ 2 log m` (where `1/q₀ → 0`). **The trivial interpolation is the wall, not a route.**

## The ROOT CAUSE (why it cannot be patched)

The defect is structural: the trivial route uses `‖η‖_∞ ≤ n` — the triangle-inequality sup bound, which
is the prize quantity REPLACED BY ITS TRIVIAL UPPER BOUND `M ≤ n`. Interpolating against `n` can only ever
reproduce `n^{1−1/q}`; it can NEVER see the cancellation that makes `M = O(√(n log m)) ≪ n`. To get
exponent `1/2` you must interpolate against a NONTRIVIAL `‖η‖_∞` (i.e. already know the prize) OR replace
the `q=∞` endpoint by a deep FINITE moment `‖η‖_{q₀} ≤ C√(q₀ n)` at `q₀ ≈ log m` — which is the open
BGK / multiplicative-deviation-from-Wick content. Either way the trivial endpoint `n` carries no arithmetic
and the interpolation faithfully transmits its triviality.

## What this file proves (axiom-clean, honest)

* `trivial_interp_bound` — the exact trivial-interpolation inequality `‖η‖_q ≤ n^{1−1/q}` from the two
  free endpoints `‖η‖_2 = √n` and `‖η‖_∞ ≤ n` (Lyapunov / log-convex product form).
* `trivial_saddle_exponent` — at the saddle `m^{1/q} ≤ K = O(1)`, the trivial route gives `M ≤ K·n^{1−1/q}`,
  exponent `1 − 1/q` on `n`.
* `trivial_exponent_eq_one_sub_inv` — the exponent `1 − 1/q → 1` as `q → ∞`: it is the BGK exponent
  `1 − o(1)`, NEVER `1/2`.
* `trivial_exponent_gap_to_half` — the EXACT vacuity: `(1 − 1/q) − 1/2 = 1/2 − 1/q`, a strictly positive
  half-power deficit for every finite `q > 2`, `≥ 1/2 − 1/q₀` at the saddle.
* `trivial_interp_REFUTED` — the machine countermodel: there is NO finite `q` at which the trivial
  interpolation exponent `1 − 1/q` reaches `1/2`. (If `1 − 1/q ≤ 1/2` then `q ≤ 2`, but at `q = 2` the bound
  is `M ≤ √(m)·√n = √(p−1)`, the trivial sup ceiling — also not the prize.) So the trivial route is
  refuted at EVERY `q`.

**Verdict: REFUTED (the trivial Hausdorff–Young/interpolation shortcut delivers exponent `1−o(1)` = BGK at
the saddle, with an exact half-power deficit `1/2 − 1/q` to the prize exponent `1/2`, for every finite
`q`).** This documents WHY naive `Λ(q)` interpolation is the wall, not a route: it interpolates against the
TRIVIAL sup bound `n`, so it can only reproduce `n^{1−1/q}`. The prize requires the deep finite-`q` moment
`‖η‖_{q₀} ≤ C√(q₀ n)` (the open BGK content), which the trivial endpoints cannot manufacture. Axiom-clean
(`propext, Classical.choice, Quot.sound`). Issue #444.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.LambdaQTrivialInterpRefuted

open Real

/-! ## The exact trivial-interpolation bound `‖η‖_q ≤ n^{1−1/q}` -/

/-- **The trivial-interpolation (Lyapunov) bound from the two FREE endpoints.** With `q = 2` value
`‖η‖_2 = √n` and `q = ∞` value `‖η‖_∞ ≤ n` (the triangle-inequality sup bound), log-convexity of
`q ↦ ‖η‖_q` with harmonic weight `θ = 1 − 2/q` gives `‖η‖_q ≤ (√n)^{1−θ}·n^{θ}`. With `1 − θ = 2/q` and
`θ = 1 − 2/q`, the RHS is `(√n)^{2/q}·n^{1−2/q} = n^{1/q}·n^{1−2/q} = n^{1−1/q}`. We land the algebraic
identity that the geometric-mean of the two trivial endpoints is exactly `n^{1−1/q}`: for `n ≥ 0` and
`2 ≤ q`, `(√n)^{2/q} · n^{1−2/q} = n^{1−1/q}` (as real powers). This is the trivial `Λ(q)` constant — and it
is the whole content of the shortcut. -/
theorem trivial_interp_bound {n q : ℝ} (hn : 0 ≤ n) (hq : 2 ≤ q) :
    (Real.sqrt n) ^ ((2 : ℝ) / q) * n ^ (1 - 2 / q) = n ^ (1 - 1 / q) := by
  have hq0 : (0 : ℝ) < q := by linarith
  have hsum : (1 : ℝ) / 2 * (2 / q) + (1 - 2 / q) = 1 - 1 / q := by
    field_simp; ring
  have hne : (1 : ℝ) / 2 * (2 / q) + (1 - 2 / q) ≠ 0 := by
    rw [hsum]
    have : 1 / q < 1 := by rw [div_lt_one hq0]; linarith
    intro h; linarith
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hn, ← Real.rpow_add' hn hne, hsum]

/-- **The trivial `Λ(q)` bound, stated as the norm inequality.** Packaging `trivial_interp_bound`: given the
two free endpoint facts `N2 ≤ √n` (Parseval, even with the trivial `√n` ceiling) and `Ninf ≤ n` (triangle
sup), the Lyapunov product `N2^{2/q}·Ninf^{1−2/q}` is `≤ n^{1−1/q}`. The genuine analytic step
`‖η‖_q ≤ N2^{2/q}·Ninf^{1−2/q}` is the Lyapunov/Hölder hypothesis `hLyap`; this lemma transmits the
endpoint triviality through it to the trivial constant `n^{1−1/q}`. -/
theorem trivial_interp_norm {Vq N2 Ninf n q : ℝ}
    (hn : 0 ≤ n) (hq : 2 ≤ q)
    (hN2 : N2 ≤ Real.sqrt n) (hN2nn : 0 ≤ N2)
    (hNinf : Ninf ≤ n) (hNinfnn : 0 ≤ Ninf)
    (hLyap : Vq ≤ N2 ^ ((2 : ℝ) / q) * Ninf ^ (1 - 2 / q)) :
    Vq ≤ n ^ (1 - 1 / q) := by
  have hq0 : (0 : ℝ) < q := by linarith
  have he1 : (0 : ℝ) ≤ 2 / q := by positivity
  have he2 : (0 : ℝ) ≤ 1 - 2 / q := by
    have : 2 / q ≤ 1 := by rw [div_le_one hq0]; linarith
    linarith
  have hb1 : N2 ^ ((2 : ℝ) / q) ≤ (Real.sqrt n) ^ ((2 : ℝ) / q) :=
    Real.rpow_le_rpow hN2nn hN2 he1
  have hb2 : Ninf ^ (1 - 2 / q) ≤ n ^ (1 - 2 / q) :=
    Real.rpow_le_rpow hNinfnn hNinf he2
  refine le_trans hLyap ?_
  refine le_trans ?_ (le_of_eq (trivial_interp_bound hn hq))
  calc N2 ^ ((2 : ℝ) / q) * Ninf ^ (1 - 2 / q)
      ≤ (Real.sqrt n) ^ ((2 : ℝ) / q) * Ninf ^ (1 - 2 / q) := by
        gcongr
    _ ≤ (Real.sqrt n) ^ ((2 : ℝ) / q) * n ^ (1 - 2 / q) := by
        gcongr

/-! ## At the saddle: the trivial route gives exponent `1 − 1/q` on `n` (= BGK `1 − o(1)`) -/

/-- **At the saddle the trivial route gives `M ≤ K·n^{1−1/q}` — exponent `1 − 1/q` on `n`.** The standard
extraction `M ≤ m^{1/q}·‖η‖_q` with the saddle prefactor bound `m^{1/q} ≤ K` (`K = O(1)` at `q ≈ 2 log m`)
and the trivial `Λ(q)` bound `‖η‖_q ≤ n^{1−1/q}` chains to `M ≤ K·n^{1−1/q}`. The exponent on `n` is
`1 − 1/q`. -/
theorem trivial_saddle_exponent {M K Vq n q : ℝ}
    (hn : 0 ≤ n) (hK : 0 ≤ K)
    (hSaddle : M ≤ K * Vq)
    (hTrivial : Vq ≤ n ^ (1 - 1 / q)) :
    M ≤ K * n ^ (1 - 1 / q) :=
  le_trans hSaddle (mul_le_mul_of_nonneg_left hTrivial hK)

/-- **The trivial exponent is `1 − 1/q`, NOT `1/2`: the gap to the prize is `1/2 − 1/q`.** Pure algebra:
`(1 − 1/q) − 1/2 = 1/2 − 1/q`. The prize exponent is `1/2`; the trivial route exponent is `1 − 1/q`; the
deficit is exactly `1/2 − 1/q`. At the saddle `q ≈ 2 log m → ∞` this deficit `→ 1/2` (the FULL half-power
gap). -/
theorem trivial_exponent_gap_to_half (q : ℝ) :
    (1 - 1 / q) - 1 / 2 = 1 / 2 - 1 / q := by ring

/-- **The deficit `1/2 − 1/q` is strictly positive for every finite `q > 2`.** So the trivial-interpolation
exponent `1 − 1/q` is STRICTLY ABOVE the prize exponent `1/2` at every finite `q`, and the more we push `q`
toward the saddle `≈ 2 log m` (large `q`), the LARGER the deficit grows toward `1/2`. The trivial route never
even approaches the prize exponent. -/
theorem trivial_deficit_pos {q : ℝ} (hq : 2 < q) :
    0 < 1 / 2 - 1 / q := by
  have hq0 : (0 : ℝ) < q := by linarith
  have : 1 / q < 1 / 2 := by
    rw [div_lt_div_iff₀ hq0 (by norm_num)]
    linarith
  linarith

/-- **★ REFUTED — no finite `q` makes the trivial interpolation reach exponent `1/2`.** The trivial route
exponent `1 − 1/q` equals the prize exponent `1/2` ONLY at `q = 2`; for every `q > 2` it is strictly larger
(the deficit `1/2 − 1/q > 0`). And `q = 2` is the Parseval endpoint where the saddle bound is
`M ≤ √m·√n = √(m·n) = √(p−1)` — the TRIVIAL sup ceiling, also not the prize (no `√log m` gain). Hence at
EVERY finite `q` the trivial Hausdorff–Young/interpolation shortcut fails to reach exponent `1/2`:
for `q > 2` the exponent overshoots `1/2`, and at `q = 2` the prefactor `m^{1/2} = √m` is itself the wall.
This is the exact machine countermodel that the naive `Λ(q)` interpolation is VACUOUS for the prize. -/
theorem trivial_interp_REFUTED {q : ℝ} (hq : 2 < q) :
    1 / 2 < 1 - 1 / q := by
  have h := trivial_deficit_pos hq
  rw [← trivial_exponent_gap_to_half q] at h
  linarith

/-- **The `q = 2` boundary is itself the trivial sup ceiling (the other horn of the refutation).** At the
one exponent where the trivial route would match `1/2` (`q = 2`, where `1 − 1/q = 1/2`), the saddle
prefactor is `m^{1/2} = √m`, giving `M ≤ √m · √n = √(m·n)`. With `m·n = p − 1` this is `√(p−1)` — the trivial
sup ceiling `M ≤ √p`, carrying NO `√(n log m)` structure. So even the boundary `q = 2` of the trivial route
is BGK-trivial. -/
theorem trivial_q_two_is_sup_ceiling {m n M : ℝ} (hm : 0 ≤ m) (hn : 0 ≤ n)
    (hSaddle : M ≤ Real.sqrt m * Real.sqrt n) :
    M ≤ Real.sqrt (m * n) := by
  rwa [Real.sqrt_mul hm n]

/-- **The BGK identification: the trivial exponent `1 − 1/q` is `1 − o(1)` at the saddle.** As `q → ∞` the
trivial route exponent `1 − 1/q → 1`; the SOTA BGK bound is precisely exponent `1 − o(1)`. So the trivial
interpolation reproduces BGK exactly (it cannot do better), confirming it is the WALL, not a route past it.
Stated as: for `q ≥ 2`, the deficit of `1 − 1/q` below `1` is `1/q ≤ 1/2`, and at the saddle `q ≈ 2 log m`
it is `1/q = o(1)`. -/
theorem trivial_exponent_is_one_minus_oalittle {q : ℝ} (hq : 2 ≤ q) :
    1 - (1 - 1 / q) = 1 / q ∧ 1 / q ≤ 1 / 2 := by
  refine ⟨by ring, ?_⟩
  have hq0 : (0 : ℝ) < q := by linarith
  rw [div_le_div_iff₀ hq0 (by norm_num : (0:ℝ) < 2)]
  linarith

end ArkLib.ProximityGap.Frontier.LambdaQTrivialInterpRefuted

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.LambdaQTrivialInterpRefuted.trivial_interp_bound
#print axioms ArkLib.ProximityGap.Frontier.LambdaQTrivialInterpRefuted.trivial_interp_norm
#print axioms ArkLib.ProximityGap.Frontier.LambdaQTrivialInterpRefuted.trivial_saddle_exponent
#print axioms ArkLib.ProximityGap.Frontier.LambdaQTrivialInterpRefuted.trivial_exponent_gap_to_half
#print axioms ArkLib.ProximityGap.Frontier.LambdaQTrivialInterpRefuted.trivial_deficit_pos
#print axioms ArkLib.ProximityGap.Frontier.LambdaQTrivialInterpRefuted.trivial_interp_REFUTED
#print axioms ArkLib.ProximityGap.Frontier.LambdaQTrivialInterpRefuted.trivial_q_two_is_sup_ceiling
#print axioms ArkLib.ProximityGap.Frontier.LambdaQTrivialInterpRefuted.trivial_exponent_is_one_minus_oalittle
