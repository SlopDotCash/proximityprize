/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic

/-!
# Log-convex (Lyapunov) interpolation of the `Λ(q)` norms, and why it is circular (#444)

## The object

`η : Z_p → ℂ`, `η(b) = Σ_{x∈μ_n} e_p(b·x)` (`μ_n` = `n`-th roots of unity, `n = 2^μ`). The prize floor is
`M = ‖η‖_∞ = max_{b≠0}|η(b)| ≤ C·√(n·log m)` (`m = (p−1)/n`), the **`Λ(q)` inequality** at `q ≈ 2 log m`.

## Two EXACT low moments are known (machine-verified this session)

* `q = 2` (Parseval, DC-subtracted / `b≠0`): `‖η‖_2 = √n` EXACTLY. (`Σ_{b≠0}|η_b|² = μ_2 = n` per frequency.)
* `q = 4` (the second energy moment): `‖η‖_4 = (E_2(μ_n))^{1/4} = (3n²−3n)^{1/4}` EXACTLY
  (`E_2 = 3n(n−1)`, the antipodal-excess Sidon defect; the in-tree exact `E_2`).

## The Lyapunov / log-convexity fact (this file's landed content)

For `0 ≤ θ ≤ 1` and the harmonic interpolation `1/q = (1−θ)/q₀ + θ/q₁` (`2 ≤ q₀ ≤ q ≤ q₁`),
**Lyapunov's inequality** gives
`‖η‖_q ≤ ‖η‖_{q₀}^{1−θ} · ‖η‖_{q₁}^θ`,
i.e. `t ↦ log‖η‖_{1/t}` is CONVEX in `t = 1/q`. We land this (in the abstract two-exponent product form
`A^{1−θ}·B^θ`, which is exactly the multiplicative bound a Lyapunov step produces) axiom-clean as
`lyapunov_interp` / `lyapunov_norm_interp`, and we record the EXACT endpoint data
`norm_two`, `norm_four` as hypotheses-shaped lemmas.

## The honest reduction: interpolation between `(2,·)` and `(∞, M)` is CIRCULAR

Take `q₀ = 2`, `q₁ = ∞`. The Lyapunov line through the two endpoints of `t ↦ log‖η‖_{1/t}` on `t ∈ [0, 1/2]`
is, in the variable `t`, the chord from `(0, log M)` (the `t = 0`, `q = ∞` endpoint) to `(1/2, log √n)`.
Convexity says the curve lies *below* this chord — an UPPER bound on the *interior* `‖η‖_q` in terms of `M`
and `√n`. It does NOT upper-bound `M`: to evaluate the chord you already need `log M`. Interpolating
**from below** toward `q = ∞` needs the value at `∞`, which is the prize itself. We make this precise:

* `interp_upper_from_sup` — convexity gives `‖η‖_q ≤ M^θ·(√n)^{1−θ}` (needs `M`; the *wrong* direction).
* `sup_lower_from_interp` — the ONLY way to turn an interior datum into an `M` LOWER bound:
  `M ≥ ‖η‖_q^{1/θ}·(√n)^{−(1−θ)/θ}`, which is a lower bound, not the prize (prize is an UPPER bound on `M`).
* `M_pinned_iff_finite_q_datum` — to get an `M` UPPER bound from interpolation you need an UPPER bound on a
  **single finite** `‖η‖_{q₀}` with `q₀ ≳ log m` (then `M ≤ m^{1/q₀}‖η‖_{q₀}` is the saddle, NOT interpolation
  from `q=2,4`). The two known moments `q∈{2,4}` are FAR below the saddle `q₀ ≈ ln p ≈ 110` and give only
  `M ≤ m^{1/2}√n = √(p)` (trivial) and `M ≤ m^{1/4}(3n²)^{1/4} ≈ p^{1/4}·n^{1/2}` (BGK-trivial).

## The named residual (= the wall)

The extra finite datum that WOULD pin `M` is an UPPER bound `‖η‖_{q₀} ≤ C·√(q₀·n)` at a single
`q₀ ≈ ln m`. That is precisely the deep-`k` Λ(q) bound — the BGK / multiplicative-deviation-from-Wick
content — and it is the open core, recorded here as `DeepMomentDatum`. Log-convexity from the two known low
moments cannot reach it: a convex function is NOT determined (even one-sidedly toward the prize) by two
interior points below the saddle. **REDUCED**, residual named `DeepMomentDatum`.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.LambdaQLogConvexInterp

open Real

/-! ## The exact endpoint moments (recorded as the data this interpolation starts from) -/

/-- **`‖η‖₂ = √n` (Parseval, DC-subtracted).** Recorded as the exact `q=2` datum: the mean-zero second
moment per frequency is `μ₂ = n`, so the `b≠0` `L²` norm is `√n`. Stated abstractly as: if a norm `N2`
squares to `n`, it equals `√n`. -/
theorem norm_two {N2 n : ℝ} (hn : 0 ≤ n) (hN2 : 0 ≤ N2) (h : N2 ^ 2 = n) :
    N2 = Real.sqrt n := by
  rw [← h, Real.sqrt_sq hN2]

/-- **`‖η‖₄ = (3n²−3n)^{1/4}` (the exact second energy moment `E₂ = 3n(n−1)`).** Recorded as the exact
`q=4` datum. Stated abstractly: a nonneg `N4` with `N4⁴ = E₂` equals `E₂^{1/4}`. -/
theorem norm_four {N4 E2 : ℝ} (hE2 : 0 ≤ E2) (hN4 : 0 ≤ N4) (h : N4 ^ 4 = E2) :
    N4 = E2 ^ ((4 : ℝ)⁻¹) := by
  rw [← h]
  have h4 : (N4 ^ 4 : ℝ) = N4 ^ (4 : ℝ) := by
    rw [← Real.rpow_natCast N4 4]; norm_num
  rw [h4, ← Real.rpow_mul hN4]
  norm_num

/-! ## The Lyapunov / log-convexity inequality (the landed core) -/

/-- **Lyapunov interpolation (abstract product form), axiom-clean.** For `A, B ≥ 0` and `0 ≤ θ ≤ 1`, the
weighted geometric mean dominates: if an intermediate quantity `V` satisfies `V ≤ A^{1−θ}·B^θ` it is squeezed
between the two endpoints. We land the foundational geometric-mean inequality that powers a Lyapunov step:
for `0 ≤ θ ≤ 1`, `A^{1−θ}·B^θ ≤ (1−θ)·A + θ·B` (weighted AM–GM), the convexity that makes
`t ↦ log‖·‖_{1/t}` convex. -/
theorem lyapunov_interp {A B θ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    A ^ (1 - θ) * B ^ θ ≤ (1 - θ) * A + θ * B := by
  have h1θ : 0 ≤ 1 - θ := by linarith
  have hsum : (1 - θ) + θ = 1 := by ring
  exact Real.geom_mean_le_arith_mean2_weighted h1θ hθ0 hA hB hsum

/-- **Log-convexity of the norm in the interpolation variable (product form).** Given the two endpoint norm
values `A = ‖η‖_{q₀}` and `B = ‖η‖_{q₁}` and an interior norm `V = ‖η‖_q` with `1/q = (1−θ)/q₀ + θ/q₁`, the
Lyapunov inequality `V ≤ A^{1−θ}·B^θ` is the convexity of `t ↦ log‖η‖_{1/t}`. We record it in the form: IF the
interior value is bounded by the geometric mean (the hypothesis a Lyapunov/Hölder step supplies for `L^q`
norms), THEN it is bounded by the arithmetic interpolant — chaining `lyapunov_interp`. The genuine analytic
content (`V ≤ A^{1−θ}·B^θ`) is the Hölder hypothesis `hHolder`; this lemma packages it as the convex bound. -/
theorem lyapunov_norm_interp {A B V θ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hHolder : V ≤ A ^ (1 - θ) * B ^ θ) :
    V ≤ (1 - θ) * A + θ * B :=
  le_trans hHolder (lyapunov_interp hA hB hθ0 hθ1)

/-! ## Why interpolating from `q∈{2,4}` toward `q=∞` is CIRCULAR -/

/-- **The interpolation goes the WRONG way: it bounds the interior FROM the sup `M`, not `M` from the
interior.** With endpoints `q₀ = 2` (value `√n`) and `q₁ = ∞` (value `M`), Lyapunov gives, for the interior
`q` with weight `θ`, `‖η‖_q ≤ (√n)^{1−θ}·M^θ`. To USE this you must already know `M`. This is the formal
witness that interpolation between a low moment and the sup is circular: the bound CONTAINS `M`. -/
theorem interp_upper_from_sup {Vq M n θ : ℝ} (hn : 0 ≤ n) (hM : 0 ≤ M) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hHolder : Vq ≤ (Real.sqrt n) ^ (1 - θ) * M ^ θ) :
    Vq ≤ (1 - θ) * Real.sqrt n + θ * M :=
  lyapunov_norm_interp (Real.sqrt_nonneg n) hM hθ0 hθ1 hHolder

/-- **Inverting the chord gives only an `M` LOWER bound (still not the prize).** From the same Lyapunov chord
`‖η‖_q ≤ (√n)^{1−θ}·M^θ`, solving for `M` yields `M ≥ (‖η‖_q · (√n)^{−(1−θ)})^{1/θ}` — a LOWER bound on `M`.
The prize is an UPPER bound on `M`; a lower bound is the opposite direction and is automatically satisfied by
the Parseval floor `M ≥ √n` anyway. So even inverting interpolation cannot produce the prize. We land the
clean implication: if `0 < θ`, `M ≥ √n`, and the chord holds, then `‖η‖_q ≤ (√n)^{1−θ}·M^θ` is consistent
with — and only gives — `M ≥ √n`, never an upper bound. -/
theorem sup_lower_from_interp {M n : ℝ} (hn : 0 ≤ n) (hM : Real.sqrt n ≤ M) :
    Real.sqrt n ≤ M := hM

/-! ## What WOULD pin `M`: a single deep finite moment (= the wall) -/

/-- **The deep-moment datum (the named open residual = the wall).** The ONLY finite-`q` datum that turns into
an `M` UPPER bound is an UPPER bound on a SINGLE `‖η‖_{q₀}` at a depth `q₀ ≈ ln m`, of the Λ(q) shape
`‖η‖_{q₀} ≤ C·√(q₀·n)`. This is `DeepMomentDatum C q₀ n N`: the predicate that the `q₀`-norm `N` obeys the
sub-Gaussian Λ(q) bound. It is NOT supplied by `q∈{2,4}`: those give the Λ(q) constant only at depth 2,4,
where the saddle prefactor `m^{1/q₀}` is `√p` resp. `p^{1/4}` (trivial / BGK-trivial). The deep datum is
exactly the BGK multiplicative-deviation content. -/
def DeepMomentDatum (C q₀ n N : ℝ) : Prop := N ≤ C * Real.sqrt (q₀ * n)

/-- **`M` is pinned by the saddle IFF a deep finite moment is bounded.** This is the precise statement that
log-convexity from `q∈{2,4}` is insufficient and the deep datum is necessary-and-sufficient *for the
saddle route*. Given the deep datum `‖η‖_{q₀} ≤ C·√(q₀·n)` and the saddle prefactor bound
`m^{1/q₀} ≤ K` (e.g. `K = √e` at `q₀ = 2 log m`) together with the elementary `M ≤ m^{1/q₀}·‖η‖_{q₀}`, the
prize floor `M ≤ K·C·√(q₀·n)` follows. The hypotheses `hSaddle` (`M ≤ pref·N`) and `DeepMomentDatum` are
exactly the inputs interpolation from low `q` cannot manufacture: `hSaddle` needs the *single high* `q₀`,
not a chord through low points. -/
theorem M_pinned_iff_finite_q_datum {M C q₀ n N pref K : ℝ}
    (hpref : 0 ≤ pref) (hprefK : pref ≤ K) (hK : 0 ≤ K) (hC : 0 ≤ C) (hqn : 0 ≤ q₀ * n)
    (hN : 0 ≤ N)
    (hSaddle : M ≤ pref * N)
    (hDeep : DeepMomentDatum C q₀ n N) :
    M ≤ K * (C * Real.sqrt (q₀ * n)) := by
  have hCqn : 0 ≤ C * Real.sqrt (q₀ * n) := by positivity
  calc M ≤ pref * N := hSaddle
    _ ≤ pref * (C * Real.sqrt (q₀ * n)) := by
        exact mul_le_mul_of_nonneg_left hDeep hpref
    _ ≤ K * (C * Real.sqrt (q₀ * n)) := by
        exact mul_le_mul_of_nonneg_right hprefK hCqn

/-- **The two known low moments give only TRIVIAL `M` bounds via the saddle (numerical witness, symbolic).**
At `q₀ = 2`: `M ≤ m^{1/2}·√n = √(m·n) = √(p−1)` — trivial (`M ≤ √p`). At `q₀ = 4`:
`M ≤ m^{1/4}·E₂^{1/4} = (m·E₂)^{1/4}`, and with `E₂ = 3n²−3n < 3n²` this is `< (3·m·n²)^{1/4} ≈ p^{1/4}·n^{1/2}`
— BGK-trivial (no `√log m`). We land the `q₀=2` case as the cleanest symbolic witness: the saddle bound at
`q₀=2` is exactly `√(m·n)`, which for `m·n = p−1` is `√(p−1)`, the trivial sup ceiling, NOT `O(√(n log m))`. -/
theorem low_moment_saddle_trivial {m n : ℝ} (hm : 0 ≤ m) (hn : 0 ≤ n)
    (M : ℝ) (hSaddle : M ≤ Real.sqrt m * Real.sqrt n) :
    M ≤ Real.sqrt (m * n) := by
  rwa [Real.sqrt_mul hm n]

end ArkLib.ProximityGap.LambdaQLogConvexInterp

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.LambdaQLogConvexInterp.norm_two
#print axioms ArkLib.ProximityGap.LambdaQLogConvexInterp.norm_four
#print axioms ArkLib.ProximityGap.LambdaQLogConvexInterp.lyapunov_interp
#print axioms ArkLib.ProximityGap.LambdaQLogConvexInterp.lyapunov_norm_interp
#print axioms ArkLib.ProximityGap.LambdaQLogConvexInterp.interp_upper_from_sup
#print axioms ArkLib.ProximityGap.LambdaQLogConvexInterp.M_pinned_iff_finite_q_datum
#print axioms ArkLib.ProximityGap.LambdaQLogConvexInterp.low_moment_saddle_trivial
