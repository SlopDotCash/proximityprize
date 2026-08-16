/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Positivity

set_option autoImplicit false

/-!
# D1 convolution-squaring bootstrap reduces to the Paley input

Issue #464 flagged arXiv:2606.24471 ("Discrepancy for Random Linear Codes") as a new-looking
handle: for a normalized test `f`, the mirrored self-convolution `F_f = f * f̌` squares Fourier
concentration, and iteration sends `α` to `α^(2^d)`.  This is powerful for random
linear codes because the starting test family is already `α`-Fourier-concentrated with
`α < 1` bounded away from one by product structure.

For the smooth-subgroup Paley core, the starting concentration of the normalized test
`1_{μ_n} / n` is exactly

```text
α = M(μ_n) / n,   M(μ_n) = max_{b ≠ 0} |Σ_{x∈μ_n} e_p(bx)|.
```

Thus the D1 bootstrap has no independent start: asking that the `d`-fold squared concentration be
below the `d`-fold squared prize threshold is logically equivalent to the original Paley bound.
The convolution operation amplifies an existing gap; it does not manufacture the first gap.

The Lean content below is deliberately abstract.  It records the load-bearing arithmetic of the
route: the map `α ↦ α^(2^d)` is order-reflecting on nonnegative reals, and the normalized
concentration inequality `M / n ≤ A` is the same as the house bound `M ≤ n * A`.
-/

namespace ArkLib.ProximityGap.Frontier.D1ConvolutionSquaring

/-- The `d`-fold concentration after iterating the mirrored self-convolution:
`α ↦ α^(2^d)`.  We use real powers to match the analytic notation in the paper. -/
noncomputable def squaredConcentration (α : ℝ) (d : ℕ) : ℝ :=
  α ^ ((2 : ℝ) ^ d)

/-- Iterated self-convolution does not hide the initial Fourier-concentration demand.  On
nonnegative reals, the `d`-fold squaring map is order-reflecting: a bound after squaring to depth
`d` is equivalent to the same bound before squaring, with both sides rooted by `2^d`. -/
theorem squaredConcentration_le_iff
    {α A : ℝ} (hα : 0 ≤ α) (hA : 0 ≤ A) (d : ℕ) :
    squaredConcentration α d ≤ squaredConcentration A d ↔ α ≤ A := by
  unfold squaredConcentration
  exact Real.rpow_le_rpow_iff hα hA (by positivity)

/-- For the normalized Paley test, bounding the starting concentration `M / n` by a target `A` is
exactly the original house bound `M ≤ n * A`. -/
theorem normalized_house_bound_iff
    {M n A : ℝ} (hn : 0 < n) :
    M / n ≤ A ↔ M ≤ n * A := by
  simpa [mul_comm] using (div_le_iff₀ hn : M / n ≤ A ↔ M ≤ A * n)

/-- **D1 reduction.**  If `M` is the Gauss-period house, `n` the subgroup size, and `A` the desired
normalized target, then the `d`-fold convolution-squared target

`(M / n)^(2^d) ≤ A^(2^d)`

is equivalent to the original Paley house bound `M ≤ n * A`.  Therefore the D1 bootstrap can be a
consumer of a Paley-strength starting estimate, but it is not an independent proof of that estimate
for the deterministic smooth subgroup. -/
theorem iterated_squared_bound_iff_house_bound
    {M n A : ℝ} (hM : 0 ≤ M) (hn : 0 < n) (hA : 0 ≤ A) (d : ℕ) :
    squaredConcentration (M / n) d ≤ squaredConcentration A d ↔ M ≤ n * A := by
  rw [squaredConcentration_le_iff (div_nonneg hM hn.le) hA d]
  exact normalized_house_bound_iff hn

/-- Contrapositive form for route audits: if the Paley house bound fails, then every finite
convolution-squaring depth fails at the correspondingly squared target. -/
theorem not_iterated_squared_bound_of_not_house_bound
    {M n A : ℝ} (hM : 0 ≤ M) (hn : 0 < n) (hA : 0 ≤ A) (d : ℕ)
    (hfail : ¬ M ≤ n * A) :
    ¬ squaredConcentration (M / n) d ≤ squaredConcentration A d := by
  exact mt (iterated_squared_bound_iff_house_bound hM hn hA d).mp hfail

/-! ## Axiom audit. -/
#print axioms squaredConcentration_le_iff
#print axioms normalized_house_bound_iff
#print axioms iterated_squared_bound_iff_house_bound
#print axioms not_iterated_squared_bound_of_not_house_bound

end ArkLib.ProximityGap.Frontier.D1ConvolutionSquaring
