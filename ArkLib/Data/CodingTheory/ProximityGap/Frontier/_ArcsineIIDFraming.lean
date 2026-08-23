/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic

/-!
# The arcsine-iid framing — the cleanest probabilistic statement of the prize (#444)

The fleet's D3 finding (`_D3FiniteFreeFallingFactorial`): the Gauss period is a sum of `n/2` **antipodal
phase contributions**, `η_b = Σ_{k=1}^{n/2} Y_k`, `Y_k = 2cos(θ_k)`, and the char-0 energy matches the
moments of `n/2` IID ARCSINE variables (machine-verified: `Var(η)=16.00` vs `n=16`, `E[η⁴]=719` vs `720`).
The arcsine variable `Y = 2cos U` has the **Bessel MGF** `E[e^{Yy}] = I₀(2y) = Σ_k y^{2k}/(k!)² ≤
Σ_k y^{2k}/k! = exp(y²)` — i.e. it is SUB-GAUSSIAN with variance proxy `2` (in-tree
`_CharZeroMGFBesselBound.besselI0Two_le_exp_sq`).

So the prize has a clean probabilistic form: **IF the `n/2` phase contributions are INDEPENDENT** (the
joint MGF factorizes — the Gauss-sum phase equidistribution = the BGK wall), then `η_b` is sub-Gaussian
with variance proxy `n/2·2 = n`, and the Chernoff max bound (the fleet's D2 `chernoff_bound`) gives
  `M = max_{b≠0}|η_b| ≤ √(2·n·log m)`   (the prize floor, machine: `M/√(2n log m) = 0.77–0.85 < 1`).

This file lands the **composition**: (per-phase sub-Gaussian MGF `≤ exp(σ²y²/2)`) + (independence =
MGF factorization) ⟹ (sum sub-Gaussian, proxy `Σσ²`) ⟹ (via Chernoff, `M ≤ √(2·Σσ²·log m)`). The arcsine
instance (`σ²=2`, `n/2` terms) gives the prize floor. The single NAMED OPEN INPUT is the phase
independence (the wraparound = the dependence correction, machine-favorable `W_r/slack = 0.002`).
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.ArcsineIIDFraming

open Real Finset

/-- **The sub-Gaussian MGF of an independent sum factorizes and adds the variance proxies.** If the joint
MGF of `m` contributions factorizes as a product (the INDEPENDENCE hypothesis) and each factor is bounded
by its sub-Gaussian MGF `exp(σ_k²·y²/2)`, then the sum's MGF is `≤ exp((Σ σ_k²)·y²/2)` — sub-Gaussian with
the SUMMED variance proxy. This is the engine: independence + per-phase sub-Gaussianity ⟹ sum
sub-Gaussianity. (Here `mgfFactor k` stands for the `k`-th contribution's MGF `E[e^{Y_k y}]`.) -/
theorem subGaussian_of_independent_factors {m : ℕ} (y : ℝ) (σsq : ℕ → ℝ) (mgfFactor : ℕ → ℝ)
    (hpos : ∀ k ∈ Finset.range m, 0 ≤ mgfFactor k)
    (hfac : ∀ k ∈ Finset.range m, mgfFactor k ≤ Real.exp (σsq k * y ^ 2 / 2)) :
    ∏ k ∈ Finset.range m, mgfFactor k
      ≤ Real.exp ((∑ k ∈ Finset.range m, σsq k) * y ^ 2 / 2) := by
  calc ∏ k ∈ Finset.range m, mgfFactor k
      ≤ ∏ k ∈ Finset.range m, Real.exp (σsq k * y ^ 2 / 2) :=
        Finset.prod_le_prod hpos hfac
    _ = Real.exp (∑ k ∈ Finset.range m, σsq k * y ^ 2 / 2) := by rw [← Real.exp_sum]
    _ = Real.exp ((∑ k ∈ Finset.range m, σsq k) * y ^ 2 / 2) := by
        rw [Finset.sum_mul, Finset.sum_div]

/-- **The arcsine variance proxy: each antipodal phase contributes `σ² = 2`.** The arcsine variable
`Y = 2cos U` has MGF `I₀(2y) ≤ exp(y²) = exp(2·y²/2)`, i.e. sub-Gaussian variance proxy `2`. Summing the
`n/2` constant proxies `σ² ≡ 2` gives the period's total proxy `Σ = (n/2)·2 = n`. -/
theorem arcsine_total_variance_proxy (m : ℕ) :
    ∑ _k ∈ Finset.range m, (2 : ℝ) = 2 * m := by
  rw [Finset.sum_const, Finset.card_range]; ring

/-- **The arcsine-iid prize floor (the cleanest probabilistic form), assembled.** Given the period's
sub-Gaussian MGF `Φ(y) ≤ exp(V·y²/2)` with `V = n` (from per-phase arcsine sub-Gaussianity `σ²=2` over
`n/2 = m` independent phases, `Σσ² = 2m = n`), the Chernoff max bound gives the prize floor
`M ≤ √(2·V·log K) = √(2n·log K)`. We state the clean Chernoff consequence: from `cosh(M·y) ≤ K·exp(V·y²/2)`
for all `y ≥ 0` (the sub-Gaussian MGF at the binding frequency, `K = #frequencies`), the optimal
`y* = √(2 log K / V)` yields `M ≤ √(2·V·log K)`. The NAMED OPEN INPUT is the independence/MGF-factorization
(`subGaussian_of_independent_factors` needs the joint MGF to factorize = the Gauss-phase equidistribution =
the wraparound = the BGK wall). -/
theorem arcsine_prize_floor {M V K : ℝ} (hV : 0 < V) (hK : 1 < K) (hM : 0 ≤ M)
    (hmgf : ∀ y : ℝ, 0 ≤ y → M * y ≤ Real.log K + V * y ^ 2 / 2) :
    M ≤ Real.sqrt (2 * V * Real.log K) := by
  have hlogK : 0 < Real.log K := Real.log_pos hK
  have hVne : V ≠ 0 := ne_of_gt hV
  -- plug the saddle y = M/V directly, then clear denominators by ×(2V).
  have key := hmgf (M / V) (by positivity)
  have hMsq : M ^ 2 ≤ 2 * V * Real.log K := by
    have key2 := mul_le_mul_of_nonneg_right key (by positivity : (0:ℝ) ≤ 2 * V)
    rw [show M * (M / V) * (2 * V) = 2 * M ^ 2 from by field_simp,
        show (Real.log K + V * (M / V) ^ 2 / 2) * (2 * V) = 2 * V * Real.log K + M ^ 2 from by
          field_simp] at key2
    linarith
  -- M ≤ √(2V log K) from M² ≤ 2V log K and M ≥ 0.
  calc M = Real.sqrt (M ^ 2) := (Real.sqrt_sq hM).symm
    _ ≤ Real.sqrt (2 * V * Real.log K) := Real.sqrt_le_sqrt hMsq

end ArkLib.ProximityGap.ArcsineIIDFraming

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.ArcsineIIDFraming.subGaussian_of_independent_factors
#print axioms ArkLib.ProximityGap.ArcsineIIDFraming.arcsine_total_variance_proxy
#print axioms ArkLib.ProximityGap.ArcsineIIDFraming.arcsine_prize_floor
