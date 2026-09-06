/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (R192 half-turn autocorrelation consumer)
-/
import Mathlib

/-!
# R192 (#466): half-turn autocorrelation consumer

R191's paired product-MGF budget is an autocorrelation of the observable
`f_j = exp(X_j / 8)` on the quotient cycle of child cosets.  This file proves
the deterministic finite-average identity:

```text
avg f_j g_j = mean(f) * mean(g) + avg (f_j-mean(f))*(g_j-mean(g)).
```

In the dyadic application `g_j = f_{j+M/2}`.  The analytic target is then a
half-turn covariance bound, or equivalently an even/odd Fourier-energy
imbalance.  This file makes that reduction exact without claiming the
finite-field covariance estimate.
-/

open Finset

namespace ArkLib.ProximityGap.Frontier.R192HalfTurnAutocorrelationConsumer

/-- Finite mean over a nonempty finset, normalized by cardinality. -/
noncomputable def mean {ι : Type*} (s : Finset ι) (f : ι → ℝ) : ℝ :=
  (∑ i ∈ s, f i) / (s.card : ℝ)

/-- Centered covariance-style average over a finite set. -/
noncomputable def centeredProductMean {ι : Type*}
    (s : Finset ι) (f g : ι → ℝ) : ℝ :=
  (∑ i ∈ s, f i * g i) / (s.card : ℝ) - mean s f * mean s g

/-- **Finite autocorrelation decomposition.**  The average product is the
product of means plus the centered product average. -/
theorem productMean_eq_mean_mul_mean_add_centered {ι : Type*}
    (s : Finset ι) (f g : ι → ℝ) (hcard : (s.card : ℝ) ≠ 0) :
    (∑ i ∈ s, f i * g i) / (s.card : ℝ) =
      mean s f * mean s g + centeredProductMean s f g := by
  unfold centeredProductMean
  ring

/-- If the half-turn/paired covariance is non-positive and both one-sided
means are bounded by `B`, then the paired product budget is bounded by `B²`.

This is the R192 proof target in consumer form: control the means by the
one-level chi-square MGF law and prove non-positive (or sufficiently small)
half-turn covariance. -/
theorem productMean_le_sq_of_centered_nonpos {ι : Type*}
    (s : Finset ι) (f g : ι → ℝ) {B : ℝ}
    (hcard : (s.card : ℝ) ≠ 0)
    (hf : mean s f ≤ B) (hg : mean s g ≤ B)
    (hB : 0 ≤ B)
    (hf_nonneg : 0 ≤ mean s f)
    (hcov : centeredProductMean s f g ≤ 0) :
    (∑ i ∈ s, f i * g i) / (s.card : ℝ) ≤ B ^ 2 := by
  rw [productMean_eq_mean_mul_mean_add_centered s f g hcard]
  have hmul : mean s f * mean s g ≤ B * B := by
    by_cases hg_nonneg : 0 ≤ mean s g
    · exact mul_le_mul hf hg hg_nonneg hB
    · have hprod_nonpos : mean s f * mean s g ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hf_nonneg (le_of_not_ge hg_nonneg)
      have hsq_nonneg : 0 ≤ B * B := mul_nonneg hB hB
      exact hprod_nonpos.trans hsq_nonneg
  nlinarith [hcov, hmul]

end ArkLib.ProximityGap.Frontier.R192HalfTurnAutocorrelationConsumer

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.R192HalfTurnAutocorrelationConsumer.productMean_eq_mean_mul_mean_add_centered
#print axioms ArkLib.ProximityGap.Frontier.R192HalfTurnAutocorrelationConsumer.productMean_le_sq_of_centered_nonpos
