/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (R193 covariance slack consumer)
-/
import Mathlib

/-!
# R193 (#466): covariance slack consumer for the product-MGF route

R192 reduced the R191 product-MGF budget to a mean-square term plus a
half-turn covariance.  Exact non-positive covariance is stronger than needed:
the R168 consumer only needs the product budget to be at most `2`.

This file records the flexible deterministic consequence:

```text
mean(f) ≤ B, mean(g) ≤ B, covariance ≤ K, B² + K ≤ A
  ⟹ avg(f*g) ≤ A.
```

The intended numerical regime is `B² ≈ 4/3`, so even a large positive slack
`K < 2/3` would still close the R168 product budget.
-/

open Finset

namespace ArkLib.ProximityGap.Frontier.R193CovarianceSlackConsumer

/-- Finite mean over a nonempty finset, normalized by cardinality. -/
noncomputable def mean {ι : Type*} (s : Finset ι) (f : ι → ℝ) : ℝ :=
  (∑ i ∈ s, f i) / (s.card : ℝ)

/-- Product excess over independent means.  In R192 this is the half-turn
covariance when `g` is the half-turn shift of `f`. -/
noncomputable def centeredProductMean {ι : Type*}
    (s : Finset ι) (f g : ι → ℝ) : ℝ :=
  (∑ i ∈ s, f i * g i) / (s.card : ℝ) - mean s f * mean s g

/-- Product average decomposes as mean product plus covariance/excess. -/
theorem productMean_eq_mean_mul_mean_add_centered {ι : Type*}
    (s : Finset ι) (f g : ι → ℝ) :
    (∑ i ∈ s, f i * g i) / (s.card : ℝ) =
      mean s f * mean s g + centeredProductMean s f g := by
  unfold centeredProductMean
  ring

/-- **Covariance-slack product budget.**  If the two one-sided means are at
most `B` and the centered paired covariance is at most `K`, then the product
average is at most `B² + K`. -/
theorem productMean_le_sq_add_covSlack {ι : Type*}
    (s : Finset ι) (f g : ι → ℝ) {B K : ℝ}
    (hcard : (s.card : ℝ) ≠ 0)
    (hf : mean s f ≤ B) (hg : mean s g ≤ B)
    (hB : 0 ≤ B)
    (hf_nonneg : 0 ≤ mean s f)
    (hcov : centeredProductMean s f g ≤ K) :
    (∑ i ∈ s, f i * g i) / (s.card : ℝ) ≤ B ^ 2 + K := by
  rw [productMean_eq_mean_mul_mean_add_centered s f g]
  have hmul : mean s f * mean s g ≤ B * B := by
    by_cases hg_nonneg : 0 ≤ mean s g
    · exact mul_le_mul hf hg hg_nonneg hB
    · have hprod_nonpos : mean s f * mean s g ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hf_nonneg (le_of_not_ge hg_nonneg)
      have hsq_nonneg : 0 ≤ B * B := mul_nonneg hB hB
      exact hprod_nonpos.trans hsq_nonneg
  nlinarith [hmul, hcov]

/-- R168-shaped product budget with explicit slack target `A`. -/
theorem productMean_le_of_sq_add_covSlack_le {ι : Type*}
    (s : Finset ι) (f g : ι → ℝ) {A B K : ℝ}
    (hcard : (s.card : ℝ) ≠ 0)
    (hf : mean s f ≤ B) (hg : mean s g ≤ B)
    (hB : 0 ≤ B)
    (hf_nonneg : 0 ≤ mean s f)
    (hcov : centeredProductMean s f g ≤ K)
    (hbudget : B ^ 2 + K ≤ A) :
    (∑ i ∈ s, f i * g i) / (s.card : ℝ) ≤ A :=
  (productMean_le_sq_add_covSlack s f g hcard hf hg hB hf_nonneg hcov).trans hbudget

end ArkLib.ProximityGap.Frontier.R193CovarianceSlackConsumer

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.R193CovarianceSlackConsumer.productMean_le_sq_add_covSlack
#print axioms ArkLib.ProximityGap.Frontier.R193CovarianceSlackConsumer.productMean_le_of_sq_add_covSlack_le
