/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (R191 product-MGF fixed point consumer)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R168DyadicTailEnvelopeConsumer

/-!
# R191 (#466): product-MGF fixed point target for the dyadic tower

R190 observed that the paired child product budget consumed by R168 is not
merely below the required constant `2`; empirically it converges to the
real-Gaussian fixed point `4/3`:

```text
  avg_i exp((left_i + right_i) / 8) ≈ 4/3.
```

For independent `χ²₁` child magnitudes this is exactly
`(1 - 4*(1/8))⁻¹ = 4/3`.  This file names the sharper residual and proves the
already-needed R168 consequence.  The residual itself remains the open
finite-field equidistribution/MGF theorem.
-/

open Finset
open Real

namespace ArkLib.ProximityGap.Frontier.R191ProductMGFFixedPointConsumer

open ArkLib.ProximityGap.Frontier.R168DyadicTailEnvelopeConsumer

/-- **Sharper dyadic product-MGF residual.**  The paired child spectrum has
the real-Gaussian product budget `4/3` at rate `1/8`. -/
def DyadicProductMGFFourThirds {ι : Type*}
    (s : Finset ι) (left right : ι → ℝ) : Prop :=
  (∑ i ∈ s, Real.exp ((1 / 8 : ℝ) * left i) *
    Real.exp ((1 / 8 : ℝ) * right i)) ≤ (4 / 3 : ℝ) * (s.card : ℝ)

/-- The `4/3` fixed-point budget is stronger than the R168 product budget
constant `2`. -/
theorem dyadicTailMGF_of_productMGF_fourThirds {ι : Type*}
    (s : Finset ι) (parent left right : ι → ℝ)
    (hparent : ∀ i ∈ s, parent i ≤ left i + right i)
    (hprod : DyadicProductMGFFourThirds s left right) :
    DyadicTailMGFBound s parent := by
  refine dyadicTailMGF_of_tower_product_budget s parent left right hparent ?_
  calc
    (∑ i ∈ s, Real.exp ((1 / 8 : ℝ) * left i) *
        Real.exp ((1 / 8 : ℝ) * right i))
        ≤ (4 / 3 : ℝ) * (s.card : ℝ) := hprod
    _ ≤ 2 * (s.card : ℝ) := by
      have hcard : 0 ≤ (s.card : ℝ) := by exact_mod_cast Nat.zero_le s.card
      nlinarith

/-- Downstream prize-square consumer with the sharper `4/3` product-MGF
residual exposed directly. -/
theorem prize_sq_of_productMGF_fourThirds {ι : Type*}
    (s : Finset ι) (parent left right : ι → ℝ)
    {Mmax n Q : ℝ} {r : ℕ}
    (hparent : ∀ i ∈ s, parent i ≤ left i + right i)
    (hprod : DyadicProductMGFFourThirds s left right)
    (hMmax : 0 ≤ Mmax) (hn : 0 ≤ n) (hQ : 0 < Q)
    (ht : ∀ b ∈ s, 0 ≤ parent b) (hP : 0 < (s.card : ℝ))
    (hr : 1 ≤ r) (hrQ : Real.log Q ≤ r)
    (hmoment : Mmax ^ (2 * r) ≤
      Q * (n ^ r * ((∑ b ∈ s, (parent b) ^ r) / (s.card : ℝ)))) :
    Mmax ^ 2 ≤ 2 * Real.exp 1 * (2 / (1 / 8 : ℝ)) * n * (r : ℝ) := by
  exact prize_sq_of_dyadicTailMGF s parent hMmax hn hQ ht hP hr hrQ
    (dyadicTailMGF_of_productMGF_fourThirds s parent left right hparent hprod)
    hmoment

end ArkLib.ProximityGap.Frontier.R191ProductMGFFixedPointConsumer

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.R191ProductMGFFixedPointConsumer.dyadicTailMGF_of_productMGF_fourThirds
#print axioms ArkLib.ProximityGap.Frontier.R191ProductMGFFixedPointConsumer.prize_sq_of_productMGF_fourThirds
