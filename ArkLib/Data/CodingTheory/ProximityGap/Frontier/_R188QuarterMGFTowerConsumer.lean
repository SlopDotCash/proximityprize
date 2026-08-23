/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (R188 quarter-MGF tower consumer)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R168DyadicTailEnvelopeConsumer

/-!
# R188 (#466): name the quarter-MGF residual used by the dyadic tower

R186 stress-tested the child-side exponential moment target

```text
  (1 / |s|) * Σ_i exp(parent_i / 4) ≤ 2.
```

R185 already proved that two such child-side bounds imply the paired product
budget needed by the R168 dyadic tail route.  This file gives that residual a
short Lean-facing name and exposes the exact consumer theorem:

```text
  left quarter-MGF + right quarter-MGF + parent ≤ left + right
    ⟹ DyadicTailMGFBound parent.
```

Status: concentration consumer only.  Residual = prove `DyadicQuarterMGFBound`
for actual dyadic Gauss-period child spectra.
-/

open Finset
open Real

namespace ArkLib.ProximityGap.Frontier.R188QuarterMGFTowerConsumer

open ArkLib.ProximityGap.Frontier.WFS11
open ArkLib.ProximityGap.Frontier.R168DyadicTailEnvelopeConsumer

/-- **Quarter-rate dyadic MGF residual.**  This is the R186 empirical target:
the normalized spectrum has exponential moment at rate `1/4` bounded by `2`. -/
def DyadicQuarterMGFBound {ι : Type*} (s : Finset ι) (t : ι → ℝ) : Prop :=
  MGFBound s t 2 (1 / 4)

/-- A quarter-MGF bound is literally the corresponding exponential-sum budget. -/
theorem quarterMGF_sum_budget {ι : Type*} (s : Finset ι) (t : ι → ℝ)
    (h : DyadicQuarterMGFBound s t) :
    (∑ i ∈ s, Real.exp ((1 / 4 : ℝ) * t i)) ≤ 2 * (s.card : ℝ) := by
  exact h

/-- **Named R186-to-R168 tower consumer.**  If the parent normalized magnitude
is pointwise bounded by the sum of two child normalized magnitudes, and both
children satisfy the quarter-MGF residual, then the parent satisfies the
conservative R168 tail-route residual at rate `1/8`. -/
theorem dyadicTailMGF_of_child_quarterMGF {ι : Type*}
    (s : Finset ι) (parent left right : ι → ℝ)
    (hparent : ∀ i ∈ s, parent i ≤ left i + right i)
    (hLeft : DyadicQuarterMGFBound s left)
    (hRight : DyadicQuarterMGFBound s right) :
    DyadicTailMGFBound s parent := by
  exact dyadicTailMGF_of_tower_amgm_mgf s parent left right hparent
    (quarterMGF_sum_budget s left hLeft)
    (quarterMGF_sum_budget s right hRight)

/-- The full downstream prize-square consumer with the quarter-MGF child
residuals exposed directly.  This keeps the new analytic target in the theorem
statement while reusing the already-audited R168/S11 layer-cake bridge. -/
theorem prize_sq_of_child_quarterMGF {ι : Type*}
    (s : Finset ι) (parent left right : ι → ℝ)
    {Mmax n Q : ℝ} {r : ℕ}
    (hparent : ∀ i ∈ s, parent i ≤ left i + right i)
    (hLeft : DyadicQuarterMGFBound s left)
    (hRight : DyadicQuarterMGFBound s right)
    (hMmax : 0 ≤ Mmax) (hn : 0 ≤ n) (hQ : 0 < Q)
    (ht : ∀ b ∈ s, 0 ≤ parent b) (hP : 0 < (s.card : ℝ))
    (hr : 1 ≤ r) (hrQ : Real.log Q ≤ r)
    (hmoment : Mmax ^ (2 * r) ≤
      Q * (n ^ r * ((∑ b ∈ s, (parent b) ^ r) / (s.card : ℝ)))) :
    Mmax ^ 2 ≤ 2 * Real.exp 1 * (2 / (1 / 8 : ℝ)) * n * (r : ℝ) := by
  exact prize_sq_of_dyadicTailMGF s parent hMmax hn hQ ht hP hr hrQ
    (dyadicTailMGF_of_child_quarterMGF s parent left right hparent hLeft hRight)
    hmoment

end ArkLib.ProximityGap.Frontier.R188QuarterMGFTowerConsumer

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.R188QuarterMGFTowerConsumer.quarterMGF_sum_budget
#print axioms ArkLib.ProximityGap.Frontier.R188QuarterMGFTowerConsumer.dyadicTailMGF_of_child_quarterMGF
#print axioms ArkLib.ProximityGap.Frontier.R188QuarterMGFTowerConsumer.prize_sq_of_child_quarterMGF
