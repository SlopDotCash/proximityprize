/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (R214 direct child MGF law)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R188QuarterMGFTowerConsumer
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R204PrizeTowerLargeIndex
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R209DyadicCauchyNormalization

/-!
# R214 (#466): direct child-MGF residual for the prize-index dyadic step

R212 packages the live concentration residual as a staircase/tail certificate.
That certificate is useful for one analytic route, but the downstream theorem
only consumes the two child quarter-MGF inequalities

```text
(1 / |s|) * sum_b exp((rawChild b)^2 / (4 * sigma^2)) <= 2.
```

This file names that direct residual and proves the raw dyadic prize-tower
consumer from it.  The remaining open analytic target is therefore the direct
large-index child-MGF law, matching the R206/R213 sampled evidence.
-/

open Finset
open Real

set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R214DirectChildMGFLaw

open ArkLib.ProximityGap.Frontier.R188QuarterMGFTowerConsumer
open ArkLib.ProximityGap.Frontier.R204PrizeTowerLargeIndex
open ArkLib.ProximityGap.Frontier.R209DyadicCauchyNormalization

noncomputable section

/-- Direct prize-index child concentration residual.  For a normalized child
spectrum `rawChild^2 / sigma^2`, this is precisely the quarter-rate MGF bound
needed by the dyadic tower consumer. -/
def LargeIndexChildQuarterMGFLaw {ι : Type*} (s : Finset ι)
    (rawChild : ι → ℝ) (σ : ℝ) : Prop :=
  DyadicQuarterMGFBound s (fun b => rawChild b ^ 2 / σ ^ 2)

/-- Unfolding lemma for the direct child-MGF law. -/
theorem childQuarterMGF_of_largeIndexChildQuarterMGFLaw {ι : Type*}
    (s : Finset ι) (rawChild : ι → ℝ) (σ : ℝ)
    (h : LargeIndexChildQuarterMGFLaw s rawChild σ) :
    DyadicQuarterMGFBound s (fun b => rawChild b ^ 2 / σ ^ 2) := by
  exact h

/-- Raw dyadic triangle plus the direct child quarter-MGF laws imply the
R168/S11 squared prize bound.  The `hcard` hypothesis records that the row is
on the actual prize-index tower; it is not used by the deterministic consumer,
but it is the intended scope of the analytic child-MGF law. -/
theorem prize_sq_of_raw_dyadic_prizeTower_child_quarterMGF
    {ι : Type*}
    (s : Finset ι) (rawParent rawLeft rawRight : ι → ℝ) {σ : ℝ}
    (depth : ℕ) {Mmax n Q : ℝ} {r : ℕ}
    (hσ : 0 < σ)
    (_hcard : s.card = DyadicTowerIndex PrizeTopIndex depth)
    (hrawParentNonneg : ∀ i ∈ s, 0 ≤ rawParent i)
    (hrawTriangle : ∀ i ∈ s, rawParent i ≤ rawLeft i + rawRight i)
    (hLeft : LargeIndexChildQuarterMGFLaw s rawLeft σ)
    (hRight : LargeIndexChildQuarterMGFLaw s rawRight σ)
    (hMmax : 0 ≤ Mmax) (hn : 0 ≤ n) (hQ : 0 < Q)
    (hP : 0 < (s.card : ℝ))
    (hr : 1 ≤ r) (hrQ : Real.log Q ≤ r)
    (hmoment : Mmax ^ (2 * r) ≤
      Q * (n ^ r *
        ((∑ b ∈ s, (rawParent b ^ 2 / (2 * σ ^ 2)) ^ r) / (s.card : ℝ)))) :
    Mmax ^ 2 ≤ 2 * Real.exp 1 * (2 / (1 / 8 : ℝ)) * n * (r : ℝ) := by
  let parentN : ι → ℝ := fun b => rawParent b ^ 2 / (2 * σ ^ 2)
  let leftN : ι → ℝ := fun b => rawLeft b ^ 2 / σ ^ 2
  let rightN : ι → ℝ := fun b => rawRight b ^ 2 / σ ^ 2
  have hparentN : ∀ i ∈ s, parentN i ≤ leftN i + rightN i := by
    intro i hi
    exact normalized_parent_sq_le_child_sq_sum hσ
      (hrawParentNonneg i hi) (hrawTriangle i hi)
  have htParent : ∀ b ∈ s, 0 ≤ parentN b := by
    intro b _
    unfold parentN
    positivity
  exact prize_sq_of_child_quarterMGF s parentN leftN rightN
    hparentN
    (childQuarterMGF_of_largeIndexChildQuarterMGFLaw s rawLeft σ hLeft)
    (childQuarterMGF_of_largeIndexChildQuarterMGFLaw s rawRight σ hRight)
    hMmax hn hQ htParent hP hr hrQ hmoment

end

end ArkLib.ProximityGap.Frontier.R214DirectChildMGFLaw

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.R214DirectChildMGFLaw.childQuarterMGF_of_largeIndexChildQuarterMGFLaw
#print axioms ArkLib.ProximityGap.Frontier.R214DirectChildMGFLaw.prize_sq_of_raw_dyadic_prizeTower_child_quarterMGF
