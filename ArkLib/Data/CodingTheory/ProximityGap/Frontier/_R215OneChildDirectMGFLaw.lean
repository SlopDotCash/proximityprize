/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (R215 one-child direct MGF law)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R202ShiftPermutationQuarterSum
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R214DirectChildMGFLaw

/-!
# R215 (#466): one-child direct MGF law under child permutation

R214 reduced the raw dyadic prize step to two direct child quarter-MGF laws.
In the intended dyadic tower, the two child normalized-square spectra should be
the same list after a quotient/frequency permutation.  This file records the
deterministic consumer: a single direct child-MGF law plus that permutation
datum supplies both child laws and hence the prize-square bound.
-/

open Finset
open Real

set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R215OneChildDirectMGFLaw

open ArkLib.ProximityGap.Frontier.R188QuarterMGFTowerConsumer
open ArkLib.ProximityGap.Frontier.R202ShiftPermutationQuarterSum
open ArkLib.ProximityGap.Frontier.R204PrizeTowerLargeIndex
open ArkLib.ProximityGap.Frontier.R214DirectChildMGFLaw

noncomputable section

/-- A right child whose normalized-square spectrum is a permutation of the left
child inherits the left direct child quarter-MGF law. -/
theorem largeIndexChildQuarterMGF_of_perm {ι : Type*}
    (s : Finset ι) (rawLeft rawRight : ι → ℝ) (σ : ℝ) (e : Equiv.Perm ι)
    (hmap : ∀ i, e i ∈ s ↔ i ∈ s)
    (hrightSq : ∀ i ∈ s, rawRight i ^ 2 / σ ^ 2 = rawLeft (e i) ^ 2 / σ ^ 2)
    (hLeft : LargeIndexChildQuarterMGFLaw s rawLeft σ) :
    LargeIndexChildQuarterMGFLaw s rawRight σ := by
  unfold LargeIndexChildQuarterMGFLaw at hLeft ⊢
  unfold DyadicQuarterMGFBound at hLeft ⊢
  exact (quarter_sum_le_of_perm s
    (fun b => rawLeft b ^ 2 / σ ^ 2)
    (fun b => rawRight b ^ 2 / σ ^ 2)
    e hmap hrightSq).trans hLeft

/-- Raw dyadic prize-tower step with only one direct child-MGF law, provided
the right child normalized-square spectrum is a permutation of the left. -/
theorem prize_sq_of_raw_dyadic_prizeTower_one_child_quarterMGF
    {ι : Type*}
    (s : Finset ι) (rawParent rawLeft rawRight : ι → ℝ) {σ : ℝ}
    (e : Equiv.Perm ι) (depth : ℕ) {Mmax n Q : ℝ} {r : ℕ}
    (hσ : 0 < σ)
    (hcard : s.card = DyadicTowerIndex PrizeTopIndex depth)
    (hrawParentNonneg : ∀ i ∈ s, 0 ≤ rawParent i)
    (hrawTriangle : ∀ i ∈ s, rawParent i ≤ rawLeft i + rawRight i)
    (hmap : ∀ i, e i ∈ s ↔ i ∈ s)
    (hrightSq : ∀ i ∈ s, rawRight i ^ 2 / σ ^ 2 = rawLeft (e i) ^ 2 / σ ^ 2)
    (hLeft : LargeIndexChildQuarterMGFLaw s rawLeft σ)
    (hMmax : 0 ≤ Mmax) (hn : 0 ≤ n) (hQ : 0 < Q)
    (hP : 0 < (s.card : ℝ))
    (hr : 1 ≤ r) (hrQ : Real.log Q ≤ r)
    (hmoment : Mmax ^ (2 * r) ≤
      Q * (n ^ r *
        ((∑ b ∈ s, (rawParent b ^ 2 / (2 * σ ^ 2)) ^ r) / (s.card : ℝ)))) :
    Mmax ^ 2 ≤ 2 * Real.exp 1 * (2 / (1 / 8 : ℝ)) * n * (r : ℝ) := by
  exact prize_sq_of_raw_dyadic_prizeTower_child_quarterMGF
    s rawParent rawLeft rawRight depth hσ hcard hrawParentNonneg
    hrawTriangle hLeft
    (largeIndexChildQuarterMGF_of_perm s rawLeft rawRight σ e hmap hrightSq hLeft)
    hMmax hn hQ hP hr hrQ hmoment

end

end ArkLib.ProximityGap.Frontier.R215OneChildDirectMGFLaw

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.R215OneChildDirectMGFLaw.largeIndexChildQuarterMGF_of_perm
#print axioms ArkLib.ProximityGap.Frontier.R215OneChildDirectMGFLaw.prize_sq_of_raw_dyadic_prizeTower_one_child_quarterMGF
