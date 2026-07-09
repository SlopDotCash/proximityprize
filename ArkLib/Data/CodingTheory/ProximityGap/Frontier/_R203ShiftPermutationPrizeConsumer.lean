/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (R203 shift-permutation prize consumer)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R200ShiftedQuarterPrizeConsumer
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R202ShiftPermutationQuarterSum

/-!
# R203 (#466): prize consumer with the child shift-permutation exposed

R200 used an abstract inequality between the right and left child quarter-MGF
sums.  R202 proved that this inequality follows from the expected quotient-shift
structure: the right child is the left child after a permutation preserving the
sampled index set.

This file composes those two facts, so later finite-field work only has to prove
the actual child-spectrum permutation/equality and the one-child quarter-MGF
bound.
-/

open Finset
open Real

namespace ArkLib.ProximityGap.Frontier.R203ShiftPermutationPrizeConsumer

open ArkLib.ProximityGap.Frontier.R200ShiftedQuarterPrizeConsumer
open ArkLib.ProximityGap.Frontier.R202ShiftPermutationQuarterSum

/-- Shift-permutation child structure plus one left-child quarter-MGF budget
imply the R168 tail-MGF residual for the parent spectrum. -/
theorem dyadicTailMGF_of_shift_perm_quarter {ι : Type*}
    (s : Finset ι) (parent left right : ι → ℝ) (e : Equiv.Perm ι)
    (hparent : ∀ i ∈ s, parent i ≤ left i + right i)
    (hmap : ∀ i, e i ∈ s ↔ i ∈ s)
    (hright : ∀ i ∈ s, right i = left (e i))
    (hLeft :
      (∑ i ∈ s, Real.exp ((1 / 4 : ℝ) * left i)) ≤ 2 * (s.card : ℝ)) :
    ArkLib.ProximityGap.Frontier.R168DyadicTailEnvelopeConsumer.DyadicTailMGFBound
      s parent := by
  exact dyadicTailMGF_of_shifted_quarter s parent left right hparent
    (quarter_sum_le_of_perm s left right e hmap hright) hLeft

/-- Full prize-square consumer with the quotient-shift/permutation datum exposed
instead of the abstract right-child quarter-sum comparison. -/
theorem prize_sq_of_shift_perm_quarter {ι : Type*}
    (s : Finset ι) (parent left right : ι → ℝ) (e : Equiv.Perm ι)
    {Mmax n Q : ℝ} {r : ℕ}
    (hparent : ∀ i ∈ s, parent i ≤ left i + right i)
    (hmap : ∀ i, e i ∈ s ↔ i ∈ s)
    (hright : ∀ i ∈ s, right i = left (e i))
    (hLeft :
      (∑ i ∈ s, Real.exp ((1 / 4 : ℝ) * left i)) ≤ 2 * (s.card : ℝ))
    (hMmax : 0 ≤ Mmax) (hn : 0 ≤ n) (hQ : 0 < Q)
    (ht : ∀ b ∈ s, 0 ≤ parent b) (hP : 0 < (s.card : ℝ))
    (hr : 1 ≤ r) (hrQ : Real.log Q ≤ r)
    (hmoment : Mmax ^ (2 * r) ≤
      Q * (n ^ r * ((∑ b ∈ s, (parent b) ^ r) / (s.card : ℝ)))) :
    Mmax ^ 2 ≤ 2 * Real.exp 1 * (2 / (1 / 8 : ℝ)) * n * (r : ℝ) := by
  exact prize_sq_of_shifted_quarter s parent left right hparent
    (quarter_sum_le_of_perm s left right e hmap hright) hLeft
    hMmax hn hQ ht hP hr hrQ hmoment

end ArkLib.ProximityGap.Frontier.R203ShiftPermutationPrizeConsumer

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.R203ShiftPermutationPrizeConsumer.dyadicTailMGF_of_shift_perm_quarter
#print axioms ArkLib.ProximityGap.Frontier.R203ShiftPermutationPrizeConsumer.prize_sq_of_shift_perm_quarter
