import Mathlib

/-!
# R202: shift-permutation invariance for quarter-MGF sums

This tiny consumer isolates the purely finite-set part of the shifted-quarter route:
if the right-child score vector is the left-child score vector after a permutation
that preserves the index set, then the quarter-MGF sum is unchanged, hence the
`right ≤ left` side-condition used by R199/R200 is available.
-/

namespace ArkLib.ProximityGap.Frontier.R202ShiftPermutationQuarterSum

open Finset Real
open scoped BigOperators

variable {ι : Type*}

theorem sum_comp_perm_eq
    (s : Finset ι) (f : ι → ℝ) (e : Equiv.Perm ι)
    (hmap : ∀ i, e i ∈ s ↔ i ∈ s) :
    (∑ i ∈ s, f (e i)) = ∑ i ∈ s, f i := by
  exact Finset.sum_equiv e (fun i => (hmap i).symm) (fun _ _ => rfl)

theorem quarter_sum_eq_of_perm
    (s : Finset ι) (left right : ι → ℝ) (e : Equiv.Perm ι)
    (hmap : ∀ i, e i ∈ s ↔ i ∈ s)
    (hright : ∀ i ∈ s, right i = left (e i)) :
    (∑ i ∈ s, exp ((1 / 4 : ℝ) * right i))
      = ∑ i ∈ s, exp ((1 / 4 : ℝ) * left i) := by
  calc
    (∑ i ∈ s, exp ((1 / 4 : ℝ) * right i))
        = ∑ i ∈ s, exp ((1 / 4 : ℝ) * left (e i)) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [hright i hi]
    _ = ∑ i ∈ s, exp ((1 / 4 : ℝ) * left i) := by
          exact sum_comp_perm_eq s (fun i => exp ((1 / 4 : ℝ) * left i)) e hmap

theorem quarter_sum_le_of_perm
    (s : Finset ι) (left right : ι → ℝ) (e : Equiv.Perm ι)
    (hmap : ∀ i, e i ∈ s ↔ i ∈ s)
    (hright : ∀ i ∈ s, right i = left (e i)) :
    (∑ i ∈ s, exp ((1 / 4 : ℝ) * right i))
      ≤ ∑ i ∈ s, exp ((1 / 4 : ℝ) * left i) :=
  (quarter_sum_eq_of_perm s left right e hmap hright).le

end ArkLib.ProximityGap.Frontier.R202ShiftPermutationQuarterSum
