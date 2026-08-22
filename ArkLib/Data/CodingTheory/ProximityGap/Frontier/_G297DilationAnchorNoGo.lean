/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# G297: dilation anchors form a coset-constant zero-sum family

For a multiplicative subgroup `H <= F^*`, define

```text
W_a(t) = #{(y,z) in H^2 : a*y-z=t},
A_a(R) = q * sum_t W_a(t) R(t) - |H|^2 * sum_t R(t).
```

The coefficient-one profile is the canonical subgroup-difference autocorrelation; the target
weighted CORE profile has coefficient two. This file proves the structural obstruction to moving
between them:

* `W_{a*u}=W_a` for every `u in H`, so `A_a` factors through multiplicative cosets;
* `sum_a W_a(t)=|H|^2` at every additive coordinate;
* consequently `sum_a A_a(R)=0` for every row `R`;
* every nonzero full coefficient family therefore contains both positive and negative values.

The zero coefficient is a separate anchor and may carry one of those signs. The nonzero part factors
through multiplicative cosets, with total `-A_0`. Thus choosing between the distinguished `a=1` and
`a=2` cosets still requires their signed placement. Uniform shifted-subgroup intersection bounds do
not provide it.

The exact proper subgroup `mu_16 <= F_113^*` additionally refutes both distinguished sign transfers
at adjacent ranks:

```text
r=5: A_1=-2,977,296, A_2=+1,727,120;
r=6: A_1=  +152,176, A_2=   -77,440.
```

FS15-FS18 give fixed-depth almost-all-prime magnitude outside resultant bad sets. G64 forces the
sponsor exceptional by depth six, so they provide neither this coset placement nor the in-window
production-row sign. This is an unconditional route no-go, not a sponsor estimate or prize closure.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G297DilationAnchorNoGo

open Finset

section Structural

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable (H : Subgroup Fˣ) [Fintype H]

/-- The coefficient-`a` weighted relation profile, counted directly on `H x H`. -/
def weightedKernel (a t : F) : ℤ :=
  ∑ y : H, ∑ z : H,
    if a * (((y : H) : Fˣ) : F) - (((z : H) : Fˣ) : F) = t then 1 else 0

/-- The centered alignment of one dilation profile against an arbitrary integer row. -/
def anchorAlignment (R : F → ℤ) (a : F) : ℤ :=
  (Fintype.card F : ℤ) * ∑ t : F, weightedKernel H a t * R t -
    (Fintype.card H : ℤ) ^ 2 * ∑ t : F, R t

omit [Fintype F] in
/-- Multiplying the coefficient by an element of `H` merely reindexes the `y` variable. Hence the
complete weighted relation profile depends only on the multiplicative coset `aH`. -/
theorem weightedKernel_mul_right (u : H) (a t : F) :
    weightedKernel H (a * (((u : H) : Fˣ) : F)) t = weightedKernel H a t := by
  unfold weightedKernel
  refine Fintype.sum_equiv (Equiv.mulLeft u) _ _ ?_
  intro y
  simp only [Equiv.coe_mulLeft, Subgroup.coe_mul, Units.val_mul, mul_assoc]
  rfl

/-- The centered anchor value is likewise constant on multiplicative cosets. -/
theorem anchorAlignment_mul_right (u : H) (R : F → ℤ) (a : F) :
    anchorAlignment H R (a * (((u : H) : Fˣ) : F)) = anchorAlignment H R a := by
  unfold anchorAlignment
  simp_rw [weightedKernel_mul_right H u]

/-- For fixed `t`, every pair `(y,z) in H^2` determines exactly one coefficient
`a=(t+z)/y`. Summing the kernel profile over the whole field therefore gives `|H|^2`. -/
theorem sum_weightedKernel (t : F) :
    ∑ a : F, weightedKernel H a t = (Fintype.card H : ℤ) ^ 2 := by
  unfold weightedKernel
  rw [Finset.sum_comm]
  calc
    (∑ y : H, ∑ a : F, ∑ z : H,
        if a * (((y : H) : Fˣ) : F) - (((z : H) : Fˣ) : F) = t then 1 else 0) =
        ∑ y : H, ∑ z : H, ∑ a : F,
          if a * (((y : H) : Fˣ) : F) - (((z : H) : Fˣ) : F) = t then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.sum_comm]
    _ = ∑ _y : H, ∑ _z : H, (1 : ℤ) := by
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro z _
      have hy : ((((y : H) : Fˣ) : F)) ≠ 0 := Units.ne_zero _
      have heq (a : F) :
          a * (((y : H) : Fˣ) : F) - (((z : H) : Fˣ) : F) = t ↔
            a = (t + (((z : H) : Fˣ) : F)) / (((y : H) : Fˣ) : F) := by
        rw [sub_eq_iff_eq_add, eq_div_iff hy]
      simp_rw [heq]
      simp
    _ = (Fintype.card H : ℤ) ^ 2 := by simp; ring

/-- The full dilation-family alignment has exact mean zero. The principal mass cancels before any
estimate, so every attempted anchor comparison is a signed quotient-placement problem. -/
theorem sum_anchorAlignment (R : F → ℤ) :
    ∑ a : F, anchorAlignment H R a = 0 := by
  unfold anchorAlignment
  rw [Finset.sum_sub_distrib]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have hinner (t : F) :
      (∑ a : F, (Fintype.card F : ℤ) * (weightedKernel H a t * R t)) =
        (Fintype.card F : ℤ) * ((Fintype.card H : ℤ) ^ 2 * R t) := by
    rw [← Finset.mul_sum]
    congr 1
    rw [← Finset.sum_mul, sum_weightedKernel H]
  rw [Finset.sum_congr rfl (fun t _ => hinner t)]
  simp only [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/-- The nonzero coefficient sum is exactly the negative of the separate zero-coefficient anchor.
This is the precise quotient-family bookkeeping omitted by the full-family zero-sum identity. -/
theorem sum_nonzero_anchorAlignment (R : F → ℤ) :
    ∑ a ∈ (Finset.univ.erase (0 : F)), anchorAlignment H R a = -anchorAlignment H R 0 := by
  have h := sum_anchorAlignment H R
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : F))] at h
  omega

omit [Field F] [DecidableEq F] in
/-- A nonzero zero-sum finite family contains both signs. Applied to the full coefficient family,
including `a=0`, this shows that no nontrivial full dilation-anchor family can be globally
one-sided. -/
theorem zero_sum_nonzero_has_both_signs (A : F → ℤ)
    (hsum : ∑ a : F, A a = 0) (hne : ∃ a, A a ≠ 0) :
    (∃ a, 0 < A a) ∧ ∃ a, A a < 0 := by
  constructor
  · by_contra hpos
    push Not at hpos
    obtain ⟨a, ha⟩ := hne
    have hnonneg : ∀ x ∈ (Finset.univ : Finset F), 0 ≤ -A x := by
      intro x _
      exact neg_nonneg.mpr (hpos x)
    have hsumneg : ∑ x : F, -A x = 0 := by
      simp only [Finset.sum_neg_distrib, hsum, neg_zero]
    have hz : -A a = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsumneg a (Finset.mem_univ a)
    exact ha (by omega)
  · by_contra hneg
    push Not at hneg
    obtain ⟨a, ha⟩ := hne
    have hz : A a = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun x (_ : x ∈ (Finset.univ : Finset F)) => hneg x)).mp hsum a (Finset.mem_univ a)
    exact ha hz

/-- Structural anchor no-go: unless all coefficient alignments vanish, some coefficient is positive
and another is negative. This statement includes `a=0`; among nonzero coefficients, values are
constant on quotient classes and their total is controlled by `sum_nonzero_anchorAlignment`. -/
theorem anchor_family_has_both_signs (R : F → ℤ)
    (hne : ∃ a, anchorAlignment H R a ≠ 0) :
    (∃ a, 0 < anchorAlignment H R a) ∧ ∃ a, anchorAlignment H R a < 0 :=
  zero_sum_nonzero_has_both_signs (anchorAlignment H R) (sum_anchorAlignment H R) hne

end Structural

section ExactWitness

/-- Exact centered alignments for one field/subgroup/rank and coefficients `a=1,2`. -/
structure DilationAnchorCell where
  p : Nat
  n : Nat
  r : Nat
  A1 : Int
  A2 : Int
  deriving DecidableEq

/-- The exact coefficient-deformation contribution `A_2-A_1`. -/
def increment (c : DilationAnchorCell) : Int := c.A2 - c.A1

/-- `G=mu_16 <= F_113^*`, rank five. -/
def cell113r5 : DilationAnchorCell :=
  { p := 113, n := 16, r := 5, A1 := -2977296, A2 := 1727120 }

/-- The same field and subgroup, rank six. -/
def cell113r6 : DilationAnchorCell :=
  { p := 113, n := 16, r := 6, A1 := 152176, A2 := -77440 }

/-- At rank five the canonical difference anchor is negative while the target is positive. -/
theorem rankFive_anchor_negative_target_positive :
    cell113r5.A1 < 0 ∧ 0 < cell113r5.A2 ∧ increment cell113r5 = 4704416 := by
  norm_num [cell113r5, increment]

/-- At rank six the same anchor is positive while the target is negative. -/
theorem rankSix_anchor_positive_target_negative :
    0 < cell113r6.A1 ∧ cell113r6.A2 < 0 ∧ increment cell113r6 = -229616 := by
  norm_num [cell113r6, increment]

/-- No rank-uniform sign-preserving transport `A_1 >= 0 -> A_2 >= 0` can hold even on this one
proper dyadic subgroup. -/
theorem nonnegative_anchor_does_not_force_nonnegative_target :
    ∃ c : DilationAnchorCell, 0 < c.A1 ∧ c.A2 < 0 :=
  ⟨cell113r6, rankSix_anchor_positive_target_negative.1,
    rankSix_anchor_positive_target_negative.2.1⟩

/-- The reverse polarity also fails: a negative anchor can accompany a positive target. -/
theorem negative_anchor_does_not_force_negative_target :
    ∃ c : DilationAnchorCell, c.A1 < 0 ∧ 0 < c.A2 :=
  ⟨cell113r5, rankFive_anchor_negative_target_positive.1,
    rankFive_anchor_negative_target_positive.2.1⟩

/-- The two failures occur at the same prime and subgroup order, differing only in the adjacent
rank. The deformation term itself changes sign and exceeds the anchor margin in each direction. -/
theorem same_cell_adjacent_rank_transport_reversal :
    cell113r5.p = cell113r6.p ∧ cell113r5.n = cell113r6.n ∧
      cell113r5.r + 1 = cell113r6.r ∧ 0 < increment cell113r5 ∧ increment cell113r6 < 0 := by
  norm_num [cell113r5, cell113r6, increment]

end ExactWitness

#print axioms weightedKernel_mul_right
#print axioms anchorAlignment_mul_right
#print axioms sum_weightedKernel
#print axioms sum_anchorAlignment
#print axioms sum_nonzero_anchorAlignment
#print axioms zero_sum_nonzero_has_both_signs
#print axioms anchor_family_has_both_signs
#print axioms rankFive_anchor_negative_target_positive
#print axioms rankSix_anchor_positive_target_negative
#print axioms nonnegative_anchor_does_not_force_nonnegative_target
#print axioms negative_anchor_does_not_force_negative_target
#print axioms same_cell_adjacent_rank_transport_reversal

end ArkLib.ProximityGap.Frontier.G297DilationAnchorNoGo
