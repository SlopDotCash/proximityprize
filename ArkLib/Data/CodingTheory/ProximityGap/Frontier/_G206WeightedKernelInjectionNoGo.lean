/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic.NormNum

/-!
# G206 no-go: collision-free weighted kernel support does not control late-Newton alignment (#466)

Shaw's late-Newton reduction uses

`W_G(t) = #{y ∈ G : 2y - t ∈ G}`

against the adjacent-rank profile `R_r(t)`.  For a cyclic subgroup `G` of order `n`, write
`z = 2y - t` and `u = z/y`.  Then

`u ∈ G`, `t = y(2-u)`, and `[t] = [2-u]` in `F_q^*/G`.

Consequently the nonzero orbit-class weights of `W_G` are exactly the fiber multiplicities of

`φ₂ : u ∈ G ↦ (2-u)^n`.

A collision in this map is the direct characteristic-`p` weighted kernel relation

`(2-u)^n = (2-v)^n`, equivalently `(2-u)/(2-v) = a ∈ G`, hence
`u - a v = 2(1-a)` for `u,v,a ∈ G`.

The strongest cheap structural case is that `φ₂` is injective.  Then every class weight is `0`
or `1`, its support has exactly `n` classes, and there are no weighted-kernel collisions at all.
This file records exact injective cells showing that even this maximal sparsity does not force a
favorable centered alignment:

* `F_113`, `n=8`: `A_5=-13128`, `A_6=-7240`;
* `F_2593`, `n=16`: `A_5=24201296`, `A_6=-13779712`;
* `F_3617`, `n=32`: `A_5=-17378716512`, `A_6=-132640776608`.

The `labels` stored below are the exact integer values `(2-u)^n mod q`, in subgroup power order.
Their `List.Nodup` proofs are kernel-checked.  The alignment constants are independently reproduced
by `scripts/probes/g206_weighted_kernel_injective_nogo.py`, using exact subgroup generation, exact
integer subset-sum histograms, and the identity

`A_r = q * Σ_t W_G(t)R_r(t) - n^2*C(n,r)*C(n,r-1)`.

Thus G205's sign no-go survives after imposing the strongest direct weighted-kernel relation
constraint.  Kernel collision counts and support sparsity do not control the placement of that
support against `R_5,R_6`.  A production proof still needs a signed joint-placement estimate, not
merely an exclusion or count of relations.  CORE remains open and on the BGK wall.

FS15-FS18 are respected: almost-all-prime resultant exclusion and simultaneous fixed-depth ladders
cannot select the production prime or reach logarithmic depth.  This result does not revive those
closed routes; it fences a different proposed escape at the actual weighted-kernel interface.
-/

namespace ArkLib.ProximityGap.Frontier.G206

/-- An exact late-alignment cell augmented by the quotient labels `(2-u)^n mod q` of its dyadic
subgroup elements `u`, listed in subgroup power order. -/
structure KernelAlignmentCell where
  /-- Prime field order. -/
  q : ℕ
  /-- Dyadic subgroup order. -/
  n : ℕ
  /-- Exact quotient labels `(2-u)^n mod q`, one for every `u ∈ G`. -/
  labels : List ℕ
  /-- Exact centered alignment at depth five. -/
  A5 : ℤ
  /-- Exact centered alignment at depth six. -/
  A6 : ℤ
  deriving DecidableEq

/-- The strongest weighted-kernel sparsity condition: there are exactly `n` labels and no two
subgroup inputs have the same quotient label.  Equivalently every nonzero class weight of `W_G`
is `0` or `1`. -/
def CollisionFree (c : KernelAlignmentCell) : Prop :=
  c.labels.length = c.n ∧ c.labels.Nodup

/-- `F_113`, order eight. -/
def cell113 : KernelAlignmentCell :=
  ⟨113, 8, [1, 16, 83, 85, 7, 64, 106, 112], -13128, -7240⟩

/-- `F_2593`, order sixteen. -/
def cell2593 : KernelAlignmentCell :=
  ⟨2593, 16,
    [1, 2008, 2389, 1170, 512, 1342, 2274, 483,
      328, 51, 1090, 2229, 2436, 585, 1767, 506],
    24201296, -13779712⟩

/-- `F_3617`, order thirty-two. -/
def cell3617 : KernelAlignmentCell :=
  ⟨3617, 32,
    [1, 98, 2353, 186, 3037, 1682, 3316, 772,
      2896, 251, 2813, 3534, 3179, 176, 19, 2071,
      2590, 985, 2040, 183, 769, 3272, 1303, 390,
      2182, 143, 361, 3564, 2488, 3176, 1485, 2360],
    -17378716512, -132640776608⟩

/-- The order-eight quotient map is injective. -/
theorem cell113_collisionFree : CollisionFree cell113 := by
  norm_num [CollisionFree, cell113]

/-- The order-sixteen quotient map is injective. -/
theorem cell2593_collisionFree : CollisionFree cell2593 := by
  norm_num [CollisionFree, cell2593]

/-- The order-thirty-two quotient map is injective. -/
theorem cell3617_collisionFree : CollisionFree cell3617 := by
  norm_num [CollisionFree, cell3617]

/-- Injective quotient support can have both late alignments negative. -/
theorem cell113_negative_alignment : cell113.A5 < 0 ∧ cell113.A6 < 0 := by
  norm_num [cell113]

/-- Injective quotient support can have mixed sign `(+, -)`. -/
theorem cell2593_mixed_alignment : 0 < cell2593.A5 ∧ cell2593.A6 < 0 := by
  norm_num [cell2593]

/-- A second injective quotient cell has both late alignments negative at larger subgroup order. -/
theorem cell3617_negative_alignment : cell3617.A5 < 0 ∧ cell3617.A6 < 0 := by
  norm_num [cell3617]

/-- The recorded exact injective-kernel census. -/
def recordedInjectiveCensus : List KernelAlignmentCell := [cell113, cell2593, cell3617]

/-- Every recorded cell has a collision-free weighted kernel. -/
theorem recorded_collisionFree (c : KernelAlignmentCell)
    (hc : c ∈ recordedInjectiveCensus) : CollisionFree c := by
  simp only [recordedInjectiveCensus, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with h | h | h
  · rw [h]
    exact cell113_collisionFree
  · rw [h]
    exact cell2593_collisionFree
  · rw [h]
    exact cell3617_collisionFree

/-- **Collision-free kernel support does not imply the depth-six positivity gate.** -/
theorem collisionFree_not_sufficient_for_A6_nonneg :
    ∃ c ∈ recordedInjectiveCensus, CollisionFree c ∧ c.A6 < 0 := by
  refine ⟨cell113, by simp [recordedInjectiveCensus], cell113_collisionFree, ?_⟩
  exact cell113_negative_alignment.2

/-- **Collision-free kernel support does not imply joint late-Newton positivity.**  The failure can
occur with both alignments negative. -/
theorem collisionFree_not_sufficient_for_joint_nonneg :
    ∃ c ∈ recordedInjectiveCensus, CollisionFree c ∧ c.A5 < 0 ∧ c.A6 < 0 := by
  refine ⟨cell113, by simp [recordedInjectiveCensus], cell113_collisionFree,
    cell113_negative_alignment⟩

/-- **Even under collision-free support the two depths can split signs.**  Thus kernel injectivity
cannot repair the one-depth-to-two-depth escape closed by G205. -/
theorem collisionFree_allows_mixed_sign :
    ∃ c ∈ recordedInjectiveCensus, CollisionFree c ∧ 0 < c.A5 ∧ c.A6 < 0 := by
  refine ⟨cell2593, by simp [recordedInjectiveCensus], cell2593_collisionFree,
    cell2593_mixed_alignment⟩

/-- The exact calibrated no-go: any claimed rule saying collision-free weighted-kernel fibers force
nonnegative depth-six alignment is false on the recorded exact census. -/
theorem no_collisionFree_A6_certificate
    (hcert : ∀ c ∈ recordedInjectiveCensus, CollisionFree c → 0 ≤ c.A6) : False := by
  have h := hcert cell113 (by simp [recordedInjectiveCensus]) cell113_collisionFree
  exact (not_le_of_gt cell113_negative_alignment.2) h

#print axioms cell113_collisionFree
#print axioms cell2593_collisionFree
#print axioms cell3617_collisionFree
#print axioms collisionFree_not_sufficient_for_A6_nonneg
#print axioms collisionFree_not_sufficient_for_joint_nonneg
#print axioms collisionFree_allows_mixed_sign
#print axioms no_collisionFree_A6_certificate

end ArkLib.ProximityGap.Frontier.G206
