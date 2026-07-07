/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card

/-!
# Higher intersection energy for finite set families

This file records a small, reusable finite set-family API for the higher-moment side of the
proximity-gap residual.  For a family `S : kappa -> Finset iota`, the ordered `d`-wise
intersection energy is the total common-support mass over ordered `d`-tuples of members.

The main identity is

`higherIntersectionEnergy d S = sum x, degree S x ^ d`.

It is deliberately purely combinatorial: downstream proximity-gap files can specialize it to
agreement supports, line-ball incidence rows, or higher-MDS failure-correction counts without
asserting any unproved bound on the prize residual.
-/

open Finset

namespace ArkLib.ProximityGap.FiniteSetFamilyEnergy

/-- Coordinate degree of a finite set family: how many members of the family contain `x`. -/
def degree {κ ι : Type*} [Fintype κ] [DecidableEq ι] (S : κ -> Finset ι) (x : ι) :
    Nat :=
  (Finset.univ.filter (fun i => x ∈ S i)).card

/-- Common support of an ordered `d`-tuple of members of a finite set family. -/
def tupleSupport {κ ι : Type*} [Fintype ι] [DecidableEq ι] {d : Nat}
    (S : κ -> Finset ι) (v : Fin d -> κ) : Finset ι :=
  Finset.univ.filter (fun x : ι => ∀ a : Fin d, x ∈ S (v a))

/-- Ordered `d`-wise intersection mass of a finite set family. -/
def higherIntersectionEnergy {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]
    (d : Nat) (S : κ -> Finset ι) : Nat :=
  ∑ v : Fin d -> κ, (tupleSupport S v).card

/-- Coordinate degrees are monotone under pointwise inclusion of the family. -/
theorem degree_le_of_subset {κ ι : Type*} [Fintype κ] [DecidableEq ι]
    {S T : κ -> Finset ι} (hST : ∀ i, S i ⊆ T i) (x : ι) :
    degree S x ≤ degree T x := by
  unfold degree
  exact Finset.card_le_card (by
    intro i hi
    rw [Finset.mem_filter] at hi ⊢
    exact ⟨hi.1, hST i hi.2⟩)

/-- Tuple common support is monotone under pointwise inclusion of the family. -/
theorem tupleSupport_subset_of_subset {κ ι : Type*} [Fintype ι] [DecidableEq ι]
    {d : Nat} {S T : κ -> Finset ι} (hST : ∀ i, S i ⊆ T i) (v : Fin d -> κ) :
    tupleSupport S v ⊆ tupleSupport T v := by
  intro x hx
  rw [tupleSupport, Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, fun a => hST (v a) (hx.2 a)⟩

/-- Ordered `d`-wise intersection mass is monotone under pointwise inclusion. -/
theorem higherIntersectionEnergy_le_of_subset {κ ι : Type*} [Fintype κ] [Fintype ι]
    [DecidableEq ι] (d : Nat) {S T : κ -> Finset ι} (hST : ∀ i, S i ⊆ T i) :
    higherIntersectionEnergy d S ≤ higherIntersectionEnergy d T := by
  unfold higherIntersectionEnergy
  exact Finset.sum_le_sum fun v _ => Finset.card_le_card (tupleSupport_subset_of_subset hST v)

/-- Ordered `d`-wise intersection mass is exactly the `d`-th moment of coordinate degrees. -/
theorem higherIntersectionEnergy_eq_sum_degree_pow {κ ι : Type*} [Fintype κ] [Fintype ι]
    [DecidableEq κ] [DecidableEq ι] (d : Nat) (S : κ -> Finset ι) :
    higherIntersectionEnergy d S = ∑ x : ι, degree S x ^ d := by
  classical
  unfold higherIntersectionEnergy tupleSupport
  have hcard :
      ∀ v : Fin d -> κ,
        (Finset.univ.filter (fun x : ι => ∀ a : Fin d, x ∈ S (v a))).card
          = ∑ x : ι, (if (∀ a : Fin d, x ∈ S (v a)) then (1 : Nat) else 0) := by
    intro v
    rw [Finset.card_filter]
  simp_rw [hcard]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.card_filter]
  have hpi :
      (Finset.univ.filter (fun v : Fin d -> κ => ∀ a : Fin d, x ∈ S (v a)))
        = Fintype.piFinset (fun _ : Fin d => Finset.univ.filter (fun i : κ => x ∈ S i)) := by
    ext v
    simp [Fintype.mem_piFinset]
  rw [hpi, Fintype.card_piFinset]
  simp [degree, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- A tuple common support is contained in each member of the tuple. -/
theorem tupleSupport_subset_member {κ ι : Type*} [Fintype ι] [DecidableEq ι]
    {d : Nat} (S : κ -> Finset ι) (v : Fin d -> κ) (a : Fin d) :
    tupleSupport S v ⊆ S (v a) := by
  intro x hx
  rw [tupleSupport, Finset.mem_filter] at hx
  exact hx.2 a

/-- A tuple common support has cardinality at most any member set in the tuple. -/
theorem tupleSupport_card_le_member {κ ι : Type*} [Fintype ι] [DecidableEq ι]
    {d : Nat} (S : κ -> Finset ι) (v : Fin d -> κ) (a : Fin d) :
    (tupleSupport S v).card ≤ (S (v a)).card :=
  Finset.card_le_card (tupleSupport_subset_member S v a)

/-- If every ordered `d`-tuple has common support bounded by `b`, then the ordered `d`-wise
intersection mass is bounded by `|kappa|^d * b`. -/
theorem higherIntersectionEnergy_le_card_pow_mul_of_tuple_bound {κ ι : Type*} [Fintype κ]
    [Fintype ι] [DecidableEq ι] (d : Nat) (S : κ -> Finset ι) (b : Nat)
    (hbound : ∀ v : Fin d -> κ, (tupleSupport S v).card ≤ b) :
    higherIntersectionEnergy d S ≤ Fintype.card κ ^ d * b := by
  classical
  unfold higherIntersectionEnergy
  calc
    (∑ v : Fin d -> κ, (tupleSupport S v).card)
        ≤ ∑ _v : Fin d -> κ, b := Finset.sum_le_sum (fun v _ => hbound v)
    _ = Fintype.card (Fin d -> κ) * b := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
    _ = Fintype.card κ ^ d * b := by
          rw [Fintype.card_fun, Fintype.card_fin]

/-- If every member of the family has size at most `b`, then every nonempty ordered tuple has
common support at most `b`, hence its ordered intersection mass is at most `|kappa|^(d+1) * b`. -/
theorem higherIntersectionEnergy_succ_le_card_pow_mul_of_card_bound {κ ι : Type*}
    [Fintype κ] [Fintype ι] [DecidableEq ι] (d : Nat) (S : κ -> Finset ι) (b : Nat)
    (hcard : ∀ i, (S i).card ≤ b) :
    higherIntersectionEnergy (d + 1) S ≤ Fintype.card κ ^ (d + 1) * b :=
  higherIntersectionEnergy_le_card_pow_mul_of_tuple_bound (d + 1) S b
    (fun v => le_trans (tupleSupport_card_le_member S v 0) (hcard (v 0)))

/-- Higher-order pigeonhole: if the ordered `d`-wise intersection mass exceeds
`|kappa|^d * t`, then some ordered `d`-tuple has common support strictly larger than `t`. -/
theorem exists_tupleSupport_gt_of_card_pow_mul_lt_higherIntersectionEnergy
    {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]
    (d : Nat) (S : κ -> Finset ι) (t : Nat)
    (hbig : Fintype.card κ ^ d * t < higherIntersectionEnergy d S) :
    ∃ v : Fin d -> κ, t < (tupleSupport S v).card := by
  classical
  by_contra h
  push Not at h
  have hle := higherIntersectionEnergy_le_card_pow_mul_of_tuple_bound d S t h
  exact (not_le_of_gt hbig) hle

end ArkLib.ProximityGap.FiniteSetFamilyEnergy

#print axioms ArkLib.ProximityGap.FiniteSetFamilyEnergy.degree_le_of_subset
#print axioms ArkLib.ProximityGap.FiniteSetFamilyEnergy.higherIntersectionEnergy_le_of_subset
#print axioms ArkLib.ProximityGap.FiniteSetFamilyEnergy.higherIntersectionEnergy_eq_sum_degree_pow
#print axioms ArkLib.ProximityGap.FiniteSetFamilyEnergy.higherIntersectionEnergy_le_card_pow_mul_of_tuple_bound
#print axioms ArkLib.ProximityGap.FiniteSetFamilyEnergy.higherIntersectionEnergy_succ_le_card_pow_mul_of_card_bound
#print axioms ArkLib.ProximityGap.FiniteSetFamilyEnergy.exists_tupleSupport_gt_of_card_pow_mul_lt_higherIntersectionEnergy
