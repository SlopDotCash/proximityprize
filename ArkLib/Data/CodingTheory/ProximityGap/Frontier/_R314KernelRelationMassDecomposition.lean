/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R313LocalShadowCollisionLoad

/-!
# LANE B2 (#466 round 314): collision mass decomposed by kernel relation

For a colliding ordered pair of distinct shadow keys `(v,w)`, put `d = w-v`.  Then `d` is a
nonzero integer vector satisfying `evalVec g m d = 0`.  This file groups the exact R312
collision surplus by those difference vectors:

```text
shadowCollisionMass = sum_{nonzero realized d in ker(evalVec g)} relationMass(d).
```

The relation mass is the characteristic-zero histogram autocorrelation carried by `d`.
This separates the two remaining tasks: count the bounded cyclotomic kernel relations, and
bound the histogram autocorrelation of each relation.

Issue #466, round 314, LANE B2.  Axiom-clean.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R314KernelRelationMassDecomposition

open ArkLib.ProximityGap.Frontier.R306Depth3CharZeroFloor
open ArkLib.ProximityGap.Frontier.R308DepthUniformShadowFloor
open ArkLib.ProximityGap.Frontier.R312ShadowCollisionMassIdentity
open ArkLib.ProximityGap.Frontier.R313LocalShadowCollisionLoad

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Difference vector of an ordered pair of shadow keys. -/
def shadowDifference {m : ℕ}
    (p : (Fin m → ℤ) × (Fin m → ℤ)) : Fin m → ℤ :=
  fun j => p.2 j - p.1 j

/-- The realized nonzero kernel relations coming from colliding shadow keys. -/
noncomputable def shadowKernelRelations (g : F) (n m r : ℕ) : Finset (Fin m → ℤ) :=
  (shadowCollisionPairs g n m r).image shadowDifference

/-- Histogram autocorrelation mass carried by one realized difference vector. -/
noncomputable def shadowRelationMass (g : F) (n m r : ℕ) (d : Fin m → ℤ) : ℕ :=
  ∑ p ∈ (shadowCollisionPairs g n m r).filter (fun p => shadowDifference p = d),
    NR n m r p.1 * NR n m r p.2

/-- Evaluation is additive on differences. -/
theorem evalVec_shadowDifference (g : F) {m : ℕ}
    (p : (Fin m → ℤ) × (Fin m → ℤ)) :
    evalVec g m (shadowDifference p) = evalVec g m p.2 - evalVec g m p.1 := by
  unfold evalVec shadowDifference
  simp only [sub_smul, Finset.sum_sub_distrib]

/-- Every coordinate of a signed basis vector is in `{-1,0,1}`. -/
theorem abs_vecOf_le_one (n m : ℕ) (a : Fin n) (j : Fin m) :
    |vecOf n m a j| ≤ (1 : ℤ) := by
  unfold vecOf
  split_ifs <;> norm_num

/-- A depth-`r` shadow vector has coordinate height at most `r`. -/
theorem abs_tupleVec_le_r (n m r : ℕ) (t : Fin r → Fin n) (j : Fin m) :
    |tupleVec n m r t j| ≤ (r : ℤ) := by
  unfold tupleVec
  calc
    |∑ i : Fin r, vecOf n m (t i) j|
        ≤ ∑ i : Fin r, |vecOf n m (t i) j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin r, (1 : ℤ) :=
      Finset.sum_le_sum (fun i _ => abs_vecOf_le_one n m (t i) j)
    _ = (r : ℤ) := by simp

/-- Every realized collision difference is a genuinely nonzero integer relation in the
kernel of evaluation at `g`. -/
theorem shadowKernelRelation_ne_zero_and_evalVec_eq_zero
    (g : F) (n m r : ℕ) {d : Fin m → ℤ}
    (hd : d ∈ shadowKernelRelations g n m r) :
    d ≠ 0 ∧ evalVec g m d = 0 := by
  classical
  rw [shadowKernelRelations, Finset.mem_image] at hd
  obtain ⟨p, hp, rfl⟩ := hd
  have hoff := (Finset.mem_filter.mp hp).1
  have heval := (Finset.mem_filter.mp hp).2
  have hne : p.1 ≠ p.2 := (Finset.mem_offDiag.mp hoff).2.2
  constructor
  · intro hzero
    apply hne
    funext j
    have hj := congrFun hzero j
    simp only [shadowDifference, Pi.zero_apply, sub_eq_zero] at hj
    exact hj.symm
  · rw [evalVec_shadowDifference, heval, sub_self]

/-- Every realized kernel relation has coefficient height at most `2r`. -/
theorem shadowKernelRelation_abs_le_two_mul_r
    (g : F) (n m r : ℕ) {d : Fin m → ℤ}
    (hd : d ∈ shadowKernelRelations g n m r) (j : Fin m) :
    |d j| ≤ (2 * r : ℕ) := by
  classical
  rw [shadowKernelRelations, Finset.mem_image] at hd
  obtain ⟨p, hp, rfl⟩ := hd
  have hoff := (Finset.mem_filter.mp hp).1
  have hp1 : p.1 ∈ keysR n m r := (Finset.mem_offDiag.mp hoff).1
  have hp2 : p.2 ∈ keysR n m r := (Finset.mem_offDiag.mp hoff).2.1
  rw [keysR, Finset.mem_image] at hp1 hp2
  obtain ⟨t, _htmem, ht⟩ := hp1
  obtain ⟨u, _humem, hu⟩ := hp2
  have htbound := abs_tupleVec_le_r n m r t j
  have hubound := abs_tupleVec_le_r n m r u j
  unfold shadowDifference
  rw [← ht, ← hu]
  calc
    |tupleVec n m r u j - tupleVec n m r t j|
        ≤ |tupleVec n m r u j| + |tupleVec n m r t j| := abs_sub _ _
    _ ≤ (r : ℤ) + (r : ℤ) := add_le_add hubound htbound
    _ = (2 * r : ℕ) := by push_cast; ring

/-- Exact decomposition of collision surplus by nonzero evaluated kernel relation. -/
theorem shadowCollisionMass_eq_sum_relationMass (g : F) (n m r : ℕ) :
    shadowCollisionMass g n m r =
      ∑ d ∈ shadowKernelRelations g n m r, shadowRelationMass g n m r d := by
  classical
  rw [shadowCollisionMass_eq_sum_pairs]
  unfold shadowKernelRelations shadowRelationMass
  exact (Finset.sum_fiberwise_of_maps_to
    (g := shadowDifference)
    (f := fun p : (Fin m → ℤ) × (Fin m → ℤ) =>
      NR n m r p.1 * NR n m r p.2)
    (fun p hp => Finset.mem_image_of_mem shadowDifference hp)).symm

/-- Count-times-autocorrelation bound.  If at most `D` bounded kernel relations occur and
each relation carries histogram mass at most `M`, then the full wraparound surplus is at
most `D*M`. -/
theorem shadowCollisionMass_le_relation_count_mul
    (g : F) (n m r D M : ℕ)
    (hcard : (shadowKernelRelations g n m r).card ≤ D)
    (hmass : ∀ d ∈ shadowKernelRelations g n m r,
      shadowRelationMass g n m r d ≤ M) :
    shadowCollisionMass g n m r ≤ D * M := by
  rw [shadowCollisionMass_eq_sum_relationMass]
  calc
    (∑ d ∈ shadowKernelRelations g n m r, shadowRelationMass g n m r d)
        ≤ ∑ _d ∈ shadowKernelRelations g n m r, M := Finset.sum_le_sum hmass
    _ = (shadowKernelRelations g n m r).card * M := by simp
    _ ≤ D * M := Nat.mul_le_mul_right M hcard

end ArkLib.ProximityGap.Frontier.R314KernelRelationMassDecomposition

/-! ## Axiom audit (must contain no `sorryAx`) -/
#print axioms
  ArkLib.ProximityGap.Frontier.R314KernelRelationMassDecomposition.evalVec_shadowDifference
#print axioms
  ArkLib.ProximityGap.Frontier.R314KernelRelationMassDecomposition.shadowKernelRelation_ne_zero_and_evalVec_eq_zero
#print axioms
  ArkLib.ProximityGap.Frontier.R314KernelRelationMassDecomposition.shadowKernelRelation_abs_le_two_mul_r
#print axioms
  ArkLib.ProximityGap.Frontier.R314KernelRelationMassDecomposition.shadowCollisionMass_eq_sum_relationMass
#print axioms
  ArkLib.ProximityGap.Frontier.R314KernelRelationMassDecomposition.shadowCollisionMass_le_relation_count_mul
