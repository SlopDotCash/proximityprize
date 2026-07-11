/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BGKLateNewtonSignedCovariance

/-!
# The late Newton `C12` term as a translate/intersection correlation

For the transition `r -> r+1`, the favourable two-colour collision count is

`C12 = #{(x,S,y,T) : x + sum S = 2*y + sum T}`,

where `x,y in G`, `|S|=r`, and `|T|=r-1`.  The elementary rearrangement

`x + sum S = 2*y + sum T  <->  2*y-x = sum S-sum T`

splits the variables into two independent physical profiles.  This file proves the exact
factorization

`C12 = sum_t W_G(t) * R_r(t)`,

where

* `W_G(t) = #{(x,y) in G^2 : 2*y-x=t} = #{y in G : 2*y-t in G}` is a shifted intersection row;
* `R_r(t) = #{(S,T) : sum S-sum T=t}` is the adjacent subset-sum correlation row.

Thus the desired lower bound is an alignment theorem between a cyclotomic intersection row and a
higher subset-correlation row.  The regular-simplex Gram law for the base colours does not contain
that alignment information.

The last section gives a sharp abstract no-go.  Two nonnegative two-cell profiles can have the
same masses and the same individual square masses while their cross inner product is either zero
or the full product of the masses.  Consequently marginals, separate Cauchy/Gram diagonals, and
nonnegativity alone cannot prove a positive `C12` bound.  Some joint placement theorem for the two
actual rows is indispensable.  No production correlation estimate is asserted.  Issue #466.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset BigOperators

namespace ArkLib.ProximityGap.Frontier.BGKC12TranslateIntersectionReduction

open ArkLib.ProximityGap.Frontier.BGKLateNewtonSignedCovariance

section ExactReduction

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Number of members of a finite phase family in one fibre, copied locally so this scratch lane
does not require an olean for the sibling two-colour scratch module. -/
noncomputable def phaseFiberCount {X : Type*} [Fintype X]
    (phi : X -> F) (t : F) : Nat :=
  (Finset.univ.filter fun x => phi x = t).card

/-- Cross collisions are the fibrewise inner product of two physical histograms. -/
theorem phaseCrossCollisionCount_eq_fiberInner
    {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (phi : X -> F) (chi : Y -> F) :
    phaseCrossCollisionCount phi chi =
      ∑ t : F, phaseFiberCount phi t * phaseFiberCount chi t := by
  classical
  unfold phaseCrossCollisionCount phaseFiberCount
  calc
    (∑ x : X, ∑ y : Y, if phi x = chi y then 1 else 0) =
        ((Finset.univ ×ˢ Finset.univ).filter
          (fun p : X × Y => phi p.1 = chi p.2)).card := by
      rw [Finset.card_filter, Finset.sum_product]
    _ = ∑ t : F,
        ((Finset.univ.filter fun x : X => phi x = t) ×ˢ
          (Finset.univ.filter fun y : Y => chi y = t)).card := by
      rw [← Finset.card_biUnion]
      · congr 1
        ext p
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and,
          Finset.mem_biUnion]
        constructor
        · intro h
          exact ⟨phi p.1, rfl, h.symm⟩
        · rintro ⟨t, hphi, hchi⟩
          exact hphi.trans hchi.symm
      · intro a _ha b _hb hab
        apply Finset.disjoint_left.mpr
        intro p hp hq
        simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
        exact hab (hp.1.symm.trans hq.1)
    _ = ∑ t : F,
        (Finset.univ.filter fun x : X => phi x = t).card *
          (Finset.univ.filter fun y : Y => chi y = t).card := by
      apply Finset.sum_congr rfl
      intro t _ht
      rw [Finset.card_product]

/-- The two marked subgroup points occurring in `C12`. -/
abbrev MarkedPair (G : Finset F) := {x : F // x ∈ G} × {y : F // y ∈ G}

/-- The adjacent pair of subset indices occurring in `C12`. -/
abbrev AdjacentSubsetPair (G : Finset F) (r : Nat) := SubsetAt G r × SubsetAt G (r - 1)

/-- Marked-point difference `2*y-x`. -/
def markedDifferencePhase (G : Finset F) (z : MarkedPair G) : F :=
  2 * z.2.1 - z.1.1

/-- Difference of the two adjacent subset sums. -/
noncomputable def subsetDifferencePhase (G : Finset F) (r : Nat)
    (z : AdjacentSubsetPair G r) : F :=
  (∑ x ∈ z.1.1, x.1) - ∑ y ∈ z.2.1, y.1

/-- Multiplicity of one marked difference. -/
noncomputable def markedDifferenceMultiplicity (G : Finset F) (t : F) : Nat :=
  phaseFiberCount (markedDifferencePhase G) t

/-- Multiplicity of one adjacent subset-sum difference. -/
noncomputable def subsetDifferenceMultiplicity (G : Finset F) (r : Nat) (t : F) : Nat :=
  phaseFiberCount (subsetDifferencePhase G r) t

/-- The reassociation which separates marked variables from subset variables. -/
def reassociateNewtonPairs (G : Finset F) (r : Nat) :
    (NewtonJoin G r × NewtonJoin G (r - 1)) ≃
      (MarkedPair G × AdjacentSubsetPair G r) where
  toFun p := ((p.1.1, p.2.1), (p.1.2, p.2.2))
  invFun p := ((p.1.1, p.2.1), (p.1.2, p.2.2))
  left_inv := by intro p; rfl
  right_inv := by intro p; rfl

/-- The original `U1/U2` collision equation is exactly equality of the two difference phases. -/
theorem newton_collision_iff_difference_collision (G : Finset F) (r : Nat)
    (p : NewtonJoin G r × NewtonJoin G (r - 1)) :
    newtonJoinPhase G 1 r p.1 = newtonJoinPhase G 2 (r - 1) p.2 ↔
      markedDifferencePhase G (reassociateNewtonPairs G r p).1 =
        subsetDifferencePhase G r (reassociateNewtonPairs G r p).2 := by
  simp only [newtonJoinPhase, markedDifferencePhase, subsetDifferencePhase,
    reassociateNewtonPairs, Nat.cast_one, one_mul, Nat.cast_ofNat]
  constructor <;> intro h <;> linear_combination h

/-- **Exact variable-separation identity.**  The late favourable collision count is a cross
collision between the marked translate row and the adjacent subset-difference row. -/
theorem newtonJoinCollisionCount_one_two_eq_differenceCrossCollision
    (G : Finset F) (r : Nat) :
    newtonJoinCollisionCount G 1 r 2 (r - 1) =
      phaseCrossCollisionCount (markedDifferencePhase G) (subsetDifferencePhase G r) := by
  classical
  unfold newtonJoinCollisionCount phaseCrossCollisionCount
  calc
    (∑ x : NewtonJoin G r, ∑ y : NewtonJoin G (r - 1),
        if newtonJoinPhase G 1 r x = newtonJoinPhase G 2 (r - 1) y then 1 else 0) =
        ∑ p : NewtonJoin G r × NewtonJoin G (r - 1),
          if newtonJoinPhase G 1 r p.1 = newtonJoinPhase G 2 (r - 1) p.2 then 1 else 0 := by
      exact (Fintype.sum_prod_type (fun p : NewtonJoin G r × NewtonJoin G (r - 1) =>
        if newtonJoinPhase G 1 r p.1 = newtonJoinPhase G 2 (r - 1) p.2 then 1 else 0)).symm
    _ = ∑ p : MarkedPair G × AdjacentSubsetPair G r,
          if markedDifferencePhase G p.1 = subsetDifferencePhase G r p.2 then 1 else 0 := by
      apply Fintype.sum_equiv (reassociateNewtonPairs G r)
      intro p
      simp only [newton_collision_iff_difference_collision]
    _ = ∑ x : MarkedPair G, ∑ y : AdjacentSubsetPair G r,
          if markedDifferencePhase G x = subsetDifferencePhase G r y then 1 else 0 := by
      rw [Fintype.sum_prod_type]

/-- **Translate/intersection factorization of `C12`.** -/
theorem newtonJoinCollisionCount_one_two_eq_translateCorrelation
    (G : Finset F) (r : Nat) :
    newtonJoinCollisionCount G 1 r 2 (r - 1) =
      ∑ t : F, markedDifferenceMultiplicity G t * subsetDifferenceMultiplicity G r t := by
  rw [newtonJoinCollisionCount_one_two_eq_differenceCrossCollision,
    phaseCrossCollisionCount_eq_fiberInner]
  rfl

/-- Literal shifted-intersection row `#{y in G : 2*y-t in G}`. -/
def doubledTranslateIntersection (G : Finset F) (t : F) : Nat :=
  (G.filter fun y => 2 * y - t ∈ G).card

/-- The marked-difference multiplicity is exactly the shifted subgroup intersection row. -/
theorem markedDifferenceMultiplicity_eq_doubledTranslateIntersection
    (G : Finset F) (t : F) :
    markedDifferenceMultiplicity G t = doubledTranslateIntersection G t := by
  classical
  unfold markedDifferenceMultiplicity phaseFiberCount doubledTranslateIntersection
  refine Finset.card_bij (fun z _hz => z.2.1) ?_ ?_ ?_
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
    refine Finset.mem_filter.mpr ⟨z.2.2, ?_⟩
    have hx : 2 * z.2.1 - t = z.1.1 := by
      unfold markedDifferencePhase at hz
      linear_combination hz
    exact hx.symm ▸ z.1.2
  · intro z hz z' hz' heq
    apply Prod.ext
    · apply Subtype.ext
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz hz'
      unfold markedDifferencePhase at hz hz'
      linear_combination hz - hz' - 2 * heq
    · exact Subtype.ext heq
  · intro y hy
    simp only [Finset.mem_filter] at hy
    let x : {x : F // x ∈ G} := ⟨2 * y - t, hy.2⟩
    let y' : {y : F // y ∈ G} := ⟨y, hy.1⟩
    refine ⟨(x, y'), ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    unfold markedDifferencePhase
    dsimp [x, y']
    ring

/-- Final exact form with the cyclotomic translate row exposed literally. -/
theorem newtonJoinCollisionCount_one_two_eq_intersectionCorrelation
    (G : Finset F) (r : Nat) :
    newtonJoinCollisionCount G 1 r 2 (r - 1) =
      ∑ t : F, doubledTranslateIntersection G t * subsetDifferenceMultiplicity G r t := by
  rw [newtonJoinCollisionCount_one_two_eq_translateCorrelation]
  apply Finset.sum_congr rfl
  intro t _ht
  rw [markedDifferenceMultiplicity_eq_doubledTranslateIntersection]

end ExactReduction

/-! ## Sharp information no-go for separate marginals and Gram diagonals -/

section MarginalNoGo

/-- A one-cell nonnegative profile. -/
def atomZero (A : Nat) (i : Fin 2) : Nat := if i = 0 then A else 0

/-- The same mass placed in the opposite cell. -/
def atomOne (A : Nat) (i : Fin 2) : Nat := if i = 1 then A else 0

theorem atomZero_mass (A : Nat) : ∑ i : Fin 2, atomZero A i = A := by
  norm_num [atomZero, Fin.sum_univ_two]

theorem atomOne_mass (A : Nat) : ∑ i : Fin 2, atomOne A i = A := by
  norm_num [atomOne, Fin.sum_univ_two]

theorem atomZero_squareMass (A : Nat) : ∑ i : Fin 2, atomZero A i ^ 2 = A ^ 2 := by
  norm_num [atomZero, Fin.sum_univ_two]

theorem atomOne_squareMass (A : Nat) : ∑ i : Fin 2, atomOne A i ^ 2 = A ^ 2 := by
  norm_num [atomOne, Fin.sum_univ_two]

theorem atomZero_aligned_inner (A B : Nat) :
    ∑ i : Fin 2, atomZero A i * atomZero B i = A * B := by
  norm_num [atomZero, Fin.sum_univ_two]

theorem atomZero_disjoint_inner (A B : Nat) :
    ∑ i : Fin 2, atomZero A i * atomOne B i = 0 := by
  norm_num [atomZero, atomOne, Fin.sum_univ_two]

/-- **Sharp marginal/diagonal-Gram no-go.**  The two candidate right profiles have identical
masses and identical square masses, but their cross inner products with the same left profile are
the two extremes `A*B` and `0`. -/
theorem same_marginals_and_squareMass_cross_inner_ranges_from_zero_to_full (A B : Nat) :
    (∑ i : Fin 2, atomZero B i) = (∑ i : Fin 2, atomOne B i) ∧
    (∑ i : Fin 2, atomZero B i ^ 2) = (∑ i : Fin 2, atomOne B i ^ 2) ∧
    (∑ i : Fin 2, atomZero A i * atomZero B i) = A * B ∧
    (∑ i : Fin 2, atomZero A i * atomOne B i) = 0 := by
  rw [atomZero_mass, atomOne_mass, atomZero_squareMass, atomOne_squareMass,
    atomZero_aligned_inner, atomZero_disjoint_inner]
  simp

/-! ## Axiom audit -/

#print axioms newtonJoinCollisionCount_one_two_eq_intersectionCorrelation
#print axioms same_marginals_and_squareMass_cross_inner_ranges_from_zero_to_full

end MarginalNoGo

end ArkLib.ProximityGap.Frontier.BGKC12TranslateIntersectionReduction
