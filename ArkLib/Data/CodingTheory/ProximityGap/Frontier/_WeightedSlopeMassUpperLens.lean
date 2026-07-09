/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DesignMatrixAffineCluster
import ArkLib.Data.CodingTheory.ProximityGap.CoveragePigeonhole
import ArkLib.Data.CodingTheory.ProximityGap.MCASecondMoment
import ArkLib.Data.CodingTheory.ProximityGap.MCAWitnessSpread

/-!
# The weighted secant-slope mass upper lens

Choose, for every bad scalar `gamma`, an explaining codeword `c gamma` and a witness
set `S gamma` of size at least `a`.  Every distinct pair has the codeword-valued secant
slope

`b = (gamma-gamma')^-1 * (c gamma-c gamma')`,

and `b` agrees with the direction row `u1` throughout `S gamma ∩ S gamma'`.

For one fixed slope `b`, equality of secant slope is equality of the affine intercept
`c gamma - gamma*b`.  Its fibers are therefore exactly affine-pencil clusters.  The
`DesignMatrixAffineCluster` theorem bounds every such fiber by

`cap_a(b) = support(u1-b) / max(1, a-agree(u1,b))`.

Combining this with the global Cauchy lower bound on witness intersections gives

`|G| * a^2 <= n^2 + n * WeightedSlopeMass`,

where

`WeightedSlopeMass = sum_{realized b} agree(u1,b) * (cap_a(b)-1)`.

This is an exact bad-count upper lens, not a solution of the good side.  Its remaining
input is a weighted list-mass bound for the realized nearby codewords `b`.  The final
coarse consumer shows that replacing this mass by an ordinary list-size bound recovers
the familiar doubled-radius/list-decoding wall.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset
open scoped BigOperators NNReal

namespace ProximityGap.Frontier.WeightedSlopeMassUpperLens

open ProximityGap
open ProximityGap.MCAWitnessSpread
open ProximityGap.Frontier.DesignMatrixAffineCluster

/-! ## Abstract weighted Cauchy engine -/

section AbstractCauchy

variable {kappa iota : Type*} [Fintype kappa] [Nonempty kappa] [DecidableEq kappa]
variable [Fintype iota] [DecidableEq iota]

/-- Total ordered off-diagonal intersection mass of a finite set family. -/
def offDiagInterMass (S : kappa -> Finset iota) : Nat :=
  ∑ x : kappa, ∑ y ∈ (Finset.univ : Finset kappa).erase x, (S x ∩ S y).card

/-- **Weighted Cauchy engine.**  If every set has size at least `a` and the total ordered
off-diagonal intersection mass is at most `|kappa|*R`, then

`|kappa| * a^2 <= |iota|^2 + |iota|*R`.

The cancellation of one factor `|kappa|` is valid because the index type is nonempty. -/
theorem card_mul_sq_le_length_sq_add_weightedMass
    (S : kappa -> Finset iota) (a R : Nat)
    (hsize : ∀ x, a <= (S x).card)
    (hmass : offDiagInterMass S <= Fintype.card kappa * R) :
    Fintype.card kappa * a ^ 2 <=
      (Fintype.card iota) ^ 2 + Fintype.card iota * R := by
  classical
  let L := Fintype.card kappa
  let N := Fintype.card iota
  have hsumLo : L * a <= ∑ x : kappa, (S x).card := by
    rw [show L * a = ∑ _x : kappa, a by simp [L, Nat.mul_comm]]
    exact Finset.sum_le_sum (fun x _ => hsize x)
  have hsplit : (∑ x : kappa, ∑ y : kappa, (S x ∩ S y).card) =
      (∑ x : kappa, (S x).card) + offDiagInterMass S := by
    rw [offDiagInterMass, <- Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _hx
    rw [show (∑ y : kappa, (S x ∩ S y).card) =
        (S x ∩ S x).card +
          ∑ y ∈ (Finset.univ : Finset kappa).erase x, (S x ∩ S y).card by
      exact (Finset.add_sum_erase Finset.univ
        (fun y => (S x ∩ S y).card) (Finset.mem_univ x)).symm]
    simp
  have hdiag : (∑ x : kappa, (S x).card) <= L * N := by
    calc
      (∑ x : kappa, (S x).card) <= ∑ _x : kappa, N := by
        apply Finset.sum_le_sum
        intro x _
        calc
          (S x).card <= (Finset.univ : Finset iota).card :=
            Finset.card_le_card (Finset.subset_univ _)
          _ = N := by simp [N]
      _ = L * N := by simp [L]
  have hCS := ArkLib.Coverage.sq_sum_card_le_card_mul_sum_inter S
  have hmain : (L * a) ^ 2 <= N * (L * N + L * R) := by
    calc
      (L * a) ^ 2 <= (∑ x : kappa, (S x).card) ^ 2 :=
        Nat.pow_le_pow_left hsumLo 2
      _ <= N * (∑ x : kappa, ∑ y : kappa, (S x ∩ S y).card) := by
        simpa [N] using hCS
      _ = N * ((∑ x : kappa, (S x).card) + offDiagInterMass S) := by
        rw [hsplit]
      _ <= N * (L * N + L * R) := by
        gcongr
  have hfactor : (L * a) ^ 2 = L * (L * a ^ 2) := by ring
  have hrhs : N * (L * N + L * R) = L * (N ^ 2 + N * R) := by ring
  rw [hfactor, hrhs] at hmain
  exact Nat.le_of_mul_le_mul_left hmain Fintype.card_pos

end AbstractCauchy

/-! ## Secant slopes and affine intercepts -/

section Slopes

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {n : Nat} [NeZero n]

/-- Secant slope of two explainer points over distinct scalar coordinates. -/
def secantSlope (gamma gamma' : F) (c c' : Fin n -> F) : Fin n -> F :=
  (gamma - gamma')⁻¹ • (c - c')

/-- Affine intercept of an explainer point relative to a proposed slope. -/
def affineIntercept (gamma : F) (c b : Fin n -> F) : Fin n -> F :=
  c - gamma • b

/-- Coordinates on which a slope codeword agrees with the direction row. -/
noncomputable def slopeAgreeSet (u1 b : Fin n -> F) : Finset (Fin n) :=
  Finset.univ.filter (fun i => b i = u1 i)

/-- Complementary support of the direction-row discrepancy. -/
noncomputable def slopeSupport (u1 b : Fin n -> F) : Finset (Fin n) :=
  Finset.univ.filter (fun i => u1 i - b i ≠ 0)

/-- Uniform pin multiplicity available for every affine cluster of slope `b`. -/
noncomputable def slopePinMultiplicity (a : Nat) (u1 b : Fin n -> F) : Nat :=
  max 1 (a - (slopeAgreeSet u1 b).card)

/-- Maximum affine-cluster size furnished by the support/pin bound. -/
noncomputable def slopeClusterCap (a : Nat) (u1 b : Fin n -> F) : Nat :=
  (slopeSupport u1 b).card / slopePinMultiplicity a u1 b

/-- Equality of a nonvertical secant slope is exactly equality of affine intercepts. -/
theorem secantSlope_eq_iff_affineIntercept_eq
    {gamma gamma' : F} (hne : gamma ≠ gamma') (c c' b : Fin n -> F) :
    secantSlope gamma gamma' c c' = b ↔
      affineIntercept gamma c b = affineIntercept gamma' c' b := by
  have hd : gamma - gamma' ≠ 0 := sub_ne_zero.mpr hne
  constructor
  · intro hslope
    have hdiff := congrArg (fun w : Fin n -> F => (gamma - gamma') • w) hslope
    have hdiff' : c - c' = (gamma - gamma') • b := by
      simpa [secantSlope, smul_smul, hd] using hdiff
    simp only [affineIntercept]
    module
  · intro hintercept
    have hdiff : c - c' = (gamma - gamma') • b := by
      simp only [affineIntercept] at hintercept
      module
    simp [secantSlope, hdiff, smul_smul, hd]

/-- The locked coordinates of an affine pencil are contained in its slope-agreement set. -/
theorem lockedSet_subset_slopeAgreeSet
    (c0 b u0 u1 : Fin n -> F) :
    lockedSet c0 b u0 u1 ⊆ slopeAgreeSet u1 b := by
  classical
  intro i hi
  rw [lockedSet, Finset.mem_filter] at hi
  rw [slopeAgreeSet, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, hi.2.2.symm⟩

/-- The cluster-independent pin multiplicity is no larger than the exact locked-set
multiplicity used by `affineCluster_card_mul_le_support`. -/
theorem slopePinMultiplicity_le_lockedMultiplicity
    (a : Nat) (c0 b u0 u1 : Fin n -> F) :
    slopePinMultiplicity a u1 b <= max 1 (a - (lockedSet c0 b u0 u1).card) := by
  have hcard : (lockedSet c0 b u0 u1).card <= (slopeAgreeSet u1 b).card :=
    Finset.card_le_card (lockedSet_subset_slopeAgreeSet c0 b u0 u1)
  exact max_le_max le_rfl (Nat.sub_le_sub_left hcard a)

/-- A witness intersection is contained in the agreement set of its secant slope. -/
theorem witness_inter_subset_slopeAgreeSet
    (C : Submodule F (Fin n -> F)) {S S' : Finset (Fin n)}
    {u0 u1 c c' : Fin n -> F} {gamma gamma' : F}
    (hne : gamma ≠ gamma') (hc : c ∈ C) (hc' : c' ∈ C)
    (hS : ∀ i ∈ S, c i = u0 i + gamma * u1 i)
    (hS' : ∀ i ∈ S', c' i = u0 i + gamma' * u1 i) :
    S ∩ S' ⊆ slopeAgreeSet u1 (secantSlope gamma gamma' c c') := by
  classical
  have hslope := line_slope_codeword_of_two_witnesses C hne hc hc'
    (by simpa [smul_eq_mul] using hS) (by simpa [smul_eq_mul] using hS')
  intro i hi
  rw [slopeAgreeSet, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, (hslope.2 i hi).symm⟩

end Slopes

end ProximityGap.Frontier.WeightedSlopeMassUpperLens

#print axioms ProximityGap.Frontier.WeightedSlopeMassUpperLens.card_mul_sq_le_length_sq_add_weightedMass
#print axioms ProximityGap.Frontier.WeightedSlopeMassUpperLens.secantSlope_eq_iff_affineIntercept_eq
#print axioms ProximityGap.Frontier.WeightedSlopeMassUpperLens.witness_inter_subset_slopeAgreeSet
