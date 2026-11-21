/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.ActualCubicHodgeIncidences
import ArkLib.Research.ProximityGap.Frontier.SquareSpecialization
import ArkLib.Research.ProximityGap.Frontier.SquarefreeCoordinateResultant
import Mathlib.RingTheory.Polynomial.Radical

/-! # Collisions of finite branch coordinates on scalar fibers of the terminal cubic -/

open Finset Polynomial UniqueFactorizationMonoid EuclideanDomain
open ArkLib.ProximityGap.Frontier
open HalfPredecessorLineCoreGeometry SecondPrimeActualPopulations SecondPrimeCoordinateWeight

namespace ProximityGap.ActualCubicBranchCollisions

variable {K : Type} [Field K]

/-- Multiplicity excess of the finite coordinate roots on a scalar fiber. -/
noncomputable def defect (B : Polynomial K[X]) (z : K) : ℕ := by
  classical
  exact B.natDegree - (B.map (evalRingHom z)).roots.toFinset.card

open Classical in
private theorem defect_le_divRadical [IsAlgClosed K] (p : K[X]) (hp : p ≠ 0) :
    p.natDegree - p.roots.toFinset.card ≤ (divRadical p).natDegree := by
  classical
  have hn := Polynomial.nodup_roots
    (PerfectField.separable_iff_squarefree.mpr (squarefree_radical (a := p)))
  have hsub : (radical p).roots.toFinset ⊆ p.roots.toFinset := by
    intro x hx
    have hroots : (radical p).roots ≤ p.roots := Polynomial.roots.le_of_dvd hp radical_dvd_self
    exact Multiset.mem_toFinset.mpr (Multiset.mem_of_le hroots (Multiset.mem_toFinset.mp hx))
  have hcard := Finset.card_le_card hsub
  rw [Multiset.toFinset_card_of_nodup hn, ← (IsAlgClosed.splits (radical p)).natDegree_eq_card_roots]
    at hcard
  have hdegree := natDegree_mul (radical_ne_zero (a := p)) (divRadical_ne_zero hp)
  rw [radical_mul_divRadical] at hdegree
  omega

/-- The second discriminant charges each loss of a distinct finite branch
coordinate, with multiplicity, over every degree-preserving scalar fiber. -/
theorem sum_defect_le [IsAlgClosed K] (B : Polynomial K[X]) (S : Finset K)
    (hsq : Squarefree B)
    (hchar : ∀ i : ℕ, 0 < i → i ≤ B.natDegree → (i : K) ≠ 0)
    (hS : ∀ z ∈ S, (B.map (evalRingHom z)).natDegree = B.natDegree) :
    ∑ z ∈ S, defect B z ≤ (2*B.natDegree-1)*Bivariate.degreeX B := by
  classical
  by_cases hr : B.natDegree = 0
  · simp [defect, hr]
  have hRes := SquarefreeCoordinateResultant.squarefree_resultant_ne_zero B hsq (by omega) hchar
  let r := B.natDegree
  let n := r-1
  let M := sylvester B B.derivative r n
  let v (z : K) := r+n-(M.map (eval z)).rank
  have hval (z : K) : ((Polynomial.X : K[X]) - Polynomial.C z)^(v z) ∣ resultant B B.derivative r n := by
    simpa only [v,Fintype.card_fin,M,resultant] using SquareSpecialization.corank_dvd_det M z
  have hs (z : K) (hz : z ∈ S) : defect B z ≤ v z := by
    let p := B.map (evalRingHom z)
    have hd : p.natDegree = r := hS z hz
    have hp : p ≠ 0 := by intro he; rw [he,natDegree_zero] at hd; exact hr hd.symm
    let W := divRadical p
    have hW : W ≠ 0 := divRadical_ne_zero hp
    have hwf : W ∣ p := divRadical_dvd_self p
    have hdeg := natDegree_le_of_dvd hwf hp
    have hwg : W ∣ B.derivative.map (evalRingHom z) := by
      rw [← derivative_map]; exact divRadical_dvd_derivative p
    have hl := SquareSpecialization.sylvester_rank_of_common_divisor p
      (B.derivative.map (evalRingHom z)) W (m := r) (n := n) hd.le
      (natDegree_map_le.trans (natDegree_derivative_le B)) hW (by omega) hwf hwg
    dsimp only [p] at hl
    rw [sylvester_map_map] at hl
    change (M.map (eval z)).rank ≤ r+n-W.natDegree at hl
    have hv := defect_le_divRadical p hp
    change r-p.roots.toFinset.card ≤ r+n-(M.map (eval z)).rank
    change p.natDegree-p.roots.toFinset.card ≤ W.natDegree at hv
    omega
  exact (Finset.sum_le_sum hs).trans
    ((SylvesterLocalMultiplicity.sum_local_orders_le_natDegree _ hRes S v (fun z _ => hval z)).trans
      (natDegree_resultant_derivative_padded_le B))

end ProximityGap.ActualCubicBranchCollisions
