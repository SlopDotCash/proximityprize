/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.ImplicitDerivativeBidegree

/-! # Counting transverse polynomial sections

Scalar-resultant bounds on the transverse components of ordinary
Reed–Solomon interpolation surfaces. A polynomial section has zero
coordinate derivative of order one past its degree.
-/

set_option autoImplicit false
noncomputable section
open Polynomial Polynomial.Bivariate ArkLib.BivariateDegreeToolkit
open scoped Differential
namespace ArkLib.ProximityGap.Frontier.TransverseSectionBudget

open ImplicitDerivativeNumerator ImplicitDerivativeBidegree WeightedSylvesterDegree

/-- The Sylvester bound at nominal bidegrees dominates the one at the true
degrees even when the characteristic lowers a leading term. -/
private theorem rectangle_mono {b c h H b' c' : ℕ} (hbh : b ≤ h) (hcH : c ≤ H)
    (hab : b' ≤ b) (hac : c' ≤ c) :
    b'*H+c'*h-b'*c' ≤ b*H+c*h-b*c := by
  have hr : ∀ a v, a ≤ h → v ≤ H → a*H+v*h-a*v = a*(H-v)+v*h := by
    intro a v _ hv
    rw [Nat.mul_sub]
    have := Nat.mul_le_mul_left a hv
    omega
  have hs : b*(H-c')+c'*h = b*H+c'*(h-b) := by
    rw [Nat.mul_sub, Nat.mul_sub]
    have hh := Nat.mul_le_mul_left b (hac.trans hcH)
    have hh' := Nat.mul_le_mul_left c' hbh
    rw [Nat.mul_comm c' b] at *
    omega
  rw [hr b' c' (hab.trans hbh) (hac.trans hcH), hr b c hbh hcH]
  calc b'*(H-c')+c'*h ≤ b*(H-c')+c'*h := Nat.add_le_add_right (Nat.mul_le_mul_right _ hab) _
       _ = b*H+c'*(h-b) := hs
       _ ≤ b*H+c*(h-b) := Nat.add_le_add_left (Nat.mul_le_mul_right _ hac) _
       _ = b*(H-c)+c*h := by
         rw [Nat.mul_sub, Nat.mul_sub]
         have hx := Nat.mul_le_mul_left b hcH
         have hy := Nat.mul_le_mul_left c hbh
         rw [Nat.mul_comm c b] at *
         omega

variable {K : Type} [Field K] [Differential K]

/-- A family of polynomial sections on a transverse factor, counted directly
by its scalar resultant. The last term includes the saving from the triangular
support in scalar and value. -/
theorem population (f : K[X][X]) (d m b : ℕ) (hb : 2 ≤ b) (hm : b ≤ m)
    (hf : TotalDegreeLe f m) (hfy : f.natDegree ≤ b) (hpos : f.natDegree ≠ 0)
    (S : Finset K) (hS : ∀ z ∈ S, z′ = 0 ∧ ∃ y : K,
      (f.map (evalRingHom z)).eval y = 0 ∧ (Differential.deriv^[d+1]) y = 0)
    (hres : letI := coefficientDifferential (K := K)
      resultant f (numerator f d) f.natDegree (numerator f d).natDegree ≠ 0) :
    S.card ≤ b*(m+2*d*(m-1))+(b+2*d*(b-1))*m-b*(b+2*d*(b-1)) := by
  let _ : Differential K[X] := coefficientDifferential (K := K)
  have hm' : 2 ≤ m := hb.trans hm
  have hf' : natWeightedDegree f 1 1 ≤ m :=
    Finset.sup_le fun i hi => by simpa using hf i (mem_support_iff.mp hi)
  have ht : TotalDegreeLe (numerator f d) (m+2*d*(m-1)) := by
    intro i hi
    simpa using (weight_coeff_le_natWeightedDegree (numerator f d) 1 1 (mem_support_iff.mpr hi)).trans
      (numerator_weight_le coefficientDifferential_degree f hm' hf' d)
  have hy : (numerator f d).natDegree ≤ b+2*d*(b-1) := by
    change natDegreeY (numerator f d) ≤ _
    rw [degreeY_as_weighted_deg]
    change natDegreeY f ≤ b at hfy
    rw [degreeY_as_weighted_deg] at hfy
    exact numerator_weight_le coefficientDifferential_degree f hb hfy d
  apply (common_fiber_count f (numerator f d) le_rfl le_rfl (Or.inl hpos) hf ht hres S ?_).trans
  · apply rectangle_mono hm (Nat.add_le_add hm (Nat.mul_le_mul_left _ (Nat.sub_le_sub_right hm 1))) hfy hy
  · intro z hz
    obtain ⟨hc,y,h,hy⟩ := hS z hz
    refine ⟨y,h,?_⟩
    let _ : Algebra K[X] K := (evalRingHom z).toAlgebra
    let _ : DifferentialAlgebra K[X] K := ⟨fun p => by
      change (p.eval z)′ = (Differential.mapCoeffs p).eval z
      simpa [hc] using (Differential.deriv_aeval_eq z p)⟩
    have hev (P : K[X][X]) : aeval y P = (P.map (evalRingHom z)).eval y := by
      rw [aeval_def, eval_map]; rfl
    rw [← hev] at h ⊢
    exact numerator_aeval_zero _ _ h _ hy

end ArkLib.ProximityGap.Frontier.TransverseSectionBudget

open ArkLib.ProximityGap.Frontier.TransverseSectionBudget in
#print axioms population
