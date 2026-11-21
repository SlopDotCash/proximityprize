/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.ApolarChartNormalization
import ArkLib.Research.ProximityGap.Frontier.ApolarRootTransition

/-! # The nonzero parameter and coordinate charts for actual bad scalars -/

open Polynomial Finset Matrix
open ProximityGap.ApolarDividedLocator ProximityGap.ApolarCoordinateTransport
open ProximityGap.ApolarMomentCoordinates ProximityGap.ApolarPrimitiveKernel
open ProximityGap.ApolarSparseSpecialization ProximityGap.ApolarChartNormalization
open ProximityGap.ApolarRootTransition

namespace ProximityGap.ApolarUnitChart

variable {K : Type*} [Field K]

/-- Affine generic weights in the new coordinate and translated parameter. -/
noncomputable def chartWeight (a x z : K) (d : ℕ) (w : K → K[X]) (y : K) : K[X] :=
  let old := (z*y-x)/(y-1)
  shift a (w old) * C ((old-z)^d)

theorem inverse_site (x z : K) (hxz : x ≠ z) {y : K} (hy : y ≠ z) :
    (z*site x z y-x)/(site x z y-1)=y := by
  have hd : y-z≠0 := sub_ne_zero.mpr hy
  have hc : z-x≠0 := sub_ne_zero.mpr hxz.symm
  have he : site x z y-1=(z-x)/(y-z) := by dsimp [site]; field_simp; ring
  apply (div_eq_iff (he ▸ div_ne_zero hc hd)).mpr
  dsimp [site]
  field_simp
  ring

theorem chartWeight_degree [DecidableEq K] (a x z : K) (hxz : x ≠ z) (H : Finset K)
    (hz : z ∉ H) (d : ℕ) (w : K → K[X]) (hw : ∀ y ∈ H, (w y).natDegree ≤ 1) :
    ∀ u ∈ H.image (site x z), (chartWeight a x z d w u).natDegree ≤ 1 := by
  intro u hu
  obtain ⟨y,hy,rfl⟩ := mem_image.mp hu
  rw [chartWeight,inverse_site x z hxz (fun h => hz (h ▸ hy)),mul_comm]
  exact (natDegree_C_mul_le _ _).trans (by rw [shift_degree]; exact hw y hy)

/-- The full-domain normalized functional has the same explicit affine weights
for all scalar parameters. The statement is over the parameter polynomial ring. -/
theorem whole_measure [Infinite K] [DecidableEq K] (m : ℕ → K[X]) (w : K → K[X]) (H : Finset K)
    (a x z : K) (hxz : x ≠ z) (hz : z ∉ H) {d : ℕ}
    (hm : ∀ j ≤ d, m j=∑ y ∈ H,w y*C (y^j)) (p : K[X][X]) (hp : p.natDegree ≤ d) :
    (normalizedFunctional m a x z d) p = measure (H.image (site x z))
      (C : K → K[X]) (chartWeight a x z d w) p := by
  classical
  let L := normalizedFunctional m a x z d
  let A := measure (H.image (site x z)) (C : K → K[X]) (chartWeight a x z d w)
  have hh (j : ℕ) (hj : j ≤ d) : L (X^j)=A (X^j) := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply Set.infinite_univ.mono
    intro t _
    change (L (X^j)).eval t=(A (X^j)).eval t
    have hsp (i : ℕ) (hi : i ≤ d) : (m i).eval (t+a)=∑ y ∈ H,(w y).eval (t+a)*y^i := by
      rw [hm i hi,eval_finsetSum]
      simp
    have h := (normalized_atoms_exact m a x z t hxz H hz _ hsp).2 (X^j) ((natDegree_X_pow_le _).trans hj)
    simpa only [L,A,ApolarRootTransition.measure,LinearMap.sum_apply,LinearMap.smul_apply,Polynomial.leval,LinearMap.coe_mk,AddHom.coe_mk,
      smul_eq_mul,eval_finsetSum,eval_mul,eval_pow,eval_C,eval_X,weighted_apply,RingHom.id_apply,
      Polynomial.map_pow,Polynomial.map_X,chartWeight,eval_shift,mul_assoc] using h
  apply Polynomial.induction_with_natDegree_le (fun q => L q=A q) d (by simp) _ _ p hp
  · intro j b _ hj
    rw [←smul_eq_C_mul,map_smul,map_smul,hh j hj]
  · intro p q _ _ h₁ h₂
    simp only [map_add,h₁,h₂]

/-- Express the literal received-word moment pencil after alphabet extension as
a sum of explicit affine polynomial weights on its original coordinate set. -/
theorem original_weights {F : Type*} [Field F] (φ : F →+* K) (H : Finset F) (u v : F → F) :
    let ψ : F ↪ K := ⟨φ,φ.injective⟩
    ∃ w : K → K[X], (∀ y ∈ H.map ψ, (w y).natDegree ≤ 1) ∧
      ∀ j, (ApolarHankelMinors.moment H u v j).map φ = ∑ y ∈ H.map ψ, w y*C (y^j) := by
  classical
  let b (y : F) : K[X] := X*C (φ (rowWeight H v y))+C (φ (rowWeight H u y))
  let w := Function.extend φ b (fun _ => 0)
  have hw (y : F) : w (φ y)=b y := φ.injective.extend_apply _ _ _
  refine ⟨w,?_,?_⟩
  · intro y hy
    obtain ⟨y,_,rfl⟩ := mem_map.mp hy
    change (w (φ y)).natDegree ≤ 1
    rw [hw]
    dsimp only [b]
    compute_degree
  · intro j
    simp only [ApolarHankelMinors.moment,syndrome,weighted_apply,RingHom.id_apply,
      eval_pow,eval_X,Polynomial.map_sum,Polynomial.map_add,Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_X,Polynomial.map_C,
      map_sum,map_mul,map_pow,Finset.mul_sum,←Finset.sum_add_distrib,Finset.sum_map,
      Function.Embedding.coeFn_mk,hw,b]
    apply sum_congr rfl
    intro y _
    ring

#print axioms whole_measure
#print axioms original_weights

end ProximityGap.ApolarUnitChart
