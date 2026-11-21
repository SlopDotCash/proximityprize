/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeCoordinateWeight
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.Localization.Algebra
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Polynomial.GaussLemma

/-! # Changing from scalar fibers to the scalar rational-function field -/

open Polynomial Finset nonZeroDivisors
namespace ArkLib.ProximityGap.Frontier.SecondPrimeScalarChart

open SecondPrimeCoordinateWeight
variable {K : Type} [Field K]

/-- Map the scalar to the coefficient field K(Z), retaining the coordinate X and value Y as
polynomial variables. -/
noncomputable def scalarChart (f : Surface K) : (RatFunc K)[X][X] :=
  (f.map Bivariate.swap.toRingHom).map (mapRingHom (algebraMap K[X] (RatFunc K)))

/-- The scalar-field chart retains the exact value degree. -/
theorem value_degree (f : Surface K) : (scalarChart f).natDegree = f.natDegree := by
  unfold scalarChart
  rw [natDegree_map_eq_of_injective (Polynomial.map_injective _ (RatFunc.algebraMap_injective K)),
    natDegree_map_eq_of_injective (f := Bivariate.swap.toRingHom) Bivariate.swap.injective]

/-- The multiplicative weight of the original trivariate surface bounds the actual weighted
bivariate degree on the scalar-field chart. -/
theorem chart_weight (f : Surface K) (d : ℕ) :
    Bivariate.natWeightedDegree (scalarChart f) 1 d ≤ weight d f := by
  classical
  apply Finset.sup_le
  intro j hj
  have hj' : f.coeff j ≠ 0 := by
    intro hh
    apply mem_support_iff.mp hj
    simp [scalarChart, coeff_map, hh]
  have hcoeff : ((scalarChart f).coeff j).natDegree = Bivariate.degreeX (f.coeff j) := by
    simp only [scalarChart, coeff_map, coe_mapRingHom]
    rw [natDegree_map_eq_of_injective (RatFunc.algebraMap_injective K)]
    exact Bivariate.natDegreeY_swap _
  obtain ⟨i, hi, heq, -⟩ := Bivariate.exists_max_index_degreeX (f.coeff j) hj'
  have h := coeff_weight_le d f (leadingCoeff_ne_zero.mpr (mem_support_iff.mp hi))
  simpa only [hcoeff, one_mul, heq, Nat.mul_comm d j] using h

private theorem fraction_of_localization {R S L : Type}
    [CommRing R] [IsDomain R] [CommRing S] [IsDomain S] [Field L]
    [Algebra R S] [Algebra S L] [Algebra R L] [IsScalarTower R S L]
    (M : Submonoid R) [IsLocalization M S] [IsFractionRing S L]
    (hinj : Function.Injective (algebraMap R S)) : IsFractionRing R L := by
  have h := IsLocalization.localization_localization_isLocalization_of_has_all_units
    M (nonZeroDivisors S) L (fun _ hu => hu.mem_nonZeroDivisors)
  have heq : (nonZeroDivisors S).comap (algebraMap R S) = nonZeroDivisors R := by
    ext r
    simp only [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero]
    exact not_congr (map_eq_zero_iff _ hinj)
  rwa [heq] at h

/-- Positive-degree irreducibility survives passage to K(Z)(X), even when the component is
not geometrically irreducible. -/
theorem generic_irreducible (f : Surface K) (hi : Irreducible f) (hb : 0 < f.natDegree) :
    Irreducible ((scalarChart f).map (algebraMap (RatFunc K)[X] (RatFunc (RatFunc K)))) := by
  let R := Polynomial K[X]
  let S := (RatFunc K)[X]
  let L := RatFunc (RatFunc K)
  let χ := algebraMap K[X] (RatFunc K)
  let g := f.map Bivariate.swap.toRingHom
  have hg : Irreducible g :=
    (MulEquiv.irreducible_iff (Polynomial.mapEquiv Bivariate.swap.toRingEquiv)).mpr hi
  have hh : g.natDegree ≠ 0 := by
    change (f.map Bivariate.swap.toRingHom).natDegree ≠ 0
    rw [natDegree_map_eq_of_injective (f := Bivariate.swap.toRingHom) Bivariate.swap.injective]
    exact hb.ne'
  let _ : Algebra R S := Polynomial.algebra K[X] (RatFunc K)
  let _ : Algebra R L := ((algebraMap S L).comp (algebraMap R S)).toAlgebra
  let _ : SMul S L := @Algebra.toSMul S L _ _ inferInstance
  let _ : SMul R L := @Algebra.toSMul R L _ _ inferInstance
  let _ : IsScalarTower R S L := IsScalarTower.of_algebraMap_eq' (R := R) (S := S) (A := L) rfl
  let M := (nonZeroDivisors K[X]).map Polynomial.C
  let _ : IsLocalization M S := Polynomial.isLocalization _ _
  have hinj : Function.Injective (algebraMap R S) :=
    Polynomial.map_injective χ (RatFunc.algebraMap_injective K)
  let _ : IsFractionRing R L := fraction_of_localization M hinj
  have h := ((hg.isPrimitive hh).irreducible_iff_irreducible_map_fraction_map (K := L)).mp hg
  change Irreducible ((g.map (algebraMap R S)).map (algebraMap S L))
  rw [Polynomial.map_map]
  exact h

#print axioms value_degree
#print axioms chart_weight
#print axioms generic_irreducible
end ArkLib.ProximityGap.Frontier.SecondPrimeScalarChart
