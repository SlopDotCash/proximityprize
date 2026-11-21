/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.QuarterRateSharedResultant
import ArkLib.Data.Polynomial.Bivariate
import Mathlib.RingTheory.Polynomial.GaussLemma

/-! # A sufficiently populous factor divides the first quarter-rate interpolant -/

namespace ArkLib.ProximityGap.Frontier.QuarterRateFactorDivisibility
open Finset Polynomial Code SecondPrimeQuarticInterpolation
open HalfPredecessorBadEventRichPointBridge WeightedSylvesterDegree
open scoped NNReal

/-- The total degree in the scalar and value variables passes to a nonzero divisor. -/
theorem total_of_dvd {R : Type*} [CommRing R] [IsDomain R] {Q f : R[X][X]} {m : ℕ}
    (hQ : Q ≠ 0) (hf : f ∣ Q) (hm : TotalDegreeLe Q m) : TotalDegreeLe f m := by
  classical
  have ht : Bivariate.totalDegree Q ≤ m := by
    unfold Bivariate.totalDegree
    exact Finset.sup_le (fun j hj => hm j (mem_support_iff.mp hj))
  obtain ⟨r, hr⟩ := hf
  rw [hr] at hQ ht
  rw [Bivariate.totalDegree_mul (left_ne_zero_of_mul hQ) (right_ne_zero_of_mul hQ)] at ht
  intro j hj
  exact (Bivariate.coeff_totalDegree_le f (mem_support_iff.mpr hj)).trans (by omega)

/-- A primitive irreducible polynomial which does not divide another polynomial
has a nonzero resultant at their actual degrees. -/
private theorem res_ne {R : Type*} [CommRing R] [IsDomain R] [IsGCDMonoid R] {f Q : R[X]}
    (hi : Irreducible f) (hp : f.IsPrimitive) (hn : ¬ f ∣ Q) :
    resultant f Q f.natDegree Q.natDegree ≠ 0 := by
  let K := FractionRing R
  let φ := algebraMap R K
  have inj : Function.Injective φ := IsFractionRing.injective R K
  have hirr := (hp.irreducible_iff_irreducible_map_fraction_map (K := K)).mp hi
  have hc : IsCoprime (f.map φ) (Q.map φ) :=
    hirr.coprime_iff_not_dvd.mpr (fun h => hn (hp.dvd_of_fraction_map_dvd_fraction_map h))
  have h := resultant_ne_zero (f.map φ) (Q.map φ) hc
  rw [natDegree_map_eq_of_injective inj, natDegree_map_eq_of_injective inj,
    resultant_map_map] at h
  exact fun hz => h (hz ▸ map_zero φ)

variable {F : Type} [Field F]

/-- If more than 32 plus the scalar-degree budget times the factor's value
degree appear on both surfaces, this irreducible factor divides the first surface. -/
theorem divides {a : Monomials 268435458 2 268435455 626349397 → F}
    {b : Monomials 16 3 268435455 (2 * 626349397) → F} (hb : b ≠ 0)
    (f : F[X][X][X]) (hi : Irreducible f) (hy : 0 < f.natDegree) (hd : f ∣ surface b)
    (M : Finset F) (q : F → F[X]) (ha : ∀ z ∈ M, specialize a z (q z) = 0)
    (hf : ∀ z ∈ M, f.eval₂ (evalRingHom (C z)) (q z) = 0)
    (hsize : f.natDegree * 268435458 + 32 < M.card) : f ∣ surface a := by
  classical
  by_contra hnot
  have hres := res_ne hi (hi.isPrimitive hy.ne') hnot
  obtain ⟨dy, ds⟩ := QuarterRateSharedResultant.surface_bounds a
  have df := total_of_dvd (surface_ne_zero hb) hd (QuarterRateSharedResultant.surface_bounds b).2
  have hdeg := natDegree_resultant_le f (surface a) (b := f.natDegree)
    (b' := (surface a).natDegree) df ds
  apply hres
  apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero _
    (f := fun z : M => (C (z : F) : F[X])) (C_injective.comp Subtype.val_injective)
  · intro z
    apply map_resultant_eq_zero_of_common_root (evalRingHom (C (z : F))) _ _
      le_rfl le_rfl (.inl hy.ne') (q z)
    · simpa only [eval_map] using hf z z.property
    · simpa only [eval_map, surface_eval] using ha z z.property
  · rw [Fintype.card_coe]
    omega

end ArkLib.ProximityGap.Frontier.QuarterRateFactorDivisibility
