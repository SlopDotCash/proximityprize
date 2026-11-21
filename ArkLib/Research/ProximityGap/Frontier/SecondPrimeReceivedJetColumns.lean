/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SecondPrimePolynomialJetColumns
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeScalarChart
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeSectionResultant
import Mathlib.RingTheory.Localization.Ideal

/-! # Polynomial jet columns at the original affine received lines -/

namespace ArkLib.ProximityGap.Frontier.SecondPrimeReceivedJetColumns

open Finset Polynomial nonZeroDivisors SecondPrimeJetMultiplication SecondPrimePolynomialJetColumns
open SecondPrimeScalarChart SecondPrimeCoordinateWeight WeightedSylvesterDegree
variable {K : Type} [Field K]

/-- Received value as a polynomial in the scalar coordinate. -/
noncomputable def affine (u v : K) : K[X] := C u + Polynomial.X * C v

/-- Integral joint Taylor expansion in the coordinate and value, with scalar still polynomial. -/
noncomputable def localPolynomial (f : Surface K) (a u v : K) : K[X][X][X] :=
  ((f.map Bivariate.swap.toRingHom).taylor (C (affine u v))).map
    (taylorAlgHom (C a)).toRingHom

private theorem taylor_sum {R : Type} [CommRing R] (p : R[X]) (c : R) (j : ℕ) :
    (p.taylor c).coeff j = ∑ k ∈ p.support, (k.choose j : R) * p.coeff k * c^(k-j) := by
  rw [taylor_coeff, hasseDeriv_apply, sum_def, eval_finsetSum]
  simp only [eval_monomial]

private theorem scalar_degree (p : K[X][X]) (a : K) (m : ℕ)
    (hp : ∀ k, (p.coeff k).natDegree ≤ m) (j : ℕ) :
    ((p.taylor (C a)).coeff j).natDegree ≤ m := by
  rw [taylor_sum]
  apply natDegree_sum_le_of_forall_le
  intro k _
  apply natDegree_mul_le.trans
  apply (Nat.add_le_add_right natDegree_mul_le _).trans
  simpa only [natDegree_natCast, ← map_pow, natDegree_C, zero_add, add_zero] using hp k

private theorem value_degree_bound (f : Surface K) (m : ℕ) (h : TotalDegreeLe f m)
    (c : K[X]) (hc : c.natDegree ≤ 1) (i j : ℕ) :
    ((((f.map Bivariate.swap.toRingHom).taylor (C c)).coeff i).coeff j).natDegree ≤ m := by
  classical
  rw [taylor_sum, finsetSum_coeff]
  apply natDegree_sum_le_of_forall_le
  intro k hk
  have hfk : f.coeff k ≠ 0 := by
    intro hz
    apply mem_support_iff.mp hk
    simp [coeff_map, hz]
  have hcap := h k hfk
  have hj : ((Bivariate.swap (f.coeff k)).coeff j).natDegree ≤ (f.coeff k).natDegree := by
    rw [← Bivariate.natDegreeY, ← Bivariate.degreeX_swap]
    by_cases hj : j ∈ (Bivariate.swap (f.coeff k)).support
    · exact Finset.le_sup (f := fun l => ((Bivariate.swap (f.coeff k)).coeff l).natDegree) hj
    · simp [notMem_support_iff.mp hj]
  rw [← map_pow, coeff_mul_C, ← map_natCast (C : K[X] →+* K[X][X]), coeff_C_mul, coeff_map]
  change ((k.choose i : K[X]) * (Bivariate.swap (f.coeff k)).coeff j * c^(k-i)).natDegree ≤ m
  apply natDegree_mul_le.trans
  apply (Nat.add_le_add natDegree_mul_le natDegree_pow_le).trans
  rw [natDegree_natCast, zero_add]
  have hk' : (k-i) * c.natDegree ≤ k-i := by simpa using Nat.mul_le_mul_left (k-i) hc
  omega

/-- Every translated jet coefficient is a polynomial of scalar degree bounded by the
original component's scalar/value total degree. This holds simultaneously at every site. -/
theorem local_degree (f : Surface K) (m : ℕ) (h : TotalDegreeLe f m) (a u v : K) (i j : ℕ) :
    (((localPolynomial f a u v).coeff i).coeff j).natDegree ≤ m := by
  have ha : (affine u v).natDegree ≤ 1 := by
    apply natDegree_add_le_of_degree_le
    · simp
    · exact natDegree_mul_le.trans (by simp)
  simp only [localPolynomial, coeff_map, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    taylorAlgHom_apply]
  exact scalar_degree _ _ _ (value_degree_bound f m h _ ha i) j

/-- Localization of the integral local expansion gives exactly the received-line joint
Taylor polynomial used by the canonical site-order certificate. -/
theorem generic_local (f : Surface K) (a u v : K) :
    generic (localPolynomial f a u v) =
      ((scalarChart f).taylor (C (RatFunc.C u + RatFunc.X * RatFunc.C v))).map
        (taylorAlgHom (RatFunc.C a)).toRingHom := by
  have hcoord (q : K[X][X][X]) :
      generic (q.map (taylorAlgHom (C a)).toRingHom) =
        (generic q).map (taylorAlgHom (RatFunc.C a)).toRingHom := by
    apply Polynomial.ext
    intro i
    simp only [generic, coeff_map, coe_mapRingHom, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, taylorAlgHom_apply, map_taylor, RatFunc.algebraMap_C]
  have hval : generic ((f.map Bivariate.swap.toRingHom).taylor (C (affine u v))) =
      (scalarChart f).taylor (C (RatFunc.C u + RatFunc.X * RatFunc.C v)) := by
    unfold generic scalarChart
    rw [map_taylor]
    congr 1
    rw [coe_mapRingHom, Polynomial.map_C]
    simp only [affine, map_add, map_mul, RatFunc.algebraMap_X, RatFunc.algebraMap_C]
  unfold localPolynomial
  rw [hcoord, hval]

private theorem prime_localized {R S : Type} [CommRing R] [CommRing S] [IsDomain S]
    [Algebra R S] (M : Submonoid R) [IsLocalization M S] {p : R} (hp : Prime p)
    (h₀ : algebraMap R S p ≠ 0) (h₁ : ¬IsUnit (algebraMap R S p)) : Prime (algebraMap R S p) := by
  have hd : Disjoint (M : Set R) (Ideal.span ({p} : Set R) : Set R) := by
    apply Set.disjoint_left.mpr
    intro x hx hmem
    exact h₁ (isUnit_of_dvd_unit (map_dvd (algebraMap R S) (Ideal.mem_span_singleton.mp hmem))
      (IsLocalization.map_units S ⟨x, hx⟩))
  apply (Ideal.span_singleton_prime h₀).mp
  simpa only [Ideal.map_span, Set.image_singleton] using
    IsLocalization.isPrime_of_isPrime_disjoint M S _
      ((Ideal.span_singleton_prime hp.ne_zero).mpr hp) hd

/-- Scalar localization preserves the irreducibility of a positive-value-degree component,
already over the coordinate polynomial ring. In particular the chart is primitive there. -/
theorem chart_irreducible (f : Surface K) (hi : Irreducible f) (hb : 0 < f.natDegree) :
    Irreducible (scalarChart f) := by
  let R := Polynomial K[X]
  let S := (RatFunc K)[X]
  let g := f.map Bivariate.swap.toRingHom
  have hg : Irreducible g :=
    (MulEquiv.irreducible_iff (Polynomial.mapEquiv Bivariate.swap.toRingEquiv)).mpr hi
  let _ : Algebra R S := Polynomial.algebra K[X] (RatFunc K)
  let M : Submonoid R := (nonZeroDivisors K[X]).map Polynomial.C
  let _ : IsLocalization M S := Polynomial.isLocalization _ _
  let _ : Algebra R[X] S[X] := Polynomial.algebra R S
  let N : Submonoid R[X] := M.map (Polynomial.C : R →+* R[X])
  let _ : IsLocalization (R := R[X]) N (Polynomial S) := by exact Polynomial.isLocalization M S
  have hd : 0 < (scalarChart f).natDegree := by rwa [value_degree]
  apply Prime.irreducible
  apply prime_localized (R := R[X]) (S := S[X]) N hg.prime
  · change scalarChart f ≠ 0
    exact fun h => by simp [h] at hd
  · change ¬IsUnit (scalarChart f)
    exact fun h => hd.ne' (natDegree_eq_zero_of_isUnit h)

/-- The true order of the polynomial columns is the canonical received-line order. -/
theorem local_order (f : Surface K) (hi : Irreducible f) (hb : 0 < f.natDegree) (a u v : K) :
    jetOrder (generic (localPolynomial f a u v)) =
      CanonicalQuarticSiteOrder.siteOrder (scalarChart f) (RatFunc.C a)
        (C (RatFunc.C u + RatFunc.X * RatFunc.C v)) := by
  rw [generic_local]
  apply jetOrder_at_site
  exact (chart_irreducible f hi hb).isPrimitive (by rw [value_degree]; exact hb.ne')

#print axioms local_order
#print axioms local_degree
#print axioms generic_local
end ArkLib.ProximityGap.Frontier.SecondPrimeReceivedJetColumns
