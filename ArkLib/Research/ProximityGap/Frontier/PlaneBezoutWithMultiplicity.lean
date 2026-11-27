/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.LogarithmicSectionHeights
import ArkLib.Research.ProximityGap.Frontier.WeightedSylvesterDegree
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.LinearAlgebra.Dimension.Finrank

/-! # Projective plane Bézout bounds with multiplicity at `[0:1:0]` and quotient dimension

This module proves two complementary axiom-clean forms of plane Bézout's theorem:

1. **Affine Bézout with multiplicity at `[0:1:0]` (`plane_bezout_with_multiplicity`)**:
   For relatively prime `F, G : K[X][X]` of total degrees `≤ m, d'` and `Y`-degrees `≤ b, b'`
   (corresponding to multiplicities `μ_F = m - b` and `μ_G = d' - b'` at `[0:1:0]`), the number
   of distinct common affine zeros `(z, y) ∈ K × K` is at most
   `m * d' - (m - b) * (d' - b') = b * d' + b' * m - b * b'`.

2. **Quotient dimension Bézout (`affine_quotient_finrank_le`)**:
   For relatively prime `H₁, H₂ : MvPolynomial (Fin 2) B` of total degrees `≤ d₁, d₂` over any
   field `B`, the quotient algebra `B[X₀, X₁] / (H₁, H₂)` is finite-dimensional over `B` of
   dimension at most `d₁ * d₂`. The proof is Fulton's elementary exact sequence of homogeneous
   polynomial spaces in `B[X₀, X₁, X₂]_N`.
-/

set_option autoImplicit false
noncomputable section

open Polynomial Finset Module

namespace ArkLib.ProximityGap.Frontier.PlaneBezoutWithMultiplicity

section AffineMultiplicityBezout

variable {K : Type*} [Field K]

/-- Clearing denominators of a polynomial over `FractionRing R` produces an integral polynomial
whose fraction-field image is a nonzero scalar multiple of the original. -/
private theorem exists_clear_denom_poly {R : Type*} [CommRing R] [IsDomain R]
    (g : (FractionRing R)[X]) :
    ∃ (c : R) (g₁ : R[X]), c ≠ 0 ∧
      g₁.map (algebraMap R (FractionRing R)) = C (algebraMap R (FractionRing R) c) * g := by
  classical
  let L := FractionRing R
  let ι := algebraMap R L
  have hrep : ∀ i, ∃ a b : R, b ≠ 0 ∧ g.coeff i = ι a / ι b := by
    intro i
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := R) (g.coeff i)
    exact ⟨a, b, mem_nonZeroDivisors_iff_ne_zero.mp hb, hab.symm⟩
  choose a b hb hab using hrep
  let c : R := ∏ i ∈ g.support, b i
  have hc : c ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hb i
  let g₁ : R[X] := ∑ i ∈ g.support, Polynomial.monomial i (a i * ∏ j ∈ g.support.erase i, b j)
  refine ⟨c, g₁, hc, ?_⟩
  ext k
  rw [coeff_map, coeff_C_mul]
  by_cases hk : k ∈ g.support
  · have hprod : c = b k * ∏ j ∈ g.support.erase k, b j := (Finset.mul_prod_erase g.support b hk).symm
    have hcoeff : g₁.coeff k = a k * ∏ j ∈ g.support.erase k, b j := by
      simp only [g₁, finsetSum_coeff, Polynomial.coeff_monomial]
      rw [Finset.sum_eq_single k]
      · simp
      · intro j _ hjk; simp [hjk]
      · intro h'; exact absurd hk h'
    rw [hcoeff, map_mul, hab k, hprod, map_mul]
    have hbk : algebraMap R (FractionRing R) (b k) ≠ 0 :=
      (map_ne_zero_iff (algebraMap R (FractionRing R)) (IsFractionRing.injective R _)).mpr (hb k)
    dsimp only [ι, L]
    field_simp [hbk]
  · have hgk : g.coeff k = 0 := Polynomial.notMem_support_iff.mp hk
    have hg1k : g₁.coeff k = 0 := by
      simp only [g₁, finsetSum_coeff, Polynomial.coeff_monomial]
      apply Finset.sum_eq_zero
      intro j hj
      have hjk : j ≠ k := fun h => hk (h ▸ hj)
      simp [hjk]
    simp [hgk, hg1k]

/-- Two relatively prime polynomials in `K[X][X]` become coprime over `FractionRing K[X]`. -/
theorem isCoprime_map_fractionRing_of_isRelPrime (F G : K[X][X])
    (hrel : IsRelPrime F G) :
    IsCoprime (F.map (algebraMap K[X] (FractionRing K[X])))
      (G.map (algebraMap K[X] (FractionRing K[X]))) := by
  classical
  let ι : K[X] →+* FractionRing K[X] := algebraMap K[X] (FractionRing K[X])
  have hF0_or_G0 : F ≠ 0 ∨ G ≠ 0 := by
    by_contra h
    push Not at h
    exact not_isUnit_zero (hrel (h.1 ▸ dvd_rfl) (h.2 ▸ dvd_rfl))
  set g : (FractionRing K[X])[X] := EuclideanDomain.gcd (F.map ι) (G.map ι)
  have hg_ne : g ≠ 0 := by
    intro h0
    have h0' : EuclideanDomain.gcd (F.map ι) (G.map ι) = 0 := h0
    rw [EuclideanDomain.gcd_eq_zero_iff] at h0'
    rcases hF0_or_G0 with hF | hG
    · exact hF ((Polynomial.map_eq_zero_iff (IsFractionRing.injective K[X] _)).mp h0'.1)
    · exact hG ((Polynomial.map_eq_zero_iff (IsFractionRing.injective K[X] _)).mp h0'.2)
  have hg_deg : g.natDegree = 0 := by
    by_contra hpos
    have hgt : 0 < g.natDegree := Nat.pos_of_ne_zero hpos
    obtain ⟨c, g₁, hc, hg₁⟩ := exists_clear_denom_poly (R := K[X]) g
    have hcL : ι c ≠ 0 :=
      (map_ne_zero_iff ι (IsFractionRing.injective K[X] _)).mpr hc
    have hg₁_ne : g₁ ≠ 0 := by
      intro h0
      rw [h0, Polynomial.map_zero] at hg₁
      exact mul_ne_zero (C_ne_zero.mpr hcL) hg_ne hg₁.symm
    let p : K[X][X] := g₁.primPart
    have hp_prim : p.IsPrimitive := isPrimitive_primPart g₁
    have hg₁_eq : g₁ = C g₁.content * p := eq_C_content_mul_primPart g₁
    have hcont_ne : g₁.content ≠ 0 := by
      intro h0
      rw [h0, map_zero, zero_mul] at hg₁_eq
      exact hg₁_ne hg₁_eq
    have hp_map_dvd_g : p.map ι ∣ g := by
      have h1 : C (ι g₁.content) * p.map ι = C (ι c) * g := by
        rw [← map_C, ← Polynomial.map_mul, ← hg₁_eq, hg₁]
      refine ⟨C (ι g₁.content / ι c), ?_⟩
      have h2 : C (ι c) * (p.map ι * C (ι g₁.content / ι c)) = C (ι c) * g := by
        calc C (ι c) * (p.map ι * C (ι g₁.content / ι c))
            = C (ι c * (ι g₁.content / ι c)) * p.map ι := by rw [C_mul]; ring
          _ = C (ι g₁.content) * p.map ι := by rw [mul_div_cancel₀ _ hcL]
          _ = C (ι c) * g := h1
      exact mul_left_cancel₀ (C_ne_zero.mpr hcL) h2.symm
    have hp_dvd_F : p ∣ F :=
      (hp_prim.dvd_iff_fraction_map_dvd_fraction_map (K := FractionRing K[X])).mpr
        (hp_map_dvd_g.trans (EuclideanDomain.gcd_dvd_left _ _))
    have hp_dvd_G : p ∣ G :=
      (hp_prim.dvd_iff_fraction_map_dvd_fraction_map (K := FractionRing K[X])).mpr
        (hp_map_dvd_g.trans (EuclideanDomain.gcd_dvd_right _ _))
    have hp_unit : IsUnit p := hrel hp_dvd_F hp_dvd_G
    have hp_deg0 : p.natDegree = 0 := natDegree_eq_zero_of_isUnit hp_unit
    have hg₁_deg : g₁.natDegree = g.natDegree := by
      rw [← natDegree_map_eq_of_injective (IsFractionRing.injective K[X] (FractionRing K[X])) g₁,
        hg₁, natDegree_C_mul hcL]
    have hp_deg_eq : p.natDegree = g₁.natDegree := by
      conv_rhs => rw [hg₁_eq]
      rw [natDegree_C_mul hcont_ne]
    omega
  have hg_unit : IsUnit g := isUnit_iff_degree_eq_zero.mpr (by
    rw [degree_eq_natDegree hg_ne, hg_deg]; rfl)
  obtain ⟨u, hu⟩ := hg_unit.exists_right_inv
  refine ⟨u * EuclideanDomain.gcdA (F.map ι) (G.map ι),
    u * EuclideanDomain.gcdB (F.map ι) (G.map ι), ?_⟩
  have hbez := EuclideanDomain.gcd_eq_gcd_ab (F.map ι) (G.map ι)
  calc u * EuclideanDomain.gcdA (F.map ι) (G.map ι) * F.map ι +
        u * EuclideanDomain.gcdB (F.map ι) (G.map ι) * G.map ι
      = (F.map ι * EuclideanDomain.gcdA (F.map ι) (G.map ι) +
          G.map ι * EuclideanDomain.gcdB (F.map ι) (G.map ι)) * u := by ring
    _ = g * u := by rw [← hbez]
    _ = 1 := hu

/-- The actual-degree resultant of two relatively prime bivariate polynomials is nonzero. -/
theorem resultant_ne_zero_of_isRelPrime (F G : K[X][X]) (hrel : IsRelPrime F G) :
    resultant F G F.natDegree G.natDegree ≠ 0 := by
  let L := FractionRing K[X]
  let ι := algebraMap K[X] L
  have hcop := isCoprime_map_fractionRing_of_isRelPrime F G hrel
  have hres := Polynomial.resultant_ne_zero (F.map ι) (G.map ι) hcop
  rw [natDegree_map_eq_of_injective (IsFractionRing.injective K[X] L),
    natDegree_map_eq_of_injective (IsFractionRing.injective K[X] L),
    resultant_map_map] at hres
  exact fun h => hres (by simp [h])

/-- A product of distinct linear factors divides any polynomial vanishing on all of them. -/
private theorem prod_X_sub_C_dvd_of_eval_eq_zero (p : K[X]) (Y : Finset K)
    (hY : ∀ y ∈ Y, p.eval y = 0) :
    (∏ y ∈ Y, (X - C y)) ∣ p := by
  classical
  induction Y using Finset.induction_on with
  | empty => simp
  | insert y s hy ih =>
    rw [Finset.prod_insert hy]
    have hp_y : (X - C y) ∣ p := dvd_iff_isRoot.mpr (hY y (Finset.mem_insert_self y s))
    have hp_s : (∏ w ∈ s, (X - C w)) ∣ p :=
      ih (fun w hw => hY w (Finset.mem_insert_of_mem hw))
    have hcop : IsCoprime (X - C y) (∏ w ∈ s, (X - C w)) := by
      refine IsCoprime.prod_right fun w hw => ?_
      have hne : y ≠ w := fun h => hy (h ▸ hw)
      exact Polynomial.isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hne).isUnit
    exact hcop.mul_dvd hp_y hp_s

/-- **Affine Plane Bézout with multiplicity at `[0:1:0]` (`L2b`).**
For relatively prime `F, G : K[X][X]` of total degrees `≤ m, d'` and `Y`-degrees `≤ b, b'`
with `b ≤ m` and `b' ≤ d'`, the number of distinct common affine zeros `(z, y) ∈ K × K` is at most
`m * d' - (m - b) * (d' - b')` (equivalently `b * d' + b' * m - b * b'`). -/
theorem plane_bezout_with_multiplicity (F G : K[X][X]) {m d' b b' : ℕ}
    (hrel : IsRelPrime F G)
    (hFm : WeightedSylvesterDegree.TotalDegreeLe F m)
    (hGd : WeightedSylvesterDegree.TotalDegreeLe G d')
    (hFb : F.natDegree ≤ b) (hbm : b ≤ m)
    (hGb : G.natDegree ≤ b') (hbd : b' ≤ d')
    (S : Finset (K × K))
    (hS : ∀ p ∈ S, (F.map (evalRingHom p.1)).eval p.2 = 0 ∧
      (G.map (evalRingHom p.1)).eval p.2 = 0) :
    S.card ≤ m * d' - (m - b) * (d' - b') := by
  classical
  have hres_ne : resultant F G F.natDegree G.natDegree ≠ 0 :=
    resultant_ne_zero_of_isRelPrime F G hrel
  let Zs : Finset K := S.image Prod.fst
  let Yz (z : K) : Finset K := (S.filter fun p => p.1 = z).image Prod.snd
  have hcard_eq : S.card = ∑ z ∈ Zs, (Yz z).card := by
    have hfib : S.card = ∑ z ∈ Zs, (S.filter fun p => p.1 = z).card :=
      Finset.card_eq_sum_card_image Prod.fst S
    rw [hfib]
    refine Finset.sum_congr rfl fun z _ => ?_
    symm
    refine Finset.card_image_of_injOn ?_
    intro p₁ hp₁ p₂ hp₂ hEq
    exact Prod.ext ((Finset.mem_filter.mp hp₁).2.trans (Finset.mem_filter.mp hp₂).2.symm) hEq
  have hfiber_dvd : ∀ z ∈ Zs, (X - C z) ^ (Yz z).card ∣ resultant F G F.natDegree G.natDegree := by
    intro z _
    let D : K[X] := ∏ y ∈ Yz z, (X - C y)
    have hD_deg : D.natDegree = (Yz z).card := by
      have hmon : ∀ y ∈ Yz z, (X - C y : K[X]).Monic := fun y _ => monic_X_sub_C y
      rw [natDegree_prod_of_monic _ _ hmon]
      simp
    have hDF : D ∣ F.map (evalRingHom z) := by
      apply prod_X_sub_C_dvd_of_eval_eq_zero
      intro y hy
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨hpS, hpz⟩ := Finset.mem_filter.mp hp
      rw [← hpz]
      exact (hS p hpS).1
    have hDG : D ∣ G.map (evalRingHom z) := by
      apply prod_X_sub_C_dvd_of_eval_eq_zero
      intro y hy
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨hpS, hpz⟩ := Finset.mem_filter.mp hp
      rw [← hpz]
      exact (hS p hpS).2
    have hne : F.map (evalRingHom z) ≠ 0 ∨ G.map (evalRingHom z) ≠ 0 := by
      by_contra hboth
      push Not at hboth
      have hdvd_C : ∀ H : K[X][X], H.map (evalRingHom z) = 0 → C (X - C z) ∣ H := by
        intro H hHz
        have hcoeff : ∀ j, (X - C z) ∣ H.coeff j := by
          intro j
          rw [dvd_iff_isRoot, IsRoot]
          have := congrArg (fun p : K[X] => p.coeff j) hHz
          simpa [coeff_map] using this
        choose q hq using hcoeff
        refine ⟨∑ j ∈ H.support, Polynomial.monomial j (q j), ?_⟩
        ext1 j
        rw [coeff_C_mul, finsetSum_coeff]
        by_cases hj : j ∈ H.support
        · rw [Finset.sum_eq_single j]
          · simp [hq j]
          · intro i _ hij; simp [Polynomial.coeff_monomial, hij]
          · intro h'; exact absurd hj h'
        · rw [Polynomial.notMem_support_iff.mp hj]
          symm
          have hsum0 : ∑ i ∈ H.support, (Polynomial.monomial i (q i)).coeff j = 0 := by
            apply Finset.sum_eq_zero
            intro i hi
            have hij : i ≠ j := fun h => hj (h ▸ hi)
            simp [Polynomial.coeff_monomial, hij]
          rw [hsum0, mul_zero]
      have hu : IsUnit (C (X - C z) : K[X][X]) :=
        hrel (hdvd_C F hboth.1) (hdvd_C G hboth.2)
      have hu' : IsUnit (X - C z : K[X]) := isUnit_C.mp hu
      have hd0 : (X - C z : K[X]).natDegree = 0 := natDegree_eq_zero_of_isUnit hu'
      rw [natDegree_X_sub_C] at hd0
      exact Nat.one_ne_zero hd0
    rcases hne with hFz | hGz
    · rw [← hD_deg]
      exact LogarithmicSectionHeights.common_factor_charge F G z D hFz hDF hDG
    · rw [← hD_deg]
      have hcomm := LogarithmicSectionHeights.common_factor_charge G F z D hGz hDG hDF
      rw [resultant_comm G F G.natDegree F.natDegree] at hcomm
      have hu : IsUnit ((-1 : K[X]) ^ (G.natDegree * F.natDegree)) := isUnit_neg_one.pow _
      exact (hu.dvd_mul_left).mp hcomm
  have hsum_le : S.card ≤ (resultant F G F.natDegree G.natDegree).natDegree := by
    rw [hcard_eq]
    exact SylvesterLocalMultiplicity.sum_local_orders_le_natDegree _ hres_ne Zs
      (fun z => (Yz z).card) hfiber_dvd
  have hres_deg : (resultant F G F.natDegree G.natDegree).natDegree ≤
      F.natDegree * d' + G.natDegree * m - F.natDegree * G.natDegree :=
    WeightedSylvesterDegree.natDegree_resultant_le F G hFm hGd
  have harith : F.natDegree * d' + G.natDegree * m - F.natDegree * G.natDegree ≤
      m * d' - (m - b) * (d' - b') := by
    have hF_le_m : F.natDegree ≤ m := hFb.trans hbm
    have hG_le_d : G.natDegree ≤ d' := hGb.trans hbd
    have h1 : (m - b) * (d' - b') ≤ (m - F.natDegree) * (d' - G.natDegree) :=
      Nat.mul_le_mul (by omega) (by omega)
    have h2 : F.natDegree * G.natDegree ≤ F.natDegree * d' + G.natDegree * m :=
      (Nat.mul_le_mul_left _ hG_le_d).trans (Nat.le_add_right _ _)
    have h3 : (m - b) * (d' - b') ≤ m * d' :=
      Nat.mul_le_mul (Nat.sub_le m b) (Nat.sub_le d' b')
    zify [h1, h2, h3, hbm, hbd, hF_le_m, hG_le_d] at h1 ⊢
    nlinarith
  exact (hsum_le.trans hres_deg).trans harith

/-- Irreducible specialization of `plane_bezout_with_multiplicity`: if `F` is irreducible and
does not divide `G`, then `F` and `G` are relatively prime and obey the multiplicity Bézout cap. -/
theorem plane_bezout_irreducible_with_multiplicity (F G : K[X][X]) {m d' b b' : ℕ}
    (hF : Irreducible F) (hndvd : ¬ F ∣ G)
    (hFm : WeightedSylvesterDegree.TotalDegreeLe F m)
    (hGd : WeightedSylvesterDegree.TotalDegreeLe G d')
    (hFb : F.natDegree ≤ b) (hbm : b ≤ m)
    (hGb : G.natDegree ≤ b') (hbd : b' ≤ d')
    (S : Finset (K × K))
    (hS : ∀ p ∈ S, (F.map (evalRingHom p.1)).eval p.2 = 0 ∧
      (G.map (evalRingHom p.1)).eval p.2 = 0) :
    S.card ≤ m * d' - (m - b) * (d' - b') := by
  have hrel : IsRelPrime F G := by
    intro d hdF hdG
    obtain ⟨q, hq⟩ := hdF
    rcases hF.isUnit_or_isUnit hq with hu | hqu
    · exact hu
    · exfalso
      obtain ⟨w, hw⟩ := hqu
      have hFd : F ∣ d := ⟨↑w⁻¹, by rw [hq, ← hw, mul_assoc, Units.mul_inv, mul_one]⟩
      exact hndvd (hFd.trans hdG)
  exact plane_bezout_with_multiplicity F G hrel hFm hGd hFb hbm hGb hbd S hS

end AffineMultiplicityBezout

section QuotientDimensionBezout

open MvPolynomial

variable {B : Type*} [Field B]

/-- Dehomogenization `B[X₀, X₁, X₂] →ₐ[B] B[X₀, X₁]` setting `X₂ = 1`. -/
def dehom : MvPolynomial (Fin 3) B →ₐ[B] MvPolynomial (Fin 2) B :=
  MvPolynomial.aeval ![MvPolynomial.X 0, MvPolynomial.X 1, 1]

/-- Extend a 2-variable exponent vector by a third coordinate `k`. -/
def ext3 (m : Fin 2 →₀ ℕ) (k : ℕ) : Fin 3 →₀ ℕ :=
  Finsupp.single 0 (m 0) + Finsupp.single 1 (m 1) + Finsupp.single 2 k

@[simp]
theorem ext3_apply_0 (m : Fin 2 →₀ ℕ) (k : ℕ) : ext3 m k 0 = m 0 := by simp [ext3]

@[simp]
theorem ext3_apply_1 (m : Fin 2 →₀ ℕ) (k : ℕ) : ext3 m k 1 = m 1 := by simp [ext3]

@[simp]
theorem ext3_apply_2 (m : Fin 2 →₀ ℕ) (k : ℕ) : ext3 m k 2 = k := by simp [ext3]

theorem m2_sum (m : Fin 2 →₀ ℕ) : m.sum (fun _ v => v) = m 0 + m 1 := by
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two]

theorem m3_sum (m : Fin 3 →₀ ℕ) : m.sum (fun _ v => v) = m 0 + m 1 + m 2 := by
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_three]

theorem weight_one_eq_sum {σ : Type*} (m : σ →₀ ℕ) :
    Finsupp.weight (1 : σ → ℕ) m = m.sum (fun _ v => v) := by
  simp [Finsupp.weight_apply]

theorem degree_eq_sum {σ : Type*} (m : σ →₀ ℕ) :
    Finsupp.degree m = m.sum (fun _ v => v) := rfl

theorem isHomogeneous_monomial_of_sum {σ : Type*} (m : σ →₀ ℕ) (c : B) (n : ℕ)
    (hm : m.sum (fun _ v => v) = n) :
    (MvPolynomial.monomial m c).IsHomogeneous n := by
  classical
  intro k hk
  rw [MvPolynomial.coeff_monomial] at hk
  split_ifs at hk with heq
  · subst heq
    rw [weight_one_eq_sum]
    exact hm
  · exact absurd rfl hk

theorem ext3_sum (m : Fin 2 →₀ ℕ) (k : ℕ) :
    (ext3 m k).sum (fun _ v => v) = m 0 + m 1 + k := by
  rw [m3_sum]; simp

/-- Restrict a 3-variable exponent vector to its first two coordinates. -/
def proj2 (m : Fin 3 →₀ ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 (m 0) + Finsupp.single 1 (m 1)

@[simp]
theorem proj2_apply_0 (m : Fin 3 →₀ ℕ) : proj2 m 0 = m 0 := by simp [proj2]

@[simp]
theorem proj2_apply_1 (m : Fin 3 →₀ ℕ) : proj2 m 1 = m 1 := by simp [proj2]

theorem ext3_proj2 (m : Fin 3 →₀ ℕ) : ext3 (proj2 m) (m 2) = m := by
  ext i; fin_cases i <;> simp

theorem proj2_ext3 (m : Fin 2 →₀ ℕ) (k : ℕ) : proj2 (ext3 m k) = m := by
  ext i; fin_cases i <;> simp

theorem dehom_monomial (m : Fin 3 →₀ ℕ) (c : B) :
    dehom (MvPolynomial.monomial m c) = MvPolynomial.monomial (proj2 m) c := by
  classical
  simp only [dehom, MvPolynomial.aeval_monomial, MvPolynomial.algebraMap_eq]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_three]
  have h0 : (![MvPolynomial.X 0, MvPolynomial.X 1, (1 : MvPolynomial (Fin 2) B)] :
      Fin 3 → MvPolynomial (Fin 2) B) 0 = MvPolynomial.X 0 := rfl
  have h1 : (![MvPolynomial.X 0, MvPolynomial.X 1, (1 : MvPolynomial (Fin 2) B)] :
      Fin 3 → MvPolynomial (Fin 2) B) 1 = MvPolynomial.X 1 := rfl
  have h2 : (![MvPolynomial.X 0, MvPolynomial.X 1, (1 : MvPolynomial (Fin 2) B)] :
      Fin 3 → MvPolynomial (Fin 2) B) 2 = 1 := rfl
  rw [h0, h1, h2, one_pow, mul_one, MvPolynomial.X, MvPolynomial.X,
    MvPolynomial.monomial_pow, MvPolynomial.monomial_pow, MvPolynomial.monomial_mul_monomial,
    MvPolynomial.C_mul_monomial]
  simp [proj2, one_pow, mul_one, Finsupp.smul_single, smul_eq_mul]

/-- Homogenization of a 2-variable polynomial `f` to degree `d` (intended for `f.totalDegree ≤ d`). -/
def homog (d : ℕ) (f : MvPolynomial (Fin 2) B) : MvPolynomial (Fin 3) B :=
  ∑ m ∈ f.support, MvPolynomial.monomial (ext3 m (d - (m 0 + m 1))) (f.coeff m)

theorem homog_isHomogeneous (d : ℕ) (f : MvPolynomial (Fin 2) B) (hf : f.totalDegree ≤ d) :
    (homog d f).IsHomogeneous d := by
  classical
  unfold homog
  refine Submodule.sum_mem (homogeneousSubmodule (Fin 3) B d) fun m hm => ?_
  have hle : m 0 + m 1 ≤ d := by
    have := Finset.le_sup (f := fun s : Fin 2 →₀ ℕ => s.sum fun _ v => v) hm
    rw [m2_sum] at this
    exact this.trans hf
  rw [mem_homogeneousSubmodule]
  apply isHomogeneous_monomial_of_sum
  rw [ext3_sum]
  omega

theorem dehom_homog (d : ℕ) (f : MvPolynomial (Fin 2) B) : dehom (homog d f) = f := by
  classical
  unfold homog
  rw [map_sum]
  calc ∑ m ∈ f.support, dehom (MvPolynomial.monomial (ext3 m (d - (m 0 + m 1))) (f.coeff m))
      = ∑ m ∈ f.support, MvPolynomial.monomial m (f.coeff m) := by
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [dehom_monomial, proj2_ext3]
    _ = f := by rw [← MvPolynomial.as_sum f]

/-- Dehomogenization is injective on homogeneous polynomials of a fixed degree `d`. -/
theorem dehom_inj_on_homogeneous (d : ℕ) {F G : MvPolynomial (Fin 3) B}
    (hF : F.IsHomogeneous d) (hG : G.IsHomogeneous d) (hFG : dehom F = dehom G) :
    F = G := by
  classical
  ext m
  by_cases hm : m 0 + m 1 + m 2 = d
  · have hcoeff (H : MvPolynomial (Fin 3) B) (hH : H.IsHomogeneous d) :
        (dehom H).coeff (proj2 m) = H.coeff m := by
      conv_lhs => rw [H.as_sum]
      rw [map_sum, MvPolynomial.coeff_sum]
      by_cases hms : m ∈ H.support
      · rw [Finset.sum_eq_single m]
        · rw [dehom_monomial, MvPolynomial.coeff_monomial, ite_eq_left_iff]
          intro hne; exact absurd rfl hne
        · intro n hn hnm
          rw [dehom_monomial, MvPolynomial.coeff_monomial]
          split_ifs with heq
          · exfalso
            have hnd : n 0 + n 1 + n 2 = d := by
              have h := hH (MvPolynomial.mem_support_iff.mp hn)
              rwa [weight_one_eq_sum, m3_sum] at h
            have h0 : n 0 = m 0 := by simpa using congrArg (fun f : Fin 2 →₀ ℕ => f 0) heq
            have h1 : n 1 = m 1 := by simpa using congrArg (fun f : Fin 2 →₀ ℕ => f 1) heq
            apply hnm
            ext i
            fin_cases i
            · exact h0
            · exact h1
            · change n 2 = m 2; omega
          · rfl
        · intro h'; exact absurd hms h'
      · rw [MvPolynomial.notMem_support_iff.mp hms]
        apply Finset.sum_eq_zero
        intro n hn
        rw [dehom_monomial, MvPolynomial.coeff_monomial]
        split_ifs with heq
        · exfalso
          have hnd : n 0 + n 1 + n 2 = d := by
            have h := hH (MvPolynomial.mem_support_iff.mp hn)
            rwa [weight_one_eq_sum, m3_sum] at h
          have h0 : n 0 = m 0 := by simpa using congrArg (fun f : Fin 2 →₀ ℕ => f 0) heq
          have h1 : n 1 = m 1 := by simpa using congrArg (fun f : Fin 2 →₀ ℕ => f 1) heq
          have hnm : n = m := by
            ext i
            fin_cases i
            · exact h0
            · exact h1
            · change n 2 = m 2; omega
          exact hms (hnm ▸ hn)
        · rfl
    rw [← hcoeff F hF, ← hcoeff G hG, hFG]
  · have hF0 : F.coeff m = 0 := by
      by_contra h
      have h1 := hF h
      rw [weight_one_eq_sum, m3_sum] at h1
      exact hm h1
    have hG0 : G.coeff m = 0 := by
      by_contra h
      have h1 := hG h
      rw [weight_one_eq_sum, m3_sum] at h1
      exact hm h1
    rw [hF0, hG0]

theorem homog_linear_comb (d : ℕ) {ι : Type*} (s : Finset ι) (c : ι → B)
    (p : ι → MvPolynomial (Fin 2) B) (hp : ∀ i ∈ s, (p i).totalDegree ≤ d) :
    homog d (∑ i ∈ s, c i • p i) = ∑ i ∈ s, c i • homog d (p i) := by
  classical
  have hdeg_sum : (∑ i ∈ s, c i • p i).totalDegree ≤ d := by
    refine (MvPolynomial.totalDegree_finsetSum s _).trans (Finset.sup_le fun i hi => ?_)
    exact (MvPolynomial.totalDegree_smul_le (c i) (p i)).trans (hp i hi)
  have hhomL : (homog d (∑ i ∈ s, c i • p i)).IsHomogeneous d :=
    homog_isHomogeneous d _ hdeg_sum
  have hhomR : (∑ i ∈ s, c i • homog d (p i)).IsHomogeneous d := by
    rw [← mem_homogeneousSubmodule]
    exact Submodule.sum_mem _ fun i hi =>
      Submodule.smul_mem _ _ ((mem_homogeneousSubmodule _ _).mpr (homog_isHomogeneous d _ (hp i hi)))
  have hdehom : dehom (homog d (∑ i ∈ s, c i • p i)) = dehom (∑ i ∈ s, c i • homog d (p i)) := by
    rw [dehom_homog, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, dehom_homog]
  exact dehom_inj_on_homogeneous d hhomL hhomR hdehom

/-- The `k`-th homogeneous component of a product is the convolution of homogeneous components. -/
private theorem homogeneousComponent_mul_eq {σ : Type*} (k : ℕ) (G Q : MvPolynomial σ B) :
    homogeneousComponent k (G * Q) =
      ∑ p ∈ Finset.antidiagonal k, homogeneousComponent p.1 G * homogeneousComponent p.2 Q := by
  classical
  ext m
  rw [MvPolynomial.coeff_homogeneousComponent, MvPolynomial.coeff_sum]
  by_cases hm : Finsupp.degree m = k
  · rw [ite_eq_left_iff.mpr fun h => absurd hm h, MvPolynomial.coeff_mul]
    simp only [MvPolynomial.coeff_mul, MvPolynomial.coeff_homogeneousComponent]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ab hab => ?_
    have hab_eq : ab.1 + ab.2 = m := Finset.mem_antidiagonal.mp hab
    have hsum_ab : Finsupp.degree ab.1 + Finsupp.degree ab.2 = k := by
      rw [← map_add, hab_eq, hm]
    let pair : ℕ × ℕ := (Finsupp.degree ab.1, Finsupp.degree ab.2)
    have hpair_mem : pair ∈ Finset.antidiagonal k := Finset.mem_antidiagonal.mpr hsum_ab
    rw [Finset.sum_eq_single pair]
    · simp [pair]
    · rintro ⟨a, b⟩ _ hne
      by_cases ha : Finsupp.degree ab.1 = a
      · by_cases hb : Finsupp.degree ab.2 = b
        · exfalso; exact hne (Prod.ext ha.symm hb.symm)
        · simp [hb]
      · simp [ha]
    · intro h'; exact absurd hpair_mem h'
  · rw [ite_eq_right_iff.mpr fun h => absurd h hm]
    symm
    apply Finset.sum_eq_zero
    rintro ⟨a, b⟩ hab
    have hab_k : a + b = k := Finset.mem_antidiagonal.mp hab
    rw [MvPolynomial.coeff_mul]
    apply Finset.sum_eq_zero
    rintro ⟨u, v⟩ huv
    have huv_m : u + v = m := Finset.mem_antidiagonal.mp huv
    simp only [MvPolynomial.coeff_homogeneousComponent]
    split_ifs with hu hv
    · exfalso
      apply hm
      rw [← huv_m, map_add, hu, hv, hab_k]
    · simp
    · simp
    · simp

/-- Every divisor of a nonzero homogeneous polynomial in `MvPolynomial σ B` is homogeneous. -/
theorem isHomogeneous_of_dvd {σ : Type*} {F G : MvPolynomial σ B} {d : ℕ}
    (hF : F.IsHomogeneous d) (hFne : F ≠ 0) (hdvd : G ∣ F) :
    ∃ k, G.IsHomogeneous k := by
  classical
  obtain ⟨Q, hQ⟩ := hdvd
  have hGne : G ≠ 0 := by rintro rfl; simp at hQ; exact hFne hQ
  have hQne : Q ≠ 0 := by rintro rfl; simp at hQ; exact hFne hQ
  let degs (P : MvPolynomial σ B) : Finset ℕ := P.support.image fun m => Finsupp.degree m
  have hcomp_ne (P : MvPolynomial σ B) (k : ℕ) (hk : k ∈ degs P) :
      homogeneousComponent k P ≠ 0 := by
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hk
    intro h0
    have h := congrArg (fun p : MvPolynomial σ B => p.coeff m) h0
    rw [MvPolynomial.coeff_homogeneousComponent] at h
    exact MvPolynomial.mem_support_iff.mp hm (by simpa using h)
  have hcomp_zero_of_notMem (P : MvPolynomial σ B) (k : ℕ) (hk : k ∉ degs P) :
      homogeneousComponent k P = 0 := by
    ext m
    rw [MvPolynomial.coeff_homogeneousComponent]
    simp only [AddMonoidAlgebra.coeff_zero]
    split_ifs with hmk
    · by_contra hne
      exact hk (Finset.mem_image.mpr ⟨m, MvPolynomial.mem_support_iff.mpr hne, hmk⟩)
    · rfl
  have hGnonempty : (degs G).Nonempty := (MvPolynomial.support_nonempty.mpr hGne).image _
  have hQnonempty : (degs Q).Nonempty := (MvPolynomial.support_nonempty.mpr hQne).image _
  let gMin := (degs G).min' hGnonempty
  let gMax := (degs G).max' hGnonempty
  let qMin := (degs Q).min' hQnonempty
  let qMax := (degs Q).max' hQnonempty
  have hmin_ne : homogeneousComponent (gMin + qMin) F ≠ 0 := by
    rw [hQ, homogeneousComponent_mul_eq, Finset.sum_eq_single (gMin, qMin)]
    · exact mul_ne_zero (hcomp_ne G gMin (Finset.min'_mem _ _))
        (hcomp_ne Q qMin (Finset.min'_mem _ _))
    · rintro ⟨a, b⟩ hab hne
      have hab' : a + b = gMin + qMin := Finset.mem_antidiagonal.mp hab
      by_cases ha : a ∈ degs G
      · by_cases hb : b ∈ degs Q
        · have ha_ge : gMin ≤ a := Finset.min'_le _ _ ha
          have hb_ge : qMin ≤ b := Finset.min'_le _ _ hb
          exfalso; exact hne (Prod.ext (by omega) (by omega))
        · rw [hcomp_zero_of_notMem Q b hb, mul_zero]
      · rw [hcomp_zero_of_notMem G a ha, zero_mul]
    · intro h'
      exact absurd (Finset.mem_antidiagonal.mpr (rfl : gMin + qMin = gMin + qMin)) h'
  have hmax_ne : homogeneousComponent (gMax + qMax) F ≠ 0 := by
    rw [hQ, homogeneousComponent_mul_eq, Finset.sum_eq_single (gMax, qMax)]
    · exact mul_ne_zero (hcomp_ne G gMax (Finset.max'_mem _ _))
        (hcomp_ne Q qMax (Finset.max'_mem _ _))
    · rintro ⟨a, b⟩ hab hne
      have hab' : a + b = gMax + qMax := Finset.mem_antidiagonal.mp hab
      by_cases ha : a ∈ degs G
      · by_cases hb : b ∈ degs Q
        · have ha_le : a ≤ gMax := Finset.le_max' _ _ ha
          have hb_le : b ≤ qMax := Finset.le_max' _ _ hb
          exfalso; exact hne (Prod.ext (by omega) (by omega))
        · rw [hcomp_zero_of_notMem Q b hb, mul_zero]
      · rw [hcomp_zero_of_notMem G a ha, zero_mul]
    · intro h'
      exact absurd (Finset.mem_antidiagonal.mpr (rfl : gMax + qMax = gMax + qMax)) h'
  have hF_comp : ∀ k, homogeneousComponent k F ≠ 0 → k = d := by
    intro k hk
    by_contra hkd
    apply hk
    ext m
    rw [MvPolynomial.coeff_homogeneousComponent]
    simp only [AddMonoidAlgebra.coeff_zero]
    split_ifs with hmk
    · by_contra hne
      have h1 := hF hne
      rw [weight_one_eq_sum] at h1
      exact hkd (hmk.symm.trans h1)
    · rfl
  have h1 : gMin + qMin = d := hF_comp _ hmin_ne
  have h2 : gMax + qMax = d := hF_comp _ hmax_ne
  have hg_le : gMin ≤ gMax := Finset.min'_le _ _ (Finset.max'_mem _ _)
  have hq_le : qMin ≤ qMax := Finset.min'_le _ _ (Finset.max'_mem _ _)
  have hg_eq : gMin = gMax := by omega
  refine ⟨gMin, ?_⟩
  intro m hm
  rw [weight_one_eq_sum]
  have hmem : Finsupp.degree m ∈ degs G :=
    Finset.mem_image.mpr ⟨m, MvPolynomial.mem_support_iff.mpr hm, rfl⟩
  have hlo : gMin ≤ Finsupp.degree m := Finset.min'_le _ _ hmem
  have hhi : Finsupp.degree m ≤ gMax := Finset.le_max' _ _ hmem
  change Finsupp.degree m = gMin
  omega

/-- If `H₁, H₂ : MvPolynomial (Fin 2) B` are nonzero and relatively prime, their minimal
homogenizations `homog H₁.totalDegree H₁` and `homog H₂.totalDegree H₂` are relatively prime
in `MvPolynomial (Fin 3) B`. -/
theorem isRelPrime_homog (H₁ H₂ : MvPolynomial (Fin 2) B) (h₁ : H₁ ≠ 0) (_h₂ : H₂ ≠ 0)
    (hrel : IsRelPrime H₁ H₂) :
    IsRelPrime (homog H₁.totalDegree H₁) (homog H₂.totalDegree H₂) := by
  classical
  let F₁ := homog H₁.totalDegree H₁
  let F₂ := homog H₂.totalDegree H₂
  have hF₁_hom : F₁.IsHomogeneous H₁.totalDegree := homog_isHomogeneous _ _ le_rfl
  have hF₁_ne : F₁ ≠ 0 := by
    intro h0
    have := congrArg dehom h0
    rw [dehom_homog, map_zero] at this
    exact h₁ this
  have hX2_ndvd : ¬ (MvPolynomial.X 2 : MvPolynomial (Fin 3) B) ∣ F₁ := by
    intro ⟨Q, hQ⟩
    have hsupp_ne : H₁.support.Nonempty := MvPolynomial.support_nonempty.mpr h₁
    obtain ⟨m, hm, hm_max⟩ :=
      Finset.exists_mem_eq_sup H₁.support hsupp_ne (fun s : Fin 2 →₀ ℕ => s.sum fun _ v => v)
    have hdeg_eq : m 0 + m 1 = H₁.totalDegree := by
      rw [← m2_sum]; exact hm_max.symm
    have hcoeff_F1 : F₁.coeff (ext3 m 0) = H₁.coeff m := by
      simp only [F₁, homog, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
      rw [Finset.sum_eq_single m]
      · simp [hdeg_eq]
      · intro n _ hnm
        split_ifs with heq
        · exfalso
          exact hnm (by simpa [proj2_ext3] using congrArg proj2 heq)
        · rfl
      · intro h'; exact absurd hm h'
    have hcoeff_zero : (MvPolynomial.X 2 * Q).coeff (ext3 m 0) = 0 := by
      rw [MvPolynomial.coeff_mul]
      apply Finset.sum_eq_zero
      rintro ⟨a, b⟩ hab
      have h2 : a 2 + b 2 = 0 := by
        have := congrArg (fun f : Fin 3 →₀ ℕ => f 2) (Finset.mem_antidiagonal.mp hab)
        simpa using this
      have ha : (MvPolynomial.X 2 : MvPolynomial (Fin 3) B).coeff a = 0 := by
        rw [MvPolynomial.coeff_X]
        split_ifs with heq
        · exfalso
          have := congrArg (fun f : Fin 3 →₀ ℕ => f 2) heq
          simp at this
          omega
        · rfl
      rw [ha, zero_mul]
    rw [← hQ, hcoeff_F1] at hcoeff_zero
    exact MvPolynomial.mem_support_iff.mp hm hcoeff_zero
  intro G hGF₁ hGF₂
  obtain ⟨k, hGk⟩ := isHomogeneous_of_dvd hF₁_hom hF₁_ne hGF₁
  have hG_dehom_dvd1 : dehom G ∣ H₁ := by
    rw [← dehom_homog H₁.totalDegree H₁]
    exact map_dvd dehom hGF₁
  have hG_dehom_dvd2 : dehom G ∣ H₂ := by
    rw [← dehom_homog H₂.totalDegree H₂]
    exact map_dvd dehom hGF₂
  have hunit_dehom : IsUnit (dehom G) := hrel hG_dehom_dvd1 hG_dehom_dvd2
  obtain ⟨c, hc_unit, hc_eq⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hunit_dehom
  have hG_eq : G = MvPolynomial.C c * MvPolynomial.X 2 ^ k := by
    have hRHS_hom : (MvPolynomial.C c * (MvPolynomial.X 2 : MvPolynomial (Fin 3) B) ^ k).IsHomogeneous k := by
      simpa using (MvPolynomial.isHomogeneous_C (Fin 3) c).mul
        ((MvPolynomial.isHomogeneous_X B (2 : Fin 3)).pow k)
    have hdehom_eq : dehom G = dehom (MvPolynomial.C c * MvPolynomial.X 2 ^ k) := by
      rw [hc_eq, map_mul, map_pow, dehom]
      simp
    exact dehom_inj_on_homogeneous k hGk hRHS_hom hdehom_eq
  cases k with
  | zero =>
    rw [hG_eq, pow_zero, mul_one]
    exact hc_unit.map MvPolynomial.C
  | succ k' =>
    exfalso
    apply hX2_ndvd
    rw [hG_eq] at hGF₁
    exact ((dvd_pow_self _ (Nat.succ_ne_zero k')).trans (dvd_mul_left _ _)).trans hGF₁

/-- The finite set of exponent vectors of degree `N` in 3 variables. -/
def homExps (N : ℕ) : Finset (Fin 3 →₀ ℕ) :=
  (((Finset.range (N + 1)) ×ˢ (Finset.range (N + 1))).filter fun ij => ij.1 + ij.2 ≤ N).image
    fun ij => Finsupp.single 0 ij.1 + Finsupp.single 1 ij.2 + Finsupp.single 2 (N - (ij.1 + ij.2))

theorem card_pairs_le (N : ℕ) :
    (((Finset.range (N + 1)) ×ˢ (Finset.range (N + 1))).filter fun ij => ij.1 + ij.2 ≤ N).card =
      (N + 2).choose 2 := by
  induction N with
  | zero => decide
  | succ n ih =>
    let S (k : ℕ) := ((Finset.range (k + 1)) ×ˢ (Finset.range (k + 1))).filter fun ij => ij.1 + ij.2 ≤ k
    let diag := (Finset.range (n + 2)).image fun i => (i, n + 1 - i)
    have hdisj : Disjoint (S n) diag := by
      rw [Finset.disjoint_left]
      intro ij hij hdiag
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hdiag
      have h1 := (Finset.mem_filter.mp hij).2
      have hi' : i < n + 2 := Finset.mem_range.mp hi
      omega
    have hunion : S (n + 1) = S n ∪ diag := by
      ext ⟨i, j⟩
      simp only [S, diag, Finset.mem_union, Finset.mem_filter, Finset.mem_product,
        Finset.mem_range, Finset.mem_image]
      constructor
      · intro ⟨⟨hi, hj⟩, hij⟩
        by_cases h : i + j ≤ n
        · left; exact ⟨⟨by omega, by omega⟩, h⟩
        · right; exact ⟨i, by omega, Prod.ext rfl (by omega)⟩
      · rintro (⟨⟨hi, hj⟩, hij⟩ | ⟨k, hk, hEq⟩)
        · exact ⟨⟨by omega, by omega⟩, by omega⟩
        · rcases Prod.mk.inj hEq with ⟨rfl, rfl⟩
          exact ⟨⟨by omega, by omega⟩, by omega⟩
    have hdiag_card : diag.card = n + 2 := by
      rw [Finset.card_image_of_injOn]
      · simp
      · intro a _ b _ hEq; exact (Prod.mk.inj hEq).1
    change (S (n + 1)).card = (n + 3).choose 2
    rw [hunion, Finset.card_union_of_disjoint hdisj, ih, hdiag_card]
    have hchoose : (n + 3).choose 2 = (n + 2).choose 2 + (n + 2) := by
      rw [Nat.choose_succ_succ (n + 2) 1, Nat.choose_one_right, add_comm]
    omega

theorem card_homExps (N : ℕ) : (homExps N).card = (N + 2).choose 2 := by
  unfold homExps
  rw [Finset.card_image_of_injOn]
  · exact card_pairs_le N
  · intro a _ b _ hEq
    have h0 := congrArg (fun f : Fin 3 →₀ ℕ => f 0) hEq
    have h1 := congrArg (fun f : Fin 3 →₀ ℕ => f 1) hEq
    simp at h0 h1
    exact Prod.ext h0 h1

theorem mem_homExps_iff (N : ℕ) (m : Fin 3 →₀ ℕ) :
    m ∈ homExps N ↔ m.sum (fun _ v => v) = N := by
  simp only [homExps, Finset.mem_image, Finset.mem_filter, Finset.mem_product,
    Finset.mem_range, m3_sum]
  constructor
  · rintro ⟨⟨i, j⟩, ⟨⟨_, _⟩, hij⟩, rfl⟩
    simp; omega
  · intro hm
    refine ⟨(m 0, m 1), ⟨⟨by omega, by omega⟩, by omega⟩, ?_⟩
    ext k
    fin_cases k
    · simp
    · simp
    · simp; omega

/-- The homogeneous submodule of degree `N` in 3 variables is finite-dimensional of dimension
`C(N + 2, 2)`. -/
theorem finrank_homogeneousSubmodule_fin3 (N : ℕ) :
    Module.Finite B (homogeneousSubmodule (Fin 3) B N) ∧
    Module.finrank B (homogeneousSubmodule (Fin 3) B N) = (N + 2).choose 2 := by
  classical
  let V := homogeneousSubmodule (Fin 3) B N
  let bFun : ↥(homExps N) → V := fun m =>
    ⟨MvPolynomial.monomial m.val 1,
      (mem_homogeneousSubmodule N _).mpr
        (isHomogeneous_monomial_of_sum m.val (1 : B) N ((mem_homExps_iff N m.val).mp m.property))⟩
  have hli : LinearIndependent B bFun := by
    rw [Fintype.linearIndependent_iff]
    intro g hg m
    have hval := congrArg (fun v : V => v.val.coeff m.val) hg
    simp only [ZeroMemClass.coe_zero, AddMonoidAlgebra.coeff_zero, Submodule.coe_sum,
      SetLike.val_smul, MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, smul_eq_mul,
      bFun, MvPolynomial.coeff_monomial] at hval
    rw [Finset.sum_eq_single m] at hval
    · simpa using hval
    · intro k _ hkm
      have hne : k.val ≠ m.val := fun h => hkm (Subtype.ext h)
      simp [hne]
    · intro h'; exact absurd (Finset.mem_univ m) h'
  have hsp : ⊤ ≤ Submodule.span B (Set.range bFun) := by
    intro v _
    have hv_sum : v.val = ∑ m ∈ homExps N, (v.val.coeff m) • MvPolynomial.monomial m 1 := by
      ext m
      rw [MvPolynomial.coeff_sum]
      by_cases hm : m ∈ homExps N
      · rw [Finset.sum_eq_single m]
        · simp
        · intro k _ hkm; simp [MvPolynomial.coeff_monomial, hkm]
        · intro h'; exact absurd hm h'
      · have h0 : v.val.coeff m = 0 := by
          by_contra hne
          have hwt := ((mem_homogeneousSubmodule N _).mp v.property) hne
          rw [weight_one_eq_sum] at hwt
          exact hm ((mem_homExps_iff N m).mpr hwt)
        rw [h0]
        symm
        apply Finset.sum_eq_zero
        intro k hk
        have hkm : k ≠ m := fun h => hm (h ▸ hk)
        simp [MvPolynomial.coeff_monomial, hkm]
    have hv_eq : v = ∑ m : ↥(homExps N), (v.val.coeff m.val) • bFun m := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      simpa only [SetLike.val_smul, bFun] using hv_sum.trans ((homExps N).sum_coe_sort _).symm
    rw [hv_eq]
    exact Submodule.sum_mem _ fun m _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)
  let bas : Basis ↥(homExps N) B V := Basis.mk hli hsp
  have : Module.Finite B V := Module.Finite.of_basis bas
  refine ⟨inferInstance, ?_⟩
  rw [Module.finrank_eq_card_basis bas, Fintype.card_coe, card_homExps N]

/-- Binomial identity for the exact sequence of homogeneous plane curves:
`C(N + 2, 2) + C(N - d₁ - d₂ + 2, 2) = C(N - d₁ + 2, 2) + C(N - d₂ + 2, 2) + d₁ * d₂`. -/
private theorem choose_bezout_identity (N d₁ d₂ : ℕ) (hN : d₁ + d₂ ≤ N) :
    (N + 2).choose 2 + (N - d₁ - d₂ + 2).choose 2 =
      (N - d₁ + 2).choose 2 + (N - d₂ + 2).choose 2 + d₁ * d₂ := by
  have h2 (k : ℕ) : 2 * (k + 2).choose 2 = (k + 2) * (k + 1) := by
    rw [Nat.choose_two_right]
    have hsub : k + 2 - 1 = k + 1 := by omega
    rw [hsub]
    have heven : Even ((k + 2) * (k + 1)) := by
      rcases Nat.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
      · exact ⟨(m + 1) * (2 * m + 1), by ring⟩
      · exact ⟨(2 * m + 3) * (m + 1), by ring⟩
    obtain ⟨t, ht⟩ := heven
    omega
  have h1 := h2 N
  have h3 := h2 (N - d₁ - d₂)
  have h4 := h2 (N - d₁)
  have h5 := h2 (N - d₂)
  zify [hN, show d₁ ≤ N by omega, show d₂ ≤ N by omega,
    show d₂ ≤ N - d₁ by omega] at h1 h3 h4 h5 ⊢
  nlinarith

/-- **Fulton's exact sequence Bézout dimension formula:**
For relatively prime nonzero homogeneous `F₁, F₂ : MvPolynomial (Fin 3) B` of degrees `d₁, d₂`
and any `N ≥ d₁ + d₂`, the homogeneous ideal `(F₁, F₂)_N` has codimension `d₁ * d₂` in
`homogeneousSubmodule (Fin 3) B N`. -/
theorem homogeneous_quotient_finrank (F₁ F₂ : MvPolynomial (Fin 3) B) {d₁ d₂ N : ℕ}
    (hF₁ : F₁.IsHomogeneous d₁) (hF₂ : F₂.IsHomogeneous d₂)
    (_hF₁_ne : F₁ ≠ 0) (hF₂_ne : F₂ ≠ 0)
    (hrel : IsRelPrime F₁ F₂) (hN : d₁ + d₂ ≤ N) :
    let V (k : ℕ) := homogeneousSubmodule (Fin 3) B k
    let β : V (N - d₁) × V (N - d₂) →ₗ[B] V N :=
      { toFun := fun ab => ⟨ab.1.val * F₁ + ab.2.val * F₂, by
          rw [mem_homogeneousSubmodule]
          have h1 : (ab.1.val * F₁).IsHomogeneous N := by
            have := ((mem_homogeneousSubmodule _ _).mp ab.1.property).mul hF₁
            rwa [Nat.sub_add_cancel (by omega)] at this
          have h2 : (ab.2.val * F₂).IsHomogeneous N := by
            have := ((mem_homogeneousSubmodule _ _).mp ab.2.property).mul hF₂
            rwa [Nat.sub_add_cancel (by omega)] at this
          exact h1.add h2⟩
        map_add' := fun x y => by apply Subtype.ext; dsimp; ring
        map_smul' := fun c x => by apply Subtype.ext; simp [smul_add] }
    Module.finrank B (V N ⧸ LinearMap.range β) = d₁ * d₂ := by
  classical
  intro V β
  have : Module.Finite B (V N) := (finrank_homogeneousSubmodule_fin3 (B := B) N).1
  have : Module.Finite B (V (N - d₁)) := (finrank_homogeneousSubmodule_fin3 (B := B) (N - d₁)).1
  have : Module.Finite B (V (N - d₂)) := (finrank_homogeneousSubmodule_fin3 (B := B) (N - d₂)).1
  have : Module.Finite B (V (N - d₁ - d₂)) :=
    (finrank_homogeneousSubmodule_fin3 (B := B) (N - d₁ - d₂)).1
  let α : V (N - d₁ - d₂) →ₗ[B] V (N - d₁) × V (N - d₂) :=
    { toFun := fun c =>
        (⟨c.val * F₂, by
            rw [mem_homogeneousSubmodule]
            have := ((mem_homogeneousSubmodule _ _).mp c.property).mul hF₂
            rwa [Nat.sub_add_cancel (by omega)] at this⟩,
         ⟨-(c.val * F₁), by
            rw [mem_homogeneousSubmodule]
            have := (((mem_homogeneousSubmodule _ _).mp c.property).mul hF₁).neg
            rwa [show N - d₁ - d₂ + d₁ = N - d₂ by omega] at this⟩)
      map_add' := fun x y => by
        apply Prod.ext <;> apply Subtype.ext <;> dsimp <;> ring
      map_smul' := fun r x => by
        apply Prod.ext <;> apply Subtype.ext <;> simp [smul_neg] }
  have hα_inj : Function.Injective α := by
    intro c₁ c₂ hEq
    have h1 := congrArg (fun p : V (N - d₁) × V (N - d₂) => p.1.val) hEq
    exact Subtype.ext (mul_right_cancel₀ hF₂_ne h1)
  have hrange_eq_ker : LinearMap.range α = LinearMap.ker β := by
    apply le_antisymm
    · rintro _ ⟨c, rfl⟩
      rw [LinearMap.mem_ker]
      apply Subtype.ext
      change c.val * F₂ * F₁ + -(c.val * F₁) * F₂ = 0
      ring
    · rintro ⟨a, b⟩ hab
      rw [LinearMap.mem_ker] at hab
      have h0 : a.val * F₁ + b.val * F₂ = 0 := congrArg Subtype.val hab
      have hF₂_dvd_aF₁ : F₂ ∣ a.val * F₁ := ⟨-b.val, by linear_combination h0⟩
      have hF₂_dvd_a : F₂ ∣ a.val := hrel.symm.dvd_of_dvd_mul_right hF₂_dvd_aF₁
      obtain ⟨c, hc⟩ := hF₂_dvd_a
      have hc_hom : c.IsHomogeneous (N - d₁ - d₂) := by
        by_cases hc0 : c = 0
        · rw [hc0]; exact isHomogeneous_zero _ _ _
        · have ha_ne : a.val ≠ 0 := by rw [hc]; exact mul_ne_zero hF₂_ne hc0
          obtain ⟨k, hck⟩ := isHomogeneous_of_dvd ((mem_homogeneousSubmodule _ _).mp a.property)
            ha_ne ⟨F₂, by rw [hc, mul_comm]⟩
          have hk_eq : d₂ + k = N - d₁ := by
            have hprod := hF₂.mul hck
            rw [← hc] at hprod
            obtain ⟨m, hm⟩ := MvPolynomial.support_nonempty.mpr ha_ne
            have h1 := ((mem_homogeneousSubmodule _ _).mp a.property)
              (MvPolynomial.mem_support_iff.mp hm)
            have h2 := hprod (MvPolynomial.mem_support_iff.mp hm)
            omega
          rwa [show N - d₁ - d₂ = k by omega]
      refine ⟨⟨c, (mem_homogeneousSubmodule _ _).mpr hc_hom⟩, ?_⟩
      apply Prod.ext
      · apply Subtype.ext; change c * F₂ = a.val; rw [hc, mul_comm]
      · apply Subtype.ext
        change -(c * F₁) = b.val
        apply mul_right_cancel₀ hF₂_ne
        linear_combination -h0 + F₁ * hc
  have h1 := LinearMap.finrank_range_add_finrank_ker α
  have h2 := LinearMap.finrank_range_add_finrank_ker β
  have h3 := Submodule.finrank_quotient_add_finrank (LinearMap.range β)
  have hα_ker0 : Module.finrank B (LinearMap.ker α) = 0 := by
    rw [LinearMap.ker_eq_bot.mpr hα_inj, finrank_bot]
  have hrange_ker_eq : Module.finrank B (LinearMap.range α) = Module.finrank B (LinearMap.ker β) :=
    by rw [hrange_eq_ker]
  have hprod_dim : Module.finrank B (V (N - d₁) × V (N - d₂)) =
      (N - d₁ + 2).choose 2 + (N - d₂ + 2).choose 2 := by
    rw [Module.finrank_prod,
      (finrank_homogeneousSubmodule_fin3 (B := B) (N - d₁)).2,
      (finrank_homogeneousSubmodule_fin3 (B := B) (N - d₂)).2]
  rw [(finrank_homogeneousSubmodule_fin3 (B := B) (N - d₁ - d₂)).2, hα_ker0, add_zero] at h1
  rw [hprod_dim] at h2
  rw [(finrank_homogeneousSubmodule_fin3 (B := B) N).2] at h3
  have hid := choose_bezout_identity N d₁ d₂ hN
  omega

/-- If every `r + 1` elements of a `B`-vector space `M` are linearly dependent, then `M` is
finite-dimensional of `finrank B M ≤ r`. -/
private theorem finite_and_finrank_le_of_not_linearIndependent {M : Type*} [AddCommGroup M]
    [Module B M] (r : ℕ) (h : ∀ v : Fin (r + 1) → M, ¬ LinearIndependent B v) :
    Module.Finite B M ∧ Module.finrank B M ≤ r := by
  classical
  let bas := Module.Basis.ofVectorSpace B M
  have hfin_idx : Finite (Module.Basis.ofVectorSpaceIndex B M) := by
    by_contra hinf
    have : Infinite (Module.Basis.ofVectorSpaceIndex B M) := not_finite_iff_infinite.mp hinf
    let f : Fin (r + 1) → Module.Basis.ofVectorSpaceIndex B M :=
      fun i => Infinite.natEmbedding _ i.val
    have hf : Function.Injective f := fun i j hij =>
      Fin.ext ((Infinite.natEmbedding _).injective hij)
    exact h (fun i => bas (f i)) (bas.linearIndependent.comp f hf)
  let : Fintype (Module.Basis.ofVectorSpaceIndex B M) := Fintype.ofFinite _
  have : Module.Finite B M := Module.Finite.of_basis bas
  refine ⟨inferInstance, ?_⟩
  rw [Module.finrank_eq_card_basis bas]
  by_contra hgt
  have hle : r + 1 ≤ Fintype.card (Module.Basis.ofVectorSpaceIndex B M) := by omega
  let e := Fintype.equivFin (Module.Basis.ofVectorSpaceIndex B M)
  let f : Fin (r + 1) → Module.Basis.ofVectorSpaceIndex B M :=
    fun i => e.symm ⟨i.val, lt_of_lt_of_le i.isLt hle⟩
  have hf : Function.Injective f := fun i j hij => by
    have h1 := e.symm.injective hij
    exact Fin.ext (congrArg (fun x : Fin (Fintype.card (Module.Basis.ofVectorSpaceIndex B M)) => x.val) h1)
  exact h (fun i => bas (f i)) (bas.linearIndependent.comp f hf)

/-- **Quotient Dimension Bézout Bound (`L2b`, algebraic form).**
For relatively prime polynomials `H₁, H₂ : MvPolynomial (Fin 2) B` of total degrees `≤ d₁, d₂`
over any field `B`, the quotient algebra `B[X₀, X₁] / (H₁, H₂)` is finite-dimensional over `B`
with `finrank B (MvPolynomial (Fin 2) B ⧸ Ideal.span {H₁, H₂}) ≤ d₁ * d₂`. -/
theorem affine_quotient_finrank_le (H₁ H₂ : MvPolynomial (Fin 2) B) {d₁ d₂ : ℕ}
    (hrel : IsRelPrime H₁ H₂) (hd₁ : H₁.totalDegree ≤ d₁) (hd₂ : H₂.totalDegree ≤ d₂) :
    Module.Finite B (MvPolynomial (Fin 2) B ⧸ Ideal.span ({H₁, H₂} : Set (MvPolynomial (Fin 2) B))) ∧
    Module.finrank B (MvPolynomial (Fin 2) B ⧸ Ideal.span ({H₁, H₂} : Set (MvPolynomial (Fin 2) B))) ≤
      d₁ * d₂ := by
  classical
  let I : Ideal (MvPolynomial (Fin 2) B) := Ideal.span {H₁, H₂}
  by_cases h10 : H₁ = 0
  · have h2u : IsUnit H₂ := hrel (h10 ▸ dvd_zero _) dvd_rfl
    have htop : I = ⊤ := Ideal.eq_top_of_isUnit_mem I
      (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))) h2u
    have : Subsingleton (MvPolynomial (Fin 2) B ⧸ I) := by
      rw [htop]; exact Ideal.Quotient.subsingleton_iff.mpr rfl
    have : Finite (MvPolynomial (Fin 2) B ⧸ I) := Finite.of_subsingleton
    exact ⟨Module.Finite.of_finite, by rw [Module.finrank_zero_of_subsingleton]; exact Nat.zero_le _⟩
  by_cases h20 : H₂ = 0
  · have h1u : IsUnit H₁ := hrel dvd_rfl (h20 ▸ dvd_zero _)
    have htop : I = ⊤ := Ideal.eq_top_of_isUnit_mem I
      (Ideal.subset_span (Set.mem_insert _ _)) h1u
    have : Subsingleton (MvPolynomial (Fin 2) B ⧸ I) := by
      rw [htop]; exact Ideal.Quotient.subsingleton_iff.mpr rfl
    have : Finite (MvPolynomial (Fin 2) B ⧸ I) := Finite.of_subsingleton
    exact ⟨Module.Finite.of_finite, by rw [Module.finrank_zero_of_subsingleton]; exact Nat.zero_le _⟩
  let e₁ := H₁.totalDegree
  let e₂ := H₂.totalDegree
  let F₁ := homog e₁ H₁
  let F₂ := homog e₂ H₂
  have hF₁_hom : F₁.IsHomogeneous e₁ := homog_isHomogeneous e₁ H₁ le_rfl
  have hF₂_hom : F₂.IsHomogeneous e₂ := homog_isHomogeneous e₂ H₂ le_rfl
  have hF₁_ne : F₁ ≠ 0 := by
    intro h0; have := congrArg dehom h0; rw [dehom_homog, map_zero] at this; exact h10 this
  have hF₂_ne : F₂ ≠ 0 := by
    intro h0; have := congrArg dehom h0; rw [dehom_homog, map_zero] at this; exact h20 this
  have hFrel : IsRelPrime F₁ F₂ := isRelPrime_homog H₁ H₂ h10 h20 hrel
  suffices hsuff : Module.Finite B (MvPolynomial (Fin 2) B ⧸ I) ∧
      Module.finrank B (MvPolynomial (Fin 2) B ⧸ I) ≤ e₁ * e₂ from
    ⟨hsuff.1, hsuff.2.trans (Nat.mul_le_mul hd₁ hd₂)⟩
  apply finite_and_finrank_le_of_not_linearIndependent (e₁ * e₂)
  intro v hli
  choose p hp using fun k : Fin (e₁ * e₂ + 1) => Ideal.Quotient.mk_surjective (v k)
  let N : ℕ := max (e₁ + e₂) (Finset.univ.sup fun k => (p k).totalDegree)
  have hN_ge : e₁ + e₂ ≤ N := le_max_left _ _
  have hp_deg (k : Fin (e₁ * e₂ + 1)) : (p k).totalDegree ≤ N :=
    (Finset.le_sup (f := fun k => (p k).totalDegree) (Finset.mem_univ k)).trans (le_max_right _ _)
  let V (k : ℕ) := homogeneousSubmodule (Fin 3) B k
  let β : V (N - e₁) × V (N - e₂) →ₗ[B] V N :=
    { toFun := fun ab => ⟨ab.1.val * F₁ + ab.2.val * F₂, by
        rw [mem_homogeneousSubmodule]
        have h1 : (ab.1.val * F₁).IsHomogeneous N := by
          have := ((mem_homogeneousSubmodule _ _).mp ab.1.property).mul hF₁_hom
          rwa [Nat.sub_add_cancel (by omega)] at this
        have h2 : (ab.2.val * F₂).IsHomogeneous N := by
          have := ((mem_homogeneousSubmodule _ _).mp ab.2.property).mul hF₂_hom
          rwa [Nat.sub_add_cancel (by omega)] at this
        exact h1.add h2⟩
      map_add' := fun x y => by apply Subtype.ext; dsimp; ring
      map_smul' := fun c x => by apply Subtype.ext; simp [smul_add] }
  have : Module.Finite B (V N) := (finrank_homogeneousSubmodule_fin3 (B := B) N).1
  have hqdim : Module.finrank B (V N ⧸ LinearMap.range β) = e₁ * e₂ :=
    homogeneous_quotient_finrank F₁ F₂ hF₁_hom hF₂_hom hF₁_ne hF₂_ne hFrel hN_ge
  let w : Fin (e₁ * e₂ + 1) → V N ⧸ LinearMap.range β := fun k =>
    Submodule.Quotient.mk ⟨homog N (p k), (mem_homogeneousSubmodule N _).mpr
      (homog_isHomogeneous N (p k) (hp_deg k))⟩
  have hw_not_li : ¬ LinearIndependent B w := by
    intro hwli
    have hcard := hwli.fintype_card_le_finrank
    rw [Fintype.card_fin, hqdim] at hcard
    omega
  rw [Fintype.not_linearIndependent_iff] at hw_not_li
  obtain ⟨c, hc_sum, k₀, hk₀⟩ := hw_not_li
  let elem : V N := ∑ k, c k • (⟨homog N (p k), (mem_homogeneousSubmodule N _).mpr
    (homog_isHomogeneous N (p k) (hp_deg k))⟩ : V N)
  have hmk_elem : (Submodule.Quotient.mk elem : V N ⧸ LinearMap.range β) = 0 := by
    have h1 : (Submodule.Quotient.mk elem : V N ⧸ LinearMap.range β) = ∑ k, c k • w k := by
      dsimp only [elem, w]
      change (LinearMap.range β).mkQ _ = _
      rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul]
      rfl
    exact h1.trans hc_sum
  have hmem_range : elem ∈ LinearMap.range β := (Submodule.Quotient.mk_eq_zero _).mp hmk_elem
  obtain ⟨⟨a, b⟩, hab⟩ := hmem_range
  have hval_eq : ∑ k, c k • homog N (p k) = a.val * F₁ + b.val * F₂ := by
    have h := congrArg Subtype.val hab
    simpa [elem, β, Submodule.coe_sum, SetLike.val_smul] using h.symm
  have hdehom_eq : ∑ k, c k • p k = dehom a.val * H₁ + dehom b.val * H₂ := by
    have h1 := congrArg dehom hval_eq
    rw [← homog_linear_comb N Finset.univ c p (fun k _ => hp_deg k), dehom_homog,
      map_add, map_mul, map_mul, dehom_homog, dehom_homog] at h1
    exact h1
  have hmem_I : ∑ k, c k • p k ∈ I := by
    rw [hdehom_eq]
    exact I.add_mem (I.mul_mem_left _ (Ideal.subset_span (Set.mem_insert _ _)))
      (I.mul_mem_left _ (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
  have hv_sum : ∑ k, c k • v k = 0 := by
    have hmk : Ideal.Quotient.mk I (∑ k, c k • p k) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hmem_I
    have hmk_eq : Ideal.Quotient.mk I (∑ k, c k • p k) = ∑ k, c k • v k := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← hp k]
      change Ideal.Quotient.mkₐ B I (c k • p k) = c k • Ideal.Quotient.mkₐ B I (p k)
      rw [map_smul]
    exact hmk_eq.symm.trans hmk
  exact hk₀ (Fintype.linearIndependent_iff.mp hli c hv_sum k₀)

end QuotientDimensionBezout

#print axioms isCoprime_map_fractionRing_of_isRelPrime
#print axioms resultant_ne_zero_of_isRelPrime
#print axioms plane_bezout_with_multiplicity
#print axioms plane_bezout_irreducible_with_multiplicity
#print axioms finrank_homogeneousSubmodule_fin3
#print axioms homogeneous_quotient_finrank
#print axioms affine_quotient_finrank_le

end ArkLib.ProximityGap.Frontier.PlaneBezoutWithMultiplicity
