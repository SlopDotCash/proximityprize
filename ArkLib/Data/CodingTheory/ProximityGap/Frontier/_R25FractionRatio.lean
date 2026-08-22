/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
import Mathlib.Tactic

/-!
#  R25FractionRatio

Module docstring for `_R25FractionRatio.lean`.
-/


namespace ArkLib.ProximityGap.Frontier.R25FractionRatio

open Polynomial

variable {F : Type*} [Field F]

noncomputable abbrev fracSwap :
    FractionRing (Polynomial (Polynomial F)) ≃+*
      FractionRing (Polynomial (Polynomial F)) :=
  IsFractionRing.ringEquivOfRingEquiv
    (Polynomial.Bivariate.swap (R := F)).toRingEquiv

theorem C_poly_ne_zero_of_ne_zero {g : F[X]} (hg : g ≠ 0) :
    (C g : Polynomial (Polynomial F)) ≠ 0 := by
  intro h
  apply hg
  apply C_injective
  simpa using h

theorem map_C_ne_zero_of_ne_zero {g : F[X]} (hg : g ≠ 0) :
    g.map (C : F →+* F[X]) ≠ 0 := by
  exact (Polynomial.map_ne_zero_iff C_injective).2 hg

theorem frac_C_poly_ne_zero_of_ne_zero {g : F[X]} (hg : g ≠ 0) :
    algebraMap (Polynomial (Polynomial F)) (FractionRing (Polynomial (Polynomial F)))
      (C g) ≠ 0 := by
  exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2
    (C_poly_ne_zero_of_ne_zero hg)

theorem frac_map_C_ne_zero_of_ne_zero {g : F[X]} (hg : g ≠ 0) :
    algebraMap (Polynomial (Polynomial F)) (FractionRing (Polynomial (Polynomial F)))
      (g.map (C : F →+* F[X])) ≠ 0 := by
  exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2
    (map_C_ne_zero_of_ne_zero hg)

theorem bivariate_swap_C_poly (g : F[X]) :
    Polynomial.Bivariate.swap (R := F) (C g : Polynomial (Polynomial F)) =
      g.map (C : F →+* F[X]) := by
  exact Polynomial.Bivariate.swap_C g

theorem bivariate_swap_map_C (g : F[X]) :
    Polynomial.Bivariate.swap (R := F) (g.map (C : F →+* F[X])) =
      (C g : Polynomial (Polynomial F)) := by
  exact Polynomial.Bivariate.swap_map_C g

theorem bivariate_swap_ratio_num_den (g : F[X]) :
    Polynomial.Bivariate.swap (R := F)
        ((C g : Polynomial (Polynomial F)) * (g.map (C : F →+* F[X]))) =
      (C g : Polynomial (Polynomial F)) * (g.map (C : F →+* F[X])) := by
  rw [map_mul, bivariate_swap_C_poly, bivariate_swap_map_C, mul_comm]

theorem fracSwap_algebraMap (P : Polynomial (Polynomial F)) :
    fracSwap (F := F)
        (algebraMap (Polynomial (Polynomial F)) (FractionRing (Polynomial (Polynomial F))) P) =
      algebraMap (Polynomial (Polynomial F)) (FractionRing (Polynomial (Polynomial F)))
        (Polynomial.Bivariate.swap (R := F) P) := by
  exact IsFractionRing.ringEquivOfRingEquiv_algebraMap
    (Polynomial.Bivariate.swap (R := F)).toRingEquiv P

theorem fracSwap_C_poly (g : F[X]) :
    fracSwap (F := F)
        (algebraMap (Polynomial (Polynomial F)) (FractionRing (Polynomial (Polynomial F)))
          (C g)) =
      algebraMap (Polynomial (Polynomial F)) (FractionRing (Polynomial (Polynomial F)))
        (g.map (C : F →+* F[X])) := by
  rw [fracSwap_algebraMap, bivariate_swap_C_poly]

theorem fracSwap_map_C (g : F[X]) :
    fracSwap (F := F)
        (algebraMap (Polynomial (Polynomial F)) (FractionRing (Polynomial (Polynomial F)))
          (g.map (C : F →+* F[X]))) =
      algebraMap (Polynomial (Polynomial F)) (FractionRing (Polynomial (Polynomial F)))
        (C g) := by
  rw [fracSwap_algebraMap, bivariate_swap_map_C]

theorem fracSwap_ratio (g : F[X]) :
    fracSwap (F := F)
        (algebraMap (Polynomial (Polynomial F)) (FractionRing (Polynomial (Polynomial F)))
            (g.map (C : F →+* F[X])) /
          algebraMap (Polynomial (Polynomial F)) (FractionRing (Polynomial (Polynomial F)))
            (C g)) =
      algebraMap (Polynomial (Polynomial F)) (FractionRing (Polynomial (Polynomial F)))
          (C g) /
        algebraMap (Polynomial (Polynomial F)) (FractionRing (Polynomial (Polynomial F)))
          (g.map (C : F →+* F[X])) := by
  rw [map_div₀, fracSwap_map_C, fracSwap_C_poly]

theorem isSquare_ringEquiv_iff {K L : Type*} [CommSemiring K] [CommSemiring L]
    (e : K ≃+* L) {z : K} :
    IsSquare (e z) ↔ IsSquare z := by
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨e.symm w, ?_⟩
    apply e.injective
    simpa [map_mul, hw]
  · rintro ⟨w, hw⟩
    refine ⟨e w, ?_⟩
    rw [hw, map_mul]

theorem isSquare_fracSwap_iff
    {z : FractionRing (Polynomial (Polynomial F))} :
    IsSquare (fracSwap (F := F) z) ↔ IsSquare z :=
  isSquare_ringEquiv_iff (fracSwap (F := F))

theorem ratio_isSquare_iff_inverse_ratio_isSquare (g : F[X]) :
    IsSquare
        (algebraMap (Polynomial (Polynomial F)) (FractionRing (Polynomial (Polynomial F)))
            (g.map (C : F →+* F[X])) /
          algebraMap (Polynomial (Polynomial F)) (FractionRing (Polynomial (Polynomial F)))
            (C g)) ↔
      IsSquare
        (algebraMap (Polynomial (Polynomial F)) (FractionRing (Polynomial (Polynomial F)))
            (C g) /
          algebraMap (Polynomial (Polynomial F)) (FractionRing (Polynomial (Polynomial F)))
            (g.map (C : F →+* F[X]))) := by
  rw [← isSquare_fracSwap_iff]
  rw [fracSwap_ratio]

theorem fracSwap_neg_ratio (g : F[X]) :
    fracSwap (F := F)
        (-(algebraMap (Polynomial (Polynomial F)) (FractionRing (Polynomial (Polynomial F)))
            (g.map (C : F →+* F[X])) /
          algebraMap (Polynomial (Polynomial F)) (FractionRing (Polynomial (Polynomial F)))
            (C g))) =
      -(algebraMap (Polynomial (Polynomial F)) (FractionRing (Polynomial (Polynomial F)))
          (C g) /
        algebraMap (Polynomial (Polynomial F)) (FractionRing (Polynomial (Polynomial F)))
          (g.map (C : F →+* F[X]))) := by
  rw [map_neg, fracSwap_ratio]

theorem neg_ratio_isSquare_iff_neg_inverse_ratio_isSquare (g : F[X]) :
    IsSquare
        (-(algebraMap (Polynomial (Polynomial F)) (FractionRing (Polynomial (Polynomial F)))
            (g.map (C : F →+* F[X])) /
          algebraMap (Polynomial (Polynomial F)) (FractionRing (Polynomial (Polynomial F)))
            (C g))) ↔
      IsSquare
        (-(algebraMap (Polynomial (Polynomial F)) (FractionRing (Polynomial (Polynomial F)))
            (C g) /
          algebraMap (Polynomial (Polynomial F)) (FractionRing (Polynomial (Polynomial F)))
            (g.map (C : F →+* F[X])))) := by
  rw [← isSquare_fracSwap_iff]
  rw [fracSwap_neg_ratio]

theorem isSquare_mul_of_isSquare_div {K : Type*} [Field K] {H G : K}
    (hG : G ≠ 0) (hsq : IsSquare (H / G)) :
    IsSquare (H * G) := by
  rcases hsq with ⟨w, hw⟩
  refine ⟨w * G, ?_⟩
  calc
    H * G = (H / G) * G ^ 2 := by
      field_simp [hG]
    _ = (w * G) * (w * G) := by
      rw [hw]
      ring

theorem isSquare_neg_mul_of_isSquare_neg_div {K : Type*} [Field K] {H G : K}
    (hG : G ≠ 0) (hsq : IsSquare (-(H / G))) :
    IsSquare (-(H * G)) := by
  rcases hsq with ⟨w, hw⟩
  refine ⟨w * G, ?_⟩
  calc
    -(H * G) = (-(H / G)) * G ^ 2 := by
      field_simp [hG]
    _ = (w * G) * (w * G) := by
      rw [hw]
      ring

theorem ratio_square_forces_product_square (g : F[X]) (hg : g ≠ 0)
    (hsq :
      IsSquare
        (algebraMap (Polynomial (Polynomial F)) (FractionRing (Polynomial (Polynomial F)))
            (g.map (C : F →+* F[X])) /
          algebraMap (Polynomial (Polynomial F)) (FractionRing (Polynomial (Polynomial F)))
            (C g))) :
    IsSquare
      (algebraMap (Polynomial (Polynomial F)) (FractionRing (Polynomial (Polynomial F)))
        ((g.map (C : F →+* F[X])) * (C g))) := by
  have hG := frac_C_poly_ne_zero_of_ne_zero hg
  have hsq' := isSquare_mul_of_isSquare_div hG hsq
  simpa [map_mul, mul_comm] using hsq'

theorem neg_ratio_square_forces_neg_product_square (g : F[X]) (hg : g ≠ 0)
    (hsq :
      IsSquare
        (-(algebraMap (Polynomial (Polynomial F)) (FractionRing (Polynomial (Polynomial F)))
            (g.map (C : F →+* F[X])) /
          algebraMap (Polynomial (Polynomial F)) (FractionRing (Polynomial (Polynomial F)))
            (C g)))) :
    IsSquare
      (-(algebraMap (Polynomial (Polynomial F)) (FractionRing (Polynomial (Polynomial F)))
        ((g.map (C : F →+* F[X])) * (C g)))) := by
  have hG := frac_C_poly_ne_zero_of_ne_zero hg
  have hsq' := isSquare_neg_mul_of_isSquare_neg_div hG hsq
  simpa [map_mul, mul_comm] using hsq'

theorem fraction_square_relation
    {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    {a : R} (hsq : IsSquare (algebraMap R K a)) :
  ∃ x y : R, y ≠ 0 ∧ a * y ^ 2 = x ^ 2 := by
  rcases hsq with ⟨w, hw⟩
  rcases IsFractionRing.div_surjective R w with ⟨x, y, hy, hwxy⟩
  refine ⟨x, y, mem_nonZeroDivisors_iff_ne_zero.mp hy, ?_⟩
  apply IsFractionRing.injective R K
  have hyK : algebraMap R K y ≠ 0 := by
    exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy
  calc
    algebraMap R K (a * y ^ 2)
        = algebraMap R K a * (algebraMap R K y) ^ 2 := by simp [map_mul, map_pow]
    _ = ((algebraMap R K x / algebraMap R K y) *
          (algebraMap R K x / algebraMap R K y)) * (algebraMap R K y) ^ 2 := by
      rw [hw, hwxy]
    _ = algebraMap R K (x ^ 2) := by
      rw [show (algebraMap R K y) ^ 2 =
          algebraMap R K y * algebraMap R K y by ring]
      rw [show ((algebraMap R K x / algebraMap R K y) *
              (algebraMap R K x / algebraMap R K y)) *
              (algebraMap R K y * algebraMap R K y) =
            ((algebraMap R K x / algebraMap R K y) * algebraMap R K y) *
              ((algebraMap R K x / algebraMap R K y) * algebraMap R K y) by ring]
      rw [div_mul_cancel₀ (algebraMap R K x) hyK]
      simp [map_pow, pow_two]

theorem fraction_square_relation_poly
    {a : Polynomial (Polynomial F)}
    (hsq : IsSquare
      (algebraMap (Polynomial (Polynomial F)) (FractionRing (Polynomial (Polynomial F))) a)) :
    ∃ x y : Polynomial (Polynomial F), y ≠ 0 ∧ a * y ^ 2 = x ^ 2 :=
  fraction_square_relation hsq

theorem even_normalizedFactors_count_of_square_relation
    {R : Type*} [CommMonoidWithZero R] [NoZeroDivisors R] [NormalizationMonoid R]
    [UniqueFactorizationMonoid R] [DecidableEq R]
    {a x y p : R} (ha : a ≠ 0) (hy : y ≠ 0) (h : a * y ^ 2 = x ^ 2) :
    Even ((UniqueFactorizationMonoid.normalizedFactors a).count p) := by
  have hy2 : y ^ 2 ≠ 0 := pow_ne_zero 2 hy
  have hx : x ≠ 0 := by
    intro hx
    have hleft : a * y ^ 2 ≠ 0 := mul_ne_zero ha hy2
    apply hleft
    simpa [hx] using h
  have hnf := congrArg
    (fun s : Multiset R => s.count p)
    (congrArg UniqueFactorizationMonoid.normalizedFactors h)
  rw [UniqueFactorizationMonoid.normalizedFactors_mul ha hy2,
    UniqueFactorizationMonoid.normalizedFactors_pow,
    UniqueFactorizationMonoid.normalizedFactors_pow] at hnf
  simp only [Multiset.count_add, Multiset.count_nsmul] at hnf
  have hcount :
      (UniqueFactorizationMonoid.normalizedFactors a).count p +
        2 * (UniqueFactorizationMonoid.normalizedFactors y).count p =
      2 * (UniqueFactorizationMonoid.normalizedFactors x).count p := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hnf
  refine ⟨(UniqueFactorizationMonoid.normalizedFactors x).count p -
    (UniqueFactorizationMonoid.normalizedFactors y).count p, ?_⟩
  omega

theorem even_normalizedFactors_count_of_fraction_square
    {R K : Type*} [CommRing R] [IsDomain R] [NormalizationMonoid R]
    [UniqueFactorizationMonoid R] [DecidableEq R] [Field K] [Algebra R K]
    [IsFractionRing R K]
    {a p : R} (ha : a ≠ 0) (hsq : IsSquare (algebraMap R K a)) :
    Even ((UniqueFactorizationMonoid.normalizedFactors a).count p) := by
  rcases fraction_square_relation hsq with ⟨x, y, hy, h⟩
  exact even_normalizedFactors_count_of_square_relation ha hy h

theorem even_normalizedFactors_count_of_fraction_square_poly
    [NormalizationMonoid (Polynomial (Polynomial F))]
    [UniqueFactorizationMonoid (Polynomial (Polynomial F))]
    [DecidableEq (Polynomial (Polynomial F))]
    {a p : Polynomial (Polynomial F)} (ha : a ≠ 0)
    (hsq : IsSquare
      (algebraMap (Polynomial (Polynomial F)) (FractionRing (Polynomial (Polynomial F))) a)) :
    Even ((UniqueFactorizationMonoid.normalizedFactors a).count p) :=
  even_normalizedFactors_count_of_fraction_square ha hsq

theorem not_fraction_square_of_not_even_normalizedFactors_count
    {R K : Type*} [CommRing R] [IsDomain R] [NormalizationMonoid R]
    [UniqueFactorizationMonoid R] [DecidableEq R] [Field K] [Algebra R K]
    [IsFractionRing R K]
    {a p : R} (ha : a ≠ 0)
    (hodd : ¬ Even ((UniqueFactorizationMonoid.normalizedFactors a).count p)) :
    ¬ IsSquare (algebraMap R K a) := by
  intro hsq
  exact hodd (even_normalizedFactors_count_of_fraction_square ha hsq)

theorem not_even_normalizedFactors_count_mul_of_count_one_count_zero
    {R : Type*} [CommMonoidWithZero R] [NormalizationMonoid R]
    [UniqueFactorizationMonoid R] [DecidableEq R]
    {a b p : R} (ha : a ≠ 0) (hb : b ≠ 0)
    (hpa : (UniqueFactorizationMonoid.normalizedFactors a).count p = 1)
    (hpb : (UniqueFactorizationMonoid.normalizedFactors b).count p = 0) :
    ¬ Even ((UniqueFactorizationMonoid.normalizedFactors (a * b)).count p) := by
  rw [UniqueFactorizationMonoid.normalizedFactors_mul ha hb, Multiset.count_add, hpa, hpb]
  norm_num

theorem not_even_normalizedFactors_count_neg_of_not_even
    {R : Type*} [CommRing R] [NormalizationMonoid R]
    [UniqueFactorizationMonoid R] [DecidableEq R]
    {a p : R} (hodd : ¬ Even ((UniqueFactorizationMonoid.normalizedFactors a).count p)) :
    ¬ Even ((UniqueFactorizationMonoid.normalizedFactors (-a)).count p) := by
  rwa [(Associated.rfl : Associated a a).neg_left.normalizedFactors_eq]

theorem not_even_normalizedFactors_count_neg_mul_of_count_one_count_zero
    {R : Type*} [CommRing R] [NormalizationMonoid R]
    [UniqueFactorizationMonoid R] [DecidableEq R]
    {a b p : R} (ha : a ≠ 0) (hb : b ≠ 0)
    (hpa : (UniqueFactorizationMonoid.normalizedFactors a).count p = 1)
    (hpb : (UniqueFactorizationMonoid.normalizedFactors b).count p = 0) :
    ¬ Even ((UniqueFactorizationMonoid.normalizedFactors (-(a * b))).count p) :=
  not_even_normalizedFactors_count_neg_of_not_even
    (not_even_normalizedFactors_count_mul_of_count_one_count_zero ha hb hpa hpb)

theorem normalizedFactors_count_eq_one_of_squarefree_dvd
    {R : Type*} [CommMonoidWithZero R] [NormalizationMonoid R]
    [UniqueFactorizationMonoid R] [DecidableEq R]
    {x p : R} (hx : x ≠ 0) (hsqf : Squarefree x)
    (hp : Irreducible p) (hnorm : normalize p = p) (hdvd : p ∣ x) :
    (UniqueFactorizationMonoid.normalizedFactors x).count p = 1 := by
  have hnodup :
      Multiset.Nodup (UniqueFactorizationMonoid.normalizedFactors x) :=
    (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hx).1 hsqf
  have hmem : p ∈ UniqueFactorizationMonoid.normalizedFactors x := by
    rw [UniqueFactorizationMonoid.mem_normalizedFactors_iff' hx]
    exact ⟨hp, hnorm, hdvd⟩
  exact Multiset.count_eq_one_of_mem hnodup hmem

theorem normalizedFactors_count_eq_zero_of_not_dvd
    {R : Type*} [CommMonoidWithZero R] [NormalizationMonoid R]
    [UniqueFactorizationMonoid R] [DecidableEq R]
    {x p : R} (hx : x ≠ 0) (hndvd : ¬ p ∣ x) :
    (UniqueFactorizationMonoid.normalizedFactors x).count p = 0 := by
  apply Multiset.count_eq_zero.mpr
  intro hmem
  exact hndvd (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hmem)

theorem not_even_normalizedFactors_count_mul_of_squarefree_factor_separated
    {R : Type*} [CommMonoidWithZero R] [NormalizationMonoid R]
    [UniqueFactorizationMonoid R] [DecidableEq R]
    {a b p : R} (ha : a ≠ 0) (hb : b ≠ 0) (hsqf : Squarefree a)
    (hp : Irreducible p) (hnorm : normalize p = p)
    (hp_dvd_a : p ∣ a) (hp_not_dvd_b : ¬ p ∣ b) :
    ¬ Even ((UniqueFactorizationMonoid.normalizedFactors (a * b)).count p) := by
  exact not_even_normalizedFactors_count_mul_of_count_one_count_zero ha hb
    (normalizedFactors_count_eq_one_of_squarefree_dvd ha hsqf hp hnorm hp_dvd_a)
    (normalizedFactors_count_eq_zero_of_not_dvd hb hp_not_dvd_b)

theorem ratio_not_square_of_not_even_product_count
    [NormalizationMonoid (Polynomial (Polynomial F))]
    [UniqueFactorizationMonoid (Polynomial (Polynomial F))]
    [DecidableEq (Polynomial (Polynomial F))]
    {g : F[X]} (hg : g ≠ 0) {p : Polynomial (Polynomial F)}
    (hodd : ¬ Even
      ((UniqueFactorizationMonoid.normalizedFactors
        ((g.map (C : F →+* F[X])) * (C g))).count p)) :
    ¬ IsSquare
      (algebraMap (Polynomial (Polynomial F)) (FractionRing (Polynomial (Polynomial F)))
          (g.map (C : F →+* F[X])) /
        algebraMap (Polynomial (Polynomial F)) (FractionRing (Polynomial (Polynomial F)))
          (C g)) := by
  intro hsq
  have hprod_sq := ratio_square_forces_product_square g hg hsq
  have hprod_ne : (g.map (C : F →+* F[X])) * (C g) ≠
      (0 : Polynomial (Polynomial F)) :=
    mul_ne_zero (map_C_ne_zero_of_ne_zero hg) (C_poly_ne_zero_of_ne_zero hg)
  exact hodd (even_normalizedFactors_count_of_fraction_square hprod_ne hprod_sq)

theorem neg_ratio_not_square_of_not_even_neg_product_count
    [NormalizationMonoid (Polynomial (Polynomial F))]
    [UniqueFactorizationMonoid (Polynomial (Polynomial F))]
    [DecidableEq (Polynomial (Polynomial F))]
    {g : F[X]} (hg : g ≠ 0) {p : Polynomial (Polynomial F)}
    (hodd : ¬ Even
      ((UniqueFactorizationMonoid.normalizedFactors
        (-((g.map (C : F →+* F[X])) * (C g)))).count p)) :
    ¬ IsSquare
      (-(algebraMap (Polynomial (Polynomial F)) (FractionRing (Polynomial (Polynomial F)))
          (g.map (C : F →+* F[X])) /
        algebraMap (Polynomial (Polynomial F)) (FractionRing (Polynomial (Polynomial F)))
          (C g))) := by
  intro hsq
  have hprod_sq := neg_ratio_square_forces_neg_product_square g hg hsq
  have hprod_ne : -((g.map (C : F →+* F[X])) * (C g)) ≠
      (0 : Polynomial (Polynomial F)) := by
    rw [neg_ne_zero]
    exact mul_ne_zero (map_C_ne_zero_of_ne_zero hg) (C_poly_ne_zero_of_ne_zero hg)
  have hprod_sq' : IsSquare
      (algebraMap (Polynomial (Polynomial F)) (FractionRing (Polynomial (Polynomial F)))
        (-((g.map (C : F →+* F[X])) * (C g)))) := by
    simpa using hprod_sq
  exact hodd (even_normalizedFactors_count_of_fraction_square hprod_ne hprod_sq')

theorem ratio_not_square_of_map_count_one_C_count_zero
    [NormalizationMonoid (Polynomial (Polynomial F))]
    [UniqueFactorizationMonoid (Polynomial (Polynomial F))]
    [DecidableEq (Polynomial (Polynomial F))]
    {g : F[X]} (hg : g ≠ 0) {p : Polynomial (Polynomial F)}
    (hpmap : (UniqueFactorizationMonoid.normalizedFactors
        (g.map (C : F →+* F[X]))).count p = 1)
    (hpC : (UniqueFactorizationMonoid.normalizedFactors
        (C g : Polynomial (Polynomial F))).count p = 0) :
    ¬ IsSquare
      (algebraMap (Polynomial (Polynomial F)) (FractionRing (Polynomial (Polynomial F)))
          (g.map (C : F →+* F[X])) /
        algebraMap (Polynomial (Polynomial F)) (FractionRing (Polynomial (Polynomial F)))
          (C g)) := by
  apply ratio_not_square_of_not_even_product_count hg
  exact not_even_normalizedFactors_count_mul_of_count_one_count_zero
    (map_C_ne_zero_of_ne_zero hg) (C_poly_ne_zero_of_ne_zero hg) hpmap hpC

theorem neg_ratio_not_square_of_map_count_one_C_count_zero
    [NormalizationMonoid (Polynomial (Polynomial F))]
    [UniqueFactorizationMonoid (Polynomial (Polynomial F))]
    [DecidableEq (Polynomial (Polynomial F))]
    {g : F[X]} (hg : g ≠ 0) {p : Polynomial (Polynomial F)}
    (hpmap : (UniqueFactorizationMonoid.normalizedFactors
        (g.map (C : F →+* F[X]))).count p = 1)
    (hpC : (UniqueFactorizationMonoid.normalizedFactors
        (C g : Polynomial (Polynomial F))).count p = 0) :
    ¬ IsSquare
      (-(algebraMap (Polynomial (Polynomial F)) (FractionRing (Polynomial (Polynomial F)))
          (g.map (C : F →+* F[X])) /
        algebraMap (Polynomial (Polynomial F)) (FractionRing (Polynomial (Polynomial F)))
          (C g))) := by
  apply neg_ratio_not_square_of_not_even_neg_product_count hg
  exact not_even_normalizedFactors_count_neg_mul_of_count_one_count_zero
    (map_C_ne_zero_of_ne_zero hg) (C_poly_ne_zero_of_ne_zero hg) hpmap hpC

theorem ratio_not_square_of_squarefree_map_factor_separated
    [NormalizationMonoid (Polynomial (Polynomial F))]
    [UniqueFactorizationMonoid (Polynomial (Polynomial F))]
    [DecidableEq (Polynomial (Polynomial F))]
    {g : F[X]} (hg : g ≠ 0) {p : Polynomial (Polynomial F)}
    (hsqf : Squarefree (g.map (C : F →+* F[X])))
    (hp : Irreducible p) (hnorm : normalize p = p)
    (hp_dvd_map : p ∣ g.map (C : F →+* F[X]))
    (hp_not_dvd_C : ¬ p ∣ (C g : Polynomial (Polynomial F))) :
    ¬ IsSquare
      (algebraMap (Polynomial (Polynomial F)) (FractionRing (Polynomial (Polynomial F)))
          (g.map (C : F →+* F[X])) /
        algebraMap (Polynomial (Polynomial F)) (FractionRing (Polynomial (Polynomial F)))
          (C g)) := by
  apply ratio_not_square_of_not_even_product_count hg
  exact not_even_normalizedFactors_count_mul_of_squarefree_factor_separated
    (map_C_ne_zero_of_ne_zero hg) (C_poly_ne_zero_of_ne_zero hg)
    hsqf hp hnorm hp_dvd_map hp_not_dvd_C

theorem neg_ratio_not_square_of_squarefree_map_factor_separated
    [NormalizationMonoid (Polynomial (Polynomial F))]
    [UniqueFactorizationMonoid (Polynomial (Polynomial F))]
    [DecidableEq (Polynomial (Polynomial F))]
    {g : F[X]} (hg : g ≠ 0) {p : Polynomial (Polynomial F)}
    (hsqf : Squarefree (g.map (C : F →+* F[X])))
    (hp : Irreducible p) (hnorm : normalize p = p)
    (hp_dvd_map : p ∣ g.map (C : F →+* F[X]))
    (hp_not_dvd_C : ¬ p ∣ (C g : Polynomial (Polynomial F))) :
    ¬ IsSquare
      (-(algebraMap (Polynomial (Polynomial F)) (FractionRing (Polynomial (Polynomial F)))
          (g.map (C : F →+* F[X])) /
        algebraMap (Polynomial (Polynomial F)) (FractionRing (Polynomial (Polynomial F)))
          (C g))) := by
  apply neg_ratio_not_square_of_not_even_neg_product_count hg
  exact not_even_normalizedFactors_count_neg_of_not_even
    (not_even_normalizedFactors_count_mul_of_squarefree_factor_separated
      (map_C_ne_zero_of_ne_zero hg) (C_poly_ne_zero_of_ne_zero hg)
      hsqf hp hnorm hp_dvd_map hp_not_dvd_C)

theorem map_C_factor_not_dvd_C_of_natDegree_pos
    {q g : F[X]} (hg : g ≠ 0) (hqdeg : 0 < q.natDegree) :
    ¬ (q.map (C : F →+* F[X])) ∣ (C g : Polynomial (Polynomial F)) := by
  intro hdvd
  have hle := Polynomial.natDegree_le_of_dvd hdvd (C_poly_ne_zero_of_ne_zero hg)
  have hmap :
      (q.map (C : F →+* F[X])).natDegree = q.natDegree :=
    Polynomial.natDegree_map (C : F →+* F[X])
  have hle0 : q.natDegree ≤ 0 := by
    simpa [hmap, Polynomial.natDegree_C] using hle
  exact (Nat.lt_irrefl 0) (hqdeg.trans_le hle0)

theorem not_dvd_C_of_natDegree_pos
    {p : Polynomial (Polynomial F)} {g : F[X]} (hg : g ≠ 0) (hpdeg : 0 < p.natDegree) :
    ¬ p ∣ (C g : Polynomial (Polynomial F)) := by
  intro hdvd
  have hle := Polynomial.natDegree_le_of_dvd hdvd (C_poly_ne_zero_of_ne_zero hg)
  have hle0 : p.natDegree ≤ 0 := by
    simpa [Polynomial.natDegree_C] using hle
  exact (Nat.lt_irrefl 0) (hpdeg.trans_le hle0)

theorem map_C_factor_dvd_map_C_of_dvd {q g : F[X]} (hqdvd : q ∣ g) :
    q.map (C : F →+* F[X]) ∣ g.map (C : F →+* F[X]) :=
  Polynomial.map_dvd (C : F →+* F[X]) hqdvd

theorem ratio_not_square_of_squarefree_mapped_factor
    [NormalizationMonoid (Polynomial (Polynomial F))]
    [UniqueFactorizationMonoid (Polynomial (Polynomial F))]
    [DecidableEq (Polynomial (Polynomial F))]
    {g q : F[X]} (hg : g ≠ 0) (hqdeg : 0 < q.natDegree)
    (hsqf : Squarefree (g.map (C : F →+* F[X])))
    (hqirr : Irreducible (q.map (C : F →+* F[X])))
    (hqnorm : normalize (q.map (C : F →+* F[X])) = q.map (C : F →+* F[X]))
    (hqdvd : q ∣ g) :
    ¬ IsSquare
      (algebraMap (Polynomial (Polynomial F)) (FractionRing (Polynomial (Polynomial F)))
          (g.map (C : F →+* F[X])) /
        algebraMap (Polynomial (Polynomial F)) (FractionRing (Polynomial (Polynomial F)))
          (C g)) := by
  exact ratio_not_square_of_squarefree_map_factor_separated hg hsqf hqirr hqnorm
    (map_C_factor_dvd_map_C_of_dvd hqdvd)
    (map_C_factor_not_dvd_C_of_natDegree_pos hg hqdeg)

theorem neg_ratio_not_square_of_squarefree_mapped_factor
    [NormalizationMonoid (Polynomial (Polynomial F))]
    [UniqueFactorizationMonoid (Polynomial (Polynomial F))]
    [DecidableEq (Polynomial (Polynomial F))]
    {g q : F[X]} (hg : g ≠ 0) (hqdeg : 0 < q.natDegree)
    (hsqf : Squarefree (g.map (C : F →+* F[X])))
    (hqirr : Irreducible (q.map (C : F →+* F[X])))
    (hqnorm : normalize (q.map (C : F →+* F[X])) = q.map (C : F →+* F[X]))
    (hqdvd : q ∣ g) :
    ¬ IsSquare
      (-(algebraMap (Polynomial (Polynomial F)) (FractionRing (Polynomial (Polynomial F)))
          (g.map (C : F →+* F[X])) /
        algebraMap (Polynomial (Polynomial F)) (FractionRing (Polynomial (Polynomial F)))
          (C g))) := by
  exact neg_ratio_not_square_of_squarefree_map_factor_separated hg hsqf hqirr hqnorm
    (map_C_factor_dvd_map_C_of_dvd hqdvd)
    (map_C_factor_not_dvd_C_of_natDegree_pos hg hqdeg)

theorem ratio_not_square_of_positive_degree_normalized_factor
    [NormalizationMonoid (Polynomial (Polynomial F))]
    [UniqueFactorizationMonoid (Polynomial (Polynomial F))]
    [DecidableEq (Polynomial (Polynomial F))]
    {g : F[X]} (hg : g ≠ 0) {p : Polynomial (Polynomial F)}
    (hsqf : Squarefree (g.map (C : F →+* F[X])))
    (hpmem : p ∈ UniqueFactorizationMonoid.normalizedFactors
      (g.map (C : F →+* F[X])))
    (hpdeg : 0 < p.natDegree) :
    ¬ IsSquare
      (algebraMap (Polynomial (Polynomial F)) (FractionRing (Polynomial (Polynomial F)))
          (g.map (C : F →+* F[X])) /
        algebraMap (Polynomial (Polynomial F)) (FractionRing (Polynomial (Polynomial F)))
          (C g)) := by
  have hp := UniqueFactorizationMonoid.irreducible_of_normalized_factor p hpmem
  have hnorm := UniqueFactorizationMonoid.normalize_normalized_factor p hpmem
  have hpdvd := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hpmem
  exact ratio_not_square_of_squarefree_map_factor_separated hg hsqf hp hnorm hpdvd
    (not_dvd_C_of_natDegree_pos hg hpdeg)

theorem neg_ratio_not_square_of_positive_degree_normalized_factor
    [NormalizationMonoid (Polynomial (Polynomial F))]
    [UniqueFactorizationMonoid (Polynomial (Polynomial F))]
    [DecidableEq (Polynomial (Polynomial F))]
    {g : F[X]} (hg : g ≠ 0) {p : Polynomial (Polynomial F)}
    (hsqf : Squarefree (g.map (C : F →+* F[X])))
    (hpmem : p ∈ UniqueFactorizationMonoid.normalizedFactors
      (g.map (C : F →+* F[X])))
    (hpdeg : 0 < p.natDegree) :
    ¬ IsSquare
      (-(algebraMap (Polynomial (Polynomial F)) (FractionRing (Polynomial (Polynomial F)))
          (g.map (C : F →+* F[X])) /
        algebraMap (Polynomial (Polynomial F)) (FractionRing (Polynomial (Polynomial F)))
          (C g))) := by
  have hp := UniqueFactorizationMonoid.irreducible_of_normalized_factor p hpmem
  have hnorm := UniqueFactorizationMonoid.normalize_normalized_factor p hpmem
  have hpdvd := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hpmem
  exact neg_ratio_not_square_of_squarefree_map_factor_separated hg hsqf hp hnorm hpdvd
    (not_dvd_C_of_natDegree_pos hg hpdeg)

private theorem multiset_poly_prod_natDegree_eq_zero_of_forall
    {s : Multiset (Polynomial (Polynomial F))}
    (hdeg : ∀ p ∈ s, p.natDegree = 0) : s.prod.natDegree = 0 := by
  induction s using Multiset.induction_on with
  | empty =>
      simp
  | cons a s ih =>
      rw [Multiset.prod_cons]
      by_cases ha : a = 0
      · simp [ha]
      by_cases hs : s.prod = 0
      · simp [hs]
      have ha_deg : a.natDegree = 0 := hdeg a (by simp)
      have hs_deg : s.prod.natDegree = 0 := ih (by
        intro p hp
        exact hdeg p (by simp [hp]))
      rw [Polynomial.natDegree_mul ha hs, ha_deg, hs_deg, zero_add]

theorem exists_positive_degree_normalizedFactor_of_natDegree_pos
    [NormalizationMonoid (Polynomial (Polynomial F))]
    [UniqueFactorizationMonoid (Polynomial (Polynomial F))]
    {g : F[X]} (hgdeg : 0 < g.natDegree) :
    ∃ p, p ∈ UniqueFactorizationMonoid.normalizedFactors
        (g.map (C : F →+* F[X])) ∧ 0 < p.natDegree := by
  let P : Polynomial (Polynomial F) := g.map (C : F →+* F[X])
  have hPdeg : 0 < P.natDegree := by
    simpa [P, Polynomial.natDegree_map (C : F →+* F[X])] using hgdeg
  have hP0 : P ≠ 0 := Polynomial.ne_zero_of_natDegree_gt hPdeg
  by_contra hnone
  push_neg at hnone
  have hall_deg :
      ∀ q ∈ UniqueFactorizationMonoid.normalizedFactors P, q.natDegree = 0 := by
    intro q hqmem
    exact Nat.eq_zero_of_le_zero (hnone q hqmem)
  have hprod_deg0 :
      (UniqueFactorizationMonoid.normalizedFactors P).prod.natDegree = 0 :=
    multiset_poly_prod_natDegree_eq_zero_of_forall hall_deg
  have hassoc := UniqueFactorizationMonoid.prod_normalizedFactors hP0
  have hprod0 : (UniqueFactorizationMonoid.normalizedFactors P).prod ≠ 0 :=
    hassoc.ne_zero_iff.mpr hP0
  have hdegree_eq := Polynomial.degree_eq_degree_of_associated hassoc
  have hprod_degree :
      (UniqueFactorizationMonoid.normalizedFactors P).prod.degree = 0 := by
    rw [Polynomial.degree_eq_natDegree hprod0, hprod_deg0]
    simp
  have hP_degree : P.degree = (P.natDegree : WithBot ℕ) :=
    Polynomial.degree_eq_natDegree hP0
  rw [hprod_degree, hP_degree] at hdegree_eq
  have hlt : (0 : WithBot ℕ) < (P.natDegree : WithBot ℕ) :=
    WithBot.coe_lt_coe.2 hPdeg
  exact (ne_of_gt hlt) hdegree_eq.symm

theorem ratio_not_square_of_squarefree_map_natDegree_pos
    [NormalizationMonoid (Polynomial (Polynomial F))]
    [UniqueFactorizationMonoid (Polynomial (Polynomial F))]
    [DecidableEq (Polynomial (Polynomial F))]
    {g : F[X]} (hg : g ≠ 0) (hgdeg : 0 < g.natDegree)
    (hsqf : Squarefree (g.map (C : F →+* F[X]))) :
    ¬ IsSquare
      (algebraMap (Polynomial (Polynomial F)) (FractionRing (Polynomial (Polynomial F)))
          (g.map (C : F →+* F[X])) /
        algebraMap (Polynomial (Polynomial F)) (FractionRing (Polynomial (Polynomial F)))
          (C g)) := by
  rcases exists_positive_degree_normalizedFactor_of_natDegree_pos (F := F) hgdeg with
    ⟨p, hpmem, hpdeg⟩
  exact ratio_not_square_of_positive_degree_normalized_factor hg hsqf hpmem hpdeg

theorem neg_ratio_not_square_of_squarefree_map_natDegree_pos
    [NormalizationMonoid (Polynomial (Polynomial F))]
    [UniqueFactorizationMonoid (Polynomial (Polynomial F))]
    [DecidableEq (Polynomial (Polynomial F))]
    {g : F[X]} (hg : g ≠ 0) (hgdeg : 0 < g.natDegree)
    (hsqf : Squarefree (g.map (C : F →+* F[X]))) :
    ¬ IsSquare
      (-(algebraMap (Polynomial (Polynomial F)) (FractionRing (Polynomial (Polynomial F)))
          (g.map (C : F →+* F[X])) /
        algebraMap (Polynomial (Polynomial F)) (FractionRing (Polynomial (Polynomial F)))
          (C g))) := by
  rcases exists_positive_degree_normalizedFactor_of_natDegree_pos (F := F) hgdeg with
    ⟨p, hpmem, hpdeg⟩
  exact neg_ratio_not_square_of_positive_degree_normalized_factor hg hsqf hpmem hpdeg

theorem squarefree_map_C_of_squarefree [PerfectField F] {g : F[X]} (hg : Squarefree g) :
    Squarefree (g.map (C : F →+* F[X])) := by
  have hsep : g.Separable := (PerfectField.separable_iff_squarefree).2 hg
  have hsep_map : (g.map (C : F →+* F[X])).Separable :=
    (Polynomial.separable_map (C : F →+* F[X])).2 hsep
  exact hsep_map.squarefree

theorem ratio_not_square_of_squarefree_natDegree_pos
    [PerfectField F]
    [NormalizationMonoid (Polynomial (Polynomial F))]
    [UniqueFactorizationMonoid (Polynomial (Polynomial F))]
    [DecidableEq (Polynomial (Polynomial F))]
    {g : F[X]} (hg0 : g ≠ 0) (hgsqf : Squarefree g) (hgdeg : 0 < g.natDegree) :
    ¬ IsSquare
      (algebraMap (Polynomial (Polynomial F)) (FractionRing (Polynomial (Polynomial F)))
          (g.map (C : F →+* F[X])) /
        algebraMap (Polynomial (Polynomial F)) (FractionRing (Polynomial (Polynomial F)))
          (C g)) :=
  ratio_not_square_of_squarefree_map_natDegree_pos hg0 hgdeg
    (squarefree_map_C_of_squarefree hgsqf)

theorem neg_ratio_not_square_of_squarefree_natDegree_pos
    [PerfectField F]
    [NormalizationMonoid (Polynomial (Polynomial F))]
    [UniqueFactorizationMonoid (Polynomial (Polynomial F))]
    [DecidableEq (Polynomial (Polynomial F))]
    {g : F[X]} (hg0 : g ≠ 0) (hgsqf : Squarefree g) (hgdeg : 0 < g.natDegree) :
    ¬ IsSquare
      (-(algebraMap (Polynomial (Polynomial F)) (FractionRing (Polynomial (Polynomial F)))
          (g.map (C : F →+* F[X])) /
        algebraMap (Polynomial (Polynomial F)) (FractionRing (Polynomial (Polynomial F)))
          (C g))) :=
  neg_ratio_not_square_of_squarefree_map_natDegree_pos hg0 hgdeg
    (squarefree_map_C_of_squarefree hgsqf)

end ArkLib.ProximityGap.Frontier.R25FractionRatio

/-! ## Axiom audit -/
open ArkLib.ProximityGap.Frontier.R25FractionRatio in
#print axioms C_poly_ne_zero_of_ne_zero
open ArkLib.ProximityGap.Frontier.R25FractionRatio in
#print axioms map_C_ne_zero_of_ne_zero
open ArkLib.ProximityGap.Frontier.R25FractionRatio in
#print axioms frac_C_poly_ne_zero_of_ne_zero
open ArkLib.ProximityGap.Frontier.R25FractionRatio in
#print axioms frac_map_C_ne_zero_of_ne_zero
open ArkLib.ProximityGap.Frontier.R25FractionRatio in
#print axioms bivariate_swap_C_poly
open ArkLib.ProximityGap.Frontier.R25FractionRatio in
#print axioms bivariate_swap_map_C
open ArkLib.ProximityGap.Frontier.R25FractionRatio in
#print axioms bivariate_swap_ratio_num_den
open ArkLib.ProximityGap.Frontier.R25FractionRatio in
#print axioms fracSwap_algebraMap
open ArkLib.ProximityGap.Frontier.R25FractionRatio in
#print axioms fracSwap_C_poly
open ArkLib.ProximityGap.Frontier.R25FractionRatio in
#print axioms fracSwap_map_C
open ArkLib.ProximityGap.Frontier.R25FractionRatio in
#print axioms fracSwap_ratio
open ArkLib.ProximityGap.Frontier.R25FractionRatio in
#print axioms isSquare_ringEquiv_iff
open ArkLib.ProximityGap.Frontier.R25FractionRatio in
#print axioms isSquare_fracSwap_iff
open ArkLib.ProximityGap.Frontier.R25FractionRatio in
#print axioms ratio_isSquare_iff_inverse_ratio_isSquare
open ArkLib.ProximityGap.Frontier.R25FractionRatio in
#print axioms fracSwap_neg_ratio
open ArkLib.ProximityGap.Frontier.R25FractionRatio in
#print axioms neg_ratio_isSquare_iff_neg_inverse_ratio_isSquare
open ArkLib.ProximityGap.Frontier.R25FractionRatio in
#print axioms isSquare_mul_of_isSquare_div
open ArkLib.ProximityGap.Frontier.R25FractionRatio in
#print axioms isSquare_neg_mul_of_isSquare_neg_div
open ArkLib.ProximityGap.Frontier.R25FractionRatio in
#print axioms ratio_square_forces_product_square
open ArkLib.ProximityGap.Frontier.R25FractionRatio in
#print axioms neg_ratio_square_forces_neg_product_square
open ArkLib.ProximityGap.Frontier.R25FractionRatio in
#print axioms fraction_square_relation
open ArkLib.ProximityGap.Frontier.R25FractionRatio in
#print axioms fraction_square_relation_poly
open ArkLib.ProximityGap.Frontier.R25FractionRatio in
#print axioms even_normalizedFactors_count_of_square_relation
open ArkLib.ProximityGap.Frontier.R25FractionRatio in
#print axioms even_normalizedFactors_count_of_fraction_square
open ArkLib.ProximityGap.Frontier.R25FractionRatio in
#print axioms even_normalizedFactors_count_of_fraction_square_poly
open ArkLib.ProximityGap.Frontier.R25FractionRatio in
#print axioms not_fraction_square_of_not_even_normalizedFactors_count
open ArkLib.ProximityGap.Frontier.R25FractionRatio in
#print axioms ratio_not_square_of_not_even_product_count
open ArkLib.ProximityGap.Frontier.R25FractionRatio in
#print axioms neg_ratio_not_square_of_not_even_neg_product_count
open ArkLib.ProximityGap.Frontier.R25FractionRatio in
#print axioms not_even_normalizedFactors_count_mul_of_count_one_count_zero
open ArkLib.ProximityGap.Frontier.R25FractionRatio in
#print axioms not_even_normalizedFactors_count_neg_of_not_even
open ArkLib.ProximityGap.Frontier.R25FractionRatio in
#print axioms normalizedFactors_count_eq_one_of_squarefree_dvd
open ArkLib.ProximityGap.Frontier.R25FractionRatio in
#print axioms normalizedFactors_count_eq_zero_of_not_dvd
open ArkLib.ProximityGap.Frontier.R25FractionRatio in
#print axioms not_even_normalizedFactors_count_mul_of_squarefree_factor_separated
open ArkLib.ProximityGap.Frontier.R25FractionRatio in
#print axioms ratio_not_square_of_map_count_one_C_count_zero
open ArkLib.ProximityGap.Frontier.R25FractionRatio in
#print axioms neg_ratio_not_square_of_map_count_one_C_count_zero
open ArkLib.ProximityGap.Frontier.R25FractionRatio in
#print axioms ratio_not_square_of_squarefree_map_factor_separated
open ArkLib.ProximityGap.Frontier.R25FractionRatio in
#print axioms neg_ratio_not_square_of_squarefree_map_factor_separated
open ArkLib.ProximityGap.Frontier.R25FractionRatio in
#print axioms map_C_factor_not_dvd_C_of_natDegree_pos
open ArkLib.ProximityGap.Frontier.R25FractionRatio in
#print axioms not_dvd_C_of_natDegree_pos
open ArkLib.ProximityGap.Frontier.R25FractionRatio in
#print axioms map_C_factor_dvd_map_C_of_dvd
open ArkLib.ProximityGap.Frontier.R25FractionRatio in
#print axioms ratio_not_square_of_squarefree_mapped_factor
open ArkLib.ProximityGap.Frontier.R25FractionRatio in
#print axioms neg_ratio_not_square_of_squarefree_mapped_factor
open ArkLib.ProximityGap.Frontier.R25FractionRatio in
#print axioms ratio_not_square_of_positive_degree_normalized_factor
open ArkLib.ProximityGap.Frontier.R25FractionRatio in
#print axioms neg_ratio_not_square_of_positive_degree_normalized_factor
open ArkLib.ProximityGap.Frontier.R25FractionRatio in
#print axioms exists_positive_degree_normalizedFactor_of_natDegree_pos
open ArkLib.ProximityGap.Frontier.R25FractionRatio in
#print axioms ratio_not_square_of_squarefree_map_natDegree_pos
open ArkLib.ProximityGap.Frontier.R25FractionRatio in
#print axioms neg_ratio_not_square_of_squarefree_map_natDegree_pos
open ArkLib.ProximityGap.Frontier.R25FractionRatio in
#print axioms squarefree_map_C_of_squarefree
open ArkLib.ProximityGap.Frontier.R25FractionRatio in
#print axioms ratio_not_square_of_squarefree_natDegree_pos
open ArkLib.ProximityGap.Frontier.R25FractionRatio in
#print axioms neg_ratio_not_square_of_squarefree_natDegree_pos
