/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Data.CodingTheory.GuruswamiSudan.GSLargeCharSeparable
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

/-! # Bivariate square classes and their specializations

Write the input in scalar variable Z with coefficients in K[X]. Removing square
factors yields either a polynomial in Z alone or a positive-degree coordinate
factor separable over K(Z). Both scalar and coordinate degree estimates survive
without introducing denominators.
-/

namespace ProximityGap.DiscriminantSquareClass

open Polynomial UniqueFactorizationMonoid
open scoped Polynomial

variable {K : Type*} [Field K]

/-- The characteristic of the rational function field over K in its fraction-ring model. -/
theorem char_fraction : ringChar (FractionRing K[X]) = ringChar K := by
  let _ : CharP K (ringChar K) := ringChar.charP K
  let _ : CharP K[X] (ringChar K) :=
    charP_of_injective_algebraMap (C_injective : Function.Injective (C : K →+* K[X])) _
  exact ringChar.eq_iff.mpr (charP_of_injective_algebraMap
    (IsFractionRing.injective K[X] (FractionRing K[X])) (ringChar K))

/-- Remove squares from a nonzero bivariate polynomial. A purely scalar remaining
factor is placed in s. Otherwise H has positive coordinate degree and separable
image over K(Z). Each output has scalar degree at most the input's scalar degree. -/
theorem normalize (P : K[X][X]) (hP : P ≠ 0)
    (hc : (Bivariate.swap P).natDegree < ringChar K ∨ ringChar K = 0) :
    ∃ (s : K[X]) (V H : K[X][X]), s ≠ 0 ∧ V ≠ 0 ∧ H ≠ 0 ∧
      P = s.map C * V ^ 2 * H ∧ s.natDegree ≤ P.natDegree ∧ V.natDegree ≤ P.natDegree ∧
      H.natDegree ≤ P.natDegree ∧ (Bivariate.swap H).natDegree ≤ (Bivariate.swap P).natDegree ∧
      (H = 1 ∨ (0 < (Bivariate.swap H).natDegree ∧
        ((Bivariate.swap H).map (algebraMap K[X] (FractionRing K[X]))).Separable)) := by
  classical
  obtain ⟨v, d, h, hd⟩ := exists_sq_mul_squarefree (Bivariate.swap P)
  have hp : Bivariate.swap P ≠ 0 := (map_ne_zero_iff (Bivariate.swap (R := K))
    Bivariate.swap.injective).mpr hP
  have hv : v ≠ 0 := by
    intro hz
    apply hp
    simpa [hz] using h.symm
  have hh := congrArg (Bivariate.swap (R := K)) h
  simp only [map_mul, map_pow, Bivariate.swap_swap_apply] at hh
  have hdu : (Bivariate.swap d).natDegree ≤ P.natDegree := natDegree_le_of_dvd
    (hh ▸ dvd_mul_left _ _) hP
  have hvu : (Bivariate.swap v).natDegree ≤ P.natDegree := natDegree_le_of_dvd
    ((dvd_pow_self _ (by decide : 2 ≠ 0)).trans (hh ▸ dvd_mul_right _ _)) hP
  have hdx : d.natDegree ≤ (Bivariate.swap P).natDegree :=
    natDegree_le_of_dvd (h ▸ dvd_mul_left _ _) hp
  have hsv : Bivariate.swap v ≠ 0 := (map_ne_zero_iff _ Bivariate.swap.injective).mpr hv
  by_cases hz : d.natDegree = 0
  · have he := eq_C_of_natDegree_eq_zero hz
    have hdz : d.coeff 0 ≠ 0 := by
      intro hz'
      apply hd.ne_zero
      calc d = C (d.coeff 0) := he
           _ = 0 := by rw [hz', C_0]
    have hswap := congrArg (Bivariate.swap (R := K)) he
    rw [Bivariate.swap_C] at hswap
    rw [hswap, natDegree_map_eq_of_injective C_injective] at hdu
    refine ⟨d.coeff 0, Bivariate.swap v, 1, hdz, hsv, one_ne_zero, ?_, hdu, hvu, ?_, ?_, Or.inl rfl⟩
    · rw [← hh, hswap, mul_one, mul_comm]
    · simp
    · simp
  · have hsd : Bivariate.swap d ≠ 0 := (map_ne_zero_iff _ Bivariate.swap.injective).mpr hd.ne_zero
    have hc' : d.natDegree < ringChar (FractionRing K[X]) ∨ ringChar (FractionRing K[X]) = 0 := by
      rw [char_fraction]
      exact hc.imp (hdx.trans_lt ·) id
    have hsep := GuruswamiSudan.OverRatFunc.separable_map_radical_of_natDegree_lt_ringChar
      hd.ne_zero hc'
    have hdiv : d.map (algebraMap K[X] (FractionRing K[X])) ∣
        (radical d).map (algebraMap K[X] (FractionRing K[X])) :=
      map_dvd (mapRingHom (algebraMap K[X] (FractionRing K[X])))
        (hd.isRadical.dvd_radical hd.ne_zero)
    refine ⟨1, Bivariate.swap v, Bivariate.swap d, one_ne_zero, hsv, hsd, ?_, ?_, hvu, hdu, ?_, ?_⟩
    · simpa using hh.symm
    · simp
    · simpa only [Bivariate.swap_swap_apply] using hdx
    · rw [Bivariate.swap_swap_apply]
      exact Or.inr ⟨Nat.pos_of_ne_zero hz, hsep.of_dvd hdiv⟩

/-- A square fiber with nonvanishing scalar and square factors leaves a square H-fiber
over an algebraically closed base field. -/
theorem square_fiber [IsAlgClosed K] {P V H : K[X][X]} {s : K[X]} (z : K)
    (h : P = s.map C * V ^ 2 * H) (hs : s.eval z ≠ 0) (hv : V.eval (C z) ≠ 0)
    (hsq : IsSquare (P.eval (C z))) : IsSquare (H.eval (C z)) := by
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq (s.eval z) zero_lt_two
  have ha0 : a ≠ 0 := by intro h0; apply hs; simpa [h0] using ha.symm
  obtain ⟨w, hw⟩ := hsq.exists_sq
  rw [h, eval_mul, eval_mul, eval_pow, eval_map, eval₂_at_apply, ← ha, map_pow] at hw
  let u := C a * V.eval (C z)
  have he : u ^ 2 * H.eval (C z) = w ^ 2 := by simpa only [u, mul_pow] using hw
  have hdiv : u ^ 2 ∣ w ^ 2 := ⟨H.eval (C z), he.symm⟩
  obtain ⟨b, hb⟩ := (pow_dvd_pow_iff_dvd (by decide : 2 ≠ 0)).mp hdiv
  refine (isSquare_iff_exists_sq _).mpr ⟨b, ?_⟩
  have hu : u ≠ 0 := mul_ne_zero (C_ne_zero.mpr ha0) hv
  rw [hb, mul_pow u b 2] at he
  exact mul_left_cancel₀ (pow_ne_zero 2 hu) he

#print axioms normalize
#print axioms square_fiber
end ProximityGap.DiscriminantSquareClass
