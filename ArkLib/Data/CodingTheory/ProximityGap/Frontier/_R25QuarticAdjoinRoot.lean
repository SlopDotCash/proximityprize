/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R24DBlockIndependence
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.RingTheory.AdjoinRoot

namespace ArkLib.ProximityGap.Frontier.R25QuarticAdjoinRoot

open Polynomial

variable {K : Type*} [Field K]

noncomputable abbrev quarticPoly (c : K) : K[X] :=
  X ^ 4 - C c

noncomputable abbrev QuarticRoot (c : K) :=
  AdjoinRoot (quarticPoly c)

/-- The adjoined quartic generator. -/
noncomputable abbrev τ (c : K) : QuarticRoot c :=
  AdjoinRoot.root (quarticPoly c)

/-- In `K[t]/(t⁴-c)`, the generator satisfies `t⁴=c`. -/
theorem tau_pow_four (c : K) : τ c ^ 4 = (c : QuarticRoot c) := by
  change AdjoinRoot.root (quarticPoly c) ^ 4 = (c : AdjoinRoot (quarticPoly c))
  have h := AdjoinRoot.eval₂_root (quarticPoly c)
  change (quarticPoly c).eval₂ (AdjoinRoot.of (quarticPoly c)) (AdjoinRoot.root (quarticPoly c)) = 0 at h
  simp [quarticPoly] at h
  exact sub_eq_zero.mp h

/-- Under irreducibility, the quartic quotient is a field.  This deliberately keeps
irreducibility explicit; the separate algebra work supplies usable criteria. -/
noncomputable example (c : K) [Fact (Irreducible (quarticPoly c))] : Field (QuarticRoot c) :=
  inferInstance

/-- Under irreducibility and `c ≠ 0`, the generator is nonzero. -/
theorem tau_ne_zero_of_irreducible (c : K) [Fact (Irreducible (quarticPoly c))]
    (hc : c ≠ 0) : τ c ≠ 0 := by
  intro hτ
  have hpow : τ c ^ 4 = (0 : QuarticRoot c) := by simp [hτ]
  have hcmap : (c : QuarticRoot c) = 0 := by
    simpa [tau_pow_four c] using hpow
  apply hc
  apply (AdjoinRoot.coe_injective' (f := quarticPoly c))
  simpa using hcmap

theorem quarticPoly_monic (c : K) : (quarticPoly c).Monic := by
  simpa [quarticPoly] using monic_X_pow_sub_C c (by norm_num : (4 : ℕ) ≠ 0)

theorem quarticPoly_natDegree (c : K) : (quarticPoly c).natDegree = 4 := by
  simp [quarticPoly]

private noncomputable def coeffPoly4 (x0 x1 x2 x3 : K) : K[X] :=
  C x0 + C x1 * X + C x2 * X ^ 2 + C x3 * X ^ 3

theorem eq_coeffPoly4_of_natDegree_lt_four (p : K[X]) (hp : p.natDegree < 4) :
    p = coeffPoly4 (p.coeff 0) (p.coeff 1) (p.coeff 2) (p.coeff 3) := by
  ext n
  by_cases hn : n < 4
  · interval_cases n <;> simp [coeffPoly4]
  · have hp0 : p.coeff n = 0 := coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hp (not_lt.mp hn))
    have hcp : (coeffPoly4 (p.coeff 0) (p.coeff 1) (p.coeff 2) (p.coeff 3)).natDegree < n := by
      rw [coeffPoly4]
      compute_degree!
      omega
    rw [hp0, coeff_eq_zero_of_natDegree_lt hcp]

theorem exists_coeffPoly4_mk_eq (c : K) (y : QuarticRoot c) :
    ∃ x0 x1 x2 x3 : K,
      AdjoinRoot.mk (quarticPoly c) (coeffPoly4 x0 x1 x2 x3) = y := by
  induction y using AdjoinRoot.induction_on with
  | ih p =>
      let r : K[X] := p %ₘ quarticPoly c
      refine ⟨r.coeff 0, r.coeff 1, r.coeff 2, r.coeff 3, ?_⟩
      have hq_ne_one : quarticPoly c ≠ 1 := by
        intro hq
        have hdeg : (quarticPoly c).natDegree = (1 : K[X]).natDegree := congrArg natDegree hq
        simp [quarticPoly_natDegree c] at hdeg
      have hrdeg : r.natDegree < 4 := by
        simpa [r, quarticPoly_natDegree c] using
          Polynomial.natDegree_modByMonic_lt p (quarticPoly_monic c) hq_ne_one
      have hrpoly : r = coeffPoly4 (r.coeff 0) (r.coeff 1) (r.coeff 2) (r.coeff 3) :=
        eq_coeffPoly4_of_natDegree_lt_four r hrdeg
      rw [← hrpoly]
      rw [AdjoinRoot.mk_eq_mk]
      refine ⟨-(p /ₘ quarticPoly c), ?_⟩
      have hdiv : r + quarticPoly c * (p /ₘ quarticPoly c) = p := by
        simpa [r] using Polynomial.modByMonic_add_div p (quarticPoly c)
      change r - p = quarticPoly c * -(p /ₘ quarticPoly c)
      rw [mul_neg]
      linear_combination hdiv

private noncomputable def squareTauRemainder (c x0 x1 x2 x3 : K) : K[X] :=
  C (x0 ^ 2 + c * (2 * x1 * x3 + x2 ^ 2))
    + C (2 * x0 * x1 + c * (2 * x2 * x3) - 1) * X
    + C (2 * x0 * x2 + x1 ^ 2 + c * x3 ^ 2) * X ^ 2
    + C (2 * x0 * x3 + 2 * x1 * x2) * X ^ 3

private noncomputable def squareTauQuotient (x1 x2 x3 : K) : K[X] :=
  C (2 * x1 * x3 + x2 ^ 2) + C (2 * x2 * x3) * X + C (x3 ^ 2) * X ^ 2

theorem squareTauRemainder_natDegree_lt_four (c x0 x1 x2 x3 : K)
    (_hrem : squareTauRemainder c x0 x1 x2 x3 ≠ 0) :
    (squareTauRemainder c x0 x1 x2 x3).natDegree < 4 := by
  rw [squareTauRemainder]
  compute_degree!

theorem squareTauRemainder_coeff_zero (c x0 x1 x2 x3 : K) :
    (squareTauRemainder c x0 x1 x2 x3).coeff 0 =
      x0 ^ 2 + c * (2 * x1 * x3 + x2 ^ 2) := by
  rw [squareTauRemainder]
  simp only [coeff_add, coeff_C, coeff_C_mul_X, coeff_C_mul_X_pow, if_true, if_false,
    zero_add, add_zero, zero_mul, one_mul]
  norm_num

theorem squareTauRemainder_coeff_one (c x0 x1 x2 x3 : K) :
    (squareTauRemainder c x0 x1 x2 x3).coeff 1 =
      2 * x0 * x1 + c * (2 * x2 * x3) - 1 := by
  rw [squareTauRemainder]
  simp only [coeff_add, coeff_C, coeff_C_mul_X, coeff_C_mul_X_pow, if_true, if_false,
    zero_add, add_zero, zero_mul, one_mul]
  norm_num

theorem squareTauRemainder_coeff_two (c x0 x1 x2 x3 : K) :
    (squareTauRemainder c x0 x1 x2 x3).coeff 2 =
      2 * x0 * x2 + x1 ^ 2 + c * x3 ^ 2 := by
  rw [squareTauRemainder]
  simp only [coeff_add, coeff_C, coeff_C_mul_X, coeff_C_mul_X_pow, if_true, if_false,
    zero_add, add_zero, zero_mul, one_mul]
  norm_num

theorem squareTauRemainder_coeff_three (c x0 x1 x2 x3 : K) :
    (squareTauRemainder c x0 x1 x2 x3).coeff 3 =
      2 * x0 * x3 + 2 * x1 * x2 := by
  rw [squareTauRemainder]
  simp only [coeff_add, coeff_C, coeff_C_mul_X, coeff_C_mul_X_pow, if_true, if_false,
    zero_add, add_zero, zero_mul, one_mul]
  norm_num

theorem coeffPoly4_square_sub_X_identity (c x0 x1 x2 x3 : K) :
    coeffPoly4 x0 x1 x2 x3 ^ 2 - X =
      quarticPoly c * squareTauQuotient x1 x2 x3
        + squareTauRemainder c x0 x1 x2 x3 := by
  rw [coeffPoly4, quarticPoly, squareTauQuotient, squareTauRemainder]
  simp only [map_mul, map_add, map_sub, map_pow, map_ofNat, map_one]
  ring_nf!

theorem mk_coeffPoly4_square_sub_tau_eq_remainder (c x0 x1 x2 x3 : K) :
    AdjoinRoot.mk (quarticPoly c) (coeffPoly4 x0 x1 x2 x3) ^ 2 - τ c =
      AdjoinRoot.mk (quarticPoly c) (squareTauRemainder c x0 x1 x2 x3) := by
  have h :=
    congrArg (AdjoinRoot.mk (quarticPoly c))
      (coeffPoly4_square_sub_X_identity c x0 x1 x2 x3)
  simpa [τ, AdjoinRoot.mk_X, map_add, map_mul, map_sub, map_pow, AdjoinRoot.mk_self,
    tau_pow_four c] using h

theorem coeff_equations_of_mk_coeffPoly4_square_eq_tau (c x0 x1 x2 x3 : K)
    (hsq : AdjoinRoot.mk (quarticPoly c) (coeffPoly4 x0 x1 x2 x3) ^ 2 = τ c) :
    x0 ^ 2 + c * (2 * x1 * x3 + x2 ^ 2) = 0 ∧
      2 * x0 * x1 + c * (2 * x2 * x3) - 1 = 0 ∧
      2 * x0 * x2 + x1 ^ 2 + c * x3 ^ 2 = 0 ∧
      2 * x0 * x3 + 2 * x1 * x2 = 0 := by
  have hmk : AdjoinRoot.mk (quarticPoly c) (squareTauRemainder c x0 x1 x2 x3) = 0 := by
    have hbridge := mk_coeffPoly4_square_sub_tau_eq_remainder c x0 x1 x2 x3
    simpa [hsq] using hbridge.symm
  have hrem_zero : squareTauRemainder c x0 x1 x2 x3 = 0 := by
    by_contra hrem
    exact (AdjoinRoot.mk_ne_zero_of_natDegree_lt (quarticPoly_monic c) hrem
      (by simpa [quarticPoly_natDegree c] using
        squareTauRemainder_natDegree_lt_four c x0 x1 x2 x3 hrem)) hmk
  have h0 := congrArg (fun p : K[X] => p.coeff 0) hrem_zero
  have h1 := congrArg (fun p : K[X] => p.coeff 1) hrem_zero
  have h2 := congrArg (fun p : K[X] => p.coeff 2) hrem_zero
  have h3 := congrArg (fun p : K[X] => p.coeff 3) hrem_zero
  simp [squareTauRemainder_coeff_zero, squareTauRemainder_coeff_one,
    squareTauRemainder_coeff_two, squareTauRemainder_coeff_three] at h0 h1 h2 h3
  exact ⟨h0, h1, h2, h3⟩

theorem quartic_generator_not_square_coeff [NeZero (2 : K)] (c x0 x1 x2 x3 : K)
    (hc : ¬ IsSquare c) (hnc : ¬ IsSquare (-c))
    (h0 : x0 ^ 2 + c * (2 * x1 * x3 + x2 ^ 2) = 0)
    (h1 : 2 * x0 * x1 + c * (2 * x2 * x3) = 1)
    (h2 : 2 * x0 * x2 + x1 ^ 2 + c * x3 ^ 2 = 0)
    (h3 : 2 * x0 * x3 + 2 * x1 * x2 = 0) :
    False := by
  have hc0 : c ≠ 0 := by
    intro hc0
    apply hc
    refine ⟨0, ?_⟩
    simp [hc0]
  by_cases hx3 : x3 = 0
  · subst hx3
    have hx1x2 : x1 * x2 = 0 := by
      have : (2 : K) * (x1 * x2) = 0 := by linear_combination h3
      exact (mul_eq_zero.mp this).resolve_left two_ne_zero
    rcases mul_eq_zero.mp hx1x2 with hx1 | hx2
    · subst hx1
      have hx0x2 : x0 * x2 = 0 := by
        have : (2 : K) * (x0 * x2) = 0 := by linear_combination h2
        exact (mul_eq_zero.mp this).resolve_left two_ne_zero
      rcases mul_eq_zero.mp hx0x2 with hx0 | hx2
      · subst hx0
        norm_num at h1
      · subst hx2
        norm_num at h1
    · subst hx2
      have hx0sq : x0 ^ 2 = 0 := by linear_combination h0
      have hx0 : x0 = 0 := (pow_eq_zero_iff two_ne_zero).mp hx0sq
      subst hx0
      norm_num at h1
  ·
    have htarget : c * x3 ^ 4 + x2 ^ 4 = 0 := by
      have hfour : (4 : K) ≠ 0 := by
        rw [show (4 : K) = 2 * 2 by norm_num]
        exact mul_ne_zero two_ne_zero two_ne_zero
      apply mul_left_cancel₀ (mul_ne_zero hfour hc0)
      linear_combination
        (-2 * (x1 * x3 - 2 * x2 ^ 2)) * h0
          + (4 * c * x3 ^ 2 - 2 * x0 * x2) * h2
          + (x0 * x1 - 3 * c * x2 * x3) * h3
    apply hnc
    refine ⟨x2 ^ 2 / x3 ^ 2, ?_⟩
    field_simp [hx3]
    linear_combination -htarget

theorem tau_not_isSquare_of_nonsquares [NeZero (2 : K)] (c : K)
    (hc : ¬ IsSquare c) (hnc : ¬ IsSquare (-c)) :
    ¬ IsSquare (τ c) := by
  rintro ⟨y, hy⟩
  rcases exists_coeffPoly4_mk_eq c y with ⟨x0, x1, x2, x3, hyrepr⟩
  have hsq : AdjoinRoot.mk (quarticPoly c) (coeffPoly4 x0 x1 x2 x3) ^ 2 = τ c := by
    simpa [hyrepr, pow_two] using hy.symm
  rcases coeff_equations_of_mk_coeffPoly4_square_eq_tau c x0 x1 x2 x3 hsq with
    ⟨h0, h1sub, h2, h3⟩
  have h1 : 2 * x0 * x1 + c * (2 * x2 * x3) = 1 := by
    linear_combination h1sub
  exact quartic_generator_not_square_coeff c x0 x1 x2 x3 hc hnc h0 h1 h2 h3

theorem field_square_eq_mul_square_forces_right_zero
    {L : Type*} [Field L] {t P Q : L} (ht : ¬ IsSquare t)
    (hrel : P ^ 2 = t * Q ^ 2) :
    Q = 0 := by
  by_contra hQ
  have hQne : Q ≠ 0 := by exact hQ
  apply ht
  refine ⟨P / Q, ?_⟩
  have hQ2 : Q ^ 2 ≠ 0 := pow_ne_zero 2 hQne
  calc
    t = P ^ 2 / Q ^ 2 := by
      rw [hrel]
      field_simp [hQ2]
    _ = (P / Q) * (P / Q) := by
      field_simp [hQne]

theorem square_eq_tau_mul_square_forces_right_zero_of_irreducible [NeZero (2 : K)] (c : K)
    [Fact (Irreducible (quarticPoly c))]
    (hc : ¬ IsSquare c) (hnc : ¬ IsSquare (-c))
    {P Q : QuarticRoot c} (hrel : P ^ 2 = τ c * Q ^ 2) :
    Q = 0 := by
  exact field_square_eq_mul_square_forces_right_zero
    (tau_not_isSquare_of_nonsquares c hc hnc) hrel

theorem quartic_monic_quadratic_factor_coeffs_force_square [NeZero (2 : K)]
    (c a b d : K)
    (hX3 : a * (d - b) = 0)
    (hX2 : b + d - a ^ 2 = 0)
    (hX0 : b * d = -c) :
    IsSquare c ∨ IsSquare (-c) := by
  rcases mul_eq_zero.mp hX3 with ha | hdb
  · subst ha
    have hd : d = -b := by linear_combination hX2
    subst hd
    left
    refine ⟨b, ?_⟩
    calc
      c = -(-c) := by ring
      _ = -(b * -b) := by rw [hX0]
      _ = b * b := by ring
  · have hd : d = b := sub_eq_zero.mp hdb
    right
    refine ⟨b, ?_⟩
    calc
      -c = b * d := hX0.symm
      _ = b * b := by rw [hd]

theorem quartic_monic_quadratic_factor_force_square [NeZero (2 : K)]
    (c a b d : K)
    (hfac : (X ^ 2 + C a * X + C b) * (X ^ 2 - C a * X + C d) = quarticPoly c) :
    IsSquare c ∨ IsSquare (-c) := by
  have hX3 : a * (d - b) = 0 := by
    have h := congrArg (fun p : K[X] => p.coeff 1) hfac
    simp [quarticPoly] at h
    have hexp :
        (X ^ 2 + C a * X + C b) * (X ^ 2 - C a * X + C d) =
          -(X * C a * C b) + X * C a * C d - X ^ 2 * C a ^ 2
            + X ^ 2 * C b + X ^ 2 * C d + X ^ 4 + C b * C d := by
      ring_nf
    have hcoeff :
        ((X ^ 2 + C a * X + C b) * (X ^ 2 - C a * X + C d)).coeff 1 =
          a * d - a * b := by
      rw [hexp]
      change (-(X * C a * C b) + X * C a * C d - X ^ 2 * C a ^ 2
            + X ^ 2 * C b + X ^ 2 * C d + X ^ 4 + C b * C d : K[X]).coeff 1 =
          a * d - a * b
      simp only [coeff_add, coeff_neg, coeff_sub, coeff_mul_C, coeff_X_pow_mul',
        coeff_X_pow, coeff_C, coeff_X]
      norm_num
      ring_nf
    rw [hcoeff] at h
    linear_combination h
  have hX2 : b + d - a ^ 2 = 0 := by
    have h := congrArg (fun p : K[X] => p.coeff 2) hfac
    simp [quarticPoly] at h
    have hexp :
        (X ^ 2 + C a * X + C b) * (X ^ 2 - C a * X + C d) =
          -(X * C a * C b) + X * C a * C d - X ^ 2 * C a ^ 2
            + X ^ 2 * C b + X ^ 2 * C d + X ^ 4 + C b * C d := by
      ring_nf
    have hcoeff :
        ((X ^ 2 + C a * X + C b) * (X ^ 2 - C a * X + C d)).coeff 2 =
          b + d - a ^ 2 := by
      rw [hexp]
      change (-(X * C a * C b) + X * C a * C d - X ^ 2 * C a ^ 2
            + X ^ 2 * C b + X ^ 2 * C d + X ^ 4 + C b * C d : K[X]).coeff 2 =
          b + d - a ^ 2
      rw [show (C a ^ 2 : K[X]) = C (a * a) by rw [pow_two, ← C_mul]]
      simp only [coeff_add, coeff_neg, coeff_sub, coeff_mul_C, coeff_X_pow_mul',
        coeff_X_pow, coeff_C, coeff_X]
      norm_num
      ring_nf
    rw [hcoeff] at h
    exact h
  have hX0 : b * d = -c := by
    have h := congrArg (fun p : K[X] => p.coeff 0) hfac
    simp [quarticPoly] at h
    linear_combination h
  exact quartic_monic_quadratic_factor_coeffs_force_square c a b d hX3 hX2 hX0

theorem quartic_linear_factor_force_square (c r : K) (q : K[X])
    (hfac : (X - C r) * q = quarticPoly c) :
    IsSquare c := by
  have hroot : (quarticPoly c).eval r = 0 := by
    rw [← hfac]
    simp
  refine ⟨r ^ 2, ?_⟩
  simp [quarticPoly] at hroot
  calc
    c = r ^ 4 := (sub_eq_zero.mp hroot).symm
    _ = r ^ 2 * r ^ 2 := by ring

theorem quartic_two_monic_quadratic_factor_force_square [NeZero (2 : K)]
    (c a b e d : K)
    (hfac : (X ^ 2 + C a * X + C b) * (X ^ 2 + C e * X + C d) = quarticPoly c) :
    IsSquare c ∨ IsSquare (-c) := by
  have hX3 : a + e = 0 := by
    have h := congrArg (fun p : K[X] => p.coeff 3) hfac
    simp [quarticPoly] at h
    have hexp :
        (X ^ 2 + C a * X + C b) * (X ^ 2 + C e * X + C d) =
          X * C a * C d + X * C e * C b + X ^ 2 * C a * C e
            + X ^ 2 * C b + X ^ 2 * C d + X ^ 3 * C a + X ^ 3 * C e
            + X ^ 4 + C b * C d := by
      ring_nf
    have hcoeff :
        ((X ^ 2 + C a * X + C b) * (X ^ 2 + C e * X + C d)).coeff 3 =
          a + e := by
      rw [hexp]
      simp only [coeff_add, coeff_mul_C, coeff_X_pow_mul', coeff_X_pow, coeff_C, coeff_X]
      norm_num
    rw [hcoeff] at h
    exact h
  have he : e = -a := by linear_combination hX3
  subst e
  have hfac' : (X ^ 2 + C a * X + C b) * (X ^ 2 - C a * X + C d) = quarticPoly c := by
    simpa [sub_eq_add_neg, neg_mul, map_neg] using hfac
  exact quartic_monic_quadratic_factor_force_square c a b d hfac'

theorem quartic_degree_one_monic_divisor_force_square (c : K) {q : K[X]}
    (hq : q.Monic) (hqdeg : q.natDegree = 1) (hdiv : q ∣ quarticPoly c) :
    IsSquare c := by
  rcases hdiv with ⟨m, hm⟩
  have hqform : q = X - C (-q.coeff 0) := by
    simpa [sub_eq_add_neg] using hq.eq_X_add_C hqdeg
  have hfac : (X - C (-q.coeff 0)) * m = quarticPoly c := by
    rw [← hqform]
    exact hm.symm
  exact quartic_linear_factor_force_square c (-q.coeff 0) m hfac

theorem exists_eq_monic_quadratic_of_natDegree_two {q : K[X]}
    (hq : q.Monic) (hqdeg : q.natDegree = 2) :
    ∃ a b : K, q = X ^ 2 + C a * X + C b := by
  have hmono : IsMonicOfDegree q 2 := by
    rw [isMonicOfDegree_iff]
    exact ⟨hqdeg.le, by simpa [hqdeg] using hq.coeff_natDegree⟩
  exact isMonicOfDegree_two_iff.mp hmono

theorem quartic_degree_two_monic_divisor_force_square [NeZero (2 : K)] (c : K) {q : K[X]}
    (hq : q.Monic) (hqdeg : q.natDegree = 2) (hdiv : q ∣ quarticPoly c) :
    IsSquare c ∨ IsSquare (-c) := by
  rcases hdiv with ⟨m, hm⟩
  have hmmonic : m.Monic := by
    have hprod : (q * m).Monic := by
      rw [← hm]
      exact quarticPoly_monic c
    exact hq.of_mul_monic_left hprod
  have hmdeg : m.natDegree = 2 := by
    have hmul := hq.natDegree_mul hmmonic
    rw [← hm, quarticPoly_natDegree c, hqdeg] at hmul
    omega
  rcases exists_eq_monic_quadratic_of_natDegree_two hq hqdeg with ⟨a, b, hqform⟩
  rcases exists_eq_monic_quadratic_of_natDegree_two hmmonic hmdeg with ⟨e, d, hmform⟩
  have hfac : (X ^ 2 + C a * X + C b) * (X ^ 2 + C e * X + C d) = quarticPoly c := by
    rw [← hqform, ← hmform]
    exact hm.symm
  exact quartic_two_monic_quadratic_factor_force_square c a b e d hfac

theorem quarticPoly_irreducible_of_nonsquares [NeZero (2 : K)] (c : K)
    (hc : ¬ IsSquare c) (hnc : ¬ IsSquare (-c)) :
    Irreducible (quarticPoly c) := by
  have hp1 : quarticPoly c ≠ 1 := by
    intro hp
    have hdeg := congrArg natDegree hp
    simp [quarticPoly_natDegree c] at hdeg
  rw [(quarticPoly_monic c).irreducible_iff_lt_natDegree_lt hp1]
  intro q hq hqdeg hdiv
  have hqdeg' : q.natDegree = 1 ∨ q.natDegree = 2 := by
    simp [quarticPoly_natDegree c] at hqdeg
    omega
  rcases hqdeg' with hqone | hqtwo
  · exact hc (quartic_degree_one_monic_divisor_force_square c hq hqone hdiv)
  · rcases quartic_degree_two_monic_divisor_force_square c hq hqtwo hdiv with hc' | hnc'
    · exact hc hc'
    · exact hnc hnc'

theorem square_eq_tau_mul_square_forces_right_zero [NeZero (2 : K)] (c : K)
    (hc : ¬ IsSquare c) (hnc : ¬ IsSquare (-c))
    {P Q : QuarticRoot c} (hrel : P ^ 2 = τ c * Q ^ 2) :
    Q = 0 := by
  letI : Fact (Irreducible (quarticPoly c)) :=
    ⟨quarticPoly_irreducible_of_nonsquares c hc hnc⟩
  exact square_eq_tau_mul_square_forces_right_zero_of_irreducible c hc hnc hrel

theorem mk_coeffPoly4_eq_zero_coeffs (c x0 x1 x2 x3 : K)
    (hzero : AdjoinRoot.mk (quarticPoly c) (coeffPoly4 x0 x1 x2 x3) = 0) :
    x0 = 0 ∧ x1 = 0 ∧ x2 = 0 ∧ x3 = 0 := by
  have hpoly : coeffPoly4 x0 x1 x2 x3 = 0 := by
    by_contra hne
    have hdeg : (coeffPoly4 x0 x1 x2 x3).natDegree < (quarticPoly c).natDegree := by
      rw [quarticPoly_natDegree c, coeffPoly4]
      compute_degree!
    exact (AdjoinRoot.mk_ne_zero_of_natDegree_lt (quarticPoly_monic c) hne hdeg) hzero
  have h0 := congrArg (fun p : K[X] => p.coeff 0) hpoly
  have h1 := congrArg (fun p : K[X] => p.coeff 1) hpoly
  have h2 := congrArg (fun p : K[X] => p.coeff 2) hpoly
  have h3 := congrArg (fun p : K[X] => p.coeff 3) hpoly
  simp [coeffPoly4] at h0 h1 h2 h3
  exact ⟨h0, h1, h2, h3⟩

theorem quartic_adjoinroot_norm_descent_coeffs [NeZero (2 : K)] (c : K)
    (hc : ¬ IsSquare c) (hnc : ¬ IsSquare (-c))
    (p0 p1 p2 p3 q0 q1 q2 q3 : K)
    (hrel :
      (AdjoinRoot.mk (quarticPoly c) (coeffPoly4 p0 p1 p2 p3)) ^ 2 =
        τ c * (AdjoinRoot.mk (quarticPoly c) (coeffPoly4 q0 q1 q2 q3)) ^ 2) :
    p0 = 0 ∧ p1 = 0 ∧ p2 = 0 ∧ p3 = 0 ∧
      q0 = 0 ∧ q1 = 0 ∧ q2 = 0 ∧ q3 = 0 := by
  letI : Fact (Irreducible (quarticPoly c)) :=
    ⟨quarticPoly_irreducible_of_nonsquares c hc hnc⟩
  have hQzero :
      AdjoinRoot.mk (quarticPoly c) (coeffPoly4 q0 q1 q2 q3) = 0 :=
    square_eq_tau_mul_square_forces_right_zero c hc hnc hrel
  have hPzero :
      AdjoinRoot.mk (quarticPoly c) (coeffPoly4 p0 p1 p2 p3) = 0 := by
    have hsq :
        (AdjoinRoot.mk (quarticPoly c) (coeffPoly4 p0 p1 p2 p3)) ^ 2 = 0 := by
      simpa [hQzero] using hrel
    exact eq_zero_of_pow_eq_zero hsq
  rcases mk_coeffPoly4_eq_zero_coeffs c p0 p1 p2 p3 hPzero with ⟨hp0, hp1, hp2, hp3⟩
  rcases mk_coeffPoly4_eq_zero_coeffs c q0 q1 q2 q3 hQzero with ⟨hq0, hq1, hq2, hq3⟩
  exact ⟨hp0, hp1, hp2, hp3, hq0, hq1, hq2, hq3⟩

private noncomputable def normRelationRemainder
    (c p0 p1 p2 p3 q0 q1 q2 q3 : K) : K[X] :=
  C (p0 ^ 2 + c * (2 * p1 * p3 + p2 ^ 2 - (2 * q0 * q3 + 2 * q1 * q2)))
    + C (2 * p0 * p1 + c * (2 * p2 * p3) - (q0 ^ 2 + c * (2 * q1 * q3 + q2 ^ 2))) * X
    + C (2 * p0 * p2 + p1 ^ 2 + c * (p3 ^ 2 - 2 * q2 * q3) - 2 * q0 * q1) * X ^ 2
    + C (2 * p0 * p3 + 2 * p1 * p2 - (2 * q0 * q2 + q1 ^ 2) - c * q3 ^ 2) * X ^ 3

private noncomputable def normRelationQuotient
    (p1 p2 p3 q0 q1 q2 q3 : K) : K[X] :=
  C (2 * p1 * p3 + p2 ^ 2 - (2 * q0 * q3 + 2 * q1 * q2))
    + C (2 * p2 * p3 - (2 * q1 * q3 + q2 ^ 2)) * X
    + C (p3 ^ 2 - 2 * q2 * q3) * X ^ 2
    - C (q3 ^ 2) * X ^ 3

theorem coeffPoly4_norm_relation_identity
    (c p0 p1 p2 p3 q0 q1 q2 q3 : K) :
    coeffPoly4 p0 p1 p2 p3 ^ 2 - X * coeffPoly4 q0 q1 q2 q3 ^ 2 =
      quarticPoly c * normRelationQuotient p1 p2 p3 q0 q1 q2 q3
        + normRelationRemainder c p0 p1 p2 p3 q0 q1 q2 q3 := by
  simp [coeffPoly4, quarticPoly, normRelationQuotient, normRelationRemainder]
  simp only [Polynomial.C_ofNat]
  ring_nf!

theorem normRelationRemainder_eq_zero_of_coeffs
    (c p0 p1 p2 p3 q0 q1 q2 q3 : K)
    (h0 : p0 ^ 2 + c * (2 * p1 * p3 + p2 ^ 2 - (2 * q0 * q3 + 2 * q1 * q2)) = 0)
    (h1 : 2 * p0 * p1 + c * (2 * p2 * p3) - (q0 ^ 2 + c * (2 * q1 * q3 + q2 ^ 2)) = 0)
    (h2 : 2 * p0 * p2 + p1 ^ 2 + c * (p3 ^ 2 - 2 * q2 * q3) - 2 * q0 * q1 = 0)
    (h3 : 2 * p0 * p3 + 2 * p1 * p2 - (2 * q0 * q2 + q1 ^ 2) - c * q3 ^ 2 = 0) :
    normRelationRemainder c p0 p1 p2 p3 q0 q1 q2 q3 = 0 := by
  ext n
  by_cases hn : n < 4
  · interval_cases n <;> simp [normRelationRemainder, h0, h1, h2, h3]
  · have hdeg : (normRelationRemainder c p0 p1 p2 p3 q0 q1 q2 q3).natDegree < n := by
      rw [normRelationRemainder]
      compute_degree!
      omega
    rw [coeff_eq_zero_of_natDegree_lt hdeg, coeff_zero]

theorem quartic_scalar_norm_descent_coeffs [NeZero (2 : K)] (c : K)
    (hc : ¬ IsSquare c) (hnc : ¬ IsSquare (-c))
    (p0 p1 p2 p3 q0 q1 q2 q3 : K)
    (h0 : p0 ^ 2 + c * (2 * p1 * p3 + p2 ^ 2 - (2 * q0 * q3 + 2 * q1 * q2)) = 0)
    (h1 : 2 * p0 * p1 + c * (2 * p2 * p3) - (q0 ^ 2 + c * (2 * q1 * q3 + q2 ^ 2)) = 0)
    (h2 : 2 * p0 * p2 + p1 ^ 2 + c * (p3 ^ 2 - 2 * q2 * q3) - 2 * q0 * q1 = 0)
    (h3 : 2 * p0 * p3 + 2 * p1 * p2 - (2 * q0 * q2 + q1 ^ 2) - c * q3 ^ 2 = 0) :
    p0 = 0 ∧ p1 = 0 ∧ p2 = 0 ∧ p3 = 0 ∧
      q0 = 0 ∧ q1 = 0 ∧ q2 = 0 ∧ q3 = 0 := by
  have hrem :
      normRelationRemainder c p0 p1 p2 p3 q0 q1 q2 q3 = 0 :=
    normRelationRemainder_eq_zero_of_coeffs c p0 p1 p2 p3 q0 q1 q2 q3 h0 h1 h2 h3
  have hrel :
      (AdjoinRoot.mk (quarticPoly c) (coeffPoly4 p0 p1 p2 p3)) ^ 2 =
        τ c * (AdjoinRoot.mk (quarticPoly c) (coeffPoly4 q0 q1 q2 q3)) ^ 2 := by
    have hpoly := coeffPoly4_norm_relation_identity c p0 p1 p2 p3 q0 q1 q2 q3
    have hmk := congrArg (AdjoinRoot.mk (quarticPoly c)) hpoly
    have hdiff :
        (AdjoinRoot.mk (quarticPoly c) (coeffPoly4 p0 p1 p2 p3)) ^ 2
            - τ c * (AdjoinRoot.mk (quarticPoly c) (coeffPoly4 q0 q1 q2 q3)) ^ 2 = 0 := by
      simpa [hrem, τ, AdjoinRoot.mk_X, map_add, map_mul, map_sub, map_pow,
        AdjoinRoot.mk_self, tau_pow_four c] using hmk
    exact sub_eq_zero.mp hdiff
  exact quartic_adjoinroot_norm_descent_coeffs c hc hnc p0 p1 p2 p3 q0 q1 q2 q3 hrel

theorem quartic_weighted_norm_descent_coeffs [NeZero (2 : K)]
    (G H : K) (hG : G ≠ 0)
    (hc : ¬ IsSquare (H / G)) (hnc : ¬ IsSquare (-(H / G)))
    (p0 p1 p2 p3 q0 q1 q2 q3 : K)
    (h0 : G * p0 ^ 2 + H * (2 * p1 * p3 + p2 ^ 2 - (2 * q0 * q3 + 2 * q1 * q2)) = 0)
    (h1 : G * (2 * p0 * p1 - q0 ^ 2)
        + H * (2 * p2 * p3 - (2 * q1 * q3 + q2 ^ 2)) = 0)
    (h2 : G * (2 * p0 * p2 + p1 ^ 2 - 2 * q0 * q1)
        + H * (p3 ^ 2 - 2 * q2 * q3) = 0)
    (h3 : G * (2 * p0 * p3 + 2 * p1 * p2 - (2 * q0 * q2 + q1 ^ 2))
        - H * q3 ^ 2 = 0) :
    p0 = 0 ∧ p1 = 0 ∧ p2 = 0 ∧ p3 = 0 ∧
      q0 = 0 ∧ q1 = 0 ∧ q2 = 0 ∧ q3 = 0 := by
  have h0' :
      p0 ^ 2 + (H / G) * (2 * p1 * p3 + p2 ^ 2 - (2 * q0 * q3 + 2 * q1 * q2)) = 0 := by
    apply mul_left_cancel₀ hG
    field_simp [hG]
    linear_combination h0
  have h1' :
      2 * p0 * p1 + (H / G) * (2 * p2 * p3)
          - (q0 ^ 2 + (H / G) * (2 * q1 * q3 + q2 ^ 2)) = 0 := by
    apply mul_left_cancel₀ hG
    field_simp [hG]
    linear_combination h1
  have h2' :
      2 * p0 * p2 + p1 ^ 2 + (H / G) * (p3 ^ 2 - 2 * q2 * q3) - 2 * q0 * q1 = 0 := by
    apply mul_left_cancel₀ hG
    field_simp [hG]
    linear_combination h2
  have h3' :
      2 * p0 * p3 + 2 * p1 * p2 - (2 * q0 * q2 + q1 ^ 2) - (H / G) * q3 ^ 2 = 0 := by
    apply mul_left_cancel₀ hG
    field_simp [hG]
    linear_combination h3
  exact quartic_scalar_norm_descent_coeffs (H / G) hc hnc
    p0 p1 p2 p3 q0 q1 q2 q3 h0' h1' h2' h3'

end ArkLib.ProximityGap.Frontier.R25QuarticAdjoinRoot

/-! ## Axiom audit -/
open ArkLib.ProximityGap.Frontier.R25QuarticAdjoinRoot in
#print axioms tau_pow_four
open ArkLib.ProximityGap.Frontier.R25QuarticAdjoinRoot in
#print axioms tau_ne_zero_of_irreducible
open ArkLib.ProximityGap.Frontier.R25QuarticAdjoinRoot in
#print axioms squareTauRemainder_natDegree_lt_four
open ArkLib.ProximityGap.Frontier.R25QuarticAdjoinRoot in
#print axioms squareTauRemainder_coeff_zero
open ArkLib.ProximityGap.Frontier.R25QuarticAdjoinRoot in
#print axioms squareTauRemainder_coeff_one
open ArkLib.ProximityGap.Frontier.R25QuarticAdjoinRoot in
#print axioms squareTauRemainder_coeff_two
open ArkLib.ProximityGap.Frontier.R25QuarticAdjoinRoot in
#print axioms squareTauRemainder_coeff_three
open ArkLib.ProximityGap.Frontier.R25QuarticAdjoinRoot in
#print axioms coeffPoly4_square_sub_X_identity
open ArkLib.ProximityGap.Frontier.R25QuarticAdjoinRoot in
#print axioms mk_coeffPoly4_square_sub_tau_eq_remainder
open ArkLib.ProximityGap.Frontier.R25QuarticAdjoinRoot in
#print axioms coeff_equations_of_mk_coeffPoly4_square_eq_tau
open ArkLib.ProximityGap.Frontier.R25QuarticAdjoinRoot in
#print axioms exists_coeffPoly4_mk_eq
open ArkLib.ProximityGap.Frontier.R25QuarticAdjoinRoot in
#print axioms tau_not_isSquare_of_nonsquares
open ArkLib.ProximityGap.Frontier.R25QuarticAdjoinRoot in
#print axioms field_square_eq_mul_square_forces_right_zero
open ArkLib.ProximityGap.Frontier.R25QuarticAdjoinRoot in
#print axioms square_eq_tau_mul_square_forces_right_zero_of_irreducible
open ArkLib.ProximityGap.Frontier.R25QuarticAdjoinRoot in
#print axioms quartic_monic_quadratic_factor_coeffs_force_square
open ArkLib.ProximityGap.Frontier.R25QuarticAdjoinRoot in
#print axioms quartic_monic_quadratic_factor_force_square
open ArkLib.ProximityGap.Frontier.R25QuarticAdjoinRoot in
#print axioms quartic_linear_factor_force_square
open ArkLib.ProximityGap.Frontier.R25QuarticAdjoinRoot in
#print axioms quartic_two_monic_quadratic_factor_force_square
open ArkLib.ProximityGap.Frontier.R25QuarticAdjoinRoot in
#print axioms quartic_degree_one_monic_divisor_force_square
open ArkLib.ProximityGap.Frontier.R25QuarticAdjoinRoot in
#print axioms exists_eq_monic_quadratic_of_natDegree_two
open ArkLib.ProximityGap.Frontier.R25QuarticAdjoinRoot in
#print axioms quartic_degree_two_monic_divisor_force_square
open ArkLib.ProximityGap.Frontier.R25QuarticAdjoinRoot in
#print axioms quarticPoly_irreducible_of_nonsquares
open ArkLib.ProximityGap.Frontier.R25QuarticAdjoinRoot in
#print axioms square_eq_tau_mul_square_forces_right_zero
open ArkLib.ProximityGap.Frontier.R25QuarticAdjoinRoot in
#print axioms mk_coeffPoly4_eq_zero_coeffs
open ArkLib.ProximityGap.Frontier.R25QuarticAdjoinRoot in
#print axioms quartic_adjoinroot_norm_descent_coeffs
open ArkLib.ProximityGap.Frontier.R25QuarticAdjoinRoot in
#print axioms coeffPoly4_norm_relation_identity
open ArkLib.ProximityGap.Frontier.R25QuarticAdjoinRoot in
#print axioms normRelationRemainder_eq_zero_of_coeffs
open ArkLib.ProximityGap.Frontier.R25QuarticAdjoinRoot in
#print axioms quartic_scalar_norm_descent_coeffs
open ArkLib.ProximityGap.Frontier.R25QuarticAdjoinRoot in
#print axioms quartic_weighted_norm_descent_coeffs
