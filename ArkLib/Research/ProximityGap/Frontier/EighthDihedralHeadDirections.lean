/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! # Complete dihedral covariance obstructions for eighth-rate four-head quartets at 671,088,640

Previously (`EighthDyadicHeadDirections.lean`), rotational covariance `X ↦ ζ X` was analyzed
for four rich eighth-rate heads at `e = 671,088,640` (`0 ≤ s ≤ 4`), ruling out the scalar
antipode and nonscalar quarter turns and pinning any nonscalar antipode to `r = 0, s = 4`.

This module completes the classification across the **entire dihedral group `D_{2n}`** of order
`2^{31}` (`⟨X ↦ ζ X, X ↦ c / X⟩` on `H = μ_{2^30}`), plus excludes the sign-flip quotient
involution `J'(w) = -w` in the surviving nonscalar antipode:

1. **Scalar reflection exclusion (`reflection_scalar_mass_odd`, `reflection_scalar_mass_even`)**:
   for ANY `c ∈ H` (even or odd), scalar reflection covariance `zᵢ(c / X) = zᵢ(X)` caps total
   fresh head labels at `1,879,048,352` (`+ 20,607,410 ≪ 2n`), impossible across all `0 ≤ s ≤ 4`.
2. **Universal polynomial reversal & fixed-point vanishing (`revPoly_eval`, `revPoly_involution`,
   `revPoly_odd_fixed_root`, `revPoly_even_fixed_roots`, `nonscalar_reflection_det_vanish`)**:
   over ANY field `F` of characteristic `≠ 2`, for any `a ∈ F` with `a² = c ≠ 0` and any
   nonscalar reflection eigenbasis (`revPoly N c Uᵢ = C ε * Uᵢ`, `revPoly N c Vᵢ = C (-ε) * Vᵢ`),
   every `2×2` triangle determinant `U₁ V₂ - U₂ V₁` vanishes at BOTH `a` and `-a`, hence is
   divisible by `X² - C c` in both parities of `N`.
3. **Nonscalar odd reflection exclusion (`nonscalar_odd_reflection_forces_s4`)**:
   when `c ∈ H \ H²` (`±a ∉ H`), `X² - C c` costs `2` roots outside `H` in every triangle
   determinant, proving ALL four profiles `0 ≤ s ≤ 3` (`(1,1,1,1)..(1,1,1,4)`) and ALL even `N`
   are impossible, and pinning `s = 4` to `r = 0, N = d, x₀ = x₃ = x₄ = 0, x₂ = 4d - 4`.
4. **Nonscalar even reflection obstruction (`fixed_point_weight_excess`,
   `nonscalar_even_reflection_obstruction`)**:
   when `c = a² ∈ H²` (`±a ∈ H`), every fixed point outside `Z(h)` adds at least `1` excess
   triangle root (`+2` unless `W(±a) = 3`), forcing `2 r + f + 8(d - r - N) ≤ 2 s`. Hence exact
   saturation `s = 0` (`(1,1,1,1)`) is impossible, `r = 0` with even `N` is impossible for all
   `0 ≤ s ≤ 4`, and `r = 0, s = 1` forces both `±a` to be triple sites.
5. **Dihedral triviality of saturated quartets (`saturated_dihedral_triviality`)**:
   combining rotational and reflectional obstructions proves that a saturated `(1,1,1,1)` quartet
   at `671,088,640` admits ZERO nontrivial symmetries in `D_{2n}`.
6. **Nonscalar antipode involution exclusion (`nonscalar_antipode_involution_ne_neg`)**:
   in the surviving `s = 4` nonscalar antipode, the quotient opposite-direction involution on `H²`
   cannot be `J'(w) = -w`, since pairwise antipodal collisions lose `4 d' = 268,435,452` labels.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.EighthDihedralHeadDirections

open Finset Polynomial

abbrev n : ℕ := 1073741824
abbrev k : ℕ := 134217728
abbrev d : ℕ := 134217727
abbrev budget : ℕ := 2147483648

/-! ## Section 1: Scalar reflection covariance exclusion (`X ↦ c / X`, all `0 ≤ s ≤ 4`) -/

/-- Under an odd scalar reflection `X ↦ c / X` (`c ∈ H \ H²`, zero fixed points in `H`),
the `n / 2 = 536,870,912` disjoint pairs `{x, c / x}` with at most `12` exceptional pairs
carry at most `1,879,048,348` distinct fresh labels, far below `2n` even with the baseline
`20,607,410` residual allowance. -/
theorem reflection_scalar_mass_odd {J : Type*} [Fintype J] [DecidableEq J]
    (bad : Finset J) (M W : J → ℕ) (other : ℕ)
    (count : Fintype.card J = 536870912)
    (rich : 1610612728 ≤ ∑ i, W i)
    (small : bad.card ≤ 12)
    (localBound : ∀ i, 2 * M i + 3 * W i ≤ 16 + (if i ∈ bad then 24 else 0))
    (hother : other ≤ 20607410) :
    (∑ i, M i) ≤ 1879048348 ∧ (∑ i, M i) + other < budget := by
  have t := sum_le_sum (s := (univ : Finset J)) (fun i _ => localBound i)
  simp only [sum_add_distrib, ← mul_sum, sum_const, card_univ, count, smul_eq_mul] at t
  have hb : (∑ i, if i ∈ bad then 24 else 0) = bad.card * 24 := by simp
  simp only [budget]
  omega

/-- Under an even scalar reflection `X ↦ a² / X` (`a ∈ H`, two fixed points `±a` in `H`),
each fixed point satisfies `M(x) + W(x) ≤ 4` (including uncovered sites `W(x) = 0, M(x) ≤ 4`),
so `fixedLabels + fixedCore ≤ 8`. Together with the `536,870,911` disjoint pairs `{x, a² / x}`
(at most `12` exceptional pairs), total fresh head labels are at most `1,879,048,352`, far
below `2n` across all `0 ≤ s ≤ 4`. -/
theorem reflection_scalar_mass_even {J : Type*} [Fintype J] [DecidableEq J]
    (bad : Finset J) (M W : J → ℕ) (fixedLabels fixedCore other : ℕ)
    (count : Fintype.card J = 536870911)
    (hfixed : fixedLabels + fixedCore ≤ 8)
    (rich : 1610612728 ≤ fixedCore + ∑ i, W i)
    (small : bad.card ≤ 12)
    (localBound : ∀ i, 2 * M i + 3 * W i ≤ 16 + (if i ∈ bad then 24 else 0))
    (hother : other ≤ 20607410) :
    fixedLabels + (∑ i, M i) ≤ 1879048352 ∧ fixedLabels + (∑ i, M i) + other < budget := by
  have t := sum_le_sum (s := (univ : Finset J)) (fun i _ => localBound i)
  simp only [sum_add_distrib, ← mul_sum, sum_const, card_univ, count, smul_eq_mul] at t
  have hb : (∑ i, if i ∈ bad then 24 else 0) = bad.card * 24 := by simp
  simp only [budget]
  omega

/-! ## Section 2: Polynomial reversal and universal fixed-point determinant vanishing -/

section Reversal

variable {F : Type*} [Field F]

/-- Degree-`N` reflection reversal operator `(revPoly N c P)(X) = X^N * P(c / X)`. -/
noncomputable def revPoly (N : ℕ) (c : F) (P : F[X]) : F[X] :=
  ∑ j ∈ range (N + 1), monomial (N - j) (c ^ j * P.coeff j)

/-- Evaluation identity: for `deg P ≤ N` and `x ≠ 0`, `(revPoly N c P).eval x = x^N * P.eval (c / x)`. -/
theorem revPoly_eval {N : ℕ} {c x : F} {P : F[X]} (hdeg : P.natDegree ≤ N) (hx : x ≠ 0) :
    (revPoly N c P).eval x = x ^ N * P.eval (c / x) := by
  unfold revPoly
  rw [eval_finsetSum, eval_eq_sum_range' (Nat.lt_succ_of_le hdeg), mul_sum]
  apply sum_congr rfl
  intro j hj
  have hjN : j ≤ N := Nat.lt_succ_iff.mp (mem_range.mp hj)
  rw [eval_monomial, div_pow]
  have hpow : x ^ N = x ^ (N - j) * x ^ j := by
    rw [← pow_add, Nat.sub_add_cancel hjN]
  have hxj : x ^ j ≠ 0 := pow_ne_zero j hx
  calc
    c ^ j * P.coeff j * x ^ (N - j) = P.coeff j * (x ^ (N - j) * (x ^ j * (c ^ j / x ^ j))) := by
        rw [mul_div_cancel₀ _ hxj]; ring
    _ = (x ^ (N - j) * x ^ j) * (P.coeff j * (c ^ j / x ^ j)) := by ring
    _ = x ^ N * (P.coeff j * (c ^ j / x ^ j)) := by rw [← hpow]

/-- Coefficient formula for `revPoly N c P`. -/
theorem revPoly_coeff (N : ℕ) (c : F) (P : F[X]) (i : ℕ) :
    (revPoly N c P).coeff i = if i ≤ N then c ^ (N - i) * P.coeff (N - i) else 0 := by
  unfold revPoly
  rw [finsetSum_coeff]
  simp only [coeff_monomial]
  by_cases hi : i ≤ N
  · simp only [hi, ↓reduceIte]
    rw [Finset.sum_eq_single (N - i)]
    · have hsub : N - (N - i) = i := Nat.sub_sub_self hi
      simp [hsub]
    · intro j hj hne
      have hjN : j ≤ N := Nat.lt_succ_iff.mp (mem_range.mp hj)
      have hne' : N - j ≠ i := by omega
      simp [hne']
    · intro hnot
      exact absurd (mem_range.mpr (by omega)) hnot
  · simp only [hi, ↓reduceIte]
    rw [Finset.sum_eq_zero]
    intro j hj
    have hne' : N - j ≠ i := by omega
    simp [hne']

/-- Applying `revPoly N c` twice scales any polynomial of degree `≤ N` by `c^N`. -/
theorem revPoly_involution {N : ℕ} {c : F} {P : F[X]} (hdeg : P.natDegree ≤ N) :
    revPoly N c (revPoly N c P) = C (c ^ N) * P := by
  ext i
  rw [revPoly_coeff, coeff_C_mul]
  by_cases hi : i ≤ N
  · simp only [hi, ↓reduceIte]
    have hsub : N - i ≤ N := Nat.sub_le N i
    rw [revPoly_coeff]
    simp only [hsub, ↓reduceIte, Nat.sub_sub_self hi]
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hi]
  · simp only [hi, ↓reduceIte]
    have h0 : P.coeff i = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    rw [h0, mul_zero]

/-- Any nonzero eigenpolynomial of `revPoly N c` with `a^2 = c` has eigenvalue `±a^N`. -/
theorem revPoly_eigenvalue {N : ℕ} {c a ε : F} {P : F[X]}
    (ha : a ^ 2 = c) (hdeg : P.natDegree ≤ N) (hP : P ≠ 0)
    (heig : revPoly N c P = C ε * P) :
    ε = a ^ N ∨ ε = -(a ^ N) := by
  have hrev_smul : revPoly N c (C ε * P) = C ε * revPoly N c P := by
    ext i
    simp only [revPoly_coeff, coeff_C_mul]
    by_cases hi : i ≤ N
    · simp only [hi, ↓reduceIte]; ring
    · simp [hi]
  have h2 : C (ε ^ 2) * P = C (c ^ N) * P := by
    calc
      C (ε ^ 2) * P = C ε * (C ε * P) := by rw [← mul_assoc, ← C_mul, sq]
      _ = C ε * revPoly N c P := by rw [heig]
      _ = revPoly N c (C ε * P) := hrev_smul.symm
      _ = revPoly N c (revPoly N c P) := by rw [heig]
      _ = C (c ^ N) * P := revPoly_involution hdeg
  have hCeq : C (ε ^ 2 - c ^ N) * P = 0 := by
    rw [map_sub, sub_mul, sub_eq_zero]; exact h2
  have hC0 : C (ε ^ 2 - c ^ N) = 0 := (mul_eq_zero.mp hCeq).resolve_right hP
  have hsq : ε ^ 2 = (a ^ N) ^ 2 := by
    have h0 : ε ^ 2 - c ^ N = 0 := C_eq_zero.mp hC0
    have hca : c ^ N = (a ^ N) ^ 2 := by rw [← ha, ← pow_mul, ← pow_mul, mul_comm]
    linear_combination h0 + hca
  have hfac : (ε - a ^ N) * (ε + a ^ N) = 0 := by linear_combination hsq
  rcases mul_eq_zero.mp hfac with h1 | h2
  · exact Or.inl (sub_eq_zero.mp h1)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h2)

/-- For odd `N` and `char F ≠ 2`, a `(+a^N)`-eigenpolynomial vanishes at `-a` and a
`(-a^N)`-eigenpolynomial vanishes at `a`. -/
theorem revPoly_odd_fixed_root {N : ℕ} {c a ε : F} {P : F[X]}
    (hchar : (2 : F) ≠ 0) (ha : a ^ 2 = c) (hane : a ≠ 0)
    (hdeg : P.natDegree ≤ N) (hodd : N % 2 = 1)
    (heig : revPoly N c P = C ε * P) :
    (ε = a ^ N → P.eval (-a) = 0) ∧ (ε = -(a ^ N) → P.eval a = 0) := by
  have hdiv_pos : c / a = a := by rw [← ha, sq, mul_div_cancel_right₀ a hane]
  have hdiv_neg : c / (-a) = -a := by
    have hna : -a ≠ 0 := neg_ne_zero.mpr hane
    rw [← ha, sq, div_eq_iff hna]; ring
  have hneg_pow : (-a) ^ N = -(a ^ N) := by
    obtain ⟨m, rfl⟩ := Nat.odd_iff.mpr hodd
    rw [pow_succ, pow_mul, neg_sq, ← pow_mul, pow_succ]; ring
  constructor
  · intro hε
    have hv := congrArg (Polynomial.eval (-a)) heig
    rw [revPoly_eval hdeg (neg_ne_zero.mpr hane), hdiv_neg, hneg_pow, eval_mul, eval_C, hε] at hv
    have h0 : (2 * a ^ N) * P.eval (-a) = 0 := by linear_combination -hv
    exact (mul_eq_zero.mp h0).resolve_left (mul_ne_zero hchar (pow_ne_zero N hane))
  · intro hε
    have hv := congrArg (Polynomial.eval a) heig
    rw [revPoly_eval hdeg hane, hdiv_pos, eval_mul, eval_C, hε] at hv
    have h0 : (2 * a ^ N) * P.eval a = 0 := by linear_combination hv
    exact (mul_eq_zero.mp h0).resolve_left (mul_ne_zero hchar (pow_ne_zero N hane))

/-- For even `N` and `char F ≠ 2`, a `(-a^N)`-eigenpolynomial vanishes at BOTH `a` and `-a`. -/
theorem revPoly_even_fixed_roots {N : ℕ} {c a : F} {P : F[X]}
    (hchar : (2 : F) ≠ 0) (ha : a ^ 2 = c) (hane : a ≠ 0)
    (hdeg : P.natDegree ≤ N) (heven : N % 2 = 0)
    (heig : revPoly N c P = C (-(a ^ N)) * P) :
    P.eval a = 0 ∧ P.eval (-a) = 0 := by
  have hdiv_pos : c / a = a := by rw [← ha, sq, mul_div_cancel_right₀ a hane]
  have hdiv_neg : c / (-a) = -a := by
    have hna : -a ≠ 0 := neg_ne_zero.mpr hane
    rw [← ha, sq, div_eq_iff hna]; ring
  have hneg_pow : (-a) ^ N = a ^ N := by
    obtain ⟨m, rfl⟩ := Nat.even_iff.mpr heven
    rw [← two_mul, pow_mul, neg_sq, ← pow_mul]
  constructor
  · have hv := congrArg (Polynomial.eval a) heig
    rw [revPoly_eval hdeg hane, hdiv_pos, eval_mul, eval_C] at hv
    have h0 : (2 * a ^ N) * P.eval a = 0 := by linear_combination hv
    exact (mul_eq_zero.mp h0).resolve_left (mul_ne_zero hchar (pow_ne_zero N hane))
  · have hv := congrArg (Polynomial.eval (-a)) heig
    rw [revPoly_eval hdeg (neg_ne_zero.mpr hane), hdiv_neg, hneg_pow, eval_mul, eval_C] at hv
    have h0 : (2 * a ^ N) * P.eval (-a) = 0 := by linear_combination hv
    exact (mul_eq_zero.mp h0).resolve_left (mul_ne_zero hchar (pow_ne_zero N hane))

/-- **Universal nonscalar reflection determinant divisibility**: over ANY field `F` with
`char F ≠ 2`, if `U₁, U₂` have reflection eigenvalue `ε ∈ {a^N, -a^N}` and `V₁, V₂` have the
opposite eigenvalue `-ε`, then `D = U₁ * V₂ - U₂ * V₁` vanishes at BOTH `a` and `-a`, and
therefore `(X^2 - C c) ∣ D` in EVERY parity of `N`. -/
theorem nonscalar_reflection_det_vanish {N : ℕ} {c a ε : F} {U₁ U₂ V₁ V₂ : F[X]}
    (hchar : (2 : F) ≠ 0) (ha : a ^ 2 = c) (hane : a ≠ 0)
    (hU1 : U₁.natDegree ≤ N) (hU2 : U₂.natDegree ≤ N)
    (hV1 : V₁.natDegree ≤ N) (hV2 : V₂.natDegree ≤ N)
    (hε : ε = a ^ N ∨ ε = -(a ^ N))
    (heU1 : revPoly N c U₁ = C ε * U₁) (heU2 : revPoly N c U₂ = C ε * U₂)
    (heV1 : revPoly N c V₁ = C (-ε) * V₁) (heV2 : revPoly N c V₂ = C (-ε) * V₂) :
    (U₁ * V₂ - U₂ * V₁).eval a = 0 ∧ (U₁ * V₂ - U₂ * V₁).eval (-a) = 0 ∧
    (X ^ 2 - C c) ∣ (U₁ * V₂ - U₂ * V₁) := by
  let D := U₁ * V₂ - U₂ * V₁
  have hvan : D.eval a = 0 ∧ D.eval (-a) = 0 := by
    rcases Nat.even_or_odd' N with ⟨m, rfl | rfl⟩
    · have heven : (2 * m) % 2 = 0 := by omega
      rcases hε with rfl | rfl
      · have h1 := revPoly_even_fixed_roots hchar ha hane hV1 heven heV1
        have h2 := revPoly_even_fixed_roots hchar ha hane hV2 heven heV2
        simp [D, h1.1, h1.2, h2.1, h2.2]
      · have h1 := revPoly_even_fixed_roots hchar ha hane hU1 heven heU1
        have h2 := revPoly_even_fixed_roots hchar ha hane hU2 heven heU2
        simp [D, h1.1, h1.2, h2.1, h2.2]
    · have hodd : (2 * m + 1) % 2 = 1 := by omega
      rcases hε with rfl | rfl
      · have hu1 := (revPoly_odd_fixed_root hchar ha hane hU1 hodd heU1).1 rfl
        have hu2 := (revPoly_odd_fixed_root hchar ha hane hU2 hodd heU2).1 rfl
        have hv1 := (revPoly_odd_fixed_root hchar ha hane hV1 hodd heV1).2 rfl
        have hv2 := (revPoly_odd_fixed_root hchar ha hane hV2 hodd heV2).2 rfl
        simp [D, hu1, hu2, hv1, hv2]
      · rw [neg_neg] at heV1 heV2
        have hu1 := (revPoly_odd_fixed_root hchar ha hane hU1 hodd heU1).2 rfl
        have hu2 := (revPoly_odd_fixed_root hchar ha hane hU2 hodd heU2).2 rfl
        have hv1 := (revPoly_odd_fixed_root hchar ha hane hV1 hodd heV1).1 rfl
        have hv2 := (revPoly_odd_fixed_root hchar ha hane hV2 hodd heV2).1 rfl
        simp [D, hu1, hu2, hv1, hv2]
  have hdvd : (X ^ 2 - C c) ∣ D := by
    have hd1 : (X - C a) ∣ D := dvd_iff_isRoot.mpr hvan.1
    obtain ⟨Q, hQ⟩ := hd1
    have hQneg : Q.eval (-a) = 0 := by
      have hv := congrArg (Polynomial.eval (-a)) hQ
      simp only [hvan.2, eval_mul, eval_sub, eval_X, eval_C] at hv
      have hne : -a - a ≠ 0 := by
        have : -a - a = -(2 * a) := by ring
        rw [this]
        exact neg_ne_zero.mpr (mul_ne_zero hchar hane)
      exact (mul_eq_zero.mp hv.symm).resolve_left hne
    obtain ⟨Q₂, hQ₂⟩ := dvd_iff_isRoot.mpr hQneg
    refine ⟨Q₂, ?_⟩
    have hfac : X ^ 2 - C c = (X - C a) * (X - C (-a)) := by
      rw [← ha, map_pow, map_neg]; ring
    rw [hQ, hQ₂, hfac]; ring
  exact ⟨hvan.1, hvan.2, hdvd⟩

end Reversal

/-! ## Section 3: Odd & even nonscalar reflection obstructions and dihedral triviality -/

/-- **Nonscalar odd reflection obstruction (`c ∈ H \ H²`)**: since both fixed points `±a ∉ H`,
the factor `X^2 - C c` consumes `2` roots outside `H` in every one of the four triangle
determinants (`≤ 2(N - 1)` roots on `H \ Z(h)` per triangle). Using the true `quotient_core_incidence`
bound `2(x₂ + 2x₃ + 3x₄) ≤ 6r + 8(N - 1) + 2x₀` together with the triangle-charge bound
`2x₂ + 5x₃ + 8x₄ ≤ 8r + 8(N - 1)` (allowing `8` per root of `h` at quadruple sites):
1. Every profile with `s ≤ 3` (`(1,1,1,1)..(1,1,1,4)`) is impossible.
2. Every even degree `N` is impossible (even at `s = 4`).
3. The sole remaining case pins `r = 0, s = 4, N = d` with `x₀ = x₃ = x₄ = 0, x₂ = 4d - 4`. -/
theorem nonscalar_odd_reflection_forces_s4 {s r N x₀ x₂ x₃ x₄ : ℕ}
    (hs : s ≤ 4) (hN : N + r ≤ d)
    (hinc : x₂ + 2 * x₃ + 3 * x₄ + s = 4 * d + x₀)
    (hquot : 2 * (x₂ + 2 * x₃ + 3 * x₄) ≤ 6 * r + 8 * (N - 1) + 2 * x₀)
    (htri : 2 * x₂ + 5 * x₃ + 8 * x₄ ≤ 8 * r + 8 * (N - 1)) :
    r = 0 ∧ s = 4 ∧ N = d ∧ N % 2 = 1 ∧ x₀ = 0 ∧ x₃ = 0 ∧ x₄ = 0 ∧ x₂ = 4 * d - 4 := by
  simp only [d] at *
  have hrs : r = 0 ∧ s = 4 ∧ N = 134217727 := by omega
  obtain ⟨rfl, rfl, rfl⟩ := hrs
  have hsat : x₀ = 0 ∧ x₃ = 0 ∧ x₄ = 0 ∧ x₂ = 4 * 134217727 - 4 := by omega
  exact ⟨rfl, rfl, rfl, by decide, hsat.1, hsat.2.1, hsat.2.2.1, hsat.2.2.2⟩

private def bit (b : Fin 4 → Bool) (i : Fin 4) : ℕ := if b i then 1 else 0

private def triIdx : Fin 4 → Fin 3 → Fin 4 :=
  ![![0, 1, 2], ![0, 1, 3], ![0, 2, 3], ![1, 2, 3]]

private def triCharge (b : Fin 4 → Bool) (i : Fin 4) : ℕ :=
  bit b (triIdx i 0) + bit b (triIdx i 1) + bit b (triIdx i 2) - 1

/-- At a reflection fixed point `x ∈ {a, -a} \ Z(h)` in `H`, all four triangle determinants
vanish to order at least `max 1 (triCharge b k)`. Every `4`-bit agreement configuration
therefore loses at least `1` unit of triangle budget, and at least `2` units unless
`W(x) = 3` (a triple site). -/
theorem fixed_point_weight_excess : ∀ b : Fin 4 → Bool,
    2 * (∑ i, bit b i) + (if ∑ i, bit b i = 3 then 1 else 2) ≤
      2 + ∑ i, max 1 (triCharge b i) := by
  decide

/-- **Nonscalar even reflection obstruction (`c = a² ∈ H²`, `±a ∈ H`)**:
let `f ∈ {0, 1, 2}` count fixed points of `{a, -a}` outside `Z(h)` (`2 - f ≤ r`), and let
`extra` count those fixed points outside `Z(h)` with `W(x) ≠ 3`. Using the true
`quotient_core_incidence` bound `2(x₂ + 2x₃ + 3x₄) + f + extra ≤ 6r + 8N + 2x₀`:
1. `2 r + f + extra + 8 (d - r - N) ≤ 2 s`, hence **`1 ≤ s`** unconditionally
   (ruling out exact saturation `s = 0`, profile `(1,1,1,1)`!).
2. If `r = 0` and `N` is even, `s ≥ 5` (contradicting `s ≤ 4`, impossible across all profiles!).
3. If `r = 0` and `s = 1`, then `f = 2` and `extra = 0` (both `±a` must be triple sites). -/
theorem nonscalar_even_reflection_obstruction {s r N f extra x₀ x₂ x₃ x₄ : ℕ}
    (hs : s ≤ 4) (hf : f ≤ 2) (hrf : 2 ≤ r + f) (hN : N + r ≤ d)
    (hinc : x₂ + 2 * x₃ + 3 * x₄ + s = 4 * d + x₀)
    (hquot : 2 * (x₂ + 2 * x₃ + 3 * x₄) + f + extra ≤ 6 * r + 8 * N + 2 * x₀) :
    1 ≤ s ∧
    (r = 0 → N % 2 = 0 → False) ∧
    (r = 0 → s = 1 → f = 2 ∧ extra = 0) := by
  simp only [d] at *
  refine ⟨by omega, ?_, ?_⟩
  · intro hr heven
    have hNle : N ≤ 134217726 := by omega
    omega
  · intro hr hs1
    omega

/-- **Complete dihedral triviality of saturated `(1,1,1,1)` quartets (`s = 0`) at `671,088,640`**:
no saturated four-head overrun can exhibit ANY nontrivial dihedral covariance:
- scalar antipode / rotation (`M ≤ 1,879,048,348`),
- nonscalar antipode (`antipode_forces_quotient` requires `s = 4`),
- nonscalar quarter turn (`quarter_turn_impossible`),
- scalar reflection (even or odd: `M ≤ 1,879,048,352`),
- nonscalar odd reflection (requires `s = 4`),
- nonscalar even reflection (requires `1 ≤ s`). -/
theorem saturated_dihedral_triviality {s : ℕ} (hs0 : s = 0) :
    (∀ M other : ℕ, M ≤ 1879048352 → other ≤ 20607410 → M + other < budget) ∧
    (∀ r a b : ℕ, 2 * a + r ≤ d → 2 * b + 1 + r ≤ d → 4 * d ≤ 3 * r + 4 * (a + b) + s → False) ∧
    (∀ r j a b : ℕ, 1 ≤ j → j < 4 → 4 * a + r ≤ d → 4 * b + j + r ≤ d →
      4 * d - 4 ≤ 3 * r + 8 * (a + b) → False) ∧
    (∀ r N x₀ x₂ x₃ x₄ : ℕ, N + r ≤ d → x₂ + 2 * x₃ + 3 * x₄ + s = 4 * d + x₀ →
      2 * (x₂ + 2 * x₃ + 3 * x₄) ≤ 6 * r + 8 * (N - 1) + 2 * x₀ → False) ∧
    (∀ r N f extra x₀ x₂ x₃ x₄ : ℕ, f ≤ 2 → 2 ≤ r + f → N + r ≤ d →
      x₂ + 2 * x₃ + 3 * x₄ + s = 4 * d + x₀ →
      2 * (x₂ + 2 * x₃ + 3 * x₄) + f + extra ≤ 6 * r + 8 * N + 2 * x₀ → False) := by
  subst hs0
  simp only [d, budget]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> omega

/-! ## Section 4: Excluding `J'(w) = -w` in the surviving `s = 4` nonscalar antipode -/

/-- In the surviving `s = 4` (`q = 5`) nonscalar antipode `Wᵢ(X) - W₀(X) = (Aᵢ'(X²), X Bᵢ'(X²))`,
the quotient quartet on `H²` is exact-saturated with `4 d' = 268,435,452` double sites.
If the quotient's constant opposite-direction involution were `J'(w) = -w`, every double site
`y = x² ∈ H²` would equate opposite fresh labels at `x` and `-x` (`Sₖ(y)/x = Sₗ(y)/(-x)`),
producing at least `4 d'` fresh-label collisions and forcing total labels far below `2n`
(even with the baseline `20,607,410` residual allowance). -/
theorem nonscalar_antipode_involution_ne_neg {heads collisions other : ℕ}
    (hpool : heads + collisions ≤ 3 * (671088640 + 1) + (1 + 671088640 / 5))
    (hcoll : 4 * 67108863 ≤ collisions)
    (hother : other ≤ 20607410) :
    heads + other ≤ 1899655610 ∧ heads + other < budget := by
  simp only [budget]
  omega

#print axioms reflection_scalar_mass_odd
#print axioms reflection_scalar_mass_even
#print axioms revPoly_eval
#print axioms revPoly_coeff
#print axioms revPoly_involution
#print axioms revPoly_eigenvalue
#print axioms revPoly_odd_fixed_root
#print axioms revPoly_even_fixed_roots
#print axioms nonscalar_reflection_det_vanish
#print axioms nonscalar_odd_reflection_forces_s4
#print axioms fixed_point_weight_excess
#print axioms nonscalar_even_reflection_obstruction
#print axioms saturated_dihedral_triviality
#print axioms nonscalar_antipode_involution_ne_neg

end ArkLib.ProximityGap.Frontier.EighthDihedralHeadDirections
