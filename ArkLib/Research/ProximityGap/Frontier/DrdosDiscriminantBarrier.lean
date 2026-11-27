/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Tactic

/-!
# Prime-Field `d = 1` Local Contact Equations, Discriminant Hit, Wronskian, and Farkas Engine

This module formalizes the characteristic-free algebraic core and linear-programming verifier of
the Stage 3–4 prime-field `d = 1` beyond-Johnson list decoding engine (`#142`/`#150`):

1. **Characteristic-Free Local Contact Equations (`local_contact_vanishing_equations`)**:
   Over ANY commutative ring `R`, if `f = A(X, Y₀) Y₁ + B(X, Y₀)` has local `(T, E)`-contact
   order at least `k` at `(x₀, y₀)` under `X = x₀ + T, Y₀ = y₀ + T (Y₁ + E)`, then using ONLY
   `E^0` and `E^1` (determinant `(q + 1) - q = 1`), we prove unconditionally:
   - `biMultGE x₀ y₀ A (k - 1)` and `biMultGE x₀ y₀ B (k - 1)`,
   - `b_{k - 1, 0} = 0`, `a_{0, k - 1} = 0`, and `a_{p, q} + b_{p - 1, q + 1} = 0` for all
     `p ≥ 1, p + q = k - 1`.
2. **Hungarian-Potential Sylvester Valuation Bound (`pow_dvd_resultant_of_potentials`)**:
   For any prime-free/general divisibility parameter `π` in a commutative ring `R` and any
   integer potentials `u, v : Fin (m + n) → ℤ` bounded by the entrywise `π`-valuations of
   `sylvester f g m n`, `π ^ (∑ u + ∑ v) ∣ resultant f g m n`. This immediately yields BOTH
   `psi_true(k, da, db)` for `Res_{Y₀}(A, B)` and `psi_discA(k, d₁)` for `Disc_{Y₀}(A₁)`!
3. **The `a_{0, k - 1} = 0` Discriminant Factor Inheritance (`biMult_and_pureY_of_unit_factor`)**:
   Factoring `A = U * A₁` where `U(x₀, y₀) ≠ 0` (e.g. `U = a_uni * ∏ G_r^r` at a tight node with
   `u_i = m_i = 0`), `A₁` inherits BOTH `biMultGE x₀ y₀ A₁ (k - 1)` AND the pure-`Y₀` vanishing
   `((shiftBi x₀ y₀ A₁).coeff (k - 1)).coeff 0 = 0`, forcing `X ^ psi_discA(k, d₁) ∣ Disc_{Y₀}(A₁)`.
4. **Stage 3 Linear ODE Wronskian Rigidity (`wronskian_linear_ode_list_cap`)**:
   Over any field `K` of characteristic `0` or `> w`, any linear first-order ODE
   `A(X) Y₁ + B₁(X) Y₀ + B₀(X) = 0` (`A ≠ 0`) has at most a 1-dimensional affine space of degree
   `≤ w` polynomial solutions, capping the codeword list at `S.card * (A - w) ≤ n - w` (`≤ 5`
   across all four prize rates!).
5. **Truncated Cauchy–Schwarz Uniform Coverage (`truncated_cauchy_schwarz_coverage`)**:
   Exact division-free finite-`L` variance and Cauchy–Schwarz bound for agreement densities `d_i`
   against any bounded node weight `0 ≤ v_i ≤ M_cap`.
6. **General Rational Multi-`(m, s)` Farkas + Pigeonhole Verifier (`exists_active_ms_of_farkas`)**:
   100% general linear-algebraic Farkas certification theorem over `ℚ` across an interval
   `c ∈ [cLo, cHi]` with tail slack `T_tail ≥ 0`.
-/

set_option autoImplicit false

open Finset Matrix Polynomial BigOperators

namespace ArkLib.ProximityGap.Frontier.DrdosDiscriminantBarrier

/-! ### Part 1: Bivariate Shift and Characteristic-Free Local Contact Equations -/

/-- Bivariate polynomials `R[X][Y₀]`. -/
abbrev BiPoly (R : Type*) [CommRing R] := Polynomial (Polynomial R)

/-- Shift `(X, Y₀) ↦ (x₀ + T, y₀ + Z)` on `BiPoly R = R[X][Y₀]`. -/
noncomputable def shiftBi {R : Type*} [CommRing R] (x₀ y₀ : R) (f : BiPoly R) : BiPoly R :=
  (f.map (Polynomial.compRingHom (Polynomial.C x₀ + Polynomial.X))).comp
    (Polynomial.C (Polynomial.C y₀) + Polynomial.X)

lemma shiftBi_add {R : Type*} [CommRing R] (x₀ y₀ : R) (f g : BiPoly R) :
    shiftBi x₀ y₀ (f + g) = shiftBi x₀ y₀ f + shiftBi x₀ y₀ g := by
  unfold shiftBi
  simp [Polynomial.map_add, Polynomial.add_comp]

lemma shiftBi_mul {R : Type*} [CommRing R] (x₀ y₀ : R) (f g : BiPoly R) :
    shiftBi x₀ y₀ (f * g) = shiftBi x₀ y₀ f * shiftBi x₀ y₀ g := by
  unfold shiftBi
  simp [Polynomial.map_mul, Polynomial.mul_comp]

/-- The `(p, q)`-th shifted coefficient `coeff_T^p (coeff_Z^q (shiftBi x₀ y₀ f))`. -/
noncomputable def shiftCoeff {R : Type*} [CommRing R] (x₀ y₀ : R) (f : BiPoly R) (p q : ℕ) : R :=
  ((shiftBi x₀ y₀ f).coeff q).coeff p

/-- Total 2D multiplicity at `(x₀, y₀)` is at least `m`: `shiftCoeff x₀ y₀ f p q = 0` for all
`p + q < m`. -/
def biMultGE {R : Type*} [CommRing R] (x₀ y₀ : R) (f : BiPoly R) (m : ℕ) : Prop :=
  ∀ p q, p + q < m → shiftCoeff x₀ y₀ f p q = 0

/-- The `(T^u, E^v, Y₁^w)` coefficient of `f(x₀ + T, y₀ + T(Y₁ + E), Y₁)` for
`f = A(X, Y₀) Y₁ + B(X, Y₀)`.
Under `Z = T (Y₁ + E)`:
- `a_{p, q} T^p Z^q Y₁ = a_{p, q} T^{p + q} ∑_v C(q, v) E^v Y₁^{q - v + 1}` contributes to
  `(u, v, w)` when `q = w + v - 1`, `p = u - q` (with `w ≥ 1` and `q ≤ u`);
- `b_{p, q} T^p Z^q = b_{p, q} T^{p + q} ∑_v C(q, v) E^v Y₁^{q - v}` contributes to
  `(u, v, w)` when `q = w + v`, `p = u - q` (with `q ≤ u`). -/
noncomputable def linearContactCoeff {R : Type*} [CommRing R]
    (x₀ y₀ : R) (A B : BiPoly R) (u v w : ℕ) : R :=
  (if 1 ≤ w ∧ w + v - 1 ≤ u then
      ((Nat.choose (w + v - 1) v : ℕ) : R) * shiftCoeff x₀ y₀ A (u - (w + v - 1)) (w + v - 1)
    else 0) +
  (if w + v ≤ u then
      ((Nat.choose (w + v) v : ℕ) : R) * shiftCoeff x₀ y₀ B (u - (w + v)) (w + v)
    else 0)

/-- Local `(T, E)`-contact vanishing of order at least `k` for `f = A(X, Y₀) Y₁ + B(X, Y₀)` at
`(x₀, y₀)`: all `(T^u E^v Y₁^w)` coefficients with `u + v < k` vanish. -/
def LinearLocalContactGE {R : Type*} [CommRing R]
    (x₀ y₀ : R) (A B : BiPoly R) (k : ℕ) : Prop :=
  ∀ u v w, u + v < k → linearContactCoeff x₀ y₀ A B u v w = 0

/-- **Characteristic-Free Local Contact Equations (`det [[1, 1], [q, q + 1]] = 1`).**
Over EVERY commutative ring `R` (zero characteristic assumption!), `LinearLocalContactGE x₀ y₀ A B k`
forces:
1. `biMultGE x₀ y₀ A (k - 1)` and `biMultGE x₀ y₀ B (k - 1)`,
2. Pure-`X` boundary vanishing `b_{u, 0} = 0` for all `u < k` (in particular `b_{k-1, 0} = 0`),
3. Pure-`Y₀` boundary vanishing `a_{0, u} = 0` for all `u < k` (in particular `a_{0, k-1} = 0`),
4. Exact diagonal pairing `a_{p, q} + b_{p - 1, q + 1} = 0` for all `p ≥ 1, p + q < k`. -/
theorem local_contact_vanishing_equations {R : Type*} [CommRing R]
    (x₀ y₀ : R) (A B : BiPoly R) (k : ℕ)
    (h : LinearLocalContactGE x₀ y₀ A B k) :
    biMultGE x₀ y₀ A (k - 1) ∧
    biMultGE x₀ y₀ B (k - 1) ∧
    (∀ u < k, shiftCoeff x₀ y₀ B u 0 = 0) ∧
    (∀ u < k, shiftCoeff x₀ y₀ A 0 u = 0) ∧
    (∀ p q, 1 ≤ p → p + q < k →
      shiftCoeff x₀ y₀ A p q + shiftCoeff x₀ y₀ B (p - 1) (q + 1) = 0) := by
  have hb0 : ∀ u < k, shiftCoeff x₀ y₀ B u 0 = 0 := by
    intro u hu
    have h0 := h u 0 0 (by omega)
    simpa [linearContactCoeff] using h0
  have ha0 : ∀ u < k, shiftCoeff x₀ y₀ A 0 u = 0 := by
    intro u hu
    have h0 := h u 0 (u + 1) (by omega)
    rw [linearContactCoeff, ite_eq_left_iff.mpr (fun hn => absurd (by omega) hn),
      ite_eq_right_iff.mpr (fun hp => absurd hp (by omega))] at h0
    simpa only [Nat.add_zero, Nat.add_sub_cancel, Nat.choose_zero_right, Nat.cast_one, one_mul,
      Nat.sub_self, add_zero] using h0
  have hpair : ∀ p q, 1 ≤ p → p + q < k →
      shiftCoeff x₀ y₀ A p q + shiftCoeff x₀ y₀ B (p - 1) (q + 1) = 0 := by
    intro p q hp hpq
    have h0 := h (p + q) 0 (q + 1) (by omega)
    rw [linearContactCoeff, ite_eq_left_iff.mpr (fun hn => absurd (by omega) hn),
      ite_eq_left_iff.mpr (fun hn => absurd (by omega) hn)] at h0
    have hs1 : p + q - (q + 1 + 0 - 1) = p := by omega
    have hs2 : p + q - (q + 1 + 0) = p - 1 := by omega
    have hq1 : q + 1 + 0 - 1 = q := by omega
    have hq2 : q + 1 + 0 = q + 1 := by omega
    rw [hs1, hs2, hq1, hq2, Nat.choose_zero_right, Nat.choose_zero_right, Nat.cast_one,
      one_mul, one_mul] at h0
    exact h0
  have hpair_zero : ∀ p q, 1 ≤ p → p + q < k - 1 →
      shiftCoeff x₀ y₀ A p q = 0 ∧ shiftCoeff x₀ y₀ B (p - 1) (q + 1) = 0 := by
    intro p q hp hpq
    have hsum := hpair p q hp (by omega)
    cases q with
    | zero =>
        have h1 := h p 1 0 (by omega)
        rw [linearContactCoeff, ite_eq_right_iff.mpr (fun hp' => absurd hp' (by omega)),
          ite_eq_left_iff.mpr (fun hn => absurd (by omega) hn)] at h1
        simp only [zero_add, Nat.choose_self, Nat.cast_one, one_mul] at h1
        have ha : shiftCoeff x₀ y₀ A p 0 = 0 := by
          rw [h1, add_zero] at hsum
          exact hsum
        exact ⟨ha, h1⟩
    | succ q' =>
        let q := q' + 1
        have h1 := h (p + q) 1 q (by omega)
        rw [linearContactCoeff, ite_eq_left_iff.mpr (fun hn => absurd (by omega) hn),
          ite_eq_left_iff.mpr (fun hn => absurd (by omega) hn)] at h1
        have hs1 : p + q - (q + 1 - 1) = p := by omega
        have hs2 : p + q - (q + 1) = p - 1 := by omega
        have hq1 : q + 1 - 1 = q := by omega
        rw [hs1, hs2, hq1, Nat.choose_one_right, Nat.choose_one_right] at h1
        have hb : shiftCoeff x₀ y₀ B (p - 1) (q + 1) = 0 := by
          have hmul : ((q : ℕ) : R) * (shiftCoeff x₀ y₀ A p q +
              shiftCoeff x₀ y₀ B (p - 1) (q + 1)) = 0 := by
            rw [hsum, mul_zero]
          push_cast at h1
          linear_combination h1 - hmul
        have ha : shiftCoeff x₀ y₀ A p q = 0 := by
          rw [hb, add_zero] at hsum
          exact hsum
        exact ⟨ha, hb⟩
  refine ⟨?_, ?_, hb0, ha0, hpair⟩
  · intro p q hpq
    cases p with
    | zero => exact ha0 q (by omega)
    | succ p' => exact (hpair_zero (p' + 1) q (by omega) hpq).1
  · intro p q hpq
    cases q with
    | zero => exact hb0 p (by omega)
    | succ q' =>
        have hz := (hpair_zero (p + 1) q' (by omega) (by omega)).2
        simpa using hz

/-! ### Part 2: Hungarian-Potential Sylvester Valuation Lower Bound (`Res(A, B)` & `Disc(A₁)`) -/

/-- **Universal Hungarian-Potential Sylvester Divisibility Theorem.**
Let `π : R` in any commutative ring `R`, and let `ordG : ℕ → ℕ`, `ordF : ℕ → ℕ` lower-bound
the `π`-valuations of the coefficients of `g` and `f` (`π ^ ordF k ∣ f.coeff k`,
`π ^ ordG k ∣ g.coeff k`).
If integer potentials `u, v : Fin (m + n) → ℤ` satisfy:
- for every left column `j : Fin m` and every `i : Fin (m + n)` with `j ≤ i ≤ j + n`:
  `u i + v (Fin.castAdd n j) ≤ ordG (i - j)`,
- for every right column `j : Fin n` and every `i : Fin (m + n)` with `j ≤ i ≤ j + m`:
  `u i + v (Fin.natAdd m j) ≤ ordF (i - j)`,
then for any `B : ℕ` with `(B : ℤ) ≤ ∑ i, u i + ∑ j, v j`, **`π ^ B ∣ Polynomial.resultant f g m n`**!

This proves BOTH `psi_true(k, da, db)` for `Res_{Y₀}(A, B)` AND `psi_discA(k, d₁)` for
`Disc_{Y₀}(A₁)` in one unified theorem! -/
theorem pow_dvd_resultant_of_potentials {R : Type*} [CommRing R] (π : R)
    (f g : R[X]) (m n B : ℕ) (ordF ordG : ℕ → ℕ)
    (hf : ∀ k ≤ m, π ^ ordF k ∣ f.coeff k)
    (hg : ∀ k ≤ n, π ^ ordG k ∣ g.coeff k)
    (u v : Fin (m + n) → ℤ)
    (hL : ∀ (i : Fin (m + n)) (j : Fin m), (j : ℕ) ≤ (i : ℕ) → (i : ℕ) ≤ (j : ℕ) + n →
      u i + v (Fin.castAdd n j) ≤ (ordG ((i : ℕ) - (j : ℕ)) : ℤ))
    (hR : ∀ (i : Fin (m + n)) (j : Fin n), (j : ℕ) ≤ (i : ℕ) → (i : ℕ) ≤ (j : ℕ) + m →
      u i + v (Fin.natAdd m j) ≤ (ordF ((i : ℕ) - (j : ℕ)) : ℤ))
    (hB : (B : ℤ) ≤ (∑ i : Fin (m + n), u i) + (∑ j : Fin (m + n), v j)) :
    π ^ B ∣ Polynomial.resultant f g m n := by
  classical
  rw [Polynomial.resultant, Matrix.det_apply]
  refine Finset.dvd_sum fun σ _ => ?_
  by_cases hzero : ∃ j : Fin (m + n), Polynomial.sylvester f g m n (σ j) j = 0
  · obtain ⟨j, hj⟩ := hzero
    have hprod : (∏ i : Fin (m + n), Polynomial.sylvester f g m n (σ i) i) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) hj
    rw [hprod, smul_zero]
    exact dvd_zero _
  · push Not at hzero
    -- For every column `j`, associate its exact coefficient valuation `w j`.
    let w : Fin (m + n) → ℕ := fun j =>
      j.addCases (fun j₁ => ordG ((σ (Fin.castAdd n j₁) : ℕ) - (j₁ : ℕ)))
                 (fun j₁ => ordF ((σ (Fin.natAdd m j₁) : ℕ) - (j₁ : ℕ)))
    have hcol : ∀ j : Fin (m + n),
        π ^ (w j) ∣ Polynomial.sylvester f g m n (σ j) j ∧
        u (σ j) + v j ≤ (w j : ℤ) := by
      intro j
      induction j using Fin.addCases with
      | left j₁ =>
          have hne := hzero (Fin.castAdd n j₁)
          simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left, Set.mem_Icc] at hne ⊢
          have hIcc : (j₁ : ℕ) ≤ (σ (Fin.castAdd n j₁) : ℕ) ∧
              (σ (Fin.castAdd n j₁) : ℕ) ≤ (j₁ : ℕ) + n := by
            by_contra hnot
            exact hne (by simp [hnot])
          simp only [hIcc, and_self, ite_true, w, Fin.addCases_left]
          exact ⟨hg _ (by omega), hL (σ (Fin.castAdd n j₁)) j₁ hIcc.1 hIcc.2⟩
      | right j₁ =>
          have hne := hzero (Fin.natAdd m j₁)
          simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right, Set.mem_Icc] at hne ⊢
          have hIcc : (j₁ : ℕ) ≤ (σ (Fin.natAdd m j₁) : ℕ) ∧
              (σ (Fin.natAdd m j₁) : ℕ) ≤ (j₁ : ℕ) + m := by
            by_contra hnot
            exact hne (by simp [hnot])
          simp only [hIcc, and_self, ite_true, w, Fin.addCases_right]
          exact ⟨hf _ (by omega), hR (σ (Fin.natAdd m j₁)) j₁ hIcc.1 hIcc.2⟩
    have hsumW : (B : ℤ) ≤ ((∑ j : Fin (m + n), w j : ℕ) : ℤ) := by
      calc
        (B : ℤ) ≤ (∑ i : Fin (m + n), u i) + (∑ j : Fin (m + n), v j) := hB
        _ = (∑ j : Fin (m + n), u (σ j)) + (∑ j : Fin (m + n), v j) := by
            rw [Equiv.sum_comp σ u]
        _ = ∑ j : Fin (m + n), (u (σ j) + v j) := (Finset.sum_add_distrib).symm
        _ ≤ ∑ j : Fin (m + n), (w j : ℤ) := Finset.sum_le_sum fun j _ => (hcol j).2
        _ = ((∑ j : Fin (m + n), w j : ℕ) : ℤ) := by simp
    have hB_le : B ≤ ∑ j : Fin (m + n), w j := Int.ofNat_le.mp hsumW
    have hdvd_prod : π ^ B ∣ ∏ j : Fin (m + n), Polynomial.sylvester f g m n (σ j) j := by
      refine (pow_dvd_pow π hB_le).trans ?_
      rw [← Finset.prod_pow_eq_pow_sum]
      exact Finset.prod_dvd_prod_of_dvd _ _ fun j _ => (hcol j).1
    obtain ⟨c, hc⟩ := hdvd_prod
    exact ⟨Equiv.Perm.sign σ • c, by rw [hc, mul_smul_comm]⟩

/-! ### Part 3: The `a_{0, k - 1} = 0` Discriminant Factor Inheritance Theorem -/

/-- **Local Multiplicity & Pure-`Y₀` Vanishing Inheritance under a Non-Vanishing Cofactor.**
Over any integral domain `R`, if `A = U * A₁` in `BiPoly R` and `U` does not vanish at `(x₀, y₀)`
(`shiftCoeff x₀ y₀ U 0 0 ≠ 0`), then:
1. `biMultGE x₀ y₀ A m → biMultGE x₀ y₀ A₁ m`,
2. If additionally `shiftCoeff x₀ y₀ A 0 m = 0`, then **`shiftCoeff x₀ y₀ A₁ 0 m = 0`**!

Applying this with `U = a_uni(X) * ∏_{r ≥ 2} G_r(X, Y₀)^r` at any tight node (`u_i = m_i = 0`)
proves that the squarefree part `A₁` inherits BOTH `biMultGE x₀ y₀ A₁ (k - 1)` AND
`a_{1; 0, k - 1} = 0`, directly feeding `pow_dvd_resultant_of_potentials` for `Disc_{Y₀}(A₁)`! -/
theorem biMult_and_pureY_of_unit_factor {R : Type*} [CommRing R] [IsDomain R]
    (x₀ y₀ : R) (U A₁ : BiPoly R) (m : ℕ)
    (hU0 : shiftCoeff x₀ y₀ U 0 0 ≠ 0)
    (hmult : biMultGE x₀ y₀ (U * A₁) m) :
    biMultGE x₀ y₀ A₁ m ∧
    (shiftCoeff x₀ y₀ (U * A₁) 0 m = 0 → shiftCoeff x₀ y₀ A₁ 0 m = 0) := by
  -- Helper: coefficient `(p, q)` of `shiftBi x₀ y₀ (U * A₁)` is a double antidiagonal sum.
  have hcoeff_mul : ∀ p q, shiftCoeff x₀ y₀ (U * A₁) p q =
      ∑ jq ∈ Finset.range (q + 1), ∑ ip ∈ Finset.range (p + 1),
        shiftCoeff x₀ y₀ U ip jq * shiftCoeff x₀ y₀ A₁ (p - ip) (q - jq) := by
    intro p q
    unfold shiftCoeff
    rw [shiftBi_mul, Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Polynomial.finsetSum_coeff]
    refine Finset.sum_congr rfl fun jq _ => ?_
    rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  -- Strong induction on `n = p + q` proving `shiftCoeff A₁ p q = 0` for all `p + q < m`.
  have hbi : ∀ n < m, ∀ p q, p + q = n → shiftCoeff x₀ y₀ A₁ p q = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn p q hpq
      have h0 := hmult p q (by omega)
      rw [hcoeff_mul] at h0
      -- Peel off the `(jq = 0, ip = 0)` term: every other term has `(p - ip) + (q - jq) < n`!
      rw [Finset.sum_range_succ', Finset.sum_range_succ'] at h0
      have hrest1 : ∑ x ∈ Finset.range q, ∑ ip ∈ Finset.range (p + 1),
          shiftCoeff x₀ y₀ U ip (x + 1) * shiftCoeff x₀ y₀ A₁ (p - ip) (q - (x + 1)) = 0 := by
        refine Finset.sum_eq_zero fun x hx => Finset.sum_eq_zero fun ip hip => ?_
        have hxq : x < q := Finset.mem_range.mp hx
        have hip' : ip ≤ p := Nat.lt_succ_iff.mp (Finset.mem_range.mp hip)
        have hlt : (p - ip) + (q - (x + 1)) < n := by omega
        rw [ih _ hlt (by omega) _ _ rfl, mul_zero]
      have hrest2 : ∑ x ∈ Finset.range p,
          shiftCoeff x₀ y₀ U (x + 1) 0 * shiftCoeff x₀ y₀ A₁ (p - (x + 1)) (q - 0) = 0 := by
        refine Finset.sum_eq_zero fun x hx => ?_
        have hxp : x < p := Finset.mem_range.mp hx
        have hlt : (p - (x + 1)) + (q - 0) < n := by omega
        rw [ih _ hlt (by omega) _ _ rfl, mul_zero]
      rw [hrest1, hrest2, zero_add, zero_add, Nat.sub_zero, Nat.sub_zero] at h0
      exact (mul_eq_zero.mp h0).resolve_left hU0
  refine ⟨fun p q hpq => hbi (p + q) hpq p q rfl, fun hpure => ?_⟩
  rw [hcoeff_mul] at hpure
  simp only [Nat.zero_add, Finset.sum_range_one, Nat.sub_zero] at hpure
  rw [Finset.sum_range_succ'] at hpure
  have hrest : ∑ x ∈ Finset.range m,
      shiftCoeff x₀ y₀ U 0 (x + 1) * shiftCoeff x₀ y₀ A₁ 0 (m - (x + 1)) = 0 := by
    refine Finset.sum_eq_zero fun x hx => ?_
    have hxm : x < m := Finset.mem_range.mp hx
    rw [hbi (m - (x + 1)) (by omega) 0 (m - (x + 1)) (by omega), mul_zero]
  rw [hrest, zero_add, Nat.sub_zero] at hpure
  exact (mul_eq_zero.mp hpure).resolve_left hU0

/-! ### Part 4: Stage 3 Linear ODE Wronskian Rigidity (`char = 0 ∨ w < char`) -/

/-- **Prime-Field Polynomial Wronskian Rigidity.**
Over any field `K` of characteristic `0` or strictly greater than `w`, if two nonzero polynomials
`H₁, H₂ ∈ K[X]` of degree at most `w` satisfy `H₁.derivative * H₂ = H₁ * H₂.derivative`, then
`H₂ = C c * H₁` for some scalar `c ∈ K`. -/
theorem wronskian_eq_zero_implies_scalar_mul {K : Type*} [Field K] {w : ℕ}
    (hchar : ringChar K = 0 ∨ w < ringChar K)
    {H₁ H₂ : K[X]} (hH₁ne : H₁ ≠ 0) (h1 : H₁.natDegree ≤ w) (h2 : H₂.natDegree ≤ w)
    (hW : H₁.derivative * H₂ = H₁ * H₂.derivative) :
    ∃ c : K, H₂ = Polynomial.C c * H₁ := by
  by_cases hH₂ : H₂ = 0
  · exact ⟨0, by simp [hH₂]⟩
  -- Helper: any nonzero `P, Q` of degree `≤ w` with `P' * Q = P * Q'` must have equal `natDegree`.
  have hdeg_eq : ∀ {P Q : K[X]}, P ≠ 0 → Q ≠ 0 → P.natDegree ≤ w → Q.natDegree ≤ w →
      P.derivative * Q = P * Q.derivative → P.natDegree = Q.natDegree := by
    intro P Q hP hQ hPw hQw hPQ
    -- Extract the coefficient of `X^(deg P + deg Q - 1)` when `deg P + deg Q ≥ 1`!
    by_cases h0 : P.natDegree = 0 ∧ Q.natDegree = 0
    · omega
    · have hpos : 0 < P.natDegree + Q.natDegree := by omega
      have hcoeff_deriv_mul : ∀ (A B : K[X]), 0 < A.natDegree + B.natDegree →
          (A.derivative * B).coeff (A.natDegree + B.natDegree - 1) =
            (A.natDegree : K) * A.leadingCoeff * B.leadingCoeff := by
        intro A B hAB
        rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
        by_cases hA0 : A.natDegree = 0
        · rw [Polynomial.eq_C_of_natDegree_eq_zero hA0]
          simp
        · have hidx : A.natDegree - 1 ∈ Finset.range (A.natDegree + B.natDegree - 1 + 1) := by
            rw [Finset.mem_range]; omega
          rw [Finset.sum_eq_single (A.natDegree - 1)]
          · have hsub : A.natDegree + B.natDegree - 1 - (A.natDegree - 1) = B.natDegree := by omega
            have hadd : A.natDegree - 1 + 1 = A.natDegree := by omega
            have hcastA : ((A.natDegree - 1 : ℕ) : K) + 1 = (A.natDegree : K) := by
              simpa [Nat.cast_add, Nat.cast_one] using congrArg (Nat.cast (R := K)) hadd
            rw [hsub, Polynomial.coeff_derivative, hadd, Polynomial.leadingCoeff,
              Polynomial.leadingCoeff]
            linear_combination A.coeff A.natDegree * B.coeff B.natDegree * hcastA
          · intro i hi hne
            have hi' : i ≤ A.natDegree + B.natDegree - 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
            by_cases hlt : i < A.natDegree - 1
            · have hgt : B.natDegree < A.natDegree + B.natDegree - 1 - i := by omega
              rw [Polynomial.coeff_eq_zero_of_natDegree_lt hgt, mul_zero]
            · have hgt : A.derivative.natDegree < i := by
                have := Polynomial.natDegree_derivative_le A
                omega
              rw [Polynomial.coeff_eq_zero_of_natDegree_lt hgt, zero_mul]
          · intro hnot; exact absurd hidx hnot
      have hLHS := hcoeff_deriv_mul P Q hpos
      have hRHS := hcoeff_deriv_mul Q P (by omega)
      have hcomm : (P * Q.derivative).coeff (P.natDegree + Q.natDegree - 1) =
          (Q.derivative * P).coeff (Q.natDegree + P.natDegree - 1) := by
        rw [mul_comm, Nat.add_comm]
      have heq := congrArg (fun R : K[X] => R.coeff (P.natDegree + Q.natDegree - 1)) hPQ
      rw [hLHS, hcomm, hRHS] at heq
      have hlc : P.leadingCoeff * Q.leadingCoeff ≠ 0 :=
        mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hP)
          (Polynomial.leadingCoeff_ne_zero.mpr hQ)
      have hcast : ((P.natDegree : ℕ) : K) = ((Q.natDegree : ℕ) : K) := by
        have hdiff : ((P.natDegree : K) - (Q.natDegree : K)) *
            (P.leadingCoeff * Q.leadingCoeff) = 0 := by
          linear_combination heq
        exact sub_eq_zero.mp ((mul_eq_zero.mp hdiff).resolve_right hlc)
      have hdiff_zero : ∀ a b : ℕ, a ≤ b → b ≤ w → ((a : ℕ) : K) = ((b : ℕ) : K) → a = b := by
        intro a b hab hbw hEq
        have hsub0 : (((b - a : ℕ) : ℕ) : K) = 0 := by
          rw [Nat.cast_sub hab, hEq, sub_self]
        have hdvd : ringChar K ∣ (b - a) := ringChar.dvd hsub0
        rcases hchar with hc0 | hcp
        · rw [hc0, zero_dvd_iff] at hdvd; omega
        · have h0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
          omega
      rcases le_total P.natDegree Q.natDegree with hle | hle
      · exact hdiff_zero P.natDegree Q.natDegree hle hQw hcast
      · exact (hdiff_zero Q.natDegree P.natDegree hle hPw hcast.symm).symm
  -- Take `c = H₂.leadingCoeff / H₁.leadingCoeff` and set `R = H₂ - C c * H₁`.
  have hdeg : H₁.natDegree = H₂.natDegree := hdeg_eq hH₁ne hH₂ h1 h2 hW
  let c : K := H₂.leadingCoeff / H₁.leadingCoeff
  let R : K[X] := H₂ - Polynomial.C c * H₁
  refine ⟨c, ?_⟩
  suffices hR0 : R = 0 by exact sub_eq_zero.mp hR0
  by_contra hRne
  have hRW : H₁.derivative * R = H₁ * R.derivative := by
    simp only [R, Polynomial.derivative_sub, Polynomial.derivative_mul, Polynomial.derivative_C,
      zero_mul, zero_add]
    linear_combination hW
  have hRdeg_lt : R.natDegree < H₁.natDegree := by
    -- Leading terms of `H₂` and `C c * H₁` cancel since `deg H₁ = deg H₂`!
    have hlc1 : H₁.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hH₁ne
    have hRle : R.natDegree ≤ H₁.natDegree := by
      refine (Polynomial.natDegree_sub_le _ _).trans (max_le (by omega) ?_)
      exact Polynomial.natDegree_mul_le.trans (by simp)
    refine lt_of_le_of_ne hRle fun hEq => ?_
    have hcoeff0 : R.coeff H₁.natDegree = 0 := by
      simp only [R, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
      rw [← Polynomial.leadingCoeff, hdeg, ← Polynomial.leadingCoeff]
      dsimp only [c]
      rw [div_mul_cancel₀ _ hlc1, sub_self]
    have hlcR : R.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hRne
    rw [Polynomial.leadingCoeff, hEq] at hlcR
    exact hlcR hcoeff0
  have hR_eq := hdeg_eq hH₁ne hRne h1 (by omega) hRW
  omega

/-- **Stage 3 Linear ODE List-Size Cap (`d_f = 1, b_f = 1`).**
Over any field `K` of characteristic `0` or `> w`, any finite set `S` of degree `≤ w` polynomials
agreeing with `y` on at least `A > w` sites of `dom : I ↪ K` and solving a nonzero linear ODE
`A₀(X) P'(X) + B₁(X) P(X) + B₀(X) = 0` satisfies `S.card * (A - w) ≤ Fintype.card I - w`
(at most `5` codewords across all four prize rates!). -/
theorem wronskian_linear_ode_list_cap {K I : Type*} [Field K] [Fintype I] [DecidableEq K]
    [DecidableEq I] {w A : ℕ}
    (dom : I ↪ K) (y : I → K) (A₀ B₁ B₀ : K[X]) (hA₀ : A₀ ≠ 0)
    (hchar : ringChar K = 0 ∨ w < ringChar K) (hwA : w < A)
    (S : Finset K[X])
    (hdeg : ∀ P ∈ S, P.natDegree ≤ w)
    (hagree : ∀ P ∈ S, A ≤ (Finset.univ.filter fun i => P.eval (dom i) = y i).card)
    (hODE : ∀ P ∈ S, A₀ * P.derivative + B₁ * P + B₀ = 0) :
    S.card * (A - w) ≤ Fintype.card I - w := by
  classical
  by_cases hS1 : S.card ≤ 1
  · rcases S.eq_empty_or_nonempty with rfl | ⟨P₀, hP₀⟩
    · simp
    · have hAn : A ≤ Fintype.card I := by
        calc
          A ≤ (Finset.univ.filter fun i => P₀.eval (dom i) = y i).card := hagree P₀ hP₀
          _ ≤ (Finset.univ : Finset I).card := Finset.card_le_card (Finset.filter_subset _ _)
          _ = Fintype.card I := Finset.card_univ
      calc
        S.card * (A - w) ≤ 1 * (A - w) := Nat.mul_le_mul_right _ hS1
        _ = A - w := one_mul _
        _ ≤ Fintype.card I - w := Nat.sub_le_sub_right hAn w
  · have h2 : 1 < S.card := by omega
    obtain ⟨P₁, hP₁, P₂, hP₂, hne⟩ := Finset.one_lt_card.mp h2
    let H₀ := P₂ - P₁
    have hH₀ne : H₀ ≠ 0 := sub_ne_zero.mpr hne.symm
    have hH₀deg : H₀.natDegree ≤ w :=
      (Polynomial.natDegree_sub_le _ _).trans (max_le (hdeg P₂ hP₂) (hdeg P₁ hP₁))
    have hH₀ode : A₀ * H₀.derivative + B₁ * H₀ = 0 := by
      have h1 := hODE P₁ hP₁
      have h2' := hODE P₂ hP₂
      simp only [H₀, Polynomial.derivative_sub]
      linear_combination h2' - h1
    -- Every `P ∈ S` is of the form `P₁ + C c * H₀`!
    have haff : ∀ P ∈ S, ∃ c : K, P = P₁ + Polynomial.C c * H₀ := by
      intro P hP
      let H := P - P₁
      have hHdeg : H.natDegree ≤ w :=
        (Polynomial.natDegree_sub_le _ _).trans (max_le (hdeg P hP) (hdeg P₁ hP₁))
      have hHode : A₀ * H.derivative + B₁ * H = 0 := by
        have h1 := hODE P₁ hP₁
        have hP' := hODE P hP
        simp only [H, Polynomial.derivative_sub]
        linear_combination hP' - h1
      have hW : H₀.derivative * H = H₀ * H.derivative := by
        have hmul : A₀ * (H₀.derivative * H - H₀ * H.derivative) = 0 := by
          linear_combination H * hH₀ode - H₀ * hHode
        exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left hA₀)
      obtain ⟨c, hc⟩ := wronskian_eq_zero_implies_scalar_mul hchar hH₀ne hH₀deg hHdeg hW
      exact ⟨c, by dsimp [H] at hc; linear_combination hc⟩
    -- Base set `B = {i | H₀(dom i) = 0}` has cardinality `≤ w`.
    let Bset : Finset I := Finset.univ.filter fun i => H₀.eval (dom i) = 0
    have hBcard : Bset.card ≤ w := by
      have hsub : Bset.image dom ⊆ H₀.roots.toFinset := by
        intro x hx
        rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hH₀ne, Polynomial.IsRoot]
        exact (Finset.mem_filter.mp hi).2
      calc
        Bset.card = (Bset.image dom).card := (Finset.card_image_of_injective _ dom.injective).symm
        _ ≤ H₀.roots.toFinset.card := Finset.card_le_card hsub
        _ ≤ H₀.roots.card := Multiset.toFinset_card_le _
        _ ≤ H₀.natDegree := Polynomial.card_roots' _
        _ ≤ w := hH₀deg
    have hfiber : ∀ i : I, i ∉ Bset → (S.filter fun P => P.eval (dom i) = y i).card ≤ 1 := by
      intro i hiB
      have hH₀eval : H₀.eval (dom i) ≠ 0 := by
        simpa [Bset] using hiB
      refine Finset.card_le_one.mpr fun P hP Q hQ => ?_
      rw [Finset.mem_filter] at hP hQ
      obtain ⟨cP, rfl⟩ := haff P hP.1
      obtain ⟨cQ, rfl⟩ := haff Q hQ.1
      have heq : (cP - cQ) * H₀.eval (dom i) = 0 := by
        have h1 := hP.2
        have h2' := hQ.2
        simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C] at h1 h2'
        linear_combination h1 - h2'
      have hc : cP = cQ := sub_eq_zero.mp ((mul_eq_zero.mp heq).resolve_right hH₀eval)
      rw [hc]
    -- Double-counting over `nonB = univ \ Bset` with fiber size `≤ 1`:
    let nonB : Finset I := Finset.univ \ Bset
    have hnonB_card : nonB.card = Fintype.card I - Bset.card := by
      simp [nonB, Finset.card_sdiff]
    have hlower : S.card * (A - Bset.card) ≤
        ∑ P ∈ S, (nonB.filter fun i => P.eval (dom i) = y i).card := by
      calc
        S.card * (A - Bset.card) = ∑ _P ∈ S, (A - Bset.card) := by simp
        _ ≤ ∑ P ∈ S, (nonB.filter fun i => P.eval (dom i) = y i).card := by
          refine Finset.sum_le_sum fun P hP => ?_
          have htot := hagree P hP
          have hsub : (Finset.univ.filter fun i => P.eval (dom i) = y i) ⊆
              (nonB.filter fun i => P.eval (dom i) = y i) ∪ Bset := by
            intro i hi
            by_cases hiB : i ∈ Bset
            · exact Finset.mem_union_right _ hiB
            · refine Finset.mem_union_left _ ?_
              rw [Finset.mem_filter] at hi ⊢
              exact ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hiB⟩, hi.2⟩
          have hsplit := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
          omega
    have hswap : (∑ P ∈ S, (nonB.filter fun i => P.eval (dom i) = y i).card) =
        ∑ i ∈ nonB, (S.filter fun P => P.eval (dom i) = y i).card := by
      simp only [Finset.card_filter]; exact Finset.sum_comm
    have hupper : (∑ i ∈ nonB, (S.filter fun P => P.eval (dom i) = y i).card) ≤
        Fintype.card I - Bset.card := by
      calc
        _ ≤ ∑ _i ∈ nonB, 1 := Finset.sum_le_sum fun i hi => hfiber i (Finset.mem_sdiff.mp hi).2
        _ = nonB.card := by simp
        _ = Fintype.card I - Bset.card := hnonB_card
    have hB := hlower.trans (hswap.le.trans hupper)
    have hAn : A ≤ Fintype.card I := by
      calc
        A ≤ (Finset.univ.filter fun i => P₁.eval (dom i) = y i).card := hagree P₁ hP₁
        _ ≤ (Finset.univ : Finset I).card := Finset.card_le_card (Finset.filter_subset _ _)
        _ = Fintype.card I := Finset.card_univ
    have hsub1 : S.card * (A - w) + S.card * (w - Bset.card) = S.card * (A - Bset.card) := by
      rw [← Nat.mul_add]; congr 1; omega
    have hsub2 : (Fintype.card I - w) + (w - Bset.card) = Fintype.card I - Bset.card := by omega
    have hdiff : w - Bset.card ≤ S.card * (w - Bset.card) :=
      Nat.le_mul_of_pos_left _ (by omega)
    omega

/-! ### Part 5: Truncated Cauchy–Schwarz Uniform Coverage Inequality -/

/-- **Exact Finite-`L` Agreement-Density Variance Bound.**
For any nonempty list `S` of `L = S.card ≥ 1` distinct polynomials of degree `≤ w` agreeing with
`y` on at least `A` sites each, the empirical agreement density `d_i = |{P ∈ S | P(dom i) = y i}| / L`
satisfies (whenever `1 ≤ 2 * α * L`):
  `∑ i, (d_i - α)² ≤ (n * α - w) / L + (w - n * α²)`! -/
theorem agreement_density_variance_le {K I : Type*} [Field K] [Fintype I] [DecidableEq K]
    [DecidableEq I] (dom : I ↪ K) (y : I → K) (w A : ℕ) (α : ℚ)
    (S : Finset K[X]) (hSne : S.Nonempty)
    (hdeg : ∀ P ∈ S, P.natDegree ≤ w)
    (hagree : ∀ P ∈ S, A ≤ (Finset.univ.filter fun i => P.eval (dom i) = y i).card)
    (hAα : (Fintype.card I : ℚ) * α ≤ (A : ℚ))
    (h2αL : (1 : ℚ) ≤ 2 * α * (S.card : ℚ)) :
    let L : ℚ := (S.card : ℚ)
    let d : I → ℚ := fun i => ((S.filter fun P => P.eval (dom i) = y i).card : ℚ) / L
    ∑ i : I, (d i - α) ^ 2 ≤
      (((Fintype.card I : ℚ) * α - (w : ℚ)) / L) + ((w : ℚ) - (Fintype.card I : ℚ) * α ^ 2) := by
  intro L d
  have hLpos : (0 : ℚ) < L := by dsimp only [L]; exact_mod_cast hSne.card_pos
  have hLne : L ≠ 0 := hLpos.ne'
  -- Step 1: `∑ i, d i ≥ A ≥ n * α`.
  have hsum1 : (Fintype.card I : ℚ) * α ≤ ∑ i : I, d i := by
    have hcount : S.card * A ≤ ∑ i : I, (S.filter fun P => P.eval (dom i) = y i).card := by
      calc
        S.card * A = ∑ _P ∈ S, A := by simp
        _ ≤ ∑ P ∈ S, (Finset.univ.filter fun i => P.eval (dom i) = y i).card :=
            Finset.sum_le_sum hagree
        _ = ∑ i : I, (S.filter fun P => P.eval (dom i) = y i).card := by
            simp only [Finset.card_filter]; exact Finset.sum_comm
    have hcountQ : L * (A : ℚ) ≤ ∑ i : I, ((S.filter fun P => P.eval (dom i) = y i).card : ℚ) := by
      dsimp only [L]
      have hcast : ((S.card * A : ℕ) : ℚ) ≤
          ((∑ i : I, (S.filter fun P => P.eval (dom i) = y i).card : ℕ) : ℚ) := by
        exact_mod_cast hcount
      simpa [Nat.cast_mul, Nat.cast_sum] using hcast
    have hdiv : (A : ℚ) ≤ ∑ i : I, d i := by
      rw [show (∑ i : I, d i) = (∑ i : I, ((S.filter fun P => P.eval (dom i) = y i).card : ℚ)) / L by
        simp only [d, Finset.sum_div]]
      exact (le_div_iff₀ hLpos).mpr (by linarith)
    exact hAα.trans hdiv
  -- Step 2: Double-counting pairs `(P, Q) ∈ S × S`: `∑ i, c_i^2 ≤ ∑ i, c_i + L * (L - 1) * w`.
  have hpair_overlap : ∀ P ∈ S, ∀ Q ∈ S, P ≠ Q →
      (Finset.univ.filter fun i => P.eval (dom i) = y i ∧ Q.eval (dom i) = y i).card ≤ w := by
    intro P hP Q hQ hne
    have hsub : (Finset.univ.filter fun i => P.eval (dom i) = y i ∧ Q.eval (dom i) = y i).image dom ⊆
        (P - Q).roots.toFinset := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
      rw [Finset.mem_filter] at hi
      rw [Multiset.mem_toFinset, Polynomial.mem_roots (sub_ne_zero.mpr hne), Polynomial.IsRoot,
        Polynomial.eval_sub, hi.2.1, hi.2.2, sub_self]
    have hdegPQ : (P - Q).natDegree ≤ w :=
      (Polynomial.natDegree_sub_le _ _).trans (max_le (hdeg P hP) (hdeg Q hQ))
    calc
      (Finset.univ.filter fun i => P.eval (dom i) = y i ∧ Q.eval (dom i) = y i).card
          = ((Finset.univ.filter fun i => P.eval (dom i) = y i ∧ Q.eval (dom i) = y i).image dom).card :=
            (Finset.card_image_of_injective _ dom.injective).symm
      _ ≤ (P - Q).roots.toFinset.card := Finset.card_le_card hsub
      _ ≤ (P - Q).roots.card := Multiset.toFinset_card_le _
      _ ≤ (P - Q).natDegree := Polynomial.card_roots' _
      _ ≤ w := hdegPQ
  have hsum2_nat : ∑ i : I, (S.filter fun P => P.eval (dom i) = y i).card ^ 2 ≤
      (∑ i : I, (S.filter fun P => P.eval (dom i) = y i).card) + S.card * (S.card - 1) * w := by
    have hsq : ∀ i : I, (S.filter fun P => P.eval (dom i) = y i).card ^ 2 =
        ∑ P ∈ S, ∑ Q ∈ S, if P.eval (dom i) = y i ∧ Q.eval (dom i) = y i then 1 else 0 := by
      intro i
      rw [sq, Finset.card_filter, Finset.sum_mul]
      refine Finset.sum_congr rfl fun P _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun Q _ => ?_
      split_ifs <;> simp_all
    simp_rw [hsq]
    rw [Finset.sum_comm]
    have hswap : (∑ P ∈ S, ∑ i : I, ∑ Q ∈ S,
        if P.eval (dom i) = y i ∧ Q.eval (dom i) = y i then 1 else 0) =
        ∑ P ∈ S, ∑ Q ∈ S,
          (Finset.univ.filter fun i => P.eval (dom i) = y i ∧ Q.eval (dom i) = y i).card := by
      refine Finset.sum_congr rfl fun P _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun Q _ => ?_
      rw [Finset.card_filter]
    rw [hswap]
    have hsplit : ∀ P ∈ S,
        (∑ Q ∈ S, (Finset.univ.filter fun i => P.eval (dom i) = y i ∧ Q.eval (dom i) = y i).card) ≤
        (Finset.univ.filter fun i => P.eval (dom i) = y i).card + (S.card - 1) * w := by
      intro P hP
      rw [← Finset.add_sum_erase _ _ hP]
      refine Nat.add_le_add ?_ ?_
      · refine le_of_eq (congrArg Finset.card ?_)
        ext i; simp
      · calc
          ∑ Q ∈ S.erase P, (Finset.univ.filter fun i => P.eval (dom i) = y i ∧ Q.eval (dom i) = y i).card
              ≤ ∑ _Q ∈ S.erase P, w :=
                Finset.sum_le_sum fun Q hQ =>
                  hpair_overlap P hP Q (Finset.mem_of_mem_erase hQ)
                    (Finset.ne_of_mem_erase hQ).symm
          _ = (S.erase P).card * w := by simp
          _ = (S.card - 1) * w := by rw [Finset.card_erase_of_mem hP]
    calc
      ∑ P ∈ S, ∑ Q ∈ S, (Finset.univ.filter fun i => P.eval (dom i) = y i ∧ Q.eval (dom i) = y i).card
          ≤ ∑ P ∈ S, ((Finset.univ.filter fun i => P.eval (dom i) = y i).card + (S.card - 1) * w) :=
            Finset.sum_le_sum hsplit
      _ = (∑ P ∈ S, (Finset.univ.filter fun i => P.eval (dom i) = y i).card) +
            S.card * ((S.card - 1) * w) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]
      _ = (∑ i : I, (S.filter fun P => P.eval (dom i) = y i).card) + S.card * (S.card - 1) * w := by
          congr 1
          · simp only [Finset.card_filter]; exact Finset.sum_comm
          · ring
  have hsum2 : ∑ i : I, (d i) ^ 2 ≤ (∑ i : I, d i) / L + ((L - 1) / L) * (w : ℚ) := by
    have hS1 : 1 ≤ S.card := hSne.card_pos
    have hQ : (∑ i : I, ((S.filter fun P => P.eval (dom i) = y i).card : ℚ) ^ 2) ≤
        (∑ i : I, ((S.filter fun P => P.eval (dom i) = y i).card : ℚ)) + L * (L - 1) * (w : ℚ) := by
      have hcast : ((∑ i : I, (S.filter fun P => P.eval (dom i) = y i).card ^ 2 : ℕ) : ℚ) ≤
          (((∑ i : I, (S.filter fun P => P.eval (dom i) = y i).card) +
            S.card * (S.card - 1) * w : ℕ) : ℚ) := by exact_mod_cast hsum2_nat
      simpa [L, Nat.cast_sub hS1] using hcast
    have hdivL2 : (∑ i : I, (d i) ^ 2) =
        (∑ i : I, ((S.filter fun P => P.eval (dom i) = y i).card : ℚ) ^ 2) / L ^ 2 := by
      simp only [d, div_pow, Finset.sum_div]
    rw [hdivL2]
    have hL2pos : (0 : ℚ) < L ^ 2 := sq_pos_of_pos hLpos
    rw [div_le_iff₀ hL2pos]
    have hsumD : (∑ i : I, d i) =
        (∑ i : I, ((S.filter fun P => P.eval (dom i) = y i).card : ℚ)) / L := by
      simp only [d, Finset.sum_div]
    rw [hsumD]
    have hrhs_gen : ∀ X : ℚ, (X / L / L + (L - 1) / L * (w : ℚ)) * L ^ 2 =
        X + L * (L - 1) * (w : ℚ) := by
      intro X
      field_simp [hLne]
    rw [hrhs_gen]
    exact hQ
  -- Step 3: Expand `∑ (d_i - α)² = ∑ d_i² - 2α ∑ d_i + n α²` and use `1/L - 2α ≤ 0`!
  have hexpand_gen : ∀ f : I → ℚ, ∑ i : I, (f i - α) ^ 2 =
      (∑ i : I, (f i) ^ 2) - 2 * α * (∑ i : I, f i) + (Fintype.card I : ℚ) * α ^ 2 := by
    intro f
    have hterm : ∀ i : I, (f i - α) ^ 2 = (f i) ^ 2 - 2 * α * f i + α ^ 2 := fun i => by ring
    simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hexpand_gen d]
  have hcoef : (1 / L - 2 * α) ≤ 0 := by
    rw [sub_nonpos, div_le_iff₀ hLpos]
    linarith
  have hmono : (1 / L - 2 * α) * (∑ i : I, d i) ≤ (1 / L - 2 * α) * ((Fintype.card I : ℚ) * α) :=
    mul_le_mul_of_nonpos_left hsum1 hcoef
  have hfinal : (1 / L - 2 * α) * ((Fintype.card I : ℚ) * α) +
      ((L - 1) / L) * (w : ℚ) + (Fintype.card I : ℚ) * α ^ 2 =
      (((Fintype.card I : ℚ) * α - (w : ℚ)) / L) + ((w : ℚ) - (Fintype.card I : ℚ) * α ^ 2) := by
    field_simp [hLne]
    ring
  have hrew : (∑ i : I, d i) / L - 2 * α * (∑ i : I, d i) = (1 / L - 2 * α) * (∑ i : I, d i) := by
    ring
  linarith

/-- **Truncated Cauchy–Schwarz Uniform Coverage Bound.**
For any node weights `v : I → ℚ` with `0 ≤ v i ≤ M_cap`, combining Cauchy–Schwarz with
`agreement_density_variance_le` bounds `(∑ i, (α - d_i) * v_i)²` directly by
`n * M_cap² * (((n * α - w) / L) + (w - n * α²))`. -/
theorem truncated_cauchy_schwarz_coverage {K I : Type*} [Field K] [Fintype I] [DecidableEq K]
    [DecidableEq I] (dom : I ↪ K) (y : I → K) (w A : ℕ) (α M_cap : ℚ)
    (S : Finset K[X]) (hSne : S.Nonempty)
    (hdeg : ∀ P ∈ S, P.natDegree ≤ w)
    (hagree : ∀ P ∈ S, A ≤ (Finset.univ.filter fun i => P.eval (dom i) = y i).card)
    (hAα : (Fintype.card I : ℚ) * α ≤ (A : ℚ))
    (h2αL : (1 : ℚ) ≤ 2 * α * (S.card : ℚ))
    (v : I → ℚ) (hv0 : ∀ i, 0 ≤ v i) (hvM : ∀ i, v i ≤ M_cap) :
    let L : ℚ := (S.card : ℚ)
    let d : I → ℚ := fun i => ((S.filter fun P => P.eval (dom i) = y i).card : ℚ) / L
    (∑ i : I, (α - d i) * v i) ^ 2 ≤
      ((Fintype.card I : ℚ) * M_cap ^ 2) *
        ((((Fintype.card I : ℚ) * α - (w : ℚ)) / L) + ((w : ℚ) - (Fintype.card I : ℚ) * α ^ 2)) := by
  intro L d
  have hcs : (∑ i : I, (α - d i) * v i) ^ 2 ≤
      (∑ i : I, (α - d i) ^ 2) * (∑ i : I, (v i) ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => α - d i) v
  have hsq_eq : ∑ i : I, (α - d i) ^ 2 = ∑ i : I, (d i - α) ^ 2 :=
    Finset.sum_congr rfl fun i _ => by ring
  have hvar := agreement_density_variance_le dom y w A α S hSne hdeg hagree hAα h2αL
  have hv2 : ∑ i : I, (v i) ^ 2 ≤ (Fintype.card I : ℚ) * M_cap ^ 2 := by
    calc
      ∑ i : I, (v i) ^ 2 ≤ ∑ _i : I, M_cap ^ 2 :=
        Finset.sum_le_sum fun i _ => sq_le_sq' (by linarith [hv0 i, hvM i]) (hvM i)
      _ = (Fintype.card I : ℚ) * M_cap ^ 2 := by simp
  have hvar_nonneg : 0 ≤ ∑ i : I, (d i - α) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hv2_nonneg : 0 ≤ ∑ i : I, (v i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  calc
    (∑ i : I, (α - d i) * v i) ^ 2 ≤ (∑ i : I, (d i - α) ^ 2) * (∑ i : I, (v i) ^ 2) := by
      rwa [← hsq_eq]
    _ ≤ ((((Fintype.card I : ℚ) * α - (w : ℚ)) / L) + ((w : ℚ) - (Fintype.card I : ℚ) * α ^ 2)) *
          ((Fintype.card I : ℚ) * M_cap ^ 2) :=
      mul_le_mul hvar hv2 hv2_nonneg (hvar_nonneg.trans hvar)
    _ = ((Fintype.card I : ℚ) * M_cap ^ 2) *
          ((((Fintype.card I : ℚ) * α - (w : ℚ)) / L) + ((w : ℚ) - (Fintype.card I : ℚ) * α ^ 2)) := by
      ring

/-! ### Part 6: General Rational Multi-`(m, s)` Farkas + Pigeonhole Verifier -/

/-- **General Rational Multi-`(m, s)` Farkas + Pigeonhole Verifier.**
Given any finite class distribution `μ : Fin P → ℚ` (`μ p ≥ 0, ∑ μ p = 1`), optional nonnegative
tail slack `T_tail ≥ 0`, parameter `c ∈ [cLo, cHi]`, linear upper-bound constraints `Amat, Atail,
B0, B1`, and candidate `(m_j, s_j)` objectives with weights `x j ≥ 0` and dual Farkas multipliers
`lam r ≥ 0, nu : ℚ`, checking the finite dual inequalities and the two interval endpoints
`c ∈ {cLo, cHi}` proves the existence of an active index `j : Fin J` with `0 < x j` and strict
quotient surplus `δ j < (V0 j + V1 j * c) - (∑ p, Cmat j p * μ p + Ctail j * T_tail)`! -/
theorem exists_active_ms_of_farkas {P R J : ℕ}
    (cLo cHi c : ℚ) (hlo : cLo ≤ c) (hhi : c ≤ cHi)
    (μ : Fin P → ℚ) (hμ0 : ∀ p, 0 ≤ μ p) (hμ1 : ∑ p : Fin P, μ p = 1)
    (T_tail : ℚ) (hT0 : 0 ≤ T_tail)
    (Amat : Fin R → Fin P → ℚ) (Atail B0 B1 : Fin R → ℚ)
    (hcon : ∀ r : Fin R, (∑ p : Fin P, Amat r p * μ p) + Atail r * T_tail ≤ B0 r + B1 r * c)
    (x : Fin J → ℚ) (hx0 : ∀ j, 0 ≤ x j)
    (V0 V1 δ Ctail : Fin J → ℚ) (Cmat : Fin J → Fin P → ℚ)
    (lam : Fin R → ℚ) (hlam0 : ∀ r, 0 ≤ lam r) (nu : ℚ)
    (hdual_p : ∀ p : Fin P, (∑ j : Fin J, x j * Cmat j p) ≤ nu + ∑ r : Fin R, lam r * Amat r p)
    (hdual_tail : (∑ j : Fin J, x j * Ctail j) ≤ ∑ r : Fin R, lam r * Atail r)
    (hend_lo : nu + (∑ r : Fin R, lam r * (B0 r + B1 r * cLo)) <
      ∑ j : Fin J, x j * (V0 j + V1 j * cLo - δ j))
    (hend_hi : nu + (∑ r : Fin R, lam r * (B0 r + B1 r * cHi)) <
      ∑ j : Fin J, x j * (V0 j + V1 j * cHi - δ j)) :
    ∃ j : Fin J, 0 < x j ∧
      δ j < (V0 j + V1 j * c) - ((∑ p : Fin P, Cmat j p * μ p) + Ctail j * T_tail) := by
  -- Step 1: Convex combination of `hend_lo` and `hend_hi` holds at `c ∈ [cLo, cHi]`.
  have hend_c : nu + (∑ r : Fin R, lam r * (B0 r + B1 r * c)) <
      ∑ j : Fin J, x j * (V0 j + V1 j * c - δ j) := by
    by_cases heq : cLo = cHi
    · have hcc : c = cLo := by linarith
      rwa [hcc]
    · have hlt : cLo < cHi := lt_of_le_of_ne (hlo.trans hhi) heq
      have hden : (0 : ℚ) < cHi - cLo := sub_pos.mpr hlt
      let t := (c - cLo) / (cHi - cLo)
      have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr hlo) hden.le
      have ht1 : 0 ≤ 1 - t := by
        have : t ≤ 1 := (div_le_one hden).mpr (sub_le_sub_right hhi cLo)
        linarith
      have hc : c = (1 - t) * cLo + t * cHi := by
        dsimp [t]; field_simp [hden.ne']; ring
      have hcomb : (1 - t) * (nu + ∑ r : Fin R, lam r * (B0 r + B1 r * cLo)) +
          t * (nu + ∑ r : Fin R, lam r * (B0 r + B1 r * cHi)) <
          (1 - t) * (∑ j : Fin J, x j * (V0 j + V1 j * cLo - δ j)) +
          t * (∑ j : Fin J, x j * (V0 j + V1 j * cHi - δ j)) := by
        by_cases htpos : 0 < t
        · exact add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left hend_lo.le ht1)
            (mul_lt_mul_of_pos_left hend_hi htpos)
        · have ht_zero : t = 0 := le_antisymm (not_lt.mp htpos) ht0
          rw [ht_zero]; linarith
      have hlhs : nu + ∑ r : Fin R, lam r * (B0 r + B1 r * c) =
          (1 - t) * (nu + ∑ r : Fin R, lam r * (B0 r + B1 r * cLo)) +
          t * (nu + ∑ r : Fin R, lam r * (B0 r + B1 r * cHi)) := by
        rw [hc, mul_add, mul_add, Finset.mul_sum, Finset.mul_sum]
        have hsum : (∑ r : Fin R, (1 - t) * (lam r * (B0 r + B1 r * cLo))) +
            (∑ r : Fin R, t * (lam r * (B0 r + B1 r * cHi))) =
            ∑ r : Fin R, lam r * (B0 r + B1 r * ((1 - t) * cLo + t * cHi)) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun r _ => by ring
        linarith
      have hrhs : ∑ j : Fin J, x j * (V0 j + V1 j * c - δ j) =
          (1 - t) * (∑ j : Fin J, x j * (V0 j + V1 j * cLo - δ j)) +
          t * (∑ j : Fin J, x j * (V0 j + V1 j * cHi - δ j)) := by
        rw [hc, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => by ring
      linarith
  -- Step 2: Primal-dual bound `∑_j x_j * cost_j ≤ nu + ∑_r lam_r * (B0_r + B1_r * c)`.
  have hprimal_dual : (∑ j : Fin J, x j * ((∑ p : Fin P, Cmat j p * μ p) + Ctail j * T_tail)) ≤
      nu + ∑ r : Fin R, lam r * (B0 r + B1 r * c) := by
    have h1 : (∑ j : Fin J, x j * ((∑ p : Fin P, Cmat j p * μ p) + Ctail j * T_tail)) =
        (∑ p : Fin P, μ p * (∑ j : Fin J, x j * Cmat j p)) +
        T_tail * (∑ j : Fin J, x j * Ctail j) := by
      simp_rw [mul_add, Finset.sum_add_distrib]
      congr 1
      · simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun j _ => by ring
      · rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
    have h2 : (∑ p : Fin P, μ p * (∑ j : Fin J, x j * Cmat j p)) ≤
        ∑ p : Fin P, μ p * (nu + ∑ r : Fin R, lam r * Amat r p) :=
      Finset.sum_le_sum fun p _ => mul_le_mul_of_nonneg_left (hdual_p p) (hμ0 p)
    have h3 : T_tail * (∑ j : Fin J, x j * Ctail j) ≤
        T_tail * (∑ r : Fin R, lam r * Atail r) :=
      mul_le_mul_of_nonneg_left hdual_tail hT0
    have h4 : (∑ p : Fin P, μ p * (nu + ∑ r : Fin R, lam r * Amat r p)) +
        T_tail * (∑ r : Fin R, lam r * Atail r) =
        nu + ∑ r : Fin R, lam r * ((∑ p : Fin P, Amat r p * μ p) + Atail r * T_tail) := by
      calc
        (∑ p : Fin P, μ p * (nu + ∑ r : Fin R, lam r * Amat r p)) +
            T_tail * (∑ r : Fin R, lam r * Atail r)
            = (∑ p : Fin P, μ p * nu) + (∑ p : Fin P, μ p * ∑ r : Fin R, lam r * Amat r p) +
              (∑ r : Fin R, T_tail * (lam r * Atail r)) := by
              simp_rw [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
        _ = nu + ((∑ r : Fin R, ∑ p : Fin P, μ p * (lam r * Amat r p)) +
              (∑ r : Fin R, T_tail * (lam r * Atail r))) := by
              rw [← Finset.sum_mul, hμ1, one_mul, add_assoc]
              congr 1; congr 1
              simp_rw [Finset.mul_sum]
              exact Finset.sum_comm
        _ = nu + ∑ r : Fin R, lam r * ((∑ p : Fin P, Amat r p * μ p) + Atail r * T_tail) := by
              congr 1
              rw [← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl fun r _ => ?_
              rw [mul_add, Finset.mul_sum]
              congr 1
              · refine Finset.sum_congr rfl fun p _ => by ring
              · ring
    have h5 : ∑ r : Fin R, lam r * ((∑ p : Fin P, Amat r p * μ p) + Atail r * T_tail) ≤
        ∑ r : Fin R, lam r * (B0 r + B1 r * c) :=
      Finset.sum_le_sum fun r _ => mul_le_mul_of_nonneg_left (hcon r) (hlam0 r)
    linarith
  -- Step 3: Pigeonhole on `∑_j x_j * (V_j - cost_j - δ_j) > 0`.
  have hpos_sum : 0 < ∑ j : Fin J,
      x j * ((V0 j + V1 j * c) - ((∑ p : Fin P, Cmat j p * μ p) + Ctail j * T_tail) - δ j) := by
    have hrew : (∑ j : Fin J,
        x j * ((V0 j + V1 j * c) - ((∑ p : Fin P, Cmat j p * μ p) + Ctail j * T_tail) - δ j)) =
        (∑ j : Fin J, x j * (V0 j + V1 j * c - δ j)) -
        (∑ j : Fin J, x j * ((∑ p : Fin P, Cmat j p * μ p) + Ctail j * T_tail)) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => by ring
    linarith
  by_contra hnone
  push Not at hnone
  have hnonpos : ∑ j : Fin J,
      x j * ((V0 j + V1 j * c) - ((∑ p : Fin P, Cmat j p * μ p) + Ctail j * T_tail) - δ j) ≤ 0 := by
    refine Finset.sum_nonpos fun j _ => ?_
    by_cases hxj : 0 < x j
    · exact mul_nonpos_of_nonneg_of_nonpos hxj.le (sub_nonpos.mpr (hnone j hxj))
    · have hx0' : x j = 0 := le_antisymm (not_lt.mp hxj) (hx0 j)
      rw [hx0', zero_mul]
  linarith

#print axioms local_contact_vanishing_equations
#print axioms pow_dvd_resultant_of_potentials
#print axioms biMult_and_pureY_of_unit_factor
#print axioms wronskian_eq_zero_implies_scalar_mul
#print axioms wronskian_linear_ode_list_cap
#print axioms agreement_density_variance_le
#print axioms truncated_cauchy_schwarz_coverage
#print axioms exists_active_ms_of_farkas

end ArkLib.ProximityGap.Frontier.DrdosDiscriminantBarrier
