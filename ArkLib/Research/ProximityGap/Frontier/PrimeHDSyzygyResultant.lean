/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Tactic

/-!
# Characteristic-Free Syzygy Resultant, `T^{k - d_B} ∣ A_{k - 1}`, & Reduced Discriminant Matrix (`PrimeHDSyzygyResultant`)

Formalizes the three characteristic-free ring-level theorems from `#251` / `#254` (shared
foundation for `@mca-pivot-breaker`'s `p2` Half-Rate Johnson Pivot `314,491,699` closure and
`@drdos-engine` / `@upstream-forks`'s beyond-Johnson Rate-1/2 list-decoding closure):

1. **Syzygy Resultant Theorem (`resultant_syzygy_eq`, `pow_dvd_lc_mul_resultant_of_syzygy`,
   `pow_dvd_lc_mul_resultant_linear_of_syzygy`):**
   Over ANY commutative ring `R`, for `A = P * Q`, `B`, `t : R`, and `C = C t * B + U * A`:
   ```text
   Polynomial.resultant P C dP dC = P.coeff dP ^ (dC - dB) * t ^ dP * Polynomial.resultant P B dP dB
   ```
   Hence over any integral domain `R` with nonzero `t`, if `P` has `t`-multiplicity `mP` and
   `C` has `t`-multiplicity `mC` (e.g. `mC = k + 1` at any order-`k` contact node!), then
   `t ^ (resOrdExact dP mP dC mC - dP) ∣ P.coeff dP ^ (dC - dB) * Polynomial.resultant P B dP dB`.
   In particular, for ANY linear factor `G ∣ A` (`dG = 1`, `mG = 1`, `mC = k + 1`), this boosts the
   resultant valuation of `(G, B)` from `k - 1` to **`k`**!
2. **Contact-Order Syzygy & `T^{k - d_B} ∣ A_{k - 1}` (`ContactOrderGE`, `biMultGE_syzygy_of_contactOrderGE`,
   `coeff_A_eq_zero_of_ge_degB`, `slack_of_degB_eq_zero`, `pow_dvd_discr_of_extra_vanishing`):**
   At any `(T, U)`-order-`k` contact node (`k ≥ 1`) with `B.natDegree ≤ dB`:
   - `C = C X * B + Y * A` automatically satisfies `biMultGE C (k + 1)`,
   - `(A.coeff s).coeff (k - 1 - s) = 0` for EVERY `dB ≤ s ≤ k - 1` (forcing `T^{k - dB} ∣ A_{k - 1}`,
     and forcing every `k ≥ 2` node to be slack whenever `dB = 0`!),
   - Universal extra-vanishing discriminant theorem (over EVERY commutative ring `R`, zero division):
     if `1 ≤ dB ≤ m < d = A.natDegree`, `∀ j, t ^ (m - j) ∣ A.coeff j`, and
     `∀ j, dB ≤ j → j ≤ m → t ^ (m + 1 - j) ∣ A.coeff j`, then
     `t ^ (m * (m - 1) + (m - dB + 1)) ∣ A.discr` — in particular giving the `#251` boosts
     `(d = 4, dB = 2, m = 3) ⇒ t^8 ∣ A.discr` (`7 → 8`) and
     `(d = 6, dB = 3, m = 5) ⇒ t^23 ∣ A.discr` (`21 → 23`)!
3. **Reduced `(2d - 2) × (2d - 2)` Discriminant Matrix `M_disc(P)` & Exact Weighted Degree Bound
   (`reducedDiscMatrix`, `discr_eq_sign_mul_det_reducedDiscMatrix`,
   `natDegree_discr_le_of_biWeightedDeg`):**
   Eliminating the bottom row of `P.sylvesterDeriv` by subtracting `d` times column `d - 2` from
   column `2d - 2` yields the exact `(2d - 2) × (2d - 2)` matrix `M_disc(P)` with zero division by
   `lc(P)`:
   - `P.discr = (-1) ^ (d * (d - 1) / 2 + d) * (reducedDiscMatrix P).det`,
   - and for any `P : BiPoly R` (`2 ≤ d = P.natDegree`) with `(1, w)`-weighted degree `≤ W`
     (`∀ j, (P.coeff j).natDegree + w * j ≤ W`),
     `P.discr.natDegree ≤ (2 * d - 2) * W - w * d * (d - 1)`!
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace ArkLib.ProximityGap.Frontier.PrimeHDSyzygyResultant

open Polynomial Matrix
open scoped BigOperators

/-! ### Part 1: Universal Matrix Dual-Potential Engine & Syzygy Resultant Theorem (`#251` Thm 1) -/

section SyzygyResultant

/-- Universal dual-potential divisibility theorem for determinants over ANY commutative ring `R`. -/
theorem pow_dvd_det_of_potential {R : Type*} [CommRing R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (t : R)
    (p q : Fin n → ℤ) (N : ℕ)
    (hsum : (N : ℤ) ≤ ∑ i : Fin n, p i + ∑ j : Fin n, q j)
    (hentry : ∀ i j : Fin n, M i j = 0 ∨ t ^ (p i + q j).toNat ∣ M i j) :
    t ^ N ∣ M.det := by
  rw [Matrix.det_apply]
  apply Finset.dvd_sum
  intro σ _
  rw [Units.smul_def, zsmul_eq_mul]
  apply dvd_mul_of_dvd_right
  by_cases hzero : ∃ i : Fin n, M (σ i) i = 0
  · obtain ⟨i, hi⟩ := hzero
    rw [Finset.prod_eq_zero (f := fun j => M (σ j) j) (Finset.mem_univ i) hi]
    exact dvd_zero _
  · push Not at hzero
    have hdvd_prod :
        (∏ i : Fin n, t ^ (p (σ i) + q i).toNat) ∣ ∏ i : Fin n, M (σ i) i :=
      Finset.prod_dvd_prod_of_dvd _ _ fun i _ =>
        (hentry (σ i) i).resolve_left (hzero i)
    rw [Finset.prod_pow_eq_pow_sum] at hdvd_prod
    have hN_le : N ≤ ∑ i : Fin n, (p (σ i) + q i).toNat := by
      have hcast : (N : ℤ) ≤ ((∑ i : Fin n, (p (σ i) + q i).toNat : ℕ) : ℤ) := by
        calc (N : ℤ)
            ≤ ∑ i : Fin n, p i + ∑ j : Fin n, q j := hsum
          _ = ∑ i : Fin n, p (σ i) + ∑ i : Fin n, q i := by rw [Equiv.sum_comp σ p]
          _ = ∑ i : Fin n, (p (σ i) + q i) := (Finset.sum_add_distrib).symm
          _ ≤ ∑ i : Fin n, ((p (σ i) + q i).toNat : ℤ) :=
              Finset.sum_le_sum fun i _ => by omega
          _ = ((∑ i : Fin n, (p (σ i) + q i).toNat : ℕ) : ℤ) := by push_cast; rfl
      exact Int.ofNat_le.mp hcast
    exact (pow_dvd_pow t hN_le).trans hdvd_prod

/-- **Exact Ring-Level Syzygy Resultant Identity (`#251` Theorem 1):**
For ANY commutative ring `R`, `A = P * Q`, `B : R[X]`, `t : R`, and `dP, dB, dC : ℕ` with
`P.natDegree ≤ dP`, `B.natDegree ≤ dB ≤ dC`, and `(X * Q).natDegree + dP ≤ dC`:
```text
  Res_{dP, dC}(P, C t * B + X * (P * Q)) = P.coeff dP ^ (dC - dB) * t ^ dP * Res_{dP, dB}(P, B).
``` -/
theorem resultant_syzygy_eq {R : Type*} [CommRing R]
    (P Q B : R[X]) (t : R) (dP dB dC : ℕ)
    (hP : P.natDegree ≤ dP) (hB : B.natDegree ≤ dB) (hBC : dB ≤ dC)
    (hQ : (Polynomial.X * Q).natDegree + dP ≤ dC) :
    Polynomial.resultant P (Polynomial.C t * B + Polynomial.X * (P * Q)) dP dC =
      P.coeff dP ^ (dC - dB) * t ^ dP * Polynomial.resultant P B dP dB := by
  have h1 : Polynomial.C t * B + Polynomial.X * (P * Q) =
      Polynomial.C t * B + P * (Polynomial.X * Q) := by ring
  have hCtB : (Polynomial.C t * B).natDegree ≤ dB :=
    (Polynomial.natDegree_C_mul_le t B).trans hB
  rw [h1, Polynomial.resultant_add_mul_right P (Polynomial.C t * B) (Polynomial.X * Q) dP dC hQ hP]
  conv_lhs => rw [← Nat.add_sub_of_le hBC]
  rw [Polynomial.resultant_add_right_deg P (Polynomial.C t * B) dP dB (dC - dB) hCtB,
    Polynomial.resultant_C_mul_right, mul_assoc]

/-- Convenience form taking `A = P * Q` with `dP ≤ dC` and `A.natDegree + 1 ≤ dC` (over an integral
domain, so `Q.natDegree + 1 + dP ≤ dC` when `P.natDegree = dP` and `P ≠ 0`). -/
theorem resultant_syzygy_eq_of_dvd {R : Type*} [CommRing R] [IsDomain R]
    (A B P : R[X]) (t : R) (dP dB dC : ℕ)
    (hP_ne : P ≠ 0) (hP_deg : P.natDegree = dP) (hP_dvd : P ∣ A)
    (hB : B.natDegree ≤ dB) (hBC : dB ≤ dC) (hPC : dP ≤ dC) (hAC : A.natDegree + 1 ≤ dC) :
    Polynomial.resultant P (Polynomial.C t * B + Polynomial.X * A) dP dC =
      P.leadingCoeff ^ (dC - dB) * t ^ dP * Polynomial.resultant P B dP dB := by
  rcases hP_dvd with ⟨Q, rfl⟩
  have hQ : (Polynomial.X * Q).natDegree + dP ≤ dC := by
    by_cases hQ0 : Q = 0
    · subst hQ0; simp [hPC]
    · rw [Polynomial.natDegree_mul (Polynomial.X_ne_zero) hQ0, Polynomial.natDegree_X]
      have hPQ : (P * Q).natDegree = dP + Q.natDegree := by
        rw [Polynomial.natDegree_mul hP_ne hQ0, hP_deg]
      omega
  have h := resultant_syzygy_eq P Q B t dP dB dC (le_of_eq hP_deg) hB hBC hQ
  have hlc : P.coeff dP = P.leadingCoeff := by rw [← hP_deg, Polynomial.coeff_natDegree]
  rwa [hlc] at h

/-- Linear-regime resultant divisibility for general asymmetric `(dP, mP, dC, mC)` over ANY
commutative ring `R`: `t ^ (dC * mP + dP * mC - dP * dC) ∣ Polynomial.resultant P C dP dC`. -/
theorem pow_dvd_resultant_asym_linear {R : Type*} [CommRing R]
    (P C : R[X]) (dP mP dC mC : ℕ) (t : R)
    (hP : ∀ j, t ^ (mP - j) ∣ P.coeff j)
    (hC : ∀ j, t ^ (mC - j) ∣ C.coeff j) :
    t ^ (dC * mP + dP * mC - dP * dC) ∣ Polynomial.resultant P C dP dC := by
  by_cases hpos : dP * dC ≤ dC * mP + dP * mC
  · rw [Polynomial.resultant]
    let p : Fin (dP + dC) → ℤ := fun i => -(i.val : ℤ)
    let q : Fin (dP + dC) → ℤ := fun j =>
      (j.val : ℤ) + if j.val < dP then (mC : ℤ) else ((mP : ℤ) - dP)
    apply pow_dvd_det_of_potential (P.sylvester C dP dC) t p q
    · have hp_sum : ∑ i : Fin (dP + dC), p i = -(∑ i : Fin (dP + dC), (i.val : ℤ)) := by
        simp [p]
      have hq_sum : ∑ j : Fin (dP + dC), q j =
          (∑ j : Fin (dP + dC), (j.val : ℤ)) +
            ((dP : ℤ) * mC + (dC : ℤ) * ((mP : ℤ) - dP)) := by
        simp only [q, Finset.sum_add_distrib]
        congr 1
        rw [Fin.sum_univ_add]
        have hL : ∑ j : Fin dP,
            (if (Fin.castAdd dC j).val < dP then (mC : ℤ) else ((mP : ℤ) - dP)) =
            (dP : ℤ) * mC := by
          have hlt : ∀ j : Fin dP, (Fin.castAdd dC j).val < dP := fun j => j.isLt
          simp_rw [ite_eq_left (hlt _)]
          simp
        have hR : ∑ k : Fin dC,
            (if (Fin.natAdd dP k).val < dP then (mC : ℤ) else ((mP : ℤ) - dP)) =
            (dC : ℤ) * ((mP : ℤ) - dP) := by
          have hge : ∀ k : Fin dC, ¬ (Fin.natAdd dP k).val < dP := fun k => by dsimp; omega
          simp_rw [ite_eq_right (hge _)]
          simp [mul_sub]
        rw [hL, hR]
      rw [hp_sum, hq_sum]
      zify [hpos]
      linarith
    · intro i j
      rw [Polynomial.sylvester, Matrix.of_apply]
      by_cases hj : j.val < dP
      · have hjeq : j = Fin.castAdd dC ⟨j.val, hj⟩ := Fin.ext rfl
        by_cases hmem : i.val ∈ Set.Icc j.val (j.val + dC)
        · right
          have hval : (j.addCases
              (fun j₁ => if i.val ∈ Set.Icc (j₁ : ℕ) (j₁ + dC) then C.coeff (i - j₁) else 0)
              (fun j₁ => if i.val ∈ Set.Icc (j₁ : ℕ) (j₁ + dP) then P.coeff (i - j₁) else 0)) =
              C.coeff (i.val - j.val) := by
            conv_lhs => rw [hjeq]
            rw [Fin.addCases_left, ite_eq_left hmem]
          rw [hval]
          have hle_ij : j.val ≤ i.val := hmem.1
          have hpq : (p i + q j).toNat ≤ mC - (i.val - j.val) := by
            dsimp only [p, q]; rw [ite_eq_left hj]; omega
          exact (pow_dvd_pow t hpq).trans (hC (i.val - j.val))
        · left
          conv_lhs => rw [hjeq]
          rw [Fin.addCases_left, ite_eq_right hmem]
      · have hklt : j.val - dP < dC := by have := j.isLt; omega
        have hjeq : j = Fin.natAdd dP ⟨j.val - dP, hklt⟩ := Fin.ext (by dsimp; omega)
        by_cases hmem : i.val ∈ Set.Icc (j.val - dP) (j.val - dP + dP)
        · right
          have hval : (j.addCases
              (fun j₁ => if i.val ∈ Set.Icc (j₁ : ℕ) (j₁ + dC) then C.coeff (i - j₁) else 0)
              (fun j₁ => if i.val ∈ Set.Icc (j₁ : ℕ) (j₁ + dP) then P.coeff (i - j₁) else 0)) =
              P.coeff (i.val - (j.val - dP)) := by
            conv_lhs => rw [hjeq]
            rw [Fin.addCases_right, ite_eq_left hmem]
          rw [hval]
          have hle_ik : j.val - dP ≤ i.val := hmem.1
          have hpq : (p i + q j).toNat ≤ mP - (i.val - (j.val - dP)) := by
            dsimp only [p, q]; rw [ite_eq_right hj]; omega
          exact (pow_dvd_pow t hpq).trans (hP (i.val - (j.val - dP)))
        · left
          conv_lhs => rw [hjeq]
          rw [Fin.addCases_right, ite_eq_right hmem]
  · have h0 : dC * mP + dP * mC - dP * dC = 0 := Nat.sub_eq_zero_of_le (by omega)
    rw [h0, pow_zero]; exact one_dvd _

/-- **Syzygy Resultant Valuation Cancellation Theorem (`#251` Theorem 1):**
Over any integral domain `R` with nonzero `t`, if `P ∣ A`, `∀ j, t ^ (mP - j) ∣ P.coeff j`, and
`∀ j, t ^ (mC - j) ∣ (C t * B + X * A).coeff j`, then
`t ^ (dC * mP + dP * mC - dP * dC - dP) ∣ P.leadingCoeff ^ (dC - dB) * Res_{dP, dB}(P, B)`! -/
theorem pow_dvd_lc_mul_resultant_of_syzygy {R : Type*} [CommRing R] [IsDomain R]
    (A B P : R[X]) (t : R) (ht : t ≠ 0) (dP dB dC mP mC : ℕ)
    (hP_ne : P ≠ 0) (hP_deg : P.natDegree = dP) (hP_dvd : P ∣ A)
    (hB : B.natDegree ≤ dB) (hBC : dB ≤ dC) (hPC : dP ≤ dC) (hAC : A.natDegree + 1 ≤ dC)
    (hP_ord : ∀ j, t ^ (mP - j) ∣ P.coeff j)
    (hC_ord : ∀ j, t ^ (mC - j) ∣ (Polynomial.C t * B + Polynomial.X * A).coeff j) :
    t ^ (dC * mP + dP * mC - dP * dC - dP) ∣
      P.leadingCoeff ^ (dC - dB) * Polynomial.resultant P B dP dB := by
  have hdvd := pow_dvd_resultant_asym_linear P (Polynomial.C t * B + Polynomial.X * A)
    dP mP dC mC t hP_ord hC_ord
  rw [resultant_syzygy_eq_of_dvd A B P t dP dB dC hP_ne hP_deg hP_dvd hB hBC hPC hAC] at hdvd
  set E := dC * mP + dP * mC - dP * dC
  by_cases hE : dP ≤ E
  · have hsplit : t ^ E = t ^ dP * t ^ (E - dP) := by rw [← pow_add, Nat.add_sub_of_le hE]
    rw [hsplit, show P.leadingCoeff ^ (dC - dB) * t ^ dP * Polynomial.resultant P B dP dB =
        t ^ dP * (P.leadingCoeff ^ (dC - dB) * Polynomial.resultant P B dP dB) by ring] at hdvd
    exact (mul_dvd_mul_iff_left (pow_ne_zero dP ht)).mp hdvd
  · have h0 : E - dP = 0 := Nat.sub_eq_zero_of_le (by omega)
    rw [h0, pow_zero]; exact one_dvd _

/-- **Linear Factor `k - 1 → k` Boost (`#251` Corollary — kills BOTH `A = a_uni * G^4` AND
`A = A_1 * G^2`!):**
For ANY linear factor `G ∣ A` (`G.natDegree = 1`) passing through the origin (`t ∣ G.coeff 0`)
at an order-`k` contact node (`∀ j, t ^ (k + 1 - j) ∣ (C t * B + X * A).coeff j`),
`t ^ k ∣ G.leadingCoeff ^ (dC - dB) * Res_{1, dB}(G, B)`! -/
theorem pow_dvd_lc_mul_resultant_linear_of_syzygy {R : Type*} [CommRing R] [IsDomain R]
    (A B G : R[X]) (t : R) (ht : t ≠ 0) (dB dC k : ℕ)
    (hG_deg : G.natDegree = 1) (hG_dvd : G ∣ A)
    (hB : B.natDegree ≤ dB) (hBC : dB ≤ dC) (hAC : A.natDegree + 1 ≤ dC)
    (hG0 : t ∣ G.coeff 0)
    (hC_ord : ∀ j, t ^ (k + 1 - j) ∣ (Polynomial.C t * B + Polynomial.X * A).coeff j) :
    t ^ k ∣ G.leadingCoeff ^ (dC - dB) * Polynomial.resultant G B 1 dB := by
  have hG_ne : G ≠ 0 := by intro h0; simp [h0] at hG_deg
  have hG_ord : ∀ j, t ^ (1 - j) ∣ G.coeff j := by
    intro j
    rcases j with _ | j
    · simpa using hG0
    · simp
  have h := pow_dvd_lc_mul_resultant_of_syzygy A B G t ht 1 dB dC 1 (k + 1)
    hG_ne hG_deg hG_dvd hB hBC (by omega) hAC hG_ord hC_ord
  have hexp : dC * 1 + 1 * (k + 1) - 1 * dC - 1 = k := by omega
  rwa [hexp] at h

end SyzygyResultant

/-! ### Part 2: Contact-Order Syzygy, `T^{k - d_B} ∣ A_{k - 1}`, & Extra-Vanishing Discriminant (`#251` Thm 2) -/

section ContactOrderAndExtraDisc

/-- Bivariate polynomial ring `A[X][Y]`. -/
abbrev BiPoly (A : Type*) [CommRing A] := Polynomial (Polynomial A)

/-- Local contact order `≥ k` at `(0, 0)` for a first-order linear-in-`Y₁` relation
`A(T, U) Y₁ + B(T, U)` (`k ≥ 1`):
- `A` and `B` both have bivariate multiplicity `≥ k - 1`, and
- the degree-`k` homogeneous part of the syzygy `T · B + U · A` vanishes identically. -/
def ContactOrderGE {R : Type*} [CommRing R] (k : ℕ) (A B : BiPoly R) : Prop :=
  (∀ i j : ℕ, i + j < k - 1 → (A.coeff j).coeff i = 0 ∧ (B.coeff j).coeff i = 0) ∧
  (∀ i j : ℕ, i + j = k →
    (if 1 ≤ i then (B.coeff j).coeff (i - 1) else 0) +
    (if 1 ≤ j then (A.coeff (j - 1)).coeff i else 0) = 0)

theorem coeff_syzygy_biPoly {R : Type*} [CommRing R] (A B : BiPoly R) (i j : ℕ) :
    (((Polynomial.C Polynomial.X * B + Polynomial.X * A : BiPoly R).coeff j).coeff i) =
      (if 1 ≤ i then (B.coeff j).coeff (i - 1) else 0) +
      (if 1 ≤ j then (A.coeff (j - 1)).coeff i else 0) := by
  rw [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_add]
  congr 1
  · rcases i with _ | i
    · simp
    · simp [Polynomial.coeff_X_mul]
  · rcases j with _ | j
    · simp
    · simp [Polynomial.coeff_X_mul]

/-- At any order-`k` contact node (`k ≥ 1`), the syzygy `C = T·B + U·A` automatically has
bivariate multiplicity `≥ k + 1` (`∀ j, X ^ (k + 1 - j) ∣ C.coeff j`)! -/
theorem X_pow_dvd_syzygy_of_contactOrderGE {R : Type*} [CommRing R]
    {k : ℕ} (hk : 1 ≤ k) {A B : BiPoly R} (hcon : ContactOrderGE k A B) :
    ∀ j, Polynomial.X ^ (k + 1 - j) ∣
      (Polynomial.C Polynomial.X * B + Polynomial.X * A : BiPoly R).coeff j := by
  intro j
  rw [Polynomial.X_pow_dvd_iff]
  intro i hi
  rw [coeff_syzygy_biPoly]
  have hij : i + j ≤ k := by omega
  rcases eq_or_lt_of_le hij with heq | hlt
  · exact hcon.2 i j heq
  · have hB : (if 1 ≤ i then (B.coeff j).coeff (i - 1) else 0) = 0 := by
      split_ifs with hi1
      · exact (hcon.1 (i - 1) j (by omega)).2
      · rfl
    have hA : (if 1 ≤ j then (A.coeff (j - 1)).coeff i else 0) = 0 := by
      split_ifs with hj1
      · exact (hcon.1 i (j - 1) (by omega)).1
      · rfl
    rw [hB, hA, add_zero]

/-- **`T^{k - d_B} ∣ A_{k - 1}` Theorem (`#251` Theorem 2):**
At any order-`k` contact node with `B.natDegree ≤ dB`, EVERY `(k - 1 - s, s)` coefficient of `A`
with `dB ≤ s ≤ k - 1` vanishes identically — hence `X ^ (k - s) ∣ A.coeff s` for all
`dB ≤ s ≤ k - 1`! -/
theorem coeff_A_eq_zero_of_ge_degB {R : Type*} [CommRing R]
    {k dB : ℕ} {A B : BiPoly R} (hcon : ContactOrderGE k A B) (hB : B.natDegree ≤ dB)
    {s : ℕ} (hs_lo : dB ≤ s) (hs_hi : s ≤ k - 1) (hk : 1 ≤ k) :
    (A.coeff s).coeff (k - 1 - s) = 0 := by
  have heq := hcon.2 (k - 1 - s) (s + 1) (by omega)
  have hB0 : B.coeff (s + 1) = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  simp only [hB0, Polynomial.coeff_zero, ite_self, zero_add,
    ite_eq_left (by omega : 1 ≤ s + 1), Nat.add_sub_cancel] at heq
  exact heq

theorem X_pow_dvd_A_coeff_of_ge_degB {R : Type*} [CommRing R]
    {k dB : ℕ} (hk : 1 ≤ k) {A B : BiPoly R}
    (hcon : ContactOrderGE k A B) (hB : B.natDegree ≤ dB)
    {s : ℕ} (hs_lo : dB ≤ s) (hs_hi : s ≤ k - 1) :
    Polynomial.X ^ (k - s) ∣ A.coeff s := by
  rw [Polynomial.X_pow_dvd_iff]
  intro i hi
  by_cases hlt : i + s < k - 1
  · exact (hcon.1 i s hlt).1
  · have hi_eq : i = k - 1 - s := by omega
    rw [hi_eq]
    exact coeff_A_eq_zero_of_ge_degB hcon hB hs_lo hs_hi hk

/-- Special case `dB = 0`: every contact node of order `k ≥ 2` is forced slack
(`biMult(A) ≥ k` AND `biMult(B) ≥ k`)! -/
theorem slack_of_degB_eq_zero {R : Type*} [CommRing R]
    {k : ℕ} (hk : 2 ≤ k) {A B : BiPoly R}
    (hcon : ContactOrderGE k A B) (hB0 : B.natDegree = 0) :
    ∀ i j : ℕ, i + j < k → (A.coeff j).coeff i = 0 ∧ (B.coeff j).coeff i = 0 := by
  intro i j hij
  by_cases hlt : i + j < k - 1
  · exact hcon.1 i j hlt
  · have heq : i + j = k - 1 := by omega
    constructor
    · have hi_eq : i = k - 1 - j := by omega
      rw [hi_eq]
      exact coeff_A_eq_zero_of_ge_degB hcon (le_of_eq hB0) (Nat.zero_le j) (by omega) (by omega)
    · rcases j with _ | j
      · have h0 := hcon.2 k 0 (by omega)
        simp only [ite_eq_left (by omega : 1 ≤ k), ite_eq_right (by omega : ¬ 1 ≤ 0),
          add_zero] at h0
        have hi_eq : i = k - 1 := by omega
        rwa [hi_eq]
      · have hBj : B.coeff (j + 1) = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
        simp [hBj]

private theorem card_filter_lt_fin (n k : ℕ) (hk : k ≤ n) :
    (Finset.univ.filter (fun i : Fin n => i.val < k)).card = k := by
  have hbij : (Finset.univ.filter (fun i : Fin n => i.val < k)).card =
      (Finset.univ : Finset (Fin k)).card := by
    refine Finset.card_bij (fun i hi => ⟨i.val, (Finset.mem_filter.mp hi).2⟩) ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro a _ b _ hab; exact Fin.ext (by simpa using congrArg Fin.val hab)
    · intro j _
      exact ⟨⟨j.val, j.isLt.trans_le hk⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, j.isLt⟩, rfl⟩
  rw [hbij, Finset.card_univ, Fintype.card_fin]

private theorem two_mul_sum_max_sub (n k : ℕ) (hk : k ≤ n) :
    2 * ∑ i : Fin n, max (0 : ℤ) ((k : ℤ) - i.val) = (k : ℤ) * (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk' : k ≤ n := Nat.le_of_succ_le hk
    have hstep : ∀ i : Fin n,
        max (0 : ℤ) (((k + 1 : ℕ) : ℤ) - i.val) =
          max (0 : ℤ) ((k : ℤ) - i.val) + if i.val < k + 1 then (1 : ℤ) else 0 := fun i => by
      split_ifs <;> omega
    have hsum_step : ∑ i : Fin n, max (0 : ℤ) (((k + 1 : ℕ) : ℤ) - i.val) =
        (∑ i : Fin n, max (0 : ℤ) ((k : ℤ) - i.val)) + ((k + 1 : ℕ) : ℤ) := by
      simp_rw [hstep, Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_ite, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.sum_const_zero, add_zero,
        card_filter_lt_fin n (k + 1) hk]
    rw [hsum_step]
    have ihk := ih hk'
    push_cast
    linarith

private theorem sylvesterDeriv_entry_cases {R : Type*} [CommRing R]
    (f : R[X]) (hd : 2 ≤ f.natDegree)
    (i j : Fin (f.natDegree - 1 + f.natDegree)) :
    (i.val = 2 * f.natDegree - 2 ∧
      ((j.val = f.natDegree - 2 ∧ f.sylvesterDeriv i j = 1) ∨
       (j.val = 2 * f.natDegree - 2 ∧ f.sylvesterDeriv i j = (f.natDegree : R)) ∨
       f.sylvesterDeriv i j = 0)) ∨
    (i.val < 2 * f.natDegree - 2 ∧
      ((j.val < f.natDegree - 1 ∧
        ((f.sylvesterDeriv i j = 0) ∨
         (j.val ≤ i.val ∧ f.sylvesterDeriv i j = f.coeff (i.val - j.val)))) ∨
       (f.natDegree - 1 ≤ j.val ∧
        ((f.sylvesterDeriv i j = 0) ∨
         (j.val - (f.natDegree - 1) ≤ i.val ∧
          f.sylvesterDeriv i j =
            (((i.val - (j.val - (f.natDegree - 1)) + 1 : ℕ) : R) *
              f.coeff (i.val - (j.val - (f.natDegree - 1)) + 1))))))) := by
  have hd0 : f.natDegree ≠ 0 := by omega
  have hi_le : i.val ≤ 2 * f.natDegree - 2 := by have := i.isLt; omega
  rcases eq_or_lt_of_le hi_le with hi_eq | hi_lt
  · left
    refine ⟨hi_eq, ?_⟩
    have hi_fin : i = ⟨2 * f.natDegree - 2, by omega⟩ := Fin.ext hi_eq
    rw [hi_fin, Polynomial.sylvesterDeriv, dite_eq_right hd0, Matrix.updateRow_self]
    by_cases hj1 : j.val = f.natDegree - 2
    · left; exact ⟨hj1, ite_eq_left hj1⟩
    · by_cases hj2 : j.val = 2 * f.natDegree - 2
      · right; left; exact ⟨hj2, by rw [ite_eq_right hj1, ite_eq_left hj2]⟩
      · right; right; rw [ite_eq_right hj1, ite_eq_right hj2]
  · right
    refine ⟨hi_lt, ?_⟩
    have hi_ne : i ≠ ⟨2 * f.natDegree - 2, by omega⟩ := fun h => by
      have := congrArg Fin.val h; dsimp at this; omega
    rw [Polynomial.sylvesterDeriv, dite_eq_right hd0, Matrix.updateRow_ne hi_ne,
      Polynomial.sylvester, Matrix.of_apply]
    by_cases hj : j.val < f.natDegree - 1
    · left
      refine ⟨hj, ?_⟩
      have hjeq : j = Fin.castAdd f.natDegree ⟨j.val, hj⟩ := Fin.ext rfl
      by_cases hmem : i.val ∈ Set.Icc j.val (j.val + f.natDegree)
      · right; refine ⟨hmem.1, ?_⟩; conv_lhs => rw [hjeq]; rw [Fin.addCases_left, ite_eq_left hmem]
      · left; conv_lhs => rw [hjeq]; rw [Fin.addCases_left, ite_eq_right hmem]
    · right
      have hjge : f.natDegree - 1 ≤ j.val := by omega
      refine ⟨hjge, ?_⟩
      have hklt : j.val - (f.natDegree - 1) < f.natDegree := by have := j.isLt; omega
      have hjeq : j = Fin.natAdd (f.natDegree - 1) ⟨j.val - (f.natDegree - 1), hklt⟩ :=
        Fin.ext (by dsimp; omega)
      by_cases hmem : i.val ∈ Set.Icc (j.val - (f.natDegree - 1))
          (j.val - (f.natDegree - 1) + (f.natDegree - 1))
      · right; refine ⟨hmem.1, ?_⟩; conv_lhs => rw [hjeq]
        rw [Fin.addCases_right, ite_eq_left hmem, Polynomial.coeff_derivative]
        dsimp only; rw [mul_comm]; push_cast; rfl
      · left; conv_lhs => rw [hjeq]; rw [Fin.addCases_right, ite_eq_right hmem]

/-- **Universal Extra-Vanishing Quadratic Discriminant Boost (`#251` Theorem 2):**
Over **EVERY commutative ring `R`**, if `1 ≤ dB ≤ m < d = f.natDegree`,
`∀ j, t ^ (m - j) ∣ f.coeff j`, AND `∀ j, dB ≤ j → j ≤ m → t ^ (m + 1 - j) ∣ f.coeff j`
(as forced by `T^{k - dB} ∣ A_{k - 1}` with `m = k - 1`!), then:
```text
  t ^ (m * (m - 1) + (m - dB + 1)) ∣ f.discr!
```
In particular:
- `dB = m`: recovers `m * (m - 1) + 1` (`#210`),
- `d = 4, dB = 2, m = 3 (k = 4)`: **`t ^ 8 ∣ f.discr`** (`7 → 8`, `#251`),
- `d = 6, dB = 3, m = 5 (k = 6)`: **`t ^ 23 ∣ f.discr`** (`21 → 23`, `#251`)! -/
theorem pow_dvd_discr_of_extra_vanishing {R : Type*} [CommRing R]
    (f : R[X]) (hd : 2 ≤ f.natDegree) (t : R) (dB m : ℕ)
    (hdB1 : 1 ≤ dB) (hdBm : dB ≤ m) (hmlt : m < f.natDegree)
    (hord : ∀ j, t ^ (m - j) ∣ f.coeff j)
    (hextra : ∀ j, dB ≤ j → j ≤ m → t ^ (m + 1 - j) ∣ f.coeff j) :
    t ^ (m * (m - 1) + (m - dB + 1)) ∣ f.discr := by
  have hm1 : 1 ≤ m := hdB1.trans hdBm
  rw [Polynomial.discr]
  apply dvd_mul_of_dvd_left
  let d := f.natDegree
  let lo := m + dB - 2
  let hi := 2 * m - 2
  let p0 : Fin (d - 1 + d) → ℤ := fun i => max 0 (((2 * m - 2 : ℕ) : ℤ) - i.val)
  let p : Fin (d - 1 + d) → ℤ := fun i =>
    p0 i + if lo ≤ i.val ∧ i.val ≤ hi then 1 else 0
  let q : Fin (d - 1 + d) → ℤ := fun j =>
    if j.val < d - 1 then -max 0 (((m - 2 : ℕ) : ℤ) - j.val)
    else -max 0 (((m - 1 : ℕ) : ℤ) - ((j.val - (d - 1) : ℕ) : ℤ))
  apply pow_dvd_det_of_potential f.sylvesterDeriv t p q
  · -- Bump sum equals `m - dB + 1`!
    have hcard_bump :
        (Finset.univ.filter (fun i : Fin (d - 1 + d) => lo ≤ i.val ∧ i.val ≤ hi)).card =
        m - dB + 1 := by
      have hbij : (Finset.univ.filter (fun i : Fin (d - 1 + d) => lo ≤ i.val ∧ i.val ≤ hi)).card =
          (Finset.univ : Finset (Fin (m - dB + 1))).card := by
        refine Finset.card_bij
          (fun i hi' => ⟨i.val - lo, by have := (Finset.mem_filter.mp hi').2; dsimp [lo, hi] at *; omega⟩)
          ?_ ?_ ?_
        · intro _ _; exact Finset.mem_univ _
        · intro a ha b hb hab
          have ha' := (Finset.mem_filter.mp ha).2
          have hb' := (Finset.mem_filter.mp hb).2
          have hval : a.val - lo = b.val - lo := congrArg Fin.val hab
          exact Fin.ext (by omega)
        · intro r _
          refine ⟨⟨lo + r.val, by have := r.isLt; dsimp [lo]; omega⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, by have := r.isLt; dsimp [lo, hi]; omega⟩, ?_⟩
          apply Fin.ext; dsimp; omega
      rw [hbij, Finset.card_univ, Fintype.card_fin]
    have hp_bump : ∑ i : Fin (d - 1 + d), p i =
        (∑ i : Fin (d - 1 + d), p0 i) + ((m - dB + 1 : ℕ) : ℤ) := by
      simp only [p, Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_ite, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.sum_const_zero, add_zero,
        hcard_bump]
    have hp2 := two_mul_sum_max_sub (d - 1 + d) (2 * m - 2) (by omega)
    have hq_split : ∑ j : Fin (d - 1 + d), q j =
        -(∑ j : Fin (d - 1), max (0 : ℤ) (((m - 2 : ℕ) : ℤ) - j.val)) -
        (∑ k : Fin d, max (0 : ℤ) (((m - 1 : ℕ) : ℤ) - k.val)) := by
      rw [Fin.sum_univ_add]
      have hL : ∑ j : Fin (d - 1), q (Fin.castAdd d j) =
          -(∑ j : Fin (d - 1), max (0 : ℤ) (((m - 2 : ℕ) : ℤ) - j.val)) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        dsimp only [q]; rw [ite_eq_left (by dsimp; omega)]; simp
      have hR : ∑ k : Fin d, q (Fin.natAdd (d - 1) k) =
          -(∑ k : Fin d, max (0 : ℤ) (((m - 1 : ℕ) : ℤ) - k.val)) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        dsimp only [q]; rw [ite_eq_right (by dsimp; omega)]
        have : (Fin.natAdd (d - 1) k).val - (d - 1) = k.val := by dsimp; omega
        rw [this]
      rw [hL, hR]; ring
    have hq1 := two_mul_sum_max_sub (d - 1) (m - 2) (by omega)
    have hq2 := two_mul_sum_max_sub d (m - 1) (by omega)
    have hq1_id : (((m - 2 : ℕ) : ℤ) * (((m - 2 : ℕ) : ℤ) + 1)) =
        ((m : ℤ) - 2) * ((m : ℤ) - 1) := by
      rcases eq_or_lt_of_le hm1 with rfl | hm2
      · norm_num
      · zify [show 2 ≤ m by omega]; ring
    have hcalc : 2 * (∑ i : Fin (d - 1 + d), p i + ∑ j : Fin (d - 1 + d), q j) =
        2 * (((m * (m - 1) + (m - dB + 1) : ℕ) : ℤ)) := by
      rw [hp_bump, hq_split]
      have hp' : 2 * ∑ i : Fin (d - 1 + d), p0 i =
          (((2 * m - 2 : ℕ) : ℤ) * (((2 * m - 2 : ℕ) : ℤ) + 1)) := hp2
      zify [hm1, hdBm, show 2 ≤ 2 * m by omega] at hp' hq2 ⊢
      nlinarith only [hp', hq1, hq1_id, hq2]
    linarith
  · -- Entrywise divisibility check
    intro i j
    rcases sylvesterDeriv_entry_cases f hd i j with
      ⟨hi_eq, ⟨hj_eq, hval⟩ | ⟨hj_eq, hval⟩ | hzero⟩ |
      ⟨hi_lt, ⟨hj_lt, hzero | ⟨hle, hval⟩⟩ | ⟨hj_ge, hzero | ⟨hle, hval⟩⟩⟩
    · right; rw [hval]
      have hpq : (p i + q j).toNat = 0 := by
        dsimp only [p, p0, q, lo, hi]
        rw [ite_eq_right (by omega : ¬ (m + dB - 2 ≤ i.val ∧ i.val ≤ 2 * m - 2)),
          ite_eq_left (by omega : j.val < d - 1)]; omega
      rw [hpq, pow_zero]
    · right; rw [hval]
      have hpq : (p i + q j).toNat = 0 := by
        dsimp only [p, p0, q, lo, hi]
        rw [ite_eq_right (by omega : ¬ (m + dB - 2 ≤ i.val ∧ i.val ≤ 2 * m - 2)),
          ite_eq_right (by omega : ¬ j.val < d - 1)]; omega
      rw [hpq, pow_zero]; exact one_dvd _
    · left; exact hzero
    · left; exact hzero
    · right; rw [hval]
      by_cases hi_b : lo ≤ i.val ∧ i.val ≤ hi
      · by_cases hrange : dB ≤ i.val - j.val ∧ i.val - j.val ≤ m
        · have hpq : (p i + q j).toNat ≤ m + 1 - (i.val - j.val) := by
            dsimp only [p, p0, q, lo, hi] at hi_b ⊢
            rw [ite_eq_left hi_b, ite_eq_left hj_lt]; omega
          exact (pow_dvd_pow t hpq).trans (hextra (i.val - j.val) hrange.1 hrange.2)
        · have hpq : (p i + q j).toNat ≤ m - (i.val - j.val) := by
            dsimp only [p, p0, q, lo, hi] at hi_b ⊢
            rw [ite_eq_left hi_b, ite_eq_left hj_lt]; omega
          exact (pow_dvd_pow t hpq).trans (hord (i.val - j.val))
      · have hpq : (p i + q j).toNat ≤ m - (i.val - j.val) := by
          dsimp only [p, p0, q, lo, hi] at hi_b ⊢
          rw [ite_eq_right hi_b, ite_eq_left hj_lt]; omega
        exact (pow_dvd_pow t hpq).trans (hord (i.val - j.val))
    · left; exact hzero
    · right; rw [hval]
      set idx := i.val - (j.val - (d - 1)) + 1
      by_cases hi_b : lo ≤ i.val ∧ i.val ≤ hi
      · by_cases hrange : dB ≤ idx ∧ idx ≤ m
        · have hpq : (p i + q j).toNat ≤ m + 1 - idx := by
            dsimp only [p, p0, q, lo, hi, idx] at hi_b ⊢
            rw [ite_eq_left hi_b, ite_eq_right (by omega : ¬ j.val < d - 1)]; omega
          exact dvd_mul_of_dvd_right ((pow_dvd_pow t hpq).trans (hextra idx hrange.1 hrange.2)) _
        · have hpq : (p i + q j).toNat ≤ m - idx := by
            dsimp only [p, p0, q, lo, hi, idx] at hi_b ⊢
            rw [ite_eq_left hi_b, ite_eq_right (by omega : ¬ j.val < d - 1)]; omega
          exact dvd_mul_of_dvd_right ((pow_dvd_pow t hpq).trans (hord idx)) _
      · have hpq : (p i + q j).toNat ≤ m - idx := by
          dsimp only [p, p0, q, lo, hi, idx] at hi_b ⊢
          rw [ite_eq_right hi_b, ite_eq_right (by omega : ¬ j.val < d - 1)]; omega
        exact dvd_mul_of_dvd_right ((pow_dvd_pow t hpq).trans (hord idx)) _

/-- Explicit `#251` specialization: `(d = 4, dB = 2, k = 4)` boosts `psi_disc(4, 3)` `7 → 8`! -/
theorem pow_eight_dvd_discr_deg4 {R : Type*} [CommRing R]
    (f : R[X]) (hd : f.natDegree = 4) (t : R)
    (hord : ∀ j, t ^ (3 - j) ∣ f.coeff j)
    (hc2 : t ^ 2 ∣ f.coeff 2) (hc3 : t ∣ f.coeff 3) :
    t ^ 8 ∣ f.discr := by
  have h := pow_dvd_discr_of_extra_vanishing f (by omega) t 2 3 (by omega) (by omega) (by omega)
    hord (fun j h1 h2 => by
      have : j = 2 ∨ j = 3 := by omega
      rcases this with rfl | rfl
      · simpa using hc2
      · simpa using hc3)
  simpa using h

/-- Explicit `#251` specialization: `(d = 6, dB = 3, k = 6)` boosts `psi_disc(6, 5)` `21 → 23`! -/
theorem pow_23_dvd_discr_deg6 {R : Type*} [CommRing R]
    (f : R[X]) (hd : f.natDegree = 6) (t : R)
    (hord : ∀ j, t ^ (5 - j) ∣ f.coeff j)
    (hc3 : t ^ 3 ∣ f.coeff 3) (hc4 : t ^ 2 ∣ f.coeff 4) (hc5 : t ∣ f.coeff 5) :
    t ^ 23 ∣ f.discr := by
  have h := pow_dvd_discr_of_extra_vanishing f (by omega) t 3 5 (by omega) (by omega) (by omega)
    hord (fun j h1 h2 => by
      have : j = 3 ∨ j = 4 ∨ j = 5 := by omega
      rcases this with rfl | rfl | rfl
      · simpa using hc3
      · simpa using hc4
      · simpa using hc5)
  simpa using h

end ContactOrderAndExtraDisc

/-! ### Part 3: Reduced `(2d - 2) × (2d - 2)` Discriminant Matrix `M_disc(P)` & Exact Weighted Degree (`#251` Thm 3) -/

section ReducedDiscMatrix

/-- Column index map inserting a skipped column at `d - 2` inside `Fin (2 * d - 1)`. -/
private def skipCol (d : ℕ) (hd : 2 ≤ d) (j : Fin (2 * d - 2)) : Fin (d - 1 + d) :=
  if h : j.val < d - 2 then ⟨j.val, by omega⟩ else ⟨j.val + 1, by omega⟩

/-- The reduced `(2d - 2) × (2d - 2)` discriminant matrix `M_disc(P)` (`#251` Theorem 3), obtained
from `P.sylvesterDeriv` by subtracting `d` times column `d - 2` from column `2d - 2` and deleting
the bottom row `2d - 2` and column `d - 2` (zero division by `P.leadingCoeff`!). -/
noncomputable def reducedDiscMatrix {R : Type*} [CommRing R] (P : R[X]) (hd : 2 ≤ P.natDegree) :
    Matrix (Fin (2 * P.natDegree - 2)) (Fin (2 * P.natDegree - 2)) R :=
  let d := P.natDegree
  Matrix.of fun i j =>
    let row : Fin (d - 1 + d) := ⟨i.val, by omega⟩
    let col : Fin (d - 1 + d) := skipCol d hd j
    if j.val = 2 * d - 3 then
      P.sylvesterDeriv row col - (d : R) * P.sylvesterDeriv row ⟨d - 2, by omega⟩
    else
      P.sylvesterDeriv row col

/-- **Exact Reduced Discriminant Matrix Identity (`#251` Theorem 3):**
Over **EVERY commutative ring `R`** and for every `P : R[X]` with `2 ≤ d = P.natDegree`,
`P.discr = (-1) ^ (d * (d - 1) / 2 + d) * (reducedDiscMatrix P hd).det`
with ZERO division by `P.leadingCoeff`! -/
theorem discr_eq_sign_mul_det_reducedDiscMatrix {R : Type*} [CommRing R]
    (P : R[X]) (hd : 2 ≤ P.natDegree) :
    P.discr =
      (-1 : R) ^ (P.natDegree * (P.natDegree - 1) / 2 + P.natDegree) *
        (reducedDiscMatrix P hd).det := by
  let d := P.natDegree
  have hd0 : d ≠ 0 := by omega
  let rLast : Fin (d - 1 + d) := ⟨2 * d - 2, by omega⟩
  let cDrop : Fin (d - 1 + d) := ⟨d - 2, by omega⟩
  let cLast : Fin (d - 1 + d) := ⟨2 * d - 2, by omega⟩
  have hc_ne : cLast ≠ cDrop := fun h => by
    have := congrArg Fin.val h; dsimp [cLast, cDrop] at this; omega
  -- Column-eliminated matrix `M'`: subtract `d • col(cDrop)` from `col(cLast)`.
  let M' : Matrix (Fin (d - 1 + d)) (Fin (d - 1 + d)) R :=
    P.sylvesterDeriv.updateCol cLast
      (fun i => P.sylvesterDeriv i cLast - (d : R) * P.sylvesterDeriv i cDrop)
  have hdet_eq : M'.det = P.sylvesterDeriv.det := by
    have hT : M'ᵀ = P.sylvesterDerivᵀ.updateRow cLast
        (P.sylvesterDerivᵀ cLast + (-(d : R)) • P.sylvesterDerivᵀ cDrop) := by
      ext i j
      by_cases hi : i = cLast
      · subst hi; simp [M', sub_eq_add_neg]
      · simp [M', hi]
    rw [← Matrix.det_transpose, hT, Matrix.det_updateRow_add_smul_self _ hc_ne,
      Matrix.det_transpose]
  -- Expand `M'.det` along bottom row `rLast`, where ONLY column `cDrop` is nonzero (value `1`)!
  have hbot : ∀ j : Fin (d - 1 + d), M' rLast j = if j = cDrop then 1 else 0 := by
    intro j
    by_cases hjL : j = cLast
    · subst hjL
      have hne1 : cLast.val ≠ d - 2 := by dsimp [cLast]; omega
      have heq2 : cLast.val = 2 * d - 2 := rfl
      have heq3 : cDrop.val = d - 2 := rfl
      simp only [M', Matrix.updateCol_self, ite_eq_right hc_ne]
      rw [Polynomial.sylvesterDeriv, dite_eq_right hd0, Matrix.updateRow_self]
      rw [ite_eq_right hne1, ite_eq_left heq2, ite_eq_left heq3, mul_one, sub_self]
    · simp only [M', Matrix.updateCol_ne hjL]
      rw [Polynomial.sylvesterDeriv, dite_eq_right hd0, Matrix.updateRow_self]
      by_cases hjD : j = cDrop
      · subst hjD; simp [cDrop, d]
      · have hneD : j.val ≠ d - 2 := fun h => hjD (Fin.ext h)
        have hneL : j.val ≠ 2 * d - 2 := fun h => hjL (Fin.ext h)
        rw [ite_eq_right hneD, ite_eq_right hneL, ite_eq_right hjD]
  -- Reindex `M'` via `finCongr` to `Fin ((2 * d - 2) + 1)` and expand via `Matrix.det_succ_row`!
  let e : Fin ((2 * d - 2) + 1) ≃ Fin (d - 1 + d) := finCongr (by omega)
  let N : Matrix (Fin ((2 * d - 2) + 1)) (Fin ((2 * d - 2) + 1)) R := M'.reindex e.symm e.symm
  have hdetN : N.det = P.sylvesterDeriv.det := by
    rw [Matrix.det_reindex_self, hdet_eq]
  let rLast' : Fin ((2 * d - 2) + 1) := ⟨2 * d - 2, by omega⟩
  let cDrop' : Fin ((2 * d - 2) + 1) := ⟨d - 2, by omega⟩
  rw [Polynomial.discr, ← hdetN, Matrix.det_succ_row N rLast']
  rw [Finset.sum_eq_single cDrop']
  · have hNval : N rLast' cDrop' = 1 := by
      have h1 : e rLast' = rLast := Fin.ext rfl
      have h2 : e cDrop' = cDrop := Fin.ext rfl
      change M' (e rLast') (e cDrop') = 1
      rw [h1, h2, hbot cDrop, ite_eq_left rfl]
    have hsub_eq : N.submatrix rLast'.succAbove cDrop'.succAbove = reducedDiscMatrix P hd := by
      ext i j
      change M' (e (rLast'.succAbove i)) (e (cDrop'.succAbove j)) = _
      have hr : e (rLast'.succAbove i) = ⟨i.val, by omega⟩ := by
        apply Fin.ext
        have hlt : i.castSucc < rLast' := by change i.val < 2 * d - 2; exact i.isLt
        simp [e, Fin.succAbove, hlt]
      have hc : e (cDrop'.succAbove j) = skipCol d hd j := by
        apply Fin.ext
        unfold skipCol
        by_cases hj : j.val < d - 2
        · have hlt : j.castSucc < cDrop' := hj
          simp [e, Fin.succAbove, hlt, hj]
        · have hge : ¬ j.castSucc < cDrop' := hj
          simp [e, Fin.succAbove, hge, hj]
      rw [hr, hc]
      dsimp only [M', reducedDiscMatrix, Matrix.of_apply]
      by_cases hjL : j.val = 2 * d - 3
      · have hcolL : skipCol d hd j = cLast := by
          apply Fin.ext; unfold skipCol; rw [dite_eq_right (by omega)]; dsimp [cLast]; omega
        rw [ite_eq_left hjL, hcolL, Matrix.updateCol_self]
      · have hcolN : skipCol d hd j ≠ cLast := by
          intro h; have := congrArg Fin.val h
          unfold skipCol at this
          split_ifs at this <;> dsimp [cLast] at this <;> omega
        rw [ite_eq_right hjL, Matrix.updateCol_ne hcolN]
    rw [hNval, hsub_eq, mul_one]
    have hsign : (-1 : R) ^ ((rLast' : ℕ) + (cDrop' : ℕ)) *
        (-1 : R) ^ (d * (d - 1) / 2) = (-1 : R) ^ (d * (d - 1) / 2 + d) := by
      have h1 : (rLast' : ℕ) + (cDrop' : ℕ) = 3 * d - 4 := by dsimp [rLast', cDrop']; omega
      rw [h1]
      have h2 : (-1 : R) ^ (3 * d - 4) = (-1 : R) ^ d := by
        have hpar : 3 * d - 4 = d + 2 * (d - 2) := by omega
        have hsq : (-1 : R) ^ 2 = 1 := by ring
        rw [hpar, pow_add, pow_mul, hsq, one_pow, mul_one]
      rw [h2, ← pow_add, add_comm]
    calc (-1 : R) ^ ((rLast' : ℕ) + (cDrop' : ℕ)) * (reducedDiscMatrix P hd).det *
            (-1 : R) ^ (d * (d - 1) / 2)
        = ((-1 : R) ^ ((rLast' : ℕ) + (cDrop' : ℕ)) * (-1 : R) ^ (d * (d - 1) / 2)) *
            (reducedDiscMatrix P hd).det := by ring
      _ = (-1 : R) ^ (d * (d - 1) / 2 + d) * (reducedDiscMatrix P hd).det := by rw [hsign]
  · intro j _ hne
    have h1 : e rLast' = rLast := Fin.ext rfl
    have h2 : e j ≠ cDrop := fun h => hne (e.injective (h.trans (Fin.ext rfl : e cDrop' = cDrop).symm))
    have h0 : N rLast' j = 0 := by
      change M' (e rLast') (e j) = 0
      rw [h1, hbot (e j), ite_eq_right h2]
    simp [h0]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **Exact Weighted Degree Bound on `P.discr` (`#251` Theorem 3):**
For ANY `P : BiPoly R` (`2 ≤ d = P.natDegree`) with `(1, w)`-weighted degree `≤ W`
(i.e. `∀ j, (P.coeff j).natDegree + w * j ≤ W`), the reduced `(2d - 2) × (2d - 2)` discriminant
matrix directly proves:
```text
  P.discr.natDegree ≤ (2 * d - 2) * W - w * d * (d - 1)!
```
(No `IsDomain` needed, zero division by `P.leadingCoeff`!) -/
theorem natDegree_discr_le_of_biWeightedDeg {R : Type*} [CommRing R]
    (P : BiPoly R) (hd : 2 ≤ P.natDegree) (w W : ℕ)
    (hW : ∀ j, P.coeff j ≠ 0 → (P.coeff j).natDegree + w * j ≤ W) :
    P.discr.natDegree ≤ (2 * P.natDegree - 2) * W - w * P.natDegree * (P.natDegree - 1) := by
  let d := P.natDegree
  rw [discr_eq_sign_mul_det_reducedDiscMatrix P hd]
  refine (Polynomial.natDegree_mul_le).trans ?_
  have hsign_deg : ((-1 : Polynomial R) ^ (d * (d - 1) / 2 + d)).natDegree = 0 := by
    have h1 : (-1 : Polynomial R) = Polynomial.C (-1 : R) := by simp
    rw [h1, ← map_pow, Polynomial.natDegree_C]
  rw [hsign_deg, zero_add, Matrix.det_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro σ _
  rw [Units.smul_def, zsmul_eq_mul]
  refine (Polynomial.natDegree_mul_le).trans ?_
  have hunit_deg : ((Equiv.Perm.sign σ : ℤ) : Polynomial R).natDegree = 0 := by
    rw [← Polynomial.C_eq_intCast, Polynomial.natDegree_C]
  rw [hunit_deg, zero_add]
  -- If any factor in the permutation product is 0, `natDegree 0 = 0 ≤ _`.
  by_cases hzero : ∃ j : Fin (2 * d - 2), reducedDiscMatrix P hd (σ j) j = 0
  · obtain ⟨j, hj⟩ := hzero
    rw [Finset.prod_eq_zero (f := fun k => reducedDiscMatrix P hd (σ k) k) (Finset.mem_univ j) hj]
    simp
  push Not at hzero
  -- Define column weight offset `colOff j` so every nonzero entry `(i, j)` has
  -- `natDegree + w * (i + colOff j) ≤ W` (in `ℤ`, with `colOff j` encoding the shift!).
  let colOff : Fin (2 * d - 2) → ℤ := fun j =>
    if j.val < d - 2 then -(j.val : ℤ)
    else if j.val = 2 * d - 3 then -((d - 2 : ℕ) : ℤ)
    else -((j.val - (d - 2) : ℕ) : ℤ) + 1
  have hentry_deg : ∀ j : Fin (2 * d - 2),
      ((reducedDiscMatrix P hd (σ j) j).natDegree : ℤ) +
        (w : ℤ) * (((σ j).val : ℤ) + colOff j) ≤ (W : ℤ) := by
    intro j
    have hne := hzero j
    dsimp only [reducedDiscMatrix, Matrix.of_apply] at hne ⊢
    set i := (σ j).val
    have hi_lt : i < 2 * d - 2 := (σ j).isLt
    by_cases hjL : j.val = 2 * d - 3
    · -- Reduced last column `col(2d - 2) - d • col(d - 2)`: both terms use coeff `i - (d - 2)`!
      rw [ite_eq_left hjL] at hne ⊢
      have hcolL : skipCol d hd j = ⟨2 * d - 2, by omega⟩ := by
        apply Fin.ext; unfold skipCol; rw [dite_eq_right (by omega)]; dsimp; omega
      rw [hcolL] at hne ⊢
      have hd0 : d ≠ 0 := by omega
      have hrne : (⟨i, by omega⟩ : Fin (d - 1 + d)) ≠ ⟨2 * d - 2, by omega⟩ := fun h => by
        have := congrArg Fin.val h; dsimp at this; omega
      have hterm1 : P.sylvesterDeriv ⟨i, by omega⟩ ⟨2 * d - 2, by omega⟩ =
          if d - 1 ≤ i then (((i - (d - 1) + 1 : ℕ) : Polynomial R) * P.coeff (i - (d - 1) + 1))
          else 0 := by
        rw [Polynomial.sylvesterDeriv, dite_eq_right hd0, Matrix.updateRow_ne hrne,
          Polynomial.sylvester, Matrix.of_apply]
        have hjeq : (⟨2 * d - 2, by omega⟩ : Fin (d - 1 + d)) =
            Fin.natAdd (d - 1) ⟨d - 1, by omega⟩ := Fin.ext (by dsimp; omega)
        rw [hjeq, Fin.addCases_right]
        dsimp only
        by_cases hle : d - 1 ≤ i
        · have hmem : i ∈ Set.Icc (d - 1) (d - 1 + (P.natDegree - 1)) := ⟨hle, by omega⟩
          rw [ite_eq_left hmem, ite_eq_left hle, Polynomial.coeff_derivative, mul_comm]
          push_cast; rfl
        · have hmem : ¬ i ∈ Set.Icc (d - 1) (d - 1 + (P.natDegree - 1)) := fun h => hle h.1
          rw [ite_eq_right hmem, ite_eq_right hle]
      have hterm2 : P.sylvesterDeriv ⟨i, by omega⟩ ⟨d - 2, by omega⟩ =
          if d - 2 ≤ i then P.coeff (i - (d - 2)) else 0 := by
        rw [Polynomial.sylvesterDeriv, dite_eq_right hd0, Matrix.updateRow_ne hrne,
          Polynomial.sylvester, Matrix.of_apply]
        have hjeq : (⟨d - 2, by omega⟩ : Fin (d - 1 + d)) =
            Fin.castAdd d ⟨d - 2, by omega⟩ := Fin.ext rfl
        rw [hjeq, Fin.addCases_left]
        dsimp only
        by_cases hle : d - 2 ≤ i
        · have hmem : i ∈ Set.Icc (d - 2) (d - 2 + P.natDegree) := ⟨hle, by omega⟩
          rw [ite_eq_left hmem, ite_eq_left hle]
        · have hmem : ¬ i ∈ Set.Icc (d - 2) (d - 2 + P.natDegree) := fun h => hle h.1
          rw [ite_eq_right hmem, ite_eq_right hle]
      rw [hterm1, hterm2] at hne ⊢
      have hle2 : d - 2 ≤ i := by
        by_contra hlt
        rw [ite_eq_right (by omega : ¬ d - 1 ≤ i), ite_eq_right hlt, mul_zero, sub_zero] at hne
        exact hne rfl
      have hcoeff_ne : P.coeff (i - (d - 2)) ≠ 0 := by
        intro hc0
        by_cases hle1 : d - 1 ≤ i
        · have hidx : i - (d - 1) + 1 = i - (d - 2) := by omega
          rw [ite_eq_left hle1, ite_eq_left hle2, hidx, hc0, mul_zero, mul_zero, sub_zero] at hne
          exact hne rfl
        · rw [ite_eq_right hle1, ite_eq_left hle2, hc0, mul_zero, sub_zero] at hne
          exact hne rfl
      have hdeg_le :
          ((if d - 1 ≤ i then (((i - (d - 1) + 1 : ℕ) : Polynomial R) * P.coeff (i - (d - 1) + 1))
            else 0) - (d : Polynomial R) * (if d - 2 ≤ i then P.coeff (i - (d - 2)) else 0)).natDegree ≤
          (P.coeff (i - (d - 2))).natDegree := by
        rw [ite_eq_left hle2]
        refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
        · split_ifs with hle1
          · have hidx : i - (d - 1) + 1 = i - (d - 2) := by omega
            rw [hidx, ← Polynomial.C_eq_natCast]
            exact Polynomial.natDegree_C_mul_le _ _
          · simp
        · rw [← Polynomial.C_eq_natCast]
          exact Polynomial.natDegree_C_mul_le _ _
      have hW_c := hW (i - (d - 2)) hcoeff_ne
      have hoff : colOff j = -((d - 2 : ℕ) : ℤ) := by
        dsimp only [colOff]; rw [ite_eq_right (by omega : ¬ j.val < d - 2), ite_eq_left hjL]
      rw [hoff]
      have hidxZ : ((i : ℤ) + -((d - 2 : ℕ) : ℤ)) = ((i - (d - 2) : ℕ) : ℤ) := by omega
      rw [hidxZ]
      exact_mod_cast (Nat.add_le_add_right hdeg_le _).trans hW_c
    · rw [ite_eq_right hjL] at hne ⊢
      have hcases := sylvesterDeriv_entry_cases P hd ⟨i, by omega⟩ (skipCol d hd j)
      rcases hcases with ⟨hi_eq, _⟩ | ⟨_, ⟨hj_lt, hzero' | ⟨hle, hval⟩⟩ | ⟨hj_ge, hzero' | ⟨hle, hval⟩⟩⟩
      · exfalso; dsimp at hi_eq; omega
      · exfalso; exact hne hzero'
      · rw [hval] at hne ⊢
        have hj_small : j.val < d - 2 := by
          unfold skipCol at hj_lt; split_ifs at hj_lt with h <;> dsimp at hj_lt <;> omega
        have hsc : (skipCol d hd j).val = j.val := by unfold skipCol; rw [dite_eq_left hj_small]
        dsimp only at hle hne ⊢
        rw [hsc] at hle hne ⊢
        have hW_c := hW (i - j.val) hne
        have hoff : colOff j = -(j.val : ℤ) := by dsimp only [colOff]; rw [ite_eq_left hj_small]
        rw [hoff]
        have hidxZ : ((i : ℤ) + -(j.val : ℤ)) = ((i - j.val : ℕ) : ℤ) := by omega
        rw [hidxZ]
        exact_mod_cast hW_c
      · exfalso; exact hne hzero'
      · rw [hval] at hne ⊢
        have hj_big : ¬ j.val < d - 2 := by
          unfold skipCol at hj_ge; split_ifs at hj_ge with h <;> dsimp at hj_ge <;> omega
        have hsc : (skipCol d hd j).val = j.val + 1 := by unfold skipCol; rw [dite_eq_right hj_big]
        dsimp only at hle hne ⊢
        rw [hsc] at hle hne ⊢
        have hidx_eq : j.val + 1 - (d - 1) = j.val - (d - 2) := by omega
        rw [hidx_eq] at hle hne ⊢
        have hc_ne : P.coeff (i - (j.val - (d - 2)) + 1) ≠ 0 := fun hc0 => by
          rw [hc0, mul_zero] at hne; exact hne rfl
        have hdeg_le : ((((i - (j.val - (d - 2)) + 1 : ℕ) : Polynomial R) *
            P.coeff (i - (j.val - (d - 2)) + 1))).natDegree ≤
            (P.coeff (i - (j.val - (d - 2)) + 1)).natDegree := by
          rw [← Polynomial.C_eq_natCast]; exact Polynomial.natDegree_C_mul_le _ _
        have hW_c := hW (i - (j.val - (d - 2)) + 1) hc_ne
        have hoff : colOff j = -((j.val - (d - 2) : ℕ) : ℤ) + 1 := by
          dsimp only [colOff]; rw [ite_eq_right hj_big, ite_eq_right hjL]
        rw [hoff]
        have hidxZ : ((i : ℤ) + (-((j.val - (d - 2) : ℕ) : ℤ) + 1)) =
            ((i - (j.val - (d - 2)) + 1 : ℕ) : ℤ) := by omega
        rw [hidxZ]
        exact_mod_cast (Nat.add_le_add_right hdeg_le _).trans hW_c
  -- Sum `hentry_deg` over all `j : Fin (2 * d - 2)`!
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  have hsum_ineq :
      ((∑ j : Fin (2 * d - 2), (reducedDiscMatrix P hd (σ j) j).natDegree : ℕ) : ℤ) +
        (w : ℤ) * (∑ j : Fin (2 * d - 2), (((σ j).val : ℤ) + colOff j)) ≤
      ((2 * d - 2 : ℕ) : ℤ) * (W : ℤ) := by
    have h1 := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hentry_deg j
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at h1
    simpa only [Nat.cast_sum] using h1
  -- Exact telescoping identity: `∑ j, ((σ j).val + colOff j) = d * (d - 1)`!
  have hsum_off : ∑ j : Fin (2 * d - 2), (((σ j).val : ℤ) + colOff j) =
      ((d * (d - 1) : ℕ) : ℤ) := by
    rw [Finset.sum_add_distrib, Equiv.sum_comp σ (fun i : Fin (2 * d - 2) => (i.val : ℤ))]
    -- Compute `2 * ∑ j, j.val` and `2 * ∑ j, colOff j` cleanly via `Finset.sum_range_id_mul_two`!
    have hsum_fin : ∀ n : ℕ, 2 * ∑ k : Fin n, (k.val : ℤ) = (n : ℤ) * ((n : ℤ) - 1) := by
      intro n
      have hnat : 2 * ∑ k : Fin n, k.val = n * (n - 1) := by
        rw [Fin.sum_univ_eq_sum_range (fun k => k) n, mul_comm]
        exact Finset.sum_range_id_mul_two n
      rcases n with _ | n
      · simp
      · zify [show 1 ≤ n + 1 by omega] at hnat ⊢
        simpa [Nat.cast_sum] using hnat
    have hsum_col : 2 * ∑ j : Fin (2 * d - 2), colOff j =
        -((d - 2 : ℕ) : ℤ) * (((d - 2 : ℕ) : ℤ) - 1) - 2 * ((d - 2 : ℕ) : ℤ) -
        ((d - 1 : ℕ) : ℤ) * (((d - 1 : ℕ) : ℤ) - 1) + 2 * ((d - 1 : ℕ) : ℤ) := by
      have hsplit1 : ∑ j : Fin (2 * d - 2), colOff j =
          (∑ j : Fin (d - 2), -((j.val : ℤ))) +
          (∑ k : Fin (d - 1), (-((k.val : ℤ)) + 1)) +
          (-((d - 2 : ℕ) : ℤ)) := by
        have hlen : 2 * d - 2 = (d - 2 + (d - 1)) + 1 := by omega
        let e1 : Fin ((d - 2 + (d - 1)) + 1) ≃ Fin (2 * d - 2) := finCongr hlen.symm
        rw [← Equiv.sum_comp e1 colOff, Fin.sum_univ_castSucc, Fin.sum_univ_add]
        congr 1
        · congr 1
          · refine Finset.sum_congr rfl fun j _ => ?_
            simp only [e1, finCongr_apply, Fin.val_cast, Fin.val_castSucc, Fin.val_castAdd, colOff]
            rw [ite_eq_left j.isLt]
          · refine Finset.sum_congr rfl fun k _ => ?_
            simp only [e1, finCongr_apply, Fin.val_cast, Fin.val_castSucc, Fin.val_natAdd, colOff]
            have h1 : ¬ (d - 2 + k.val) < d - 2 := by omega
            have h2 : d - 2 + k.val ≠ 2 * d - 3 := by have := k.isLt; omega
            rw [ite_eq_right h1, ite_eq_right h2]
            have h3 : d - 2 + k.val - (d - 2) = k.val := by omega
            rw [h3]
        · simp only [e1, finCongr_apply, Fin.val_cast, Fin.val_last, colOff]
          have h1 : ¬ (d - 2 + (d - 1)) < d - 2 := by omega
          have h2 : d - 2 + (d - 1) = 2 * d - 3 := by omega
          rw [ite_eq_right h1, ite_eq_left h2]
      rw [hsplit1]
      have h1 := hsum_fin (d - 2)
      have h2 := hsum_fin (d - 1)
      simp only [Finset.sum_neg_distrib, Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at h1 h2 ⊢
      linarith
    have htop := hsum_fin (2 * d - 2)
    have hmul2 : 2 * (∑ j : Fin (2 * d - 2), (j.val : ℤ) + ∑ j : Fin (2 * d - 2), colOff j) =
        2 * ((d * (d - 1) : ℕ) : ℤ) := by
      rw [mul_add, htop, hsum_col]
      zify [show 1 ≤ d by omega, show 2 ≤ d by omega, show 2 ≤ 2 * d by omega]
      ring
    linarith
  rw [hsum_off] at hsum_ineq
  have hnat_ineq :
      (∑ j : Fin (2 * d - 2), (reducedDiscMatrix P hd (σ j) j).natDegree) + w * d * (d - 1) ≤
      (2 * d - 2) * W := by
    have : ((∑ j : Fin (2 * d - 2), (reducedDiscMatrix P hd (σ j) j).natDegree +
        w * d * (d - 1) : ℕ) : ℤ) ≤ (((2 * d - 2) * W : ℕ) : ℤ) := by
      push_cast at hsum_ineq ⊢
      nlinarith only [hsum_ineq]
    exact Int.ofNat_le.mp this
  exact Nat.le_sub_of_add_le hnat_ineq

end ReducedDiscMatrix

/-- The two lowest homogeneous jet identities give a quadratic relation
between the top coefficient and any linear combination of the other two. -/
theorem quadratic_initial_syzygy {R : Type*} [CommRing R]
    (u z a b c t : R) (hval : u^2*a + u*z*b + z^2*c = 0)
    (hslope : u*b + 2*z*c = 0) :
    u^2*(a+t*b) = (z^2-2*t*u*z)*c := by
  linear_combination hval + (t*u-z)*hslope

/-- In successive homogeneous degrees the top coefficient has two, then
one, powers of the local abscissa factor. -/
theorem quadratic_initial_top_divisibility {R : Type*} [CommRing R] [IsDomain R]
    {u z : R} (hu : Prime u) (hz : ¬ u ∣ z) (a b c a' b' c' : R)
    (hval : u^2*a + u*z*b + z^2*c = 0) (hslope : u*b + 2*z*c = 0)
    (hnext : u^2*a' + u*z*b' + z^2*c' = 0) :
    u^2 ∣ c ∧ u ∣ c' := by
  have hcop : ¬ u ∣ z^2 := fun h => hz (hu.dvd_of_dvd_pow h)
  constructor
  · apply hu.pow_dvd_of_dvd_mul_left 2 hcop
    exact ⟨a, by linear_combination -hval + z*hslope⟩
  · apply (hu.dvd_or_dvd (show u ∣ z^2*c' from
      ⟨-(u*a'+z*b'), by linear_combination hnext⟩)).resolve_left hcop

#print axioms quadratic_initial_syzygy
#print axioms quadratic_initial_top_divisibility
#print axioms pow_dvd_det_of_potential
#print axioms resultant_syzygy_eq
#print axioms resultant_syzygy_eq_of_dvd
#print axioms pow_dvd_resultant_asym_linear
#print axioms pow_dvd_lc_mul_resultant_of_syzygy
#print axioms pow_dvd_lc_mul_resultant_linear_of_syzygy
#print axioms X_pow_dvd_syzygy_of_contactOrderGE
#print axioms coeff_A_eq_zero_of_ge_degB
#print axioms X_pow_dvd_A_coeff_of_ge_degB
#print axioms slack_of_degB_eq_zero
#print axioms pow_dvd_discr_of_extra_vanishing
#print axioms pow_eight_dvd_discr_deg4
#print axioms pow_23_dvd_discr_deg6
#print axioms discr_eq_sign_mul_det_reducedDiscMatrix
#print axioms natDegree_discr_le_of_biWeightedDeg

end ArkLib.ProximityGap.Frontier.PrimeHDSyzygyResultant
