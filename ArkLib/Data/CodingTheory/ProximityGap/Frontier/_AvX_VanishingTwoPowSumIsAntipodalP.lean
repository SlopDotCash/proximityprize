/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import ArkLib.Data.CodingTheory.ProximityGap.LamLeungTwoPower

/-!
# Char-0 Lam–Leung, 2-power case: vanishing sums of `2^(k+1)`-th roots are antipodally paired

`VanishingTwoPowSumIsAntipodalPairing` is the canonical char-0 Lam–Leung statement specialized to
2-power order, packaged as a clean coefficient-symmetry theorem on a `ℕ`-weight vector.

Setup: `L` a `CharZero` field, `ζ` a primitive `2^(k+1)`-th root of unity, and a weight vector
`c : ℕ → ℕ` supported on `i < 2^(k+1)`.  If the weighted sum `∑_{i < 2^(k+1)} c i · ζ^i = 0`,
then `c i = c (i + 2^k)` for every `i < 2^k` — i.e. the vanishing sum is a `ℕ`-combination of
antipodal pairs `{ζ^i, -ζ^i}` (each `ζ^i + ζ^{i+2^k} = ζ^i - ζ^i = 0`).

Reference: Lam–Leung, *On vanishing sums of roots of unity*, J. Algebra 224 (2000) 91–109; the
2-power case (order `n = 2^a`, a single prime) has the trivial minimal-relation structure (the
only minimal vanishing block is the 2-gon `{ζ, -ζ}`).

Proof.  The weight vector defines a **rational** polynomial `Pℚ = ∑ (c i) · X^i ∈ ℚ[X]`,
vanishing at `ζ` (the hypothesis `hsum`).  Hence the minimal polynomial of `ζ` over `ℚ` divides
`Pℚ` (`minpoly.dvd`).  That minimal polynomial is the `2^{k+1}`-th cyclotomic polynomial, which
equals `X^{2^k} + 1` (`cyclotomic_two_pow`).  Mapping `(X^{2^k}+1) ∣ Pℚ` into `L[X]` gives
`(X^{2^k}+1) ∣ P` for the weight polynomial `P = Pℚ.map (algebraMap ℚ L)` over `L`.  Writing
`P = (X^{2^k}+1)·Q` with `deg Q < 2^k` and applying the in-tree engine `antipodal_coeff_of_dvd`
yields `P.coeff i = P.coeff (i + 2^k)`, i.e. `c i = c (i + 2^k)`.

All consumed pieces (`antipodal_coeff_of_dvd`) are in-tree and axiom-clean.  This is a char-0
fact (it does NOT close the open prize core); it discharges the named `char-0 Lam–Leung` /
`fiber_balanced` obligation cited by the No-Excess framework, packaged as a single citable
coefficient-symmetry theorem on a `ℕ`-weight vector.
-/

open Polynomial

namespace ArkLib.ProximityGap.LamLeung

/-- **The `2^(k+1)`-th cyclotomic polynomial is `X^{2^k} + 1`.**  Specialization of
`cyclotomic_prime_pow_eq_geom_sum` at `p = 2`: the `range 2` geometric sum is `1 + X^{2^k}`. -/
theorem cyclotomic_two_pow (R : Type*) [CommRing R] (k : ℕ) :
    cyclotomic (2 ^ (k + 1)) R = X ^ 2 ^ k + 1 := by
  rw [cyclotomic_prime_pow_eq_geom_sum (R := R) (p := 2) (n := k) Nat.prime_two]
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  simp [add_comm]

variable {L : Type*} [Field L] [CharZero L]

/-- **Char-0 Lam–Leung, 2-power coefficient form.**

Let `ζ : L` be a primitive `2^(k+1)`-th root of unity in a characteristic-zero field, and let
`c : ℕ → ℕ` be a weight vector supported on `i < 2^(k+1)` (i.e. `c i = 0` for `i ≥ 2^(k+1)`).
If the weighted sum of roots vanishes,
`∑_{i ∈ range (2^(k+1))} (c i : L) • ζ^i = 0`,
then the weights are antipodally equal:
`c i = c (i + 2^k)` for every `i < 2^k`.

Equivalently, the vanishing sum is a `ℕ`-combination of antipodal pairs `{ζ^i, -ζ^i}`. -/
theorem VanishingTwoPowSumIsAntipodalPairing {k : ℕ} {ζ : L}
    (hζ : IsPrimitiveRoot ζ (2 ^ (k + 1))) (c : ℕ → ℕ)
    (hsum : ∑ i ∈ Finset.range (2 ^ (k + 1)), (c i : L) • ζ ^ i = 0)
    {i : ℕ} (hi : i < 2 ^ k) :
    c i = c (i + 2 ^ k) := by
  have h2pos : 0 < 2 ^ (k + 1) := Nat.two_pow_pos _
  have hpow : (2 : ℕ) ^ k + 2 ^ k = 2 ^ (k + 1) := by ring
  have hih : i + 2 ^ k < 2 ^ (k + 1) := by omega
  -- The rational weight polynomial `Pℚ = ∑_j (c j) • X^j`.
  set Pℚ : ℚ[X] := ∑ j ∈ Finset.range (2 ^ (k + 1)), (C (c j : ℚ)) * X ^ j with hPℚ
  -- `aeval ζ Pℚ = 0`: the hypothesis `hsum`.
  have hroot : aeval ζ Pℚ = 0 := by
    rw [hPℚ, map_sum, ← hsum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_mul, aeval_C, aeval_X_pow, Algebra.smul_def]
    congr 1
    simp
  -- The minimal polynomial of `ζ` over `ℚ` is `X^{2^k}+1`.
  have hmin : minpoly ℚ ζ = (X ^ 2 ^ k + 1 : ℚ[X]) := by
    rw [← cyclotomic_eq_minpoly_rat hζ h2pos, cyclotomic_two_pow]
  have hdvdℚ : (X ^ 2 ^ k + 1 : ℚ[X]) ∣ Pℚ := by
    rw [← hmin]; exact minpoly.dvd ℚ ζ hroot
  -- Map into `L[X]`.
  set φ : ℚ →+* L := algebraMap ℚ L with hφ
  set P : L[X] := Pℚ.map φ with hP
  have hdvdL : (X ^ 2 ^ k + 1 : L[X]) ∣ P := by
    have h : ((X ^ 2 ^ k + 1 : ℚ[X]).map φ) ∣ (Pℚ.map φ) := Polynomial.map_dvd φ hdvdℚ
    simpa [hP] using h
  -- Coefficients of `P` recover the weights below `2^(k+1)`, and vanish above.
  have hPcoeff : ∀ j, P.coeff j = if j < 2 ^ (k + 1) then (c j : L) else 0 := by
    intro j
    rw [hP, hPℚ, Polynomial.map_sum, finset_sum_coeff]
    by_cases hj : j < 2 ^ (k + 1)
    · rw [if_pos hj, Finset.sum_eq_single j]
      · rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
          coeff_C_mul, coeff_X_pow, if_pos rfl, mul_one, hφ]; simp
      · intro b _ hb
        rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
          coeff_C_mul, coeff_X_pow, if_neg (by omega), mul_zero]
      · intro hjmem; exact absurd (Finset.mem_range.mpr hj) hjmem
    · rw [if_neg hj]
      apply Finset.sum_eq_zero
      intro b hb
      simp only [Finset.mem_range] at hb
      rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
        coeff_C_mul, coeff_X_pow, if_neg (by omega), mul_zero]
  -- `P.natDegree < 2^(k+1)`.
  have hdegP : P.natDegree < 2 ^ (k + 1) := by
    have hle : P.natDegree ≤ 2 ^ (k + 1) - 1 := by
      rw [natDegree_le_iff_coeff_eq_zero]
      intro N hN
      rw [hPcoeff, if_neg (by omega)]
    omega
  -- Write `P = (X^{2^k}+1) * Q`, bound `Q.natDegree < 2^k`, apply the engine.
  obtain ⟨Q, hQeq⟩ := hdvdL
  have hkpos : 0 < (2 : ℕ) ^ k := Nat.two_pow_pos _
  have hmonic : (X ^ 2 ^ k + 1 : L[X]).Monic := by
    apply monic_X_pow_add
    rw [degree_one]
    exact_mod_cast (Nat.cast_pos (α := WithBot ℕ)).mpr hkpos
  have hdegXh : (X ^ 2 ^ k + 1 : L[X]).natDegree = 2 ^ k := by
    have : (X ^ 2 ^ k + 1 : L[X]) = X ^ 2 ^ k + C 1 := by simp
    rw [this, natDegree_X_pow_add_C]
  -- The coefficient equality from the in-tree engine, IF `Q.natDegree < 2^k`.
  -- Bound `Q.natDegree`.
  have hQdeg : Q.natDegree < 2 ^ k := by
    rcases eq_or_ne Q 0 with hQ0 | hQ0
    · rw [hQ0]; simpa using hkpos
    · have hnd : P.natDegree = 2 ^ k + Q.natDegree := by
        rw [hQeq, hmonic.natDegree_mul' hQ0, hdegXh]
      omega
  -- Apply the engine: `P.coeff i = P.coeff (i + 2^k)`.
  have hkey : P.coeff i = P.coeff (i + 2 ^ k) := by
    rw [hQeq]
    exact antipodal_coeff_of_dvd Q hQdeg hi
  -- Translate coefficient equality back to the weight equality.
  rw [hPcoeff i, hPcoeff (i + 2 ^ k), if_pos (by omega), if_pos hih] at hkey
  exact_mod_cast hkey

#print axioms cyclotomic_two_pow
#print axioms VanishingTwoPowSumIsAntipodalPairing

end ArkLib.ProximityGap.LamLeung
