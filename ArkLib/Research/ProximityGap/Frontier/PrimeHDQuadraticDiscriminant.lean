/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Tactic

/-!
# Quadratic Discriminant & Universal Weighted Resultant Valuations (`PrimeHDQuadraticDiscriminant`)

Characteristic-free (universal over **every** commutative ring `R`, zero `IsDomain` needed for the
core divisibility theorems!) quadratic discriminant and universal weighted Sylvester resultant
valuation bounds for bivariate polynomials `BiPoly A = A[X][Y]`, supporting the prime-field
hidden-derivative list-decoding & MCA pivot-breaking engines (`#210`, `#216`, `#228`, `#229`).

## Main statements

1. **Universal Matrix Dual-Potential Engine (`pow_dvd_det_of_potential`):**
   For any `n × n` matrix `M` over any commutative ring `R`, any `t : R`, and integer row/column
   potentials `p, q : Fin n → ℤ` with `(N : ℤ) ≤ ∑ i, p i + ∑ j, q j` and
   `M i j = 0 ∨ t ^ (p i + q j).toNat ∣ M i j`, we have `t ^ N ∣ M.det`.
2. **Quadratic Discriminant Valuation Theorem (`discOrdQuad`, `pow_dvd_discr_of_coeff_dvd`):**
   For any `f : R[Y]` of `Y`-degree `d = f.natDegree ≥ 2` and any `m : ℕ` with
   `∀ j, t ^ (m - j) ∣ f.coeff j`:
   - `t ^ (m * (m - 1)) ∣ f.discr` whenever `m ≤ d`,
   - `t ^ ((2 * d - 2) * m - d * (d - 1)) ∣ f.discr` whenever `m > d`.
3. **Exact `+1` Boost under `a_{0, m} = 0` (`discOrdQuadBoost`, `pow_dvd_discr_boost_of_coeff_dvd`):**
   If additionally `t ∣ f.coeff m` (`a_{0, m} = 0`), then for ALL `1 ≤ m < d`:
   - `t ^ (m * (m - 1) + 1) ∣ f.discr`.
4. **Corrected Universal Weighted Resultant Valuation (`resOrdUniv`, `pow_dvd_resultant_univ`):**
   Incorporating the `#228` soundness correction for `m > max dA dB`: with `a = (m - dA)^+`,
   `b = (m - dB)^+`:
   - `resOrdUniv dA dB m = a * dB + b * dA + (m - a) * (m - b)`,
   - equals `m^2` when `m ≤ min dA dB` and `(dA + dB) * m - dA * dB` otherwise (strictly beating
     `m^2` by `(dA - m) * (m - dB)` when `dB < m < dA`, and strictly `< m^2` when `m > max dA dB`),
   - `t ^ resOrdUniv dA dB m ∣ Polynomial.resultant A B dA dB` over EVERY commutative ring `R`.
5. **Bivariate Shift Covariance & Distinct-Site Global Sum Bounds on `BiPoly K = K[X][Y]`:**
   - `discr_shiftBi`: `(shiftBi x₀ y₀ P).discr = P.discr.comp (C x₀ + X)` in EVERY characteristic
     (including `char K ∣ P.natDegree`!).
   - `X_sub_C_pow_dvd_discr_of_biMultGE`, `X_sub_C_pow_dvd_discr_boost_of_biMultGE`,
     `X_sub_C_pow_dvd_resultant_univ_of_biMultGE`,
     `X_sub_C_pow_dvd_leadingCoeff_of_biMultGE`, `X_sub_C_pow_dvd_leadingCoeff_boost_of_biMultGE`.
   - Global distinct-site sum bounds `sum_discOrdQuad_le_natDegree_discr`,
     `sum_discOrdQuadBoost_le_natDegree_discr`, `sum_resOrdUniv_le_natDegree_resultant`,
     `sum_leadingCoeffOrd_le_natDegree_leadingCoeff`,
     `sum_leadingCoeffOrdBoost_le_natDegree_leadingCoeff`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace ArkLib.ProximityGap.Frontier.PrimeHDQuadraticDiscriminant

open Polynomial Matrix
open scoped BigOperators

/-! ### Part 1: Universal Matrix Dual-Potential Divisibility Engine -/

section PotentialEngine

/-- Universal dual-potential divisibility theorem for determinants over ANY commutative ring `R`:
if every nonzero entry `M i j` is divisible by `t ^ (p i + q j).toNat`, then `t ^ N ∣ M.det`
for every `N ≤ ∑ i, p i + ∑ j, q j`. -/
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
          _ = ∑ i : Fin n, p (σ i) + ∑ i : Fin n, q i := by
              rw [Equiv.sum_comp σ p]
          _ = ∑ i : Fin n, (p (σ i) + q i) := (Finset.sum_add_distrib).symm
          _ ≤ ∑ i : Fin n, ((p (σ i) + q i).toNat : ℤ) :=
              Finset.sum_le_sum fun i _ => by omega
          _ = ((∑ i : Fin n, (p (σ i) + q i).toNat : ℕ) : ℤ) := by push_cast; rfl
      exact Int.ofNat_le.mp hcast
    exact (pow_dvd_pow t hN_le).trans hdvd_prod

private theorem card_filter_lt_fin (n k : ℕ) (hk : k ≤ n) :
    (Finset.univ.filter (fun i : Fin n => i.val < k)).card = k := by
  have hbij : (Finset.univ.filter (fun i : Fin n => i.val < k)).card =
      (Finset.univ : Finset (Fin k)).card := by
    refine Finset.card_bij (fun i hi => ⟨i.val, (Finset.mem_filter.mp hi).2⟩) ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro a _ b _ hab
      exact Fin.ext (by simpa using congrArg Fin.val hab)
    · intro j _
      exact ⟨⟨j.val, j.isLt.trans_le hk⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, j.isLt⟩, rfl⟩
  rw [hbij, Finset.card_univ, Fintype.card_fin]

/-- Exact triangular sum of `max 0 (k - i)` over `i : Fin n` whenever `k ≤ n`. -/
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

private theorem sum_fin_split (a b : ℕ) (g : Fin (a + b) → ℤ) :
    ∑ j : Fin (a + b), g j =
      (∑ j : Fin a, g (Fin.castAdd b j)) + (∑ k : Fin b, g (Fin.natAdd a k)) := by
  rw [← Fin.sum_univ_add]

end PotentialEngine

/-! ### Part 2: Quadratic Discriminant Valuation & Exact `+1` Boost under `a_{0, m} = 0` -/

section DiscriminantValuation

/-- Quadratic discriminant valuation lower bound for `Y`-degree `d` and bivariate multiplicity `m`:
- `m * (m - 1)` when `m ≤ d`,
- `(2 * d - 2) * m - d * (d - 1)` when `m > d`. -/
def discOrdQuad (d m : ℕ) : ℕ :=
  if m ≤ d then m * (m - 1) else (2 * d - 2) * m - d * (d - 1)

/-- Strict `+1`-boosted quadratic discriminant bound under `a_{0, m} = 0` (`t ∣ f.coeff m`):
adds `+1` whenever `1 ≤ m < d`. -/
def discOrdQuadBoost (d m : ℕ) : ℕ :=
  if 1 ≤ m ∧ m < d then m * (m - 1) + 1 else discOrdQuad d m

/-- Helper: entrywise characterization of `f.sylvesterDeriv` for `d = f.natDegree ≥ 2`. -/
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
      · right
        refine ⟨hmem.1, ?_⟩
        conv_lhs => rw [hjeq]
        rw [Fin.addCases_left, ite_eq_left hmem]
      · left
        conv_lhs => rw [hjeq]
        rw [Fin.addCases_left, ite_eq_right hmem]
    · right
      have hjge : f.natDegree - 1 ≤ j.val := by omega
      refine ⟨hjge, ?_⟩
      have hklt : j.val - (f.natDegree - 1) < f.natDegree := by have := j.isLt; omega
      have hjeq : j = Fin.natAdd (f.natDegree - 1) ⟨j.val - (f.natDegree - 1), hklt⟩ :=
        Fin.ext (by dsimp; omega)
      by_cases hmem : i.val ∈ Set.Icc (j.val - (f.natDegree - 1))
          (j.val - (f.natDegree - 1) + (f.natDegree - 1))
      · right
        refine ⟨hmem.1, ?_⟩
        conv_lhs => rw [hjeq]
        rw [Fin.addCases_right, ite_eq_left hmem, Polynomial.coeff_derivative]
        dsimp only
        rw [mul_comm]; push_cast; rfl
      · left
        conv_lhs => rw [hjeq]
        rw [Fin.addCases_right, ite_eq_right hmem]

/-- High-multiplicity regime (`m ≥ d`, `d ≥ 2`):
`t ^ ((2 * d - 2) * m - d * (d - 1)) ∣ f.discr` over ANY commutative ring `R`. -/
theorem pow_dvd_discr_of_ge {R : Type*} [CommRing R]
    (f : R[X]) (hd : 2 ≤ f.natDegree) (t : R) (m : ℕ) (hm : f.natDegree ≤ m)
    (hord : ∀ j, t ^ (m - j) ∣ f.coeff j) :
    t ^ ((2 * f.natDegree - 2) * m - f.natDegree * (f.natDegree - 1)) ∣ f.discr := by
  rw [Polynomial.discr]
  apply dvd_mul_of_dvd_left
  let d := f.natDegree
  let p : Fin (d - 1 + d) → ℤ := fun i =>
    -(i.val : ℤ) - if i.val = 2 * d - 2 then ((m : ℤ) - d) else 0
  let q : Fin (d - 1 + d) → ℤ := fun j =>
    (j.val : ℤ) + if j.val < d - 1 then (m : ℤ) else ((m : ℤ) - d)
  apply pow_dvd_det_of_potential f.sylvesterDeriv t p q
  · -- Sum of potentials equals `(2 * d - 2) * m - d * (d - 1)` identically!
    have hp_sum : ∑ i : Fin (d - 1 + d), p i =
        -(∑ i : Fin (d - 1 + d), (i.val : ℤ)) - ((m : ℤ) - d) := by
      simp only [p, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
      congr 1
      rw [Finset.sum_eq_single ⟨2 * d - 2, by omega⟩]
      · simp
      · intro i _ hne
        have : i.val ≠ 2 * d - 2 := fun h => hne (Fin.ext h)
        simp [this]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hq_sum : ∑ j : Fin (d - 1 + d), q j =
        (∑ j : Fin (d - 1 + d), (j.val : ℤ)) +
          (((d - 1 : ℕ) : ℤ) * m + (d : ℤ) * ((m : ℤ) - d)) := by
      simp only [q, Finset.sum_add_distrib]
      congr 1
      rw [sum_fin_split (d - 1) d]
      have hL : ∑ j : Fin (d - 1),
          (if (Fin.castAdd d j).val < d - 1 then (m : ℤ) else ((m : ℤ) - d)) =
          ((d - 1 : ℕ) : ℤ) * m := by
        have hlt : ∀ j : Fin (d - 1), (Fin.castAdd d j).val < d - 1 := fun j => j.isLt
        simp_rw [ite_eq_left (hlt _)]
        simp
      have hR : ∑ k : Fin d,
          (if (Fin.natAdd (d - 1) k).val < d - 1 then (m : ℤ) else ((m : ℤ) - d)) =
          (d : ℤ) * ((m : ℤ) - d) := by
        have hge : ∀ k : Fin d, ¬ (Fin.natAdd (d - 1) k).val < d - 1 := fun k => by dsimp; omega
        simp_rw [ite_eq_right (hge _)]
        simp [mul_sub]
      rw [hL, hR]
    rw [hp_sum, hq_sum]
    have hge1 : d * (d - 1) ≤ (2 * d - 2) * m := by
      have h1 : 2 * d - 2 = 2 * (d - 1) := by omega
      rw [h1]; nlinarith
    change (((2 * d - 2) * m - d * (d - 1) : ℕ) : ℤ) ≤ _
    zify [hge1, show 1 ≤ d by omega, show 2 ≤ 2 * d by omega]
    linarith
  · -- Entrywise divisibility check
    intro i j
    rcases sylvesterDeriv_entry_cases f hd i j with
      ⟨hi_eq, ⟨hj_eq, hval⟩ | ⟨hj_eq, hval⟩ | hzero⟩ |
      ⟨hi_lt, ⟨hj_lt, hzero | ⟨hle, hval⟩⟩ | ⟨hj_ge, hzero | ⟨hle, hval⟩⟩⟩
    · right; rw [hval]
      have hpq : (p i + q j).toNat = 0 := by
        dsimp only [p, q]
        rw [ite_eq_left hi_eq, ite_eq_left (by omega : j.val < d - 1)]; omega
      rw [hpq, pow_zero]
    · right; rw [hval]
      have hpq : (p i + q j).toNat = 0 := by
        dsimp only [p, q]
        rw [ite_eq_left hi_eq, ite_eq_right (by omega : ¬ j.val < d - 1)]; omega
      rw [hpq, pow_zero]; exact one_dvd _
    · left; exact hzero
    · left; exact hzero
    · right; rw [hval]
      have hpq : (p i + q j).toNat ≤ m - (i.val - j.val) := by
        dsimp only [p, q]
        rw [ite_eq_right (by omega : i.val ≠ 2 * d - 2), ite_eq_left hj_lt]; omega
      exact (pow_dvd_pow t hpq).trans (hord (i.val - j.val))
    · left; exact hzero
    · right; rw [hval]
      have hpq : (p i + q j).toNat ≤ m - (i.val - (j.val - (d - 1)) + 1) := by
        dsimp only [p, q]
        rw [ite_eq_right (by omega : i.val ≠ 2 * d - 2),
          ite_eq_right (by omega : ¬ j.val < d - 1)]; omega
      exact dvd_mul_of_dvd_right ((pow_dvd_pow t hpq).trans (hord _)) _

/-- Low-multiplicity regime (`m ≤ d`, `d ≥ 2`):
`t ^ (m * (m - 1)) ∣ f.discr` over ANY commutative ring `R`. -/
theorem pow_dvd_discr_of_le {R : Type*} [CommRing R]
    (f : R[X]) (hd : 2 ≤ f.natDegree) (t : R) (m : ℕ) (hm : m ≤ f.natDegree)
    (hord : ∀ j, t ^ (m - j) ∣ f.coeff j) :
    t ^ (m * (m - 1)) ∣ f.discr := by
  by_cases hm0 : m = 0
  · subst hm0; simp
  have hm1 : 1 ≤ m := Nat.pos_of_ne_zero hm0
  rw [Polynomial.discr]
  apply dvd_mul_of_dvd_left
  let d := f.natDegree
  let p : Fin (d - 1 + d) → ℤ := fun i => max 0 (((2 * m - 2 : ℕ) : ℤ) - i.val)
  let q : Fin (d - 1 + d) → ℤ := fun j =>
    if j.val < d - 1 then -max 0 (((m - 2 : ℕ) : ℤ) - j.val)
    else -max 0 (((m - 1 : ℕ) : ℤ) - ((j.val - (d - 1) : ℕ) : ℤ))
  apply pow_dvd_det_of_potential f.sylvesterDeriv t p q
  · -- Exact potential sum `= m * (m - 1)` via `two_mul_sum_max_sub`!
    have hp2 := two_mul_sum_max_sub (d - 1 + d) (2 * m - 2) (by omega)
    have hq_split : ∑ j : Fin (d - 1 + d), q j =
        -(∑ j : Fin (d - 1), max (0 : ℤ) (((m - 2 : ℕ) : ℤ) - j.val)) -
        (∑ k : Fin d, max (0 : ℤ) (((m - 1 : ℕ) : ℤ) - k.val)) := by
      rw [sum_fin_split (d - 1) d]
      have hL : ∑ j : Fin (d - 1), q (Fin.castAdd d j) =
          -(∑ j : Fin (d - 1), max (0 : ℤ) (((m - 2 : ℕ) : ℤ) - j.val)) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        dsimp only [q]; rw [ite_eq_left (by dsimp; omega)]; simp
      have hR : ∑ k : Fin d, q (Fin.natAdd (d - 1) k) =
          -(∑ k : Fin d, max (0 : ℤ) (((m - 1 : ℕ) : ℤ) - k.val)) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        dsimp only [q]
        rw [ite_eq_right (by dsimp; omega)]
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
        2 * (((m * (m - 1) : ℕ) : ℤ)) := by
      rw [hq_split]
      have hp' : 2 * ∑ i : Fin (d - 1 + d), p i =
          (((2 * m - 2 : ℕ) : ℤ) * (((2 * m - 2 : ℕ) : ℤ) + 1)) := hp2
      zify [hm1, show 2 ≤ 2 * m by omega] at hp' hq2 ⊢
      nlinarith only [hp', hq1, hq1_id, hq2]
    linarith
  · -- Entrywise divisibility check
    intro i j
    rcases sylvesterDeriv_entry_cases f hd i j with
      ⟨hi_eq, ⟨hj_eq, hval⟩ | ⟨hj_eq, hval⟩ | hzero⟩ |
      ⟨hi_lt, ⟨hj_lt, hzero | ⟨hle, hval⟩⟩ | ⟨hj_ge, hzero | ⟨hle, hval⟩⟩⟩
    · right; rw [hval]
      have hpq : (p i + q j).toNat = 0 := by
        dsimp only [p, q]; rw [ite_eq_left (by omega : j.val < d - 1)]; omega
      rw [hpq, pow_zero]
    · right; rw [hval]
      have hpq : (p i + q j).toNat = 0 := by
        dsimp only [p, q]; rw [ite_eq_right (by omega : ¬ j.val < d - 1)]; omega
      rw [hpq, pow_zero]; exact one_dvd _
    · left; exact hzero
    · left; exact hzero
    · right; rw [hval]
      have hpq : (p i + q j).toNat ≤ m - (i.val - j.val) := by
        dsimp only [p, q]; rw [ite_eq_left hj_lt]; omega
      exact (pow_dvd_pow t hpq).trans (hord (i.val - j.val))
    · left; exact hzero
    · right; rw [hval]
      have hpq : (p i + q j).toNat ≤ m - (i.val - (j.val - (d - 1)) + 1) := by
        dsimp only [p, q]; rw [ite_eq_right (by omega : ¬ j.val < d - 1)]; omega
      exact dvd_mul_of_dvd_right ((pow_dvd_pow t hpq).trans (hord _)) _

/-- **Strict `+1`-Boosted Quadratic Discriminant Theorem (`#210`):**
When `1 ≤ m < d = f.natDegree` and additionally `t ∣ f.coeff m` (i.e. `a_{0, m} = 0`), bumping the
single row potential `p(2m - 2)` from `0` to `1` proves `t ^ (m * (m - 1) + 1) ∣ f.discr` over
**EVERY commutative ring `R`**! -/
theorem pow_dvd_discr_boost_of_lt {R : Type*} [CommRing R]
    (f : R[X]) (hd : 2 ≤ f.natDegree) (t : R) (m : ℕ) (hm1 : 1 ≤ m) (hmlt : m < f.natDegree)
    (hord : ∀ j, t ^ (m - j) ∣ f.coeff j)
    (ha0m : t ∣ f.coeff m) :
    t ^ (m * (m - 1) + 1) ∣ f.discr := by
  rw [Polynomial.discr]
  apply dvd_mul_of_dvd_left
  let d := f.natDegree
  let p0 : Fin (d - 1 + d) → ℤ := fun i => max 0 (((2 * m - 2 : ℕ) : ℤ) - i.val)
  let p : Fin (d - 1 + d) → ℤ := fun i => p0 i + if i.val = 2 * m - 2 then 1 else 0
  let q : Fin (d - 1 + d) → ℤ := fun j =>
    if j.val < d - 1 then -max 0 (((m - 2 : ℕ) : ℤ) - j.val)
    else -max 0 (((m - 1 : ℕ) : ℤ) - ((j.val - (d - 1) : ℕ) : ℤ))
  apply pow_dvd_det_of_potential f.sylvesterDeriv t p q
  · -- Sum is `∑ p0 + 1 + ∑ q = m * (m - 1) + 1`!
    have hp_bump : ∑ i : Fin (d - 1 + d), p i = (∑ i : Fin (d - 1 + d), p0 i) + 1 := by
      simp only [p, Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_eq_single ⟨2 * m - 2, by omega⟩]
      · simp
      · intro i _ hne
        have : i.val ≠ 2 * m - 2 := fun h => hne (Fin.ext h)
        simp [this]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hp2 := two_mul_sum_max_sub (d - 1 + d) (2 * m - 2) (by omega)
    have hq_split : ∑ j : Fin (d - 1 + d), q j =
        -(∑ j : Fin (d - 1), max (0 : ℤ) (((m - 2 : ℕ) : ℤ) - j.val)) -
        (∑ k : Fin d, max (0 : ℤ) (((m - 1 : ℕ) : ℤ) - k.val)) := by
      rw [sum_fin_split (d - 1) d]
      have hL : ∑ j : Fin (d - 1), q (Fin.castAdd d j) =
          -(∑ j : Fin (d - 1), max (0 : ℤ) (((m - 2 : ℕ) : ℤ) - j.val)) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        dsimp only [q]; rw [ite_eq_left (by dsimp; omega)]; simp
      have hR : ∑ k : Fin d, q (Fin.natAdd (d - 1) k) =
          -(∑ k : Fin d, max (0 : ℤ) (((m - 1 : ℕ) : ℤ) - k.val)) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        dsimp only [q]
        rw [ite_eq_right (by dsimp; omega)]
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
        2 * (((m * (m - 1) + 1 : ℕ) : ℤ)) := by
      rw [hp_bump, hq_split]
      have hp' : 2 * ∑ i : Fin (d - 1 + d), p0 i =
          (((2 * m - 2 : ℕ) : ℤ) * (((2 * m - 2 : ℕ) : ℤ) + 1)) := hp2
      zify [hm1, show 2 ≤ 2 * m by omega] at hp' hq2 ⊢
      nlinarith only [hp', hq1, hq1_id, hq2]
    linarith
  · -- Entrywise divisibility check (only row `i = 2m - 2` uses `ha0m`!)
    intro i j
    rcases sylvesterDeriv_entry_cases f hd i j with
      ⟨hi_eq, ⟨hj_eq, hval⟩ | ⟨hj_eq, hval⟩ | hzero⟩ |
      ⟨hi_lt, ⟨hj_lt, hzero | ⟨hle, hval⟩⟩ | ⟨hj_ge, hzero | ⟨hle, hval⟩⟩⟩
    · right; rw [hval]
      have hpq : (p i + q j).toNat = 0 := by
        dsimp only [p, p0, q]
        rw [ite_eq_right (by omega : i.val ≠ 2 * m - 2),
          ite_eq_left (by omega : j.val < d - 1)]; omega
      rw [hpq, pow_zero]
    · right; rw [hval]
      have hpq : (p i + q j).toNat = 0 := by
        dsimp only [p, p0, q]
        rw [ite_eq_right (by omega : i.val ≠ 2 * m - 2),
          ite_eq_right (by omega : ¬ j.val < d - 1)]; omega
      rw [hpq, pow_zero]; exact one_dvd _
    · left; exact hzero
    · left; exact hzero
    · right; rw [hval]
      by_cases hi_b : i.val = 2 * m - 2
      · by_cases hjm : i.val - j.val = m
        · have hpq : (p i + q j).toNat ≤ 1 := by
            dsimp only [p, p0, q]; rw [ite_eq_left hi_b, ite_eq_left hj_lt]; omega
          rw [hjm]
          exact (pow_dvd_pow t hpq).trans (by simpa using ha0m)
        · have hpq : (p i + q j).toNat ≤ m - (i.val - j.val) := by
            dsimp only [p, p0, q]; rw [ite_eq_left hi_b, ite_eq_left hj_lt]; omega
          exact (pow_dvd_pow t hpq).trans (hord (i.val - j.val))
      · have hpq : (p i + q j).toNat ≤ m - (i.val - j.val) := by
          dsimp only [p, p0, q]; rw [ite_eq_right hi_b, ite_eq_left hj_lt]; omega
        exact (pow_dvd_pow t hpq).trans (hord (i.val - j.val))
    · left; exact hzero
    · right; rw [hval]
      by_cases hi_b : i.val = 2 * m - 2
      · by_cases hkm : i.val - (j.val - (d - 1)) + 1 = m
        · have hpq : (p i + q j).toNat ≤ 1 := by
            dsimp only [p, p0, q]
            rw [ite_eq_left hi_b, ite_eq_right (by omega : ¬ j.val < d - 1)]; omega
          rw [hkm]
          exact dvd_mul_of_dvd_right ((pow_dvd_pow t hpq).trans (by simpa using ha0m)) _
        · have hpq : (p i + q j).toNat ≤ m - (i.val - (j.val - (d - 1)) + 1) := by
            dsimp only [p, p0, q]
            rw [ite_eq_left hi_b, ite_eq_right (by omega : ¬ j.val < d - 1)]; omega
          exact dvd_mul_of_dvd_right ((pow_dvd_pow t hpq).trans (hord _)) _
      · have hpq : (p i + q j).toNat ≤ m - (i.val - (j.val - (d - 1)) + 1) := by
          dsimp only [p, p0, q]
          rw [ite_eq_right hi_b, ite_eq_right (by omega : ¬ j.val < d - 1)]; omega
        exact dvd_mul_of_dvd_right ((pow_dvd_pow t hpq).trans (hord _)) _

/-- **Master Quadratic Discriminant Valuation Theorem (all `d ≥ 2, m : ℕ`, any commutative ring):**
If `∀ j, t ^ (m - j) ∣ f.coeff j`, then `t ^ discOrdQuad f.natDegree m ∣ f.discr`. -/
theorem pow_dvd_discr_of_coeff_dvd {R : Type*} [CommRing R]
    (f : R[X]) (hd : 2 ≤ f.natDegree) (t : R) (m : ℕ)
    (hord : ∀ j, t ^ (m - j) ∣ f.coeff j) :
    t ^ discOrdQuad f.natDegree m ∣ f.discr := by
  unfold discOrdQuad
  split_ifs with hle
  · exact pow_dvd_discr_of_le f hd t m hle hord
  · exact pow_dvd_discr_of_ge f hd t m (by omega) hord

/-- **Master `+1`-Boosted Quadratic Discriminant Theorem (`a_{0, m} = 0`):**
If `∀ j, t ^ (m - j) ∣ f.coeff j` and `t ∣ f.coeff m`, then
`t ^ discOrdQuadBoost f.natDegree m ∣ f.discr`. -/
theorem pow_dvd_discr_boost_of_coeff_dvd {R : Type*} [CommRing R]
    (f : R[X]) (hd : 2 ≤ f.natDegree) (t : R) (m : ℕ)
    (hord : ∀ j, t ^ (m - j) ∣ f.coeff j)
    (ha0m : t ∣ f.coeff m) :
    t ^ discOrdQuadBoost f.natDegree m ∣ f.discr := by
  unfold discOrdQuadBoost
  split_ifs with hlt
  · exact pow_dvd_discr_boost_of_lt f hd t m hlt.1 hlt.2 hord ha0m
  · exact pow_dvd_discr_of_coeff_dvd f hd t m hord

end DiscriminantValuation

/-! ### Part 3: Corrected Universal Weighted Resultant Valuation (`#228` Soundness-Fixed) -/

section UniversalResultant

/-- Corrected universal Sylvester resultant valuation (`#228`):
for `a = (m - dA)^+`, `b = (m - dB)^+`:
`resOrdUniv dA dB m = a * dB + b * dA + (m - a) * (m - b)`.
Equals `m^2` when `m ≤ min dA dB`, and `(dA + dB) * m - dA * dB` whenever `m ≥ min dA dB`
(fixing `#210`'s `max(m^2, ·)` overclaim in the regime `m > max dA dB`). -/
def resOrdUniv (dA dB m : ℕ) : ℕ :=
  let a := m - dA
  let b := m - dB
  a * dB + b * dA + (m - a) * (m - b)

theorem resOrdUniv_eq_sq_of_le {dA dB m : ℕ} (hA : m ≤ dA) (hB : m ≤ dB) :
    resOrdUniv dA dB m = m * m := by
  unfold resOrdUniv
  have ha : m - dA = 0 := Nat.sub_eq_zero_of_le hA
  have hb : m - dB = 0 := Nat.sub_eq_zero_of_le hB
  simp [ha, hb]

theorem resOrdUniv_eq_linear_of_ge {dA dB m : ℕ} (h : dA ≤ m ∨ dB ≤ m) :
    resOrdUniv dA dB m = (dA + dB) * m - dA * dB := by
  unfold resOrdUniv
  rcases h with hA | hB
  · by_cases hB : dB ≤ m
    · zify [hA, hB, show dA * dB ≤ (dA + dB) * m by nlinarith,
        show m - dA ≤ m by omega, show m - dB ≤ m by omega]
      ring
    · have hb : m - dB = 0 := Nat.sub_eq_zero_of_le (by omega)
      simp only [hb, zero_mul, Nat.sub_zero, add_zero]
      zify [hA, show dA * dB ≤ (dA + dB) * m by nlinarith, show m - dA ≤ m by omega]
      ring
  · by_cases hA : dA ≤ m
    · zify [hA, hB, show dA * dB ≤ (dA + dB) * m by nlinarith,
        show m - dA ≤ m by omega, show m - dB ≤ m by omega]
      ring
    · have ha : m - dA = 0 := Nat.sub_eq_zero_of_le (by omega)
      simp only [ha, zero_mul, Nat.sub_zero, zero_add]
      zify [hB, show dA * dB ≤ (dA + dB) * m by nlinarith, show m - dB ≤ m by omega]
      ring

/-- In the intermediate regime `dB < m < dA`, `resOrdUniv` strictly beats `m^2` by
`(dA - m) * (m - dB) > 0` (e.g. `10 > 9` at `dA = 4, dB = 2, m = 3`). -/
theorem resOrdUniv_eq_sq_add_excess {dA dB m : ℕ} (hB : dB ≤ m) (hA : m ≤ dA) :
    resOrdUniv dA dB m = m * m + (dA - m) * (m - dB) := by
  rw [resOrdUniv_eq_linear_of_ge (Or.inr hB)]
  zify [hA, hB, show dA * dB ≤ (dA + dB) * m by nlinarith]
  ring

/-- Soundness guard (`#228`): when `m > dA` AND `m > dB`, `resOrdUniv dA dB m < m * m`! -/
theorem resOrdUniv_lt_sq_of_gt {dA dB m : ℕ} (hA : dA < m) (hB : dB < m) :
    resOrdUniv dA dB m < m * m := by
  rw [resOrdUniv_eq_linear_of_ge (Or.inl (le_of_lt hA))]
  have h1 : dA * dB ≤ (dA + dB) * m := by nlinarith
  zify [h1]
  nlinarith

/-- **Corrected Universal Weighted Resultant Valuation Theorem (any commutative ring `R`):**
If `∀ j, t ^ (m - j) ∣ A.coeff j` and `∀ j, t ^ (m - j) ∣ B.coeff j`, then
`t ^ resOrdUniv dA dB m ∣ Polynomial.resultant A B dA dB`. -/
theorem pow_dvd_resultant_univ {R : Type*} [CommRing R]
    (A B : R[X]) (dA dB m : ℕ) (t : R)
    (hA : ∀ j, t ^ (m - j) ∣ A.coeff j)
    (hB : ∀ j, t ^ (m - j) ∣ B.coeff j) :
    t ^ resOrdUniv dA dB m ∣ Polynomial.resultant A B dA dB := by
  rw [Polynomial.resultant]
  by_cases hle : m ≤ dA ∧ m ≤ dB
  · rw [resOrdUniv_eq_sq_of_le hle.1 hle.2]
    by_cases hm0 : m = 0
    · subst hm0; simp
    have hm1 : 1 ≤ m := Nat.pos_of_ne_zero hm0
    let p : Fin (dA + dB) → ℤ := fun i => max 0 (((2 * m - 1 : ℕ) : ℤ) - i.val)
    let q : Fin (dA + dB) → ℤ := fun j =>
      if j.val < dA then -max 0 (((m - 1 : ℕ) : ℤ) - j.val)
      else -max 0 (((m - 1 : ℕ) : ℤ) - ((j.val - dA : ℕ) : ℤ))
    apply pow_dvd_det_of_potential (A.sylvester B dA dB) t p q
    · have hp2 := two_mul_sum_max_sub (dA + dB) (2 * m - 1) (by omega)
      have hq_split : ∑ j : Fin (dA + dB), q j =
          -(∑ j : Fin dA, max (0 : ℤ) (((m - 1 : ℕ) : ℤ) - j.val)) -
          (∑ k : Fin dB, max (0 : ℤ) (((m - 1 : ℕ) : ℤ) - k.val)) := by
        rw [sum_fin_split dA dB]
        have hL : ∑ j : Fin dA, q (Fin.castAdd dB j) =
            -(∑ j : Fin dA, max (0 : ℤ) (((m - 1 : ℕ) : ℤ) - j.val)) := by
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          dsimp only [q]; rw [ite_eq_left (by dsimp; omega)]; simp
        have hR : ∑ k : Fin dB, q (Fin.natAdd dA k) =
            -(∑ k : Fin dB, max (0 : ℤ) (((m - 1 : ℕ) : ℤ) - k.val)) := by
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun k _ => ?_
          dsimp only [q]; rw [ite_eq_right (by dsimp; omega)]
          have : (Fin.natAdd dA k).val - dA = k.val := by dsimp; omega
          rw [this]
        rw [hL, hR]; ring
      have hq1 := two_mul_sum_max_sub dA (m - 1) (by omega)
      have hq2 := two_mul_sum_max_sub dB (m - 1) (by omega)
      have hcalc : 2 * (∑ i : Fin (dA + dB), p i + ∑ j : Fin (dA + dB), q j) =
          2 * (((m * m : ℕ) : ℤ)) := by
        rw [hq_split]
        have hp' : 2 * ∑ i : Fin (dA + dB), p i =
            (((2 * m - 1 : ℕ) : ℤ) * (((2 * m - 1 : ℕ) : ℤ) + 1)) := hp2
        zify [hm1, show 1 ≤ 2 * m by omega] at hp' hq1 hq2 ⊢
        nlinarith only [hp', hq1, hq2]
      linarith
    · intro i j
      rw [Polynomial.sylvester, Matrix.of_apply]
      by_cases hj : j.val < dA
      · have hjeq : j = Fin.castAdd dB ⟨j.val, hj⟩ := Fin.ext rfl
        by_cases hmem : i.val ∈ Set.Icc j.val (j.val + dB)
        · right
          have hval : (j.addCases
              (fun j₁ => if i.val ∈ Set.Icc (j₁ : ℕ) (j₁ + dB) then B.coeff (i - j₁) else 0)
              (fun j₁ => if i.val ∈ Set.Icc (j₁ : ℕ) (j₁ + dA) then A.coeff (i - j₁) else 0)) =
              B.coeff (i.val - j.val) := by
            conv_lhs => rw [hjeq]
            rw [Fin.addCases_left, ite_eq_left hmem]
          rw [hval]
          have hle_ij : j.val ≤ i.val := hmem.1
          have hpq : (p i + q j).toNat ≤ m - (i.val - j.val) := by
            dsimp only [p, q]; rw [ite_eq_left hj]; omega
          exact (pow_dvd_pow t hpq).trans (hB (i.val - j.val))
        · left
          conv_lhs => rw [hjeq]
          rw [Fin.addCases_left, ite_eq_right hmem]
      · have hklt : j.val - dA < dB := by have := j.isLt; omega
        have hjeq : j = Fin.natAdd dA ⟨j.val - dA, hklt⟩ := Fin.ext (by dsimp; omega)
        by_cases hmem : i.val ∈ Set.Icc (j.val - dA) (j.val - dA + dA)
        · right
          have hval : (j.addCases
              (fun j₁ => if i.val ∈ Set.Icc (j₁ : ℕ) (j₁ + dB) then B.coeff (i - j₁) else 0)
              (fun j₁ => if i.val ∈ Set.Icc (j₁ : ℕ) (j₁ + dA) then A.coeff (i - j₁) else 0)) =
              A.coeff (i.val - (j.val - dA)) := by
            conv_lhs => rw [hjeq]
            rw [Fin.addCases_right, ite_eq_left hmem]
          rw [hval]
          have hle_ik : j.val - dA ≤ i.val := hmem.1
          have hpq : (p i + q j).toNat ≤ m - (i.val - (j.val - dA)) := by
            dsimp only [p, q]; rw [ite_eq_right hj]; omega
          exact (pow_dvd_pow t hpq).trans (hA (i.val - (j.val - dA)))
        · left
          conv_lhs => rw [hjeq]
          rw [Fin.addCases_right, ite_eq_right hmem]
  · have hge : dA ≤ m ∨ dB ≤ m := by omega
    rw [resOrdUniv_eq_linear_of_ge hge]
    let p : Fin (dA + dB) → ℤ := fun i => -(i.val : ℤ)
    let q : Fin (dA + dB) → ℤ := fun j =>
      (j.val : ℤ) + if j.val < dA then (m : ℤ) else ((m : ℤ) - dA)
    apply pow_dvd_det_of_potential (A.sylvester B dA dB) t p q
    · have hp_sum : ∑ i : Fin (dA + dB), p i = -(∑ i : Fin (dA + dB), (i.val : ℤ)) := by
        simp [p]
      have hq_sum : ∑ j : Fin (dA + dB), q j =
          (∑ j : Fin (dA + dB), (j.val : ℤ)) +
            ((dA : ℤ) * m + (dB : ℤ) * ((m : ℤ) - dA)) := by
        simp only [q, Finset.sum_add_distrib]
        congr 1
        rw [sum_fin_split dA dB]
        have hL : ∑ j : Fin dA,
            (if (Fin.castAdd dB j).val < dA then (m : ℤ) else ((m : ℤ) - dA)) = (dA : ℤ) * m := by
          have hlt : ∀ j : Fin dA, (Fin.castAdd dB j).val < dA := fun j => j.isLt
          simp_rw [ite_eq_left (hlt _)]
          simp
        have hR : ∑ k : Fin dB,
            (if (Fin.natAdd dA k).val < dA then (m : ℤ) else ((m : ℤ) - dA)) =
            (dB : ℤ) * ((m : ℤ) - dA) := by
          have hge' : ∀ k : Fin dB, ¬ (Fin.natAdd dA k).val < dA := fun k => by dsimp; omega
          simp_rw [ite_eq_right (hge' _)]
          simp [mul_sub]
        rw [hL, hR]
      rw [hp_sum, hq_sum]
      have hprod : dA * dB ≤ (dA + dB) * m := by
        rcases hge with h1 | h2 <;> nlinarith
      zify [hprod]
      linarith
    · intro i j
      rw [Polynomial.sylvester, Matrix.of_apply]
      by_cases hj : j.val < dA
      · have hjeq : j = Fin.castAdd dB ⟨j.val, hj⟩ := Fin.ext rfl
        by_cases hmem : i.val ∈ Set.Icc j.val (j.val + dB)
        · right
          have hval : (j.addCases
              (fun j₁ => if i.val ∈ Set.Icc (j₁ : ℕ) (j₁ + dB) then B.coeff (i - j₁) else 0)
              (fun j₁ => if i.val ∈ Set.Icc (j₁ : ℕ) (j₁ + dA) then A.coeff (i - j₁) else 0)) =
              B.coeff (i.val - j.val) := by
            conv_lhs => rw [hjeq]
            rw [Fin.addCases_left, ite_eq_left hmem]
          rw [hval]
          have hle_ij : j.val ≤ i.val := hmem.1
          have hpq : (p i + q j).toNat ≤ m - (i.val - j.val) := by
            dsimp only [p, q]; rw [ite_eq_left hj]; omega
          exact (pow_dvd_pow t hpq).trans (hB (i.val - j.val))
        · left
          conv_lhs => rw [hjeq]
          rw [Fin.addCases_left, ite_eq_right hmem]
      · have hklt : j.val - dA < dB := by have := j.isLt; omega
        have hjeq : j = Fin.natAdd dA ⟨j.val - dA, hklt⟩ := Fin.ext (by dsimp; omega)
        by_cases hmem : i.val ∈ Set.Icc (j.val - dA) (j.val - dA + dA)
        · right
          have hval : (j.addCases
              (fun j₁ => if i.val ∈ Set.Icc (j₁ : ℕ) (j₁ + dB) then B.coeff (i - j₁) else 0)
              (fun j₁ => if i.val ∈ Set.Icc (j₁ : ℕ) (j₁ + dA) then A.coeff (i - j₁) else 0)) =
              A.coeff (i.val - (j.val - dA)) := by
            conv_lhs => rw [hjeq]
            rw [Fin.addCases_right, ite_eq_left hmem]
          rw [hval]
          have hle_ik : j.val - dA ≤ i.val := hmem.1
          have hpq : (p i + q j).toNat ≤ m - (i.val - (j.val - dA)) := by
            dsimp only [p, q]; rw [ite_eq_right hj]; omega
          exact (pow_dvd_pow t hpq).trans (hA (i.val - (j.val - dA)))
        · left
          conv_lhs => rw [hjeq]
          rw [Fin.addCases_right, ite_eq_right hmem]

end UniversalResultant

/-! ### Part 4: Bivariate Shift Covariance & Distinct-Site Global Sum Bounds on `BiPoly K` -/

section BiPolyGlobal

/-- Bivariate polynomial ring `A[X][Y]`, matching `PrimeHDResultant.BiPoly` and
`DrdosDiscriminantBarrier.BiPoly` definitionally. -/
abbrev BiPoly (A : Type*) [CommRing A] := Polynomial (Polynomial A)

/-- Coordinate shift `(X, Y) ↦ (x₀ + X, y₀ + Y)` on `BiPoly A`. -/
noncomputable def shiftBi {A : Type*} [CommRing A] (x0 y0 : A) (f : BiPoly A) : BiPoly A :=
  (f.map (Polynomial.compRingHom (Polynomial.C x0 + Polynomial.X))).comp
    (Polynomial.C (Polynomial.C y0) + Polynomial.X)

/-- Bivariate vanishing multiplicity `≥ m` at `(x₀, y₀)`: every shifted `(i, j)` coefficient with
`i + j < m` vanishes. -/
def biMultGE {A : Type*} [CommRing A] (x0 y0 : A) (f : BiPoly A) (m : ℕ) : Prop :=
  ∀ i j : ℕ, i + j < m → ((shiftBi x0 y0 f).coeff j).coeff i = 0

/-- Deterministic leading-coefficient order bound `max(0, m - d)` (and `+1` when `m = d` and
`a_{0, d} = 0`). -/
def leadingCoeffOrd (d m : ℕ) : ℕ := m - d

def leadingCoeffOrdBoost (d m : ℕ) : ℕ := if m = d then 1 else m - d

theorem biMultGE_iff_X_pow_dvd {A : Type*} [CommRing A] (x0 y0 : A) (f : BiPoly A) (m : ℕ) :
    biMultGE x0 y0 f m ↔ ∀ j, Polynomial.X ^ (m - j) ∣ (shiftBi x0 y0 f).coeff j := by
  constructor
  · intro h j
    rw [Polynomial.X_pow_dvd_iff]
    intro i hi
    exact h i j (by omega)
  · intro h i j hij
    exact (Polynomial.X_pow_dvd_iff.mp (h j)) i (by omega)

private theorem leadingCoeff_taylor {R : Type*} [CommRing R] (c : R) (p : R[X]) :
    (Polynomial.taylor c p).leadingCoeff = p.leadingCoeff := by
  rw [Polynomial.leadingCoeff, Polynomial.leadingCoeff, Polynomial.natDegree_taylor,
    Polynomial.taylor_coeff]
  have hhd : Polynomial.hasseDeriv p.natDegree p = Polynomial.C (p.coeff p.natDegree) := by
    ext k
    rw [Polynomial.hasseDeriv_coeff, Polynomial.coeff_C]
    split_ifs with hk
    · subst hk; simp
    · have hgt : p.natDegree < k + p.natDegree := by omega
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hgt, mul_zero]
  rw [hhd, Polynomial.eval_C]

private theorem natDegree_comp_C_add_X {R : Type*} [CommRing R] (c : R) (p : R[X]) :
    (p.comp (Polynomial.C c + Polynomial.X)).natDegree = p.natDegree := by
  have h1 : (p.comp (Polynomial.C c + Polynomial.X)).natDegree ≤ p.natDegree := by
    refine Polynomial.natDegree_comp_le.trans ?_
    have hX : (Polynomial.C c + Polynomial.X : R[X]).natDegree ≤ 1 :=
      (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) Polynomial.natDegree_X_le)
    nlinarith
  have h2 : p.natDegree ≤ (p.comp (Polynomial.C c + Polynomial.X)).natDegree := by
    have hback : (p.comp (Polynomial.C c + Polynomial.X)).comp (Polynomial.C (-c) + Polynomial.X) =
        p := by
      rw [Polynomial.comp_assoc, Polynomial.add_comp, Polynomial.C_comp, Polynomial.X_comp]
      have : Polynomial.C c + (Polynomial.C (-c) + Polynomial.X) = Polynomial.X := by
        rw [← add_assoc, ← map_add, add_neg_cancel, map_zero, zero_add]
      rw [this, Polynomial.comp_X]
    calc p.natDegree
        = ((p.comp (Polynomial.C c + Polynomial.X)).comp
            (Polynomial.C (-c) + Polynomial.X)).natDegree := by rw [hback]
      _ ≤ (p.comp (Polynomial.C c + Polynomial.X)).natDegree *
            (Polynomial.C (-c) + Polynomial.X).natDegree := Polynomial.natDegree_comp_le
      _ ≤ (p.comp (Polynomial.C c + Polynomial.X)).natDegree := by
          have hX : (Polynomial.C (-c) + Polynomial.X : R[X]).natDegree ≤ 1 :=
            (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) Polynomial.natDegree_X_le)
          nlinarith
  exact le_antisymm h1 h2

private theorem compRingHom_C_add_X_injective {A : Type*} [CommRing A] (x0 : A) :
    Function.Injective (Polynomial.compRingHom (Polynomial.C x0 + Polynomial.X)) := by
  intro p q hpq
  have h : (p.comp (Polynomial.C x0 + Polynomial.X)).comp (Polynomial.C (-x0) + Polynomial.X) =
      (q.comp (Polynomial.C x0 + Polynomial.X)).comp (Polynomial.C (-x0) + Polynomial.X) :=
    congrArg (fun r => r.comp (Polynomial.C (-x0) + Polynomial.X)) hpq
  have hid : ∀ r : Polynomial A,
      (r.comp (Polynomial.C x0 + Polynomial.X)).comp (Polynomial.C (-x0) + Polynomial.X) = r := by
    intro r
    rw [Polynomial.comp_assoc, Polynomial.add_comp, Polynomial.C_comp, Polynomial.X_comp]
    have : Polynomial.C x0 + (Polynomial.C (-x0) + Polynomial.X) = Polynomial.X := by
      rw [← add_assoc, ← map_add, add_neg_cancel, map_zero, zero_add]
    rw [this, Polynomial.comp_X]
  simpa only [hid] using h

theorem natDegree_shiftBi {A : Type*} [CommRing A] (x0 y0 : A) (f : BiPoly A) :
    (shiftBi x0 y0 f).natDegree = f.natDegree := by
  unfold shiftBi
  rw [natDegree_comp_C_add_X, Polynomial.natDegree_map_eq_of_injective
    (compRingHom_C_add_X_injective x0)]

theorem leadingCoeff_shiftBi {A : Type*} [CommRing A] (x0 y0 : A) (f : BiPoly A) :
    (shiftBi x0 y0 f).leadingCoeff = f.leadingCoeff.comp (Polynomial.C x0 + Polynomial.X) := by
  unfold shiftBi
  have hcomp : Polynomial.C (Polynomial.C y0) + Polynomial.X =
      Polynomial.X + Polynomial.C (Polynomial.C y0) := add_comm _ _
  rw [hcomp, ← Polynomial.taylor_apply, leadingCoeff_taylor,
    Polynomial.leadingCoeff_map_of_injective (compRingHom_C_add_X_injective x0)]
  rfl

/-- `discr` commutes with any ring homomorphism preserving `natDegree`. -/
theorem discr_map_of_natDegree_eq {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (f : R[X]) (hdeg : (f.map φ).natDegree = f.natDegree) :
    (f.map φ).discr = φ f.discr := by
  have hexp : (f.map φ).natDegree * ((f.map φ).natDegree - 1) / 2 =
      f.natDegree * (f.natDegree - 1) / 2 := by rw [hdeg]
  rw [Polynomial.discr, Polynomial.discr, hexp, map_mul, map_pow, map_neg, map_one]
  congr 1
  let e : Fin ((f.map φ).natDegree - 1 + (f.map φ).natDegree) ≃
      Fin (f.natDegree - 1 + f.natDegree) := finCongr (by rw [hdeg])
  rw [← Matrix.det_reindex_self e, RingHom.map_det]
  congr 1
  ext ⟨i, hi⟩ ⟨j, hj⟩
  by_cases hn : f.natDegree = 0
  · exfalso; omega
  have hnm : (f.map φ).natDegree ≠ 0 := by omega
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, e, finCongr_symm, finCongr_apply,
    Fin.cast_mk, RingHom.mapMatrix_apply, Matrix.map_apply, Polynomial.sylvesterDeriv,
    dite_eq_right hn, dite_eq_right hnm]
  by_cases hbot : i = 2 * f.natDegree - 2
  · have h1 : (⟨i, by omega⟩ : Fin ((f.map φ).natDegree - 1 + (f.map φ).natDegree)) =
        ⟨2 * (f.map φ).natDegree - 2, by omega⟩ := Fin.ext (by dsimp; omega)
    have h2 : (⟨i, hi⟩ : Fin (f.natDegree - 1 + f.natDegree)) =
        ⟨2 * f.natDegree - 2, by omega⟩ := Fin.ext hbot
    rw [h1, h2, Matrix.updateRow_self, Matrix.updateRow_self]
    simp only [hdeg, apply_ite φ, map_one, map_zero, map_natCast]
  · have h1 : (⟨i, by omega⟩ : Fin ((f.map φ).natDegree - 1 + (f.map φ).natDegree)) ≠
        ⟨2 * (f.map φ).natDegree - 2, by omega⟩ := fun h => by
      have := congrArg Fin.val h; dsimp at this; omega
    have h2 : (⟨i, hi⟩ : Fin (f.natDegree - 1 + f.natDegree)) ≠
        ⟨2 * f.natDegree - 2, by omega⟩ := fun h => by
      have := congrArg Fin.val h; dsimp at this; omega
    rw [Matrix.updateRow_ne h1, Matrix.updateRow_ne h2]
    simp only [Polynomial.sylvester, Matrix.of_apply, Polynomial.derivative_map]
    by_cases hj1 : j < (f.map φ).natDegree - 1
    · have hje1 : (⟨j, by omega⟩ : Fin ((f.map φ).natDegree - 1 + (f.map φ).natDegree)) =
          Fin.castAdd (f.map φ).natDegree ⟨j, hj1⟩ := Fin.ext rfl
      have hje2 : (⟨j, hj⟩ : Fin (f.natDegree - 1 + f.natDegree)) =
          Fin.castAdd f.natDegree ⟨j, by omega⟩ := Fin.ext rfl
      rw [hje1, hje2, Fin.addCases_left, Fin.addCases_left]
      simp only [hdeg, apply_ite φ, Polynomial.coeff_map, map_zero]
    · have hje1 : (⟨j, by omega⟩ : Fin ((f.map φ).natDegree - 1 + (f.map φ).natDegree)) =
          Fin.natAdd ((f.map φ).natDegree - 1) ⟨j - ((f.map φ).natDegree - 1), by omega⟩ :=
        Fin.ext (by dsimp; omega)
      have hje2 : (⟨j, hj⟩ : Fin (f.natDegree - 1 + f.natDegree)) =
          Fin.natAdd (f.natDegree - 1) ⟨j - (f.natDegree - 1), by omega⟩ :=
        Fin.ext (by dsimp; omega)
      rw [hje1, hje2, Fin.addCases_right, Fin.addCases_right]
      simp only [hdeg, apply_ite φ, Polynomial.coeff_map, map_zero]

/-- Translation invariance of `Polynomial.discr` over ANY integral domain `R` and ANY characteristic
(including `char R ∣ f.natDegree`!). -/
theorem discr_taylor {R : Type*} [CommRing R] [IsDomain R] (r : R) (f : R[X]) :
    (Polynomial.taylor r f).discr = f.discr := by
  by_cases hd0 : f.natDegree = 0
  · have hf : f = Polynomial.C (f.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hd0
    rw [hf, Polynomial.taylor_C, Polynomial.discr_C]
  have hd_pos : 0 < f.natDegree := Nat.pos_of_ne_zero hd0
  by_cases hd1 : f.natDegree = 1
  · have hdeg : f.degree = 1 :=
      (Polynomial.degree_eq_iff_natDegree_eq_of_pos one_pos).mpr hd1
    have hdeg' : (Polynomial.taylor r f).degree = 1 :=
      (Polynomial.degree_eq_iff_natDegree_eq_of_pos one_pos).mpr
        (by rw [Polynomial.natDegree_taylor, hd1])
    rw [Polynomial.discr_of_degree_eq_one hdeg, Polynomial.discr_of_degree_eq_one hdeg']
  have hf_ne : f ≠ 0 := by intro h0; simp [h0] at hd0
  have hlc_ne : f.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hf_ne
  have hderiv_taylor : (Polynomial.taylor r f).derivative = Polynomial.taylor r f.derivative := by
    rw [Polynomial.taylor_apply, Polynomial.taylor_apply, Polynomial.derivative_comp]
    simp
  have hlc_taylor : (Polynomial.taylor r f).leadingCoeff = f.leadingCoeff := leadingCoeff_taylor r f
  have hdeg_pos : 0 < f.degree := Polynomial.natDegree_pos_iff_degree_pos.mp hd_pos
  have hdeg_pos' : 0 < (Polynomial.taylor r f).degree :=
    Polynomial.natDegree_pos_iff_degree_pos.mp (by rw [Polynomial.natDegree_taylor]; exact hd_pos)
  have hres1 := Polynomial.resultant_deriv hdeg_pos
  have hres2 := Polynomial.resultant_deriv hdeg_pos'
  rw [Polynomial.natDegree_taylor, hlc_taylor, hderiv_taylor] at hres2
  have hres_eq :
      Polynomial.resultant (Polynomial.taylor r f) (Polynomial.taylor r f.derivative)
        f.natDegree (f.natDegree - 1) =
      Polynomial.resultant f f.derivative f.natDegree (f.natDegree - 1) := by
    by_cases hder0 : f.derivative = 0
    · rw [hder0, map_zero, Polynomial.resultant_zero_right, Polynomial.resultant_zero_right,
        zero_pow hd0, zero_mul, zero_mul]
    · have hder_le : f.derivative.natDegree ≤ f.natDegree - 1 :=
        Polynomial.natDegree_derivative_le f
      let k := (f.natDegree - 1) - f.derivative.natDegree
      have hk_eq : f.derivative.natDegree + k = f.natDegree - 1 := Nat.add_sub_of_le hder_le
      have h1 : Polynomial.resultant f f.derivative f.natDegree (f.natDegree - 1) =
          f.leadingCoeff ^ k *
            Polynomial.resultant f f.derivative f.natDegree f.derivative.natDegree := by
        rw [← hk_eq, Polynomial.resultant_add_right_deg f f.derivative f.natDegree
          f.derivative.natDegree k le_rfl, Polynomial.coeff_natDegree]
      have h2 : Polynomial.resultant (Polynomial.taylor r f) (Polynomial.taylor r f.derivative)
            f.natDegree (f.natDegree - 1) =
          (Polynomial.taylor r f).leadingCoeff ^ k *
            Polynomial.resultant (Polynomial.taylor r f) (Polynomial.taylor r f.derivative)
              (Polynomial.taylor r f).natDegree (Polynomial.taylor r f.derivative).natDegree := by
        rw [Polynomial.natDegree_taylor, Polynomial.natDegree_taylor, ← hk_eq,
          Polynomial.resultant_add_right_deg (Polynomial.taylor r f)
            (Polynomial.taylor r f.derivative) f.natDegree f.derivative.natDegree k
            (by rw [Polynomial.natDegree_taylor]),
          ← Polynomial.natDegree_taylor f r, Polynomial.coeff_natDegree]
      rw [h1, h2, hlc_taylor, Polynomial.resultant_taylor]
  rw [hres_eq, hres1] at hres2
  have hfac_ne : ((-1 : R) ^ (f.natDegree * (f.natDegree - 1) / 2) * f.leadingCoeff) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) hlc_ne
  exact mul_left_cancel₀ hfac_ne hres2.symm

/-- **Exact Shift Covariance of the `Y`-Discriminant (`BiPoly K`, ANY characteristic!):**
`(shiftBi x₀ y₀ P).discr = P.discr.comp (C x₀ + X)`. -/
theorem discr_shiftBi {K : Type*} [CommRing K] [IsDomain K] (x0 y0 : K) (P : BiPoly K) :
    (shiftBi x0 y0 P).discr = P.discr.comp (Polynomial.C x0 + Polynomial.X) := by
  unfold shiftBi
  let φ : Polynomial K →+* Polynomial K := Polynomial.compRingHom (Polynomial.C x0 + Polynomial.X)
  have hcomm : Polynomial.C (Polynomial.C y0) + Polynomial.X =
      Polynomial.X + Polynomial.C (Polynomial.C y0) := add_comm _ _
  rw [hcomm, ← Polynomial.taylor_apply]
  change (Polynomial.taylor (Polynomial.C y0) (P.map φ)).discr = φ P.discr
  rw [discr_taylor]
  exact discr_map_of_natDegree_eq (R := Polynomial K) (S := Polynomial K) φ P
    (Polynomial.natDegree_map_eq_of_injective (compRingHom_C_add_X_injective x0) P)

/-- Pull back divisibility by `X ^ k` on `p.comp (C x₀ + X)` to `(X - C x₀) ^ k ∣ p`. -/
private theorem X_sub_C_pow_dvd_of_X_pow_dvd_comp {A : Type*} [CommRing A]
    (x0 : A) (p : Polynomial A) (k : ℕ)
    (h : Polynomial.X ^ k ∣ p.comp (Polynomial.C x0 + Polynomial.X)) :
    (Polynomial.X - Polynomial.C x0) ^ k ∣ p := by
  rcases h with ⟨q, hq⟩
  refine ⟨q.comp (Polynomial.X - Polynomial.C x0), ?_⟩
  have hback : (p.comp (Polynomial.C x0 + Polynomial.X)).comp (Polynomial.X - Polynomial.C x0) =
      p := by
    rw [Polynomial.comp_assoc, Polynomial.add_comp, Polynomial.C_comp, Polynomial.X_comp]
    have : Polynomial.C x0 + (Polynomial.X - Polynomial.C x0) = Polynomial.X := by ring
    rw [this, Polynomial.comp_X]
  calc p = (p.comp (Polynomial.C x0 + Polynomial.X)).comp (Polynomial.X - Polynomial.C x0) :=
        hback.symm
    _ = (Polynomial.X ^ k * q).comp (Polynomial.X - Polynomial.C x0) := by rw [hq]
    _ = (Polynomial.X - Polynomial.C x0) ^ k * q.comp (Polynomial.X - Polynomial.C x0) := by
        rw [Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.X_comp]

/-- **Local Quadratic Discriminant Divisibility at `(x₀, y₀)` on `BiPoly K`:** -/
theorem X_sub_C_pow_dvd_discr_of_biMultGE {K : Type*} [CommRing K] [IsDomain K]
    (x0 y0 : K) (P : BiPoly K) (hd : 2 ≤ P.natDegree) (m : ℕ)
    (hm : biMultGE x0 y0 P m) :
    (Polynomial.X - Polynomial.C x0) ^ discOrdQuad P.natDegree m ∣ P.discr := by
  apply X_sub_C_pow_dvd_of_X_pow_dvd_comp
  rw [← discr_shiftBi x0 y0 P]
  have hd' : 2 ≤ (shiftBi x0 y0 P).natDegree := by rw [natDegree_shiftBi]; exact hd
  have h := pow_dvd_discr_of_coeff_dvd (shiftBi x0 y0 P) hd' Polynomial.X m
    ((biMultGE_iff_X_pow_dvd x0 y0 P m).mp hm)
  rwa [natDegree_shiftBi] at h

/-- **Local `+1`-Boosted Quadratic Discriminant Divisibility under `a_{0, m} = 0` at `(x₀, y₀)`:** -/
theorem X_sub_C_pow_dvd_discr_boost_of_biMultGE {K : Type*} [CommRing K] [IsDomain K]
    (x0 y0 : K) (P : BiPoly K) (hd : 2 ≤ P.natDegree) (m : ℕ)
    (hm : biMultGE x0 y0 P m)
    (ha0m : ((shiftBi x0 y0 P).coeff m).coeff 0 = 0) :
    (Polynomial.X - Polynomial.C x0) ^ discOrdQuadBoost P.natDegree m ∣ P.discr := by
  apply X_sub_C_pow_dvd_of_X_pow_dvd_comp
  rw [← discr_shiftBi x0 y0 P]
  have hd' : 2 ≤ (shiftBi x0 y0 P).natDegree := by rw [natDegree_shiftBi]; exact hd
  have hXdvd : Polynomial.X ∣ (shiftBi x0 y0 P).coeff m := Polynomial.X_dvd_iff.mpr ha0m
  have h := pow_dvd_discr_boost_of_coeff_dvd (shiftBi x0 y0 P) hd' Polynomial.X m
    ((biMultGE_iff_X_pow_dvd x0 y0 P m).mp hm) hXdvd
  rwa [natDegree_shiftBi] at h

/-- **Exact Shift Covariance of `Polynomial.resultant` on `BiPoly K` (all `A.natDegree ≤ dA`,
`B.natDegree ≤ dB`):** -/
theorem resultant_shiftBi_eq {K : Type*} [CommRing K] [IsDomain K]
    (x0 y0 : K) (A B : BiPoly K) (dA dB : ℕ)
    (hA : A.natDegree ≤ dA) (hB : B.natDegree ≤ dB) :
    Polynomial.resultant (shiftBi x0 y0 A) (shiftBi x0 y0 B) dA dB =
      (Polynomial.resultant A B dA dB).comp (Polynomial.C x0 + Polynomial.X) := by
  unfold shiftBi
  let φ := Polynomial.compRingHom (Polynomial.C x0 + Polynomial.X)
  have hcomm : Polynomial.C (Polynomial.C y0) + Polynomial.X =
      Polynomial.X + Polynomial.C (Polynomial.C y0) := add_comm _ _
  rw [hcomm, ← Polynomial.taylor_apply, ← Polynomial.taylor_apply]
  change Polynomial.resultant (Polynomial.taylor (Polynomial.C y0) (A.map φ))
      (Polynomial.taylor (Polynomial.C y0) (B.map φ)) dA dB =
    φ (Polynomial.resultant A B dA dB)
  rw [← Polynomial.resultant_map_map A B dA dB φ]
  have hmapA : (A.map φ).natDegree = A.natDegree :=
    Polynomial.natDegree_map_eq_of_injective (compRingHom_C_add_X_injective x0) A
  have hmapB : (B.map φ).natDegree = B.natDegree :=
    Polynomial.natDegree_map_eq_of_injective (compRingHom_C_add_X_injective x0) B
  let kA := dA - A.natDegree
  let kB := dB - B.natDegree
  have hkA : A.natDegree + kA = dA := Nat.add_sub_of_le hA
  have hkB : B.natDegree + kB = dB := Nat.add_sub_of_le hB
  by_cases hkAB : 0 < kA ∧ 0 < kB
  · have hzero : ∀ (p q : BiPoly K), p.natDegree < dA → q.natDegree < dB →
        Polynomial.resultant p q dA dB = 0 := by
      intro p q hp hq
      rw [Polynomial.resultant]
      apply Matrix.det_eq_zero_of_row_eq_zero ⟨dA + dB - 1, by omega⟩
      intro j
      rw [Polynomial.sylvester, Matrix.of_apply]
      by_cases hj : j.val < dA
      · have hjeq : j = Fin.castAdd dB ⟨j.val, hj⟩ := Fin.ext rfl
        conv_lhs => rw [hjeq]
        rw [Fin.addCases_left]
        split_ifs with hmem
        · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by dsimp at *; omega)
        · rfl
      · have hklt : j.val - dA < dB := by have := j.isLt; omega
        have hjeq : j = Fin.natAdd dA ⟨j.val - dA, hklt⟩ := Fin.ext (by dsimp; omega)
        conv_lhs => rw [hjeq]
        rw [Fin.addCases_right]
        split_ifs with hmem
        · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by dsimp at *; omega)
        · rfl
    rw [hzero _ _ (by rw [Polynomial.natDegree_taylor, hmapA]; omega)
          (by rw [Polynomial.natDegree_taylor, hmapB]; omega),
        hzero _ _ (by rw [hmapA]; omega) (by rw [hmapB]; omega)]
  · rcases (by omega : kA = 0 ∨ kB = 0) with hkA0 | hkB0
    · have hdA_eq : dA = A.natDegree := by omega
      rw [hdA_eq, ← hkB]
      have h1 := Polynomial.resultant_add_right_deg
        (Polynomial.taylor (Polynomial.C y0) (A.map φ))
        (Polynomial.taylor (Polynomial.C y0) (B.map φ))
        A.natDegree B.natDegree kB (by rw [Polynomial.natDegree_taylor, hmapB])
      have h2 := Polynomial.resultant_add_right_deg (A.map φ) (B.map φ)
        A.natDegree B.natDegree kB (by rw [hmapB])
      rw [h1, h2]
      have hc1 : (Polynomial.taylor (Polynomial.C y0) (A.map φ)).coeff A.natDegree =
          (A.map φ).coeff A.natDegree := by
        calc (Polynomial.taylor (Polynomial.C y0) (A.map φ)).coeff A.natDegree
            = (Polynomial.taylor (Polynomial.C y0) (A.map φ)).leadingCoeff := by
                rw [Polynomial.leadingCoeff, Polynomial.natDegree_taylor, hmapA]
          _ = (A.map φ).leadingCoeff := leadingCoeff_taylor _ _
          _ = (A.map φ).coeff A.natDegree := by rw [Polynomial.leadingCoeff, hmapA]
      rw [hc1]
      congr 1
      have := Polynomial.resultant_taylor (A.map φ) (B.map φ) (Polynomial.C y0)
      simpa only [Polynomial.natDegree_taylor, hmapA, hmapB] using this
    · have hdB_eq : dB = B.natDegree := by omega
      rw [hdB_eq, ← hkA]
      have h1 := Polynomial.resultant_add_left_deg
        (Polynomial.taylor (Polynomial.C y0) (A.map φ))
        (Polynomial.taylor (Polynomial.C y0) (B.map φ))
        A.natDegree B.natDegree kA (by rw [Polynomial.natDegree_taylor, hmapA])
      have h2 := Polynomial.resultant_add_left_deg (A.map φ) (B.map φ)
        A.natDegree B.natDegree kA (by rw [hmapA])
      rw [h1, h2]
      have hc1 : (Polynomial.taylor (Polynomial.C y0) (B.map φ)).coeff B.natDegree =
          (B.map φ).coeff B.natDegree := by
        calc (Polynomial.taylor (Polynomial.C y0) (B.map φ)).coeff B.natDegree
            = (Polynomial.taylor (Polynomial.C y0) (B.map φ)).leadingCoeff := by
                rw [Polynomial.leadingCoeff, Polynomial.natDegree_taylor, hmapB]
          _ = (B.map φ).leadingCoeff := leadingCoeff_taylor _ _
          _ = (B.map φ).coeff B.natDegree := by rw [Polynomial.leadingCoeff, hmapB]
      rw [hc1]
      congr 1
      have := Polynomial.resultant_taylor (A.map φ) (B.map φ) (Polynomial.C y0)
      simpa only [Polynomial.natDegree_taylor, hmapA, hmapB] using this

theorem X_sub_C_pow_dvd_resultant_univ_of_biMultGE {K : Type*} [CommRing K] [IsDomain K]
    (x0 y0 : K) (A B : BiPoly K) (dA dB m : ℕ)
    (hdegA : A.natDegree ≤ dA) (hdegB : B.natDegree ≤ dB)
    (hA : biMultGE x0 y0 A m) (hB : biMultGE x0 y0 B m) :
    (Polynomial.X - Polynomial.C x0) ^ resOrdUniv dA dB m ∣ Polynomial.resultant A B dA dB := by
  apply X_sub_C_pow_dvd_of_X_pow_dvd_comp
  rw [← resultant_shiftBi_eq x0 y0 A B dA dB hdegA hdegB]
  exact pow_dvd_resultant_univ (shiftBi x0 y0 A) (shiftBi x0 y0 B) dA dB m Polynomial.X
    ((biMultGE_iff_X_pow_dvd x0 y0 A m).mp hA) ((biMultGE_iff_X_pow_dvd x0 y0 B m).mp hB)

/-- **Deterministic Leading-Coefficient Order Bounds (`#210` Item 4):** -/
theorem X_sub_C_pow_dvd_leadingCoeff_of_biMultGE {A : Type*} [CommRing A]
    (x0 y0 : A) (P : BiPoly A) (m : ℕ) (hm : biMultGE x0 y0 P m) :
    (Polynomial.X - Polynomial.C x0) ^ leadingCoeffOrd P.natDegree m ∣ P.leadingCoeff := by
  apply X_sub_C_pow_dvd_of_X_pow_dvd_comp
  rw [← leadingCoeff_shiftBi x0 y0 P, Polynomial.leadingCoeff, natDegree_shiftBi]
  exact (biMultGE_iff_X_pow_dvd x0 y0 P m).mp hm P.natDegree

theorem X_sub_C_pow_dvd_leadingCoeff_boost_of_biMultGE {A : Type*} [CommRing A]
    (x0 y0 : A) (P : BiPoly A) (m : ℕ) (hm : biMultGE x0 y0 P m)
    (ha0m : ((shiftBi x0 y0 P).coeff m).coeff 0 = 0) :
    (Polynomial.X - Polynomial.C x0) ^ leadingCoeffOrdBoost P.natDegree m ∣ P.leadingCoeff := by
  unfold leadingCoeffOrdBoost
  split_ifs with heq
  · apply X_sub_C_pow_dvd_of_X_pow_dvd_comp
    rw [pow_one, ← leadingCoeff_shiftBi x0 y0 P, Polynomial.leadingCoeff, natDegree_shiftBi, ← heq]
    exact Polynomial.X_dvd_iff.mpr ha0m
  · exact X_sub_C_pow_dvd_leadingCoeff_of_biMultGE x0 y0 P m hm

/-- Helper: distinct-site product divisibility gives `∑ i, e i ≤ p.natDegree` for any nonzero
`p : K[X]` over a field `K`. -/
theorem sum_orders_le_natDegree_of_dvd {K ι : Type*} [Field K] [Fintype ι]
    (p : Polynomial K) (hp : p ≠ 0) (x : ι → K) (hx : Function.Injective x)
    (e : ι → ℕ) (hdvd : ∀ i, (Polynomial.X - Polynomial.C (x i)) ^ e i ∣ p) :
    ∑ i : ι, e i ≤ p.natDegree := by
  have hprod_dvd : (∏ i : ι, (Polynomial.X - Polynomial.C (x i)) ^ e i) ∣ p := by
    apply Finset.prod_dvd_of_coprime
    · intro i _ j _ hij
      exact (Polynomial.isCoprime_X_sub_C_of_isUnit_sub
        (sub_ne_zero.mpr fun h => hij (hx h)).isUnit).pow_left.pow_right
    · intro i _; exact hdvd i
  have hdeg : (∏ i : ι, (Polynomial.X - Polynomial.C (x i)) ^ e i).natDegree = ∑ i : ι, e i := by
    rw [Polynomial.natDegree_prod (Finset.univ) _
      (fun i _ => pow_ne_zero _ (Polynomial.X_sub_C_ne_zero (x i)))]
    simp [Polynomial.natDegree_pow]
  rw [← hdeg]
  exact Polynomial.natDegree_le_of_dvd hprod_dvd hp

/-- **Global Quadratic Discriminant Sum Bound (distinct sites `x : ι → K`, any field `K`):** -/
theorem sum_discOrdQuad_le_natDegree_discr {K ι : Type*} [Field K] [Fintype ι]
    (P : BiPoly K) (hd : 2 ≤ P.natDegree) (hdisc : P.discr ≠ 0)
    (x y : ι → K) (hx : Function.Injective x) (m : ι → ℕ)
    (hm : ∀ i, biMultGE (x i) (y i) P (m i)) :
    ∑ i : ι, discOrdQuad P.natDegree (m i) ≤ P.discr.natDegree :=
  sum_orders_le_natDegree_of_dvd P.discr hdisc x hx _ fun i =>
    X_sub_C_pow_dvd_discr_of_biMultGE (x i) (y i) P hd (m i) (hm i)

/-- **Global `+1`-Boosted Quadratic Discriminant Sum Bound (`a_{0, m_i} = 0` at every site):** -/
theorem sum_discOrdQuadBoost_le_natDegree_discr {K ι : Type*} [Field K] [Fintype ι]
    (P : BiPoly K) (hd : 2 ≤ P.natDegree) (hdisc : P.discr ≠ 0)
    (x y : ι → K) (hx : Function.Injective x) (m : ι → ℕ)
    (hm : ∀ i, biMultGE (x i) (y i) P (m i))
    (ha0m : ∀ i, ((shiftBi (x i) (y i) P).coeff (m i)).coeff 0 = 0) :
    ∑ i : ι, discOrdQuadBoost P.natDegree (m i) ≤ P.discr.natDegree :=
  sum_orders_le_natDegree_of_dvd P.discr hdisc x hx _ fun i =>
    X_sub_C_pow_dvd_discr_boost_of_biMultGE (x i) (y i) P hd (m i) (hm i) (ha0m i)

/-- **Global Corrected Universal Resultant Sum Bound (`#228` soundness-fixed):** -/
theorem sum_resOrdUniv_le_natDegree_resultant {K ι : Type*} [Field K] [Fintype ι]
    (A B : BiPoly K) (dA dB : ℕ)
    (hdegA : A.natDegree ≤ dA) (hdegB : B.natDegree ≤ dB)
    (hres : Polynomial.resultant A B dA dB ≠ 0)
    (x y : ι → K) (hx : Function.Injective x) (m : ι → ℕ)
    (hA : ∀ i, biMultGE (x i) (y i) A (m i))
    (hB : ∀ i, biMultGE (x i) (y i) B (m i)) :
    ∑ i : ι, resOrdUniv dA dB (m i) ≤ (Polynomial.resultant A B dA dB).natDegree :=
  sum_orders_le_natDegree_of_dvd (Polynomial.resultant A B dA dB) hres x hx _ fun i =>
    X_sub_C_pow_dvd_resultant_univ_of_biMultGE (x i) (y i) A B dA dB (m i) hdegA hdegB (hA i) (hB i)

/-- **Global Leading-Coefficient Sum Bounds (`#210` Item 4):** -/
theorem sum_leadingCoeffOrd_le_natDegree_leadingCoeff {K ι : Type*} [Field K] [Fintype ι]
    (P : BiPoly K) (hP : P ≠ 0)
    (x y : ι → K) (hx : Function.Injective x) (m : ι → ℕ)
    (hm : ∀ i, biMultGE (x i) (y i) P (m i)) :
    ∑ i : ι, leadingCoeffOrd P.natDegree (m i) ≤ P.leadingCoeff.natDegree :=
  sum_orders_le_natDegree_of_dvd P.leadingCoeff (Polynomial.leadingCoeff_ne_zero.mpr hP) x hx _
    fun i => X_sub_C_pow_dvd_leadingCoeff_of_biMultGE (x i) (y i) P (m i) (hm i)

theorem sum_leadingCoeffOrdBoost_le_natDegree_leadingCoeff {K ι : Type*} [Field K] [Fintype ι]
    (P : BiPoly K) (hP : P ≠ 0)
    (x y : ι → K) (hx : Function.Injective x) (m : ι → ℕ)
    (hm : ∀ i, biMultGE (x i) (y i) P (m i))
    (ha0m : ∀ i, ((shiftBi (x i) (y i) P).coeff (m i)).coeff 0 = 0) :
    ∑ i : ι, leadingCoeffOrdBoost P.natDegree (m i) ≤ P.leadingCoeff.natDegree :=
  sum_orders_le_natDegree_of_dvd P.leadingCoeff (Polynomial.leadingCoeff_ne_zero.mpr hP) x hx _
    fun i => X_sub_C_pow_dvd_leadingCoeff_boost_of_biMultGE (x i) (y i) P (m i) (hm i) (ha0m i)

end BiPolyGlobal

#print axioms pow_dvd_det_of_potential
#print axioms pow_dvd_discr_of_coeff_dvd
#print axioms pow_dvd_discr_boost_of_coeff_dvd
#print axioms resOrdUniv_eq_sq_of_le
#print axioms resOrdUniv_eq_linear_of_ge
#print axioms resOrdUniv_eq_sq_add_excess
#print axioms resOrdUniv_lt_sq_of_gt
#print axioms pow_dvd_resultant_univ
#print axioms discr_shiftBi
#print axioms X_sub_C_pow_dvd_discr_of_biMultGE
#print axioms X_sub_C_pow_dvd_discr_boost_of_biMultGE
#print axioms X_sub_C_pow_dvd_resultant_univ_of_biMultGE
#print axioms X_sub_C_pow_dvd_leadingCoeff_of_biMultGE
#print axioms X_sub_C_pow_dvd_leadingCoeff_boost_of_biMultGE
#print axioms sum_discOrdQuad_le_natDegree_discr
#print axioms sum_discOrdQuadBoost_le_natDegree_discr
#print axioms sum_resOrdUniv_le_natDegree_resultant
#print axioms sum_leadingCoeffOrd_le_natDegree_leadingCoeff
#print axioms sum_leadingCoeffOrdBoost_le_natDegree_leadingCoeff

end ArkLib.ProximityGap.Frontier.PrimeHDQuadraticDiscriminant
