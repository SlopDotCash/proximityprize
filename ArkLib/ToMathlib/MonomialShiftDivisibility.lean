/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.Polynomial.Roots

/-!
# The sparse-polynomial shift-divisibility bound (Heath-Brown–Konyagin Lemma 6)

A nonzero polynomial over a field of characteristic `p` that is a sum of `N` distinct
monomials and has degree `< p` is **not** divisible by `(X − a)^N` for any `a ≠ 0`
([HBK00], Lemma 6; the non-vanishing heart of the Stepanov bound for additive equations
in multiplicative subgroups, `#{(x,y) ∈ G² : x + y = λ} = O(|G|^{2/3})`).

The proof is an induction on the number of monomials via the Euler-type combination
`g = X·P′ − deg(P)·P`, which kills the top monomial and (because all exponents are
distinct integers `< p`) keeps every other one alive, while `(X−a)^N ∣ P` forces
`(X−a)^{N−1} ∣ g`.

The degree hypothesis is essential in characteristic `p`: `(X − 1)^p = X^p − 1` is a sum
of **two** distinct monomials divisible by `(X − 1)^p` — Frobenius destroys the statement
the moment degrees reach `p`.

## Main results

* `natCast_injOn_lt_char` — distinct naturals `< p` stay distinct in a characteristic-`p`
  domain (the cast-injectivity the induction consumes).
* `eulerComb_coeff`, `eulerComb_support`, `pow_dvd_eulerComb_of_pow_dvd` — the Euler
  combination's coefficient formula, support, and divisibility transfer.
* `not_pow_card_support_dvd_of_natDegree_lt_char` — **the monomial lemma**: for `a ≠ 0`,
  `P ≠ 0`, `P.natDegree < p`: `¬ (X − C a) ^ P.support.card ∣ P`.

## References

[HBK00] D.R. Heath-Brown, S.V. Konyagin, *New bounds for Gauss sums derived from kth
powers, and for Heilbronn's exponential sum*, Q. J. Math. 51 (2000), 221–235, Lemma 6.
-/

open Polynomial

namespace ArkLib.MonomialShiftDivisibility

variable {F : Type*} [Field F] {p : ℕ} [Fact p.Prime] [CharP F p]

/-- Distinct naturals below the characteristic stay distinct under the cast. -/
theorem natCast_injOn_lt_char {i j : ℕ} (hi : i < p) (hj : j < p) (hij : i ≠ j) :
    (i : F) ≠ (j : F) := by
  intro h
  -- wlog via symmetry: reduce to the case i < j
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · have hsub : ((j - i : ℕ) : F) = 0 := by
      have : ((j : F) - (i : F)) = ((j - i : ℕ) : F) := by
        rw [Nat.cast_sub (le_of_lt hlt)]
      rw [← this, h, sub_self]
    have hdvd : p ∣ j - i := (CharP.cast_eq_zero_iff F p _).mp hsub
    have hpos : 0 < j - i := Nat.sub_pos_of_lt hlt
    have hlt' : j - i < p := lt_of_le_of_lt (Nat.sub_le _ _) hj
    exact absurd (Nat.le_of_dvd hpos hdvd) (not_le.mpr hlt')
  · have hsub : ((i - j : ℕ) : F) = 0 := by
      have : ((i : F) - (j : F)) = ((i - j : ℕ) : F) := by
        rw [Nat.cast_sub (le_of_lt hlt)]
      rw [← this, h, sub_self]
    have hdvd : p ∣ i - j := (CharP.cast_eq_zero_iff F p _).mp hsub
    have hpos : 0 < i - j := Nat.sub_pos_of_lt hlt
    have hlt' : i - j < p := lt_of_le_of_lt (Nat.sub_le _ _) hi
    exact absurd (Nat.le_of_dvd hpos hdvd) (not_le.mpr hlt')

/-- The Euler-type combination killing the top monomial: `g = X·P′ − natDegree(P)·P`. -/
noncomputable def eulerComb (P : F[X]) : F[X] :=
  X * derivative P - C ((P.natDegree : F)) * P

/-- Coefficient formula: `(eulerComb P).coeff l = (l − deg P) · P.coeff l`. -/
theorem eulerComb_coeff (P : F[X]) (l : ℕ) :
    (eulerComb P).coeff l = ((l : F) - (P.natDegree : F)) * P.coeff l := by
  rcases l with _ | m
  · simp [eulerComb, coeff_X_mul_zero, sub_mul]
  · rw [eulerComb, coeff_sub, coeff_X_mul, coeff_derivative, coeff_C_mul]
    push_cast
    ring

/-- The Euler combination's support is the original support minus the top exponent
(all exponents below the characteristic). -/
theorem eulerComb_support (P : F[X]) (hdeg : P.natDegree < p) :
    (eulerComb P).support = P.support.erase P.natDegree := by
  ext l
  rw [Finset.mem_erase, mem_support_iff, mem_support_iff, eulerComb_coeff, mul_ne_zero_iff]
  constructor
  · rintro ⟨hcast, hco⟩
    refine ⟨fun h => hcast (by rw [h, sub_self]), hco⟩
  · rintro ⟨hne, hco⟩
    have hl : l < p := lt_of_le_of_lt (le_natDegree_of_ne_zero hco) hdeg
    exact ⟨sub_ne_zero.mpr (natCast_injOn_lt_char hl hdeg hne), hco⟩

/-- Divisibility transfer: `(X − a)^(N+1) ∣ P  ⟹  (X − a)^N ∣ eulerComb P`. -/
theorem pow_dvd_eulerComb_of_pow_dvd {a : F} {P : F[X]} {N : ℕ}
    (hdvd : (X - C a) ^ (N + 1) ∣ P) :
    (X - C a) ^ N ∣ eulerComb P := by
  obtain ⟨Q, hQ⟩ := hdvd
  have hderiv : derivative P
      = (X - C a) ^ N * (((N : F) + 1) • Q + (X - C a) * derivative Q) := by
    rw [hQ, derivative_mul, derivative_pow, derivative_X_sub_C]
    push_cast
    ring_nf
    simp [smul_eq_C_mul]
    ring
  refine ⟨X * (((N : F) + 1) • Q + (X - C a) * derivative Q)
    - C ((P.natDegree : F)) * ((X - C a) * Q), ?_⟩
  rw [eulerComb, hderiv, hQ]
  ring

/-- **The monomial lemma** ([HBK00] Lemma 6).  Over a field of characteristic `p`, a
nonzero polynomial of degree `< p` that is a sum of `N` distinct monomials is not
divisible by `(X − a)^N`, for any `a ≠ 0`.  Sharp: `(X−1)^p = X^p − 1` (two monomials)
shows the degree hypothesis cannot be dropped, and `X^N` shows `a ≠ 0` is needed. -/
theorem not_pow_card_support_dvd_of_natDegree_lt_char {a : F} (ha : a ≠ 0) :
    ∀ (N : ℕ) (P : F[X]), P ≠ 0 → P.natDegree < p → P.support.card ≤ N →
      ¬ (X - C a) ^ P.support.card ∣ P := by
  intro N
  induction N with
  | zero =>
    intro P hP _ hcard
    exact absurd (Finset.card_eq_zero.mp (Nat.le_zero.mp hcard))
      (support_eq_empty.ne.mpr hP ∘ id)
  | succ N ih =>
    intro P hP hdeg hcard hdvd
    rcases Nat.lt_or_ge P.support.card (N + 1) with hlt | hge
    · exact ih P hP hdeg (Nat.lt_succ_iff.mp hlt) hdvd
    have hcardeq : P.support.card = N + 1 := le_antisymm hcard hge
    rcases Nat.eq_zero_or_pos N with hN0 | hNpos
    · -- single monomial: a nonzero monomial has no nonzero root
      subst hN0
      obtain ⟨l, hl⟩ := Finset.card_eq_one.mp hcardeq
      have hroot : P.eval a = 0 := by
        have h1 : (X - C a) ∣ P := by
          simpa [hcardeq] using hdvd
        exact (dvd_iff_isRoot.mp h1)
      have heval : P.eval a = P.coeff l * a ^ l := by
        rw [eval_eq_sum, sum_def, hl]
        simp
      have hco : P.coeff l ≠ 0 := by
        have : l ∈ P.support := by rw [hl]; exact Finset.mem_singleton_self l
        exact mem_support_iff.mp this
      rw [heval] at hroot
      exact (mul_ne_zero hco (pow_ne_zero l ha)) hroot
    · -- N ≥ 1: pass to the Euler combination
      set g := eulerComb P with hg
      have hsupp : g.support = P.support.erase P.natDegree := eulerComb_support P hdeg
      have hmem : P.natDegree ∈ P.support := natDegree_mem_support_of_nonzero hP
      have hgcard : g.support.card = N := by
        rw [hsupp, Finset.card_erase_of_mem hmem, hcardeq]
        omega
      have hg0 : g ≠ 0 := by
        intro h0
        have : g.support.card = 0 := by rw [h0]; simp
        omega
      have hgdeg : g.natDegree < p := by
        have h1 : g.natDegree ∈ g.support := natDegree_mem_support_of_nonzero hg0
        have h2 : g.natDegree ∈ P.support := by
          rw [hsupp] at h1
          exact Finset.mem_of_mem_erase h1
        exact lt_of_le_of_lt (le_natDegree_of_mem_supp _ h2) hdeg
      have hdvdg : (X - C a) ^ N ∣ g := by
        rw [hg]
        refine pow_dvd_eulerComb_of_pow_dvd ?_
        rw [← hcardeq]
        exact hdvd
      have := ih g hg0 hgdeg (le_of_eq hgcard)
      rw [hgcard] at this
      exact this hdvdg

/-- The packaged form: `P ≠ 0`, `deg P < p`, `a ≠ 0` ⟹ `(X − a)^{#monomials} ∤ P`. -/
theorem monomial_lemma {a : F} (ha : a ≠ 0) (P : F[X]) (hP : P ≠ 0)
    (hdeg : P.natDegree < p) :
    ¬ (X - C a) ^ P.support.card ∣ P :=
  not_pow_card_support_dvd_of_natDegree_lt_char ha P.support.card P hP hdeg le_rfl

end ArkLib.MonomialShiftDivisibility

/-! ## Axiom audit — kernel-clean. -/
#print axioms ArkLib.MonomialShiftDivisibility.monomial_lemma
#print axioms ArkLib.MonomialShiftDivisibility.eulerComb_support
#print axioms ArkLib.MonomialShiftDivisibility.pow_dvd_eulerComb_of_pow_dvd
