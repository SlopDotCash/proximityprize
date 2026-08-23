/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Tactic.Ring

/-!
# Cyclotomic pattern injectivity — the char-0 subset-sum bijection (issue #232)

For `ζ` a primitive `2^(k+1)`-th root of unity in a characteristic-zero field, the
`2^k` powers `ζ^0, …, ζ^(2^k − 1)` are linearly independent over the integers:

* `pattern_sum_injective` — integer-coefficient combinations
  `∑_{j<2^k} ε_j ζ^j` determine the coefficients `ε_j`.
* `signed_subset_sum_injective` — hence the map
  `(P, N) ↦ ∑_{j∈P} ζ^j − ∑_{j∈N} ζ^j` is injective on disjoint pairs
  `P, N ⊆ range 2^k`.

This is the bijection step of the exact characteristic-zero image count for subgroup
subset sums (DISPROOF_LOG O11′/O43, `06-AVERAGED-PA` Theorem A): since
`ζ^(j + 2^k) = −ζ^j`, every `r`-subset sum of the full group `μ_{2^(k+1)}` of roots of
unity is a `±1/0`-pattern combination of the basis powers, so *distinct admissible
patterns give distinct sums* and the image count equals the pattern count
`N₀(m, r) = ∑_s C(m/2, s)·2^s` formalized in
`ArkLib.ToMathlib.DisjointPairCount.n0_pattern_count`.

The proof is three Mathlib facts glued together: the minimal polynomial of `ζ` over `ℚ`
is the cyclotomic polynomial (`cyclotomic_eq_minpoly_rat`), its degree is
`φ(2^(k+1)) = 2^k` (`natDegree_cyclotomic`, `Nat.totient_prime_pow`), and no nonzero
rational polynomial of smaller degree annihilates `ζ` (`minpoly.degree_le_of_ne_zero`).
So the difference of two equal-sum patterns, read as a polynomial of degree `< 2^k`
vanishing at `ζ`, must be the zero polynomial.
-/

namespace ArkLib.CyclotomicPatterns

open Finset Polynomial

variable {F : Type*} [Field F] [CharZero F]

/-- Pattern injectivity: in characteristic zero, integer-coefficient combinations of
`ζ^0, …, ζ^(2^k − 1)` for `ζ` a primitive `2^(k+1)`-th root of unity determine their
coefficients. -/
theorem pattern_sum_injective {k : ℕ} {ζ : F} (hζ : IsPrimitiveRoot ζ (2 ^ (k + 1)))
    {ε ε' : ℕ → ℤ}
    (hsum : ∑ j ∈ range (2 ^ k), (ε j : F) * ζ ^ j =
      ∑ j ∈ range (2 ^ k), (ε' j : F) * ζ ^ j) :
    ∀ j < 2 ^ k, ε j = ε' j := by
  set P : ℚ[X] := ∑ j ∈ range (2 ^ k), C ((ε j - ε' j : ℤ) : ℚ) * X ^ j with hPdef
  have haeval : aeval ζ P = 0 := by
    have hterm : aeval ζ P = ∑ j ∈ range (2 ^ k), ((ε j : F) - (ε' j : F)) * ζ ^ j := by
      rw [hPdef, map_sum]
      refine sum_congr rfl fun j _ => ?_
      rw [map_mul, aeval_C, map_pow, aeval_X, map_intCast]
      push_cast
      ring
    rw [hterm]
    simp only [sub_mul]
    rw [Finset.sum_sub_distrib, hsum, sub_self]
  have hP0 : P = 0 := by
    by_contra hP0
    have hmin : degree (minpoly ℚ ζ) ≤ degree P :=
      minpoly.degree_le_of_ne_zero ℚ ζ hP0 haeval
    rw [← cyclotomic_eq_minpoly_rat hζ (by positivity)] at hmin
    have hdegcyc : degree (cyclotomic (2 ^ (k + 1)) ℚ) = ((2 ^ k : ℕ) : WithBot ℕ) := by
      rw [degree_eq_natDegree (cyclotomic_ne_zero _ ℚ), natDegree_cyclotomic]
      norm_num [Nat.totient_prime_pow Nat.prime_two]
    have hdegP : degree P < ((2 ^ k : ℕ) : WithBot ℕ) := by
      rw [hPdef]
      apply lt_of_le_of_lt (degree_sum_le _ _)
      rw [Finset.sup_lt_iff (by exact WithBot.bot_lt_coe _)]
      intro j hj
      exact lt_of_le_of_lt (degree_C_mul_X_pow_le _ _)
        (by exact_mod_cast mem_range.mp hj)
    rw [hdegcyc] at hmin
    exact absurd hmin (not_le.mpr hdegP)
  intro j hj
  have hcoeff : P.coeff j = ((ε j - ε' j : ℤ) : ℚ) := by
    rw [hPdef, finset_sum_coeff]
    rw [sum_congr rfl fun j' _ => coeff_C_mul_X_pow ((ε j' - ε' j' : ℤ) : ℚ) j' j]
    rw [Finset.sum_ite_eq (range (2 ^ k)) j fun j' => ((ε j' - ε' j' : ℤ) : ℚ)]
    rw [if_pos (mem_range.mpr hj)]
  rw [hP0, coeff_zero] at hcoeff
  have : (ε j - ε' j : ℤ) = 0 := by exact_mod_cast hcoeff.symm
  omega

/-- Signed subset sums determine the pair of disjoint supports: the map
`(P, N) ↦ ∑_{j∈P} ζ^j − ∑_{j∈N} ζ^j` is injective on disjoint pairs inside
`range (2^k)`. -/
theorem signed_subset_sum_injective {k : ℕ} {ζ : F}
    (hζ : IsPrimitiveRoot ζ (2 ^ (k + 1))) {P N P' N' : Finset ℕ}
    (hP : P ⊆ range (2 ^ k)) (hN : N ⊆ range (2 ^ k))
    (hP' : P' ⊆ range (2 ^ k)) (hN' : N' ⊆ range (2 ^ k))
    (hd : Disjoint P N) (hd' : Disjoint P' N')
    (hsum : (∑ j ∈ P, ζ ^ j) - ∑ j ∈ N, ζ ^ j =
      (∑ j ∈ P', ζ ^ j) - ∑ j ∈ N', ζ ^ j) :
    P = P' ∧ N = N' := by
  set ε : ℕ → ℤ := fun j => (if j ∈ P then 1 else 0) - (if j ∈ N then 1 else 0) with hεdef
  set ε' : ℕ → ℤ := fun j => (if j ∈ P' then 1 else 0) - (if j ∈ N' then 1 else 0) with hε'def
  have hindic : ∀ (A : Finset ℕ), A ⊆ range (2 ^ k) →
      ∑ j ∈ range (2 ^ k), (if j ∈ A then (1 : F) else 0) * ζ ^ j = ∑ j ∈ A, ζ ^ j := by
    intro A hA
    simp only [ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hA]
  have hkey : ∀ j < 2 ^ k, ε j = ε' j := by
    apply pattern_sum_injective hζ
    have lhs : ∑ j ∈ range (2 ^ k), (ε j : F) * ζ ^ j =
        (∑ j ∈ P, ζ ^ j) - ∑ j ∈ N, ζ ^ j := by
      rw [← hindic P hP, ← hindic N hN, ← Finset.sum_sub_distrib]
      refine sum_congr rfl fun j _ => ?_
      simp only [hεdef]
      push_cast
      ring
    have rhs : ∑ j ∈ range (2 ^ k), (ε' j : F) * ζ ^ j =
        (∑ j ∈ P', ζ ^ j) - ∑ j ∈ N', ζ ^ j := by
      rw [← hindic P' hP', ← hindic N' hN', ← Finset.sum_sub_distrib]
      refine sum_congr rfl fun j _ => ?_
      simp only [hε'def]
      push_cast
      ring
    rw [lhs, rhs, hsum]
  constructor
  · ext j
    by_cases hjr : j < 2 ^ k
    · have := hkey j hjr
      simp only [hεdef, hε'def] at this
      constructor
      · intro hjP
        by_contra hjP'
        have hjN : j ∉ N := fun hh => (Finset.disjoint_left.mp hd) hjP hh
        by_cases hjN' : j ∈ N' <;> simp [hjP, hjP', hjN, hjN'] at this
      · intro hjP'
        by_contra hjP
        have hjN' : j ∉ N' := fun hh => (Finset.disjoint_left.mp hd') hjP' hh
        by_cases hjN : j ∈ N <;> simp [hjP, hjP', hjN, hjN'] at this
    · constructor
      · intro hjP; exact absurd (mem_range.mp (hP hjP)) hjr
      · intro hjP'; exact absurd (mem_range.mp (hP' hjP')) hjr
  · ext j
    by_cases hjr : j < 2 ^ k
    · have := hkey j hjr
      simp only [hεdef, hε'def] at this
      constructor
      · intro hjN
        by_contra hjN'
        have hjP : j ∉ P := fun hh => (Finset.disjoint_left.mp hd) hh hjN
        by_cases hjP' : j ∈ P' <;> simp [hjP, hjP', hjN, hjN'] at this
      · intro hjN'
        by_contra hjN
        have hjP' : j ∉ P' := fun hh => (Finset.disjoint_left.mp hd') hh hjN'
        by_cases hjP : j ∈ P <;> simp [hjP, hjP', hjN, hjN'] at this
    · constructor
      · intro hjN; exact absurd (mem_range.mp (hN hjN)) hjr
      · intro hjN'; exact absurd (mem_range.mp (hN' hjN')) hjr

/-- The minimal polynomial of a primitive `2^(k+1)`-th root of unity over `ℚ` has degree
exactly `2^k`. Composed with `R11.linearIndependent_pow_le` and `R11.antipodal_of_sum_zero`
(`LamLeungUnconditionalQ.lean`), this discharges the linear-independence hypothesis there
*unconditionally at every 2-power level* in characteristic zero — upgrading the t = 1
antipodal rigidity theorem from its `ℚ(i)` instantiation to all FRI domains. -/
theorem natDegree_minpoly_rat_two_pow {k : ℕ} {ζ : F}
    (hζ : IsPrimitiveRoot ζ (2 ^ (k + 1))) :
    (minpoly ℚ ζ).natDegree = 2 ^ k := by
  rw [← cyclotomic_eq_minpoly_rat hζ (by positivity), natDegree_cyclotomic]
  simp [Nat.totient_prime_pow Nat.prime_two]

end ArkLib.CyclotomicPatterns
