/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# The Stepanov counting lemma (#389): the provable heart of the rep bound

The open core of the `μ_n` supply wall is a sub-`n³` additive-energy / Garcia–Voloch
representation bound, which has no elementary proof and requires **Stepanov's
polynomial method**.  That method has two halves:

1. **Counting** (this file, fully proven): a single nonzero polynomial that vanishes
   to order `≥ m` at each of `|S|` distinct points has degree `≥ m·|S|`, so
   `|S| ≤ deg(f)/m`.
2. **Construction** (the named open input): exhibiting such an auxiliary `f` of
   *controlled* degree `≪ n` that vanishes to high order at every representation
   point `{w ∈ μ_n : c·w+1 ∈ μ_n}`.

> **`card_le_natDegree_of_vanishing`** — for `f ≠ 0`, if `(X − s)^m ∣ f` for every `s`
> in a finset `S`, then `m · |S| ≤ f.natDegree`.

This isolates the genuine difficulty: the *counting* half — the part usually elided as
"obviously a polynomial has few high-multiplicity roots" — is here machine-checked and
reusable; only the *auxiliary-polynomial construction* (the Wronskian/derivative
estimate that makes Stepanov work for a multiplicative subgroup) remains open.

Proof: the factors `(X − s)^m`, `s ∈ S`, are pairwise coprime (distinct linear factors
over a field), each divides `f`, so their product `∏ (X − s)^m` — of degree `m·|S|` —
divides `f`; degree of a divisor of a nonzero polynomial is `≤` its degree.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`.
-/

open Polynomial

namespace ArkLib.ProximityGap.Stepanov

variable {F : Type*} [Field F]

/-- **The Stepanov counting lemma.**  If a nonzero polynomial `f` is divisible by
`(X − s)^m` for each `s` in a finite set `S` of distinct field elements, then
`m · |S| ≤ deg(f)`.  Equivalently `|S| ≤ deg(f)/m` — a degree-`< N·m` polynomial has
fewer than `N` points of multiplicity `≥ m`. -/
theorem card_le_natDegree_of_vanishing {S : Finset F} {f : F[X]} {m : ℕ}
    (hf : f ≠ 0) (hdvd : ∀ s ∈ S, (X - C s) ^ m ∣ f) :
    m * S.card ≤ f.natDegree := by
  classical
  -- the pairwise-coprime product of high-multiplicity linear factors divides f
  have hprod : (∏ s ∈ S, (X - C s) ^ m) ∣ f := by
    refine Finset.prod_dvd_of_coprime ?_ hdvd
    intro a _ b _ hab
    exact (isCoprime_X_sub_C_of_isUnit_sub ((sub_ne_zero.mpr hab).isUnit)).pow
  -- its degree is exactly m·|S|
  have hne : ∀ s ∈ S, (X - C s) ^ m ≠ (0 : F[X]) := fun s _ =>
    pow_ne_zero _ (X_sub_C_ne_zero s)
  have hdeg : (∏ s ∈ S, (X - C s) ^ m).natDegree = m * S.card := by
    rw [Polynomial.natDegree_prod _ _ hne]
    have : ∀ s ∈ S, ((X - C s) ^ m).natDegree = m := by
      intro s _; rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]
    rw [Finset.sum_congr rfl this, Finset.sum_const, smul_eq_mul, mul_comm]
  -- a divisor of a nonzero polynomial has no larger degree
  calc m * S.card = (∏ s ∈ S, (X - C s) ^ m).natDegree := hdeg.symm
    _ ≤ f.natDegree := Polynomial.natDegree_le_of_dvd hprod hf

/-- **Consumer form**: a nonzero polynomial of degree `< N·m` vanishes to order `≥ m`
at fewer than `N` points.  This is the bound that, fed an auxiliary polynomial of
degree `≈ n` vanishing to order `≈ n^{1/3}`, yields the Garcia–Voloch rep estimate
`r(c) ≲ n^{2/3}` — the construction of that auxiliary polynomial being the sole
remaining open input. -/
theorem card_lt_of_natDegree_lt {S : Finset F} {f : F[X]} {m N : ℕ} (hm : 1 ≤ m)
    (hf : f ≠ 0) (hdeg : f.natDegree < N * m) (hdvd : ∀ s ∈ S, (X - C s) ^ m ∣ f) :
    S.card < N := by
  have h := card_le_natDegree_of_vanishing hf hdvd
  by_contra hc
  push_neg at hc
  have : N * m ≤ m * S.card := by
    rw [mul_comm N m]; exact Nat.mul_le_mul_left m hc
  omega

end ArkLib.ProximityGap.Stepanov

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.Stepanov.card_le_natDegree_of_vanishing
#print axioms ArkLib.ProximityGap.Stepanov.card_lt_of_natDegree_lt
