/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

set_option linter.style.longLine false

/-!
# Irreducible polynomials of degree below the characteristic are separable

Over a field `K` of characteristic `p = ringChar K`, an irreducible polynomial whose degree is
strictly below `p` is automatically separable: it cannot be a polynomial in `X^p` (that would force
its degree to be a multiple of `p`, hence `0` or `≥ p`), so its derivative is nonzero, and an
irreducible polynomial is separable iff its derivative is nonzero.

This complements Mathlib's `Irreducible.separable` (which requires `CharZero`).  It is the clean
large-characteristic discharge of the function-field separability side condition (`hsepFF`) in the
BCIKS20 §5 list-decoding chain: the Guruswami–Sudan interpolant has `Y`-degree `poly(n)`, so for a
field of characteristic above that polynomial bound, all its irreducible factors are separable.

## Main results

* `derivative_ne_zero_of_natDegree_lt_ringChar` — `0 < deg f < ringChar K ⟹ derivative f ≠ 0`.
* `Irreducible.separable_of_natDegree_lt_ringChar` — irreducible + `deg < ringChar K ⟹ separable`.
* `Separable.map_fractionRing_of_irreducible_natDegree_lt_ringChar` — the function-field form.
-/

open Polynomial

variable {K : Type*} [Field K]

/-- Over a field, a polynomial of degree `0 < deg f < ringChar K` has nonzero derivative: the
`(deg f − 1)`-th derivative coefficient is `leadingCoeff · deg f`, and `deg f` is a nonzero scalar
since `0 < deg f < p` rules out `p ∣ deg f`. -/
theorem derivative_ne_zero_of_natDegree_lt_ringChar {f : K[X]}
    (hd : 0 < f.natDegree) (hlt : f.natDegree < ringChar K) : derivative f ≠ 0 := by
  intro h
  have hcoeff : (derivative f).coeff (f.natDegree - 1)
      = f.coeff (f.natDegree) * (f.natDegree : K) := by
    rw [Polynomial.coeff_derivative]
    have h1 : f.natDegree - 1 + 1 = f.natDegree := by omega
    rw [h1]
    congr 1
    have hcast : ((f.natDegree - 1 : ℕ) : K) + 1 = (f.natDegree : K) := by
      have : (f.natDegree - 1 : ℕ) + 1 = f.natDegree := by omega
      rw [← this]; push_cast; ring
    rw [hcast]
  rw [h, Polynomial.coeff_zero] at hcoeff
  have hlc : f.coeff (f.natDegree) ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr (fun hf => by rw [hf] at hd; simp at hd)
  have hnd : (f.natDegree : K) = 0 := by
    rcases mul_eq_zero.mp hcoeff.symm with h1 | h1
    · exact absurd h1 hlc
    · exact h1
  haveI : CharP K (ringChar K) := ringChar.charP K
  have hdvd : ringChar K ∣ f.natDegree := (CharP.cast_eq_zero_iff K (ringChar K) _).mp hnd
  obtain ⟨c, hc⟩ := hdvd
  rcases Nat.eq_zero_or_pos c with hc0 | hc0
  · rw [hc0, Nat.mul_zero] at hc; omega
  · have : ringChar K ≤ f.natDegree := by rw [hc]; exact Nat.le_mul_of_pos_right _ hc0
    omega

/-- **Irreducible + low degree ⟹ separable.** Over a field `K`, an irreducible polynomial of degree
strictly below `ringChar K` is separable.  (Char-`p` companion to Mathlib's `Irreducible.separable`,
which assumes `CharZero`.) -/
theorem Irreducible.separable_of_natDegree_lt_ringChar {f : K[X]} (hirr : Irreducible f)
    (hlt : f.natDegree < ringChar K) : f.Separable := by
  rw [Polynomial.separable_iff_derivative_ne_zero hirr]
  exact derivative_ne_zero_of_natDegree_lt_ringChar hirr.natDegree_pos hlt

/-- **Function-field form.** For an integral domain `A` with `R : A[X]` irreducible *after mapping to
the fraction field*, if its degree is below `ringChar A`, then the mapped polynomial is separable
over `FractionRing A`.  This is the shape consumed by the BCIKS20 §5 `hsepFF` side condition once the
characteristic exceeds the Guruswami–Sudan degree budget. -/
theorem Separable.map_fractionRing_of_irreducible_natDegree_lt_ringChar
    {A : Type*} [CommRing A] [IsDomain A] {R : A[X]}
    (hirr : Irreducible (R.map (algebraMap A (FractionRing A))))
    (hlt : (R.map (algebraMap A (FractionRing A))).natDegree < ringChar A) :
    (R.map (algebraMap A (FractionRing A))).Separable := by
  have hchar : ringChar (FractionRing A) = ringChar A := by
    haveI : CharP (FractionRing A) (ringChar A) := IsFractionRing.charP A (ringChar A)
    exact ringChar.eq (FractionRing A) (ringChar A)
  exact Irreducible.separable_of_natDegree_lt_ringChar hirr (by rw [hchar]; exact hlt)
