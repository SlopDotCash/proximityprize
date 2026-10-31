/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Algebra.CharP.Lemmas

/-!
# Hasse-derivative collapse of `X^(2^a) - 1` in characteristic 2

For the Ethereum Proximity Prize "derandomization" direction (Issue #232), an earlier note
suggested using the fact that, over a *smooth* (power-of-two-sized) multiplicative subgroup `L`
of a binary field, the strictly-intermediate Hasse derivatives of the vanishing polynomial
`V_L(X) = X^{|L|} - 1` collapse to zero. **That domain application is impossible:** in
characteristic `2`, `X^(2^a) - 1 = (X - 1)^(2^a)` has `1` as its only root in any field, so a
binary field has no multiplicative subgroup of size `2^a` for `a > 0` (the multiplicative group
of `𝔽_{2^d}` has odd order `2^d - 1`). For `a = 0` the range `0 < m < 2^a` is empty. Hence
`X^(2^a) - 1` is *not* the vanishing polynomial of any nontrivial multiplicative domain in
characteristic `2`; it is a repeated-root polynomial.

What this file proves is therefore only the following pure algebraic identity about the
polynomial `X^(2^a) - 1` over a characteristic-`2` commutative ring. It carries no
interpolation-rank or derivative-multiplicity consequence for an evaluation domain:

* smooth *multiplicative* domains of size `2^a` exist only in odd characteristic, where
  `X^(2^a) - 1` is separable and these identities do not apply;
* binary-field FRI/STIR-style domains are *additive* (affine subspaces), whose vanishing
  polynomial is a linearized (subspace) polynomial — a different object, not `X^(2^a) - 1`.

Any derivative/rank inference must first fix which of these two settings it is in.

The previous revision of this file laundered the intended consequences through a `sorry`-valued
custom `HasseDerivative` def, a `sorry`-valued `hasse_lucas_collapse`, and a vacuous
`… : True := by trivial` "rank bound" placebo (exactly the axiom-laundering pattern banned by
#169/#171). All three are removed: we use mathlib's `Polynomial.hasseDeriv` and prove the real
identity, and the genuinely-open interpolation-matrix rank statement is *not* faked here (it
belongs to the open derandomization research surface, not a `True` theorem).

Contents (both machine-checked, `[propext, Classical.choice, Quot.sound]`-clean):

* `choose_two_pow_cast_eq_zero` — in any commutative ring of characteristic `2`, the middle
  binomial coefficient `C(2^a, m)` casts to `0` for `0 < m < 2^a`. Proof: the `X^m`-coefficient
  of `(X+1)^{2^a}` is `C(2^a, m)` (binomial theorem), but `(X+1)^{2^a} = X^{2^a} + 1` by the
  Frobenius endomorphism, whose `X^m`-coefficient is `0` strictly between the endpoints.
* `hasseDeriv_X_pow_two_pow_sub_one` — consequently `hasseDeriv m (X^{2^a} - 1) = 0` for
  `0 < m < 2^a` (a Lucas/Frobenius identity for the repeated-root polynomial `(X - 1)^(2^a)`).

These are algebraic identities only; they do **not** describe any nontrivial binary-field
evaluation domain, bound any interpolation-matrix rank, or resolve the prize threshold `δ*`.
-/

open Polynomial

namespace ArkLib.CodingTheory.Research

variable {R : Type*} [CommRing R]

/-- **Char-2 middle binomial vanishing.** In a commutative ring of characteristic two,
`C(2^a, m)` casts to zero whenever `0 < m < 2^a`. The endpoints `m = 0` and `m = 2^a` give
`C = 1`; everything strictly between collapses — the Lucas/Kummer statement for the prime `2`.

Proof: comparing the `X^m`-coefficients of the equal polynomials `(X+1)^{2^a}` (whose
`X^m`-coefficient is `C(2^a, m)` by the binomial theorem) and `X^{2^a} + 1` (the Frobenius
form, whose `X^m`-coefficient is `0` for `0 < m < 2^a`). -/
lemma choose_two_pow_cast_eq_zero [CharP R 2] (a m : ℕ) (hm : 0 < m) (hlt : m < 2 ^ a) :
    ((2 ^ a).choose m : R) = 0 := by
  have hfrob : (X + 1 : R[X]) ^ (2 ^ a) = X ^ (2 ^ a) + 1 := by
    have h : (X + 1 : R[X]) ^ (2 ^ a) = X ^ (2 ^ a) + (1 : R[X]) ^ (2 ^ a) :=
      add_pow_char_pow X 1 2 a
    rwa [one_pow] at h
  have e := congrArg (fun p : R[X] => p.coeff m) hfrob
  simp only [coeff_X_add_one_pow, coeff_add, coeff_X_pow, coeff_one] at e
  rw [if_neg (Nat.ne_of_lt hlt), if_neg (Nat.pos_iff_ne_zero.mp hm), add_zero] at e
  exact e

/-- **Hasse–Lucas collapse of `X^(2^a) - 1`.** Over a characteristic-`2` ring, every
strictly-intermediate Hasse derivative of the polynomial `X^(2^a) - 1` vanishes identically:
`hasseDeriv m (X^{2^a} - 1) = 0` for `0 < m < 2^a`.

Caveat: in characteristic `2` this polynomial equals `(X - 1)^(2^a)`, whose only root in a field
is `1`, so it is **not** the vanishing polynomial of any nontrivial multiplicative subgroup (none
of size `2^a`, `a > 0`, exists in a binary field). The statement is a pure polynomial identity
and implies nothing about evaluation domains or interpolation ranks. -/
theorem hasseDeriv_X_pow_two_pow_sub_one [CharP R 2] (a m : ℕ) (hm : 0 < m) (hlt : m < 2 ^ a) :
    hasseDeriv m (X ^ (2 ^ a) - 1 : R[X]) = 0 := by
  ext j
  rw [coeff_zero, hasseDeriv_coeff, coeff_sub, coeff_X_pow, coeff_one]
  by_cases hj : j + m = 2 ^ a
  · rw [if_pos hj, if_neg (show ¬ j + m = 0 by omega), sub_zero, mul_one, hj]
    exact choose_two_pow_cast_eq_zero a m hm hlt
  · rw [if_neg hj, if_neg (show ¬ j + m = 0 by omega), sub_zero, mul_zero]

end ArkLib.CodingTheory.Research
