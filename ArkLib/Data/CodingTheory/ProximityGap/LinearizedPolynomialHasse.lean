/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
# Hasse-derivative structure of linearized polynomials in characteristic `p`

This file isolates the algebraic backbone of the **derandomization** research direction for the
ABF26 Proximity Prize (tracking issue #232, direction §7.1): explicit smooth/structured
evaluation domains and the Guruswami–Sudan multiplicity (Hasse-derivative) constraints used to
list-decode Reed–Solomon codes over them.

## A framing correction (the object the prize's binary domains actually use)

A previous research stub asserted (unproven) a "Hasse–Lucas collapse" for the polynomial
`X^{|L|} - 1` over a *smooth power-of-two multiplicative subgroup* `L` in **characteristic 2**.
That framing is mathematically incoherent:

* In characteristic `p`, Frobenius gives `X^{p^a} - 1 = (X - 1)^{p^a}`, so this polynomial has the
  single root `1` with multiplicity `p^a` — the **inseparable** case, *not* the vanishing
  polynomial of `p^a` distinct points.
* A smooth multiplicative subgroup `L` with `|L| = 2^a` requires `2^a ∣ |F| - 1`, which forces
  `char F ≠ 2` (in characteristic 2, `|F| - 1` is odd). For such `L`, `X^{|L|} - 1` is separable
  with `|L|` distinct roots, and its intermediate Hasse derivatives do **not** all vanish — the
  collapse needs the exponent to be a power of the *characteristic*.

The object the prize's **binary STARK domains** genuinely use is the vanishing polynomial of an
`𝔽_p`-affine **subspace**, which is a *linearized* (additive) polynomial `∑ᵢ cᵢ X^{p^i}`. This file
proves the correct structural fact for that object.

## Main results

* `choose_prime_pow_cast_eq_zero` — char-`p` middle-binomial vanishing `(p^a).choose m = 0` for
  `0 < m < p^a`, via Frobenius vs. the binomial theorem.
* `hasseDeriv_X_pow_prime_pow_eq_zero` — `hasseDeriv m (X^{p^a}) = 0` for `0 < m < p^a`.
* `hasseDeriv_X_pow_prime_pow_sub_one` — the inseparable form `hasseDeriv m (X^{p^a} - 1) = 0`.
* `hasseDeriv_X_pow_prime_pow_natDegree_le` — **decoupling:** every Hasse derivative of order
  `m ≥ 1` of a `p`-power monomial `X^{p^a}` is a *constant* polynomial.
* `hasseDeriv_linearizedPoly_natDegree_le` — every Hasse derivative of order `m ≥ 1` of a
  linearized polynomial is a constant. This is precisely why multiplicity/derivative constraints
  decouple over additive evaluation domains.
* `derivative_linearizedPoly_natDegree_le` — the classical separability backbone: the formal
  derivative of a linearized polynomial is a constant (`m = 1` instance).

All results are hole-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`). They are
honest scaffolding for the open derandomization direction; they do **not** by themselves bound any
interpolation-matrix rank, pin the threshold `δ*`, or resolve any Grand Challenge.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Tracking issue #232; direction §7.1 (derandomizing capacity results for explicit domains).
-/

open Polynomial
open scoped BigOperators

namespace ProximityGap.LinearizedPolynomialHasse

variable {R : Type*} [CommRing R]

/-- **Char-`p` middle binomial vanishing.** For a commutative ring of characteristic `p` (prime),
`(p^a).choose m = 0` whenever `0 < m < p^a`. Proof: compare the coefficient of `X^m` in
`(X + 1)^{p^a}` computed by Frobenius (`= X^{p^a} + 1`) versus the binomial theorem. -/
lemma choose_prime_pow_cast_eq_zero (p : ℕ) [Fact p.Prime] [CharP R p]
    (a m : ℕ) (hm : 0 < m) (hlt : m < p ^ a) : ((p ^ a).choose m : R) = 0 := by
  have hfrob : (X + 1 : R[X]) ^ (p ^ a) = X ^ (p ^ a) + 1 := by
    have h : (X + 1 : R[X]) ^ (p ^ a) = X ^ (p ^ a) + (1 : R[X]) ^ (p ^ a) :=
      add_pow_char_pow X 1 p a
    rwa [one_pow] at h
  have e := congrArg (fun q : R[X] => q.coeff m) hfrob
  simp only [coeff_X_add_one_pow, coeff_add, coeff_X_pow, coeff_one] at e
  rw [if_neg (Nat.ne_of_lt hlt), if_neg (Nat.pos_iff_ne_zero.mp hm), add_zero] at e
  exact e

/-- **Monomial Hasse collapse.** In characteristic `p`, `hasseDeriv m (X^{p^a}) = 0` for
`0 < m < p^a`. -/
theorem hasseDeriv_X_pow_prime_pow_eq_zero (p : ℕ) [Fact p.Prime] [CharP R p]
    (a m : ℕ) (hm : 0 < m) (hlt : m < p ^ a) :
    hasseDeriv m (X ^ (p ^ a) : R[X]) = 0 := by
  rw [X_pow_eq_monomial, hasseDeriv_monomial,
    choose_prime_pow_cast_eq_zero p a m hm hlt, mul_one, monomial_zero_right]

/-- **Inseparable vanishing-polynomial form.** In characteristic `p`,
`hasseDeriv m (X^{p^a} - 1) = 0` for `0 < m < p^a`. Note `X^{p^a} - 1 = (X - 1)^{p^a}` here, the
inseparable single-root case. -/
theorem hasseDeriv_X_pow_prime_pow_sub_one (p : ℕ) [Fact p.Prime] [CharP R p]
    (a m : ℕ) (hm : 0 < m) (hlt : m < p ^ a) :
    hasseDeriv m (X ^ (p ^ a) - 1 : R[X]) = 0 := by
  ext j
  rw [coeff_zero, hasseDeriv_coeff, coeff_sub, coeff_X_pow, coeff_one]
  by_cases hj : j + m = p ^ a
  · rw [if_pos hj, if_neg (show ¬ j + m = 0 by omega), sub_zero, mul_one, hj]
    exact choose_prime_pow_cast_eq_zero p a m hm hlt
  · rw [if_neg hj, if_neg (show ¬ j + m = 0 by omega), sub_zero, mul_zero]

/-- **Decoupling of a `p`-power monomial.** In characteristic `p`, *every* Hasse derivative of
order `m ≥ 1` of the monomial `X^{p^a}` is a constant polynomial. (For `m < p^a` it is `0`; for
`m = p^a` it is `1`; for `m > p^a` it is `0` by degree.) This constancy is the algebraic backbone
of linearized/additive vanishing polynomials. -/
theorem hasseDeriv_X_pow_prime_pow_natDegree_le (p : ℕ) [Fact p.Prime] [CharP R p]
    (a m : ℕ) (hm : 0 < m) :
    (hasseDeriv m (X ^ (p ^ a) : R[X])).natDegree ≤ 0 := by
  rcases lt_or_ge m (p ^ a) with hlt | hge
  · rw [hasseDeriv_X_pow_prime_pow_eq_zero p a m hm hlt]; simp
  · refine (natDegree_hasseDeriv_le _ _).trans ?_
    have hd : (X ^ (p ^ a) : R[X]).natDegree ≤ p ^ a := natDegree_X_pow_le _
    omega

/-- A **linearized** (additive / `p`-)polynomial: a finite `R`-combination of `p`-power
monomials `X^{p^i}`. Over `𝔽_p` such polynomials are exactly the additive maps `x ↦ P(x)`, and
the vanishing polynomial of an `𝔽_p`-subspace is of this form. -/
noncomputable def linearizedPoly (p : ℕ) (c : ℕ → R) (s : Finset ℕ) : R[X] :=
  ∑ i ∈ s, C (c i) * X ^ (p ^ i)

private lemma hasseDeriv_C_mul (m : ℕ) (r : R) (q : R[X]) :
    hasseDeriv m (C r * q) = C r * hasseDeriv m q := by
  rw [← smul_eq_C_mul, map_smul, smul_eq_C_mul]

/-- **Linearized Hasse structure.** In characteristic `p`, every Hasse derivative of order
`m ≥ 1` of a linearized polynomial is a constant. This is precisely why the multiplicity /
derivative constraints of a Guruswami–Sudan interpolation decouple over an additive (e.g. binary
STARK) evaluation domain: each order-`m` constraint contributes only a *scalar* relation. -/
theorem hasseDeriv_linearizedPoly_natDegree_le (p : ℕ) [Fact p.Prime] [CharP R p]
    (c : ℕ → R) (s : Finset ℕ) (m : ℕ) (hm : 0 < m) :
    (hasseDeriv m (linearizedPoly p c s)).natDegree ≤ 0 := by
  unfold linearizedPoly
  rw [map_sum]
  refine (natDegree_sum_le _ _).trans ?_
  simp only [Finset.fold_max_le]
  refine ⟨Nat.zero_le _, fun i _ => ?_⟩
  rw [Function.comp_apply, hasseDeriv_C_mul]
  refine (natDegree_C_mul_le _ _).trans ?_
  exact hasseDeriv_X_pow_prime_pow_natDegree_le p i m hm

/-- **Separability backbone (classical).** In characteristic `p`, the formal derivative of a
linearized polynomial is a constant — the `m = 1` instance of the decoupling above. (Concretely
the derivative equals the linear coefficient `c₀`, the obstruction governing separability of
additive polynomials.) -/
theorem derivative_linearizedPoly_natDegree_le (p : ℕ) [Fact p.Prime] [CharP R p]
    (c : ℕ → R) (s : Finset ℕ) :
    (derivative (linearizedPoly p c s)).natDegree ≤ 0 := by
  rw [← hasseDeriv_one]
  exact hasseDeriv_linearizedPoly_natDegree_le p c s 1 one_pos

/-- **The defining additivity.** In characteristic `p`, the evaluation map `x ↦ P(x)` of a
linearized polynomial `P = ∑ᵢ cᵢ X^{p^i}` is additive: `P(x + y) = P(x) + P(y)`. This is why such
`P` are called *linearized* / *additive*, and is the bridge to subspace vanishing polynomials: the
vanishing polynomial of an `𝔽_p`-subspace `V` is the linearized polynomial whose evaluation map is
the additive `V`-quotient projection. Proof: Frobenius `(x + y)^{p^i} = x^{p^i} + y^{p^i}` term by
term. -/
theorem eval_linearizedPoly_add (p : ℕ) [Fact p.Prime] [CharP R p]
    (c : ℕ → R) (s : Finset ℕ) (x y : R) :
    (linearizedPoly p c s).eval (x + y)
      = (linearizedPoly p c s).eval x + (linearizedPoly p c s).eval y := by
  unfold linearizedPoly
  simp only [eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [add_pow_char_pow, mul_add]

/-- A linearized polynomial vanishes at `0` (every monomial `X^{p^i}` has exponent `p^i ≥ 1`). -/
theorem eval_linearizedPoly_zero (p : ℕ) [Fact p.Prime] (c : ℕ → R) (s : Finset ℕ) :
    (linearizedPoly p c s).eval 0 = 0 := by
  unfold linearizedPoly
  simp only [eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [zero_pow (pow_ne_zero i (Nat.Prime.ne_zero (Fact.out))), mul_zero]

/-- **The evaluation map of a linearized polynomial as an additive homomorphism.** Packaging
`eval_linearizedPoly_add` and `eval_linearizedPoly_zero`: over a characteristic-`p` ring, the map
`x ↦ P(x)` of a linearized `P` is an `R →+ R`. -/
noncomputable def linearizedEvalHom (p : ℕ) [Fact p.Prime] [CharP R p]
    (c : ℕ → R) (s : Finset ℕ) : R →+ R where
  toFun x := (linearizedPoly p c s).eval x
  map_zero' := eval_linearizedPoly_zero p c s
  map_add' := eval_linearizedPoly_add p c s

/-- **Linearized polynomial ⟺ subspace vanishing polynomial (the root-set correspondence).** The
root set of a linearized polynomial is exactly the kernel of its additive evaluation map, hence an
*additive subgroup* of `R`. This is the algebraic content of "the evaluation domain of a binary
STARK is an additive subspace": such a domain is precisely the root set of a linearized vanishing
polynomial. -/
theorem linearizedRoots_eq_ker (p : ℕ) [Fact p.Prime] [CharP R p]
    (c : ℕ → R) (s : Finset ℕ) :
    {x : R | (linearizedPoly p c s).eval x = 0}
      = ((linearizedEvalHom p c s).ker : Set R) := by
  ext x
  simp only [Set.mem_setOf_eq, SetLike.mem_coe, AddMonoidHom.mem_ker, linearizedEvalHom,
    AddMonoidHom.coe_mk, ZeroHom.coe_mk]

#print axioms choose_prime_pow_cast_eq_zero
#print axioms hasseDeriv_X_pow_prime_pow_eq_zero
#print axioms hasseDeriv_X_pow_prime_pow_sub_one
#print axioms hasseDeriv_X_pow_prime_pow_natDegree_le
#print axioms hasseDeriv_linearizedPoly_natDegree_le
#print axioms derivative_linearizedPoly_natDegree_le
#print axioms eval_linearizedPoly_add
#print axioms eval_linearizedPoly_zero
#print axioms linearizedRoots_eq_ker

/-! ## Concrete validation: the Artin–Schreier polynomial `X^p - X`

The whole abstract machinery is non-vacuous: the canonical additive polynomial `X^p - X` is a
linearized polynomial whose root set is exactly the prime field `{x | x^p = x}` — the smallest
additive evaluation domain — and whose derivative is the nonzero constant `-1` (so it is
separable, the multiplicity-1 condition required of a valid evaluation domain). -/
section ArtinSchreier

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] (p : ℕ) [Fact p.Prime] [CharP F p]

/-- Coefficient data exhibiting `X^p - X` as a linearized polynomial supported on `{0, 1}`. -/
private def asCoeff : ℕ → F := fun i => if i = 0 then -1 else 1

/-- `X^p - X` is the linearized polynomial `-X^{p^0} + X^{p^1}`. -/
theorem artinSchreier_eq_linearizedPoly :
    (X ^ p - X : F[X]) = linearizedPoly p (asCoeff (F := F)) {0, 1} := by
  have h0 : asCoeff (F := F) 0 = -1 := rfl
  have h1 : asCoeff (F := F) 1 = 1 := rfl
  rw [linearizedPoly, Finset.sum_pair (show (0 : ℕ) ≠ 1 by decide), h0, h1, pow_zero, pow_one,
    map_neg, map_one]
  ring

/-- Evaluation of the Artin–Schreier polynomial. -/
theorem eval_artinSchreier (x : F) : (X ^ p - X : F[X]).eval x = x ^ p - x := by
  simp

/-- The roots of `X^p - X` are exactly the elements fixed by Frobenius (the prime field). -/
theorem artinSchreier_root_iff (x : F) : (X ^ p - X : F[X]).eval x = 0 ↔ x ^ p = x := by
  rw [eval_artinSchreier, sub_eq_zero]

/-- The derivative of `X^p - X` is the nonzero constant `-1`: the polynomial is separable, so its
root set is a genuine multiplicity-1 evaluation domain. -/
theorem derivative_artinSchreier : derivative (X ^ p - X : F[X]) = -1 := by
  rw [derivative_sub, derivative_X_pow, derivative_X, CharP.cast_eq_zero, map_zero, zero_mul,
    zero_sub]

/-- The prime field `{x | x^p = x}` is an additive subgroup of `F` — recovered as a concrete
instance of the general linearized root-subgroup correspondence `linearizedRoots_eq_ker`. -/
theorem artinSchreier_primeField_eq_ker :
    {x : F | x ^ p = x}
      = ((linearizedEvalHom p (asCoeff (F := F)) {0, 1}).ker : Set F) := by
  have h := linearizedRoots_eq_ker p (asCoeff (F := F)) {0, 1}
  rw [← artinSchreier_eq_linearizedPoly] at h
  rw [← h]
  ext x
  rw [Set.mem_setOf_eq, Set.mem_setOf_eq, artinSchreier_root_iff]

end ArtinSchreier

#print axioms artinSchreier_eq_linearizedPoly
#print axioms derivative_artinSchreier
#print axioms artinSchreier_primeField_eq_ker

end ProximityGap.LinearizedPolynomialHasse
