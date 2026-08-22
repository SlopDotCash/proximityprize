/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ChebotarevValuationModP
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ChebotarevVandermondeCrux
import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# The `n = 3` instance of the generalized-Vandermonde alternant crux of Chebotarev (#407)

`_ChebotarevValuationModP.lean` reduced the all-`n` Chebotarev minor theorem to the deep crux
`GeneralizedVandermondeNonzeroModP p n` — the lowest-order `(X − 1)`-Taylor coefficient of the
integer minor polynomial `detPoly ri ci` (the *generalized-Vandermonde alternant*) is **nonzero
mod `p`** for injective row/column selections `ri ci : Fin n → ZMod p`. The siblings proved the
reduction and the `n ≤ 1` boundary; the `n = 2` case was claimed in a docstring but never actually
formalized. This file delivers the genuine **`n = 3` instance of the crux** by computing the
alternant in closed form.

## What is PROVEN here (axiom-clean)

* **`taylor_one_X_pow_coeff`** : `(taylor 1 (X^a)).coeff k = C(a, k)` (the `k`-th Taylor-at-`1`
  coefficient of a monomial is a binomial coefficient — `hasseDeriv` of a monomial).

* **`alternant_three_eq`** : the integer `n = 3` alternant, expanded. Reading the degree-`3`
  Taylor-at-`1` coefficient off the six signed permutation monomials of the `3 × 3` determinant,
  `alternant ri ci = Σ_σ sign(σ)·C(s_σ, 3)` where `s_σ = e_{0σ0}+e_{1σ1}+e_{2σ2}` and
  `e i j = minorExp ri ci i j`.

* **`choose_three_zmod`** : `6·(C(a,3) : ZMod p) = a(a−1)(a−2)` (the cubic descending-factorial
  identity, cast to `ZMod p`).

* **`e_cast`** : `((minorExp ri ci i j : ℕ) : ZMod p) = −(ci j · ri i)` (the exponent cast).

* **`six_alternantModP_eq`** (the closed form, **all `p`**) : multiplying the alternant by `6` and
  casting mod `p`, the cubic identity linearizes each of the six binomial terms and the
  antisymmetric sum **collapses to a pure Vandermonde difference product**:
  `6·alternantModP ri ci = −3·V_r·V_c`, where
  `V_r = (ri 0 − ri 1)(ri 0 − ri 2)(ri 1 − ri 2)` and
  `V_c = (ci 0 − ci 1)(ci 0 − ci 2)(ci 1 − ci 2)`.
  (Verified first by the probe `scripts/probes/probe_407_chebotarev_alternant_n3.py`; the constant,
  linear, and quadratic parts of `t(t−1)(t−2)` antisymmetrize away — a pure `ring` identity. The
  factor `(p−1)/2 = −2⁻¹` is the alternant-to-Vandermonde ratio observed in the probe.)

* **`generalizedVandermondeNonzeroModP_three`** (the **headline**) : the `n = 3` instance of the
  deep crux, for **every prime `p`**. For `p ≥ 5`: from `6·alternantModP = −3·V_r·V_c` with `6, 3`
  invertible and `V_r, V_c ≠ 0` (injectivity), `alternantModP ≠ 0`. For `p = 3`: `6 ≡ 0`, so the
  closed form degenerates; the `n = 3` case is instead a **finite decidable check** over the `27²`
  functions `Fin 3 → ZMod 3` (the alternant is `±1 (mod 3)` on the `36` injective pairs, by Lucas —
  `C(4,3)≡1`). For `p = 2`: vacuous (`Fin 3 → ZMod 2` has no injective map). So the crux holds at
  `n = 3` for all primes with **no prime restriction**.

## The honest BOUNDARY and the general-`n` residual

* **`p = 3` vs `p ≥ 5`** : the *clean Vandermonde-product mechanism* needs `2, 3` invertible mod `p`
  (i.e. `p ≥ 5`). At `p = 3` the result still holds but by a *different* (finite/Lucas) mechanism,
  not the closed form. The headline covers both via a case split, so it is genuinely all-prime.

* **The general-`n` factorization is NOT claimed proven.** The probe
  (`probe_407_chebotarev_alternant_n3.py` and the `n = 4, 5` sweep) *suggests* the alternant factors
  as `c_n·V_r·V_c` (a pure difference product, with an `n`-dependent constant `c_n`) even for
  `n ≥ 4` — surprising, since a generic generalized Vandermonde carries a Schur-polynomial factor
  that can vanish. This is plausibly forced by the **rank-`1`** exponent structure
  `e_{ij} = −(c_j r_i) (mod p)`, but it is **only sampled numerical evidence** for `n ≥ 4` (the
  `n = 4` constant is unexplained and the symbolic antisymmetrization is not done). Per the #407
  honesty contract we do **not** state an all-`n` reduction theorem:
  `GeneralizedVandermondeNonzeroModP p n` stays the named-open crux for `n ≥ 4`. Only the `n = 3`
  instance is proven.

## Honesty contract (per #407)

`GeneralizedVandermondeNonzeroModP` stays the genuine deep core for `n ≥ 4`; we never claim it or
general Chebotarev proven. `generalizedVandermondeNonzeroModP_three` is a genuine theorem
(all primes, `n = 3`); `six_alternantModP_eq` is its probe-verified closed form. No `sorry`, no
`native_decide` (the `p = 3` case uses kernel `decide`).

Reference: P. Stevenhagen & H. W. Lenstra, *Chebotarëv and his density theorem*, Math. Intelligencer
18 (1996); T. Tao, *An uncertainty principle for cyclic groups of prime order* (2005).

Axiom-clean (`propext, Classical.choice, Quot.sound`; no `sorryAx`). Issue #407.
-/

open Finset ZMod Matrix Polynomial Complex
open ProximityGap.Frontier.ChebotarevReductionModP
open ProximityGap.Frontier.ChebotarevValuationModP

namespace ProximityGap.Frontier.ChebotarevAlternantThree

variable {p : ℕ} [Fact p.Prime]

/-! ## Helper lemmas. -/

/-- **The `k`-th Taylor-at-`1` coefficient of a monomial (PROVEN).** `(taylor 1 (X^a)).coeff k =
C(a, k)`: by `taylor_coeff` it is `(hasseDeriv k (X^a)).eval 1`, and `hasseDeriv` of a monomial is
the monomial `C(a,k)·X^{a-k}`, evaluating to `C(a,k)` at `1`. -/
theorem taylor_one_X_pow_coeff (a k : ℕ) :
    (taylor (1 : ℤ) (X ^ a)).coeff k = (a.choose k : ℤ) := by
  rw [taylor_coeff, ← monomial_one_right_eq_X_pow, hasseDeriv_monomial]
  simp

/-- **The cubic descending-factorial identity mod `p` (PROVEN).** `6·(C(a,3) : ZMod p) =
a(a−1)(a−2)`. Over `ℤ`, `6·C(a,3) = a.descFactorial 3 = (descPochhammer ℤ 3).eval a = a(a−1)(a−2)`;
cast to `ZMod p` through the integer ring hom. -/
theorem choose_three_zmod (a : ℕ) :
    6 * (a.choose 3 : ZMod p) = (a : ZMod p) * ((a : ZMod p) - 1) * ((a : ZMod p) - 2) := by
  have hI : 6 * (a.choose 3 : ℤ) = (a : ℤ) * ((a : ℤ) - 1) * ((a : ℤ) - 2) := by
    have h1 : a.descFactorial 3 = Nat.factorial 3 * a.choose 3 :=
      Nat.descFactorial_eq_factorial_mul_choose a 3
    have h2 : (a.descFactorial 3 : ℤ) = (a : ℤ) * ((a : ℤ) - 1) * ((a : ℤ) - 2) := by
      rw [← descPochhammer_eval_eq_descFactorial ℤ a 3]
      simp [descPochhammer_succ_right]
    rw [← h2, h1, show Nat.factorial 3 = 6 from rfl]
    push_cast; ring
  have := congrArg (Int.cast : ℤ → ZMod p) hI
  push_cast at this
  convert this using 2

/-- Shorthand for the `(i, j)` exponent of a `3 × 3` minor. -/
abbrev e (ri ci : Fin 3 → ZMod p) (i j : Fin 3) : ℕ := minorExp ri ci i j

/-- **The exponent cast (PROVEN).** `((minorExp ri ci i j : ℕ) : ZMod p) = −(ci j · ri i)`
(the exponent is the canonical representative of `−(ci j · ri i)`). -/
theorem e_cast (ri ci : Fin 3 → ZMod p) (i j : Fin 3) :
    ((e ri ci i j : ℕ) : ZMod p) = -(ci j * ri i) := by
  rw [e, minorExp, ZMod.natCast_zmod_val]

/-! ## The `n = 3` alternant as a signed sum of six binomials, and its closed form. -/

/-- **The `n = 3` alternant, expanded (PROVEN).** Expanding the `3 × 3` determinant into its six
signed permutation terms `± X^{s_σ}` and reading off the degree-`3` Taylor-at-`1` coefficient (which
on each monomial `X^a` is `C(a, 3)`), the integer alternant is the signed sum of six binomials. -/
theorem alternant_three_eq (ri ci : Fin 3 → ZMod p) :
    alternant ri ci
      = (e ri ci 0 0 + e ri ci 1 1 + e ri ci 2 2).choose 3
        - (e ri ci 0 0 + e ri ci 1 2 + e ri ci 2 1).choose 3
        - (e ri ci 0 1 + e ri ci 1 0 + e ri ci 2 2).choose 3
        + (e ri ci 0 1 + e ri ci 1 2 + e ri ci 2 0).choose 3
        + (e ri ci 0 2 + e ri ci 1 0 + e ri ci 2 1).choose 3
        - (e ri ci 0 2 + e ri ci 1 1 + e ri ci 2 0).choose 3 := by
  rw [alternant, show (3 : ℕ) * (3 - 1) / 2 = 3 from by norm_num]
  have hdp : detPoly ri ci
      = X ^ (e ri ci 0 0 + e ri ci 1 1 + e ri ci 2 2)
        - X ^ (e ri ci 0 0 + e ri ci 1 2 + e ri ci 2 1)
        - X ^ (e ri ci 0 1 + e ri ci 1 0 + e ri ci 2 2)
        + X ^ (e ri ci 0 1 + e ri ci 1 2 + e ri ci 2 0)
        + X ^ (e ri ci 0 2 + e ri ci 1 0 + e ri ci 2 1)
        - X ^ (e ri ci 0 2 + e ri ci 1 1 + e ri ci 2 0) := by
    rw [detPoly, Matrix.det_fin_three]
    simp only [Matrix.of_apply, e, ← pow_add]
  rw [hdp]
  simp only [map_add, map_sub, coeff_add, coeff_sub, taylor_one_X_pow_coeff]

/-- **The `6·alternant` closed form mod `p` (PROVEN, every `p`).** Multiplying the alternant by `6`
and casting mod `p`, the cubic identity `6·C(s,3) = s(s−1)(s−2)` linearizes each of the six binomial
terms; the antisymmetric sum collapses (the constant, linear, and quadratic parts of `t(t−1)(t−2)`
cancel under antisymmetrization) to `−3` times the product of the two Vandermonde difference
products of `ri` and `ci`. Probe-verified (`probe_407_chebotarev_alternant_n3.py`); a pure
`ring` identity after casting the exponents. -/
theorem six_alternantModP_eq (ri ci : Fin 3 → ZMod p) :
    6 * alternantModP ri ci
      = -3 * ((ri 0 - ri 1) * (ri 0 - ri 2) * (ri 1 - ri 2))
            * ((ci 0 - ci 1) * (ci 0 - ci 2) * (ci 1 - ci 2)) := by
  rw [alternantModP, alternant_three_eq]
  push_cast
  have key : ∀ a : ℕ, 6 * (a.choose 3 : ZMod p)
      = (a : ZMod p) * ((a : ZMod p) - 1) * ((a : ZMod p) - 2) := choose_three_zmod
  -- linearize the six `6·C(s_σ,3)` terms into cubics in the casts `↑s_σ`.
  have hstep : 6 *
      (((e ri ci 0 0 + e ri ci 1 1 + e ri ci 2 2).choose 3 : ZMod p)
        - ((e ri ci 0 0 + e ri ci 1 2 + e ri ci 2 1).choose 3 : ZMod p)
        - ((e ri ci 0 1 + e ri ci 1 0 + e ri ci 2 2).choose 3 : ZMod p)
        + ((e ri ci 0 1 + e ri ci 1 2 + e ri ci 2 0).choose 3 : ZMod p)
        + ((e ri ci 0 2 + e ri ci 1 0 + e ri ci 2 1).choose 3 : ZMod p)
        - ((e ri ci 0 2 + e ri ci 1 1 + e ri ci 2 0).choose 3 : ZMod p))
      = (((e ri ci 0 0 + e ri ci 1 1 + e ri ci 2 2 : ℕ) : ZMod p)
            * (((e ri ci 0 0 + e ri ci 1 1 + e ri ci 2 2 : ℕ) : ZMod p) - 1)
            * (((e ri ci 0 0 + e ri ci 1 1 + e ri ci 2 2 : ℕ) : ZMod p) - 2))
        - (((e ri ci 0 0 + e ri ci 1 2 + e ri ci 2 1 : ℕ) : ZMod p)
            * (((e ri ci 0 0 + e ri ci 1 2 + e ri ci 2 1 : ℕ) : ZMod p) - 1)
            * (((e ri ci 0 0 + e ri ci 1 2 + e ri ci 2 1 : ℕ) : ZMod p) - 2))
        - (((e ri ci 0 1 + e ri ci 1 0 + e ri ci 2 2 : ℕ) : ZMod p)
            * (((e ri ci 0 1 + e ri ci 1 0 + e ri ci 2 2 : ℕ) : ZMod p) - 1)
            * (((e ri ci 0 1 + e ri ci 1 0 + e ri ci 2 2 : ℕ) : ZMod p) - 2))
        + (((e ri ci 0 1 + e ri ci 1 2 + e ri ci 2 0 : ℕ) : ZMod p)
            * (((e ri ci 0 1 + e ri ci 1 2 + e ri ci 2 0 : ℕ) : ZMod p) - 1)
            * (((e ri ci 0 1 + e ri ci 1 2 + e ri ci 2 0 : ℕ) : ZMod p) - 2))
        + (((e ri ci 0 2 + e ri ci 1 0 + e ri ci 2 1 : ℕ) : ZMod p)
            * (((e ri ci 0 2 + e ri ci 1 0 + e ri ci 2 1 : ℕ) : ZMod p) - 1)
            * (((e ri ci 0 2 + e ri ci 1 0 + e ri ci 2 1 : ℕ) : ZMod p) - 2))
        - (((e ri ci 0 2 + e ri ci 1 1 + e ri ci 2 0 : ℕ) : ZMod p)
            * (((e ri ci 0 2 + e ri ci 1 1 + e ri ci 2 0 : ℕ) : ZMod p) - 1)
            * (((e ri ci 0 2 + e ri ci 1 1 + e ri ci 2 0 : ℕ) : ZMod p) - 2)) := by
    linear_combination key (e ri ci 0 0 + e ri ci 1 1 + e ri ci 2 2)
      - key (e ri ci 0 0 + e ri ci 1 2 + e ri ci 2 1)
      - key (e ri ci 0 1 + e ri ci 1 0 + e ri ci 2 2)
      + key (e ri ci 0 1 + e ri ci 1 2 + e ri ci 2 0)
      + key (e ri ci 0 2 + e ri ci 1 0 + e ri ci 2 1)
      - key (e ri ci 0 2 + e ri ci 1 1 + e ri ci 2 0)
  rw [hstep]
  -- split the natural-sum casts, substitute `↑(e i j) = −(ci j · ri i)`, antisymmetrize.
  push_cast [e_cast]
  ring

/-! ## Vandermonde nonvanishing from injectivity. -/

/-- For injective `ri : Fin 3 → ZMod p`, the Vandermonde difference product
`(ri 0 − ri 1)(ri 0 − ri 2)(ri 1 − ri 2)` is nonzero (a field, all three differences nonzero). -/
theorem vandermonde_three_ne_zero (ri : Fin 3 → ZMod p) (hri : Function.Injective ri) :
    (ri 0 - ri 1) * (ri 0 - ri 2) * (ri 1 - ri 2) ≠ 0 := by
  have h01 : ri 0 ≠ ri 1 := fun h => by simpa using hri h
  have h02 : ri 0 ≠ ri 2 := fun h => by simpa using hri h
  have h12 : ri 1 ≠ ri 2 := fun h => by simpa using hri h
  exact mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr h01) (sub_ne_zero.mpr h02))
    (sub_ne_zero.mpr h12)

/-- **The `p = 3` finite check (PROVEN by `decide`).** The six-binomial integer alternant formula
cast mod `3` is nonzero on every *injective* pair `ri ci : Fin 3 → ZMod 3` — a finite kernel
`decide` over the `27²` functions (no `Fact` instance in scope so the goal has no free variables).
The clean
`6·alternant = −3·V_r·V_c` mechanism degenerates at `p = 3` (`6 ≡ 0`); this is the separate Lucas
route (`C(4,3) ≡ 1 (mod 3)`). -/
theorem alternantModP_three_at_three :
    ∀ ri ci : Fin 3 → ZMod 3, Function.Injective ri → Function.Injective ci →
      (((minorExp ri ci 0 0 + minorExp ri ci 1 1 + minorExp ri ci 2 2).choose 3
          - (minorExp ri ci 0 0 + minorExp ri ci 1 2 + minorExp ri ci 2 1).choose 3
          - (minorExp ri ci 0 1 + minorExp ri ci 1 0 + minorExp ri ci 2 2).choose 3
          + (minorExp ri ci 0 1 + minorExp ri ci 1 2 + minorExp ri ci 2 0).choose 3
          + (minorExp ri ci 0 2 + minorExp ri ci 1 0 + minorExp ri ci 2 1).choose 3
          - (minorExp ri ci 0 2 + minorExp ri ci 1 1 + minorExp ri ci 2 0).choose 3 : ℤ) : ZMod 3) ≠ 0 := by
  decide

/-! ## The headline: the `n = 3` instance of the crux (every prime). -/

/-- **The `n = 3` instance of the generalized-Vandermonde alternant crux (PROVEN, every prime).**

For every prime `p` and every pair of *injective* selections `ri ci : Fin 3 → ZMod p`, the alternant
`alternantModP ri ci` (the lowest-order `(1 − ζ)`-coefficient of the `3 × 3` minor determinant) is
nonzero mod `p` — the `n = 3` case of the deep heart of Chebotarev's theorem.

Proof. Case split on `p`:
* `p ≥ 5`: the closed form `6·alternantModP = −3·V_r·V_c` (`six_alternantModP_eq`) has `6, 3`
  invertible and `V_r, V_c ≠ 0` (injectivity), so `alternantModP ≠ 0`.
* `p = 3`: the closed form degenerates (`6 ≡ 0`); instead the six-binomial integer formula
  (`alternant_three_eq`) cast mod `3` is `≠ 0` by a finite kernel `decide` over `Fin 3 → ZMod 3`
  (the alternant is `±1 (mod 3)` on every injective pair, by Lucas — `C(4,3) ≡ 1`).
* `p = 2`: vacuous — `Fin 3 → ZMod 2` admits no injective map (`3 > 2`). -/
theorem generalizedVandermondeNonzeroModP_three :
    GeneralizedVandermondeNonzeroModP p 3 := by
  intro ri ci hri hci
  have hp2 := (Fact.out (p := p.Prime)).two_le
  -- `p = 2`: no injective `Fin 3 → ZMod 2` (`3 = card (Fin 3) ≤ card (ZMod 2) = p`).
  by_cases hp2' : p = 2
  · subst hp2'
    have hcard := Fintype.card_le_of_injective ri hri
    rw [Fintype.card_fin, ZMod.card] at hcard
    omega
  -- `p = 3`: finite decidable check on the six-binomial integer formula.
  by_cases hp3 : p = 3
  · subst hp3
    rw [alternantModP, alternant_three_eq]
    exact alternantModP_three_at_three ri ci hri hci
  · -- `p ≥ 5`: closed-form nonvanishing (`6, 3` invertible; `V_r, V_c ≠ 0`).
    have hp5 : 5 ≤ p := by
      rcases (Fact.out (p := p.Prime)).eq_two_or_odd' with h2 | hodd
      · exact absurd h2 hp2'
      · -- `p` odd, `p ≥ 2`, `p ≠ 3` ⟹ `p ≥ 5`.
        rcases Nat.lt_or_ge p 5 with hlt | hge
        · interval_cases p
          · exact absurd rfl hp2'
          · exact absurd rfl hp3
          · simp [Nat.odd_iff] at hodd
        · exact hge
    have h3 : ((3 : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hdvd; have := Nat.le_of_dvd (by norm_num) hdvd; omega
    have h3' : (-3 : ZMod p) ≠ 0 := by
      have : (3 : ZMod p) ≠ 0 := by simpa using h3
      simpa using neg_ne_zero.mpr this
    intro hzero
    have hsix := six_alternantModP_eq ri ci
    rw [hzero, mul_zero] at hsix
    -- `0 = −3·V_r·V_c` with all three factors nonzero — contradiction.
    have hrhs : -3 * ((ri 0 - ri 1) * (ri 0 - ri 2) * (ri 1 - ri 2))
        * ((ci 0 - ci 1) * (ci 0 - ci 2) * (ci 1 - ci 2)) ≠ 0 :=
      mul_ne_zero (mul_ne_zero h3' (vandermonde_three_ne_zero ri hri))
        (vandermonde_three_ne_zero ci hci)
    exact hrhs hsix.symm

end ProximityGap.Frontier.ChebotarevAlternantThree

/-! ## Axiom audit (expected: `propext, Classical.choice, Quot.sound` only — no `sorryAx`). -/
#print axioms ProximityGap.Frontier.ChebotarevAlternantThree.taylor_one_X_pow_coeff
#print axioms ProximityGap.Frontier.ChebotarevAlternantThree.choose_three_zmod
#print axioms ProximityGap.Frontier.ChebotarevAlternantThree.e_cast
#print axioms ProximityGap.Frontier.ChebotarevAlternantThree.alternant_three_eq
#print axioms ProximityGap.Frontier.ChebotarevAlternantThree.six_alternantModP_eq
#print axioms ProximityGap.Frontier.ChebotarevAlternantThree.vandermonde_three_ne_zero
#print axioms ProximityGap.Frontier.ChebotarevAlternantThree.alternantModP_three_at_three
#print axioms ProximityGap.Frontier.ChebotarevAlternantThree.generalizedVandermondeNonzeroModP_three
