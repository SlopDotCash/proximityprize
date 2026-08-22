/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ChebotarevValuationModP
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ChebotarevAlternantThree
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.LinearAlgebra.Vandermonde

/-!
# The `n = 4` instance of the generalized-Vandermonde alternant crux of Chebotarev (#407)

Sibling `_ChebotarevAlternantThree.lean` discharged the `n = 3` instance of the deep crux
`GeneralizedVandermondeNonzeroModP p n` with the closed form `6·alternant = −3·V_r·V_c`. This file
delivers the genuine **`n = 4` instance** (for `p ≥ 7`), with the probe-verified closed form

  **`720·alternantModP = 60·V_r·V_c`**     (equivalently `alternant = (1/12)·V_r·V_c`),

where `V_r = ∏_{i<j}(ri i − ri j)`, `V_c = ∏_{i<j}(ci i − ci j)` are the two `4`-point Vandermonde
difference products.

## What is PROVEN here (axiom-clean)

* **`det_fin_four`** : the `4 × 4` determinant Leibniz expansion (cofactor along row `0`).

* **`choose_six_zmod`** : `720·(C(a,6) : ZMod p) = a(a−1)(a−2)(a−3)(a−4)(a−5)` (the order-`6`
  descending-factorial identity, cast to `ZMod p`).

* **`alternant_four_eq`** : the integer `n = 4` alternant, expanded. Reading the degree-`6`
  Taylor-at-`1` coefficient off the `24` signed permutation monomials of the `4 × 4` determinant,
  `alternant ri ci = Σ_σ sign(σ)·C(s_σ, 6)` where `s_σ = Σ_i e_{i,σ i}` and `e i j = minorExp ri ci i j`.

* **`sevenTwenty_alternantModP_eq`** (the closed form, **every `p`**) : multiplying the alternant by
  `720` and casting mod `p`, the order-`6` descending-factorial identity linearizes each of the `24`
  binomial terms and the antisymmetric sum **collapses to `60` times the product of the two
  Vandermonde difference products** : `720·alternantModP = 60·V_r·V_c`. Probe-verified
  (`scripts/probes/probe_407_chebotarev_alternant_n4.py`, full census `p = 5, 7`, sampled to
  `p = 47`; the unique rational ratio `alternant/(V_r V_c)` matching all primes is `1/12`); the
  symbolic identity `720·alternant = 60·V_r·V_c` is `ring`-checked over `ℚ[r,c]`.

* **`generalizedVandermondeNonzeroModP_four`** (the **headline**, `p ≥ 7`) : the `n = 4` instance of
  the deep crux, for every prime `p ≥ 7`. From `720·alternantModP = 60·V_r·V_c` with `720, 60`
  invertible (`p ∤ 720 = 2⁴·3²·5`, i.e. `p ≥ 7`) and `V_r, V_c ≠ 0` (injectivity), `alternantModP ≠ 0`.

## The honest BOUNDARY

* **`p = 2, 3`** : vacuous — `Fin 4 → ZMod 2` / `Fin 4 → ZMod 3` admit no injective map (`4 > p`).
  Hence `generalizedVandermondeNonzeroModP_four` only needs the `p ≥ 7` branch beyond these.

* **`p = 5`** : `Fin 4 → ZMod 5` IS injective-friendly (`4 ≤ 5`), so `p = 5` is a genuine case, but the
  order-`6` descending-factorial mechanism **degenerates** there: `720 = 2⁴·3²·5 ≡ 0 (mod 5)` and
  `60 = 2²·3·5 ≡ 0 (mod 5)`, so `720·alternantModP = 60·V_r·V_c` reads `0 = 0`. The alternant is still
  nonzero mod `5` (probe: ratio `≡ 3`, i.e. `2·alternant ≡ V_r V_c (mod 5)`), but its `(mod 5)` value
  is Lucas-type (`C(s,6) (mod 5)` is **not** a polynomial in `s`), so no `ring`/closed-form route gives
  it, and a finite `decide` over the `5⁸ = 390625` injective pairs is infeasible (measured: the bare
  enumeration alone is `> 6` min at the elaborator, before the kernel re-check). The `p = 5` case is
  therefore left **named-open** as `GeneralizedVandermondeNonzeroAtFive` (a `def … : Prop`); the headline
  takes `7 ≤ p`. (The `n = 3` sibling cleared its analogous bad prime `p = 3` by `decide` over only
  `3³ = 27` functions — here that route does not scale.)

* **The general-`n` factorization is NOT claimed proven.** The probe `c_n·V_r·V_c` factorization is
  documented numerical evidence (`c_3 = −1/2`, `c_4 = 1/12`); per the #407 honesty contract the all-`n`
  crux stays named-open. The structural antisymmetry⟹Vandermonde-divisibility route is recorded as the
  named conjecture `AlternantFactorsConstant` with the clean (easy-direction) reduction
  `crux_of_factorConstant`; the factorization itself is NOT proven (Mathlib's multivariate
  antisymmetric ⟹ Vandermonde-divisibility support is thin).

Reference: P. Stevenhagen & H. W. Lenstra, *Chebotarëv and his density theorem*, Math. Intelligencer
18 (1996); T. Tao, *An uncertainty principle for cyclic groups of prime order* (2005).

Axiom-clean (`propext, Classical.choice, Quot.sound`; no `sorryAx`, no `native_decide`). Issue #407.
-/

open Finset ZMod Matrix Polynomial Complex
open ProximityGap.Frontier.ChebotarevReductionModP
open ProximityGap.Frontier.ChebotarevValuationModP
open ProximityGap.Frontier.ChebotarevAlternantThree

namespace ProximityGap.Frontier.ChebotarevAlternantFour

variable {p : ℕ} [Fact p.Prime]

/-! ## Helper: the `4 × 4` determinant Leibniz expansion. -/

/-- **The `4 × 4` determinant, expanded (PROVEN).** Cofactor expansion along row `0`; the `24`
signed permutation terms. (Mathlib provides `det_fin_three` but not `det_fin_four`.) -/
theorem det_fin_four {R : Type*} [CommRing R] (A : Matrix (Fin 4) (Fin 4) R) :
    det A =
      A 0 0 * (A 1 1 * A 2 2 * A 3 3 - A 1 1 * A 2 3 * A 3 2 - A 1 2 * A 2 1 * A 3 3
              + A 1 2 * A 2 3 * A 3 1 + A 1 3 * A 2 1 * A 3 2 - A 1 3 * A 2 2 * A 3 1)
      - A 0 1 * (A 1 0 * A 2 2 * A 3 3 - A 1 0 * A 2 3 * A 3 2 - A 1 2 * A 2 0 * A 3 3
              + A 1 2 * A 2 3 * A 3 0 + A 1 3 * A 2 0 * A 3 2 - A 1 3 * A 2 2 * A 3 0)
      + A 0 2 * (A 1 0 * A 2 1 * A 3 3 - A 1 0 * A 2 3 * A 3 1 - A 1 1 * A 2 0 * A 3 3
              + A 1 1 * A 2 3 * A 3 0 + A 1 3 * A 2 0 * A 3 1 - A 1 3 * A 2 1 * A 3 0)
      - A 0 3 * (A 1 0 * A 2 1 * A 3 2 - A 1 0 * A 2 2 * A 3 1 - A 1 1 * A 2 0 * A 3 2
              + A 1 1 * A 2 2 * A 3 0 + A 1 2 * A 2 0 * A 3 1 - A 1 2 * A 2 1 * A 3 0) := by
  rw [det_succ_row_zero, Fin.sum_univ_four]
  simp only [det_fin_three, submatrix_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    show (Fin.succ (2:Fin 3) : Fin 4) = 3 from rfl,
    show ((0:Fin 4).succAbove (0:Fin 3) : Fin 4) = 1 from rfl,
    show ((0:Fin 4).succAbove (1:Fin 3) : Fin 4) = 2 from rfl,
    show ((0:Fin 4).succAbove (2:Fin 3) : Fin 4) = 3 from rfl,
    show ((1:Fin 4).succAbove (0:Fin 3) : Fin 4) = 0 from rfl,
    show ((1:Fin 4).succAbove (1:Fin 3) : Fin 4) = 2 from rfl,
    show ((1:Fin 4).succAbove (2:Fin 3) : Fin 4) = 3 from rfl,
    show ((2:Fin 4).succAbove (0:Fin 3) : Fin 4) = 0 from rfl,
    show ((2:Fin 4).succAbove (1:Fin 3) : Fin 4) = 1 from rfl,
    show ((2:Fin 4).succAbove (2:Fin 3) : Fin 4) = 3 from rfl,
    show ((3:Fin 4).succAbove (0:Fin 3) : Fin 4) = 0 from rfl,
    show ((3:Fin 4).succAbove (1:Fin 3) : Fin 4) = 1 from rfl,
    show ((3:Fin 4).succAbove (2:Fin 3) : Fin 4) = 2 from rfl]
  norm_num [Fin.val_zero, Fin.val_one, Fin.val_two]
  ring

/-! ## Helpers: order-6 descending factorial and the `n = 4` exponent abbreviation. -/

/-- **The order-`6` descending-factorial identity mod `p` (PROVEN).** `720·(C(a,6) : ZMod p) =
a(a−1)(a−2)(a−3)(a−4)(a−5)`. Over `ℤ`, `720·C(a,6) = a.descFactorial 6 = (descPochhammer ℤ 6).eval a`;
cast to `ZMod p`. -/
theorem choose_six_zmod (a : ℕ) :
    720 * (a.choose 6 : ZMod p)
      = (a : ZMod p) * ((a:ZMod p) - 1) * ((a:ZMod p) - 2) * ((a:ZMod p) - 3)
          * ((a:ZMod p) - 4) * ((a:ZMod p) - 5) := by
  have hI : 720 * (a.choose 6 : ℤ)
      = (a:ℤ) * ((a:ℤ)-1) * ((a:ℤ)-2) * ((a:ℤ)-3) * ((a:ℤ)-4) * ((a:ℤ)-5) := by
    have h1 : a.descFactorial 6 = Nat.factorial 6 * a.choose 6 :=
      Nat.descFactorial_eq_factorial_mul_choose a 6
    have h2 : (a.descFactorial 6 : ℤ)
        = (a:ℤ) * ((a:ℤ)-1) * ((a:ℤ)-2) * ((a:ℤ)-3) * ((a:ℤ)-4) * ((a:ℤ)-5) := by
      rw [← descPochhammer_eval_eq_descFactorial ℤ a 6]
      simp [descPochhammer_succ_right]
    rw [← h2, h1, show Nat.factorial 6 = 720 from rfl]
    push_cast; ring
  have := congrArg (Int.cast : ℤ → ZMod p) hI
  push_cast at this
  convert this using 2

/-- Shorthand for the `(i, j)` exponent of a `4 × 4` minor. -/
abbrev e (ri ci : Fin 4 → ZMod p) (i j : Fin 4) : ℕ := minorExp ri ci i j

/-- The exponent cast (PROVEN), `n = 4` version. `((minorExp ri ci i j : ℕ) : ZMod p) = −(ci j · ri i)`. -/
theorem e_cast (ri ci : Fin 4 → ZMod p) (i j : Fin 4) :
    ((e ri ci i j : ℕ) : ZMod p) = -(ci j * ri i) := by
  rw [e, minorExp, ZMod.natCast_zmod_val]

/-! ## The `n = 4` alternant as a signed sum of 24 binomials, and its closed form. -/

/-- **The `n = 4` alternant, expanded (PROVEN).** Expanding the `4 × 4` determinant into its `24`
signed permutation terms `± X^{s_σ}` and reading off the degree-`6` Taylor-at-`1` coefficient (which
on each monomial `X^a` is `C(a, 6)`), the integer alternant is the signed sum of `24` binomials. -/
theorem alternant_four_eq (ri ci : Fin 4 → ZMod p) :
    alternant ri ci
      =
        (e ri ci 0 0 + e ri ci 1 1 + e ri ci 2 2 + e ri ci 3 3).choose 6
        - (e ri ci 0 0 + e ri ci 1 1 + e ri ci 2 3 + e ri ci 3 2).choose 6
        - (e ri ci 0 0 + e ri ci 1 2 + e ri ci 2 1 + e ri ci 3 3).choose 6
        + (e ri ci 0 0 + e ri ci 1 2 + e ri ci 2 3 + e ri ci 3 1).choose 6
        + (e ri ci 0 0 + e ri ci 1 3 + e ri ci 2 1 + e ri ci 3 2).choose 6
        - (e ri ci 0 0 + e ri ci 1 3 + e ri ci 2 2 + e ri ci 3 1).choose 6
        - (e ri ci 0 1 + e ri ci 1 0 + e ri ci 2 2 + e ri ci 3 3).choose 6
        + (e ri ci 0 1 + e ri ci 1 0 + e ri ci 2 3 + e ri ci 3 2).choose 6
        + (e ri ci 0 1 + e ri ci 1 2 + e ri ci 2 0 + e ri ci 3 3).choose 6
        - (e ri ci 0 1 + e ri ci 1 2 + e ri ci 2 3 + e ri ci 3 0).choose 6
        - (e ri ci 0 1 + e ri ci 1 3 + e ri ci 2 0 + e ri ci 3 2).choose 6
        + (e ri ci 0 1 + e ri ci 1 3 + e ri ci 2 2 + e ri ci 3 0).choose 6
        + (e ri ci 0 2 + e ri ci 1 0 + e ri ci 2 1 + e ri ci 3 3).choose 6
        - (e ri ci 0 2 + e ri ci 1 0 + e ri ci 2 3 + e ri ci 3 1).choose 6
        - (e ri ci 0 2 + e ri ci 1 1 + e ri ci 2 0 + e ri ci 3 3).choose 6
        + (e ri ci 0 2 + e ri ci 1 1 + e ri ci 2 3 + e ri ci 3 0).choose 6
        + (e ri ci 0 2 + e ri ci 1 3 + e ri ci 2 0 + e ri ci 3 1).choose 6
        - (e ri ci 0 2 + e ri ci 1 3 + e ri ci 2 1 + e ri ci 3 0).choose 6
        - (e ri ci 0 3 + e ri ci 1 0 + e ri ci 2 1 + e ri ci 3 2).choose 6
        + (e ri ci 0 3 + e ri ci 1 0 + e ri ci 2 2 + e ri ci 3 1).choose 6
        + (e ri ci 0 3 + e ri ci 1 1 + e ri ci 2 0 + e ri ci 3 2).choose 6
        - (e ri ci 0 3 + e ri ci 1 1 + e ri ci 2 2 + e ri ci 3 0).choose 6
        - (e ri ci 0 3 + e ri ci 1 2 + e ri ci 2 0 + e ri ci 3 1).choose 6
        + (e ri ci 0 3 + e ri ci 1 2 + e ri ci 2 1 + e ri ci 3 0).choose 6 := by
  rw [alternant, show (4 : ℕ) * (4 - 1) / 2 = 6 from by norm_num]
  have hdp : detPoly ri ci
      =
        X ^ (e ri ci 0 0 + e ri ci 1 1 + e ri ci 2 2 + e ri ci 3 3)
        - X ^ (e ri ci 0 0 + e ri ci 1 1 + e ri ci 2 3 + e ri ci 3 2)
        - X ^ (e ri ci 0 0 + e ri ci 1 2 + e ri ci 2 1 + e ri ci 3 3)
        + X ^ (e ri ci 0 0 + e ri ci 1 2 + e ri ci 2 3 + e ri ci 3 1)
        + X ^ (e ri ci 0 0 + e ri ci 1 3 + e ri ci 2 1 + e ri ci 3 2)
        - X ^ (e ri ci 0 0 + e ri ci 1 3 + e ri ci 2 2 + e ri ci 3 1)
        - X ^ (e ri ci 0 1 + e ri ci 1 0 + e ri ci 2 2 + e ri ci 3 3)
        + X ^ (e ri ci 0 1 + e ri ci 1 0 + e ri ci 2 3 + e ri ci 3 2)
        + X ^ (e ri ci 0 1 + e ri ci 1 2 + e ri ci 2 0 + e ri ci 3 3)
        - X ^ (e ri ci 0 1 + e ri ci 1 2 + e ri ci 2 3 + e ri ci 3 0)
        - X ^ (e ri ci 0 1 + e ri ci 1 3 + e ri ci 2 0 + e ri ci 3 2)
        + X ^ (e ri ci 0 1 + e ri ci 1 3 + e ri ci 2 2 + e ri ci 3 0)
        + X ^ (e ri ci 0 2 + e ri ci 1 0 + e ri ci 2 1 + e ri ci 3 3)
        - X ^ (e ri ci 0 2 + e ri ci 1 0 + e ri ci 2 3 + e ri ci 3 1)
        - X ^ (e ri ci 0 2 + e ri ci 1 1 + e ri ci 2 0 + e ri ci 3 3)
        + X ^ (e ri ci 0 2 + e ri ci 1 1 + e ri ci 2 3 + e ri ci 3 0)
        + X ^ (e ri ci 0 2 + e ri ci 1 3 + e ri ci 2 0 + e ri ci 3 1)
        - X ^ (e ri ci 0 2 + e ri ci 1 3 + e ri ci 2 1 + e ri ci 3 0)
        - X ^ (e ri ci 0 3 + e ri ci 1 0 + e ri ci 2 1 + e ri ci 3 2)
        + X ^ (e ri ci 0 3 + e ri ci 1 0 + e ri ci 2 2 + e ri ci 3 1)
        + X ^ (e ri ci 0 3 + e ri ci 1 1 + e ri ci 2 0 + e ri ci 3 2)
        - X ^ (e ri ci 0 3 + e ri ci 1 1 + e ri ci 2 2 + e ri ci 3 0)
        - X ^ (e ri ci 0 3 + e ri ci 1 2 + e ri ci 2 0 + e ri ci 3 1)
        + X ^ (e ri ci 0 3 + e ri ci 1 2 + e ri ci 2 1 + e ri ci 3 0) := by
    rw [detPoly, det_fin_four]
    simp only [Matrix.of_apply, e, ← pow_add]
    ring
  rw [hdp]
  simp only [map_add, map_sub, coeff_add, coeff_sub, taylor_one_X_pow_coeff]

/-- **The `720·alternant` closed form mod `p` (PROVEN, every `p`).** Multiplying the alternant by
`720` and casting mod `p`, the order-`6` descending-factorial identity `720·C(s,6) =
s(s−1)(s−2)(s−3)(s−4)(s−5)` linearizes each of the `24` binomial terms; the antisymmetric sum
collapses (all lower-degree symmetric parts cancel) to `60` times the product of the two `4`-point
Vandermonde difference products of `ri` and `ci`. Probe-verified
(`probe_407_chebotarev_alternant_n4.py`); a pure `ring` identity after casting the exponents. -/
theorem sevenTwenty_alternantModP_eq (ri ci : Fin 4 → ZMod p) :
    720 * alternantModP ri ci
      = 60 * ((ri 0 - ri 1) * (ri 0 - ri 2) * (ri 0 - ri 3) * (ri 1 - ri 2) * (ri 1 - ri 3) * (ri 2 - ri 3))
            * ((ci 0 - ci 1) * (ci 0 - ci 2) * (ci 0 - ci 3) * (ci 1 - ci 2) * (ci 1 - ci 3) * (ci 2 - ci 3)) := by
  rw [alternantModP, alternant_four_eq]
  push_cast
  have key6 : ∀ a : ℕ, 720 * (a.choose 6 : ZMod p)
      = (a : ZMod p) * ((a:ZMod p) - 1) * ((a:ZMod p) - 2) * ((a:ZMod p) - 3)
          * ((a:ZMod p) - 4) * ((a:ZMod p) - 5) := choose_six_zmod
  have hstep : 720 *
      (
        ((e ri ci 0 0 + e ri ci 1 1 + e ri ci 2 2 + e ri ci 3 3).choose 6 : ZMod p)
        - ((e ri ci 0 0 + e ri ci 1 1 + e ri ci 2 3 + e ri ci 3 2).choose 6 : ZMod p)
        - ((e ri ci 0 0 + e ri ci 1 2 + e ri ci 2 1 + e ri ci 3 3).choose 6 : ZMod p)
        + ((e ri ci 0 0 + e ri ci 1 2 + e ri ci 2 3 + e ri ci 3 1).choose 6 : ZMod p)
        + ((e ri ci 0 0 + e ri ci 1 3 + e ri ci 2 1 + e ri ci 3 2).choose 6 : ZMod p)
        - ((e ri ci 0 0 + e ri ci 1 3 + e ri ci 2 2 + e ri ci 3 1).choose 6 : ZMod p)
        - ((e ri ci 0 1 + e ri ci 1 0 + e ri ci 2 2 + e ri ci 3 3).choose 6 : ZMod p)
        + ((e ri ci 0 1 + e ri ci 1 0 + e ri ci 2 3 + e ri ci 3 2).choose 6 : ZMod p)
        + ((e ri ci 0 1 + e ri ci 1 2 + e ri ci 2 0 + e ri ci 3 3).choose 6 : ZMod p)
        - ((e ri ci 0 1 + e ri ci 1 2 + e ri ci 2 3 + e ri ci 3 0).choose 6 : ZMod p)
        - ((e ri ci 0 1 + e ri ci 1 3 + e ri ci 2 0 + e ri ci 3 2).choose 6 : ZMod p)
        + ((e ri ci 0 1 + e ri ci 1 3 + e ri ci 2 2 + e ri ci 3 0).choose 6 : ZMod p)
        + ((e ri ci 0 2 + e ri ci 1 0 + e ri ci 2 1 + e ri ci 3 3).choose 6 : ZMod p)
        - ((e ri ci 0 2 + e ri ci 1 0 + e ri ci 2 3 + e ri ci 3 1).choose 6 : ZMod p)
        - ((e ri ci 0 2 + e ri ci 1 1 + e ri ci 2 0 + e ri ci 3 3).choose 6 : ZMod p)
        + ((e ri ci 0 2 + e ri ci 1 1 + e ri ci 2 3 + e ri ci 3 0).choose 6 : ZMod p)
        + ((e ri ci 0 2 + e ri ci 1 3 + e ri ci 2 0 + e ri ci 3 1).choose 6 : ZMod p)
        - ((e ri ci 0 2 + e ri ci 1 3 + e ri ci 2 1 + e ri ci 3 0).choose 6 : ZMod p)
        - ((e ri ci 0 3 + e ri ci 1 0 + e ri ci 2 1 + e ri ci 3 2).choose 6 : ZMod p)
        + ((e ri ci 0 3 + e ri ci 1 0 + e ri ci 2 2 + e ri ci 3 1).choose 6 : ZMod p)
        + ((e ri ci 0 3 + e ri ci 1 1 + e ri ci 2 0 + e ri ci 3 2).choose 6 : ZMod p)
        - ((e ri ci 0 3 + e ri ci 1 1 + e ri ci 2 2 + e ri ci 3 0).choose 6 : ZMod p)
        - ((e ri ci 0 3 + e ri ci 1 2 + e ri ci 2 0 + e ri ci 3 1).choose 6 : ZMod p)
        + ((e ri ci 0 3 + e ri ci 1 2 + e ri ci 2 1 + e ri ci 3 0).choose 6 : ZMod p)
      )
      =
        ((((e ri ci 0 0 + e ri ci 1 1 + e ri ci 2 2 + e ri ci 3 3 : ℕ) : ZMod p)) * ((((e ri ci 0 0 + e ri ci 1 1 + e ri ci 2 2 + e ri ci 3 3 : ℕ) : ZMod p)) - 1) * ((((e ri ci 0 0 + e ri ci 1 1 + e ri ci 2 2 + e ri ci 3 3 : ℕ) : ZMod p)) - 2) * ((((e ri ci 0 0 + e ri ci 1 1 + e ri ci 2 2 + e ri ci 3 3 : ℕ) : ZMod p)) - 3) * ((((e ri ci 0 0 + e ri ci 1 1 + e ri ci 2 2 + e ri ci 3 3 : ℕ) : ZMod p)) - 4) * ((((e ri ci 0 0 + e ri ci 1 1 + e ri ci 2 2 + e ri ci 3 3 : ℕ) : ZMod p)) - 5))
        - ((((e ri ci 0 0 + e ri ci 1 1 + e ri ci 2 3 + e ri ci 3 2 : ℕ) : ZMod p)) * ((((e ri ci 0 0 + e ri ci 1 1 + e ri ci 2 3 + e ri ci 3 2 : ℕ) : ZMod p)) - 1) * ((((e ri ci 0 0 + e ri ci 1 1 + e ri ci 2 3 + e ri ci 3 2 : ℕ) : ZMod p)) - 2) * ((((e ri ci 0 0 + e ri ci 1 1 + e ri ci 2 3 + e ri ci 3 2 : ℕ) : ZMod p)) - 3) * ((((e ri ci 0 0 + e ri ci 1 1 + e ri ci 2 3 + e ri ci 3 2 : ℕ) : ZMod p)) - 4) * ((((e ri ci 0 0 + e ri ci 1 1 + e ri ci 2 3 + e ri ci 3 2 : ℕ) : ZMod p)) - 5))
        - ((((e ri ci 0 0 + e ri ci 1 2 + e ri ci 2 1 + e ri ci 3 3 : ℕ) : ZMod p)) * ((((e ri ci 0 0 + e ri ci 1 2 + e ri ci 2 1 + e ri ci 3 3 : ℕ) : ZMod p)) - 1) * ((((e ri ci 0 0 + e ri ci 1 2 + e ri ci 2 1 + e ri ci 3 3 : ℕ) : ZMod p)) - 2) * ((((e ri ci 0 0 + e ri ci 1 2 + e ri ci 2 1 + e ri ci 3 3 : ℕ) : ZMod p)) - 3) * ((((e ri ci 0 0 + e ri ci 1 2 + e ri ci 2 1 + e ri ci 3 3 : ℕ) : ZMod p)) - 4) * ((((e ri ci 0 0 + e ri ci 1 2 + e ri ci 2 1 + e ri ci 3 3 : ℕ) : ZMod p)) - 5))
        + ((((e ri ci 0 0 + e ri ci 1 2 + e ri ci 2 3 + e ri ci 3 1 : ℕ) : ZMod p)) * ((((e ri ci 0 0 + e ri ci 1 2 + e ri ci 2 3 + e ri ci 3 1 : ℕ) : ZMod p)) - 1) * ((((e ri ci 0 0 + e ri ci 1 2 + e ri ci 2 3 + e ri ci 3 1 : ℕ) : ZMod p)) - 2) * ((((e ri ci 0 0 + e ri ci 1 2 + e ri ci 2 3 + e ri ci 3 1 : ℕ) : ZMod p)) - 3) * ((((e ri ci 0 0 + e ri ci 1 2 + e ri ci 2 3 + e ri ci 3 1 : ℕ) : ZMod p)) - 4) * ((((e ri ci 0 0 + e ri ci 1 2 + e ri ci 2 3 + e ri ci 3 1 : ℕ) : ZMod p)) - 5))
        + ((((e ri ci 0 0 + e ri ci 1 3 + e ri ci 2 1 + e ri ci 3 2 : ℕ) : ZMod p)) * ((((e ri ci 0 0 + e ri ci 1 3 + e ri ci 2 1 + e ri ci 3 2 : ℕ) : ZMod p)) - 1) * ((((e ri ci 0 0 + e ri ci 1 3 + e ri ci 2 1 + e ri ci 3 2 : ℕ) : ZMod p)) - 2) * ((((e ri ci 0 0 + e ri ci 1 3 + e ri ci 2 1 + e ri ci 3 2 : ℕ) : ZMod p)) - 3) * ((((e ri ci 0 0 + e ri ci 1 3 + e ri ci 2 1 + e ri ci 3 2 : ℕ) : ZMod p)) - 4) * ((((e ri ci 0 0 + e ri ci 1 3 + e ri ci 2 1 + e ri ci 3 2 : ℕ) : ZMod p)) - 5))
        - ((((e ri ci 0 0 + e ri ci 1 3 + e ri ci 2 2 + e ri ci 3 1 : ℕ) : ZMod p)) * ((((e ri ci 0 0 + e ri ci 1 3 + e ri ci 2 2 + e ri ci 3 1 : ℕ) : ZMod p)) - 1) * ((((e ri ci 0 0 + e ri ci 1 3 + e ri ci 2 2 + e ri ci 3 1 : ℕ) : ZMod p)) - 2) * ((((e ri ci 0 0 + e ri ci 1 3 + e ri ci 2 2 + e ri ci 3 1 : ℕ) : ZMod p)) - 3) * ((((e ri ci 0 0 + e ri ci 1 3 + e ri ci 2 2 + e ri ci 3 1 : ℕ) : ZMod p)) - 4) * ((((e ri ci 0 0 + e ri ci 1 3 + e ri ci 2 2 + e ri ci 3 1 : ℕ) : ZMod p)) - 5))
        - ((((e ri ci 0 1 + e ri ci 1 0 + e ri ci 2 2 + e ri ci 3 3 : ℕ) : ZMod p)) * ((((e ri ci 0 1 + e ri ci 1 0 + e ri ci 2 2 + e ri ci 3 3 : ℕ) : ZMod p)) - 1) * ((((e ri ci 0 1 + e ri ci 1 0 + e ri ci 2 2 + e ri ci 3 3 : ℕ) : ZMod p)) - 2) * ((((e ri ci 0 1 + e ri ci 1 0 + e ri ci 2 2 + e ri ci 3 3 : ℕ) : ZMod p)) - 3) * ((((e ri ci 0 1 + e ri ci 1 0 + e ri ci 2 2 + e ri ci 3 3 : ℕ) : ZMod p)) - 4) * ((((e ri ci 0 1 + e ri ci 1 0 + e ri ci 2 2 + e ri ci 3 3 : ℕ) : ZMod p)) - 5))
        + ((((e ri ci 0 1 + e ri ci 1 0 + e ri ci 2 3 + e ri ci 3 2 : ℕ) : ZMod p)) * ((((e ri ci 0 1 + e ri ci 1 0 + e ri ci 2 3 + e ri ci 3 2 : ℕ) : ZMod p)) - 1) * ((((e ri ci 0 1 + e ri ci 1 0 + e ri ci 2 3 + e ri ci 3 2 : ℕ) : ZMod p)) - 2) * ((((e ri ci 0 1 + e ri ci 1 0 + e ri ci 2 3 + e ri ci 3 2 : ℕ) : ZMod p)) - 3) * ((((e ri ci 0 1 + e ri ci 1 0 + e ri ci 2 3 + e ri ci 3 2 : ℕ) : ZMod p)) - 4) * ((((e ri ci 0 1 + e ri ci 1 0 + e ri ci 2 3 + e ri ci 3 2 : ℕ) : ZMod p)) - 5))
        + ((((e ri ci 0 1 + e ri ci 1 2 + e ri ci 2 0 + e ri ci 3 3 : ℕ) : ZMod p)) * ((((e ri ci 0 1 + e ri ci 1 2 + e ri ci 2 0 + e ri ci 3 3 : ℕ) : ZMod p)) - 1) * ((((e ri ci 0 1 + e ri ci 1 2 + e ri ci 2 0 + e ri ci 3 3 : ℕ) : ZMod p)) - 2) * ((((e ri ci 0 1 + e ri ci 1 2 + e ri ci 2 0 + e ri ci 3 3 : ℕ) : ZMod p)) - 3) * ((((e ri ci 0 1 + e ri ci 1 2 + e ri ci 2 0 + e ri ci 3 3 : ℕ) : ZMod p)) - 4) * ((((e ri ci 0 1 + e ri ci 1 2 + e ri ci 2 0 + e ri ci 3 3 : ℕ) : ZMod p)) - 5))
        - ((((e ri ci 0 1 + e ri ci 1 2 + e ri ci 2 3 + e ri ci 3 0 : ℕ) : ZMod p)) * ((((e ri ci 0 1 + e ri ci 1 2 + e ri ci 2 3 + e ri ci 3 0 : ℕ) : ZMod p)) - 1) * ((((e ri ci 0 1 + e ri ci 1 2 + e ri ci 2 3 + e ri ci 3 0 : ℕ) : ZMod p)) - 2) * ((((e ri ci 0 1 + e ri ci 1 2 + e ri ci 2 3 + e ri ci 3 0 : ℕ) : ZMod p)) - 3) * ((((e ri ci 0 1 + e ri ci 1 2 + e ri ci 2 3 + e ri ci 3 0 : ℕ) : ZMod p)) - 4) * ((((e ri ci 0 1 + e ri ci 1 2 + e ri ci 2 3 + e ri ci 3 0 : ℕ) : ZMod p)) - 5))
        - ((((e ri ci 0 1 + e ri ci 1 3 + e ri ci 2 0 + e ri ci 3 2 : ℕ) : ZMod p)) * ((((e ri ci 0 1 + e ri ci 1 3 + e ri ci 2 0 + e ri ci 3 2 : ℕ) : ZMod p)) - 1) * ((((e ri ci 0 1 + e ri ci 1 3 + e ri ci 2 0 + e ri ci 3 2 : ℕ) : ZMod p)) - 2) * ((((e ri ci 0 1 + e ri ci 1 3 + e ri ci 2 0 + e ri ci 3 2 : ℕ) : ZMod p)) - 3) * ((((e ri ci 0 1 + e ri ci 1 3 + e ri ci 2 0 + e ri ci 3 2 : ℕ) : ZMod p)) - 4) * ((((e ri ci 0 1 + e ri ci 1 3 + e ri ci 2 0 + e ri ci 3 2 : ℕ) : ZMod p)) - 5))
        + ((((e ri ci 0 1 + e ri ci 1 3 + e ri ci 2 2 + e ri ci 3 0 : ℕ) : ZMod p)) * ((((e ri ci 0 1 + e ri ci 1 3 + e ri ci 2 2 + e ri ci 3 0 : ℕ) : ZMod p)) - 1) * ((((e ri ci 0 1 + e ri ci 1 3 + e ri ci 2 2 + e ri ci 3 0 : ℕ) : ZMod p)) - 2) * ((((e ri ci 0 1 + e ri ci 1 3 + e ri ci 2 2 + e ri ci 3 0 : ℕ) : ZMod p)) - 3) * ((((e ri ci 0 1 + e ri ci 1 3 + e ri ci 2 2 + e ri ci 3 0 : ℕ) : ZMod p)) - 4) * ((((e ri ci 0 1 + e ri ci 1 3 + e ri ci 2 2 + e ri ci 3 0 : ℕ) : ZMod p)) - 5))
        + ((((e ri ci 0 2 + e ri ci 1 0 + e ri ci 2 1 + e ri ci 3 3 : ℕ) : ZMod p)) * ((((e ri ci 0 2 + e ri ci 1 0 + e ri ci 2 1 + e ri ci 3 3 : ℕ) : ZMod p)) - 1) * ((((e ri ci 0 2 + e ri ci 1 0 + e ri ci 2 1 + e ri ci 3 3 : ℕ) : ZMod p)) - 2) * ((((e ri ci 0 2 + e ri ci 1 0 + e ri ci 2 1 + e ri ci 3 3 : ℕ) : ZMod p)) - 3) * ((((e ri ci 0 2 + e ri ci 1 0 + e ri ci 2 1 + e ri ci 3 3 : ℕ) : ZMod p)) - 4) * ((((e ri ci 0 2 + e ri ci 1 0 + e ri ci 2 1 + e ri ci 3 3 : ℕ) : ZMod p)) - 5))
        - ((((e ri ci 0 2 + e ri ci 1 0 + e ri ci 2 3 + e ri ci 3 1 : ℕ) : ZMod p)) * ((((e ri ci 0 2 + e ri ci 1 0 + e ri ci 2 3 + e ri ci 3 1 : ℕ) : ZMod p)) - 1) * ((((e ri ci 0 2 + e ri ci 1 0 + e ri ci 2 3 + e ri ci 3 1 : ℕ) : ZMod p)) - 2) * ((((e ri ci 0 2 + e ri ci 1 0 + e ri ci 2 3 + e ri ci 3 1 : ℕ) : ZMod p)) - 3) * ((((e ri ci 0 2 + e ri ci 1 0 + e ri ci 2 3 + e ri ci 3 1 : ℕ) : ZMod p)) - 4) * ((((e ri ci 0 2 + e ri ci 1 0 + e ri ci 2 3 + e ri ci 3 1 : ℕ) : ZMod p)) - 5))
        - ((((e ri ci 0 2 + e ri ci 1 1 + e ri ci 2 0 + e ri ci 3 3 : ℕ) : ZMod p)) * ((((e ri ci 0 2 + e ri ci 1 1 + e ri ci 2 0 + e ri ci 3 3 : ℕ) : ZMod p)) - 1) * ((((e ri ci 0 2 + e ri ci 1 1 + e ri ci 2 0 + e ri ci 3 3 : ℕ) : ZMod p)) - 2) * ((((e ri ci 0 2 + e ri ci 1 1 + e ri ci 2 0 + e ri ci 3 3 : ℕ) : ZMod p)) - 3) * ((((e ri ci 0 2 + e ri ci 1 1 + e ri ci 2 0 + e ri ci 3 3 : ℕ) : ZMod p)) - 4) * ((((e ri ci 0 2 + e ri ci 1 1 + e ri ci 2 0 + e ri ci 3 3 : ℕ) : ZMod p)) - 5))
        + ((((e ri ci 0 2 + e ri ci 1 1 + e ri ci 2 3 + e ri ci 3 0 : ℕ) : ZMod p)) * ((((e ri ci 0 2 + e ri ci 1 1 + e ri ci 2 3 + e ri ci 3 0 : ℕ) : ZMod p)) - 1) * ((((e ri ci 0 2 + e ri ci 1 1 + e ri ci 2 3 + e ri ci 3 0 : ℕ) : ZMod p)) - 2) * ((((e ri ci 0 2 + e ri ci 1 1 + e ri ci 2 3 + e ri ci 3 0 : ℕ) : ZMod p)) - 3) * ((((e ri ci 0 2 + e ri ci 1 1 + e ri ci 2 3 + e ri ci 3 0 : ℕ) : ZMod p)) - 4) * ((((e ri ci 0 2 + e ri ci 1 1 + e ri ci 2 3 + e ri ci 3 0 : ℕ) : ZMod p)) - 5))
        + ((((e ri ci 0 2 + e ri ci 1 3 + e ri ci 2 0 + e ri ci 3 1 : ℕ) : ZMod p)) * ((((e ri ci 0 2 + e ri ci 1 3 + e ri ci 2 0 + e ri ci 3 1 : ℕ) : ZMod p)) - 1) * ((((e ri ci 0 2 + e ri ci 1 3 + e ri ci 2 0 + e ri ci 3 1 : ℕ) : ZMod p)) - 2) * ((((e ri ci 0 2 + e ri ci 1 3 + e ri ci 2 0 + e ri ci 3 1 : ℕ) : ZMod p)) - 3) * ((((e ri ci 0 2 + e ri ci 1 3 + e ri ci 2 0 + e ri ci 3 1 : ℕ) : ZMod p)) - 4) * ((((e ri ci 0 2 + e ri ci 1 3 + e ri ci 2 0 + e ri ci 3 1 : ℕ) : ZMod p)) - 5))
        - ((((e ri ci 0 2 + e ri ci 1 3 + e ri ci 2 1 + e ri ci 3 0 : ℕ) : ZMod p)) * ((((e ri ci 0 2 + e ri ci 1 3 + e ri ci 2 1 + e ri ci 3 0 : ℕ) : ZMod p)) - 1) * ((((e ri ci 0 2 + e ri ci 1 3 + e ri ci 2 1 + e ri ci 3 0 : ℕ) : ZMod p)) - 2) * ((((e ri ci 0 2 + e ri ci 1 3 + e ri ci 2 1 + e ri ci 3 0 : ℕ) : ZMod p)) - 3) * ((((e ri ci 0 2 + e ri ci 1 3 + e ri ci 2 1 + e ri ci 3 0 : ℕ) : ZMod p)) - 4) * ((((e ri ci 0 2 + e ri ci 1 3 + e ri ci 2 1 + e ri ci 3 0 : ℕ) : ZMod p)) - 5))
        - ((((e ri ci 0 3 + e ri ci 1 0 + e ri ci 2 1 + e ri ci 3 2 : ℕ) : ZMod p)) * ((((e ri ci 0 3 + e ri ci 1 0 + e ri ci 2 1 + e ri ci 3 2 : ℕ) : ZMod p)) - 1) * ((((e ri ci 0 3 + e ri ci 1 0 + e ri ci 2 1 + e ri ci 3 2 : ℕ) : ZMod p)) - 2) * ((((e ri ci 0 3 + e ri ci 1 0 + e ri ci 2 1 + e ri ci 3 2 : ℕ) : ZMod p)) - 3) * ((((e ri ci 0 3 + e ri ci 1 0 + e ri ci 2 1 + e ri ci 3 2 : ℕ) : ZMod p)) - 4) * ((((e ri ci 0 3 + e ri ci 1 0 + e ri ci 2 1 + e ri ci 3 2 : ℕ) : ZMod p)) - 5))
        + ((((e ri ci 0 3 + e ri ci 1 0 + e ri ci 2 2 + e ri ci 3 1 : ℕ) : ZMod p)) * ((((e ri ci 0 3 + e ri ci 1 0 + e ri ci 2 2 + e ri ci 3 1 : ℕ) : ZMod p)) - 1) * ((((e ri ci 0 3 + e ri ci 1 0 + e ri ci 2 2 + e ri ci 3 1 : ℕ) : ZMod p)) - 2) * ((((e ri ci 0 3 + e ri ci 1 0 + e ri ci 2 2 + e ri ci 3 1 : ℕ) : ZMod p)) - 3) * ((((e ri ci 0 3 + e ri ci 1 0 + e ri ci 2 2 + e ri ci 3 1 : ℕ) : ZMod p)) - 4) * ((((e ri ci 0 3 + e ri ci 1 0 + e ri ci 2 2 + e ri ci 3 1 : ℕ) : ZMod p)) - 5))
        + ((((e ri ci 0 3 + e ri ci 1 1 + e ri ci 2 0 + e ri ci 3 2 : ℕ) : ZMod p)) * ((((e ri ci 0 3 + e ri ci 1 1 + e ri ci 2 0 + e ri ci 3 2 : ℕ) : ZMod p)) - 1) * ((((e ri ci 0 3 + e ri ci 1 1 + e ri ci 2 0 + e ri ci 3 2 : ℕ) : ZMod p)) - 2) * ((((e ri ci 0 3 + e ri ci 1 1 + e ri ci 2 0 + e ri ci 3 2 : ℕ) : ZMod p)) - 3) * ((((e ri ci 0 3 + e ri ci 1 1 + e ri ci 2 0 + e ri ci 3 2 : ℕ) : ZMod p)) - 4) * ((((e ri ci 0 3 + e ri ci 1 1 + e ri ci 2 0 + e ri ci 3 2 : ℕ) : ZMod p)) - 5))
        - ((((e ri ci 0 3 + e ri ci 1 1 + e ri ci 2 2 + e ri ci 3 0 : ℕ) : ZMod p)) * ((((e ri ci 0 3 + e ri ci 1 1 + e ri ci 2 2 + e ri ci 3 0 : ℕ) : ZMod p)) - 1) * ((((e ri ci 0 3 + e ri ci 1 1 + e ri ci 2 2 + e ri ci 3 0 : ℕ) : ZMod p)) - 2) * ((((e ri ci 0 3 + e ri ci 1 1 + e ri ci 2 2 + e ri ci 3 0 : ℕ) : ZMod p)) - 3) * ((((e ri ci 0 3 + e ri ci 1 1 + e ri ci 2 2 + e ri ci 3 0 : ℕ) : ZMod p)) - 4) * ((((e ri ci 0 3 + e ri ci 1 1 + e ri ci 2 2 + e ri ci 3 0 : ℕ) : ZMod p)) - 5))
        - ((((e ri ci 0 3 + e ri ci 1 2 + e ri ci 2 0 + e ri ci 3 1 : ℕ) : ZMod p)) * ((((e ri ci 0 3 + e ri ci 1 2 + e ri ci 2 0 + e ri ci 3 1 : ℕ) : ZMod p)) - 1) * ((((e ri ci 0 3 + e ri ci 1 2 + e ri ci 2 0 + e ri ci 3 1 : ℕ) : ZMod p)) - 2) * ((((e ri ci 0 3 + e ri ci 1 2 + e ri ci 2 0 + e ri ci 3 1 : ℕ) : ZMod p)) - 3) * ((((e ri ci 0 3 + e ri ci 1 2 + e ri ci 2 0 + e ri ci 3 1 : ℕ) : ZMod p)) - 4) * ((((e ri ci 0 3 + e ri ci 1 2 + e ri ci 2 0 + e ri ci 3 1 : ℕ) : ZMod p)) - 5))
        + ((((e ri ci 0 3 + e ri ci 1 2 + e ri ci 2 1 + e ri ci 3 0 : ℕ) : ZMod p)) * ((((e ri ci 0 3 + e ri ci 1 2 + e ri ci 2 1 + e ri ci 3 0 : ℕ) : ZMod p)) - 1) * ((((e ri ci 0 3 + e ri ci 1 2 + e ri ci 2 1 + e ri ci 3 0 : ℕ) : ZMod p)) - 2) * ((((e ri ci 0 3 + e ri ci 1 2 + e ri ci 2 1 + e ri ci 3 0 : ℕ) : ZMod p)) - 3) * ((((e ri ci 0 3 + e ri ci 1 2 + e ri ci 2 1 + e ri ci 3 0 : ℕ) : ZMod p)) - 4) * ((((e ri ci 0 3 + e ri ci 1 2 + e ri ci 2 1 + e ri ci 3 0 : ℕ) : ZMod p)) - 5)) := by
    linear_combination
      key6 (e ri ci 0 0 + e ri ci 1 1 + e ri ci 2 2 + e ri ci 3 3)
      - key6 (e ri ci 0 0 + e ri ci 1 1 + e ri ci 2 3 + e ri ci 3 2)
      - key6 (e ri ci 0 0 + e ri ci 1 2 + e ri ci 2 1 + e ri ci 3 3)
      + key6 (e ri ci 0 0 + e ri ci 1 2 + e ri ci 2 3 + e ri ci 3 1)
      + key6 (e ri ci 0 0 + e ri ci 1 3 + e ri ci 2 1 + e ri ci 3 2)
      - key6 (e ri ci 0 0 + e ri ci 1 3 + e ri ci 2 2 + e ri ci 3 1)
      - key6 (e ri ci 0 1 + e ri ci 1 0 + e ri ci 2 2 + e ri ci 3 3)
      + key6 (e ri ci 0 1 + e ri ci 1 0 + e ri ci 2 3 + e ri ci 3 2)
      + key6 (e ri ci 0 1 + e ri ci 1 2 + e ri ci 2 0 + e ri ci 3 3)
      - key6 (e ri ci 0 1 + e ri ci 1 2 + e ri ci 2 3 + e ri ci 3 0)
      - key6 (e ri ci 0 1 + e ri ci 1 3 + e ri ci 2 0 + e ri ci 3 2)
      + key6 (e ri ci 0 1 + e ri ci 1 3 + e ri ci 2 2 + e ri ci 3 0)
      + key6 (e ri ci 0 2 + e ri ci 1 0 + e ri ci 2 1 + e ri ci 3 3)
      - key6 (e ri ci 0 2 + e ri ci 1 0 + e ri ci 2 3 + e ri ci 3 1)
      - key6 (e ri ci 0 2 + e ri ci 1 1 + e ri ci 2 0 + e ri ci 3 3)
      + key6 (e ri ci 0 2 + e ri ci 1 1 + e ri ci 2 3 + e ri ci 3 0)
      + key6 (e ri ci 0 2 + e ri ci 1 3 + e ri ci 2 0 + e ri ci 3 1)
      - key6 (e ri ci 0 2 + e ri ci 1 3 + e ri ci 2 1 + e ri ci 3 0)
      - key6 (e ri ci 0 3 + e ri ci 1 0 + e ri ci 2 1 + e ri ci 3 2)
      + key6 (e ri ci 0 3 + e ri ci 1 0 + e ri ci 2 2 + e ri ci 3 1)
      + key6 (e ri ci 0 3 + e ri ci 1 1 + e ri ci 2 0 + e ri ci 3 2)
      - key6 (e ri ci 0 3 + e ri ci 1 1 + e ri ci 2 2 + e ri ci 3 0)
      - key6 (e ri ci 0 3 + e ri ci 1 2 + e ri ci 2 0 + e ri ci 3 1)
      + key6 (e ri ci 0 3 + e ri ci 1 2 + e ri ci 2 1 + e ri ci 3 0)
  rw [hstep]
  push_cast [e_cast]
  ring

/-! ## Vandermonde nonvanishing from injectivity. -/

/-- For injective `ri : Fin 4 → ZMod p`, the `4`-point Vandermonde difference product is nonzero. -/
theorem vandermonde_four_ne_zero (ri : Fin 4 → ZMod p) (hri : Function.Injective ri) :
    (ri 0 - ri 1) * (ri 0 - ri 2) * (ri 0 - ri 3) * (ri 1 - ri 2) * (ri 1 - ri 3) * (ri 2 - ri 3) ≠ 0 := by
  have h01 : ri 0 ≠ ri 1 := fun h => by simpa using hri h
  have h02 : ri 0 ≠ ri 2 := fun h => by simpa using hri h
  have h03 : ri 0 ≠ ri 3 := fun h => by simpa using hri h
  have h12 : ri 1 ≠ ri 2 := fun h => by simpa using hri h
  have h13 : ri 1 ≠ ri 3 := fun h => by simpa using hri h
  have h23 : ri 2 ≠ ri 3 := fun h => by simpa using hri h
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
    (sub_ne_zero.mpr h01) (sub_ne_zero.mpr h02)) (sub_ne_zero.mpr h03))
    (sub_ne_zero.mpr h12)) (sub_ne_zero.mpr h13)) (sub_ne_zero.mpr h23)

/-! ## The headline: the `n = 4` instance of the crux (`p ≥ 7`). -/

/-- Local instance so `GeneralizedVandermondeNonzeroModP 5 4` (the named `p = 5` residual below)
type-checks; `5` is prime. -/
instance primeFact_ChebotarevAlternantFour_1 : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- **The lone unresolved prime for `n = 4`: `p = 5` (NAMED, not proven).** This is exactly the
statement `GeneralizedVandermondeNonzeroModP 5 4`, recorded as its own name because the order-`6`
descending-factorial mechanism degenerates at `p = 5` (`720, 60 ≡ 0 (mod 5)`) and a finite `decide`
over the `5⁸` injective pairs is infeasible (see the file docstring). The probe confirms the alternant
*is* nonzero mod `5` (ratio `≡ 3`, i.e. `2·alternant ≡ V_r V_c`); only a Lucas-type or symmetry-reduced
argument would close it, and that is left open. It is implied by `AlternantFactorsConstant 5 4` with the
witness `c = 1/12 ≡ 3 (mod 5) ≠ 0` (see `crux_of_factorConstant`), so Route B subsumes it. -/
def GeneralizedVandermondeNonzeroAtFive : Prop :=
  GeneralizedVandermondeNonzeroModP 5 4

/-- **The `n = 4` instance of the generalized-Vandermonde alternant crux (PROVEN, `p ≥ 7`).**

For every prime `p ≥ 7` and every pair of *injective* selections `ri ci : Fin 4 → ZMod p`, the
alternant `alternantModP ri ci` is nonzero mod `p`. Proof: the closed form `720·alternantModP =
60·V_r·V_c` (`sevenTwenty_alternantModP_eq`) has `720, 60` invertible (`p ≥ 7`) and `V_r, V_c ≠ 0`
(injectivity), so `alternantModP ≠ 0`. (`p = 2, 3` are vacuous, `p = 5` is named-open — see the
file docstring.) -/
theorem generalizedVandermondeNonzeroModP_four (hp7 : 7 ≤ p) :
    GeneralizedVandermondeNonzeroModP p 4 := by
  intro ri ci hri hci
  have hpp := (Fact.out (p := p.Prime))
  -- `(60 : ZMod p) ≠ 0` : `60 = 2²·3·5`, every prime factor is `< 7`.
  have h60 : (60 : ZMod p) ≠ 0 := by
    have : ((60 : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hdvd
      rw [show (60 : ℕ) = 2 ^ 2 * 3 * 5 from by norm_num] at hdvd
      rcases (Nat.Prime.dvd_mul hpp).mp hdvd with h1 | h5
      · rcases (Nat.Prime.dvd_mul hpp).mp h1 with h2 | h3
        · have := hpp.dvd_of_dvd_pow h2
          have := (Nat.prime_dvd_prime_iff_eq hpp (by decide)).mp this; omega
        · have := (Nat.prime_dvd_prime_iff_eq hpp (by decide)).mp h3; omega
      · have := (Nat.prime_dvd_prime_iff_eq hpp (by decide)).mp h5; omega
    simpa using this
  -- assume the alternant vanishes; then `0 = 720·alternantModP = 60·V_r·V_c`, but the RHS ≠ 0.
  intro hzero
  have hsix := sevenTwenty_alternantModP_eq ri ci
  rw [hzero, mul_zero] at hsix
  have hrhs : (60 : ZMod p)
      * ((ri 0 - ri 1) * (ri 0 - ri 2) * (ri 0 - ri 3) * (ri 1 - ri 2) * (ri 1 - ri 3) * (ri 2 - ri 3))
      * ((ci 0 - ci 1) * (ci 0 - ci 2) * (ci 0 - ci 3) * (ci 1 - ci 2) * (ci 1 - ci 3) * (ci 2 - ci 3)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero h60 (vandermonde_four_ne_zero ri hri))
      (vandermonde_four_ne_zero ci hci)
  exact hrhs hsix.symm

/-! ## Route B (NAMED, not proven): the all-`n` constant-factorization conjecture + easy reduction.

The probe (`probe_407_chebotarev_alternant_n4.py`, and the `n=3,5` sweep) suggests that for *every*
`n` the alternant factors as a *constant* times the product of the two `n`-point Vandermonde
difference products:

  `alternantModP ri ci = c_n · V_r(ri) · V_c(ci)`     (`c_3 = −1/2`, `c_4 = 1/12`),

with `V_r(ri) = det (vandermonde ri) = ∏_{i<j}(ri j − ri i)`. The structural reason (NOT formalized
here) is antisymmetry: swapping two rows of the minor matrix negates `det`, hence negates every
`(X−1)`-Taylor coefficient, hence the alternant; so the alternant (as a polynomial in the `ri`)
vanishes whenever two `ri` coincide, so is divisible by `V_r`, symmetrically by `V_c`, and a
total-degree count (`deg = 2·binom(n,2) = deg V_r + deg V_c`) forces the quotient to be a constant.
Mathlib's multivariate antisymmetric ⟹ Vandermonde-divisibility support is thin, so we do **NOT**
prove the factorization; it is stated as the named conjecture below, with the genuine (easy-direction)
reduction `crux_of_factorConstant`. This is a NON-vacuous reduction: it really does reduce the deep
`n`-crux to the single arithmetic fact `c_n ≠ 0 (mod p)` — *given* the (unproven) factorization. -/

/-- **NAMED conjecture (Route B).** `AlternantFactorsConstant p n` asserts the alternant factors as a
fixed scalar `c` times the product of the two `n`-point Vandermonde determinants, uniformly over all
injective row/column selections. Probe-verified for `n = 3` (`c = −1/2`) and `n = 4` (`c = 1/12`);
NOT proven for general `n` (the antisymmetry⟹divisibility⟹degree-count argument is not formalized). -/
def AlternantFactorsConstant (p : ℕ) [Fact p.Prime] (n : ℕ) : Prop :=
  ∃ c : ZMod p, ∀ (ri ci : Fin n → ZMod p),
    Function.Injective ri → Function.Injective ci →
      alternantModP ri ci = c * Matrix.det (Matrix.vandermonde ri) * Matrix.det (Matrix.vandermonde ci)

/-- **The easy-direction reduction (PROVEN).** If the alternant factors as a *nonzero* constant times
the two Vandermonde determinants (`AlternantFactorsConstant` with witness `c ≠ 0`), then the deep crux
`GeneralizedVandermondeNonzeroModP p n` holds: for injective `ri ci`, both Vandermonde determinants are
nonzero (`det_vandermonde_eq_zero_iff`) and `c ≠ 0`, so the product `alternantModP = c·V_r·V_c ≠ 0`.
This is the genuine, non-vacuous reduction of the crux to the single arithmetic fact `c ≠ 0`; the
factorization hypothesis itself (the `∃ c`) is the named-open Route B. -/
theorem crux_of_factorConstant {n : ℕ} {c : ZMod p}
    (hfac : ∀ (ri ci : Fin n → ZMod p), Function.Injective ri → Function.Injective ci →
      alternantModP ri ci = c * Matrix.det (Matrix.vandermonde ri) * Matrix.det (Matrix.vandermonde ci))
    (hc : c ≠ 0) :
    GeneralizedVandermondeNonzeroModP p n := by
  intro ri ci hri hci
  rw [hfac ri ci hri hci]
  have hVr : Matrix.det (Matrix.vandermonde ri) ≠ 0 := by
    rw [Ne, Matrix.det_vandermonde_eq_zero_iff]
    rintro ⟨i, j, hij, hne⟩
    exact hne (hri hij)
  have hVc : Matrix.det (Matrix.vandermonde ci) ≠ 0 := by
    rw [Ne, Matrix.det_vandermonde_eq_zero_iff]
    rintro ⟨i, j, hij, hne⟩
    exact hne (hci hij)
  exact mul_ne_zero (mul_ne_zero hc hVr) hVc

end ProximityGap.Frontier.ChebotarevAlternantFour

/-! ## Axiom audit (expected: `propext, Classical.choice, Quot.sound` only — no `sorryAx`). -/
#print axioms ProximityGap.Frontier.ChebotarevAlternantFour.det_fin_four
#print axioms ProximityGap.Frontier.ChebotarevAlternantFour.choose_six_zmod
#print axioms ProximityGap.Frontier.ChebotarevAlternantFour.e_cast
#print axioms ProximityGap.Frontier.ChebotarevAlternantFour.alternant_four_eq
#print axioms ProximityGap.Frontier.ChebotarevAlternantFour.sevenTwenty_alternantModP_eq
#print axioms ProximityGap.Frontier.ChebotarevAlternantFour.vandermonde_four_ne_zero
#print axioms ProximityGap.Frontier.ChebotarevAlternantFour.generalizedVandermondeNonzeroModP_four
#print axioms ProximityGap.Frontier.ChebotarevAlternantFour.crux_of_factorConstant
