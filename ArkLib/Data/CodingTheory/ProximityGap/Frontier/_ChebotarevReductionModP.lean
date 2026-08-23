/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._TaoFromChebotarev
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.Algebra.CharP.Lemmas

/-!
# Reducing general-exponent Chebotarev to a Vandermonde-mod-`p` crux (#407)

`_TaoFromChebotarev.lean` reduced Tao's additive uncertainty principle to **Chebotarev's
minor-nonvanishing theorem** `ChebotarevMinorNonvanishing p` (every minor of the prime DFT matrix
is nonzero), and discharged the `n = 1`, the *full* `n = 2`, and the *equal-spacing exponent*
general-`n` cases. The deep open content is the **general-exponent** general-`n` case: for arbitrary
distinct exponents the Mathlib Vandermonde formula does not apply, and over a generic field the
determinant *can* vanish — it is nonzero precisely because `p` is prime.

This file performs the **standard Tao reduction-mod-`(1−ζ)`** for that general-exponent case,
isolating its genuine combinatorial heart as a single named crux. Let `ζ = stdAddChar 1 ∈ ℂ`, a
primitive `p`-th root of unity, and for injective row/column selections `ri ci : Fin n → ZMod p`
write the minor entry as `stdAddChar (-(ci j · ri i)) = ζ ^ e i j` with
`e i j := (-(ci j · ri i)).val`.

Define the **integer minor polynomial** `detPoly := det (X ^ e i j) ∈ ℤ[X]`, so the minor
determinant is `D = aeval ζ detPoly` (eval-of-det bridge). Tao's argument: if `D = 0`, then since the
minimal polynomial of `ζ` over `ℤ` is `cyclotomic p ℤ` (degree `p − 1`, irreducible),
`cyclotomic p ℤ ∣ detPoly`. Reduce mod `p`: `cyclotomic p (ZMod p) = (X − 1)^{p−1}` (Frobenius
collapse), so `(X − 1)^{p−1}` divides the mod-`p` reduction `detPolyModP`, i.e.
`rootMultiplicity 1 detPolyModP ≥ p − 1`. The contradiction is that the multiplicity of the root `1`
is `< p − 1`, because the lowest-order Taylor coefficient of `detPoly(1 + Y)` is a generalized
**Vandermonde determinant** that is **nonzero mod `p`** for distinct `a_i`, distinct `b_j` — the deep
combinatorial core of Chebotarev's theorem (genuinely *false* for composite `p`).

## What is PROVEN here (axiom-clean)

* **`cyclotomic_p_mod_p`** : `cyclotomic p (ZMod p) = (X − 1)^{p−1}`. Pure Mathlib: from
  `cyclotomic p R · (X − 1) = X^p − 1` and the Frobenius identity `(X − 1)^p = X^p − 1` over
  characteristic `p`, cancel the nonzero factor `(X − 1)` in the domain `(ZMod p)[X]`.

* **`detPoly`, `stdAddChar_eq_zeta_pow`, `detPoly_aeval_eq_minor`** : the integer minor polynomial and
  the eval-of-det bridge `aeval ζ detPoly = (the minor determinant)`, via `AlgHom.map_det`.

* **`isPrimitiveRoot_stdAddChar_one`** : `ζ = stdAddChar 1` is a primitive `p`-th root of unity.

* **`cyclotomic_dvd_of_aeval_eq_zero`** : `aeval ζ g = 0 ⟹ cyclotomic p ℤ ∣ g`
  (minimal polynomial of `ζ` is `cyclotomic p ℤ`).

* **`chebotarev_of_multiplicityBound`** : the REDUCTION. IF the named crux `MinorTaylorMultiplicityLt p`
  holds (the mod-`p` reduction of every valid `detPoly` is NOT divisible by `(X − 1)^{p−1}`, i.e.
  the root `1` has multiplicity `< p − 1`), THEN `ChebotarevMinorNonvanishing p`. PROVEN by the
  cyclotomic-divisibility argument above.

* **`tao_of_multiplicityBound`** : the end-to-end composite `MinorTaylorMultiplicityLt p ⟹
  TaoUncertainty p` (chaining with `tao_of_chebotarev`), pushing the prime-capacity dichotomy's sole
  open input down to this single concrete Vandermonde-mod-`p` statement.

## What stays the NAMED OPEN crux

* **`MinorTaylorMultiplicityLt p`** : `∀` valid injective `ri ci`, `¬ (X − 1)^{p−1} ∣ detPolyModP`
  (equivalently `rootMultiplicity 1 detPolyModP < p − 1`, see `minorTaylorMultiplicityLt_iff`).
  The `n = 0` and `n = 1` instances ARE discharged as sanity checks (`minorTaylorMultiplicityLt_zero`,
  `minorTaylorMultiplicityLt_one`); the `n = 2` instance is proven in the sibling file.

> ## ⚠️ CORRECTION (the `∀ n` crux as stated here is REFUTED — read before using the reduction)
>
> A later exact census (sibling `_ChebotarevVandermondeCrux.lean`,
> `scripts/probes/probe_407_chebotarev_multiplicity.py`) established that the worst-case
> `rootMultiplicity 1 (detPolyModP ri ci)` is **exactly `binom(n,2) = n(n−1)/2`** (the alternant /
> `(1−ζ)`-adic valuation), and `detPolyModP ≠ 0` always. Hence the universally-quantified
> `MinorTaylorMultiplicityLt p` (over **all** `n`) is **FALSE for every prime `p`**: it fails at any
> `n ≤ p` with `binom(n,2) ≥ p − 1` (e.g. `p = 5, n = 4`), where `(X−1)^{p−1} ∣ detPolyModP` genuinely
> holds. Consequently `chebotarev_of_multiplicityBound` / `tao_of_multiplicityBound` below are valid
> Lean implications but have an **unsatisfiable hypothesis — they are VACUOUS as reductions** and must
> NOT be read as "general Chebotarev reduces to one crux". The `(X−1)^{p−1}`-divisibility mechanism
> only proves Chebotarev in the **small regime `binom(n,2) < p − 1`** (`n ≲ √(2p)`); large `n` needs
> the *finiteness* of the alternant valuation, not `(X−1)^{p−1}` divisibility. The corrected n-wise,
> small-regime framing — `GeneralizedVandermondeMultiplicityLe p n` (the genuine residual:
> `detPolyModP ≠ 0 ∧ rootMultiplicity 1 ≤ binom(n,2)`), `smallRegime_crux_of_multiplicityBound`, and
> the PROVEN `n = 2` instance `minorTaylorMultiplicityLt_two` — lives in `_ChebotarevVandermondeCrux.lean`.

So this file's PROVEN content is the cyclotomic-divisibility framework (`cyclotomic_p_mod_p`, the
eval-of-det bridge, `cyclotomic_dvd_of_aeval_eq_zero`); the `chebotarev_of_multiplicityBound` reduction
is correct-but-vacuous as stated, and the genuine (small-regime, n-wise) reduction is in the sibling.

## Honesty contract (per #407)

`MinorTaylorMultiplicityLt` is a `def … : Prop` (a named classical hypothesis), carrying no axioms;
we never `sorry` it and never claim the general case proven. What is PROVEN is the cyclotomic-mod-`p`
fact, the eval-of-det bridge, and the reduction `chebotarev_of_multiplicityBound`. Never claim general
Chebotarev proven; the crux is the genuine deep core.

Reference: T. Tao, *An uncertainty principle for cyclic groups of prime order*, Math. Res. Lett. 12
(2005); Tao's blog post of the same title (the reduction-mod-`(1−ζ)` proof of Chebotarev's theorem).

Axiom-clean (`propext, Classical.choice, Quot.sound`; no `sorryAx`). Issue #407.
-/

open Finset ZMod Matrix Polynomial Complex
open ProximityGap.Frontier.ZModDonohoStark
open ProximityGap.Frontier.PrimeCapacityUncertainty
open ProximityGap.Frontier.TaoFromChebotarev

namespace ProximityGap.Frontier.ChebotarevReductionModP

variable {p : ℕ} [Fact p.Prime]

/-! ## Layer 1: `cyclotomic p (ZMod p) = (X − 1)^{p−1}` (PROVEN). -/

/-- **The mod-`p` collapse of the `p`-th cyclotomic polynomial (PROVEN).** Over `ZMod p` the
`p`-th cyclotomic polynomial collapses to `(X − 1)^{p−1}`. This is the Frobenius fact at the heart of
the reduction-mod-`(1−ζ)` argument: `Φ_p ≡ (X−1)^{p−1} (mod p)`.

Proof: `Φ_p · (X − 1) = X^p − 1` (`cyclotomic_prime_mul_X_sub_one`), and over characteristic `p` the
freshman's dream gives `(X − 1)^p = X^p − 1^p = X^p − 1` (`sub_pow_char`). Hence
`Φ_p · (X − 1) = (X − 1)^p = (X − 1)^{p−1} · (X − 1)`; cancel the nonzero factor `(X − 1)` in the
domain `(ZMod p)[X]`. -/
theorem cyclotomic_p_mod_p :
    cyclotomic p (ZMod p) = (X - 1) ^ (p - 1) := by
  have hp1 : 1 ≤ p := (Fact.out (p := p.Prime)).one_lt.le
  -- `Φ_p · (X − 1) = X^p − 1`.
  have hmul : cyclotomic p (ZMod p) * (X - 1) = X ^ p - 1 := cyclotomic_prime_mul_X_sub_one _ p
  -- Frobenius: `(X − 1)^p = X^p − 1` over characteristic `p`.
  have hfrob : (X - 1 : (ZMod p)[X]) ^ p = X ^ p - 1 := by
    rw [sub_pow_char]; simp
  -- `(X − 1)` is a nonzero element of the domain `(ZMod p)[X]`.
  have hX1ne : (X - 1 : (ZMod p)[X]) ≠ 0 := by simpa using X_sub_C_ne_zero (1 : ZMod p)
  -- `(X − 1)^{p−1} · (X − 1) = (X − 1)^p`.
  have hsplit : (X - 1 : (ZMod p)[X]) ^ (p - 1) * (X - 1) = (X - 1) ^ p := by
    rw [← pow_succ, Nat.sub_add_cancel hp1]
  -- so `Φ_p · (X − 1) = (X − 1)^{p−1} · (X − 1)`; cancel `(X − 1)`.
  have hkey : cyclotomic p (ZMod p) * (X - 1) = (X - 1) ^ (p - 1) * (X - 1) := by
    rw [hmul, ← hfrob, hsplit]
  exact mul_right_cancel₀ hX1ne hkey

/-! ## Layer 2: the integer minor polynomial and the eval-of-det bridge (PROVEN). -/

/-- `ζ = stdAddChar 1 ∈ ℂ` is a **primitive `p`-th root of unity** (PROVEN). The standard additive
character sends `1 ∈ ZMod p` to `exp(2πi/p)`, which `isPrimitiveRoot_exp` identifies as primitive. -/
theorem isPrimitiveRoot_stdAddChar_one :
    IsPrimitiveRoot (stdAddChar (1 : ZMod p) : ℂ) p := by
  have hp0 : p ≠ 0 := (Fact.out (p := p.Prime)).pos.ne'
  have h1 : (stdAddChar (1 : ZMod p) : ℂ) = Complex.exp (2 * ↑Real.pi * I / p) := by
    have he : (1 : ZMod p) = ((1 : ℤ) : ZMod p) := by simp
    rw [he, stdAddChar_coe]; push_cast; ring_nf
  rw [h1]
  exact isPrimitiveRoot_exp p hp0

/-- The character value `stdAddChar a` is the power `ζ ^ a.val` of `ζ = stdAddChar 1` (PROVEN):
`a = a.val • 1` in `ZMod p`, and `stdAddChar` is an additive character (`map_nsmul_eq_pow`). -/
theorem stdAddChar_eq_zeta_pow (a : ZMod p) :
    (stdAddChar a : ℂ) = (stdAddChar (1 : ZMod p) : ℂ) ^ a.val := by
  have ha : a = (a.val : ℕ) • (1 : ZMod p) := by
    rw [nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
  conv_lhs => rw [ha]
  rw [AddChar.map_nsmul_eq_pow]

/-- The exponent of the `(i, j)` entry of the prime-DFT minor: `e i j = (-(ci j · ri i)).val`. The
minor entry is `stdAddChar (-(ci j · ri i)) = ζ ^ (e i j)`. -/
def minorExp {n : ℕ} (ri ci : Fin n → ZMod p) (i j : Fin n) : ℕ :=
  (-(ci j * ri i)).val

/-- **The integer minor polynomial (definition).** `detPoly := det (X ^ e i j) ∈ ℤ[X]`, where
`e i j = minorExp ri ci i j`. Evaluating at `ζ = stdAddChar 1` recovers the prime-DFT minor
determinant; reducing mod `p` lands the Frobenius / multiplicity argument. -/
noncomputable def detPoly {n : ℕ} (ri ci : Fin n → ZMod p) : ℤ[X] :=
  (Matrix.of fun (i j : Fin n) => (X : ℤ[X]) ^ minorExp ri ci i j).det

/-- The mod-`p` reduction `detPolyModP := map (ℤ → ZMod p) detPoly ∈ (ZMod p)[X]`. -/
noncomputable def detPolyModP {n : ℕ} (ri ci : Fin n → ZMod p) : (ZMod p)[X] :=
  map (Int.castRingHom (ZMod p)) (detPoly ri ci)

/-- **Eval-of-det bridge (PROVEN).** Evaluating the integer minor polynomial at `ζ = stdAddChar 1`
recovers the prime-DFT minor determinant `D = det (stdAddChar (-(ci j · ri i)))`. Proof: `aeval ζ`
is an algebra homomorphism, so it commutes with `det` (`AlgHom.map_det`); entrywise
`aeval ζ (X^{e i j}) = ζ^{e i j} = stdAddChar (-(ci j · ri i))` by `stdAddChar_eq_zeta_pow`. -/
theorem detPoly_aeval_eq_minor {n : ℕ} (ri ci : Fin n → ZMod p) :
    (aeval (stdAddChar (1 : ZMod p) : ℂ)) (detPoly ri ci)
      = (Matrix.of fun (i j : Fin n) => (stdAddChar (-(ci j * ri i)) : ℂ)).det := by
  rw [detPoly, AlgHom.map_det]
  congr 1
  ext i j
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, aeval_X_pow]
  rw [minorExp, ← stdAddChar_eq_zeta_pow]

/-! ## Layer 3: the cyclotomic-divisibility reduction (PROVEN). -/

/-- **`ζ`'s minimal-polynomial divisibility (PROVEN).** If an integer polynomial `g` vanishes at
`ζ = stdAddChar 1` then it is divisible by `cyclotomic p ℤ`, the minimal polynomial of `ζ` over `ℤ`.
Proof: `ζ` is integral over `ℤ` and `cyclotomic p ℤ = minpoly ℤ ζ` (`cyclotomic_eq_minpoly`); then
`minpoly.isIntegrallyClosed_dvd` divides any polynomial with `ζ` as a root. -/
theorem cyclotomic_dvd_of_aeval_eq_zero {g : ℤ[X]}
    (hzero : (aeval (stdAddChar (1 : ZMod p) : ℂ)) g = 0) :
    cyclotomic p ℤ ∣ g := by
  have hpos : 0 < p := (Fact.out (p := p.Prime)).pos
  have hz := isPrimitiveRoot_stdAddChar_one (p := p)
  have hint : IsIntegral ℤ (stdAddChar (1 : ZMod p) : ℂ) := hz.isIntegral hpos
  rw [cyclotomic_eq_minpoly hz hpos]
  exact minpoly.isIntegrallyClosed_dvd hint hzero

/-- **The named OPEN crux: the generalized Vandermonde determinant is nonzero mod `p`.**

For every `n` and every pair of *injective* selections `ri ci : Fin n → ZMod p`, the mod-`p`
reduction `detPolyModP ri ci` of the integer minor polynomial is **NOT** divisible by
`(X − 1)^{p−1}`; equivalently the root `1` of `detPolyModP` has multiplicity `< p − 1`
(see `minorTaylorMultiplicityLt_iff`), equivalently the lowest-order Taylor coefficient of
`detPoly(1 + Y)` — a generalized Vandermonde determinant in the distinct `ri`, `ci` — is nonzero
mod `p`.

This is the deep combinatorial heart of **Chebotarev's theorem** (the only place primality of `p` is
genuinely used — it is *false* for composite `p`). Per the #407 honesty contract it is a named `Prop`
(carries no axioms); we never prove the general case nor `sorry` it. The `n = 0` and `n = 1` cases
ARE discharged below (`minorTaylorMultiplicityLt_zero`, `minorTaylorMultiplicityLt_one`).

⚠️ REFUTED AS STATED (`∀ n`): the worst-case `rootMultiplicity 1 detPolyModP = binom(n,2)` exactly, so
this `∀ n` `Prop` is FALSE for every prime (fails at `binom(n,2) ≥ p−1`, e.g. `p=5,n=4`). The
reductions below are therefore valid-but-VACUOUS; the corrected small-regime (`binom(n,2) < p−1`),
n-wise framing + the proven `n=2` case are in `_ChebotarevVandermondeCrux.lean`. See the module
docstring's ⚠️ CORRECTION block. -/
def MinorTaylorMultiplicityLt (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (n : ℕ) (ri ci : Fin n → ZMod p), Function.Injective ri → Function.Injective ci →
    ¬ ((X - 1) ^ (p - 1) ∣ detPolyModP ri ci)

/-- **The crux, in `rootMultiplicity` form (PROVEN equivalence).** For nonzero `detPolyModP`,
`¬ (X − 1)^{p−1} ∣ detPolyModP ⟺ rootMultiplicity 1 detPolyModP < p − 1`. The divisibility form is
used in the reduction; this exposes the (more recognizable) Taylor-multiplicity reading. Note the
crux's divisibility form *also* forces `detPolyModP ≠ 0` (since `(X−1)^{p−1} ∣ 0`), so it is the
faithful "lowest Taylor coefficient nonzero" statement. -/
theorem minorTaylorMultiplicityLt_iff {n : ℕ} (ri ci : Fin n → ZMod p)
    (hne : detPolyModP ri ci ≠ 0) :
    ¬ ((X - 1) ^ (p - 1) ∣ detPolyModP ri ci)
      ↔ rootMultiplicity 1 (detPolyModP ri ci) < p - 1 := by
  -- `(X − 1) = (X − C 1)`, then `le_rootMultiplicity_iff` + `not_le`.
  have h1 : (X - (1 : (ZMod p)[X])) = (X - C (1 : ZMod p)) := by rw [map_one]
  rw [h1, ← le_rootMultiplicity_iff hne, not_le]

/-- **General-exponent Chebotarev, REDUCED to the Vandermonde-mod-`p` crux (PROVEN reduction).**

`MinorTaylorMultiplicityLt p ⟹ ChebotarevMinorNonvanishing p`: granting that every mod-`p` minor
polynomial avoids the `(X − 1)^{p−1}` divisibility (its root `1` has multiplicity `< p − 1`), every
minor of the prime DFT matrix is nonzero.

Proof (Tao's reduction-mod-`(1−ζ)`): for injective `ri ci`, suppose the minor determinant `D = 0`.
By the eval-of-det bridge `D = aeval ζ (detPoly ri ci)`, so `aeval ζ (detPoly ri ci) = 0`. Then
`cyclotomic p ℤ ∣ detPoly ri ci` (`cyclotomic_dvd_of_aeval_eq_zero`), and mapping mod `p` together
with `cyclotomic p (ZMod p) = (X − 1)^{p−1}` (`cyclotomic_p_mod_p`) gives
`(X − 1)^{p−1} ∣ detPolyModP ri ci` — contradicting the crux. PROVEN, consuming only the named
`MinorTaylorMultiplicityLt`. -/
theorem chebotarev_of_multiplicityBound (hCrux : MinorTaylorMultiplicityLt p) :
    ChebotarevMinorNonvanishing p := by
  intro n ri ci hri hci
  -- Suppose the minor determinant is zero; derive a contradiction.
  intro hD
  -- the minor determinant is `aeval ζ (detPoly ri ci)`.
  have hbridge := detPoly_aeval_eq_minor ri ci
  have hzero : (aeval (stdAddChar (1 : ZMod p) : ℂ)) (detPoly ri ci) = 0 := by
    rw [hbridge]; exact hD
  -- `cyclotomic p ℤ ∣ detPoly`.
  have hdvdZ : cyclotomic p ℤ ∣ detPoly ri ci := cyclotomic_dvd_of_aeval_eq_zero hzero
  -- map mod `p`: `(X − 1)^{p−1} ∣ detPolyModP`.
  have hmap : map (Int.castRingHom (ZMod p)) (cyclotomic p ℤ) = (X - 1) ^ (p - 1) := by
    rw [map_cyclotomic_int]; exact cyclotomic_p_mod_p
  have hdvdP : (X - 1 : (ZMod p)[X]) ^ (p - 1) ∣ detPolyModP ri ci := by
    rw [detPolyModP, ← hmap]
    exact Polynomial.map_dvd _ hdvdZ
  -- contradiction with the crux.
  exact hCrux n ri ci hri hci hdvdP

/-- **End-to-end: the Vandermonde-mod-`p` crux implies Tao's additive uncertainty principle
(PROVEN composite).** Chaining `chebotarev_of_multiplicityBound` (this file) with
`tao_of_chebotarev` (`_TaoFromChebotarev.lean`): `MinorTaylorMultiplicityLt p ⟹ TaoUncertainty p`.
This pushes the sole open input of the prime-capacity dichotomy all the way down to a single
concrete combinatorial statement about a Vandermonde-type determinant mod `p`. -/
theorem tao_of_multiplicityBound (hCrux : MinorTaylorMultiplicityLt p) : TaoUncertainty p :=
  tao_of_chebotarev (chebotarev_of_multiplicityBound hCrux)

/-! ## Layer 4: the smallest crux instances (`n = 0`, `n = 1`) discharged as sanity checks (PROVEN).
The general crux is the deep open core and is NOT proven; we only de-name the trivial small cases,
where the `0 × 0` minor polynomial is `1` and the `1 × 1` minor polynomial is a single monomial
`X^k`, neither of which `(X − 1)^{p−1}` (a non-unit, with `1` as a non-root of `X^k`) can divide. -/

/-- **The `n = 0` case of the crux (PROVEN).** The empty minor has `detPoly = det (0×0) = 1`, so
`detPolyModP = 1`, and `(X − 1)^{p−1} ∣ 1` would make `(X − 1)^{p−1}` a unit — impossible since
`p − 1 ≥ 1` and `X − 1` is a non-unit (positive degree) in the domain `(ZMod p)[X]`. -/
theorem minorTaylorMultiplicityLt_zero (ri ci : Fin 0 → ZMod p) :
    ¬ ((X - 1) ^ (p - 1) ∣ detPolyModP ri ci) := by
  have hp1 : 1 ≤ p - 1 := by
    have := (Fact.out (p := p.Prime)).two_le; omega
  -- `detPolyModP = 1`.
  have hone : detPolyModP ri ci = 1 := by
    rw [detPolyModP, detPoly, Matrix.det_isEmpty, Polynomial.map_one]
  rw [hone]
  -- `(X − 1)^{p−1} ∣ 1` ⟹ `(X − 1)^{p−1}` is a unit ⟹ `X − 1` is a unit.
  intro hdvd
  have hunit : IsUnit ((X - 1 : (ZMod p)[X]) ^ (p - 1)) := isUnit_of_dvd_one hdvd
  have hX1unit : IsUnit (X - 1 : (ZMod p)[X]) := (isUnit_pow_iff (by omega)).1 hunit
  -- but `X − 1` has degree 1, so it is not a unit.
  have hdeg : (X - 1 : (ZMod p)[X]).degree = 1 := by
    simpa using degree_X_sub_C (1 : ZMod p)
  rw [Polynomial.isUnit_iff_degree_eq_zero, hdeg] at hX1unit
  exact one_ne_zero hX1unit

/-- **The `n = 1` case of the crux (PROVEN, sanity check).** The `1 × 1` minor polynomial is the
single monomial `X^{e 0 0}`, whose mod-`p` reduction is `X^{e 0 0}`. Since `X` and `X − 1` are
coprime (the root `1` of `X^{e 0 0}` has multiplicity `0`: evaluating at `1` gives `1 ≠ 0`), and
`p − 1 ≥ 1`, the divisor `(X − 1)^{p−1}` cannot divide `X^{e 0 0}`. This de-names the `n = 1`
instance; the general `n` case stays the named open crux. -/
theorem minorTaylorMultiplicityLt_one (ri ci : Fin 1 → ZMod p) :
    ¬ ((X - 1) ^ (p - 1) ∣ detPolyModP ri ci) := by
  have hp1 : p - 1 ≠ 0 := by have := (Fact.out (p := p.Prime)).two_le; omega
  -- `detPolyModP = X^{e 0 0}`.
  have hX : detPolyModP ri ci = X ^ minorExp ri ci 0 0 := by
    rw [detPolyModP, detPoly, Matrix.det_fin_one]
    simp [Matrix.of_apply, Polynomial.map_pow, map_X]
  rw [hX]
  -- `(X − 1)^{p−1} ∣ X^k` ⟹ `(X − C 1) ∣ X^k`, but `1` is not a root of `X^k`.
  intro hdvd
  have hroot : ¬ (X - C (1 : ZMod p)) ∣ X ^ minorExp ri ci 0 0 := by
    rw [dvd_iff_isRoot]; simp [IsRoot]
  have h1 : (X - (1 : (ZMod p)[X])) = X - C (1 : ZMod p) := by rw [map_one]
  rw [h1] at hdvd
  exact hroot ((dvd_pow_self _ hp1).trans hdvd)

end ProximityGap.Frontier.ChebotarevReductionModP

/-! ## Axiom audit (expected: `propext, Classical.choice, Quot.sound` only — no `sorryAx`).
`MinorTaylorMultiplicityLt` is a `def … : Prop` (a named classical hypothesis), so it carries no
axioms; the PROVEN content below consumes / discharges it. -/
#print axioms ProximityGap.Frontier.ChebotarevReductionModP.cyclotomic_p_mod_p
#print axioms ProximityGap.Frontier.ChebotarevReductionModP.isPrimitiveRoot_stdAddChar_one
#print axioms ProximityGap.Frontier.ChebotarevReductionModP.stdAddChar_eq_zeta_pow
#print axioms ProximityGap.Frontier.ChebotarevReductionModP.detPoly_aeval_eq_minor
#print axioms ProximityGap.Frontier.ChebotarevReductionModP.cyclotomic_dvd_of_aeval_eq_zero
#print axioms ProximityGap.Frontier.ChebotarevReductionModP.minorTaylorMultiplicityLt_iff
#print axioms ProximityGap.Frontier.ChebotarevReductionModP.chebotarev_of_multiplicityBound
#print axioms ProximityGap.Frontier.ChebotarevReductionModP.tao_of_multiplicityBound
#print axioms ProximityGap.Frontier.ChebotarevReductionModP.minorTaylorMultiplicityLt_zero
#print axioms ProximityGap.Frontier.ChebotarevReductionModP.minorTaylorMultiplicityLt_one
