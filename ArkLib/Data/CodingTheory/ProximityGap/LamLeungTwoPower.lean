/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Lam–Leung for 2-power roots of unity: vanishing sums decompose into antipodal pairs (#389)

The census programme's collision systems live in the classical theory of vanishing sums of
roots of unity.  For a **2-power-order** smooth domain the relevant root order is `2^μ` (a single
prime divisor), where the Lam–Leung structure theorem
([Lam–Leung, J. Algebra 224 (2000); arXiv:math/9511209], via Rédei–de Bruijn–Schoenberg; the
2-power case is robust to weight 21, [Christie–Dykema–Klep, arXiv:2008.11268]) takes its
strongest form:

> **Every vanishing sum of `2^μ`-th roots of unity decomposes into antipodal pairs
> `ζⁱ + (−ζⁱ) = 0`.**  The only minimal vanishing sum of 2-power order is the 2-gon
> `{ζ, −ζ}`; no exotic minimal blocks intrude (those first appear with prime factors 5, 7).

This file formalizes the *structural heart* of that statement as a reusable, axiom-clean engine.

Write a vanishing sum with multiplicities `cⱼ` as the polynomial `P = ∑ⱼ cⱼ·Xʲ` of degree
`< 2^μ`.  Let `ζ` be a primitive `2^μ`-th root of unity and `h = 2^{μ-1}`.  Then:

* `ζ` has minimal polynomial `Φ_{2^μ}(X) = X^h + 1` (the `2^μ`-th cyclotomic polynomial — a
  standard Mathlib fact via `IsPrimitiveRoot.cyclotomic_eq_minpoly` once `cyclotomic (2^μ) =
  X^{2^{μ-1}} + 1`), so `P(ζ) = 0 ⟺ (X^h + 1) ∣ P` (using `deg P < 2h = 2^μ`).  This is the
  *named bridge* supplying the divisibility hypothesis below; it is classical and Mathlib-backed.
* The antipodal map `ζⁱ ↦ −ζⁱ` is exactly the index shift `i ↦ i + h`, because
  `ζ^h = −1` (`antipodal_shift`).
* **The engine** (`antipodal_coeff_of_dvd`): divisibility `P = (X^h + 1)·Q` with `deg Q < h`
  forces `cᵢ = c_{i+h}` for every `i < h` — i.e. the multiplicity on `ζⁱ` equals the
  multiplicity on its antipode `−ζⁱ = ζ^{i+h}`.  *That equality is precisely the
  antipodal-pair decomposition*: `P` is `∑_{i<h} cᵢ·(Xⁱ + X^{i+h})`, and each block
  `ζⁱ + ζ^{i+h} = ζⁱ − ζⁱ = 0`.

The engine is the divisibility-`⟹`-antipodal direction, which is the content the census uses
(it replaces the machine-generated per-weight pairing enumeration — 10395 pairings → 8
survivors — with a uniform a-priori decomposition).  The reverse direction (vanishing `⟹`
divisible) is the cyclotomic-minimality bridge noted above.  This does NOT close any open core;
it is a census-compression lemma.  See `docs/kb/deltastar-literature-findings-2026-06-13.md`.
-/

open Polynomial

namespace ArkLib.ProximityGap.LamLeung

variable {R : Type*} [CommRing R]

/-- **The antipodal map is the index shift by `h`.**  If `ζ^h = −1` (e.g. `ζ` a primitive
`2h`-th root of unity, `h = 2^{μ-1}`), then `ζ^{i+h} = −ζⁱ`: shifting the exponent by `h`
sends each root to its antipode.  This is why the coefficient equality `cᵢ = c_{i+h}` below
*is* the antipodal-pair decomposition. -/
theorem antipodal_shift {ζ : R} {h : ℕ} (hζ : ζ ^ h = -1) (i : ℕ) :
    ζ ^ (i + h) = -ζ ^ i := by
  rw [pow_add, hζ]; ring

/-- **The Lam–Leung antipodal engine (2-power case).**  If a coefficient polynomial is divisible
by `X^h + 1` with quotient of degree `< h` — i.e. `P = (X^h + 1)·Q`, `Q.natDegree < h`, which for
`deg P < 2h` is exactly `P(ζ) = 0` at a primitive `2h`-th root `ζ` — then its coefficients are
**antipodally equal**: `P.coeff i = P.coeff (i + h)` for every `i < h`.

In census terms: the multiplicity of the sum on `ζⁱ` equals the multiplicity on its antipode
`−ζⁱ = ζ^{i+h}`, so the vanishing sum splits into antipodal pairs `{ζⁱ, −ζⁱ}` each of
multiplicity `P.coeff i`.  Unconditional and axiom-clean. -/
theorem antipodal_coeff_of_dvd {h : ℕ} (Q : R[X]) (hQ : Q.natDegree < h)
    {i : ℕ} (hi : i < h) :
    ((X ^ h + 1) * Q).coeff i = ((X ^ h + 1) * Q).coeff (i + h) := by
  have hPexp : (X ^ h + 1) * Q = Q * X ^ h + Q := by ring
  rw [hPexp, coeff_add, coeff_add, coeff_mul_X_pow', coeff_mul_X_pow']
  rw [if_neg (by omega : ¬ h ≤ i), if_pos (by omega : h ≤ i + h)]
  have e1 : i + h - h = i := by omega
  have hz : Q.coeff (i + h) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  rw [e1, hz]; ring

/-- **The vanishing sum evaluates to a sum of antipodal pairs.**  If `ζ^h = −1`, then a
polynomial divisible by `X^h + 1` evaluates at `ζ` to `0` — directly, the antipodal pairing
makes `(ζ^h + 1) = 0` annihilate the whole sum.  This is the "easy" (`divisible ⟹ vanishing`)
direction; combined with `antipodal_coeff_of_dvd` it certifies the pairing both as a coefficient
symmetry and as the literal vanishing of `(ζ^h + 1)·Q(ζ)`. -/
theorem eval_dvd_eq_zero {ζ : R} {h : ℕ} (hζ : ζ ^ h = -1) (Q : R[X]) :
    ((X ^ h + 1) * Q).eval ζ = 0 := by
  rw [eval_mul, eval_add, eval_pow, eval_X, eval_one, hζ]; ring

end ArkLib.ProximityGap.LamLeung
