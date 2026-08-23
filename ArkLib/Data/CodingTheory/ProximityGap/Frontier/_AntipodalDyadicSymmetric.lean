/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.RingTheory.Polynomial.Vieta

/-!
# The antipodal dyadic elementary-symmetric recursion (#444)

This file formalizes the **char-free, prime-independent algebraic engine** of issue #444's
most-promising off-BGK prize route (comment 97's antipodal-tower list-decoding recursion).

## The math (clean, char-free, holds over ANY commutative ring `R`)

For a `Finset Z : Finset R` of "representatives", consider the antipodally-closed root multiset
`S = {z, −z : z ∈ Z}` (size `2|Z|`).  Its monic polynomial factors through squaring:

  `∏_{z∈Z} (X − C z)(X + C z) = (∏_{z∈Z} (X − C (z^2))).comp (X^2)`

because `(X − C z)(X + C z) = X^2 − C (z^2) = (X − C (z^2)).comp (X^2)`, and `Polynomial.comp`
distributes over the finite product.  Writing `Q := ∏_{z∈Z}(X − C (z^2))` — the polynomial whose
roots are the squares `{z^2}` — the antipodal polynomial `P := ∏_{z∈Z}(X − C z)(X + C z)` equals
`Q.comp (X^2)` (= `Polynomial.expand R 2 Q`).

The coefficient consequences (the comment-97 identity `e_{2ℓ}(±z) = (−1)^ℓ e_ℓ(z²)`, `e_odd = 0`):

* `P.coeff k = 0` for **odd** `k` (a `comp (X^2)` is supported on even degrees);
* `P.coeff (2*ℓ) = Q.coeff ℓ` (the even coefficients of `P` ARE the coefficients of `Q`).

Since elementary symmetric functions are (signed) coefficients
(`e_k(S) = (−1)^k · [X^{|S|−k}] P` for a monic degree-`|S|` `P`), this is exactly the **dyadic
descent** `e_{2ℓ}(S) = (−1)^ℓ e_ℓ(Z²)`, `e_odd(S) = 0` — prime-independent, descending
`|S| = 2m → |Z²| = m` (one octave of the antipodal tower).  This is delivered literally in the
elementary-symmetric form by `antipodal_esymm_even` / `antipodal_esymm_odd` below, via Mathlib's
`Multiset.prod_X_sub_C_coeff`.

## Honest scope (this is the engine, NOT the prize)

This is a **genuine char-free algebraic identity** — PROVEN, not a reduction to anything open.  It
is the *engine* of the off-BGK list route: it formalizes the prime-independent dyadic descent that
makes the worst-case `2`-sparse list count **prime-decoupled** (#444 c.97).  The list **upper
bound** itself — the prize's open core — is NOT proved here; this recursion *feeds* it but does not
by itself close it.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.  Issue #444.
-/

namespace ProximityGap.Frontier.AntipodalDyadicSymmetric

open Polynomial

variable {R : Type*} [CommRing R]

/-! ## The antipodal factor and its descent -/

/-- One antipodal factor squares away: `(X − C z)(X + C z) = (X − C (z²)).comp (X²)`.
This is the single-root form of the dyadic descent — the product over `z ∈ Z` of these is the
whole identity. -/
theorem antipodal_factor (z : R) :
    (X - C z) * (X + C z) = (X - C (z ^ 2)).comp (X ^ 2) := by
  rw [sub_comp, X_comp, C_comp, map_pow]
  ring

/-- **The core identity (`antipodalPoly_eq_comp`).**  The antipodal polynomial whose roots are
`{z, −z : z ∈ Z}` equals the polynomial whose roots are the squares `{z² : z ∈ Z}`, composed with
`X²`:

  `∏_{z∈Z} (X − C z)(X + C z) = (∏_{z∈Z} (X − C (z²))).comp (X²)`.

Holds over any `CommRing R`.  This is the char-free dyadic-descent engine. -/
theorem antipodalPoly_eq_comp (Z : Finset R) :
    (∏ z ∈ Z, (X - C z) * (X + C z))
      = (∏ z ∈ Z, (X - C (z ^ 2))).comp (X ^ 2) := by
  rw [prod_comp]
  exact Finset.prod_congr rfl fun z _ => antipodal_factor z

/-! ## Coefficient consequences (even/odd descent) -/

/-- **Odd coefficients vanish (`antipodalPoly_coeff_odd`).**  For odd `k`, the antipodal polynomial
has `coeff k = 0` — the `comp (X²)` is supported entirely on even degrees.  (`e_odd(S) = 0`.) -/
theorem antipodalPoly_coeff_odd (Z : Finset R) {k : ℕ} (hk : Odd k) :
    (∏ z ∈ Z, (X - C z) * (X + C z)).coeff k = 0 := by
  rw [antipodalPoly_eq_comp, ← expand_eq_comp_X_pow, coeff_expand (by norm_num : 0 < 2)]
  rw [if_neg]
  rw [Nat.odd_iff] at hk
  omega

/-- **Even coefficients descend (`antipodalPoly_coeff_even`).**  The degree-`2ℓ` coefficient of the
antipodal polynomial equals the degree-`ℓ` coefficient of the squares polynomial:

  `(∏_{z∈Z}(X − C z)(X + C z)).coeff (2*ℓ) = (∏_{z∈Z}(X − C (z²))).coeff ℓ`.

The `X²` substitution carries the degree-`ℓ` term to degree `2ℓ`.  This is the bare coefficient
form of `e_{2ℓ}(S) = (−1)^ℓ e_ℓ(Z²)`. -/
theorem antipodalPoly_coeff_even (Z : Finset R) (ℓ : ℕ) :
    (∏ z ∈ Z, (X - C z) * (X + C z)).coeff (2 * ℓ)
      = (∏ z ∈ Z, (X - C (z ^ 2))).coeff ℓ := by
  rw [antipodalPoly_eq_comp, ← expand_eq_comp_X_pow, coeff_expand_mul' (by norm_num : 0 < 2)]

/-! ## The literal elementary-symmetric form (optional polish)

We now state the descent in the literal `Multiset.esymm` language.  The antipodal multiset is
`S = Z.val.map id + Z.val.map (−·)` (the `2|Z|` roots `{z, −z}`); the squares multiset is
`Z².val = Z.val.map (·²)`.  Mathlib's `Multiset.prod_X_sub_C_coeff` converts coefficients to
elementary symmetric functions, so the coefficient identities above become the textbook dyadic
elementary-symmetric recursion. -/

/-- The antipodal root multiset `{z, −z : z ∈ Z}` (cardinality `2|Z|`). -/
noncomputable def antipodalRoots (Z : Finset R) : Multiset R :=
  Z.val.map id + Z.val.map (fun z => -z)

/-- The squares root multiset `{z² : z ∈ Z}` (cardinality `|Z|`). -/
noncomputable def squareRoots (Z : Finset R) : Multiset R :=
  Z.val.map (fun z => z ^ 2)

@[simp] theorem card_antipodalRoots (Z : Finset R) :
    Multiset.card (antipodalRoots Z) = 2 * Z.card := by
  rw [antipodalRoots, Multiset.card_add, Multiset.card_map, Multiset.card_map,
    ← Finset.card_val, two_mul]

@[simp] theorem card_squareRoots (Z : Finset R) :
    Multiset.card (squareRoots Z) = Z.card := by
  rw [squareRoots, Multiset.card_map, ← Finset.card_val]

/-- The monic polynomial of the antipodal roots equals the antipodal product `∏ (X−Cz)(X+Cz)`. -/
theorem prod_X_sub_C_antipodalRoots (Z : Finset R) :
    ((antipodalRoots Z).map fun t => X - C t).prod
      = ∏ z ∈ Z, (X - C z) * (X + C z) := by
  rw [antipodalRoots, Multiset.map_add, Multiset.prod_add, Finset.prod, Multiset.map_map,
    Multiset.map_map, ← Multiset.prod_map_mul]
  congr 1
  refine Multiset.map_congr rfl fun z _ => ?_
  simp [Function.comp, sub_neg_eq_add]

/-- The monic polynomial of the squares roots equals the squares product `∏ (X − C (z²))`. -/
theorem prod_X_sub_C_squareRoots (Z : Finset R) :
    ((squareRoots Z).map fun t => X - C t).prod = ∏ z ∈ Z, (X - C (z ^ 2)) := by
  rw [squareRoots, Multiset.map_map, Finset.prod]
  rfl


/-- **The dyadic elementary-symmetric descent, even degrees (`antipodal_esymm_even`).**  For
`ℓ ≤ |Z|`, the elementary symmetric function of the antipodal roots in *even* co-degree equals,
up to sign, the elementary symmetric function of the squares:

  `e_{2|Z|−2ℓ}(S) = (−1)^ℓ · e_{|Z|−ℓ}(Z²)`,

equivalently `e_{2j}(S) = (−1)^{j} e_{j}(Z²)` after reindexing `j = |Z|−ℓ`.  This is the literal
comment-97 identity `e_{2ℓ}(±z) = (−1)^ℓ e_ℓ(z²)`. -/
theorem antipodal_esymm_even (Z : Finset R) {ℓ : ℕ} (hℓ : ℓ ≤ Z.card) :
    (antipodalRoots Z).esymm (2 * (Z.card - ℓ))
      = (-1) ^ (Z.card - ℓ) * (squareRoots Z).esymm (Z.card - ℓ) := by
  -- Both sides via `prod_X_sub_C_coeff`, matched through `antipodalPoly_coeff_even`.
  have hcardA : Multiset.card (antipodalRoots Z) = 2 * Z.card := card_antipodalRoots Z
  have hcardS : Multiset.card (squareRoots Z) = Z.card := card_squareRoots Z
  -- LHS coefficient: coeff at 2ℓ of antipodal poly = (-1)^(2|Z|-2ℓ) e_{2|Z|-2ℓ}(S)
  have hA := Multiset.prod_X_sub_C_coeff (antipodalRoots Z)
      (k := 2 * ℓ) (by rw [hcardA]; omega)
  rw [prod_X_sub_C_antipodalRoots, hcardA] at hA
  -- RHS coefficient: coeff at ℓ of squares poly = (-1)^(|Z|-ℓ) e_{|Z|-ℓ}(Z²)
  have hS := Multiset.prod_X_sub_C_coeff (squareRoots Z) (k := ℓ) (by rw [hcardS]; omega)
  rw [prod_X_sub_C_squareRoots, hcardS] at hS
  -- Bridge the two coefficients with the even descent.
  have hbridge := antipodalPoly_coeff_even Z ℓ
  rw [hA, hS] at hbridge
  -- Now: (-1)^(2|Z|-2ℓ) e_{2|Z|-2ℓ}(S) = (-1)^(|Z|-ℓ) e_{|Z|-ℓ}(Z²)
  -- Note 2*|Z| - 2*ℓ = 2*(|Z|-ℓ) and (-1)^(2m) = 1.
  have he : 2 * Z.card - 2 * ℓ = 2 * (Z.card - ℓ) := by omega
  rw [he] at hbridge
  rw [pow_mul] at hbridge
  simpa using hbridge

/-- **The dyadic elementary-symmetric descent, odd degrees (`antipodal_esymm_odd`).**  Every
*odd-co-degree* elementary symmetric function of the antipodal roots vanishes: `e_odd(S) = 0`.
Stated as: for odd `j ≤ 2|Z|`, `e_j(S) = 0`. -/
theorem antipodal_esymm_odd [Nontrivial R] (Z : Finset R) {j : ℕ}
    (hj : Odd j) (hjle : j ≤ 2 * Z.card) :
    (antipodalRoots Z).esymm j = 0 := by
  have hcardA : Multiset.card (antipodalRoots Z) = 2 * Z.card := card_antipodalRoots Z
  -- The complementary index k = 2|Z| - j is odd (2|Z| even, j odd).
  set k := 2 * Z.card - j with hk
  have hkodd : Odd k := by
    rcases hj with ⟨m, hm⟩
    refine ⟨Z.card - m - 1, ?_⟩
    omega
  have hkle : k ≤ Multiset.card (antipodalRoots Z) := by rw [hcardA, hk]; omega
  have hA := Multiset.prod_X_sub_C_coeff (antipodalRoots Z) hkle
  rw [prod_X_sub_C_antipodalRoots] at hA
  -- coeff k of antipodal poly is 0 (k odd).
  have hzero := antipodalPoly_coeff_odd Z hkodd
  rw [hzero] at hA
  -- 0 = (-1)^(card - k) * e_{card - k}(S); card - k = j; (-1)^j is a unit ⟹ e_j = 0.
  have hcj : Multiset.card (antipodalRoots Z) - k = j := by rw [hcardA, hk]; omega
  rw [hcj] at hA
  have heq : ((-1 : R) ^ j) * (antipodalRoots Z).esymm j = 0 := hA.symm
  have hunit : IsUnit ((-1 : R) ^ j) := (isUnit_one.neg).pow j
  exact (hunit.mul_right_eq_zero).mp heq

end ProximityGap.Frontier.AntipodalDyadicSymmetric

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Frontier.AntipodalDyadicSymmetric.antipodalPoly_eq_comp
#print axioms ProximityGap.Frontier.AntipodalDyadicSymmetric.antipodalPoly_coeff_odd
#print axioms ProximityGap.Frontier.AntipodalDyadicSymmetric.antipodalPoly_coeff_even
#print axioms ProximityGap.Frontier.AntipodalDyadicSymmetric.antipodal_esymm_even
#print axioms ProximityGap.Frontier.AntipodalDyadicSymmetric.antipodal_esymm_odd
