/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Group.EvenFunction
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.FieldTheory.Finite.Basic

/-!
# Loop 49 (O11 sharpening) — the §7 subgroup-sumset lives in large characteristic and is governed by
# the ±pairing of the `2^m`-th roots of unity.

The BCHKS §7 attack (Loop46, `CandidateAttackLoop46.lean`) reduces the prize's *disproof* route to a
single additive-combinatorics question (O11):

> For a multiplicative subgroup `G` of order `2^m` (the prize's smooth domain), how large is the
> `ℓ`-fold distinct-subset-sumset `|G^{(+ℓ)}|`? Poly in `2^m` ⟹ the prize survives §7; super-poly at
> fixed gap ⟹ the prize-as-stated is **false**.

This loop sharpens O11 with two verified observations and a reduction, all sorry-free, axiom-clean.

## 1. The §7 subgroup cannot live in characteristic 2 (`no_even_order_element_char_two`).
A finite field of characteristic 2 has `2^k` elements, so `Fˣ` has *odd* order `2^k − 1`. By Lagrange
no element (hence no subgroup) has even order `2^m` (`m ≥ 1`). **So the §7 attack's domain is forced
into large characteristic** `p ≡ 1 (mod 2^m)` — exactly the STARK regime (Goldilocks/BabyBear-type
primes), where `G` is the group of `2^m`-th roots of unity in `F_p`.

## 2. Those roots are negation-closed — the ±pairing (`neg_pow_eq_one_of_even`).
Since `2^m` is even, `(-x)^{2^m} = x^{2^m}`, so the `2^m`-th roots of unity are closed under negation;
`−1` is the order-2 element `ζ^{2^{m-1}}`. Hence `G` partitions into `2^{m-1}` pairs `{g, −g}`. This
is the **only** prime-power-`2` vanishing relation (Lam–Leung): a sum of `n`-th roots of unity with
`n = 2^m` a prime power vanishes iff it is a `ℤ_{≥0}`-combination of the single prime `2`, i.e. is
built from the basic relations `g + (−g) = 0`.

## 3. The reduction (the genuine remaining question).
Two `ℓ`-subsets of `G` have equal sum iff their signed difference is a vanishing `{−1,0,1}`-sum of
`2^m`-th roots of unity. By Lam–Leung the *only* such relations are spanned by the ±pairing, so the
distinct-sum count is pinned **between** the pairing collapse (each of the `2^{m-1}` pairs
contributing `+g`, `−g`, or `0`, giving the structural ceiling `3^{2^{m-1}}`) and the genuine
cross-pair distinctness (the open lower bound). Both ends are **super-polynomial in `2^m`** at fixed
gap, so — *modulo formalizing the Lam–Leung distinctness* — O11 leans toward **disproof of the
minimal-domain prize**, consistent with `thm71_no_fixed_exponent` (Loop46), and re-opens the O6
statement-fidelity question (is the prize claimed at small `n`, or only asymptotically?).

We verify the two structural facts (1) and (2) here; the Lam–Leung distinctness (3) is the next
residual. See `DISPROOF_LOG.md` (O14/Loop49).
-/

namespace ArkLib.ProximityGap.SubgroupSumsetLoop49

open scoped BigOperators

/-! ## 1. Characteristic-2 obstruction: no even-order multiplicative subgroup -/

/-- **No element of even multiplicative order in characteristic 2.** In a finite field `F` of
characteristic 2, `|Fˣ| = |F| − 1` is odd, so the order of any unit divides an odd number and is odd.
In particular there is no element — hence no subgroup — of order `2^m` for `m ≥ 1`. This forces the
§7 attack's smooth multiplicative subgroup into *large characteristic*. -/
theorem orderOf_odd_of_char_two {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F = 2) (x : Fˣ) :
    Odd (orderOf x) := by
  -- `|Fˣ| = |F| − 1`, and `|F|` is even in char 2, so `|Fˣ|` is odd
  have hcard : Fintype.card Fˣ = Fintype.card F - 1 := Fintype.card_units F
  have hFeven : Fintype.card F % 2 = 0 := FiniteField.even_card_of_char_two hF
  have hpos : 0 < Fintype.card F := Fintype.card_pos
  have hdvd : orderOf x ∣ Fintype.card Fˣ := orderOf_dvd_card
  rw [Nat.odd_iff]
  rcases Nat.even_or_odd (orderOf x) with he | ho
  · exfalso
    have h2 : 2 ∣ Fintype.card Fˣ := (even_iff_two_dvd.mp he).trans hdvd
    rw [hcard] at h2
    omega
  · rwa [Nat.odd_iff] at ho

/-- **Corollary: a multiplicative subgroup of even order `2^m` (`m ≥ 1`) cannot exist in
characteristic 2.** Any such subgroup would contain (by Cauchy) an element of order `2`, but every
unit has odd order. -/
theorem no_even_order_element_char_two {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F = 2) (x : Fˣ) (m : ℕ) (hm : 1 ≤ m) :
    orderOf x ≠ 2 ^ m := by
  intro hx
  have hodd := orderOf_odd_of_char_two hF x
  rw [hx] at hodd
  -- `2^m` is even for `m ≥ 1`, contradicting oddness
  have hev : Even (2 ^ m) := Nat.even_pow.mpr ⟨even_two, by omega⟩
  exact (Nat.not_even_iff_odd.mpr hodd) hev

/-! ## 2. The ±pairing: even-power roots of unity are negation-closed -/

/-- **Negation closure of even-power roots of unity.** If `d` is even and `x^d = 1` in a commutative
ring, then `(−x)^d = 1`: the `d`-th roots of unity are closed under negation. For `d = 2^m` (`m ≥ 1`)
this is the ±pairing `{g, −g}` underlying the Lam–Leung structure of subset-sum coincidences. -/
theorem neg_pow_eq_one_of_even {R : Type*} [CommRing R] {d : ℕ} (hd : Even d)
    {x : R} (hx : x ^ d = 1) :
    (-x) ^ d = 1 := by
  rw [hd.neg_pow, hx]

/-- **The root set is negation-closed.** Phrased as a membership stability: negation maps the set of
`d`-th roots of unity into itself when `d` is even. This is the structural form of `±g ∈ G`. -/
theorem nthRoots_set_neg_closed {R : Type*} [CommRing R] {d : ℕ} (hd : Even d) :
    ∀ x ∈ {y : R | y ^ d = 1}, -x ∈ {y : R | y ^ d = 1} := by
  intro x hx
  exact neg_pow_eq_one_of_even hd hx

/-- **`−1` is a `2^m`-th root of unity for `m ≥ 1`.** It is the order-2 element of the subgroup, the
canonical realiser of the ±pairing (`g · (−1) = −g`). -/
theorem neg_one_mem_nthRoots {R : Type*} [CommRing R] {m : ℕ} (hm : 1 ≤ m) :
    (-1 : R) ^ (2 ^ m) = 1 := by
  have hd : Even (2 ^ m) := Nat.even_pow.mpr ⟨even_two, by omega⟩
  rw [hd.neg_pow, one_pow]

/-! ## 3. Note on the vanishing power-sums (not formalized here)

The survive-direction intuition rests on the vanishing power-sums `∑_{g ∈ G} g^j = 0` (`1 ≤ j < |G|`)
of the full `2^m`-th-root group — these are *Vieta* identities in the **field** `F` (the `2^m`-th
roots are the roots of `X^{2^m} − 1`, whose subleading coefficients vanish for `2^m ≥ 2`), **not** a
group-theoretic fact: over an abstract finite abelian group `∑_{a} a` need *not* vanish (e.g. `ℤ/2`).
Formalizing them requires the `nthRoots` multiset and coefficient extraction; that is deferred. The
honest takeaway is that these are genuine *additive* constraints on a *multiplicative* subgroup — the
sum-product tension — and whether they suppress `|G^{(+ℓ)}|` below super-polynomial is exactly the
open O11 question.
-/

end ArkLib.ProximityGap.SubgroupSumsetLoop49

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.SubgroupSumsetLoop49.orderOf_odd_of_char_two
#print axioms ArkLib.ProximityGap.SubgroupSumsetLoop49.no_even_order_element_char_two
#print axioms ArkLib.ProximityGap.SubgroupSumsetLoop49.neg_pow_eq_one_of_even
#print axioms ArkLib.ProximityGap.SubgroupSumsetLoop49.nthRoots_set_neg_closed
#print axioms ArkLib.ProximityGap.SubgroupSumsetLoop49.neg_one_mem_nthRoots
