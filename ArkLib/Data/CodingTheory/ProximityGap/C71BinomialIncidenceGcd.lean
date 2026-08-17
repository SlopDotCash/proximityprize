/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Int.GCD
import Mathlib.Data.Finset.Card
import ArkLib.Data.CodingTheory.ProximityGap.C71BinomialIncidence

/-!
# Conjecture 7.1 residual: the **gcd-tight** binomial (2-term) strata incidence bound (#444)

## Context (extends `C71BinomialIncidence`, `861dd47e5`)
`C71BinomialIncidence.binomial_incidence_card_le` landed the polynomial-method count
`#{x : X^i - c X^j = 0, x ≠ 0} ≤ i - j` via `Polynomial.card_nthRoots`. That bound is robust but
**field-universal** -- it ignores the THIN-subgroup structure of the domain `μ_n` and is therefore
*useless when `i - j ~ n`* (the bound degenerates to `≈ n`, i.e. "every point could be a root").
The c71binom report explicitly left the **gcd-tight refinement** -- the one that uses the cyclic
structure of `μ_n` -- as a follow-on. This file supplies it.

## The sharp law (cyclic-kernel count)
On the thin subgroup `μ_n` (cyclic of order `n`), the map `x ↦ x^(i-j)` is a group endomorphism
whose kernel is the `gcd(i-j, n)`-th roots of unity inside `μ_n`, of size exactly `gcd(i-j, n)`.
Hence the fiber `{x ∈ μ_n : x^(i-j) = c}` is empty or a single coset of that kernel, so its
cardinality is `0` or exactly `gcd(i-j, n)` -- in particular `≤ gcd(i-j, n)`.

Probe `scripts/probes/probe_c71_binomial_incidence_gcd.py` (EXACT, 4584/4584 over PROPER thin
`μ_n` `n = 2^a` (`a = 2,3,4`), multi-prime incl `p > n^3` and Fermat `257`, genuine binomial
`c ∈ μ_n`, NEVER
`n = q-1`) confirms the law `#roots ∈ {0, gcd(i-j, n)}`, and that the `gcd` bound is **strictly
sharper than `i - j`** in 2140 of those rows. So this is genuine frontier-movement, not a
re-confirmation of the `≤ i-j` bound.

## The argument (char-free, no primitive-root hypothesis needed)
For a nonzero domain point `x` with `x^(i-j) = c` AND `x^n = 1` (the only `μ_n` fact used), let
`g = gcd(i-j, n)`. Bézout (`Nat.gcd_eq_gcd_ab`) gives integers `u = gcdA`, `v = gcdB` with
`g = (i-j)·u + n·v`. Using `zpow` on the nonzero `x`:
  `x^g = x^((i-j)u + nv) = (x^(i-j))^u · (x^n)^v = c^u · 1^v = c^u`.
So **every** root satisfies `x^g = c^u` for the FIXED field element `c' := c^u` (a `zpow`,
well-defined since `c ≠ 0`). The roots therefore inject into `nthRoots g c'`, whose multiset
cardinality is `≤ g = gcd(i-j, n)` (`Polynomial.card_nthRoots`).

## Theorems
* `pow_gcd_of_pow_eq_of_pow_n` : the key cyclic-kernel collapse: `x ≠ 0`, `x^d = c`, `x^n = 1`
  ⟹ `x ^ gcd(d, n) = c ^ (gcdA d n : ℤ)` (a `zpow`).
* `binomial_incidence_card_le_gcd` (HEADLINE) : for any `S : Finset F` whose elements all satisfy
  `x^n = 1` (i.e. `S ⊆ μ_n`), and any `c`, the count of nonzero points of `S` at which the
  binomial direction `X^i - c X^j` (`j < i`) vanishes is at most `Nat.gcd (i - j) n`. This is
  STRICTLY sharper than `C71BinomialIncidence.binomial_incidence_card_le` whenever
  `gcd(i-j, n) < i - j` (e.g. all `i-j` coprime-to-`n` rows give `gcd = 1`, a single root).

These EXTEND `C71BinomialIncidence` (the `≤ i-j` count) by injecting the THIN-subgroup (`x^n = 1`)
structure; they add no character-sum / BGK content. The `3`-term strata and the full
strata-incidence-to-soundness reduction remain OPEN and are NOT claimed here.

Axiom-clean (`propext, Classical.choice, Quot.sound`).
-/

open Finset Polynomial

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

namespace ArkLib.ProximityGap.C71BinomialIncidenceGcd

variable {F : Type*} [Field F] [DecidableEq F]

/-- **The cyclic-kernel collapse.** If `x ≠ 0`, `x ^ d = c`, and `x ^ n = 1` (the `μ_n` membership
fact), then `x ^ gcd(d, n) = c ^ (gcdA d n : ℤ)` as a `zpow`. Bézout `gcd d n = d·gcdA + n·gcdB`
lifted through `zpow_add₀` on the nonzero `x`, killing the `x^n = 1` factor. This is what makes the
`gcd`-tight count possible: every fiber point lands on a SINGLE field value `c ^ gcdA`. -/
theorem pow_gcd_of_pow_eq_of_pow_n {x c : F} (hx : x ≠ 0) {d n : ℕ}
    (hd : x ^ d = c) (hn : x ^ n = 1) :
    x ^ (Nat.gcd d n) = c ^ (Nat.gcdA d n) := by
  -- Bézout: (gcd d n : ℤ) = d * gcdA d n + n * gcdB d n
  have hbez : (Nat.gcd d n : ℤ) = d * Nat.gcdA d n + n * Nat.gcdB d n := Nat.gcd_eq_gcd_ab d n
  -- compute via zpow on the nonzero x
  have hxz : (x : F) ^ (Nat.gcd d n : ℤ) = c ^ (Nat.gcdA d n) := by
    rw [hbez, zpow_add₀ hx, zpow_mul, zpow_mul]
    -- x ^ (d : ℤ) = x ^ d = c;  x ^ (n : ℤ) = x ^ n = 1
    have h1 : (x : F) ^ (d : ℤ) = c := by rw [zpow_natCast, hd]
    have h2 : (x : F) ^ (n : ℤ) = 1 := by rw [zpow_natCast, hn]
    rw [h1, h2, one_zpow, mul_one]
  -- drop the (gcd : ℤ) zpow back to a ℕ pow
  rwa [zpow_natCast] at hxz

/-- **The gcd-tight binomial-direction incidence bound (HEADLINE).** For any finite set `S ⊆ F`
all of whose elements satisfy `x ^ n = 1` (i.e. `S ⊆ μ_n`, the thin subgroup), and any `c`,
the number of NONZERO points of `S` at which the binomial direction `X^i - c X^j` (`j < i`,
genuine) vanishes is at most `Nat.gcd (i - j) n`. STRICTLY sharper than the field-universal
`C71BinomialIncidence.binomial_incidence_card_le` (`≤ i - j`) whenever `gcd(i-j, n) < i - j` --
the thin-subgroup refinement that makes the incidence count useful in the prize regime. -/
theorem binomial_incidence_card_le_gcd (S : Finset F) (c : F)
    {i j n : ℕ} (hij : j < i) (hSn : ∀ x ∈ S, x ^ n = 1) :
    (S.filter (fun x => x ≠ 0 ∧ x ^ i - c * x ^ j = 0)).card ≤ Nat.gcd (i - j) n := by
  set d := i - j with hd
  set c' : F := c ^ (Nat.gcdA d n) with hc'
  -- the qualifying roots inject into nthRoots (gcd d n) c'
  set T := S.filter (fun x => x ≠ 0 ∧ x ^ i - c * x ^ j = 0) with hT
  by_cases hgpos : 0 < Nat.gcd d n
  · have hsub : T ⊆ (nthRoots (Nat.gcd d n) c').toFinset := by
      intro x hx
      rw [hT, mem_filter] at hx
      obtain ⟨hxS, hxne, hroot⟩ := hx
      -- from the binomial vanishing: x^d = c (punctured reduction)
      have hpow : x ^ d = c :=
        (ArkLib.ProximityGap.C71BinomialIncidence.binomial_root_iff_pow_eq c x hxne
          (le_of_lt hij)).mp hroot
      -- μ_n membership: x^n = 1
      have hxn : x ^ n = 1 := hSn x hxS
      -- collapse to the single field value c'
      have hcollapse : x ^ (Nat.gcd d n) = c' := by
        rw [hc']; exact pow_gcd_of_pow_eq_of_pow_n hxne hpow hxn
      rw [Multiset.mem_toFinset, mem_nthRoots hgpos]
      exact hcollapse
    calc T.card ≤ (nthRoots (Nat.gcd d n) c').toFinset.card := Finset.card_le_card hsub
      _ ≤ Multiset.card (nthRoots (Nat.gcd d n) c') := Multiset.toFinset_card_le _
      _ ≤ Nat.gcd d n := card_nthRoots (Nat.gcd d n) c'
  · -- gcd d n = 0 forces d = 0, contradicting j < i (so this branch is vacuous on the data,
    -- but we close it directly: gcd (i-j) n = 0 ⟹ i - j = 0 ⟹ i ≤ j, contra hij).
    exfalso
    have hgz : Nat.gcd d n = 0 := Nat.eq_zero_of_not_pos hgpos
    have hd0 : d = 0 := Nat.eq_zero_of_gcd_eq_zero_left hgz
    have : i - j = 0 := hd0
    omega

/-- **Gcd-tight binomial incidence bound without a puncturing predicate.** If `n > 0`, every
point of `S ⊆ μ_n` is nonzero, so the sharp cyclic-kernel bound applies directly to the ordinary
binomial vanishing filter. This is the caller-facing form of
`binomial_incidence_card_le_gcd` for positive-order thin subgroups. -/
theorem binomial_incidence_card_le_gcd_unpunctured (S : Finset F) (c : F)
    {i j n : ℕ} (hn : 0 < n) (hij : j < i) (hSn : ∀ x ∈ S, x ^ n = 1) :
    (S.filter (fun x => x ^ i - c * x ^ j = 0)).card ≤ Nat.gcd (i - j) n := by
  rw [← C71BinomialIncidence.binomial_incidence_filter_punctured_eq_unpunctured S c hn hSn]
  exact binomial_incidence_card_le_gcd S c hij hSn

/-- **Coprime-step binomial incidence is at most one.** In the gcd-tight C71 binomial bound, the
most useful thin-subgroup rows are the steps `i-j` coprime to the subgroup order `n`: the power map
`x ↦ x^(i-j)` has trivial kernel on `μ_n`, so a binomial direction has at most one nonzero root on
any finite `S ⊆ μ_n`. This is the caller-facing exact-incidence corollary used to isolate the
Sidon-like rows of the 2-sparse stratum. -/
theorem binomial_incidence_card_le_one_of_coprime (S : Finset F) (c : F)
    {i j n : ℕ} (hij : j < i) (hSn : ∀ x ∈ S, x ^ n = 1)
    (hcop : Nat.Coprime (i - j) n) :
    (S.filter (fun x => x ≠ 0 ∧ x ^ i - c * x ^ j = 0)).card ≤ 1 := by
  simpa [hcop.gcd_eq_one] using binomial_incidence_card_le_gcd S c hij hSn

/-- **Unpunctured coprime-step binomial incidence is at most one.** Positive-order `μ_n` removes
the explicit `x ≠ 0` guard from `binomial_incidence_card_le_one_of_coprime`. -/
theorem binomial_incidence_card_le_one_of_coprime_unpunctured (S : Finset F) (c : F)
    {i j n : ℕ} (hn : 0 < n) (hij : j < i) (hSn : ∀ x ∈ S, x ^ n = 1)
    (hcop : Nat.Coprime (i - j) n) :
    (S.filter (fun x => x ^ i - c * x ^ j = 0)).card ≤ 1 := by
  simpa [hcop.gcd_eq_one] using
    binomial_incidence_card_le_gcd_unpunctured S c hn hij hSn

end ArkLib.ProximityGap.C71BinomialIncidenceGcd

/-! ## Axiom audit -/
namespace ArkLib.ProximityGap.C71BinomialIncidenceGcd

#print axioms pow_gcd_of_pow_eq_of_pow_n
#print axioms binomial_incidence_card_le_gcd
#print axioms binomial_incidence_card_le_gcd_unpunctured
#print axioms binomial_incidence_card_le_one_of_coprime
#print axioms binomial_incidence_card_le_one_of_coprime_unpunctured

end ArkLib.ProximityGap.C71BinomialIncidenceGcd
