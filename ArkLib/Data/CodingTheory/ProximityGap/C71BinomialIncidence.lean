/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Finset.Card
import ArkLib.Data.CodingTheory.ProximityGap.C71SparseOrbitGap

/-!
# Conjecture 7.1 residual: the NON-orbit incidence bound on the binomial (2-term) strata (#444)

## Ground-truth pivot context
The June-2026 literature pivot (commit `231b0ec9c`) relocated the prize to the ABOVE-JOHNSON
`O(1)/|F|` regime, which Chai-Fan 2026/861 reduces to **Conjecture 7.1**: the worst-case FRI
adversary direction is `<= 3`-sparse. `ActionOrbitGeneralF.eigen_forces_monomial` PINS that the
per-line `gamma`-orbit `O(1)/|F|` compression is *eigenvector-gated*, hence **monomial-only**
(1-sparse). `C71SparseOrbitGap` (the route-B brick, `5dd3a409e`) shows the worst-case `<= 3`-sparse
adversary is **strictly multi-term** (`s23max = 9 > s1max = 8`), so it ESCAPES the orbit pin: its
bad set is not a union of `gamma`-orbits and receives no `O(1)/|F|` orbit compression. The
named-open residual is therefore a **non-orbit incidence bound on the 2- and 3-term strata**
-- a polynomial-method (root-count) argument, NOT an orbit count.

## What this file supplies (the first concrete residual brick: the 2-term / binomial strata)
A genuine **binomial** direction over the thin domain `mu_n` is `f = X^i - c * X^j` with `i > j` and
`c != 0`. Its `mu_n`-incidence (the count of domain points where the direction vanishes, which feeds
the line-incidence `I` of `IncidencePeriodBridge`) is governed NOT by an orbit count but by the
**binomial root-count law**: on the multiplicative group a point `x != 0` is a root iff
`x^(i-j) = c`, so the nonzero roots inject into the `(i-j)`-th roots of `c`, of which there are at
most `i - j` (`Polynomial.card_nthRoots`). This is a NON-orbit, field- and thickness-universal,
char-free polynomial-method count -- it covers exactly the route-B multi-term worst case that the
action-orbit pin provably misses.

Probe `scripts/probes/probe_c71_multiterm_incidence_rootcap.py` (EXACT, reproducible, 8/8 over thin
`mu_n` `n = 2^a`, multi-prime incl `p > n^3` and Fermat `257`, NEVER `n = q-1`) confirms the SHARP
form `#roots(X^i - c X^j in mu_n) <= gcd(|i-j|, n)` and the 2-sparse `mult < 2` law. We formalize
the robust `<= (i-j)` Mathlib-backed bound (the polynomial-method count; the `gcd`-tight refinement
needs the cyclic-kernel order and is left for a follow-on).

## Theorems
* `binomial_root_iff_pow_eq` : on the punctured domain (`x != 0`), `x` is a root of the binomial
  direction `X^i - c * X^j` iff `x^(i-j) = c`. (The reduction that makes it a pure power equation.)
* `binomial_incidence_card_le` (HEADLINE) : the count of nonzero points of any finite set `S` at
  which the binomial direction vanishes is at most `i - j`. With `S = mu_n` this is the binomial
  direction's `mu_n`-incidence bound -- a NON-orbit (no dilation-eigenvector hypothesis) count that
  covers the route-B multi-term worst case the action-orbit pin misses.

These EXTEND the polynomial-method toolset (`Polynomial.card_nthRoots`) and the `C71SparseOrbitGap`
route-B localization; they add no character-sum / BGK content. The residual reduction of the full
2- and 3-term-strata incidence to a soundness bound, and the `3`-term case, remain OPEN and are NOT
claimed here.

Axiom-clean (`propext, Classical.choice, Quot.sound`).
-/

open Finset Polynomial

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

namespace ArkLib.ProximityGap.C71BinomialIncidence

variable {F : Type*} [Field F] [DecidableEq F]

/-- A positive-order root of unity in a field is nonzero. This is the binomial-strata version of
the puncturing guard: on `μ_n` with `n > 0`, the condition `x ≠ 0` is automatic. -/
theorem ne_zero_of_pow_eq_one {n : ℕ} (hn : 0 < n) {x : F} (hx : x ^ n = 1) : x ≠ 0 := by
  intro hx0
  have hzero : x ^ n = 0 := by rw [hx0, zero_pow (Nat.ne_of_gt hn)]
  rw [hx] at hzero
  exact zero_ne_one hzero.symm

/-- **The punctured-domain root reduction.** For a binomial direction `X^i - c * X^j` with `i >= j`,
a nonzero point `x` is a root iff `x ^ (i - j) = c`. (Divide the vanishing `x^i = c * x^j` by the
nonzero `x^j`.) -/
theorem binomial_root_iff_pow_eq (c x : F) (hx : x ≠ 0) {i j : ℕ} (hij : j ≤ i) :
    x ^ i - c * x ^ j = 0 ↔ x ^ (i - j) = c := by
  have hxj : x ^ j ≠ 0 := pow_ne_zero _ hx
  rw [sub_eq_zero]
  constructor
  · intro h
    -- x^i = c * x^j, and x^i = x^(i-j) * x^j, cancel x^j.
    have hsplit : x ^ (i - j) * x ^ j = x ^ i := by
      rw [← pow_add, Nat.sub_add_cancel hij]
    have : x ^ (i - j) * x ^ j = c * x ^ j := by rw [hsplit, h]
    exact mul_right_cancel₀ hxj this
  · intro h
    rw [← Nat.sub_add_cancel hij, pow_add, h]

/-- **The binomial-direction incidence bound (NON-orbit, headline).** For any finite set `S ⊆ F`,
the number of NONZERO points of `S` at which the binomial direction `X^i - c * X^j` (`i >= j`,
genuine: `i > j`) vanishes is at most `i - j`. With `S = mu_n` this is the binomial direction's
`mu_n`-incidence bound -- a polynomial-method (`nthRoots`) count requiring NO dilation-eigenvector
(orbit) hypothesis, hence covering the route-B multi-term worst case (`C71SparseOrbitGap`) that the
action-orbit `O(1)/|F|` pin provably misses. -/
theorem binomial_incidence_card_le (S : Finset F) (c : F) {i j : ℕ} (hij : j < i) :
    (S.filter (fun x => x ≠ 0 ∧ x ^ i - c * x ^ j = 0)).card ≤ i - j := by
  have hposd : 0 < i - j := Nat.sub_pos_of_lt hij
  have hjle : j ≤ i := le_of_lt hij
  -- map each qualifying nonzero root into the nthRoots multiset, injectively (Finset filter has
  -- no repeats), bounded by card (nthRoots (i-j) c) <= i - j.
  set T := S.filter (fun x => x ≠ 0 ∧ x ^ i - c * x ^ j = 0) with hT
  have hsub : T ⊆ (nthRoots (i - j) c).toFinset := by
    intro x hx
    rw [hT, mem_filter] at hx
    obtain ⟨_, hxne, hroot⟩ := hx
    rw [Multiset.mem_toFinset, mem_nthRoots hposd]
    exact (binomial_root_iff_pow_eq c x hxne hjle).mp hroot
  calc T.card ≤ (nthRoots (i - j) c).toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card (nthRoots (i - j) c) := Multiset.toFinset_card_le _
    _ ≤ i - j := card_nthRoots (i - j) c

/-- **Puncturing is exactly redundant for binomial strata on positive-order `μ_n`.** Over any
finite `S ⊆ μ_n`, the explicit nonzero guard in the binomial vanishing-incidence filter is equal
to the ordinary vanishing filter. -/
theorem binomial_incidence_filter_punctured_eq_unpunctured {n : ℕ} (S : Finset F) (c : F)
    {i j : ℕ} (hn : 0 < n) (hSn : ∀ x ∈ S, x ^ n = 1) :
    S.filter (fun x => x ≠ 0 ∧ x ^ i - c * x ^ j = 0)
      = S.filter (fun x => x ^ i - c * x ^ j = 0) := by
  ext x
  simp only [mem_filter]
  constructor
  · intro hx
    exact ⟨hx.1, hx.2.2⟩
  · intro hx
    exact ⟨hx.1, ne_zero_of_pow_eq_one hn (hSn x hx.1), hx.2⟩

/-- **Caller-facing binomial incidence bound without a puncturing predicate.** If `n > 0`, every
point of a finite `S ⊆ μ_n` is automatically nonzero, so the binomial non-orbit root count applies
directly to the ordinary vanishing-incidence set. -/
theorem binomial_incidence_card_le_unpunctured {n : ℕ} (S : Finset F) (c : F) {i j : ℕ}
    (hn : 0 < n) (hij : j < i) (hSn : ∀ x ∈ S, x ^ n = 1) :
    (S.filter (fun x => x ^ i - c * x ^ j = 0)).card ≤ i - j := by
  rw [← binomial_incidence_filter_punctured_eq_unpunctured S c hn hSn]
  exact binomial_incidence_card_le S c hij

end ArkLib.ProximityGap.C71BinomialIncidence

/-! ## Axiom audit -/
namespace ArkLib.ProximityGap.C71BinomialIncidence

#print axioms ne_zero_of_pow_eq_one
#print axioms binomial_root_iff_pow_eq
#print axioms binomial_incidence_card_le
#print axioms binomial_incidence_filter_punctured_eq_unpunctured
#print axioms binomial_incidence_card_le_unpunctured

end ArkLib.ProximityGap.C71BinomialIncidence
