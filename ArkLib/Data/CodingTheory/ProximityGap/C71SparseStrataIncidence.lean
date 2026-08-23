/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Roots
import ArkLib.Data.CodingTheory.ProximityGap.C71TrinomialIncidence

/-!
# Conjecture 7.1 residual: the GENERAL `m`-sparse strata `μ_n`-incidence gcd bound (#444)

## Ground-truth pivot context
The June-2026 pivot (`231b0ec9c`) relocated the prize to the ABOVE-JOHNSON `O(1)/|F|` regime, which
Chai-Fan 2026/861 reduces to **Conjecture 7.1**: the worst-case FRI adversary direction is
`<= 3`-sparse. `C71SparseOrbitGap` (`5dd3a409e`) showed the worst case is **strictly multi-term**, so
it escapes the action-orbit eigenvector pin and the residual is a **non-orbit incidence bound on the
sparse strata** (a polynomial-method root count, not an orbit count). The binomial
(`C71BinomialIncidence` `861dd47e5`, `C71BinomialIncidenceGcd` `d9615d195`) and trinomial
(`C71TrinomialIncidence`) cases were landed term-by-term.

## What this file supplies (the UNIFORM mechanism)
The gcd-divisibility mechanism behind every one of those bricks is **`m`-uniform** -- it never used
the number of terms. This file isolates the single general lemma, stated for an **arbitrary**
direction polynomial `g` over a domain whose elements satisfy `x^n = 1`:

> **`munRoot_card_le_gcd_natDegree`** : for a finite set `S` with `∀ x ∈ S, x ^ n = 1`, the count of
> NONZERO points of `S` that are roots of any polynomial `g ≠ 0` is at most
> `deg gcd(X^n - 1, g)`.

A point `x ∈ S` that is a root of `g` is a *common* root of `X^n - 1` and `g`, hence a root of their
gcd; distinct roots inject into the gcd's root multiset. This is the NON-orbit, char-free,
thickness-universal count covering the route-B multi-term worst case the action-orbit `O(1)/|F|` pin
provably misses. The binomial (`#roots ≤ gcd(i-j, n)`) and trinomial
(`#roots ≤ deg gcd(X^n-1, X^(i-k) - C c1 X^(j-k) - C c2)`) incidence bounds are now both **instances**
of this one lemma (see `trinomial_incidence_card_le_gcd_general`).

Probe `scripts/probes/probe_c71_msparse_incidence.py` (reproducible, strided/sampled `F_p^*`
coefficients over thin `μ_n`, `n = 2^a`, `p == 1 mod n`, NEVER `n = q-1`) confirms the gcd-degree
bound HOLDS and is EXACTLY sharp (= the root count) in 100% of sampled configs for `m = 2, 3, 4`
(`428/428`, `2642/2642`, `36204/36204`), and is strictly tighter than the bare degree bound in nearly
all of them -- i.e. the `m`-uniform law is the sharp count for every small sparsity, not just `m ≤ 3`.

## Honest scope
This is the uniform polynomial-method **incidence count** for the sparse strata. The reduction of
that strata-incidence to a FRI **soundness** bound (the actual Conjecture-7.1 content) remains OPEN
and is NOT claimed here. This is NOT a CORE / Conj-7.1 closure.

Axiom-clean (`propext, Classical.choice, Quot.sound`).
-/

open Finset Polynomial

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

namespace ArkLib.ProximityGap.C71SparseStrataIncidence

variable {F : Type*} [Field F] [DecidableEq F]

/-- **A `μ_n`-root of `g` divides `gcd(X^n - 1, g)`.** If `x ^ n = 1` and `g.IsRoot x`, then
`(X - C x)` divides `gcd(X^n - 1, g)`: `x` is a common root of `X^n - 1` and `g`. (The uniform core
of every sparse-strata incidence brick.) -/
theorem dvd_munGcd_of_munRoot {n : ℕ} {x : F} {g : F[X]}
    (hxn : x ^ n = 1) (hroot : g.IsRoot x) :
    (X - C x) ∣ gcd (X ^ n - 1 : F[X]) g := by
  have hr1 : (X ^ n - 1 : F[X]).IsRoot x := by simp [Polynomial.IsRoot.def, hxn]
  exact dvd_gcd (Polynomial.dvd_iff_isRoot.mpr hr1) (Polynomial.dvd_iff_isRoot.mpr hroot)

/-- **The `μ_n`-incidence of any direction polynomial injects into the roots of the gcd.** The
nonzero points of `S` (where `∀ x ∈ S, x ^ n = 1`) that are roots of `g ≠ 0` are a subset of the
root set of `gcd(X^n - 1, g)`. -/
theorem munRoot_subset_gcd_roots {n : ℕ} (S : Finset F) {g : F[X]} (hg : g ≠ 0)
    (hSn : ∀ x ∈ S, x ^ n = 1) :
    (S.filter (fun x => x ≠ 0 ∧ g.IsRoot x)) ⊆ (gcd (X ^ n - 1 : F[X]) g).roots.toFinset := by
  have hgne : gcd (X ^ n - 1 : F[X]) g ≠ 0 := by
    intro h; rw [_root_.gcd_eq_zero_iff] at h; exact hg h.2
  intro x hx
  rw [mem_filter] at hx
  obtain ⟨hxS, _, hroot⟩ := hx
  rw [Multiset.mem_toFinset, Polynomial.mem_roots hgne]
  exact Polynomial.dvd_iff_isRoot.mp (dvd_munGcd_of_munRoot (hSn x hxS) hroot)

/-- **The general `m`-sparse strata `μ_n`-incidence gcd bound (NON-orbit, headline).** For any
finite set `S ⊆ F` whose elements satisfy `x ^ n = 1` (e.g. `S = μ_n`), the count of NONZERO points
of `S` that are roots of any direction polynomial `g ≠ 0` is at most `deg gcd(X^n - 1, g)`. A
polynomial-method (common-root / gcd-divisibility) count requiring NO dilation-eigenvector (orbit)
hypothesis -- the UNIFORM mechanism behind the binomial and trinomial strata bricks. -/
theorem munRoot_card_le_gcd_natDegree {n : ℕ} (S : Finset F) {g : F[X]} (hg : g ≠ 0)
    (hSn : ∀ x ∈ S, x ^ n = 1) :
    (S.filter (fun x => x ≠ 0 ∧ g.IsRoot x)).card ≤ (gcd (X ^ n - 1 : F[X]) g).natDegree := by
  calc (S.filter (fun x => x ≠ 0 ∧ g.IsRoot x)).card
      ≤ (gcd (X ^ n - 1 : F[X]) g).roots.toFinset.card :=
        Finset.card_le_card (munRoot_subset_gcd_roots S hg hSn)
    _ ≤ Multiset.card (gcd (X ^ n - 1 : F[X]) g).roots :=
        (gcd (X ^ n - 1 : F[X]) g).roots.toFinset_card_le
    _ ≤ (gcd (X ^ n - 1 : F[X]) g).natDegree := Polynomial.card_roots' _

/-- **The trinomial incidence bound is an instance of the general lemma.** Re-deriving
`C71TrinomialIncidence.trinomial_incidence_card_le_gcd_natDegree` from the uniform
`munRoot_card_le_gcd_natDegree` with `g = trinDirPoly`, exhibiting it as the `m = 3` special case. -/
theorem trinomial_incidence_card_le_gcd_general {n : ℕ} (S : Finset F) (c1 c2 : F) {i j k : ℕ}
    (hjk : k ≤ j) (hji : j < i) (hik : k < i) (hSn : ∀ x ∈ S, x ^ n = 1) :
    (S.filter (fun x => x ≠ 0 ∧ x ^ i - c1 * x ^ j - c2 * x ^ k = 0)).card
      ≤ (gcd (X ^ n - 1 : F[X])
          (ArkLib.ProximityGap.C71TrinomialIncidence.trinDirPoly c1 c2 i j k)).natDegree := by
  set g := ArkLib.ProximityGap.C71TrinomialIncidence.trinDirPoly c1 c2 i j k with hgdef
  have hg : g ≠ 0 :=
    ArkLib.ProximityGap.C71TrinomialIncidence.trinDirPoly_ne_zero c1 c2 hjk hji hik
  -- rewrite the trinomial-vanishing predicate to `g.IsRoot x` on the nonzero domain
  have hfilter : (S.filter (fun x => x ≠ 0 ∧ x ^ i - c1 * x ^ j - c2 * x ^ k = 0))
      = (S.filter (fun x => x ≠ 0 ∧ g.IsRoot x)) := by
    apply Finset.filter_congr
    intro x _
    constructor
    · rintro ⟨hxne, hv⟩
      exact ⟨hxne, (ArkLib.ProximityGap.C71TrinomialIncidence.trinomial_root_iff_dehom
        c1 c2 x hxne hjk (le_of_lt hji)).mp hv⟩
    · rintro ⟨hxne, hr⟩
      exact ⟨hxne, (ArkLib.ProximityGap.C71TrinomialIncidence.trinomial_root_iff_dehom
        c1 c2 x hxne hjk (le_of_lt hji)).mpr hr⟩
  rw [hfilter]
  exact munRoot_card_le_gcd_natDegree S hg hSn

end ArkLib.ProximityGap.C71SparseStrataIncidence

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.C71SparseStrataIncidence.dvd_munGcd_of_munRoot
#print axioms ArkLib.ProximityGap.C71SparseStrataIncidence.munRoot_card_le_gcd_natDegree
#print axioms ArkLib.ProximityGap.C71SparseStrataIncidence.trinomial_incidence_card_le_gcd_general
