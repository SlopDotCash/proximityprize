/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Data.Finset.Card
import ArkLib.Data.CodingTheory.ProximityGap.C71BinomialIncidence

/-!
# Conjecture 7.1 residual: the NON-orbit incidence bound on the 3-term (trinomial) strata (#444)

## Ground-truth pivot context
The June-2026 literature pivot (commit `231b0ec9c`) relocated the prize to the ABOVE-JOHNSON
`O(1)/|F|` regime, which Chai-Fan 2026/861 reduces to **Conjecture 7.1**: the worst-case FRI
adversary direction is `<= 3`-sparse. `C71SparseOrbitGap` (route-B, `5dd3a409e`) shows the
worst-case `<= 3`-sparse adversary is **strictly multi-term** (`s23max = 9 > s1max = 8`), so it
ESCAPES the action-orbit eigenvector pin and receives NO `O(1)/|F|` orbit compression. The
named-open residual is a **non-orbit incidence bound on the 2- and 3-term strata** -- a
polynomial-method (root-count) argument, NOT an orbit count.

`C71BinomialIncidence` (`861dd47e5`) supplied the **2-term / binomial** strata (the gcd-sharp law
`#roots = gcd(|i-j|, n)`, the cyclic-kernel count, is `MultiplicativeRigidity.binomial_agree_card`).
It explicitly left the **3-term case OPEN**. This file supplies that 3-term case.

## What this file supplies (the 3-term / trinomial strata incidence bound)
A genuine **trinomial** direction over the thin domain `mu_n` is `f = X^i - c1 * X^j - c2 * X^k`
with `i > j > k` and `c1, c2 != 0`. Dividing the vanishing `f(x) = 0` by the unit `x^k` (`x` is a
nonzero element of `mu_n`) reduces it to the vanishing of the **dehomogenised** degree-`(i-k)`
trinomial
`g := X^(i-k) - C c1 * X^(j-k) - C c2`.
A `mu_n`-root `x` of `g` is *also* a root of `X^n - 1` (it lies in `mu_n`), so it is a **common**
root, hence a root of `gcd(X^n - 1, g)`. Distinct `mu_n`-roots therefore contribute distinct linear
factors of the gcd, giving the **NON-orbit, char-free, thickness-universal** incidence bound

> **`trinomial_incidence_card_le_gcd_natDegree`** :
>   `#{x in mu_n : x^i - c1 x^j - c2 x^k = 0} <= deg gcd(X^n - 1, X^(i-k) - C c1 X^(j-k) - C c2)`.

This is the SAME provable mechanism as the sibling `RepCountFiberGcdSharp` (common-root -> gcd
divisibility), applied to the route-B 3-term strata. It does NOT use the action-orbit count (so it
covers the multi-term worst case the orbit pin provably misses), and it adds no character-sum / BGK
content.

Probe `scripts/probes/probe_c71_trinomial_gcddeg.py` (reproducible, with `c1, c2` SAMPLED on a fixed
stride across `F_p^*` -- not an exhaustive enumeration of every coefficient pair) confirms over thin
`mu_n` `n = 2^a` at primes `p == 1 mod n`, `(p-1)/n >= 2` (NEVER `n = q-1`), `p` up to `40961`
(`16330` sampled nonzero-root configs), that this gcd-degree bound HOLDS in every sampled config, is
STRICTLY tighter than the bare degree bound `i - k` in `16256/16330` of them, and is EXACTLY equal
to the root count in ALL `16330/16330` of them (strong evidence it is the SHARP law; the proven
bound below is the `<=` direction, which holds unconditionally). A companion EXACT/exhaustive sweep
(`probe_c71_trinomial_gcdsum.py`, every genuine trinomial over all of `mu_n` plus a strided `F_p^*`
adversary) independently confirms the weaker `gcd(i-j,n)+gcd(j-k,n)` and `i-k` bounds hold with no
failures. The naive `union-of-binomials` decomposition (`R ⊆ B1 ∪ B2`) was probed and FAILS
(`probe_c71_trinomial_mechanism.py`) -- a generic trinomial root satisfies neither pairwise binomial
-- so the gcd route, not a union bound, is the correct provable mechanism.

## Theorems
* `trinomial_root_iff_dehom` : on the punctured domain (`x != 0`), `x` is a root of the trinomial
  direction `X^i - c1 X^j - c2 X^k` iff `x` is a root of the dehomogenised degree-`(i-k)` trinomial
  `g = X^(i-k) - C c1 X^(j-k) - C c2`. (The reduction that makes the orbit pin irrelevant.)
* `dvd_trinGcd_of_munRoot` : a `mu_n`-root of `g` divides `gcd(X^n - 1, g)`.
* `trinomial_incidence_card_le_gcd_natDegree` (HEADLINE) : the `mu_n`-incidence of the trinomial
  direction is at most `deg gcd(X^n - 1, dehomogenised g)` -- the SHARP non-orbit count.
* `trinGcd_natDegree_le` : `deg gcd(X^n - 1, g) <= i - k`, so the gcd bound is never weaker than the
  bare degree bound `i - k` (and per the probe is strictly sharper in the thin regime).

The residual reduction of the full 2- and 3-term-strata incidence to a soundness bound remains OPEN
and is NOT claimed here.

Axiom-clean (`propext, Classical.choice, Quot.sound`).
-/

open Finset Polynomial

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

namespace ArkLib.ProximityGap.C71TrinomialIncidence

variable {F : Type*} [Field F] [DecidableEq F]

/-- A positive-order root of unity in a field is nonzero. This packages the puncturing guard used
by the C71 trinomial incidence callers: on `μ_n` with `n > 0`, the condition `x ≠ 0` is automatic. -/
theorem ne_zero_of_pow_eq_one {n : ℕ} (hn : 0 < n) {x : F} (hx : x ^ n = 1) : x ≠ 0 := by
  intro hx0
  have hzero : x ^ n = 0 := by rw [hx0, zero_pow (Nat.ne_of_gt hn)]
  rw [hx] at hzero
  exact zero_ne_one hzero.symm

/-- The **dehomogenised trinomial-direction polynomial** of a genuine trinomial
`X^i - c1 X^j - c2 X^k` (`i > j > k`): divide by `X^k` to get the degree-`(i-k)` polynomial
`X^(i-k) - C c1 * X^(j-k) - C c2`. Its `mu_n`-roots are exactly the nonzero `mu_n`-roots of the
trinomial. -/
noncomputable def trinDirPoly (c1 c2 : F) (i j k : ℕ) : F[X] :=
  X ^ (i - k) - C c1 * X ^ (j - k) - C c2

/-- **The punctured-domain root reduction.** For a trinomial direction `X^i - c1 X^j - c2 X^k` with
`i >= j >= k`, a nonzero point `x` is a root iff it is a root of the dehomogenised `trinDirPoly`.
(Divide the vanishing `x^i - c1 x^j - c2 x^k = 0` by the nonzero `x^k`.) -/
theorem trinomial_root_iff_dehom (c1 c2 x : F) (hx : x ≠ 0) {i j k : ℕ}
    (hjk : k ≤ j) (hij : j ≤ i) :
    x ^ i - c1 * x ^ j - c2 * x ^ k = 0 ↔ (trinDirPoly c1 c2 i j k).eval x = 0 := by
  have hik : k ≤ i := le_trans hjk hij
  have hxk : x ^ k ≠ 0 := pow_ne_zero _ hx
  -- split the powers across X^k
  have hsi : x ^ (i - k) * x ^ k = x ^ i := by rw [← pow_add, Nat.sub_add_cancel hik]
  have hsj : x ^ (j - k) * x ^ k = x ^ j := by rw [← pow_add, Nat.sub_add_cancel hjk]
  simp only [trinDirPoly, eval_sub, eval_mul, eval_pow, eval_X, eval_C]
  constructor
  · intro h
    -- x^i - c1 x^j - c2 x^k = 0  ==>  (x^(i-k) - c1 x^(j-k) - c2) * x^k = 0
    have hfac : (x ^ (i - k) - c1 * x ^ (j - k) - c2) * x ^ k = 0 := by
      have : (x ^ (i - k) - c1 * x ^ (j - k) - c2) * x ^ k
          = x ^ i - c1 * x ^ j - c2 * x ^ k := by ring_nf; rw [hsi, hsj]; ring
      rw [this, h]
    exact (mul_eq_zero.mp hfac).resolve_right hxk
  · intro h
    -- (x^(i-k) - c1 x^(j-k) - c2) = 0  ==>  multiply by x^k
    have : (x ^ (i - k) - c1 * x ^ (j - k) - c2) * x ^ k
        = x ^ i - c1 * x ^ j - c2 * x ^ k := by ring_nf; rw [hsi, hsj]; ring
    rw [h, zero_mul] at this
    exact this.symm

/-- The `(i-k)`-th coefficient of the dehomogenised trinomial direction polynomial is `1`,
provided `j < i` (so `j - k < i - k`) and `k < i` (so `i - k > 0`): the leading power `X^(i-k)`
sits strictly above both lower terms `C c1 * X^(j-k)` and `C c2`. -/
theorem trinDirPoly_coeff_top (c1 c2 : F) {i j k : ℕ} (hjk : k ≤ j) (hji : j < i) (hik : k < i) :
    (trinDirPoly c1 c2 i j k).coeff (i - k) = 1 := by
  have hXpow : (X ^ (i - k) : F[X]).coeff (i - k) = 1 := by
    rw [coeff_X_pow, if_pos rfl]
  have h1 : (C c1 * X ^ (j - k)).coeff (i - k) = 0 := by
    rw [coeff_C_mul, coeff_X_pow, if_neg (by omega), mul_zero]
  have h2 : (C c2).coeff (i - k) = 0 := by
    rw [coeff_C, if_neg (by omega)]
  simp only [trinDirPoly, coeff_sub, hXpow, h1, h2, sub_zero]

/-- The dehomogenised trinomial direction polynomial is nonzero: its `(i-k)`-th coefficient is `1`
(`trinDirPoly_coeff_top`), so it is not the zero polynomial. -/
theorem trinDirPoly_ne_zero (c1 c2 : F) {i j k : ℕ} (hjk : k ≤ j) (hji : j < i) (hik : k < i) :
    trinDirPoly c1 c2 i j k ≠ 0 := by
  intro h
  have := trinDirPoly_coeff_top c1 c2 hjk hji hik
  rw [h, coeff_zero] at this
  exact one_ne_zero this.symm

/-- The dehomogenised trinomial direction polynomial has degree at most `i - k` (the leading
`X^(i-k)` is its top power). -/
theorem trinDirPoly_natDegree_le (c1 c2 : F) {i j k : ℕ} (hjk : k ≤ j) (hji : j < i) :
    (trinDirPoly c1 c2 i j k).natDegree ≤ i - k := by
  have hji' : j - k ≤ i - k := by omega
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · exact natDegree_X_pow_le (i - k)
    · calc (C c1 * X ^ (j - k)).natDegree ≤ (X ^ (j - k) : F[X]).natDegree := by
            simpa using natDegree_C_mul_le c1 (X ^ (j - k))
        _ ≤ j - k := natDegree_X_pow_le (j - k)
        _ ≤ i - k := hji'
  · simpa using (natDegree_C c2).le.trans (Nat.zero_le _)

/-- **A `mu_n`-root of the dehomogenised trinomial divides the gcd.** If `x ^ n = 1` and `x` is a
root of `trinDirPoly`, then `(X - C x)` divides `gcd (X ^ n - 1) (trinDirPoly ...)`: `x` is a common
root of `X^n - 1` and `g`. -/
theorem dvd_trinGcd_of_munRoot {n : ℕ} {x c1 c2 : F} {i j k : ℕ}
    (hxn : x ^ n = 1) (hroot : (trinDirPoly c1 c2 i j k).eval x = 0) :
    (X - C x) ∣ gcd (X ^ n - 1 : F[X]) (trinDirPoly c1 c2 i j k) := by
  have hr1 : (X ^ n - 1 : F[X]).IsRoot x := by
    simp [Polynomial.IsRoot.def, hxn]
  have hr2 : (trinDirPoly c1 c2 i j k).IsRoot x := hroot
  exact dvd_gcd (Polynomial.dvd_iff_isRoot.mpr hr1) (Polynomial.dvd_iff_isRoot.mpr hr2)

/-- **The trinomial-direction `mu_n`-incidence injects into the roots of the gcd.** The nonzero
`mu_n`-points at which the trinomial direction `X^i - c1 X^j - c2 X^k` vanishes are a subset of the
root set of `gcd (X^n - 1) (trinDirPoly ...)` -- a strictly sharper, NON-orbit container. -/
theorem trinomial_incidence_subset_gcd_roots {n : ℕ} (S : Finset F) (c1 c2 : F) {i j k : ℕ}
    (hjk : k ≤ j) (hji : j < i) (hik : k < i)
    (hSn : ∀ x ∈ S, x ^ n = 1) :
    (S.filter (fun x => x ≠ 0 ∧ x ^ i - c1 * x ^ j - c2 * x ^ k = 0))
      ⊆ (gcd (X ^ n - 1 : F[X]) (trinDirPoly c1 c2 i j k)).roots.toFinset := by
  have hgne : gcd (X ^ n - 1 : F[X]) (trinDirPoly c1 c2 i j k) ≠ 0 := by
    intro h
    rw [_root_.gcd_eq_zero_iff] at h
    exact trinDirPoly_ne_zero c1 c2 hjk hji hik h.2
  intro x hx
  rw [mem_filter] at hx
  obtain ⟨hxS, hxne, hvanish⟩ := hx
  have hxn : x ^ n = 1 := hSn x hxS
  have hdehom : (trinDirPoly c1 c2 i j k).eval x = 0 :=
    (trinomial_root_iff_dehom c1 c2 x hxne hjk (le_of_lt hji)).mp hvanish
  rw [Multiset.mem_toFinset, Polynomial.mem_roots hgne]
  exact Polynomial.dvd_iff_isRoot.mp (dvd_trinGcd_of_munRoot hxn hdehom)

/-- **The trinomial-direction `mu_n`-incidence gcd bound (NON-orbit, headline).** For any finite
set `S ⊆ F` whose elements satisfy `x ^ n = 1` (e.g. `S = mu_n`), the count of NONZERO points of
`S` at which the genuine trinomial direction `X^i - c1 X^j - c2 X^k` (`i > j > k`) vanishes is at
most `deg gcd (X^n - 1) (X^(i-k) - C c1 X^(j-k) - C c2)`. This is a polynomial-method
(common-root / gcd-divisibility) count requiring NO dilation-eigenvector (orbit) hypothesis, hence
covering the route-B multi-term worst case (`C71SparseOrbitGap`) that the action-orbit `O(1)/|F|`
pin provably misses. It mirrors the sibling `RepCountFiberGcdSharp` mechanism for the 3-term strata,
and (per `probe_c71_trinomial_gcddeg.py`) is the SHARP law (equal to the root count in all probed
configs). -/
theorem trinomial_incidence_card_le_gcd_natDegree {n : ℕ} (S : Finset F) (c1 c2 : F) {i j k : ℕ}
    (hjk : k ≤ j) (hji : j < i) (hik : k < i)
    (hSn : ∀ x ∈ S, x ^ n = 1) :
    (S.filter (fun x => x ≠ 0 ∧ x ^ i - c1 * x ^ j - c2 * x ^ k = 0)).card
      ≤ (gcd (X ^ n - 1 : F[X]) (trinDirPoly c1 c2 i j k)).natDegree := by
  calc (S.filter (fun x => x ≠ 0 ∧ x ^ i - c1 * x ^ j - c2 * x ^ k = 0)).card
      ≤ (gcd (X ^ n - 1 : F[X]) (trinDirPoly c1 c2 i j k)).roots.toFinset.card :=
        Finset.card_le_card (trinomial_incidence_subset_gcd_roots S c1 c2 hjk hji hik hSn)
    _ ≤ Multiset.card (gcd (X ^ n - 1 : F[X]) (trinDirPoly c1 c2 i j k)).roots :=
        (gcd (X ^ n - 1 : F[X]) (trinDirPoly c1 c2 i j k)).roots.toFinset_card_le
    _ ≤ (gcd (X ^ n - 1 : F[X]) (trinDirPoly c1 c2 i j k)).natDegree :=
        Polynomial.card_roots' _

/-- **The gcd bound refines the bare degree bound `i - k`.** `deg gcd(X^n-1, g) <= i - k`, so the
trinomial gcd incidence bound is never weaker than the elementary degree-`(i-k)` count, and (per
the probe) is strictly sharper in the thin regime (`16256/16330` configs). -/
theorem trinGcd_natDegree_le {n : ℕ} (c1 c2 : F) {i j k : ℕ} (hjk : k ≤ j) (hji : j < i) :
    (gcd (X ^ n - 1 : F[X]) (trinDirPoly c1 c2 i j k)).natDegree ≤ i - k := by
  have hik : k < i := lt_of_le_of_lt hjk hji
  have hgne : trinDirPoly c1 c2 i j k ≠ 0 := trinDirPoly_ne_zero c1 c2 hjk hji hik
  have hdvd : gcd (X ^ n - 1 : F[X]) (trinDirPoly c1 c2 i j k) ∣ trinDirPoly c1 c2 i j k :=
    gcd_dvd_right _ _
  calc (gcd (X ^ n - 1 : F[X]) (trinDirPoly c1 c2 i j k)).natDegree
      ≤ (trinDirPoly c1 c2 i j k).natDegree := Polynomial.natDegree_le_of_dvd hdvd hgne
    _ ≤ i - k := trinDirPoly_natDegree_le c1 c2 hjk hji

/-- **Unpunctured gcd-degree incidence bound.** If `n > 0`, every point of `S ⊆ μ_n` is
nonzero, so the sharp gcd-degree container applies to the ordinary trinomial vanishing-incidence
set without an explicit puncturing predicate. -/
theorem trinomial_incidence_card_le_gcd_natDegree_unpunctured {n : ℕ} (S : Finset F) (c1 c2 : F)
    {i j k : ℕ} (hn : 0 < n) (hjk : k ≤ j) (hji : j < i) (hik : k < i)
    (hSn : ∀ x ∈ S, x ^ n = 1) :
    (S.filter (fun x => x ^ i - c1 * x ^ j - c2 * x ^ k = 0)).card
      ≤ (gcd (X ^ n - 1 : F[X]) (trinDirPoly c1 c2 i j k)).natDegree := by
  have hsubset :
      (S.filter (fun x => x ^ i - c1 * x ^ j - c2 * x ^ k = 0))
        ⊆ (S.filter (fun x => x ≠ 0 ∧ x ^ i - c1 * x ^ j - c2 * x ^ k = 0)) := by
    intro x hx
    rw [mem_filter] at hx ⊢
    obtain ⟨hxS, hvanish⟩ := hx
    refine ⟨hxS, ?_, hvanish⟩
    intro hx0
    have hzero : x ^ n = 0 := by rw [hx0, zero_pow (Nat.ne_of_gt hn)]
    rw [hSn x hxS] at hzero
    exact zero_ne_one hzero.symm
  exact (Finset.card_le_card hsubset).trans
    (trinomial_incidence_card_le_gcd_natDegree S c1 c2 hjk hji hik hSn)

/-- **Puncturing is exactly redundant on `μ_n` when `n > 0`.** The nonzero guard in the
trinomial incidence set is not merely harmless for cardinal bounds: over any finite `S ⊆ μ_n`, the
punctured and unpunctured vanishing filters are equal. This packages the precise subset/equality
relation behind the caller-facing C71 unpunctured incidence lemmas. -/
theorem trinomial_incidence_filter_punctured_eq_unpunctured {n : ℕ} (S : Finset F) (c1 c2 : F)
    {i j k : ℕ} (hn : 0 < n) (hSn : ∀ x ∈ S, x ^ n = 1) :
    S.filter (fun x => x ≠ 0 ∧ x ^ i - c1 * x ^ j - c2 * x ^ k = 0)
      = S.filter (fun x => x ^ i - c1 * x ^ j - c2 * x ^ k = 0) := by
  ext x
  simp only [mem_filter]
  constructor
  · intro hx
    exact ⟨hx.1, hx.2.2⟩
  · intro hx
    exact ⟨hx.1, ne_zero_of_pow_eq_one hn (hSn x hx.1), hx.2⟩

/-- Cardinal form of `trinomial_incidence_filter_punctured_eq_unpunctured`: on positive-order
`μ_n`, adding the nonzero guard to a trinomial vanishing-incidence set does not change its size. -/
theorem trinomial_incidence_card_punctured_eq_unpunctured {n : ℕ} (S : Finset F) (c1 c2 : F)
    {i j k : ℕ} (hn : 0 < n) (hSn : ∀ x ∈ S, x ^ n = 1) :
    (S.filter (fun x => x ≠ 0 ∧ x ^ i - c1 * x ^ j - c2 * x ^ k = 0)).card
      = (S.filter (fun x => x ^ i - c1 * x ^ j - c2 * x ^ k = 0)).card := by
  rw [trinomial_incidence_filter_punctured_eq_unpunctured S c1 c2 hn hSn]

/-- **The caller-facing bare span cap for the 3-term strata.** The sharp gcd container above
immediately implies the robust polynomial-method fallback bound: a genuine trinomial direction of
span `i-k` has at most `i-k` nonzero incidences on any finite `S ⊆ μ_n`. This is the exact bound
that survives after the cyclotomic-divisor analogs for trinomials fail: it is NON-orbit, char-free,
and makes no sparsity-by-term-count claim. -/
theorem trinomial_incidence_card_le_span {n : ℕ} (S : Finset F) (c1 c2 : F) {i j k : ℕ}
    (hjk : k ≤ j) (hji : j < i) (hik : k < i)
    (hSn : ∀ x ∈ S, x ^ n = 1) :
    (S.filter (fun x => x ≠ 0 ∧ x ^ i - c1 * x ^ j - c2 * x ^ k = 0)).card ≤ i - k := by
  calc
    (S.filter (fun x => x ≠ 0 ∧ x ^ i - c1 * x ^ j - c2 * x ^ k = 0)).card
        ≤ (gcd (X ^ n - 1 : F[X]) (trinDirPoly c1 c2 i j k)).natDegree :=
          trinomial_incidence_card_le_gcd_natDegree S c1 c2 hjk hji hik hSn
    _ ≤ i - k := trinGcd_natDegree_le c1 c2 hjk hji


/-- **Caller-facing span cap without a puncturing predicate.** If `n > 0`, every point of a finite
`S ⊆ μ_n` is automatically nonzero, so the trinomial span cap applies directly to the ordinary
vanishing-incidence set. This packages the common `μ_n` nonzero guard for downstream C71 callers. -/
theorem trinomial_incidence_card_le_span_unpunctured {n : ℕ} (S : Finset F) (c1 c2 : F)
    {i j k : ℕ} (hn : 0 < n) (hjk : k ≤ j) (hji : j < i) (hik : k < i)
    (hSn : ∀ x ∈ S, x ^ n = 1) :
    (S.filter (fun x => x ^ i - c1 * x ^ j - c2 * x ^ k = 0)).card ≤ i - k := by
  have hsubset :
      (S.filter (fun x => x ^ i - c1 * x ^ j - c2 * x ^ k = 0))
        ⊆ (S.filter (fun x => x ≠ 0 ∧ x ^ i - c1 * x ^ j - c2 * x ^ k = 0)) := by
    intro x hx
    rw [mem_filter] at hx ⊢
    obtain ⟨hxS, hvanish⟩ := hx
    refine ⟨hxS, ?_, hvanish⟩
    intro hx0
    have hzero : x ^ n = 0 := by rw [hx0, zero_pow (Nat.ne_of_gt hn)]
    rw [hSn x hxS] at hzero
    exact zero_ne_one hzero.symm
  exact (Finset.card_le_card hsubset).trans
    (trinomial_incidence_card_le_span S c1 c2 hjk hji hik hSn)

end ArkLib.ProximityGap.C71TrinomialIncidence

/-! ## Axiom audit -/
namespace ArkLib.ProximityGap.C71TrinomialIncidence

#print axioms ne_zero_of_pow_eq_one
#print axioms trinomial_root_iff_dehom
#print axioms trinDirPoly_ne_zero
#print axioms trinomial_incidence_card_le_gcd_natDegree
#print axioms trinGcd_natDegree_le
#print axioms trinomial_incidence_card_le_span
#print axioms trinomial_incidence_filter_punctured_eq_unpunctured
#print axioms trinomial_incidence_card_punctured_eq_unpunctured
#print axioms trinomial_incidence_card_le_gcd_natDegree_unpunctured
#print axioms trinomial_incidence_card_le_span_unpunctured

end ArkLib.ProximityGap.C71TrinomialIncidence
