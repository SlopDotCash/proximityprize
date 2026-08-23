/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic

/-!
# The divisor-counting list bound (#389, the char-0-cyclotomic route)

For a word `w` (as a polynomial) on the smooth domain `μ_n = {x : xⁿ = 1}`, the agreement
of a degree-`<k` codeword `c` with `w` is `deg gcd(w − c, Xⁿ − 1)` (the number of common
roots).  This file lands the **structural heart** of the divisor route to the past-Johnson
list:

> **`gcd_injOn_aux`** — on the list `{c : deg c < k, deg gcd(w−c, Z) ≥ a}` with `a ≥ k`,
> the map `c ↦ gcd(w−c, Z)` is **injective**: two such codewords share a gcd `D` of degree
> `≥ a > deg(c−c')`, and `D ∣ (c−c')` forces `c = c'`.

> **`list_card_le_gcdImage`** — consequently the list injects into the divisors of `Z` it
> produces: `|list| = |image of c ↦ gcd(w−c, Z)|`, and every image element divides `Z`
> with degree `≥ a`.  Hence

>   `|list| ≤ #{monic divisors D of Z : deg D ≥ a}`.

**Why this is the right route, and why it is hard.** Over `ℚ`, `Z = Xⁿ − 1 = ∏_{d∣n} Φ_d`
has only `O(log n)` cyclotomic factors, so `O(n)` divisors total — a *polynomial* list,
the whole conjecture, for free.  Over the deployed split field `F_q` (`n ∣ q−1`), `Z`
splits into `n` linear factors, giving `2ⁿ` divisors — the bound goes vacuous.  The
past-Johnson wall is *exactly* this gap: the divisor count is poly in characteristic zero
and exponential over the split field, and bridging them requires controlling which
divisors actually carry a low-degree residue of `w` — the open `CensusDomination` content.
This file proves the route's injective backbone unconditionally; the divisor *count* over
`F_q` is the open core.  Issue #389.
-/

open Polynomial EuclideanDomain

namespace ProximityGap.DivisorList

variable {F : Type*} [Field F] [DecidableEq F]

/-- **The list-decoding gcd is injective on low-degree codewords.**  Two degree-`<k`
codewords whose shifted gcds with `Z` agree, when that gcd reaches degree `≥ a ≥ k`, are
equal: `D := gcd(w−c, Z) = gcd(w−c', Z)` divides `c'−c`, whose degree is `< k ≤ a ≤ deg D`,
forcing `c' − c = 0`. -/
theorem gcd_injOn_aux (Z w : F[X]) {k a : ℕ} (hka : k ≤ a)
    {c c' : F[X]} (hc : c.degree < (k : ℕ)) (hc' : c'.degree < (k : ℕ))
    (ha : a ≤ (EuclideanDomain.gcd (w - c) Z).natDegree)
    (hgcd : EuclideanDomain.gcd (w - c) Z = EuclideanDomain.gcd (w - c') Z) :
    c = c' := by
  set D := EuclideanDomain.gcd (w - c) Z with hD
  have hDc : D ∣ (w - c) := gcd_dvd_left _ _
  have hDc' : D ∣ (w - c') := hgcd ▸ gcd_dvd_left (w - c') Z
  have hDdiff : D ∣ (c' - c) := by
    have hrw : (w - c) - (w - c') = c' - c := by ring
    rw [← hrw]; exact dvd_sub hDc hDc'
  by_contra hne
  have hdiff0 : c' - c ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have h1 : D.natDegree ≤ (c' - c).natDegree := natDegree_le_of_dvd hDdiff hdiff0
  have h2 : (c' - c).natDegree < k :=
    (natDegree_lt_iff_degree_lt hdiff0).mpr
      (lt_of_le_of_lt (degree_sub_le _ _) (max_lt hc' hc))
  omega

open Classical in
/-- **The divisor-counting list bound.**  The list of degree-`<k` codewords with shifted
gcd of degree `≥ a ≥ k` has cardinality equal to its gcd-image, every element of which is
a divisor of `Z` of degree `≥ a`.  In particular it is at most the number of such divisors
of `Z`. -/
theorem list_card_le_gcdImage (Z w : F[X]) {k a : ℕ} (hka : k ≤ a)
    (L : Finset F[X])
    (hL : ∀ c ∈ L, c.degree < (k : ℕ) ∧ a ≤ (EuclideanDomain.gcd (w - c) Z).natDegree) :
    L.card = (L.image (fun c => EuclideanDomain.gcd (w - c) Z)).card
      ∧ (∀ c ∈ L, EuclideanDomain.gcd (w - c) Z ∣ Z
          ∧ a ≤ (EuclideanDomain.gcd (w - c) Z).natDegree) := by
  refine ⟨(Finset.card_image_of_injOn ?_).symm, fun c hc => ⟨gcd_dvd_right _ _, (hL c hc).2⟩⟩
  intro c hc c' hc' he
  exact gcd_injOn_aux Z w hka (hL c hc).1 (hL c' hc').1 (hL c hc).2 he

end ProximityGap.DivisorList

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.DivisorList.gcd_injOn_aux
#print axioms ProximityGap.DivisorList.list_card_le_gcdImage
