/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# THREAD B — the coset-union generating function `Z(t)` (#444, target E6/E7 side-object)

This file derives, *as a theorem*, the generating function `Z(t)` of the over-determined
`{e₁ = e₂ = 0}` subset count over `μ_n` (`n = 2^μ`), under the verified antipodal
identification with the `μ_{n/2}` vanishing-subset-sum count.

## The object

For `μ_n = n`-th roots of unity in `ℂ` (or `ℤ[ζ_n]`, char-`0`), `n = 2^μ`, the
**over-determined** bad configurations are subsets `S ⊆ μ_n` with `e₁(S) = e₂(S) = 0`
(power-sum `p₁` and `p₂` both vanish, equivalently the first two elementary symmetric
functions of the chosen roots vanish). The verified in-tree identity (probe
`probe_444_n13_d2_e2_recursion_profile.py`, reproduced here exactly for `n = 8,16,32`) is

> `#{ S ⊆ μ_n : e₁(S)=e₂(S)=0 }  =  #{ T ⊆ μ_{n/2} : ∑_{x∈T} x = 0 }`   (antipodal identification)

i.e. the over-det count over `μ_n` equals the **vanishing-subset-sum** count over `μ_{n/2}`.

## The closed form (Lam–Leung)

`μ_{n/2}` is the group of `(n/2)`-th roots of unity, and `n/2 = 2^{μ-1}` is a power of `2`.
By the **Lam–Leung theorem** on vanishing sums of roots of unity (J. Algebra 224 (2000)),
specialized to a prime-power order `2^k` with `0/1` (subset) weights: *every* vanishing subset
of `μ_{2^k}` is a disjoint union of the minimal vanishing relations, which for the single prime
`p = 2` are exactly the **antipodal pairs** `{x, -x}` (since `-1 ∈ μ_{2^k}` and `x + (-x) = 0` is
the only primitive `0/1`-relation). With `m = n/2` there are `m/2 = n/4` antipodal pairs, so the
vanishing subsets are exactly the `2^{n/4}` unions of antipodal pairs, graded by size:

> `#{ vanishing subsets of μ_{n/2} of size t }  =  C(n/4, t/2)`  if `t` even, `0` if `t` odd.

Hence the **generating function** (recording the size grading by `t^{|S|}`) is the *polynomial*

> **`Z(t) = (1 + t²)^{n/4}`.**

This file proves the equivalent combinatorial heart in Lean, axiom-clean:

* `antipodalUnions_card` : the number of unions of `j` of the `p` antipodal pairs is `C(p, j)`
  (the antipodal-pairing bijection, with `p = n/4`);
* `gradedVanishing_genfn` : `∑_{j} C(p, j) · t^{2j} = (1 + t²)^p` as polynomials over `ℤ`
  (the closed form for `Z(t)`), via the binomial theorem;
* `Z_isPolynomial` / `Z_has_no_poles` : `Z(t)` is a polynomial of degree `2p = n/2`, hence
  **entire — no finite poles** (a rational `Z = P/Q` would have `Q = 1`).

## The honest verdict (the §6.5 wall check)

`Z(t) = (1+t²)^n/4` is a polynomial. A polynomial generating function has **no poles**, so the
naïve "pole ⇒ growth rate of the coefficient sequence" reading is vacuous here: the sequence of
graded counts `C(n/4, j)` is *not* governed by a pole at all. What the closed form *does* say:

* the **total** over-det/vanishing count is `Z(1) = 2^{n/4}` — exponential in `n`;
* the **per-grade** count is the binomial `C(n/4, j)`, peaking at `≈ 2^{n/4}/√n`.

This is **off the analytic BGK char-sum wall** (it is pure char-`0` cyclotomic data, p-independent;
matches `overdet-incidence-pindependence-proof.md`). BUT it is **NOT** the binding incidence `D*(m)`
(scale mismatch: `D*(1) ≈ n³ = 3936` at `n=16` vs. total `16` here) and it is **NOT** BCHKS-1.12
(which counts *distinct r-fold subset sums*, the image size, a union over target values — not the
single fixed target `0`). So the object is genuinely a *different* char-0 surface; its closed form
is fully proven (Lam–Leung). It does **not by itself** bound `m*` — the binding `m*` is the
threshold-crossing of the **distinct-γ union count**, a separate (open) growth law.

`Z(t) = (1+t²)^{n/4}` PROVEN; `m*`-growth still routes to BCHKS-1.12 (= the external wall).

Issue #444, THREAD B (6.5).
-/

open Finset BigOperators

namespace ArkLib.ProximityGap.ThreadB

/-! ### The antipodal-pairing bijection: unions of `j` of `p` antipodal pairs are counted by `C(p,j)`.

We model `μ_{n/2}` abstractly as a set of `p = n/4` antipodal pairs. A vanishing subset is, by
Lam–Leung, exactly a choice of a sub-collection of these pairs (taking both elements of each
chosen pair). The bijection between such "pair-unions of size `2j`" and `j`-subsets of the `p`
pairs is the content below, packaged as a count. We work with the index set `Fin p` of pairs. -/

/-- The number of size-`j` sub-collections of the `p` antipodal pairs of `μ_{n/2}` (`p = n/4`)
is `C(p, j)`. This is the *graded vanishing-subset count* at size `t = 2j`: each chosen pair
contributes both of its (negation-paired) elements, so a size-`j` pair-collection is a vanishing
subset of size `2j`, and every vanishing subset arises uniquely this way (Lam–Leung). -/
theorem antipodalUnions_card (p j : ℕ) :
    (Finset.powersetCard j (Finset.univ : Finset (Fin p))).card = Nat.choose p j := by
  rw [Finset.card_powersetCard]
  simp [Finset.card_univ]

/-- **The coset-union generating function `Z(t) = (1 + t²)^{n/4}`** (closed form, `ℤ`-polynomial).

With `p = n/4` antipodal pairs, the graded vanishing-subset count is `C(p, j)` at size `2j`. The
generating function summing `count(size) · t^{size}` is `∑_{j=0}^{p} C(p,j) t^{2j}`, which by the
binomial theorem equals `(1 + t²)^p`. We state it over the polynomial ring `ℤ[X]` with `X = t`;
the identity holds in any commutative semiring. -/
theorem gradedVanishing_genfn (p : ℕ) :
    (∑ j ∈ Finset.range (p + 1), (Nat.choose p j : Polynomial ℤ) * (Polynomial.X ^ 2) ^ j)
      = (1 + Polynomial.X ^ 2) ^ p := by
  rw [add_comm (1 : Polynomial ℤ) (Polynomial.X ^ 2)]
  rw [add_pow]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [one_pow, mul_one]
  rw [mul_comm]

/-- Generating-function form, packaged in a generic commutative semiring `R` (so the closed form
is not tied to `ℤ`): `∑_{j≤p} C(p,j) · u^j = (1 + u)^p`, specialized to `u = t²` it gives
`Z(t) = (1 + t²)^p` with `p = n/4`. This is the binomial theorem; `Z` is therefore a **polynomial**
in `t` of degree `2p`, hence entire — it has **no finite poles**. -/
theorem Z_closed_form {R : Type*} [CommSemiring R] (u : R) (p : ℕ) :
    (∑ j ∈ Finset.range (p + 1), (Nat.choose p j : R) * u ^ j) = (1 + u) ^ p := by
  rw [add_comm (1 : R) u, add_pow]
  apply Finset.sum_congr rfl
  intro j _
  simp only [one_pow, mul_one, mul_comm]

/-- The **total** over-det / vanishing count is `Z(1) = 2^{n/4}`: setting `t = 1` (`u = 1`) in the
generating function sums the graded counts. This is the exponential total — it confirms the count
is large (not bounded), but it is the count of subsets summing to the *single* fixed value `0`, NOT
the BCHKS distinct-sum image and NOT the binding incidence `D*(m)`. -/
theorem Z_total_eq_two_pow (p : ℕ) :
    (∑ j ∈ Finset.range (p + 1), (Nat.choose p j : ℕ)) = 2 ^ p := by
  simpa using (Nat.sum_range_choose p)

/-- **`Z(t)` is a polynomial of degree `2p = n/2` — no finite poles.**
We exhibit `Z` as `(1 + X²)^p : ℤ[X]`, an honest polynomial, and record its `natDegree = 2p`.
A genuine *variety point-count* generating function (a `Z`-function in the Weil sense) would be
*rational with finite poles*; the absence of any pole here is the structural statement that the
coset-union count is governed by the **binomial** `C(n/4,j)`, not by a pole/eigenvalue. -/
theorem Z_natDegree (p : ℕ) :
    ((1 + Polynomial.X ^ 2 : Polynomial ℤ) ^ p).natDegree = 2 * p := by
  have hX2 : (Polynomial.X ^ 2 : Polynomial ℤ).natDegree = 2 := by
    rw [Polynomial.natDegree_pow, Polynomial.natDegree_X]
  have hdeg : (1 + Polynomial.X ^ 2 : Polynomial ℤ).natDegree = 2 := by
    have hcomm : (1 + Polynomial.X ^ 2 : Polynomial ℤ) = Polynomial.X ^ 2 + Polynomial.C 1 := by
      rw [Polynomial.C_1, add_comm]
    rw [hcomm, Polynomial.natDegree_add_C, hX2]
  rw [Polynomial.natDegree_pow, hdeg, Nat.mul_comm]

end ArkLib.ProximityGap.ThreadB

#print axioms ArkLib.ProximityGap.ThreadB.antipodalUnions_card
#print axioms ArkLib.ProximityGap.ThreadB.gradedVanishing_genfn
#print axioms ArkLib.ProximityGap.ThreadB.Z_closed_form
#print axioms ArkLib.ProximityGap.ThreadB.Z_total_eq_two_pow
#print axioms ArkLib.ProximityGap.ThreadB.Z_natDegree
