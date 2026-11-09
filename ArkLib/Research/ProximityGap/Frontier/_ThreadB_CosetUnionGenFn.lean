/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# THREAD B — the coset-union generating function `Z(t)` (#444, target E6/E7 side-object)

This file proves the binomial closed forms of the generating functions of the over-determined
`{e₁ = e₂ = 0}` subset count over `μ_n` (`n = 2^μ`), under the probe-verified (not formalized)
antipodal identification with the `μ_{n/2}` vanishing-subset-sum count. The `S`-grade and the
`T`-grade differ by `t ↦ t²` (see "Two different gradings" below).

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

**Two different gradings (audit R-303 correction).** The antipodal identification above is an
*ungraded* count identity: it preserves the total number of subsets but NOT their size. An
`S ⊆ μ_n` with `e₁ = e₂ = 0` is a union of antipodal pairs `{x, -x}`, and the square map sends
each such pair to one point of `μ_{n/2}`, so `|S| = 2|T|`. A vanishing `T` is itself a union of
`j` antipodal pairs of `μ_{n/2}`, so `|T| = 2j` while `|S| = 4j`. Hence there are two distinct
generating functions:

> `Z_T(t) = ∑_T t^{|T|} = (1 + t²)^{n/4}`   (graded by the size of `T ⊆ μ_{n/2}`),
> `Z_S(t) = ∑_S t^{|S|} = Z_T(t²) = (1 + t⁴)^{n/4}`   (graded by the original size of `S ⊆ μ_n`).

Already at `n = 4` the `e₁ = e₂ = 0` subsets of `μ_4` are only `∅` and `μ_4`, giving
`Z_S = 1 + t⁴` (not `1 + t²`); at `n = 8`, `Z_S = 1 + 2t⁴ + t⁸`. An earlier version of this
header identified the two gradings without the factor `2` and wrote `t^{|S|}` for the `T`-grading;
that was wrong. Both share the ungraded total `Z_S(1) = Z_T(1) = 2^{n/4}`.

This file proves, in Lean, only the **abstract pair-choice combinatorics** for these gradings:

* `antipodalUnions_card` : the number of `j`-element sub-collections of `p` abstract pair
  indices `Fin p` is `C(p, j)`;
* `gradedVanishing_genfn` : `∑_{j} C(p, j) · (t²)^j = (1 + t²)^p` over `ℤ[t]` — the `T`-grade
  polynomial `Z_T` (with `p = n/4`), via the binomial theorem;
* `gradedOverdet_genfn` : `∑_{j} C(p, j) · (t⁴)^j = (1 + t⁴)^p` over `ℤ[t]` — the `S`-grade
  polynomial `Z_S`, obtained from `Z_T` by the substitution `t ↦ t²`;
* `Z_closed_form` : the generic binomial identity `∑_{j} C(p, j) u^j = (1 + u)^p`;
* `Z_total_eq_two_pow` : the ungraded total `2^p`;
* `Z_natDegree` : `(1 + t²)^p` has degree `2p` (so `Z_T` has degree `n/2`; `Z_S` has degree `n`).

**Not formalized here.** No root-of-unity carrier appears: the actual square-map bijection between
the `e₁ = e₂ = 0` subsets of `μ_n` and the vanishing subsets of `μ_{n/2}`, the size relation
`|S| = 2|T|`, and the Lam–Leung classification of vanishing subsets are cited / probe-verified
(`n = 8, 16, 32`), not proved. The theorems below count the abstract pair-index carrier only.

## The honest verdict (the §6.5 wall check)

`Z_T(t) = (1+t²)^{n/4}` and `Z_S(t) = (1+t⁴)^{n/4}` are polynomials. A polynomial generating
function has **no poles**, so the naïve "pole ⇒ growth rate of the coefficient sequence" reading is
vacuous here: the sequence of graded counts `C(n/4, j)` is *not* governed by a pole at all. What the
closed form *does* say:

* the **total** over-det/vanishing count is `Z_S(1) = Z_T(1) = 2^{n/4}` — exponential in `n`;
* the **per-grade** count is the binomial `C(n/4, j)` (at `|T| = 2j`, equivalently `|S| = 4j`),
  peaking at `≈ 2^{n/4}/√n`.

This is **off the analytic BGK char-sum wall** (it is pure char-`0` cyclotomic data, p-independent;
matches `overdet-incidence-pindependence-proof.md`). BUT it is **NOT** the binding incidence `D*(m)`
(scale mismatch: `D*(1) ≈ n³ = 3936` at `n=16` vs. total `16` here) and it is **NOT** BCHKS-1.12
(which counts *distinct r-fold subset sums*, the image size, a union over target values — not the
single fixed target `0`). So the object is genuinely a *different* char-0 surface; its closed form
follows from Lam–Leung (cited) plus the binomial identities proved below. It does **not by itself**
bound `m*` — the binding `m*` is the threshold-crossing of the **distinct-γ union count**, a
separate (open) growth law.

Status: the binomial closed forms `Z_T(t) = (1+t²)^{n/4}` and `Z_S(t) = (1+t⁴)^{n/4}` are PROVEN on
the abstract pair-index carrier; the root-set bijection and Lam–Leung are cited, not formalized;
`m*`-growth still routes to BCHKS-1.12 (= the external wall).

Issue #444, THREAD B (6.5).
-/

open Finset BigOperators

namespace ArkLib.ProximityGap.ThreadB

/-! ### The antipodal-pairing bijection: unions of `j` of `p` antipodal pairs are counted by `C(p,j)`.

We model `μ_{n/2}` abstractly as a set of `p = n/4` antipodal pairs. A vanishing subset is, by
Lam–Leung, exactly a choice of a sub-collection of these pairs (taking both elements of each
chosen pair). The bijection between such "pair-unions of size `2j`" and `j`-subsets of the `p`
pairs is the content below, packaged as a count. We work with the index set `Fin p` of pairs. -/

/-- The number of size-`j` sub-collections of `p` abstract pair indices `Fin p` is `C(p, j)`.
Read with `p = n/4` antipodal pairs of `μ_{n/2}`, this is the intended *graded vanishing-subset
count* at `|T| = 2j` (each chosen pair contributes both of its negation-paired elements; that every
vanishing subset arises uniquely this way is Lam–Leung, cited, not proved here). Lifted along the
square map, the same `j` corresponds to an `e₁ = e₂ = 0` subset `S ⊆ μ_n` with `|S| = 4j`.
This theorem counts only the abstract index carrier; no root-set bijection is proved. -/
theorem antipodalUnions_card (p j : ℕ) :
    (Finset.powersetCard j (Finset.univ : Finset (Fin p))).card = Nat.choose p j := by
  rw [Finset.card_powersetCard]
  simp [Finset.card_univ]

/-- **The `T`-graded generating function `Z_T(t) = (1 + t²)^{n/4}`** (closed form,
`ℤ`-polynomial).

With `p = n/4` antipodal pairs, the graded vanishing-subset count over `μ_{n/2}` is `C(p, j)` at
size `|T| = 2j`. The generating function summing `count(|T|) · t^{|T|}` is
`∑_{j=0}^{p} C(p,j) t^{2j}`, which by the binomial theorem equals `(1 + t²)^p`. This grades `T`,
NOT the original `S ⊆ μ_n` (for which `|S| = 4j`; see `gradedOverdet_genfn`). We state it over
the polynomial ring `ℤ[X]` with `X = t`; the identity holds in any commutative semiring. -/
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
is not tied to `ℤ`): `∑_{j≤p} C(p,j) · u^j = (1 + u)^p`. Specialized to `u = t²` it gives the
`T`-grade `Z_T(t) = (1 + t²)^p`, and to `u = t⁴` the `S`-grade `Z_S(t) = (1 + t⁴)^p`, with
`p = n/4`. This is the binomial theorem; both are therefore **polynomials** in `t` (of degrees
`2p` and `4p`), hence entire — they have **no finite poles**. -/
theorem Z_closed_form {R : Type*} [CommSemiring R] (u : R) (p : ℕ) :
    (∑ j ∈ Finset.range (p + 1), (Nat.choose p j : R) * u ^ j) = (1 + u) ^ p := by
  rw [add_comm (1 : R) u, add_pow]
  apply Finset.sum_congr rfl
  intro j _
  simp only [one_pow, mul_one, mul_comm]

/-- **The `S`-graded generating function `Z_S(t) = Z_T(t²) = (1 + t⁴)^{n/4}`** (closed form,
`ℤ`-polynomial; audit R-303 correction).

Grading by the ORIGINAL size `|S| = 4j` of an `e₁ = e₂ = 0` subset `S ⊆ μ_n` (rather than by
`|T| = 2j`) substitutes `t ↦ t²` into `Z_T`: `∑_{j=0}^{p} C(p,j) (t⁴)^j = (1 + t⁴)^p`. As with
`gradedVanishing_genfn`, this is the binomial identity on the abstract pair-index carrier; the
actual square-map bijection and the size relation `|S| = 2|T|` are not formalized here. -/
theorem gradedOverdet_genfn (p : ℕ) :
    (∑ j ∈ Finset.range (p + 1), (Nat.choose p j : Polynomial ℤ) * (Polynomial.X ^ 4) ^ j)
      = (1 + Polynomial.X ^ 4) ^ p :=
  Z_closed_form (Polynomial.X ^ 4) p

/-- The **total** over-det / vanishing count is `Z(1) = 2^{n/4}`: setting `t = 1` (`u = 1`) in the
generating function sums the graded counts. This is the exponential total — it confirms the count
is large (not bounded), but it is the count of subsets summing to the *single* fixed value `0`, NOT
the BCHKS distinct-sum image and NOT the binding incidence `D*(m)`. -/
theorem Z_total_eq_two_pow (p : ℕ) :
    (∑ j ∈ Finset.range (p + 1), (Nat.choose p j : ℕ)) = 2 ^ p := by
  simpa using (Nat.sum_range_choose p)

/-- **`Z_T(t)` is a polynomial of degree `2p = n/2` — no finite poles.**
We exhibit `Z_T` as `(1 + X²)^p : ℤ[X]` (the `S`-grade `Z_S = (1 + X⁴)^p` has degree `4p = n`), an honest polynomial, and record its `natDegree = 2p`.
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
#print axioms ArkLib.ProximityGap.ThreadB.gradedOverdet_genfn
#print axioms ArkLib.ProximityGap.ThreadB.Z_total_eq_two_pow
#print axioms ArkLib.ProximityGap.ThreadB.Z_natDegree
