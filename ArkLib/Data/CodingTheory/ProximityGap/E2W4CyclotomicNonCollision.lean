/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.E2DilationDirectCount
import ArkLib.Data.CodingTheory.ProximityGap.CyclotomicResultantBound
import ArkLib.Data.CodingTheory.ProximityGap.SharpResultantBound

/-!
# The width-4 cyclotomic non-collision: when the combinatorial model `K = n/4 − 1` equals the
ACTUAL `F_q` dilation-orbit count (#407 — closing the open part of D1)

`E2DilationDirectCount` proved the exact direct count `#{bad α} = n · K` where
`K := #(B.image (orbit μ_n ·))` is the number of **dilation orbits of bad SCALARS**
(`α = −1/e₁(S)`) in `F_q`. `_E2VanishWidthFourLaw` pinned the width-4 *combinatorial* model
`Kmodel(n) = n/4 − 1` (the number of orbits of width-4 bad SETS under exponent dilation). The
**open part of D1** is the bridge:

> does the combinatorial model equal the actual `F_q` orbit count, i.e. do distinct width-4
> exponent-orbits give distinct `e₁`-VALUE dilation orbits in `F_q`?

This file states that bridge precisely, proves the **unconditional algebraic core** (the real-
cyclotomic structure of `e₁` at width 4), and reduces the bridge to a named cyclotomic
non-collision `Prop`. The cosine-monotonicity core proves separation only after the standard
antipodal sign collapse. The quotient-free `Cd₀NonCollision` stated below is now explicitly
refuted on every even odd-characteristic domain: `t` and `-t` have invariants in the same
`μ_n`-orbit. This is an honest failure of the over-strong bridge, not a delta-star proof.

## The clean structure (the algebraic core)

A width-4 `e₂=0` bad set is, in exponents, `{ζ^i, ζ^{i+h}, ζ^{i+d₀}, ζ^{i−d₀}}` with `h = n/2`
(so `ζ^{i+h} = −ζ^i`) and `a·b = ζ^{i+d₀}·ζ^{i−d₀} = ζ^{2i} = x²` **automatically** — the product-
square condition `e₂ = 0` is exactly `b = ζ^{2i}/a`, i.e. `b = ζ^{i−d₀}` once `a = ζ^{i+d₀}`. Then

> `e1_widthFour_dilation` :  `e₁ = ζ^{i+d₀} + ζ^{i−d₀} = ζ^i · (ζ^{d₀} + ζ^{−d₀})`.

The factor `c_{d₀} := ζ^{d₀} + ζ^{−d₀}` is a **real** cyclotomic integer (`= 2·cos(2π d₀/n)` under
the standard embedding). The bad scalar is `α = −1/e₁ = −ζ^{−i}/c_{d₀}`, so its `μ_n`-dilation
orbit is `μ_n · (−1/c_{d₀})`, determined **entirely by `c_{d₀}` up to `μ_n`**. Two width-4 sets
with difference-parameters `d₀, d₀'` are in the **same** orbit iff `c_{d₀'} = ζ^u · c_{d₀}` for
some `u` (`cReal_orbit_collision_iff`).

The allowed `d₀` (forced by `a, b ∉ {x, −x}`, `a ≠ b`, `a + b ≠ 0`) range over
`{1,…,n−1} \ {0, h, n/4, 3n/4}`, and `c_{d₀} = c_{−d₀} = −c_{d₀+h}` collapses them to exactly
`n/4 − 1` classes (`= Kmodel`). So:

> `K = Kmodel(n) = n/4 − 1`   ⟺   sign-quotiented non-collision:
> away from the equality and antipodal classes, `c_{d₀'} ∉ μ_n · c_{d₀}`.

## The verdict (precise obstruction)

* **char 0 (ℂ), sign-quotiented core: UNCONDITIONAL.** `c_{d₀} = 2 cos(2π d₀/n)`; for
  `d₀ ∈ {1,…,n/4−1}` the values `|c_{d₀}|` are *strictly decreasing* (cos strictly monotone on
  `[0, π/2]`), and `|ζ^u·c_{d₀}| = |c_{d₀}|`, so distinct sign-quotiented `d₀`-classes give
  distinct orbit moduli. This file proves the cosine-monotonicity core (`cos_lt_cos_of_…` over ℝ)
  and the modulus-injectivity.
* **quotient-free `Cd₀NonCollision`: REFUTED.** If `-1 ∈ G` and the characteristic is not `2`,
  then `t' = -t`, `u = -1` gives
  `t' + t'⁻¹ = -1 * (t + t⁻¹)`. Thus the stated `Cd₀NonCollision` cannot hold in the even
  smooth-domain regime. A corrected bridge must quotient the antipodal sign class before asking
  for non-collision.
* **char `p`: NOT `q`-independent after the sign quotient.** Collision
  `c_{d₀'} = ζ^u c_{d₀}` over `F_p`, away from the antipodal class, happens iff
  `p ∣ Norm_{ℚ(ζ_n)/ℚ}(c_{d₀'} − ζ^u c_{d₀})`, a **nonzero** integer (by the ℂ sign-quotiented
  result), so its prime divisors are finite. Probe-measured bad primes: `n=16 → {17}`,
  `n=32 → {97,…,2113}` (largest `2113`).
  **They are real and small but `q`-DEPENDENT.** The crude norm bound
  `|Norm| ≤ 4^{φ(n)} = 2^n` is *vacuous at the prize point* `n = 2^30` (`2^{2^30} ≫ 2^158`), so
  the existence of the prize prime as a *good* prime is **NOT** delivered by the norm bound — it
  holds for *every prime above the (small, measured) bad-prime threshold*, which is the SAME
  good-prime / bad-prime dichotomy the KB records for the additive-energy kernel. The width-4
  orbit count is therefore `n/4 − 1` for all good primes; pinning that the *specific* prize prime
  is good is the residual (a primality/PNT-in-APs existence statement, not a coding fact).

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.

## References
- [ABF26] Arnon, Boneh, Fenzi.
  *Open Problems in List Decoding and Correlated Agreement*. 2026.
  #407.
- Chai–Fan. *Action–Orbit FRI Soundness Above the Johnson Radius*. eprint 2026/861.
- Kronecker (1857); Lam–Leung, *On vanishing sums of roots of unity*, J. Algebra 224 (2000).
-/
set_option linter.style.longLine false
set_option linter.style.longFile 2600
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option autoImplicit false

open Finset
open scoped NNReal
open ArkLib.ProximityGap.E2VanishEnergy
open ArkLib.ProximityGap.E2DilationDirectCount

namespace ArkLib.ProximityGap.E2W4CyclotomicNonCollision

/-! ## Part 1 — the unconditional algebraic core (any field)

The width-4 `e₂=0` bad set, parametrised by its centre `x = ζ^i` and difference factor
`t := ζ^{d₀}`, is `{x, −x, x·t, x·t⁻¹}` (so `a = x t`, `b = x t⁻¹`, `a·b = x² = x²` ✓). We work
over an arbitrary field with `ζ`, `x`, `t` units; nothing here needs `ζ` to be a root of unity. -/

variable {F : Type*} [Field F] [DecidableEq F]

/-- **The width-4 antipodal quadruple in product form.** With centre `x ≠ 0` and difference
factor `t` (`t ≠ ±1` and `t² ≠ −1` for genuine 4 distinct elements), the bad set is
`{x, −x, x·t, x·t⁻¹}`. Its product-pair is `a = x·t`, `b = x·t⁻¹`, with `a·b = x²` automatic. -/
noncomputable def quadT (x t : F) : Finset F := {x, -x, x * t, x * t⁻¹}

/-- **Product-form subgroup containment.** If `G` is multiplicatively closed, contains `-1`, and
contains the centre/factor `x,t`, then the whole product-form quadruple lies in `G`. -/
theorem quadT_subset_of_mem {G : Finset F} (hG : FinSubgroup G) (hneg : (-1 : F) ∈ G)
    {x t : F} (hxG : x ∈ G) (htG : t ∈ G) :
    quadT x t ⊆ G := by
  intro y hy
  simp only [quadT, Finset.mem_insert, Finset.mem_singleton] at hy
  rcases hy with rfl | rfl | rfl | rfl
  · exact hxG
  · simpa using hG.mul_mem (-1 : F) hneg x hxG
  · exact hG.mul_mem x hxG t htG
  · exact hG.mul_mem x hxG t⁻¹ (hG.inv_mem t htG)

/-- **`-1` lies in `μ_n` when `n` is even.** This is the only extra subgroup fact needed for the
product-form subset proof over the smooth dyadic domain. -/
theorem neg_one_mem_nthRootsFinset_of_even {n : ℕ} (hn : 0 < n) (heven : 2 ∣ n) :
    (-1 : F) ∈ Polynomial.nthRootsFinset n (1 : F) := by
  rw [Polynomial.mem_nthRootsFinset hn]
  obtain ⟨k, rfl⟩ := heven
  rw [pow_mul, show (-1 : F) ^ 2 = 1 by ring, one_pow]

/-- **Concrete even-`μ_n` subset proof.** For even `n`, if `x,t ∈ μ_n`, then the whole
product-form quadruple `quadT x t` lies in `μ_n`. -/
theorem quadT_subset_nthRootsFinset_of_even {n : ℕ} (hn : 0 < n) (heven : 2 ∣ n)
    {x t : F} (hxG : x ∈ Polynomial.nthRootsFinset n (1 : F))
    (htG : t ∈ Polynomial.nthRootsFinset n (1 : F)) :
    quadT x t ⊆ Polynomial.nthRootsFinset n (1 : F) :=
  quadT_subset_of_mem
    (nthRootsFinset_finSubgroup (F := F) hn)
    (neg_one_mem_nthRootsFinset_of_even (F := F) hn heven) hxG htG

/-- **The product-square condition is automatic.** `a · b = (x·t)·(x·t⁻¹) = x²` for any `t ≠ 0`:
the `e₂ = 0` constraint `a·b = x²` of `_E2VanishWidthFourLaw` holds *by construction* in the
product parametrisation. -/
theorem quadT_prod_eq (x : F) {t : F} (ht : t ≠ 0) : (x * t) * (x * t⁻¹) = x ^ 2 := by
  field_simp

/-- **The product-form quadruple has cardinality four.** The six distinctness hypotheses are
exactly the insert obligations for `{x, -x, x·t, x·t⁻¹}`. -/
theorem quadT_card (x : F) {t : F}
    (h1 : x ≠ -x) (h2 : x * t ≠ x) (h3 : x * t ≠ -x) (h4 : x * t⁻¹ ≠ x)
    (h5 : x * t⁻¹ ≠ -x) (h6 : x * t ≠ x * t⁻¹) :
    (quadT x t).card = 4 := by
  classical
  unfold quadT
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem, Finset.card_singleton]
  · simp only [Finset.mem_singleton]
    exact h6
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun hc => h3 hc.symm, fun hc => h5 hc.symm⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨h1, fun hc => h2 hc.symm, fun hc => h4 hc.symm⟩

/-- **The width-4 `e₁` law in product form (the algebraic core).** For the bad set
`{x, −x, x·t, x·t⁻¹}` with the four elements distinct, the first power sum is
`e₁ = x·t + x·t⁻¹ = x·(t + t⁻¹)`. The antipodal pair `x + (−x) = 0` cancels, leaving the
product-pair `x·(t + t⁻¹)`. The factor `c := t + t⁻¹` is the (real, when `t` is a root of unity)
invariant that controls the dilation orbit. -/
theorem e1_quadT (x : F) {t : F}
    (h1 : x ≠ -x) (h2 : x * t ≠ x) (h3 : x * t ≠ -x) (h4 : x * t⁻¹ ≠ x)
    (h5 : x * t⁻¹ ≠ -x) (h6 : x * t ≠ x * t⁻¹) :
    e1 (quadT x t) = x * (t + t⁻¹) := by
  classical
  unfold e1 quadT
  rw [Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
  · ring
  · simp only [Finset.mem_singleton]; exact h6
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun hc => h3 hc.symm, fun hc => h5 hc.symm⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨h1, fun hc => h2 hc.symm, fun hc => h4 hc.symm⟩

/-- **The product-form `p₂` law.** The antipodal pair contributes two copies of `x²`, and the
remaining pair contributes `(x·t)² + (x·t⁻¹)²`. -/
theorem p2_quadT (x : F) {t : F}
    (h1 : x ≠ -x) (h2 : x * t ≠ x) (h3 : x * t ≠ -x) (h4 : x * t⁻¹ ≠ x)
    (h5 : x * t⁻¹ ≠ -x) (h6 : x * t ≠ x * t⁻¹) :
    p2 (quadT x t) = x ^ 2 + (-x) ^ 2 + (x * t) ^ 2 + (x * t⁻¹) ^ 2 := by
  classical
  unfold p2 quadT
  rw [Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
  · ring
  · simp only [Finset.mem_singleton]; exact h6
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun hc => h3 hc.symm, fun hc => h5 hc.symm⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨h1, fun hc => h2 hc.symm, fun hc => h4 hc.symm⟩

/-- **The product-form energy identity.** If `t ≠ 0`, then `p₂(quadT x t) = e₁(quadT x t)²`.
This is the algebraic reason product-form width-4 quadruples lie on the `e₂ = 0` locus. -/
theorem p2_quadT_eq_e1_sq (x : F) {t : F} (ht : t ≠ 0)
    (h1 : x ≠ -x) (h2 : x * t ≠ x) (h3 : x * t ≠ -x) (h4 : x * t⁻¹ ≠ x)
    (h5 : x * t⁻¹ ≠ -x) (h6 : x * t ≠ x * t⁻¹) :
    p2 (quadT x t) = (e1 (quadT x t)) ^ 2 := by
  rw [p2_quadT x h1 h2 h3 h4 h5 h6, e1_quadT x h1 h2 h3 h4 h5 h6]
  field_simp [ht]
  ring

/-- **Product-form width-4 quadruples satisfy `e₂ = 0`.** This packages the product-square
parametrisation directly in the symmetric-function language used by `e2BadScalarSet`. -/
theorem e2_quadT_zero (x : F) {t : F} (ht : t ≠ 0)
    (h1 : x ≠ -x) (h2 : x * t ≠ x) (h3 : x * t ≠ -x) (h4 : x * t⁻¹ ≠ x)
    (h5 : x * t⁻¹ ≠ -x) (h6 : x * t ≠ x * t⁻¹) :
    e2 (quadT x t) = 0 := by
  rw [e2_eq, p2_quadT_eq_e1_sq x ht h1 h2 h3 h4 h5 h6]
  ring

/-- **The bad scalar of the product-form quadruple.** `α = −1/e₁ = −(x·(t+t⁻¹))⁻¹`. The point is
that the orbit of `α` under `μ_n`-dilation of the *centre* `x` is governed by the factor
`c := t + t⁻¹`: dilating `x ↦ u·x` sends `α ↦ u⁻¹·α`, so the orbit `μ_n·α` equals `μ_n·(−(c)⁻¹)`,
depending on `t` only through `c = t + t⁻¹`. -/
theorem badScalar_quadT (x : F) {t : F}
    (h1 : x ≠ -x) (h2 : x * t ≠ x) (h3 : x * t ≠ -x) (h4 : x * t⁻¹ ≠ x)
    (h5 : x * t⁻¹ ≠ -x) (h6 : x * t ≠ x * t⁻¹) :
    -(e1 (quadT x t))⁻¹ = x⁻¹ * (-(t + t⁻¹)⁻¹) := by
  rw [e1_quadT x h1 h2 h3 h4 h5 h6, mul_inv]
  ring

/-- **Product-form witnesses land in the concrete `e₂ = 0` bad-scalar image.** If `quadT x t`
is a four-subset of the ambient subgroup `G`, `t ≠ 0`, and the invariant `t+t⁻¹` is nonzero, then
its bad scalar belongs to `e2BadScalarSet G 4`. This is the missing wiring from the width-4
product parametrisation to the exact direct-count image used by `E2DilationDirectCount`. -/
theorem badScalar_quadT_mem_e2BadScalarSet {G : Finset F} {x t : F}
    (hsub : quadT x t ⊆ G) (ht : t ≠ 0)
    (h1 : x ≠ -x) (h2 : x * t ≠ x) (h3 : x * t ≠ -x) (h4 : x * t⁻¹ ≠ x)
    (h5 : x * t⁻¹ ≠ -x) (h6 : x * t ≠ x * t⁻¹)
    (hc : (t + t⁻¹) ≠ 0) :
    x⁻¹ * (-(t + t⁻¹)⁻¹) ∈ e2BadScalarSet G 4 := by
  classical
  rw [← badScalar_quadT x h1 h2 h3 h4 h5 h6]
  unfold e2BadScalarSet
  rw [Finset.mem_image]
  refine ⟨quadT x t, ?_, rfl⟩
  rw [Finset.mem_filter, Finset.mem_powersetCard]
  have hx : x ≠ 0 := by
    intro hx0
    exact h1 (by rw [hx0, neg_zero])
  have hcard : (quadT x t).card = 4 := quadT_card x h1 h2 h3 h4 h5 h6
  have hE2 : e2 (quadT x t) = 0 := e2_quadT_zero x ht h1 h2 h3 h4 h5 h6
  have hE1 : e1 (quadT x t) ≠ 0 := by
    rw [e1_quadT x h1 h2 h3 h4 h5 h6]
    exact mul_ne_zero hx hc
  exact ⟨⟨hsub, hcard⟩, hE2, hE1⟩

/-- Product-form image membership using only subgroup membership of `x,t` plus `-1 ∈ G`. -/
theorem badScalar_quadT_mem_e2BadScalarSet_of_mem {G : Finset F}
    (hG : FinSubgroup G) (hneg : (-1 : F) ∈ G) {x t : F}
    (hxG : x ∈ G) (htG : t ∈ G)
    (h1 : x ≠ -x) (h2 : x * t ≠ x) (h3 : x * t ≠ -x) (h4 : x * t⁻¹ ≠ x)
    (h5 : x * t⁻¹ ≠ -x) (h6 : x * t ≠ x * t⁻¹)
    (hc : (t + t⁻¹) ≠ 0) :
    x⁻¹ * (-(t + t⁻¹)⁻¹) ∈ e2BadScalarSet G 4 :=
  badScalar_quadT_mem_e2BadScalarSet
    (quadT_subset_of_mem hG hneg hxG htG) (ne_zero_of_mem_finSubgroup hG htG)
    h1 h2 h3 h4 h5 h6 hc

/-! ## Part 2 — the orbit-collision reduction (the bridge to the combinatorial model)

The dilation orbit of the bad scalar is `μ_n · (−(c)⁻¹)` with `c = t + t⁻¹`. Two width-4 sets
(centres `x, x'`, factors `t, t'`, all in `μ_n`) lie in the SAME `μ_n`-dilation orbit of bad
scalars iff `−(c')⁻¹ = ζ^u · (−(c)⁻¹)` for some root of unity `ζ^u`, i.e. iff `c' = ζ^{-u}·c`,
i.e. iff `c' ∈ μ_n · c`.  `K = #{distinct orbits}` therefore equals `#{distinct μ_n·c classes}`.
The combinatorial model `Kmodel = n/4 − 1` counts the `c`-classes *as exponent data*; the bridge
"`K = Kmodel`" is exactly: distinct allowed factors `t = ζ^{d₀}` give distinct `μ_n·c` classes. -/

/-- **The orbit-collision criterion.** Bad scalars `−(c)⁻¹` and `−(c')⁻¹` (`c, c' ≠ 0`) lie in the
same multiplicative-`G`-orbit iff `c'` and `c` differ by an element of `G⁻¹ = G` (a subgroup):
`(∃ u ∈ G, −(c')⁻¹ = u · (−(c)⁻¹)) ↔ (∃ v ∈ G, c' = v · c)`, where `v = u⁻¹`. This is the exact
reduction of the orbit count to the `c`-value collision. -/
theorem orbit_collision_iff {G : Finset F} (hG : FinSubgroup G) {c c' : F}
    (hc : c ≠ 0) (hc' : c' ≠ 0) :
    (∃ u ∈ G, -(c')⁻¹ = u * (-(c)⁻¹)) ↔ (∃ v ∈ G, c' = v * c) := by
  constructor
  · rintro ⟨u, huG, heq⟩
    have hune : u ≠ 0 := fun h => hG.zero_notMem (h ▸ huG)
    refine ⟨u⁻¹, hG.inv_mem _ huG, ?_⟩
    -- `-(c')⁻¹ = u * (-(c)⁻¹)` ⇒ `(c')⁻¹ = u * (c)⁻¹` ⇒ (invert) `c' = u⁻¹ * c`.
    have hcc : (c')⁻¹ = u * (c)⁻¹ := by linear_combination -heq
    field_simp at hcc
    field_simp
    linear_combination -hcc
  · rintro ⟨v, hvG, heq⟩
    have hvne : v ≠ 0 := fun h => hG.zero_notMem (h ▸ hvG)
    refine ⟨v⁻¹, hG.inv_mem _ hvG, ?_⟩
    -- `c' = v * c` ⇒ `(c')⁻¹ = v⁻¹ * (c)⁻¹` ⇒ negate.
    rw [heq, mul_inv, mul_comm v⁻¹ _]
    ring

/-! ## Part 3 — the char-0 discharge (the cyclotomic non-collision, UNCONDITIONAL over ℝ/ℂ)

Over ℂ with `ζ = exp(2π i/n)` and factor `t = ζ^d`, the invariant `c_d := t + t⁻¹ = ζ^d + ζ^{−d}
= 2·cos(2π d/n)` is **real**, and every element of its `μ_n`-orbit has modulus `|c_d|` (since
roots of unity have modulus 1). So distinct orbits ⟺ distinct `|c_d|`. For the allowed range
`d ∈ {1,…,⌊n/4⌋−1}` the angle `θ_d := 2π d/n` lies in `(0, π/2)`, where `cos` is strictly positive
and strictly decreasing — hence `c_d = 2 cos θ_d` are **distinct positive reals**, so `|c_d|` is
injective and there is **no collision**. This is the entire char-0 obstruction, discharged by
elementary cosine monotonicity (`Real.strictAntiOn_cos`), NOT Kronecker / Lam–Leung.

We isolate the q-independent mathematical heart as a standalone ℝ statement: the map
`d ↦ 2·cos(2π d/n)` is injective (indeed strictly decreasing, with positive values) on the
allowed window `0 < d`, `2·d ≤ ⌊n/2⌋ − 1 < n/2` (equivalently `θ_d < π/2`).
The `c`-collision in char 0 would force two such cosines to be equal, up to the `μ_n` modulus,
which is 1. That is impossible. -/

open Real in
/-- **The char-0 cyclotomic non-collision core (the cosine separation).** For real angles
`0 ≤ θ < θ' ≤ π/2`, `2·cos θ' < 2·cos θ`, and both are `≥ 0`. Specialised to `θ = 2π d/n`,
`θ' = 2π d'/n` with `0 ≤ d < d'` and `2 d' ≤ n/2` (the allowed width-4 window, `θ' ≤ π/2`), this
says the invariants `c_d = 2 cos θ_d > c_{d'} = 2 cos θ_{d'} ≥ 0` are **strictly separated** — so
their `μ_n`-orbit moduli `|c_d| ≠ |c_{d'}|` and the two width-4 orbits do not collide over ℂ. -/
theorem cos_invariant_strict_anti {θ θ' : ℝ} (h0 : 0 ≤ θ) (hlt : θ < θ') (hpi : θ' ≤ π / 2) :
    2 * Real.cos θ' < 2 * Real.cos θ ∧ 0 ≤ 2 * Real.cos θ' := by
  have hπ : (0:ℝ) ≤ π := Real.pi_nonneg
  have hmem  : θ  ∈ Set.Icc (0:ℝ) π := ⟨h0, le_trans (le_trans hlt.le hpi) (by linarith)⟩
  have hmem' : θ' ∈ Set.Icc (0:ℝ) π := ⟨le_trans h0 hlt.le, le_trans hpi (by linarith)⟩
  refine ⟨by linarith [Real.strictAntiOn_cos hmem hmem' hlt], ?_⟩
  have : (0:ℝ) ≤ Real.cos θ' := Real.cos_nonneg_of_mem_Icc ⟨by linarith, hpi⟩
  linarith

/-- **The char-0 invariant is injective on the allowed window (no orbit collision over ℂ).**
For distinct `d, d'` in the allowed range — both giving angles in `[0, π/2]` — the real invariants
`2 cos θ_d` are distinct. This is the contrapositive packaging of `cos_invariant_strict_anti`:
equal invariants force equal angles on the sign-quotiented window. It is the char-0 separation
core for the repaired non-collision statement, not a proof of the quotient-free
`Cd₀NonCollision` below. -/
theorem cos_invariant_injOn {θ θ' : ℝ} (h0 : 0 ≤ θ) (h0' : 0 ≤ θ')
    (hpi : θ ≤ Real.pi / 2) (hpi' : θ' ≤ Real.pi / 2) (hne : θ ≠ θ') :
    2 * Real.cos θ ≠ 2 * Real.cos θ' := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact (ne_of_gt (cos_invariant_strict_anti h0 hlt hpi').1)
  · exact (ne_of_lt (cos_invariant_strict_anti h0' hgt hpi).1)

/-! ## Part 4 — the named cyclotomic non-collision `Prop` and the verdict

We keep the original quotient-free `Prop` as a documented failed scanner hypothesis, then introduce
the repaired sign-quotiented residual. The quotient-free form is useful as a guardrail because the
antipodal refuter below shows exactly why it is too strong in even domains. -/

/-- **The width-4 cyclotomic non-collision hypothesis.** Over a field `F` carrying the subgroup
`G = μ_n`, for any two factors `t, t' ∈ G` whose invariants `c = t + t⁻¹`, `c' = t' + t'⁻¹` are
*distinct and nonzero*, the invariants do not lie in the same `G`-orbit: `∀ u ∈ G, c' ≠ u·c`.
This is exactly the condition (`orbit_collision_iff`) for the bad-scalar orbits not to collide,
hence for the actual orbit count `K` to equal the combinatorial model `Kmodel = n/4 − 1`. -/
def Cd₀NonCollision (G : Finset F) : Prop :=
  ∀ t ∈ G, ∀ t' ∈ G, (t + t⁻¹) ≠ 0 → (t' + t'⁻¹) ≠ 0 → (t + t⁻¹) ≠ (t' + t'⁻¹) →
    ∀ u ∈ G, (t' + t'⁻¹) ≠ u * (t + t⁻¹)

open Classical in
/-- **Exact scanner-failure form for `Cd₀NonCollision`.** The named char-`p` residual fails
precisely when a concrete pair of nonzero, distinct invariants collides under multiplication by
some subgroup element. This is the finite witness shape used by the width-4 orbit scanner. -/
theorem not_cd0NonCollision_iff_exists_collision (G : Finset F) :
    (¬ Cd₀NonCollision (F := F) G) ↔
      ∃ t ∈ G, ∃ t' ∈ G,
        (t + t⁻¹) ≠ 0 ∧
        (t' + t'⁻¹) ≠ 0 ∧
        (t + t⁻¹) ≠ (t' + t'⁻¹) ∧
        ∃ u ∈ G, (t' + t'⁻¹) = u * (t + t⁻¹) := by
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro t htG t' ht'G hc hc' hne u huG
    exact fun hcollision => hnone ⟨t, htG, t', ht'G, hc, hc', hne, u, huG, hcollision⟩
  · rintro ⟨t, htG, t', ht'G, hc, hc', hne, u, huG, hcollision⟩ hNC
    exact hNC t htG t' ht'G hc hc' hne u huG hcollision

/-- A concrete invariant collision refutes `Cd₀NonCollision`. -/
theorem not_cd0NonCollision_of_collision {G : Finset F} {t t' u : F}
    (htG : t ∈ G) (ht'G : t' ∈ G)
    (hc : (t + t⁻¹) ≠ 0) (hc' : (t' + t'⁻¹) ≠ 0)
    (hne : (t + t⁻¹) ≠ (t' + t'⁻¹)) (huG : u ∈ G)
    (hcollision : (t' + t'⁻¹) = u * (t + t⁻¹)) :
    ¬ Cd₀NonCollision G := by
  intro hNC
  exact hNC t htG t' ht'G hc hc' hne u huG hcollision

/-- A no-collision scanner certificate proves `Cd₀NonCollision`. -/
theorem cd0NonCollision_of_no_collision {G : Finset F}
    (hno :
      ¬ ∃ t ∈ G, ∃ t' ∈ G,
        (t + t⁻¹) ≠ 0 ∧
        (t' + t'⁻¹) ≠ 0 ∧
        (t + t⁻¹) ≠ (t' + t'⁻¹) ∧
        ∃ u ∈ G, (t' + t'⁻¹) = u * (t + t⁻¹)) :
    Cd₀NonCollision G := by
  intro t htG t' ht'G hc hc' hne u huG
  exact fun hcollision => hno ⟨t, htG, t', ht'G, hc, hc', hne, u, huG, hcollision⟩

/-! ### The repaired sign-quotiented non-collision statement -/

/-- **Sign-quotiented width-4 cyclotomic non-collision.** This is the repaired residual after
the antipodal collapse `t ↦ -t`: two nonzero invariants are required not to collide only when
they are distinct even after quotienting by sign. Equivalently, the only permitted collisions are
the trivial equality class and the antipodal sign class. -/
def Cd₀NonCollisionModSign (G : Finset F) : Prop :=
  ∀ t ∈ G, ∀ t' ∈ G,
    (t + t⁻¹) ≠ 0 →
    (t' + t'⁻¹) ≠ 0 →
    (t + t⁻¹) ≠ (t' + t'⁻¹) →
    (t + t⁻¹) ≠ -(t' + t'⁻¹) →
      ∀ u ∈ G, (t' + t'⁻¹) ≠ u * (t + t⁻¹)

/-- The quotient-free residual implies the repaired sign-quotiented residual. -/
theorem cd0NonCollisionModSign_of_cd0NonCollision {G : Finset F}
    (hNC : Cd₀NonCollision G) :
    Cd₀NonCollisionModSign G := by
  intro t htG t' ht'G hc hc' hne _hsign u huG
  exact hNC t htG t' ht'G hc hc' hne u huG

open Classical in
/-- **Exact scanner-failure form for `Cd₀NonCollisionModSign`.** The repaired residual fails
precisely when a concrete pair of nonzero invariants, distinct modulo the sign quotient, collides
under multiplication by some subgroup element. -/
theorem not_cd0NonCollisionModSign_iff_exists_collision (G : Finset F) :
    (¬ Cd₀NonCollisionModSign (F := F) G) ↔
      ∃ t ∈ G, ∃ t' ∈ G,
        (t + t⁻¹) ≠ 0 ∧
        (t' + t'⁻¹) ≠ 0 ∧
        (t + t⁻¹) ≠ (t' + t'⁻¹) ∧
        (t + t⁻¹) ≠ -(t' + t'⁻¹) ∧
        ∃ u ∈ G, (t' + t'⁻¹) = u * (t + t⁻¹) := by
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro t htG t' ht'G hc hc' hne hsign u huG
    exact fun hcollision =>
      hnone ⟨t, htG, t', ht'G, hc, hc', hne, hsign, u, huG, hcollision⟩
  · rintro ⟨t, htG, t', ht'G, hc, hc', hne, hsign, u, huG, hcollision⟩ hNC
    exact hNC t htG t' ht'G hc hc' hne hsign u huG hcollision

/-- A concrete sign-distinct invariant collision refutes `Cd₀NonCollisionModSign`. -/
theorem not_cd0NonCollisionModSign_of_collision {G : Finset F} {t t' u : F}
    (htG : t ∈ G) (ht'G : t' ∈ G)
    (hc : (t + t⁻¹) ≠ 0) (hc' : (t' + t'⁻¹) ≠ 0)
    (hne : (t + t⁻¹) ≠ (t' + t'⁻¹))
    (hsign : (t + t⁻¹) ≠ -(t' + t'⁻¹)) (huG : u ∈ G)
    (hcollision : (t' + t'⁻¹) = u * (t + t⁻¹)) :
    ¬ Cd₀NonCollisionModSign G := by
  intro hNC
  exact hNC t htG t' ht'G hc hc' hne hsign u huG hcollision

/-- A no-collision scanner certificate proves `Cd₀NonCollisionModSign`. -/
theorem cd0NonCollisionModSign_of_no_collision {G : Finset F}
    (hno :
      ¬ ∃ t ∈ G, ∃ t' ∈ G,
        (t + t⁻¹) ≠ 0 ∧
        (t' + t'⁻¹) ≠ 0 ∧
        (t + t⁻¹) ≠ (t' + t'⁻¹) ∧
        (t + t⁻¹) ≠ -(t' + t'⁻¹) ∧
        ∃ u ∈ G, (t' + t'⁻¹) = u * (t + t⁻¹)) :
    Cd₀NonCollisionModSign G := by
  intro t htG t' ht'G hc hc' hne hsign u huG
  exact fun hcollision => hno ⟨t, htG, t', ht'G, hc, hc', hne, hsign, u, huG, hcollision⟩

/-! ### Antipodal refutation of the quotient-free non-collision statement -/

/-- Negating the factor negates the width-4 invariant `t + t⁻¹`. -/
theorem invariant_neg_eq_neg_invariant (t : F) :
    -t + (-t)⁻¹ = -(t + t⁻¹) := by
  rw [inv_neg]
  ring

/-- In odd characteristic, a nonzero invariant is not equal to its own negative. -/
theorem invariant_ne_neg_of_two_ne_zero {c : F} (h2 : (2 : F) ≠ 0) (hc : c ≠ 0) :
    c ≠ -c := by
  intro h
  have hsub : c - (-c) = 0 := sub_eq_zero.mpr h
  have hmul : (2 : F) * c = 0 := by
    rw [← hsub]
    ring
  exact (mul_ne_zero h2 hc) hmul

/-- **Antipodal collision refutes quotient-free `Cd₀NonCollision`.** If `-1 ∈ G`, then every
factor with nonzero invariant gives a collision between `t` and `-t`; the subgroup multiplier is
`u = -1`. This is the formal reason the raw non-collision statement must be sign-quotiented before
it can model the width-4 orbit count. -/
theorem not_cd0NonCollision_of_antipodal_collision {G : Finset F}
    (hG : FinSubgroup G) (hneg : (-1 : F) ∈ G) (h2 : (2 : F) ≠ 0)
    {t : F} (htG : t ∈ G) (hc : (t + t⁻¹) ≠ 0) :
    ¬ Cd₀NonCollision G := by
  have hneg_tG : -t ∈ G := by
    simpa using hG.mul_mem (-1 : F) hneg t htG
  have hc' : (-t + (-t)⁻¹) ≠ 0 := by
    rw [invariant_neg_eq_neg_invariant]
    exact neg_ne_zero.mpr hc
  have hne : (t + t⁻¹) ≠ (-t + (-t)⁻¹) := by
    rw [invariant_neg_eq_neg_invariant]
    exact invariant_ne_neg_of_two_ne_zero h2 hc
  have hcollision : (-t + (-t)⁻¹) = (-1 : F) * (t + t⁻¹) := by
    rw [invariant_neg_eq_neg_invariant]
    ring
  exact not_cd0NonCollision_of_collision htG hneg_tG hc hc' hne hneg hcollision

/-- **Any even odd-characteristic subgroup refutes quotient-free `Cd₀NonCollision`.** Taking
`t = 1` gives the invariant `2`, so no extra witness search is needed. -/
theorem not_cd0NonCollision_of_neg_mem {G : Finset F}
    (hG : FinSubgroup G) (hneg : (-1 : F) ∈ G) (h2 : (2 : F) ≠ 0) :
    ¬ Cd₀NonCollision G := by
  refine not_cd0NonCollision_of_antipodal_collision hG hneg h2 hG.one_mem ?_
  rw [show (1 : F)⁻¹ = 1 by simp]
  convert h2 using 1
  ring

/-- **Concrete even-`μ_n` refuter for quotient-free `Cd₀NonCollision`.** This closes the scanner
audit for the raw hypothesis: it is false in every even smooth-domain subgroup over odd
characteristic. -/
theorem not_cd0NonCollision_nthRootsFinset_of_even {n : ℕ}
    (hn : 0 < n) (heven : 2 ∣ n) (h2 : (2 : F) ≠ 0) :
    ¬ Cd₀NonCollision (Polynomial.nthRootsFinset n (1 : F)) :=
  not_cd0NonCollision_of_neg_mem
    (nthRootsFinset_finSubgroup (F := F) hn)
    (neg_one_mem_nthRootsFinset_of_even (F := F) hn heven) h2

/-- Characteristic-zero specialization of the concrete even-`μ_n` refuter. -/
theorem not_cd0NonCollision_nthRootsFinset_of_even_charZero [CharZero F] {n : ℕ}
    (hn : 0 < n) (heven : 2 ∣ n) :
    ¬ Cd₀NonCollision (Polynomial.nthRootsFinset n (1 : F)) :=
  not_cd0NonCollision_nthRootsFinset_of_even hn heven two_ne_zero

/-- **The bridge `K = Kmodel` from non-collision (the reduction theorem).** Granting the named
`Cd₀NonCollision G`, two width-4 product-form bad sets with distinct nonzero invariants
`c = t+t⁻¹ ≠ c' = t'+t'⁻¹` produce bad scalars in **distinct** `G`-orbits. This is the exact
content of "distinct quotient-free width-4 exponent-orbits give distinct `F_q` orbits". The
hypothesis is now known to be over-strong in the even domain by
`not_cd0NonCollision_nthRootsFinset_of_even`; future callers should use a sign-quotiented
replacement. -/
theorem orbits_distinct_of_nonCollision {G : Finset F} (hG : FinSubgroup G)
    (hNC : Cd₀NonCollision G) {t t' : F} (htG : t ∈ G) (ht'G : t' ∈ G)
    (hc : (t + t⁻¹) ≠ 0) (hc' : (t' + t'⁻¹) ≠ 0)
    (hne : (t + t⁻¹) ≠ (t' + t'⁻¹)) :
    ¬ (∃ u ∈ G, -(t' + t'⁻¹)⁻¹ = u * (-(t + t⁻¹)⁻¹)) := by
  rw [orbit_collision_iff hG hc hc']
  rintro ⟨v, hvG, heq⟩
  exact hNC t htG t' ht'G hc hc' hne v hvG heq

/-- **The repaired sign-quotiented orbit bridge.** Granting `Cd₀NonCollisionModSign G`, two
width-4 invariants give distinct bad-scalar orbits once they are nonzero and distinct modulo the
antipodal sign quotient: `c ≠ c'` and `c ≠ -c'`. -/
theorem orbits_distinct_of_nonCollisionModSign {G : Finset F} (hG : FinSubgroup G)
    (hNC : Cd₀NonCollisionModSign G) {t t' : F} (htG : t ∈ G) (ht'G : t' ∈ G)
    (hc : (t + t⁻¹) ≠ 0) (hc' : (t' + t'⁻¹) ≠ 0)
    (hne : (t + t⁻¹) ≠ (t' + t'⁻¹))
    (hsign : (t + t⁻¹) ≠ -(t' + t'⁻¹)) :
    ¬ (∃ u ∈ G, -(t' + t'⁻¹)⁻¹ = u * (-(t + t⁻¹)⁻¹)) := by
  rw [orbit_collision_iff hG hc hc']
  rintro ⟨v, hvG, heq⟩
  exact hNC t htG t' ht'G hc hc' hne hsign v hvG heq

/-- **The full bad-set form of the reduction.** Two width-4 product-form bad sets `quadT x t`,
`quadT x' t'` (centres `x, x' ≠ 0`, factors `t, t' ∈ G = μ_n`, all four-element-distinctness
hypotheses) produce bad scalars `−1/e₁` in DISTINCT `G`-orbits whenever their invariants
`c = t+t⁻¹`, `c' = t'+t'⁻¹` are distinct (and nonzero), granting `Cd₀NonCollision G`. Combined
with `E2DilationDirectCount.badScalarSet_card_eq_orbit_mul` (`#bad = #G · K`), this is the
quotient-free version of the orbit-count bridge. The hypothesis is intentionally retained for
backward compatibility, but it is over-strong in even domains. -/
theorem badScalar_orbits_distinct_of_nonCollision {G : Finset F} (hG : FinSubgroup G)
    (hNC : Cd₀NonCollision G) {x x' t t' : F}
    (hxG : x ∈ G) (hx'G : x' ∈ G) (htG : t ∈ G) (ht'G : t' ∈ G)
    -- distinctness for `quadT x t`:
    (hx1 : x ≠ -x) (hx2 : x * t ≠ x) (hx3 : x * t ≠ -x) (hx4 : x * t⁻¹ ≠ x)
    (hx5 : x * t⁻¹ ≠ -x) (hx6 : x * t ≠ x * t⁻¹)
    -- distinctness for `quadT x' t'`:
    (hy1 : x' ≠ -x') (hy2 : x' * t' ≠ x') (hy3 : x' * t' ≠ -x') (hy4 : x' * t'⁻¹ ≠ x')
    (hy5 : x' * t'⁻¹ ≠ -x') (hy6 : x' * t' ≠ x' * t'⁻¹)
    (hc : (t + t⁻¹) ≠ 0) (hc' : (t' + t'⁻¹) ≠ 0)
    (hne : (t + t⁻¹) ≠ (t' + t'⁻¹)) :
    ¬ (∃ u ∈ G, -(e1 (quadT x' t'))⁻¹ = u * (-(e1 (quadT x t))⁻¹)) := by
  -- rewrite both bad scalars via `badScalar_quadT`, peel the centre factors `x`, `x'`.
  intro hcoll
  obtain ⟨u, huG, heq⟩ := hcoll
  have hxne : x ≠ 0 := fun h => hG.zero_notMem (h ▸ hxG)
  have hx'ne : x' ≠ 0 := fun h => hG.zero_notMem (h ▸ hx'G)
  rw [badScalar_quadT x' hy1 hy2 hy3 hy4 hy5 hy6,
      badScalar_quadT x hx1 hx2 hx3 hx4 hx5 hx6] at heq
  -- heq : x'⁻¹·(−c'⁻¹) = u·(x⁻¹·(−c⁻¹)).  Multiply by x'  ⇒  −c'⁻¹ = (u·x'·x⁻¹)·(−c⁻¹).
  -- The orbit element `v = u·x'·x⁻¹` lies in `G` (closure + inverse), contradicting non-collision.
  apply orbits_distinct_of_nonCollision hG hNC htG ht'G hc hc' hne
  refine ⟨u * (x' * x⁻¹), hG.mul_mem _ huG _ (hG.mul_mem _ hx'G _ (hG.inv_mem _ hxG)), ?_⟩
  -- `heq : x'⁻¹·(−c'⁻¹) = u·(x⁻¹·(−c⁻¹))`.  Multiply both sides by `x'` and regroup.
  have key : -(t' + t'⁻¹)⁻¹ = x' * (u * (x⁻¹ * -(t + t⁻¹)⁻¹)) := by
    rw [← heq, ← mul_assoc, mul_inv_cancel₀ hx'ne, one_mul]
  rw [key]; ring

/-- **The repaired full bad-set form of the reduction.** This is the usable sign-quotiented
version: two product-form witnesses give distinct bad-scalar orbits when their invariants are
distinct and not antipodal. -/
theorem badScalar_orbits_distinct_of_nonCollisionModSign {G : Finset F} (hG : FinSubgroup G)
    (hNC : Cd₀NonCollisionModSign G) {x x' t t' : F}
    (hxG : x ∈ G) (hx'G : x' ∈ G) (htG : t ∈ G) (ht'G : t' ∈ G)
    -- distinctness for `quadT x t`:
    (hx1 : x ≠ -x) (hx2 : x * t ≠ x) (hx3 : x * t ≠ -x) (hx4 : x * t⁻¹ ≠ x)
    (hx5 : x * t⁻¹ ≠ -x) (hx6 : x * t ≠ x * t⁻¹)
    -- distinctness for `quadT x' t'`:
    (hy1 : x' ≠ -x') (hy2 : x' * t' ≠ x') (hy3 : x' * t' ≠ -x')
    (hy4 : x' * t'⁻¹ ≠ x') (hy5 : x' * t'⁻¹ ≠ -x')
    (hy6 : x' * t' ≠ x' * t'⁻¹)
    (hc : (t + t⁻¹) ≠ 0) (hc' : (t' + t'⁻¹) ≠ 0)
    (hne : (t + t⁻¹) ≠ (t' + t'⁻¹))
    (hsign : (t + t⁻¹) ≠ -(t' + t'⁻¹)) :
    ¬ (∃ u ∈ G, -(e1 (quadT x' t'))⁻¹ = u * (-(e1 (quadT x t))⁻¹)) := by
  intro hcoll
  obtain ⟨u, huG, heq⟩ := hcoll
  have hxne : x ≠ 0 := fun h => hG.zero_notMem (h ▸ hxG)
  have hx'ne : x' ≠ 0 := fun h => hG.zero_notMem (h ▸ hx'G)
  rw [badScalar_quadT x' hy1 hy2 hy3 hy4 hy5 hy6,
      badScalar_quadT x hx1 hx2 hx3 hx4 hx5 hx6] at heq
  apply orbits_distinct_of_nonCollisionModSign hG hNC htG ht'G hc hc' hne hsign
  refine ⟨u * (x' * x⁻¹), hG.mul_mem _ huG _ (hG.mul_mem _ hx'G _ (hG.inv_mem _ hxG)), ?_⟩
  have key : -(t' + t'⁻¹)⁻¹ = x' * (u * (x⁻¹ * -(t + t⁻¹)⁻¹)) := by
    rw [← heq, ← mul_assoc, mul_inv_cancel₀ hx'ne, one_mul]
  rw [key]; ring

/-- **Two non-colliding product-form width-4 witnesses break the subgroup-size budget.** Once the
two product-form witnesses are certified as members of `e2BadScalarSet G 4`, the non-collision
theorem gives two distinct full `G`-orbits inside that image. The direct-count consumer from
`E2DilationDirectCount` then converts this into `#G < #e2BadScalarSet`. -/
theorem group_card_lt_e2BadScalarSet_card_of_two_quadT_nonCollision {G : Finset F}
    (hG : FinSubgroup G) (hNC : Cd₀NonCollision G) {x x' t t' : F}
    (hsub : quadT x t ⊆ G) (hsub' : quadT x' t' ⊆ G)
    (hxG : x ∈ G) (hx'G : x' ∈ G) (htG : t ∈ G) (ht'G : t' ∈ G)
    (ht0 : t ≠ 0) (ht'0 : t' ≠ 0)
    -- distinctness for `quadT x t`:
    (hx1 : x ≠ -x) (hx2 : x * t ≠ x) (hx3 : x * t ≠ -x) (hx4 : x * t⁻¹ ≠ x)
    (hx5 : x * t⁻¹ ≠ -x) (hx6 : x * t ≠ x * t⁻¹)
    -- distinctness for `quadT x' t'`:
    (hy1 : x' ≠ -x') (hy2 : x' * t' ≠ x') (hy3 : x' * t' ≠ -x')
    (hy4 : x' * t'⁻¹ ≠ x') (hy5 : x' * t'⁻¹ ≠ -x')
    (hy6 : x' * t' ≠ x' * t'⁻¹)
    (hc : (t + t⁻¹) ≠ 0) (hc' : (t' + t'⁻¹) ≠ 0)
    (hne : (t + t⁻¹) ≠ (t' + t'⁻¹)) :
    G.card < (e2BadScalarSet G 4).card := by
  classical
  let α : F := -(e1 (quadT x t))⁻¹
  let β : F := -(e1 (quadT x' t'))⁻¹
  have hα : α ∈ e2BadScalarSet G 4 := by
    dsimp [α]
    rw [badScalar_quadT x hx1 hx2 hx3 hx4 hx5 hx6]
    exact badScalar_quadT_mem_e2BadScalarSet hsub ht0 hx1 hx2 hx3 hx4 hx5 hx6 hc
  have hβ : β ∈ e2BadScalarSet G 4 := by
    dsimp [β]
    rw [badScalar_quadT x' hy1 hy2 hy3 hy4 hy5 hy6]
    exact badScalar_quadT_mem_e2BadScalarSet hsub' ht'0 hy1 hy2 hy3 hy4 hy5 hy6 hc'
  have hnotcoll : ¬ (∃ u ∈ G, β = u * α) := by
    dsimp [α, β]
    exact badScalar_orbits_distinct_of_nonCollision hG hNC hxG hx'G htG ht'G
      hx1 hx2 hx3 hx4 hx5 hx6 hy1 hy2 hy3 hy4 hy5 hy6 hc hc' hne
  have horbit_ne : orbit G β ≠ orbit G α := by
    intro heq
    have hmem : β ∈ orbit G α := by
      simpa [heq] using self_mem_orbit hG β
    unfold orbit at hmem
    rw [Finset.mem_image] at hmem
    obtain ⟨u, huG, hmul⟩ := hmem
    exact hnotcoll ⟨u, huG, hmul.symm⟩
  have hpair_subset :
      ({orbit G α, orbit G β} : Finset (Finset F)) ⊆
        (e2BadScalarSet G 4).image (fun y => orbit G y) := by
    intro O hO
    simp only [Finset.mem_insert, Finset.mem_singleton] at hO
    rcases hO with rfl | rfl
    · exact Finset.mem_image_of_mem _ hα
    · exact Finset.mem_image_of_mem _ hβ
  have hpair_card : ({orbit G α, orbit G β} : Finset (Finset F)).card = 2 := by
    simp [horbit_ne.symm]
  have horbits : 2 ≤ ((e2BadScalarSet G 4).image (fun y => orbit G y)).card := by
    calc
      2 = ({orbit G α, orbit G β} : Finset (Finset F)).card := hpair_card.symm
      _ ≤ ((e2BadScalarSet G 4).image (fun y => orbit G y)).card :=
        Finset.card_le_card hpair_subset
  exact group_card_lt_badScalarSet_card_of_two_orbits hG
    (zero_notMem_e2BadScalarSet G 4) (e2BadScalarSet_stable hG 4) horbits

/-- **Sign-quotiented two-witness budget refuter.** This is the corrected version of
`group_card_lt_e2BadScalarSet_card_of_two_quadT_nonCollision`: the two invariants must be
distinct modulo sign, and the non-collision hypothesis is the repaired
`Cd₀NonCollisionModSign`. -/
theorem group_card_lt_e2BadScalarSet_card_of_two_quadT_modSignNonCollision {G : Finset F}
    (hG : FinSubgroup G) (hNC : Cd₀NonCollisionModSign G) {x x' t t' : F}
    (hsub : quadT x t ⊆ G) (hsub' : quadT x' t' ⊆ G)
    (hxG : x ∈ G) (hx'G : x' ∈ G) (htG : t ∈ G) (ht'G : t' ∈ G)
    (ht0 : t ≠ 0) (ht'0 : t' ≠ 0)
    -- distinctness for `quadT x t`:
    (hx1 : x ≠ -x) (hx2 : x * t ≠ x) (hx3 : x * t ≠ -x) (hx4 : x * t⁻¹ ≠ x)
    (hx5 : x * t⁻¹ ≠ -x) (hx6 : x * t ≠ x * t⁻¹)
    -- distinctness for `quadT x' t'`:
    (hy1 : x' ≠ -x') (hy2 : x' * t' ≠ x') (hy3 : x' * t' ≠ -x')
    (hy4 : x' * t'⁻¹ ≠ x') (hy5 : x' * t'⁻¹ ≠ -x')
    (hy6 : x' * t' ≠ x' * t'⁻¹)
    (hc : (t + t⁻¹) ≠ 0) (hc' : (t' + t'⁻¹) ≠ 0)
    (hne : (t + t⁻¹) ≠ (t' + t'⁻¹))
    (hsign : (t + t⁻¹) ≠ -(t' + t'⁻¹)) :
    G.card < (e2BadScalarSet G 4).card := by
  classical
  let α : F := -(e1 (quadT x t))⁻¹
  let β : F := -(e1 (quadT x' t'))⁻¹
  have hα : α ∈ e2BadScalarSet G 4 := by
    dsimp [α]
    rw [badScalar_quadT x hx1 hx2 hx3 hx4 hx5 hx6]
    exact badScalar_quadT_mem_e2BadScalarSet hsub ht0 hx1 hx2 hx3 hx4 hx5 hx6 hc
  have hβ : β ∈ e2BadScalarSet G 4 := by
    dsimp [β]
    rw [badScalar_quadT x' hy1 hy2 hy3 hy4 hy5 hy6]
    exact badScalar_quadT_mem_e2BadScalarSet hsub' ht'0 hy1 hy2 hy3 hy4 hy5 hy6 hc'
  have hnotcoll : ¬ (∃ u ∈ G, β = u * α) := by
    dsimp [α, β]
    exact badScalar_orbits_distinct_of_nonCollisionModSign hG hNC hxG hx'G htG ht'G
      hx1 hx2 hx3 hx4 hx5 hx6 hy1 hy2 hy3 hy4 hy5 hy6 hc hc' hne hsign
  have horbit_ne : orbit G β ≠ orbit G α := by
    intro heq
    have hmem : β ∈ orbit G α := by
      simpa [heq] using self_mem_orbit hG β
    unfold orbit at hmem
    rw [Finset.mem_image] at hmem
    obtain ⟨u, huG, hmul⟩ := hmem
    exact hnotcoll ⟨u, huG, hmul.symm⟩
  have hpair_subset :
      ({orbit G α, orbit G β} : Finset (Finset F)) ⊆
        (e2BadScalarSet G 4).image (fun y => orbit G y) := by
    intro O hO
    simp only [Finset.mem_insert, Finset.mem_singleton] at hO
    rcases hO with rfl | rfl
    · exact Finset.mem_image_of_mem _ hα
    · exact Finset.mem_image_of_mem _ hβ
  have hpair_card : ({orbit G α, orbit G β} : Finset (Finset F)).card = 2 := by
    simp [horbit_ne.symm]
  have horbits : 2 ≤ ((e2BadScalarSet G 4).image (fun y => orbit G y)).card := by
    calc
      2 = ({orbit G α, orbit G β} : Finset (Finset F)).card := hpair_card.symm
      _ ≤ ((e2BadScalarSet G 4).image (fun y => orbit G y)).card :=
        Finset.card_le_card hpair_subset
  exact group_card_lt_badScalarSet_card_of_two_orbits hG
    (zero_notMem_e2BadScalarSet G 4) (e2BadScalarSet_stable hG 4) horbits

/-- Two non-colliding product-form witnesses break the subgroup-size budget, using only subgroup
membership of the centres/factors plus `-1 ∈ G`. -/
theorem group_card_lt_e2BadScalarSet_card_of_two_quadT_mem_nonCollision {G : Finset F}
    (hG : FinSubgroup G) (hneg : (-1 : F) ∈ G) (hNC : Cd₀NonCollision G)
    {x x' t t' : F}
    (hxG : x ∈ G) (hx'G : x' ∈ G) (htG : t ∈ G) (ht'G : t' ∈ G)
    -- distinctness for `quadT x t`:
    (hx1 : x ≠ -x) (hx2 : x * t ≠ x) (hx3 : x * t ≠ -x) (hx4 : x * t⁻¹ ≠ x)
    (hx5 : x * t⁻¹ ≠ -x) (hx6 : x * t ≠ x * t⁻¹)
    -- distinctness for `quadT x' t'`:
    (hy1 : x' ≠ -x') (hy2 : x' * t' ≠ x') (hy3 : x' * t' ≠ -x')
    (hy4 : x' * t'⁻¹ ≠ x') (hy5 : x' * t'⁻¹ ≠ -x')
    (hy6 : x' * t' ≠ x' * t'⁻¹)
    (hc : (t + t⁻¹) ≠ 0) (hc' : (t' + t'⁻¹) ≠ 0)
    (hne : (t + t⁻¹) ≠ (t' + t'⁻¹)) :
    G.card < (e2BadScalarSet G 4).card :=
  group_card_lt_e2BadScalarSet_card_of_two_quadT_nonCollision hG hNC
    (quadT_subset_of_mem hG hneg hxG htG)
    (quadT_subset_of_mem hG hneg hx'G ht'G)
    hxG hx'G htG ht'G (ne_zero_of_mem_finSubgroup hG htG)
    (ne_zero_of_mem_finSubgroup hG ht'G) hx1 hx2 hx3 hx4 hx5 hx6 hy1 hy2 hy3
    hy4 hy5 hy6 hc hc' hne

/-- Sign-quotiented two-witness budget refuter using only subgroup membership of the
centres/factors plus `-1 ∈ G`. -/
theorem group_card_lt_e2BadScalarSet_card_of_two_quadT_mem_modSignNonCollision {G : Finset F}
    (hG : FinSubgroup G) (hneg : (-1 : F) ∈ G) (hNC : Cd₀NonCollisionModSign G)
    {x x' t t' : F}
    (hxG : x ∈ G) (hx'G : x' ∈ G) (htG : t ∈ G) (ht'G : t' ∈ G)
    -- distinctness for `quadT x t`:
    (hx1 : x ≠ -x) (hx2 : x * t ≠ x) (hx3 : x * t ≠ -x) (hx4 : x * t⁻¹ ≠ x)
    (hx5 : x * t⁻¹ ≠ -x) (hx6 : x * t ≠ x * t⁻¹)
    -- distinctness for `quadT x' t'`:
    (hy1 : x' ≠ -x') (hy2 : x' * t' ≠ x') (hy3 : x' * t' ≠ -x')
    (hy4 : x' * t'⁻¹ ≠ x') (hy5 : x' * t'⁻¹ ≠ -x')
    (hy6 : x' * t' ≠ x' * t'⁻¹)
    (hc : (t + t⁻¹) ≠ 0) (hc' : (t' + t'⁻¹) ≠ 0)
    (hne : (t + t⁻¹) ≠ (t' + t'⁻¹))
    (hsign : (t + t⁻¹) ≠ -(t' + t'⁻¹)) :
    G.card < (e2BadScalarSet G 4).card :=
  group_card_lt_e2BadScalarSet_card_of_two_quadT_modSignNonCollision hG hNC
    (quadT_subset_of_mem hG hneg hxG htG)
    (quadT_subset_of_mem hG hneg hx'G ht'G)
    hxG hx'G htG ht'G (ne_zero_of_mem_finSubgroup hG htG)
    (ne_zero_of_mem_finSubgroup hG ht'G) hx1 hx2 hx3 hx4 hx5 hx6 hy1 hy2 hy3
    hy4 hy5 hy6 hc hc' hne hsign

/-! ### Pairwise non-collision: the exact local residual needed by a two-witness scanner -/

/-- **Pairwise invariant non-collision.** This is the local residual actually needed to separate
two displayed width-4 witnesses: the second invariant is not in the `G`-orbit of the first.  It is
strictly weaker than the global `Cd₀NonCollisionModSign G`. -/
def InvariantPairNonCollision (G : Finset F) (t t' : F) : Prop :=
  ∀ u ∈ G, (t' + t'⁻¹) ≠ u * (t + t⁻¹)

/-- **The invariant ratio for a displayed pair of width-4 factors.**  When
`c = t + t⁻¹` is nonzero, `invariantRatio t t' = c'/c`; over `μ_n`, the pairwise
non-collision residual is exactly the statement that this ratio is not an `n`-th root. -/
noncomputable def invariantRatio (t t' : F) : F :=
  (t' + t'⁻¹) * (t + t⁻¹)⁻¹

open Classical in
/-- Exact failure form for `InvariantPairNonCollision`. -/
theorem not_invariantPairNonCollision_iff_exists_collision (G : Finset F) (t t' : F) :
    (¬ InvariantPairNonCollision (F := F) G t t') ↔
      ∃ u ∈ G, (t' + t'⁻¹) = u * (t + t⁻¹) := by
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    intro u huG hcollision
    exact hnone ⟨u, huG, hcollision⟩
  · rintro ⟨u, huG, hcollision⟩ hpair
    exact hpair u huG hcollision

/-- **Pairwise non-collision as a ratio-membership test.** If
`c = t + t⁻¹ ≠ 0`, then `c'` is not in the `G`-orbit of `c` iff the ratio `c'/c`
is not itself an element of `G`. -/
theorem invariantPairNonCollision_iff_ratio_notMem {G : Finset F} (_hG : FinSubgroup G)
    {t t' : F} (hc : (t + t⁻¹) ≠ 0) :
    InvariantPairNonCollision G t t' ↔ invariantRatio t t' ∉ G := by
  let c : F := t + t⁻¹
  let c' : F := t' + t'⁻¹
  have hc0 : c ≠ 0 := by simpa [c] using hc
  constructor
  · intro hpair hmem
    have hcollision : c' = (c' * c⁻¹) * c := by
      rw [mul_assoc, inv_mul_cancel₀ hc0, mul_one]
    exact hpair (c' * c⁻¹) (by simpa [invariantRatio, c, c'] using hmem)
      (by simpa [c, c'] using hcollision)
  · intro hratio u huG hcollision
    apply hratio
    have hratio_eq : invariantRatio t t' = u := by
      rw [invariantRatio, hcollision, mul_assoc, mul_inv_cancel₀ hc, mul_one]
    simpa [hratio_eq] using huG

/-- Failure of pairwise non-collision is exactly ratio membership. -/
theorem not_invariantPairNonCollision_iff_ratio_mem {G : Finset F} (hG : FinSubgroup G)
    {t t' : F} (hc : (t + t⁻¹) ≠ 0) :
    (¬ InvariantPairNonCollision G t t') ↔ invariantRatio t t' ∈ G := by
  rw [invariantPairNonCollision_iff_ratio_notMem hG hc]
  simp

/-- **Concrete `μ_n` pairwise non-collision test.** For the smooth-domain subgroup
`μ_n = nthRootsFinset n 1`, the local pairwise obstruction is the single algebraic inequality
`(c'/c)^n ≠ 1`. -/
theorem invariantPairNonCollision_nthRootsFinset_iff_ratio_pow_ne_one {n : ℕ}
    (hn : 0 < n) {t t' : F} (hc : (t + t⁻¹) ≠ 0) :
    InvariantPairNonCollision (Polynomial.nthRootsFinset n (1 : F)) t t' ↔
      invariantRatio t t' ^ n ≠ 1 := by
  rw [invariantPairNonCollision_iff_ratio_notMem
    (nthRootsFinset_finSubgroup (F := F) hn) hc]
  simp [Polynomial.mem_nthRootsFinset hn]

/-- Concrete failure form for the `μ_n` ratio test. -/
theorem not_invariantPairNonCollision_nthRootsFinset_iff_ratio_pow_eq_one {n : ℕ}
    (hn : 0 < n) {t t' : F} (hc : (t + t⁻¹) ≠ 0) :
    (¬ InvariantPairNonCollision (Polynomial.nthRootsFinset n (1 : F)) t t') ↔
      invariantRatio t t' ^ n = 1 := by
  rw [invariantPairNonCollision_nthRootsFinset_iff_ratio_pow_ne_one (F := F) hn hc]
  simp

/-- Pairwise invariant non-collision separates the corresponding bad-scalar orbits. -/
theorem orbits_distinct_of_pairNonCollision {G : Finset F} (hG : FinSubgroup G) {t t' : F}
    (hc : (t + t⁻¹) ≠ 0) (hc' : (t' + t'⁻¹) ≠ 0)
    (hpair : InvariantPairNonCollision G t t') :
    ¬ (∃ u ∈ G, -(t' + t'⁻¹)⁻¹ = u * (-(t + t⁻¹)⁻¹)) := by
  rw [orbit_collision_iff hG hc hc']
  rintro ⟨v, hvG, heq⟩
  exact hpair v hvG heq

/-- Pairwise invariant non-collision gives distinct bad-scalar orbits for two product-form
width-4 witnesses. -/
theorem badScalar_orbits_distinct_of_pairNonCollision {G : Finset F} (hG : FinSubgroup G)
    {x x' t t' : F}
    (hxG : x ∈ G) (hx'G : x' ∈ G)
    -- distinctness for `quadT x t`:
    (hx1 : x ≠ -x) (hx2 : x * t ≠ x) (hx3 : x * t ≠ -x) (hx4 : x * t⁻¹ ≠ x)
    (hx5 : x * t⁻¹ ≠ -x) (hx6 : x * t ≠ x * t⁻¹)
    -- distinctness for `quadT x' t'`:
    (hy1 : x' ≠ -x') (hy2 : x' * t' ≠ x') (hy3 : x' * t' ≠ -x')
    (hy4 : x' * t'⁻¹ ≠ x') (hy5 : x' * t'⁻¹ ≠ -x')
    (hy6 : x' * t' ≠ x' * t'⁻¹)
    (hc : (t + t⁻¹) ≠ 0) (hc' : (t' + t'⁻¹) ≠ 0)
    (hpair : InvariantPairNonCollision G t t') :
    ¬ (∃ u ∈ G, -(e1 (quadT x' t'))⁻¹ = u * (-(e1 (quadT x t))⁻¹)) := by
  intro hcoll
  obtain ⟨u, huG, heq⟩ := hcoll
  have hxne : x ≠ 0 := fun h => hG.zero_notMem (h ▸ hxG)
  have hx'ne : x' ≠ 0 := fun h => hG.zero_notMem (h ▸ hx'G)
  rw [badScalar_quadT x' hy1 hy2 hy3 hy4 hy5 hy6,
      badScalar_quadT x hx1 hx2 hx3 hx4 hx5 hx6] at heq
  apply orbits_distinct_of_pairNonCollision hG hc hc' hpair
  refine ⟨u * (x' * x⁻¹), hG.mul_mem _ huG _ (hG.mul_mem _ hx'G _ (hG.inv_mem _ hxG)), ?_⟩
  have key : -(t' + t'⁻¹)⁻¹ = x' * (u * (x⁻¹ * -(t + t⁻¹)⁻¹)) := by
    rw [← heq, ← mul_assoc, mul_inv_cancel₀ hx'ne, one_mul]
  rw [key]; ring

/-- **Pairwise two-witness budget refuter.** A local invariant non-collision certificate for the
two displayed product-form witnesses is enough to force two full bad-scalar orbits in the concrete
image. -/
theorem group_card_lt_e2BadScalarSet_card_of_two_quadT_pairNonCollision {G : Finset F}
    (hG : FinSubgroup G) {x x' t t' : F}
    (hsub : quadT x t ⊆ G) (hsub' : quadT x' t' ⊆ G)
    (hxG : x ∈ G) (hx'G : x' ∈ G)
    (ht0 : t ≠ 0) (ht'0 : t' ≠ 0)
    -- distinctness for `quadT x t`:
    (hx1 : x ≠ -x) (hx2 : x * t ≠ x) (hx3 : x * t ≠ -x) (hx4 : x * t⁻¹ ≠ x)
    (hx5 : x * t⁻¹ ≠ -x) (hx6 : x * t ≠ x * t⁻¹)
    -- distinctness for `quadT x' t'`:
    (hy1 : x' ≠ -x') (hy2 : x' * t' ≠ x') (hy3 : x' * t' ≠ -x')
    (hy4 : x' * t'⁻¹ ≠ x') (hy5 : x' * t'⁻¹ ≠ -x')
    (hy6 : x' * t' ≠ x' * t'⁻¹)
    (hc : (t + t⁻¹) ≠ 0) (hc' : (t' + t'⁻¹) ≠ 0)
    (hpair : InvariantPairNonCollision G t t') :
    G.card < (e2BadScalarSet G 4).card := by
  classical
  let α : F := -(e1 (quadT x t))⁻¹
  let β : F := -(e1 (quadT x' t'))⁻¹
  have hα : α ∈ e2BadScalarSet G 4 := by
    dsimp [α]
    rw [badScalar_quadT x hx1 hx2 hx3 hx4 hx5 hx6]
    exact badScalar_quadT_mem_e2BadScalarSet hsub ht0 hx1 hx2 hx3 hx4 hx5 hx6 hc
  have hβ : β ∈ e2BadScalarSet G 4 := by
    dsimp [β]
    rw [badScalar_quadT x' hy1 hy2 hy3 hy4 hy5 hy6]
    exact badScalar_quadT_mem_e2BadScalarSet hsub' ht'0 hy1 hy2 hy3 hy4 hy5 hy6 hc'
  have hnotcoll : ¬ (∃ u ∈ G, β = u * α) := by
    dsimp [α, β]
    exact badScalar_orbits_distinct_of_pairNonCollision hG hxG hx'G
      hx1 hx2 hx3 hx4 hx5 hx6 hy1 hy2 hy3 hy4 hy5 hy6 hc hc' hpair
  have horbit_ne : orbit G α ≠ orbit G β := by
    intro heq
    have hmem : β ∈ orbit G α := by
      simpa [← heq] using self_mem_orbit hG β
    unfold orbit at hmem
    rw [Finset.mem_image] at hmem
    obtain ⟨u, huG, hmul⟩ := hmem
    exact hnotcoll ⟨u, huG, hmul.symm⟩
  exact group_card_lt_badScalarSet_card_of_distinct_orbits hG
    (zero_notMem_e2BadScalarSet G 4) (e2BadScalarSet_stable hG 4) hα hβ horbit_ne

/-- Pairwise two-witness budget refuter using only subgroup membership of the centres/factors plus
`-1 ∈ G`. -/
theorem group_card_lt_e2BadScalarSet_card_of_two_quadT_mem_pairNonCollision {G : Finset F}
    (hG : FinSubgroup G) (hneg : (-1 : F) ∈ G) {x x' t t' : F}
    (hxG : x ∈ G) (hx'G : x' ∈ G) (htG : t ∈ G) (ht'G : t' ∈ G)
    -- distinctness for `quadT x t`:
    (hx1 : x ≠ -x) (hx2 : x * t ≠ x) (hx3 : x * t ≠ -x) (hx4 : x * t⁻¹ ≠ x)
    (hx5 : x * t⁻¹ ≠ -x) (hx6 : x * t ≠ x * t⁻¹)
    -- distinctness for `quadT x' t'`:
    (hy1 : x' ≠ -x') (hy2 : x' * t' ≠ x') (hy3 : x' * t' ≠ -x')
    (hy4 : x' * t'⁻¹ ≠ x') (hy5 : x' * t'⁻¹ ≠ -x')
    (hy6 : x' * t' ≠ x' * t'⁻¹)
    (hc : (t + t⁻¹) ≠ 0) (hc' : (t' + t'⁻¹) ≠ 0)
    (hpair : InvariantPairNonCollision G t t') :
    G.card < (e2BadScalarSet G 4).card :=
  group_card_lt_e2BadScalarSet_card_of_two_quadT_pairNonCollision hG
    (quadT_subset_of_mem hG hneg hxG htG)
    (quadT_subset_of_mem hG hneg hx'G ht'G)
    hxG hx'G (ne_zero_of_mem_finSubgroup hG htG)
    (ne_zero_of_mem_finSubgroup hG ht'G) hx1 hx2 hx3 hx4 hx5 hx6 hy1 hy2 hy3
    hy4 hy5 hy6 hc hc' hpair

/-! ## Part 5 — primitive-root plumbing for fixed width-4 witnesses -/

/-- A primitive `n`-th root lies in the concrete `μ_n` finset. -/
theorem primRoot_mem_nthRootsFinset {n : ℕ} (hn : 0 < n) {ζ : F}
    (hζ : IsPrimitiveRoot ζ n) :
    ζ ∈ Polynomial.nthRootsFinset n (1 : F) := by
  rw [Polynomial.mem_nthRootsFinset hn]
  exact hζ.pow_eq_one

/-- Powers of a primitive `n`-th root lie in `μ_n`. -/
theorem primRoot_pow_mem_nthRootsFinset {n k : ℕ} (hn : 0 < n) {ζ : F}
    (hζ : IsPrimitiveRoot ζ n) :
    ζ ^ k ∈ Polynomial.nthRootsFinset n (1 : F) := by
  rw [Polynomial.mem_nthRootsFinset hn]
  rw [← pow_mul, Nat.mul_comm, pow_mul, hζ.pow_eq_one, one_pow]

/-- A primitive root in a field is nonzero. -/
theorem primRoot_ne_zero {n : ℕ} (hn : 0 < n) {ζ : F} (hζ : IsPrimitiveRoot ζ n) :
    ζ ≠ 0 :=
  Polynomial.ne_zero_of_mem_nthRootsFinset one_ne_zero (primRoot_mem_nthRootsFinset hn hζ)

/-- Low nonzero powers below the primitive order are not `1`. -/
theorem primRoot_pow_ne_one_of_lt {n k : ℕ} {ζ : F} (hζ : IsPrimitiveRoot ζ n)
    (hk0 : k ≠ 0) (hklt : k < n) : ζ ^ k ≠ 1 :=
  hζ.pow_ne_one_of_pos_of_lt hk0 hklt

/-- If `2k < n`, a primitive `n`-th root cannot have `ζ^k = -1`. -/
theorem primRoot_pow_ne_neg_one_of_two_mul_lt {n k : ℕ} {ζ : F}
    (hζ : IsPrimitiveRoot ζ n) (hk0 : k ≠ 0) (hklt : k * 2 < n) :
    ζ ^ k ≠ -1 := by
  intro h
  have hpow : ζ ^ (k * 2) = 1 := by
    rw [pow_mul ζ k 2, h]
    ring
  exact hζ.pow_ne_one_of_pos_of_lt (by omega : k * 2 ≠ 0) hklt hpow

/-- If `2k < n`, the power `ζ^k` is not its own inverse. -/
theorem primRoot_pow_ne_inv_of_two_mul_lt {n k : ℕ} (hn : 0 < n) {ζ : F}
    (hζ : IsPrimitiveRoot ζ n) (hk0 : k ≠ 0) (hklt : k * 2 < n) :
    ζ ^ k ≠ (ζ ^ k)⁻¹ := by
  intro h
  have hz0 : ζ ^ k ≠ 0 := pow_ne_zero k (primRoot_ne_zero hn hζ)
  have hpow : ζ ^ (k * 2) = 1 := by
    rw [pow_mul ζ k 2, pow_two]
    nth_rw 2 [h]
    rw [mul_inv_cancel₀ hz0]
  exact hζ.pow_ne_one_of_pos_of_lt (by omega : k * 2 ≠ 0) hklt hpow

/-- If `4k < n`, the width-4 invariant `ζ^k + (ζ^k)⁻¹` is nonzero. -/
theorem primRoot_pow_add_inv_ne_zero_of_four_mul_lt {n k : ℕ} (hn : 0 < n) {ζ : F}
    (hζ : IsPrimitiveRoot ζ n) (hk0 : k ≠ 0) (hklt : k * 4 < n) :
    ζ ^ k + (ζ ^ k)⁻¹ ≠ 0 := by
  intro h
  let z : F := ζ ^ k
  have hz0 : z ≠ 0 := pow_ne_zero k (primRoot_ne_zero hn hζ)
  have hz2 : z ^ 2 = -1 := by
    dsimp [z] at h hz0 ⊢
    field_simp [hz0] at h
    linear_combination h
  have hz4 : z ^ 4 = 1 := by
    rw [show z ^ 4 = (z ^ 2) ^ 2 by ring, hz2]
    ring
  have hpow : ζ ^ (k * 4) = 1 := by
    rw [pow_mul ζ k 4]
    exact hz4
  exact hζ.pow_ne_one_of_pos_of_lt (by omega : k * 4 ≠ 0) hklt hpow

/-- In a field, the half-power of a primitive even-order root is `-1`. -/
theorem primRoot_pow_half_eq_neg_one_of_even {n h : ℕ} {ζ : F}
    (hζ : IsPrimitiveRoot ζ n) (hnh : n = 2 * h) (hh : h ≠ 0) : ζ ^ h = -1 := by
  have hsq : ζ ^ h * ζ ^ h = 1 := by
    rw [← pow_add, ← two_mul, ← hnh]
    exact hζ.pow_eq_one
  rcases mul_self_eq_one_iff.mp hsq with h1 | h1
  · exact absurd h1 (hζ.pow_ne_one_of_pos_of_lt hh (by omega))
  · exact h1

/-- A field carrying a primitive even-order root has `1 ≠ -1`. -/
theorem one_ne_neg_one_of_primRoot_even {n h : ℕ} {ζ : F}
    (hζ : IsPrimitiveRoot ζ n) (hnh : n = 2 * h) (hh : h ≠ 0) : (1 : F) ≠ -1 := by
  intro hchar
  have hz : ζ ^ h = 1 := by
    rw [primRoot_pow_half_eq_neg_one_of_even hζ hnh hh]
    exact hchar.symm
  exact hζ.pow_ne_one_of_pos_of_lt hh (by omega) hz

/-- The two canonical invariants `ζ + ζ⁻¹` and `ζ² + ζ⁻²` are distinct when `3 < n`. -/
theorem primRoot_add_inv_ne_sq_add_inv {n : ℕ} (hn : 0 < n) {ζ : F}
    (hζ : IsPrimitiveRoot ζ n) (h1lt : 1 < n) (h3lt : 3 < n) :
    ζ + ζ⁻¹ ≠ ζ ^ 2 + (ζ ^ 2)⁻¹ := by
  intro h
  have hz0 : ζ ≠ 0 := primRoot_ne_zero hn hζ
  have hpoly : ζ ^ 4 - ζ ^ 3 - ζ + 1 = 0 := by
    field_simp [hz0] at h
    linear_combination -h
  have hfac : (ζ - 1) * (ζ ^ 3 - 1) = 0 := by
    linear_combination hpoly
  rcases mul_eq_zero.mp hfac with hleft | hright
  · have hz1 : ζ ^ 1 = 1 := by
      rw [pow_one]
      linear_combination hleft
    exact hζ.pow_ne_one_of_pos_of_lt one_ne_zero h1lt hz1
  · exact hζ.pow_ne_one_of_pos_of_lt (by norm_num : (3 : ℕ) ≠ 0) h3lt
      (by linear_combination hright)

/-- The two canonical invariants are also distinct after the sign quotient when `6 < n`. -/
theorem primRoot_add_inv_ne_neg_sq_add_inv {n : ℕ} (hn : 0 < n) {ζ : F}
    (hζ : IsPrimitiveRoot ζ n) (h2lt : 2 < n) (h6lt : 6 < n) :
    ζ + ζ⁻¹ ≠ -(ζ ^ 2 + (ζ ^ 2)⁻¹) := by
  intro h
  have hz0 : ζ ≠ 0 := primRoot_ne_zero hn hζ
  have hpoly : ζ ^ 4 + ζ ^ 3 + ζ + 1 = 0 := by
    field_simp [hz0] at h
    linear_combination h
  have hfac : (ζ + 1) * (ζ ^ 3 + 1) = 0 := by
    linear_combination hpoly
  rcases mul_eq_zero.mp hfac with hleft | hright
  · have hz2 : ζ ^ 2 = 1 := by
      rw [show ζ ^ 2 = (ζ + 1) * (ζ - 1) + 1 by ring]
      rw [hleft]
      ring
    exact hζ.pow_ne_one_of_pos_of_lt (by norm_num : (2 : ℕ) ≠ 0) h2lt hz2
  · have hz6 : ζ ^ 6 = 1 := by
      have hz3 : ζ ^ 3 = -1 := by linear_combination hright
      rw [show ζ ^ 6 = (ζ ^ 3) ^ 2 by ring, hz3]
      ring
    exact hζ.pow_ne_one_of_pos_of_lt (by norm_num : (6 : ℕ) ≠ 0) h6lt hz6

/-! ### Complex fixed-pair non-collision -/

/-- A real complex `n`-th root of unity is `1` or `-1`. -/
theorem complex_root_of_unity_real_eq_one_or_neg_one {n : ℕ} (hn : n ≠ 0) {u : ℂ}
    (hu : u ^ n = 1) (huim : u.im = 0) : u = 1 ∨ u = -1 := by
  have hnorm : ‖u‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hu hn
  have hns : Complex.normSq u = 1 := by
    rw [Complex.normSq_eq_norm_sq, hnorm]
    norm_num
  rw [Complex.normSq_apply, huim] at hns
  have hfac : (u.re - 1) * (u.re + 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp hfac with h1 | hneg
  · left
    apply Complex.ext
    · simp
      nlinarith
    · simpa using huim
  · right
    apply Complex.ext
    · simp
      nlinarith
    · simp [huim]

/-- The real cyclotomic invariant `z + z⁻¹` has zero imaginary part for a complex root of unity. -/
theorem complex_root_add_inv_im_eq_zero {n : ℕ} (hn : n ≠ 0) {z : ℂ}
    (hz : z ^ n = 1) : (z + z⁻¹).im = 0 := by
  have hnorm : ‖z‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hz hn
  rw [Complex.inv_eq_conj hnorm]
  simp

/-- Over `ℂ`, the canonical primitive pair `ζ, ζ²` has no invariant collision with an `n`-th
root scalar once `8 < n`. Any collision scalar would be real, hence `±1`, and the two
field-general primitive-root separation lemmas rule those cases out. -/
theorem invariantPairNonCollision_complex_primitive_zeta_sq {n : ℕ} {ζ : ℂ}
    (hn : 0 < n) (hn8 : 8 < n) (hζ : IsPrimitiveRoot ζ n) :
    InvariantPairNonCollision (Polynomial.nthRootsFinset n (1 : ℂ)) ζ (ζ ^ 2) := by
  intro u hu hcollision
  have hc : ζ + ζ⁻¹ ≠ 0 := by
    simpa [pow_one] using
      primRoot_pow_add_inv_ne_zero_of_four_mul_lt (F := ℂ) (ζ := ζ) (k := 1) hn hζ
        one_ne_zero (by omega : 1 * 4 < n)
  have hcim : (ζ + ζ⁻¹).im = 0 :=
    complex_root_add_inv_im_eq_zero hn.ne' hζ.pow_eq_one
  have hζ2pow : (ζ ^ 2) ^ n = 1 := by
    rw [← pow_mul]
    rw [mul_comm]
    rw [pow_mul, hζ.pow_eq_one]
    simp
  have hc'im : (ζ ^ 2 + (ζ ^ 2)⁻¹).im = 0 :=
    complex_root_add_inv_im_eq_zero hn.ne' hζ2pow
  have hcre : (ζ + ζ⁻¹).re ≠ 0 := by
    intro hcre
    apply hc
    apply Complex.ext
    · simpa using hcre
    · simpa using hcim
  have huPow : u ^ n = 1 := by
    simpa [Polynomial.mem_nthRootsFinset hn] using hu
  have huim : u.im = 0 := by
    have him : u.im * (ζ + ζ⁻¹).re = 0 := by
      have h := congrArg Complex.im hcollision
      rw [hc'im, Complex.mul_im, hcim, mul_zero, zero_add] at h
      exact h.symm
    exact (mul_eq_zero.mp him).resolve_right hcre
  rcases complex_root_of_unity_real_eq_one_or_neg_one hn.ne' huPow huim with rfl | rfl
  · have hne : ζ + ζ⁻¹ ≠ ζ ^ 2 + (ζ ^ 2)⁻¹ :=
      primRoot_add_inv_ne_sq_add_inv (F := ℂ) hn hζ (by omega : 1 < n) (by omega : 3 < n)
    exact hne (by
      rw [hcollision]
      ring)
  · have hsign : ζ + ζ⁻¹ ≠ -(ζ ^ 2 + (ζ ^ 2)⁻¹) :=
      primRoot_add_inv_ne_neg_sq_add_inv (F := ℂ) hn hζ (by omega : 2 < n)
        (by omega : 6 < n)
    exact hsign (by
      rw [hcollision]
      ring)

/-- **Concrete `μ_n` width-4 refuter.** For the actual smooth-domain subgroup
`μ_n = nthRootsFinset n 1`, two non-colliding product-form width-4 witnesses force the concrete
`e₂ = 0` bad-scalar image to exceed the literal `n` budget. -/
theorem n_lt_e2BadScalarSet_mu_card_of_two_quadT_nonCollision {n : ℕ} {ζ x x' t t' : F}
    (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n)
    (hNC : Cd₀NonCollision (Polynomial.nthRootsFinset n (1 : F)))
    (hsub : quadT x t ⊆ Polynomial.nthRootsFinset n (1 : F))
    (hsub' : quadT x' t' ⊆ Polynomial.nthRootsFinset n (1 : F))
    (htG : t ∈ Polynomial.nthRootsFinset n (1 : F))
    (ht'G : t' ∈ Polynomial.nthRootsFinset n (1 : F))
    (ht0 : t ≠ 0) (ht'0 : t' ≠ 0)
    -- distinctness for `quadT x t`:
    (hx1 : x ≠ -x) (hx2 : x * t ≠ x) (hx3 : x * t ≠ -x) (hx4 : x * t⁻¹ ≠ x)
    (hx5 : x * t⁻¹ ≠ -x) (hx6 : x * t ≠ x * t⁻¹)
    -- distinctness for `quadT x' t'`:
    (hy1 : x' ≠ -x') (hy2 : x' * t' ≠ x') (hy3 : x' * t' ≠ -x')
    (hy4 : x' * t'⁻¹ ≠ x') (hy5 : x' * t'⁻¹ ≠ -x')
    (hy6 : x' * t' ≠ x' * t'⁻¹)
    (hc : (t + t⁻¹) ≠ 0) (hc' : (t' + t'⁻¹) ≠ 0)
    (hne : (t + t⁻¹) ≠ (t' + t'⁻¹)) :
    n < (e2BadScalarSet (Polynomial.nthRootsFinset n (1 : F)) 4).card := by
  have hxG : x ∈ Polynomial.nthRootsFinset n (1 : F) := hsub (by simp [quadT])
  have hx'G : x' ∈ Polynomial.nthRootsFinset n (1 : F) := hsub' (by simp [quadT])
  simpa [hζ.card_nthRootsFinset] using
    (group_card_lt_e2BadScalarSet_card_of_two_quadT_nonCollision
      (F := F) (G := Polynomial.nthRootsFinset n (1 : F))
      (nthRootsFinset_finSubgroup (F := F) hn) hNC hsub hsub' hxG hx'G htG ht'G
      ht0 ht'0 hx1 hx2 hx3 hx4 hx5 hx6 hy1 hy2 hy3 hy4 hy5 hy6 hc hc' hne)

/-- Concrete `μ_n` width-4 refuter under the repaired sign-quotiented non-collision residual. -/
theorem n_lt_e2BadScalarSet_mu_card_of_two_quadT_modSignNonCollision
    {n : ℕ} {ζ x x' t t' : F}
    (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n)
    (hNC : Cd₀NonCollisionModSign (Polynomial.nthRootsFinset n (1 : F)))
    (hsub : quadT x t ⊆ Polynomial.nthRootsFinset n (1 : F))
    (hsub' : quadT x' t' ⊆ Polynomial.nthRootsFinset n (1 : F))
    (htG : t ∈ Polynomial.nthRootsFinset n (1 : F))
    (ht'G : t' ∈ Polynomial.nthRootsFinset n (1 : F))
    (ht0 : t ≠ 0) (ht'0 : t' ≠ 0)
    -- distinctness for `quadT x t`:
    (hx1 : x ≠ -x) (hx2 : x * t ≠ x) (hx3 : x * t ≠ -x) (hx4 : x * t⁻¹ ≠ x)
    (hx5 : x * t⁻¹ ≠ -x) (hx6 : x * t ≠ x * t⁻¹)
    -- distinctness for `quadT x' t'`:
    (hy1 : x' ≠ -x') (hy2 : x' * t' ≠ x') (hy3 : x' * t' ≠ -x')
    (hy4 : x' * t'⁻¹ ≠ x') (hy5 : x' * t'⁻¹ ≠ -x')
    (hy6 : x' * t' ≠ x' * t'⁻¹)
    (hc : (t + t⁻¹) ≠ 0) (hc' : (t' + t'⁻¹) ≠ 0)
    (hne : (t + t⁻¹) ≠ (t' + t'⁻¹))
    (hsign : (t + t⁻¹) ≠ -(t' + t'⁻¹)) :
    n < (e2BadScalarSet (Polynomial.nthRootsFinset n (1 : F)) 4).card := by
  have hxG : x ∈ Polynomial.nthRootsFinset n (1 : F) := hsub (by simp [quadT])
  have hx'G : x' ∈ Polynomial.nthRootsFinset n (1 : F) := hsub' (by simp [quadT])
  simpa [hζ.card_nthRootsFinset] using
    (group_card_lt_e2BadScalarSet_card_of_two_quadT_modSignNonCollision
      (F := F) (G := Polynomial.nthRootsFinset n (1 : F))
      (nthRootsFinset_finSubgroup (F := F) hn) hNC hsub hsub' hxG hx'G htG ht'G
      ht0 ht'0 hx1 hx2 hx3 hx4 hx5 hx6 hy1 hy2 hy3 hy4 hy5 hy6 hc hc' hne
      hsign)

/-- Concrete `μ_n` width-4 refuter using membership of `x,x',t,t'` plus `-1 ∈ μ_n`, instead of
manual subset proofs for both product-form quadruples. -/
theorem n_lt_e2BadScalarSet_mu_card_of_two_quadT_mem_nonCollision
    {n : ℕ} {ζ x x' t t' : F}
    (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n)
    (hneg : (-1 : F) ∈ Polynomial.nthRootsFinset n (1 : F))
    (hNC : Cd₀NonCollision (Polynomial.nthRootsFinset n (1 : F)))
    (hxG : x ∈ Polynomial.nthRootsFinset n (1 : F))
    (hx'G : x' ∈ Polynomial.nthRootsFinset n (1 : F))
    (htG : t ∈ Polynomial.nthRootsFinset n (1 : F))
    (ht'G : t' ∈ Polynomial.nthRootsFinset n (1 : F))
    -- distinctness for `quadT x t`:
    (hx1 : x ≠ -x) (hx2 : x * t ≠ x) (hx3 : x * t ≠ -x) (hx4 : x * t⁻¹ ≠ x)
    (hx5 : x * t⁻¹ ≠ -x) (hx6 : x * t ≠ x * t⁻¹)
    -- distinctness for `quadT x' t'`:
    (hy1 : x' ≠ -x') (hy2 : x' * t' ≠ x') (hy3 : x' * t' ≠ -x')
    (hy4 : x' * t'⁻¹ ≠ x') (hy5 : x' * t'⁻¹ ≠ -x')
    (hy6 : x' * t' ≠ x' * t'⁻¹)
    (hc : (t + t⁻¹) ≠ 0) (hc' : (t' + t'⁻¹) ≠ 0)
    (hne : (t + t⁻¹) ≠ (t' + t'⁻¹)) :
    n < (e2BadScalarSet (Polynomial.nthRootsFinset n (1 : F)) 4).card := by
  simpa [hζ.card_nthRootsFinset] using
    (group_card_lt_e2BadScalarSet_card_of_two_quadT_mem_nonCollision
      (F := F) (G := Polynomial.nthRootsFinset n (1 : F))
      (nthRootsFinset_finSubgroup (F := F) hn) hneg hNC hxG hx'G htG ht'G
      hx1 hx2 hx3 hx4 hx5 hx6 hy1 hy2 hy3 hy4 hy5 hy6 hc hc' hne)

/-- Concrete `μ_n` width-4 refuter under the repaired residual, using membership of
`x,x',t,t'` plus `-1 ∈ μ_n`. -/
theorem n_lt_e2BadScalarSet_mu_card_of_two_quadT_mem_modSignNonCollision
    {n : ℕ} {ζ x x' t t' : F}
    (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n)
    (hneg : (-1 : F) ∈ Polynomial.nthRootsFinset n (1 : F))
    (hNC : Cd₀NonCollisionModSign (Polynomial.nthRootsFinset n (1 : F)))
    (hxG : x ∈ Polynomial.nthRootsFinset n (1 : F))
    (hx'G : x' ∈ Polynomial.nthRootsFinset n (1 : F))
    (htG : t ∈ Polynomial.nthRootsFinset n (1 : F))
    (ht'G : t' ∈ Polynomial.nthRootsFinset n (1 : F))
    -- distinctness for `quadT x t`:
    (hx1 : x ≠ -x) (hx2 : x * t ≠ x) (hx3 : x * t ≠ -x) (hx4 : x * t⁻¹ ≠ x)
    (hx5 : x * t⁻¹ ≠ -x) (hx6 : x * t ≠ x * t⁻¹)
    -- distinctness for `quadT x' t'`:
    (hy1 : x' ≠ -x') (hy2 : x' * t' ≠ x') (hy3 : x' * t' ≠ -x')
    (hy4 : x' * t'⁻¹ ≠ x') (hy5 : x' * t'⁻¹ ≠ -x')
    (hy6 : x' * t' ≠ x' * t'⁻¹)
    (hc : (t + t⁻¹) ≠ 0) (hc' : (t' + t'⁻¹) ≠ 0)
    (hne : (t + t⁻¹) ≠ (t' + t'⁻¹))
    (hsign : (t + t⁻¹) ≠ -(t' + t'⁻¹)) :
    n < (e2BadScalarSet (Polynomial.nthRootsFinset n (1 : F)) 4).card := by
  simpa [hζ.card_nthRootsFinset] using
    (group_card_lt_e2BadScalarSet_card_of_two_quadT_mem_modSignNonCollision
      (F := F) (G := Polynomial.nthRootsFinset n (1 : F))
      (nthRootsFinset_finSubgroup (F := F) hn) hneg hNC hxG hx'G htG ht'G
      hx1 hx2 hx3 hx4 hx5 hx6 hy1 hy2 hy3 hy4 hy5 hy6 hc hc' hne hsign)

/-- **Concrete `μ_n` scanner-failure form.** The same two-witness certificate refutes the literal
`n` budget for the width-4 `e₂ = 0` bad-scalar image over `μ_n`. -/
theorem not_e2BadScalarSet_mu_card_le_n_of_two_quadT_nonCollision {n : ℕ} {ζ x x' t t' : F}
    (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n)
    (hNC : Cd₀NonCollision (Polynomial.nthRootsFinset n (1 : F)))
    (hsub : quadT x t ⊆ Polynomial.nthRootsFinset n (1 : F))
    (hsub' : quadT x' t' ⊆ Polynomial.nthRootsFinset n (1 : F))
    (htG : t ∈ Polynomial.nthRootsFinset n (1 : F))
    (ht'G : t' ∈ Polynomial.nthRootsFinset n (1 : F))
    (ht0 : t ≠ 0) (ht'0 : t' ≠ 0)
    -- distinctness for `quadT x t`:
    (hx1 : x ≠ -x) (hx2 : x * t ≠ x) (hx3 : x * t ≠ -x) (hx4 : x * t⁻¹ ≠ x)
    (hx5 : x * t⁻¹ ≠ -x) (hx6 : x * t ≠ x * t⁻¹)
    -- distinctness for `quadT x' t'`:
    (hy1 : x' ≠ -x') (hy2 : x' * t' ≠ x') (hy3 : x' * t' ≠ -x')
    (hy4 : x' * t'⁻¹ ≠ x') (hy5 : x' * t'⁻¹ ≠ -x')
    (hy6 : x' * t' ≠ x' * t'⁻¹)
    (hc : (t + t⁻¹) ≠ 0) (hc' : (t' + t'⁻¹) ≠ 0)
    (hne : (t + t⁻¹) ≠ (t' + t'⁻¹)) :
    ¬ (e2BadScalarSet (Polynomial.nthRootsFinset n (1 : F)) 4).card ≤ n :=
  not_le.mpr
    (n_lt_e2BadScalarSet_mu_card_of_two_quadT_nonCollision hn hζ hNC hsub hsub'
      htG ht'G ht0 ht'0 hx1 hx2 hx3 hx4 hx5 hx6 hy1 hy2 hy3 hy4 hy5 hy6 hc hc'
      hne)

/-- Concrete `μ_n` scanner-failure form under the repaired sign-quotiented residual. -/
theorem not_e2BadScalarSet_mu_card_le_n_of_two_quadT_modSignNonCollision
    {n : ℕ} {ζ x x' t t' : F}
    (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n)
    (hNC : Cd₀NonCollisionModSign (Polynomial.nthRootsFinset n (1 : F)))
    (hsub : quadT x t ⊆ Polynomial.nthRootsFinset n (1 : F))
    (hsub' : quadT x' t' ⊆ Polynomial.nthRootsFinset n (1 : F))
    (htG : t ∈ Polynomial.nthRootsFinset n (1 : F))
    (ht'G : t' ∈ Polynomial.nthRootsFinset n (1 : F))
    (ht0 : t ≠ 0) (ht'0 : t' ≠ 0)
    -- distinctness for `quadT x t`:
    (hx1 : x ≠ -x) (hx2 : x * t ≠ x) (hx3 : x * t ≠ -x) (hx4 : x * t⁻¹ ≠ x)
    (hx5 : x * t⁻¹ ≠ -x) (hx6 : x * t ≠ x * t⁻¹)
    -- distinctness for `quadT x' t'`:
    (hy1 : x' ≠ -x') (hy2 : x' * t' ≠ x') (hy3 : x' * t' ≠ -x')
    (hy4 : x' * t'⁻¹ ≠ x') (hy5 : x' * t'⁻¹ ≠ -x')
    (hy6 : x' * t' ≠ x' * t'⁻¹)
    (hc : (t + t⁻¹) ≠ 0) (hc' : (t' + t'⁻¹) ≠ 0)
    (hne : (t + t⁻¹) ≠ (t' + t'⁻¹))
    (hsign : (t + t⁻¹) ≠ -(t' + t'⁻¹)) :
    ¬ (e2BadScalarSet (Polynomial.nthRootsFinset n (1 : F)) 4).card ≤ n :=
  not_le.mpr
    (n_lt_e2BadScalarSet_mu_card_of_two_quadT_modSignNonCollision
      hn hζ hNC hsub hsub' htG ht'G ht0 ht'0 hx1 hx2 hx3 hx4 hx5 hx6 hy1
      hy2 hy3 hy4 hy5 hy6 hc hc' hne hsign)

/-- Concrete `μ_n` scanner-failure form using subgroup membership plus `-1 ∈ μ_n`. -/
theorem not_e2BadScalarSet_mu_card_le_n_of_two_quadT_mem_nonCollision
    {n : ℕ} {ζ x x' t t' : F}
    (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n)
    (hneg : (-1 : F) ∈ Polynomial.nthRootsFinset n (1 : F))
    (hNC : Cd₀NonCollision (Polynomial.nthRootsFinset n (1 : F)))
    (hxG : x ∈ Polynomial.nthRootsFinset n (1 : F))
    (hx'G : x' ∈ Polynomial.nthRootsFinset n (1 : F))
    (htG : t ∈ Polynomial.nthRootsFinset n (1 : F))
    (ht'G : t' ∈ Polynomial.nthRootsFinset n (1 : F))
    -- distinctness for `quadT x t`:
    (hx1 : x ≠ -x) (hx2 : x * t ≠ x) (hx3 : x * t ≠ -x) (hx4 : x * t⁻¹ ≠ x)
    (hx5 : x * t⁻¹ ≠ -x) (hx6 : x * t ≠ x * t⁻¹)
    -- distinctness for `quadT x' t'`:
    (hy1 : x' ≠ -x') (hy2 : x' * t' ≠ x') (hy3 : x' * t' ≠ -x')
    (hy4 : x' * t'⁻¹ ≠ x') (hy5 : x' * t'⁻¹ ≠ -x')
    (hy6 : x' * t' ≠ x' * t'⁻¹)
    (hc : (t + t⁻¹) ≠ 0) (hc' : (t' + t'⁻¹) ≠ 0)
    (hne : (t + t⁻¹) ≠ (t' + t'⁻¹)) :
    ¬ (e2BadScalarSet (Polynomial.nthRootsFinset n (1 : F)) 4).card ≤ n :=
  not_le.mpr
    (n_lt_e2BadScalarSet_mu_card_of_two_quadT_mem_nonCollision
      hn hζ hneg hNC hxG hx'G htG ht'G hx1 hx2 hx3 hx4 hx5 hx6 hy1 hy2 hy3 hy4
      hy5 hy6 hc hc' hne)

/-- Concrete `μ_n` scanner-failure form under the repaired residual, using subgroup membership
plus `-1 ∈ μ_n`. -/
theorem not_e2BadScalarSet_mu_card_le_n_of_two_quadT_mem_modSignNonCollision
    {n : ℕ} {ζ x x' t t' : F}
    (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n)
    (hneg : (-1 : F) ∈ Polynomial.nthRootsFinset n (1 : F))
    (hNC : Cd₀NonCollisionModSign (Polynomial.nthRootsFinset n (1 : F)))
    (hxG : x ∈ Polynomial.nthRootsFinset n (1 : F))
    (hx'G : x' ∈ Polynomial.nthRootsFinset n (1 : F))
    (htG : t ∈ Polynomial.nthRootsFinset n (1 : F))
    (ht'G : t' ∈ Polynomial.nthRootsFinset n (1 : F))
    -- distinctness for `quadT x t`:
    (hx1 : x ≠ -x) (hx2 : x * t ≠ x) (hx3 : x * t ≠ -x) (hx4 : x * t⁻¹ ≠ x)
    (hx5 : x * t⁻¹ ≠ -x) (hx6 : x * t ≠ x * t⁻¹)
    -- distinctness for `quadT x' t'`:
    (hy1 : x' ≠ -x') (hy2 : x' * t' ≠ x') (hy3 : x' * t' ≠ -x')
    (hy4 : x' * t'⁻¹ ≠ x') (hy5 : x' * t'⁻¹ ≠ -x')
    (hy6 : x' * t' ≠ x' * t'⁻¹)
    (hc : (t + t⁻¹) ≠ 0) (hc' : (t' + t'⁻¹) ≠ 0)
    (hne : (t + t⁻¹) ≠ (t' + t'⁻¹))
    (hsign : (t + t⁻¹) ≠ -(t' + t'⁻¹)) :
    ¬ (e2BadScalarSet (Polynomial.nthRootsFinset n (1 : F)) 4).card ≤ n :=
  not_le.mpr
    (n_lt_e2BadScalarSet_mu_card_of_two_quadT_mem_modSignNonCollision
      hn hζ hneg hNC hxG hx'G htG ht'G hx1 hx2 hx3 hx4 hx5 hx6 hy1 hy2 hy3
      hy4 hy5 hy6 hc hc' hne hsign)

/-- Concrete even-`μ_n` width-4 refuter using only membership of `x,x',t,t'`.  For even `n`,
the hypothesis `-1 ∈ μ_n` required by the membership wrapper is automatic. -/
theorem n_lt_e2BadScalarSet_mu_card_of_two_quadT_even_nonCollision
    {n : ℕ} {ζ x x' t t' : F}
    (hn : 0 < n) (heven : 2 ∣ n) (hζ : IsPrimitiveRoot ζ n)
    (hNC : Cd₀NonCollision (Polynomial.nthRootsFinset n (1 : F)))
    (hxG : x ∈ Polynomial.nthRootsFinset n (1 : F))
    (hx'G : x' ∈ Polynomial.nthRootsFinset n (1 : F))
    (htG : t ∈ Polynomial.nthRootsFinset n (1 : F))
    (ht'G : t' ∈ Polynomial.nthRootsFinset n (1 : F))
    -- distinctness for `quadT x t`:
    (hx1 : x ≠ -x) (hx2 : x * t ≠ x) (hx3 : x * t ≠ -x) (hx4 : x * t⁻¹ ≠ x)
    (hx5 : x * t⁻¹ ≠ -x) (hx6 : x * t ≠ x * t⁻¹)
    -- distinctness for `quadT x' t'`:
    (hy1 : x' ≠ -x') (hy2 : x' * t' ≠ x') (hy3 : x' * t' ≠ -x')
    (hy4 : x' * t'⁻¹ ≠ x') (hy5 : x' * t'⁻¹ ≠ -x')
    (hy6 : x' * t' ≠ x' * t'⁻¹)
    (hc : (t + t⁻¹) ≠ 0) (hc' : (t' + t'⁻¹) ≠ 0)
    (hne : (t + t⁻¹) ≠ (t' + t'⁻¹)) :
    n < (e2BadScalarSet (Polynomial.nthRootsFinset n (1 : F)) 4).card :=
  n_lt_e2BadScalarSet_mu_card_of_two_quadT_mem_nonCollision
    hn hζ (neg_one_mem_nthRootsFinset_of_even (F := F) hn heven) hNC
    hxG hx'G htG ht'G hx1 hx2 hx3 hx4 hx5 hx6 hy1 hy2 hy3 hy4 hy5 hy6 hc hc'
    hne

/-- Concrete even-`μ_n` width-4 refuter under the repaired sign-quotiented residual. -/
theorem n_lt_e2BadScalarSet_mu_card_of_two_quadT_even_modSignNonCollision
    {n : ℕ} {ζ x x' t t' : F}
    (hn : 0 < n) (heven : 2 ∣ n) (hζ : IsPrimitiveRoot ζ n)
    (hNC : Cd₀NonCollisionModSign (Polynomial.nthRootsFinset n (1 : F)))
    (hxG : x ∈ Polynomial.nthRootsFinset n (1 : F))
    (hx'G : x' ∈ Polynomial.nthRootsFinset n (1 : F))
    (htG : t ∈ Polynomial.nthRootsFinset n (1 : F))
    (ht'G : t' ∈ Polynomial.nthRootsFinset n (1 : F))
    -- distinctness for `quadT x t`:
    (hx1 : x ≠ -x) (hx2 : x * t ≠ x) (hx3 : x * t ≠ -x) (hx4 : x * t⁻¹ ≠ x)
    (hx5 : x * t⁻¹ ≠ -x) (hx6 : x * t ≠ x * t⁻¹)
    -- distinctness for `quadT x' t'`:
    (hy1 : x' ≠ -x') (hy2 : x' * t' ≠ x') (hy3 : x' * t' ≠ -x')
    (hy4 : x' * t'⁻¹ ≠ x') (hy5 : x' * t'⁻¹ ≠ -x')
    (hy6 : x' * t' ≠ x' * t'⁻¹)
    (hc : (t + t⁻¹) ≠ 0) (hc' : (t' + t'⁻¹) ≠ 0)
    (hne : (t + t⁻¹) ≠ (t' + t'⁻¹))
    (hsign : (t + t⁻¹) ≠ -(t' + t'⁻¹)) :
    n < (e2BadScalarSet (Polynomial.nthRootsFinset n (1 : F)) 4).card :=
  n_lt_e2BadScalarSet_mu_card_of_two_quadT_mem_modSignNonCollision
    hn hζ (neg_one_mem_nthRootsFinset_of_even (F := F) hn heven) hNC
    hxG hx'G htG ht'G hx1 hx2 hx3 hx4 hx5 hx6 hy1 hy2 hy3 hy4 hy5 hy6 hc hc'
    hne hsign

/-- Concrete even-`μ_n` scanner-failure form using only membership of `x,x',t,t'`. -/
theorem not_e2BadScalarSet_mu_card_le_n_of_two_quadT_even_nonCollision
    {n : ℕ} {ζ x x' t t' : F}
    (hn : 0 < n) (heven : 2 ∣ n) (hζ : IsPrimitiveRoot ζ n)
    (hNC : Cd₀NonCollision (Polynomial.nthRootsFinset n (1 : F)))
    (hxG : x ∈ Polynomial.nthRootsFinset n (1 : F))
    (hx'G : x' ∈ Polynomial.nthRootsFinset n (1 : F))
    (htG : t ∈ Polynomial.nthRootsFinset n (1 : F))
    (ht'G : t' ∈ Polynomial.nthRootsFinset n (1 : F))
    -- distinctness for `quadT x t`:
    (hx1 : x ≠ -x) (hx2 : x * t ≠ x) (hx3 : x * t ≠ -x) (hx4 : x * t⁻¹ ≠ x)
    (hx5 : x * t⁻¹ ≠ -x) (hx6 : x * t ≠ x * t⁻¹)
    -- distinctness for `quadT x' t'`:
    (hy1 : x' ≠ -x') (hy2 : x' * t' ≠ x') (hy3 : x' * t' ≠ -x')
    (hy4 : x' * t'⁻¹ ≠ x') (hy5 : x' * t'⁻¹ ≠ -x')
    (hy6 : x' * t' ≠ x' * t'⁻¹)
    (hc : (t + t⁻¹) ≠ 0) (hc' : (t' + t'⁻¹) ≠ 0)
    (hne : (t + t⁻¹) ≠ (t' + t'⁻¹)) :
    ¬ (e2BadScalarSet (Polynomial.nthRootsFinset n (1 : F)) 4).card ≤ n :=
  not_le.mpr
    (n_lt_e2BadScalarSet_mu_card_of_two_quadT_even_nonCollision
      hn heven hζ hNC hxG hx'G htG ht'G hx1 hx2 hx3 hx4 hx5 hx6 hy1 hy2 hy3
      hy4 hy5 hy6 hc hc' hne)

/-- Concrete even-`μ_n` scanner-failure form under the repaired sign-quotiented residual. -/
theorem not_e2BadScalarSet_mu_card_le_n_of_two_quadT_even_modSignNonCollision
    {n : ℕ} {ζ x x' t t' : F}
    (hn : 0 < n) (heven : 2 ∣ n) (hζ : IsPrimitiveRoot ζ n)
    (hNC : Cd₀NonCollisionModSign (Polynomial.nthRootsFinset n (1 : F)))
    (hxG : x ∈ Polynomial.nthRootsFinset n (1 : F))
    (hx'G : x' ∈ Polynomial.nthRootsFinset n (1 : F))
    (htG : t ∈ Polynomial.nthRootsFinset n (1 : F))
    (ht'G : t' ∈ Polynomial.nthRootsFinset n (1 : F))
    -- distinctness for `quadT x t`:
    (hx1 : x ≠ -x) (hx2 : x * t ≠ x) (hx3 : x * t ≠ -x) (hx4 : x * t⁻¹ ≠ x)
    (hx5 : x * t⁻¹ ≠ -x) (hx6 : x * t ≠ x * t⁻¹)
    -- distinctness for `quadT x' t'`:
    (hy1 : x' ≠ -x') (hy2 : x' * t' ≠ x') (hy3 : x' * t' ≠ -x')
    (hy4 : x' * t'⁻¹ ≠ x') (hy5 : x' * t'⁻¹ ≠ -x')
    (hy6 : x' * t' ≠ x' * t'⁻¹)
    (hc : (t + t⁻¹) ≠ 0) (hc' : (t' + t'⁻¹) ≠ 0)
    (hne : (t + t⁻¹) ≠ (t' + t'⁻¹))
    (hsign : (t + t⁻¹) ≠ -(t' + t'⁻¹)) :
    ¬ (e2BadScalarSet (Polynomial.nthRootsFinset n (1 : F)) 4).card ≤ n :=
  not_le.mpr
    (n_lt_e2BadScalarSet_mu_card_of_two_quadT_even_modSignNonCollision
      hn heven hζ hNC hxG hx'G htG ht'G hx1 hx2 hx3 hx4 hx5 hx6 hy1 hy2 hy3
      hy4 hy5 hy6 hc hc' hne hsign)

/-- **Fixed primitive-root width-4 refuter with only a pairwise residual.** For even `n > 8`,
the canonical witnesses `quadT 1 ζ` and `quadT 1 ζ²` satisfy all algebraic side conditions.  The
only remaining input is the exact local statement that the invariant of `ζ²` is not in the
`μ_n`-orbit of the invariant of `ζ`. -/
theorem n_lt_e2BadScalarSet_mu_card_of_primitive_zeta_sq_even_pairNonCollision
    {n : ℕ} {ζ : F} (hn : 0 < n) (heven : 2 ∣ n) (hn8 : 8 < n)
    (hζ : IsPrimitiveRoot ζ n)
    (hpair :
      InvariantPairNonCollision (Polynomial.nthRootsFinset n (1 : F)) ζ (ζ ^ 2)) :
    n < (e2BadScalarSet (Polynomial.nthRootsFinset n (1 : F)) 4).card := by
  have heven0 : 2 ∣ n := heven
  obtain ⟨h, hnh⟩ := heven
  have hh : h ≠ 0 := by omega
  have hone : (1 : F) ≠ -1 := one_ne_neg_one_of_primRoot_even hζ hnh hh
  have h1G : (1 : F) ∈ Polynomial.nthRootsFinset n (1 : F) :=
    Polynomial.one_mem_nthRootsFinset hn
  have hζG : ζ ∈ Polynomial.nthRootsFinset n (1 : F) :=
    primRoot_mem_nthRootsFinset hn hζ
  have hζ2G : ζ ^ 2 ∈ Polynomial.nthRootsFinset n (1 : F) :=
    primRoot_pow_mem_nthRootsFinset (k := 2) hn hζ
  have hζne1 : ζ ≠ 1 := by
    simpa [pow_one] using
      primRoot_pow_ne_one_of_lt (F := F) (ζ := ζ) hζ one_ne_zero (by omega : 1 < n)
  have hζneneg1 : ζ ≠ -1 := by
    simpa [pow_one] using
      primRoot_pow_ne_neg_one_of_two_mul_lt (F := F) (ζ := ζ) (k := 1) hζ one_ne_zero
        (by omega : 1 * 2 < n)
  have hζinvne1 : ζ⁻¹ ≠ 1 := by
    intro h
    exact hζne1 (inv_eq_one.mp h)
  have hζinvneneg1 : ζ⁻¹ ≠ -1 := by
    intro h
    exact hζneneg1 (by simpa [inv_neg, inv_one] using congrArg (fun y : F => y⁻¹) h)
  have hζneinv : ζ ≠ ζ⁻¹ := by
    simpa [pow_one] using
      primRoot_pow_ne_inv_of_two_mul_lt (F := F) (ζ := ζ) (k := 1) hn hζ one_ne_zero
        (by omega : 1 * 2 < n)
  have hζ2ne1 : ζ ^ 2 ≠ 1 :=
    primRoot_pow_ne_one_of_lt (F := F) (ζ := ζ) (k := 2) hζ
      (by norm_num : (2 : ℕ) ≠ 0) (by omega : 2 < n)
  have hζ2neneg1 : ζ ^ 2 ≠ -1 :=
    primRoot_pow_ne_neg_one_of_two_mul_lt (F := F) (ζ := ζ) (k := 2) hζ
      (by norm_num : (2 : ℕ) ≠ 0) (by omega : 2 * 2 < n)
  have hζ2invne1 : (ζ ^ 2)⁻¹ ≠ 1 := by
    intro h
    exact hζ2ne1 (inv_eq_one.mp h)
  have hζ2invneneg1 : (ζ ^ 2)⁻¹ ≠ -1 := by
    intro h
    exact hζ2neneg1 (by simpa [inv_neg, inv_one] using congrArg (fun y : F => y⁻¹) h)
  have hζ2neinv : ζ ^ 2 ≠ (ζ ^ 2)⁻¹ :=
    primRoot_pow_ne_inv_of_two_mul_lt (F := F) (ζ := ζ) (k := 2) hn hζ
      (by norm_num : (2 : ℕ) ≠ 0) (by omega : 2 * 2 < n)
  have hc : ζ + ζ⁻¹ ≠ 0 := by
    simpa [pow_one] using
      primRoot_pow_add_inv_ne_zero_of_four_mul_lt (F := F) (ζ := ζ) (k := 1) hn hζ
        one_ne_zero (by omega : 1 * 4 < n)
  have hc' : ζ ^ 2 + (ζ ^ 2)⁻¹ ≠ 0 :=
    primRoot_pow_add_inv_ne_zero_of_four_mul_lt (F := F) (ζ := ζ) (k := 2) hn hζ
      (by norm_num : (2 : ℕ) ≠ 0) (by omega : 2 * 4 < n)
  simpa [hζ.card_nthRootsFinset] using
    (group_card_lt_e2BadScalarSet_card_of_two_quadT_mem_pairNonCollision
      (F := F) (G := Polynomial.nthRootsFinset n (1 : F))
      (nthRootsFinset_finSubgroup (F := F) hn)
      (neg_one_mem_nthRootsFinset_of_even (F := F) hn heven0)
      (x := (1 : F)) (x' := (1 : F)) (t := ζ) (t' := ζ ^ 2)
      h1G h1G hζG hζ2G
      hone
      (by simpa using hζne1)
      (by simpa using hζneneg1)
      (by simpa using hζinvne1)
      (by simpa using hζinvneneg1)
      (by simpa using hζneinv)
      hone
      (by simpa using hζ2ne1)
      (by simpa using hζ2neneg1)
      (by simpa using hζ2invne1)
      (by simpa using hζ2invneneg1)
      (by simpa using hζ2neinv)
      hc hc' hpair)

/-- Fixed primitive-root scanner-failure form with only the pairwise invariant non-collision
residual. -/
theorem not_e2BadScalarSet_mu_card_le_n_of_primitive_zeta_sq_even_pairNonCollision
    {n : ℕ} {ζ : F} (hn : 0 < n) (heven : 2 ∣ n) (hn8 : 8 < n)
    (hζ : IsPrimitiveRoot ζ n)
    (hpair :
      InvariantPairNonCollision (Polynomial.nthRootsFinset n (1 : F)) ζ (ζ ^ 2)) :
    ¬ (e2BadScalarSet (Polynomial.nthRootsFinset n (1 : F)) 4).card ≤ n :=
  not_le.mpr
    (n_lt_e2BadScalarSet_mu_card_of_primitive_zeta_sq_even_pairNonCollision
      hn heven hn8 hζ hpair)

/-- **Fixed primitive-root width-4 refuter with the ratio-power residual.** This is the most
algebraic local form of the canonical two-witness scanner: for even `n > 8`, it is enough to prove
that the displayed invariant ratio
`((ζ² + ζ⁻²) / (ζ + ζ⁻¹))` is not an `n`-th root. -/
theorem n_lt_e2BadScalarSet_mu_card_of_primitive_zeta_sq_even_ratioPowNeOne
    {n : ℕ} {ζ : F} (hn : 0 < n) (heven : 2 ∣ n) (hn8 : 8 < n)
    (hζ : IsPrimitiveRoot ζ n)
    (hratio : invariantRatio ζ (ζ ^ 2) ^ n ≠ 1) :
    n < (e2BadScalarSet (Polynomial.nthRootsFinset n (1 : F)) 4).card := by
  have hc : ζ + ζ⁻¹ ≠ 0 := by
    simpa [pow_one] using
      primRoot_pow_add_inv_ne_zero_of_four_mul_lt (F := F) (ζ := ζ) (k := 1) hn hζ
        one_ne_zero (by omega : 1 * 4 < n)
  exact n_lt_e2BadScalarSet_mu_card_of_primitive_zeta_sq_even_pairNonCollision
    hn heven hn8 hζ
    ((invariantPairNonCollision_nthRootsFinset_iff_ratio_pow_ne_one
      (F := F) hn (t := ζ) (t' := ζ ^ 2) hc).mpr hratio)

/-- Scanner-failure form of the fixed primitive-root ratio-power refuter. -/
theorem not_e2BadScalarSet_mu_card_le_n_of_primitive_zeta_sq_even_ratioPowNeOne
    {n : ℕ} {ζ : F} (hn : 0 < n) (heven : 2 ∣ n) (hn8 : 8 < n)
    (hζ : IsPrimitiveRoot ζ n)
    (hratio : invariantRatio ζ (ζ ^ 2) ^ n ≠ 1) :
    ¬ (e2BadScalarSet (Polynomial.nthRootsFinset n (1 : F)) 4).card ≤ n :=
  not_le.mpr
    (n_lt_e2BadScalarSet_mu_card_of_primitive_zeta_sq_even_ratioPowNeOne
      hn heven hn8 hζ hratio)

/-! ### Polynomial form of the fixed canonical ratio residual -/

/-- **Integer carrier for the fixed canonical denominator-cleared obstruction.** A primitive
finite-field root `ζ` satisfies the local width-4 ratio obstruction exactly when this polynomial
vanishes at `ζ`. -/
noncomputable def canonicalRatioPoly (n : ℕ) : Polynomial ℤ :=
  (Polynomial.X ^ 4 + Polynomial.C 1) ^ n - (Polynomial.X ^ 2 + Polynomial.C 1) ^ n

/-- Evaluation form of `canonicalRatioPoly` after mapping coefficients to any commutative ring. -/
theorem canonicalRatioPoly_eval_map {R : Type*} [CommRing R] (n : ℕ) (z : R) :
    ((canonicalRatioPoly n).map (Int.castRingHom R)).eval z =
      (z ^ 4 + 1) ^ n - (z ^ 2 + 1) ^ n := by
  simp [canonicalRatioPoly]

/-- The canonical obstruction polynomial is monic for positive `n`. -/
theorem canonicalRatioPoly_monic {n : ℕ} (hn : 0 < n) : (canonicalRatioPoly n).Monic := by
  unfold canonicalRatioPoly
  apply Polynomial.Monic.sub_of_left
  · exact (Polynomial.monic_X_pow_add_C (R := ℤ) (a := 1)
      (by norm_num : (4 : ℕ) ≠ 0)).pow n
  · let hmon2 : (Polynomial.X ^ 2 + Polynomial.C 1 : Polynomial ℤ).Monic :=
      Polynomial.monic_X_pow_add_C (R := ℤ) (a := 1) (by norm_num : (2 : ℕ) ≠ 0)
    let hmon4 : (Polynomial.X ^ 4 + Polynomial.C 1 : Polynomial ℤ).Monic :=
      Polynomial.monic_X_pow_add_C (R := ℤ) (a := 1) (by norm_num : (4 : ℕ) ≠ 0)
    rw [Polynomial.degree_eq_natDegree (hmon2.pow n).ne_zero,
      Polynomial.degree_eq_natDegree (hmon4.pow n).ne_zero]
    have hleft :
        ((Polynomial.X ^ 4 + Polynomial.C 1 : Polynomial ℤ) ^ n).natDegree = n * 4 := by
      rw [Polynomial.natDegree_pow]
      congr
      simpa using (Polynomial.natDegree_X_pow_add_C (R := ℤ) (n := 4) (r := 1))
    have hright :
        ((Polynomial.X ^ 2 + Polynomial.C 1 : Polynomial ℤ) ^ n).natDegree = n * 2 := by
      rw [Polynomial.natDegree_pow]
      congr
      simpa using (Polynomial.natDegree_X_pow_add_C (R := ℤ) (n := 2) (r := 1))
    rw [hleft, hright]
    exact_mod_cast (Nat.mul_lt_mul_of_pos_left (by norm_num : 2 < 4) hn)

/-- Mapping the canonical obstruction polynomial to `ZMod p` preserves degree. -/
theorem canonicalRatioPoly_natDegree_map_zmod {p n : ℕ} [Fact p.Prime] (hn : 0 < n) :
    ((canonicalRatioPoly n).map (Int.castRingHom (ZMod p))).natDegree =
      (canonicalRatioPoly n).natDegree := by
  rw [Polynomial.natDegree_map_eq_of_isUnit_leadingCoeff]
  rw [(canonicalRatioPoly_monic hn).leadingCoeff]
  exact isUnit_one

/-- A denominator-cleared polynomial equality is exactly a root of `canonicalRatioPoly`. -/
theorem canonicalRatioPoly_eval_zmod_eq_zero_of_polynomial_eq {p n : ℕ} [Fact p.Prime]
    {ζ : ZMod p} (hpoly : (ζ ^ 4 + 1) ^ n = (ζ ^ 2 + 1) ^ n) :
    ((canonicalRatioPoly n).map (Int.castRingHom (ZMod p))).eval ζ = 0 := by
  rw [canonicalRatioPoly_eval_map]
  exact sub_eq_zero.mpr hpoly

/-- **Denominator-cleared canonical ratio obstruction.** For a primitive `n`-th root `ζ`, once
`ζ² + 1` is nonzero, the local ratio-root obstruction is exactly the polynomial equality
`(ζ⁴ + 1)^n = (ζ² + 1)^n`.  This removes inverses from the fixed `quadT 1 ζ`, `quadT 1 ζ²`
scanner residual and is the finite-field/norm target. -/
theorem invariantRatio_zeta_sq_pow_eq_one_iff_polynomial_eq {n : ℕ} {ζ : F}
    (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n) (hden : ζ ^ 2 + 1 ≠ 0) :
    invariantRatio ζ (ζ ^ 2) ^ n = 1 ↔ (ζ ^ 4 + 1) ^ n = (ζ ^ 2 + 1) ^ n := by
  have hζ0 : ζ ≠ 0 := primRoot_ne_zero hn hζ
  have hζn : ζ ^ n = 1 := hζ.pow_eq_one
  have hdenpow : (ζ ^ 2 + 1) ^ n ≠ 0 := pow_ne_zero n hden
  have hratio :
      invariantRatio ζ (ζ ^ 2) = (ζ ^ 4 + 1) * ζ⁻¹ * (ζ ^ 2 + 1)⁻¹ := by
    rw [invariantRatio]
    field_simp [hζ0, hden, pow_ne_zero 2 hζ0]
  have hpow :
      invariantRatio ζ (ζ ^ 2) ^ n = (ζ ^ 4 + 1) ^ n * ((ζ ^ 2 + 1) ^ n)⁻¹ := by
    rw [hratio, mul_pow, mul_pow]
    simp [inv_pow, hζn]
  rw [hpow]
  constructor
  · intro h
    have hmul := congrArg (fun y : F => y * (ζ ^ 2 + 1) ^ n) h
    simpa [mul_assoc, hdenpow] using hmul
  · intro h
    rw [h]
    exact mul_inv_cancel₀ hdenpow

/-- Negated denominator-cleared form of the canonical ratio obstruction. -/
theorem invariantRatio_zeta_sq_pow_ne_one_iff_polynomial_ne {n : ℕ} {ζ : F}
    (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n) (hden : ζ ^ 2 + 1 ≠ 0) :
    invariantRatio ζ (ζ ^ 2) ^ n ≠ 1 ↔ (ζ ^ 4 + 1) ^ n ≠ (ζ ^ 2 + 1) ^ n := by
  constructor
  · intro hne hpoly
    exact hne ((invariantRatio_zeta_sq_pow_eq_one_iff_polynomial_eq hn hζ hden).mpr hpoly)
  · intro hne hratio
    exact hne ((invariantRatio_zeta_sq_pow_eq_one_iff_polynomial_eq hn hζ hden).mp hratio)

/-- For the canonical even `n > 8` primitive-root lane, the ratio-power residual is equivalent to
one denominator-free polynomial nonvanishing statement. -/
theorem invariantRatio_primitive_zeta_sq_pow_ne_one_iff_polynomial_ne {n : ℕ} {ζ : F}
    (hn : 0 < n) (hn8 : 8 < n) (hζ : IsPrimitiveRoot ζ n) :
    invariantRatio ζ (ζ ^ 2) ^ n ≠ 1 ↔ (ζ ^ 4 + 1) ^ n ≠ (ζ ^ 2 + 1) ^ n := by
  have hζ2neneg1 : ζ ^ 2 ≠ -1 :=
    primRoot_pow_ne_neg_one_of_two_mul_lt (F := F) (ζ := ζ) (k := 2) hζ
      (by norm_num : (2 : ℕ) ≠ 0) (by omega : 2 * 2 < n)
  have hden : ζ ^ 2 + 1 ≠ 0 := by
    intro h
    exact hζ2neneg1 (eq_neg_of_add_eq_zero_left h)
  exact invariantRatio_zeta_sq_pow_ne_one_iff_polynomial_ne hn hζ hden

/-- Scanner-failure wrapper using the denominator-free polynomial residual for the fixed
primitive witnesses. -/
theorem n_lt_e2BadScalarSet_mu_card_of_primitive_zeta_sq_even_polynomialNe
    {n : ℕ} {ζ : F} (hn : 0 < n) (heven : 2 ∣ n) (hn8 : 8 < n)
    (hζ : IsPrimitiveRoot ζ n)
    (hpoly : (ζ ^ 4 + 1) ^ n ≠ (ζ ^ 2 + 1) ^ n) :
    n < (e2BadScalarSet (Polynomial.nthRootsFinset n (1 : F)) 4).card :=
  n_lt_e2BadScalarSet_mu_card_of_primitive_zeta_sq_even_ratioPowNeOne
    hn heven hn8 hζ
    ((invariantRatio_primitive_zeta_sq_pow_ne_one_iff_polynomial_ne hn hn8 hζ).mpr hpoly)

/-- Literal-budget refuter using the denominator-free polynomial residual. -/
theorem not_e2BadScalarSet_mu_card_le_n_of_primitive_zeta_sq_even_polynomialNe
    {n : ℕ} {ζ : F} (hn : 0 < n) (heven : 2 ∣ n) (hn8 : 8 < n)
    (hζ : IsPrimitiveRoot ζ n)
    (hpoly : (ζ ^ 4 + 1) ^ n ≠ (ζ ^ 2 + 1) ^ n) :
    ¬ (e2BadScalarSet (Polynomial.nthRootsFinset n (1 : F)) 4).card ≤ n :=
  not_le.mpr
    (n_lt_e2BadScalarSet_mu_card_of_primitive_zeta_sq_even_polynomialNe
      hn heven hn8 hζ hpoly)

/-! ### Complex discharge of the fixed canonical ratio residual -/

/-- Over `ℂ`, the fixed canonical invariant ratio for `ζ, ζ²` is not an `n`-th root when
`ζ` is primitive and `8 < n`. -/
theorem invariantRatio_pow_ne_one_complex_primitive_zeta_sq {n : ℕ} {ζ : ℂ}
    (hn : 0 < n) (hn8 : 8 < n) (hζ : IsPrimitiveRoot ζ n) :
    invariantRatio ζ (ζ ^ 2) ^ n ≠ 1 := by
  have hc : ζ + ζ⁻¹ ≠ 0 := by
    simpa [pow_one] using
      primRoot_pow_add_inv_ne_zero_of_four_mul_lt (F := ℂ) (ζ := ζ) (k := 1) hn hζ
        one_ne_zero (by omega : 1 * 4 < n)
  exact
    (invariantPairNonCollision_nthRootsFinset_iff_ratio_pow_ne_one
      (F := ℂ) hn (t := ζ) (t' := ζ ^ 2) hc).mp
      (invariantPairNonCollision_complex_primitive_zeta_sq hn hn8 hζ)

/-- Over `ℂ`, the denominator-cleared fixed canonical polynomial obstruction is nonzero for every
primitive `ζ` with `8 < n`. This is the characteristic-zero nonvanishing input needed by the
cyclotomic-resultant bad-prime route. -/
theorem polynomial_ne_complex_primitive_zeta_sq {n : ℕ} {ζ : ℂ}
    (hn : 0 < n) (hn8 : 8 < n) (hζ : IsPrimitiveRoot ζ n) :
    (ζ ^ 4 + 1) ^ n ≠ (ζ ^ 2 + 1) ^ n :=
  (invariantRatio_primitive_zeta_sq_pow_ne_one_iff_polynomial_ne
    (F := ℂ) hn hn8 hζ).mp
    (invariantRatio_pow_ne_one_complex_primitive_zeta_sq hn hn8 hζ)

/-- The canonical width-4 obstruction resultant is nonzero in characteristic zero. -/
theorem resultant_canonicalRatioPoly_ne_zero {n : ℕ} (hn : 0 < n) (hn8 : 8 < n) :
    Polynomial.resultant (Polynomial.cyclotomic n ℤ) (canonicalRatioPoly n)
        (Polynomial.cyclotomic n ℤ).natDegree (canonicalRatioPoly n).natDegree ≠ 0 := by
  apply _root_.resultant_cyclotomic_ne_zero_of_forall_root_ne n (canonicalRatioPoly n)
  intro ω hω
  haveI : NeZero (n : ℂ) := ⟨Nat.cast_ne_zero.mpr hn.ne'⟩
  have hprim : IsPrimitiveRoot ω n :=
    Polynomial.isRoot_cyclotomic_iff.mp (Polynomial.isRoot_of_mem_roots hω)
  have hne : (ω ^ 4 + 1) ^ n ≠ (ω ^ 2 + 1) ^ n :=
    polynomial_ne_complex_primitive_zeta_sq hn hn8 hprim
  rw [canonicalRatioPoly_eval_map]
  exact sub_ne_zero.mpr hne

/-- If the canonical denominator-cleared obstruction vanishes in `ZMod p`, then `p` divides the
nonzero cyclotomic resultant of the integer carrier polynomial. -/
theorem prime_dvd_resultant_canonicalRatioPoly_of_polynomial_eq_zmod
    {p n : ℕ} [Fact p.Prime] (hn : 0 < n) {ζ : ZMod p}
    (hζ : IsPrimitiveRoot ζ n)
    (hpoly : (ζ ^ 4 + 1) ^ n = (ζ ^ 2 + 1) ^ n) :
    (p : ℤ) ∣ Polynomial.resultant (Polynomial.cyclotomic n ℤ) (canonicalRatioPoly n)
      (Polynomial.cyclotomic n ℤ).natDegree (canonicalRatioPoly n).natDegree :=
  _root_.dvd_resultant_of_isPrimitiveRoot_isRoot hn (canonicalRatioPoly n)
    (canonicalRatioPoly_natDegree_map_zmod hn) hζ
    (canonicalRatioPoly_eval_zmod_eq_zero_of_polynomial_eq hpoly)

/-- If the canonical polynomial obstruction vanishes in `ZMod p`, then `p` is bounded by the
absolute value of the nonzero integer resultant. -/
theorem prime_le_natAbs_resultant_canonicalRatioPoly_of_polynomial_eq_zmod
    {p n : ℕ} [Fact p.Prime] (hn : 0 < n) (hn8 : 8 < n) {ζ : ZMod p}
    (hζ : IsPrimitiveRoot ζ n)
    (hpoly : (ζ ^ 4 + 1) ^ n = (ζ ^ 2 + 1) ^ n) :
    p ≤ (Polynomial.resultant (Polynomial.cyclotomic n ℤ) (canonicalRatioPoly n)
      (Polynomial.cyclotomic n ℤ).natDegree (canonicalRatioPoly n).natDegree).natAbs := by
  have hdvd :=
    prime_dvd_resultant_canonicalRatioPoly_of_polynomial_eq_zmod hn hζ hpoly
  have hne : Polynomial.resultant (Polynomial.cyclotomic n ℤ) (canonicalRatioPoly n)
        (Polynomial.cyclotomic n ℤ).natDegree (canonicalRatioPoly n).natDegree ≠ 0 :=
    resultant_canonicalRatioPoly_ne_zero hn hn8
  exact Nat.le_of_dvd (Int.natAbs_pos.mpr hne) (Int.natAbs_dvd_natAbs.mpr hdvd)

/-- Crude archimedean bound for the canonical obstruction polynomial on `n`-th roots of unity. -/
theorem canonicalRatioPoly_eval_nnnorm_le_two_pow_succ {n : ℕ} (hn : n ≠ 0) {ω : ℂ}
    (hω : ω ^ n = 1) :
    ‖((canonicalRatioPoly n).map (Int.castRingHom ℂ)).eval ω‖₊
      ≤ ((2 ^ (n + 1) : ℕ) : ℝ≥0) := by
  have hnormω : ‖ω‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hω hn
  have h4 : ‖ω ^ 4 + 1‖ ≤ (2 : ℝ) := by
    calc ‖ω ^ 4 + 1‖
        ≤ ‖ω ^ 4‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ = 2 := by rw [norm_pow, hnormω, one_pow, norm_one]; norm_num
  have h2 : ‖ω ^ 2 + 1‖ ≤ (2 : ℝ) := by
    calc ‖ω ^ 2 + 1‖
        ≤ ‖ω ^ 2‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ = 2 := by rw [norm_pow, hnormω, one_pow, norm_one]; norm_num
  have h4pow : ‖(ω ^ 4 + 1) ^ n‖ ≤ (2 : ℝ) ^ n := by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) h4 n
  have h2pow : ‖(ω ^ 2 + 1) ^ n‖ ≤ (2 : ℝ) ^ n := by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) h2 n
  have hreal : ‖(ω ^ 4 + 1) ^ n - (ω ^ 2 + 1) ^ n‖ ≤ (2 : ℝ) ^ (n + 1) := by
    calc ‖(ω ^ 4 + 1) ^ n - (ω ^ 2 + 1) ^ n‖
        ≤ ‖(ω ^ 4 + 1) ^ n‖ + ‖(ω ^ 2 + 1) ^ n‖ := norm_sub_le _ _
      _ ≤ (2 : ℝ) ^ n + (2 : ℝ) ^ n := add_le_add h4pow h2pow
      _ = (2 : ℝ) ^ (n + 1) := by rw [pow_succ']; ring
  have heval :
      ((canonicalRatioPoly n).map (Int.castRingHom ℂ)).eval ω =
        (ω ^ 4 + 1) ^ n - (ω ^ 2 + 1) ^ n :=
    canonicalRatioPoly_eval_map n ω
  rw [heval]
  exact_mod_cast hreal

/-- Explicit crude upper bound for the canonical width-4 obstruction resultant. -/
theorem natAbs_resultant_canonicalRatioPoly_le_two_pow_succ_totient {n : ℕ} (hn : n ≠ 0) :
    (Polynomial.resultant (Polynomial.cyclotomic n ℤ) (canonicalRatioPoly n)
      (Polynomial.cyclotomic n ℤ).natDegree (canonicalRatioPoly n).natDegree).natAbs
      ≤ (2 ^ (n + 1)) ^ n.totient :=
  _root_.natAbs_resultant_cyclotomic_le_of_bound n (2 ^ (n + 1)) (canonicalRatioPoly n)
    (fun _ hω => by
      simpa [Nat.cast_pow] using canonicalRatioPoly_eval_nnnorm_le_two_pow_succ hn hω)

/-- Contrapositive polynomial form: above the canonical obstruction resultant, the denominator-free
polynomial collision cannot occur. -/
theorem polynomial_ne_zmod_of_resultant_natAbs_lt_prime
    {p n : ℕ} [Fact p.Prime] (hn : 0 < n) (hn8 : 8 < n) {ζ : ZMod p}
    (hζ : IsPrimitiveRoot ζ n)
    (hsmall :
      (Polynomial.resultant (Polynomial.cyclotomic n ℤ) (canonicalRatioPoly n)
        (Polynomial.cyclotomic n ℤ).natDegree (canonicalRatioPoly n).natDegree).natAbs < p) :
    (ζ ^ 4 + 1) ^ n ≠ (ζ ^ 2 + 1) ^ n := by
  intro hpoly
  exact not_lt_of_ge
    (prime_le_natAbs_resultant_canonicalRatioPoly_of_polynomial_eq_zmod
      hn hn8 hζ hpoly) hsmall

/-- Crude explicit good-prime form: if `p` exceeds the elementary archimedean bound for the
canonical obstruction resultant, the denominator-free collision cannot occur. -/
theorem polynomial_ne_zmod_of_two_pow_succ_totient_lt_prime
    {p n : ℕ} [Fact p.Prime] (hn : 0 < n) (hn8 : 8 < n) {ζ : ZMod p}
    (hζ : IsPrimitiveRoot ζ n)
    (hlarge : (2 ^ (n + 1)) ^ n.totient < p) :
    (ζ ^ 4 + 1) ^ n ≠ (ζ ^ 2 + 1) ^ n :=
  polynomial_ne_zmod_of_resultant_natAbs_lt_prime hn hn8 hζ
    ((natAbs_resultant_canonicalRatioPoly_le_two_pow_succ_totient hn.ne').trans_lt hlarge)

/-- Scanner-facing crude good-prime form: the elementary archimedean bound alone is enough to refute
the literal width-4 `≤ n` budget once `(2^(n+1))^φ(n) < p`. -/
theorem not_e2BadScalarSet_mu_card_le_n_zmod_of_two_pow_succ_totient_lt_prime
    {p n : ℕ} [Fact p.Prime] (hn : 0 < n) (heven : 2 ∣ n) (hn8 : 8 < n)
    {ζ : ZMod p} (hζ : IsPrimitiveRoot ζ n)
    (hlarge : (2 ^ (n + 1)) ^ n.totient < p) :
    ¬ (e2BadScalarSet (Polynomial.nthRootsFinset n (1 : ZMod p)) 4).card ≤ n :=
  not_e2BadScalarSet_mu_card_le_n_of_primitive_zeta_sq_even_polynomialNe
    hn heven hn8 hζ
    (polynomial_ne_zmod_of_two_pow_succ_totient_lt_prime hn hn8 hζ hlarge)

/-! ### Exact `n = 16` good-prime certificate -/

/-- Exact reduction of the denominator-free canonical obstruction at order `16`.
Modulo `ζ⁸ = -1`, the obstruction carries an explicit factor `17 * 48` times a cubic in `ζ²`. -/
theorem canonicalRatioPoly16_reduction_zmod {p : ℕ} [Fact p.Prime] {ζ : ZMod p}
    (h8 : ζ ^ 8 = -1) :
    (ζ ^ 4 + 1) ^ 16 - (ζ ^ 2 + 1) ^ 16 =
      (17 : ZMod p) * 48 * (8 * ζ ^ 6 - 8 * ζ ^ 2 - 11) := by
  rw [show
      (ζ ^ 4 + 1) ^ 16 - (ζ ^ 2 + 1) ^ 16 =
        (17 : ZMod p) * 48 * (8 * ζ ^ 6 - 8 * ζ ^ 2 - 11) +
        (ζ ^ 8 + 1) *
          (8976 + 6512 * ζ ^ 2 - 104 * ζ ^ 4 - 7088 * ζ ^ 6 -
            10676 * ζ ^ 8 - 10880 * ζ ^ 10 - 7344 * ζ ^ 12 -
            4352 * ζ ^ 14 - 374 * ζ ^ 16 - 560 * ζ ^ 18 +
            3704 * ζ ^ 20 - 16 * ζ ^ 22 + 6562 * ζ ^ 24 +
            7616 * ζ ^ 28 + 6307 * ζ ^ 32 + 3824 * ζ ^ 36 +
            1701 * ζ ^ 40 + 544 * ζ ^ 44 + 119 * ζ ^ 48 +
            16 * ζ ^ 52 + ζ ^ 56) by ring]
  rw [h8]
  ring

/-- Bezout certificate for the reduced `n = 16` obstruction.
Together with `y⁴ + 1 = 0`, a vanishing reduced cubic would force `7 = 0`. -/
theorem canonicalRatioPoly16_bezout {R : Type*} [CommRing R] (y : R) :
    (128 - 64 * y ^ 2) * (y ^ 4 + 1) +
      (11 - 8 * y + 8 * y ^ 3) * (8 * y ^ 3 - 8 * y - 11) = 7 := by
  ring

/-- Exact `n = 16` good-prime form: above the unique small obstruction prime `17`, the
denominator-free canonical collision cannot occur. -/
theorem polynomial_ne_zmod16_of_prime_gt17
    {p : ℕ} [Fact p.Prime] (hp17 : 17 < p) {ζ : ZMod p}
    (hζ : IsPrimitiveRoot ζ 16) :
    (ζ ^ 4 + 1) ^ 16 ≠ (ζ ^ 2 + 1) ^ 16 := by
  intro hpoly
  have h8 : ζ ^ 8 = -1 :=
    primRoot_pow_half_eq_neg_one_of_even (F := ZMod p) (ζ := ζ) (n := 16) (h := 8)
      hζ (by norm_num) (by norm_num)
  have hdiff : (ζ ^ 4 + 1) ^ 16 - (ζ ^ 2 + 1) ^ 16 = 0 := sub_eq_zero.mpr hpoly
  have hred := canonicalRatioPoly16_reduction_zmod (p := p) (ζ := ζ) h8
  have hprod : (17 : ZMod p) * 48 * (8 * ζ ^ 6 - 8 * ζ ^ 2 - 11) = 0 := by
    rw [← hred]
    exact hdiff
  have h17nz : (17 : ZMod p) ≠ 0 := by
    change ¬ (((17 : ℕ) : ZMod p) = 0)
    rw [ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt (by norm_num : 0 < 17) hp17
  have h48nz : (48 : ZMod p) ≠ 0 := by
    change ¬ (((48 : ℕ) : ZMod p) = 0)
    rw [ZMod.natCast_eq_zero_iff]
    intro hdvd
    have hp : Nat.Prime p := Fact.out
    have h48 : (48 : ℕ) = 3 * 2 ^ 4 := by norm_num
    have hdvd' : p ∣ 3 * 2 ^ 4 := by
      simpa [← h48] using hdvd
    rcases (Nat.Prime.dvd_mul hp).mp hdvd' with h3 | h2pow
    · have hp_eq3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3
      omega
    · have hp_dvd2 : p ∣ 2 := hp.dvd_of_dvd_pow h2pow
      have hp_eq2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp_dvd2
      omega
  have hcoeff : (17 : ZMod p) * 48 ≠ 0 := mul_ne_zero h17nz h48nz
  have hcubic : 8 * ζ ^ 6 - 8 * ζ ^ 2 - 11 = 0 :=
    (mul_eq_zero.mp hprod).resolve_left hcoeff
  have hy4 : (ζ ^ 2) ^ 4 + 1 = 0 := by
    have hy4' : (ζ ^ 2) ^ 4 = -1 := by
      calc
        (ζ ^ 2) ^ 4 = ζ ^ 8 := by ring
        _ = -1 := h8
    rw [hy4']
    ring
  have hcubic_y : 8 * (ζ ^ 2) ^ 3 - 8 * (ζ ^ 2) - 11 = 0 := by
    convert hcubic using 1
    ring
  have h7zero : (7 : ZMod p) = 0 := by
    rw [← canonicalRatioPoly16_bezout (R := ZMod p) (ζ ^ 2)]
    rw [hy4, hcubic_y]
    ring
  have h7nz : (7 : ZMod p) ≠ 0 := by
    change ¬ (((7 : ℕ) : ZMod p) = 0)
    rw [ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt (by norm_num : 0 < 7) (by omega : 7 < p)
  exact h7nz h7zero

/-- Scanner-facing exact `n = 16` good-prime form: for every prime `p > 17`, the literal
width-4 `≤ 16` budget is impossible in the canonical primitive-root lane. -/
theorem not_e2BadScalarSet_mu16_card_le_16_zmod_of_prime_gt17
    {p : ℕ} [Fact p.Prime] (hp17 : 17 < p) {ζ : ZMod p}
    (hζ : IsPrimitiveRoot ζ 16) :
    ¬ (e2BadScalarSet (Polynomial.nthRootsFinset 16 (1 : ZMod p)) 4).card ≤ 16 :=
  not_e2BadScalarSet_mu_card_le_n_of_primitive_zeta_sq_even_polynomialNe
    (F := ZMod p) (n := 16) (ζ := ζ)
    (by norm_num) (by norm_num) (by norm_num) hζ
    (polynomial_ne_zmod16_of_prime_gt17 hp17 hζ)


/-- Complex fixed primitive-root width-4 refuter for the canonical witnesses. -/
theorem n_lt_e2BadScalarSet_mu_card_of_complex_primitive_zeta_sq_even
    {n : ℕ} {ζ : ℂ} (hn : 0 < n) (heven : 2 ∣ n) (hn8 : 8 < n)
    (hζ : IsPrimitiveRoot ζ n) :
    n < (e2BadScalarSet (Polynomial.nthRootsFinset n (1 : ℂ)) 4).card :=
  n_lt_e2BadScalarSet_mu_card_of_primitive_zeta_sq_even_ratioPowNeOne
    (F := ℂ) hn heven hn8 hζ
    (invariantRatio_pow_ne_one_complex_primitive_zeta_sq hn hn8 hζ)

/-- Complex scanner-failure form for the canonical width-4 witnesses. -/
theorem not_e2BadScalarSet_mu_card_le_n_of_complex_primitive_zeta_sq_even
    {n : ℕ} {ζ : ℂ} (hn : 0 < n) (heven : 2 ∣ n) (hn8 : 8 < n)
    (hζ : IsPrimitiveRoot ζ n) :
    ¬ (e2BadScalarSet (Polynomial.nthRootsFinset n (1 : ℂ)) 4).card ≤ n :=
  not_le.mpr
    (n_lt_e2BadScalarSet_mu_card_of_complex_primitive_zeta_sq_even
      hn heven hn8 hζ)

/-! ### A concrete finite-field ratio obstruction (`n = 16`, `p = 12289`) -/

section Concrete12289Ratio

local instance fact_prime_12289_ratio : Fact (Nat.Prime 12289) := ⟨by norm_num⟩

/-- The same `F₁₂₂₈₉` primitive 16-th root used by the sub-ceiling ladder. -/
theorem orderOf_4134_ratio : orderOf (4134 : ZMod 12289) = 16 := by
  have h8 : ¬ (4134 : ZMod 12289) ^ (2 : ℕ) ^ 3 = 1 := by decide
  have h16 : (4134 : ZMod 12289) ^ (2 : ℕ) ^ 4 = 1 := by decide
  have h := orderOf_eq_prime_pow (x := (4134 : ZMod 12289)) h8 h16
  norm_num at h
  exact h

/-- `4134` is a primitive 16-th root in `F₁₂₂₈₉`. -/
theorem isPrimitiveRoot_4134_16_ratio : IsPrimitiveRoot (4134 : ZMod 12289) 16 := by
  rw [IsPrimitiveRoot.iff_orderOf]
  exact orderOf_4134_ratio

/-- The denominator-free polynomial obstruction holds for the canonical pair in `F₁₂₂₈₉`. -/
theorem polynomial_4134_sq_pow16_ne :
    ((4134 : ZMod 12289) ^ 4 + 1) ^ 16 ≠
      ((4134 : ZMod 12289) ^ 2 + 1) ^ 16 := by
  decide

/-- The canonical pair `ζ, ζ²` fails the ratio-root condition in `F₁₂₂₈₉`. -/
theorem invariantRatio_4134_sq_pow16_ne_one :
    invariantRatio (4134 : ZMod 12289) ((4134 : ZMod 12289) ^ 2) ^ 16 ≠ 1 :=
  (invariantRatio_primitive_zeta_sq_pow_ne_one_iff_polynomial_ne
    (F := ZMod 12289) (n := 16) (ζ := (4134 : ZMod 12289))
    (by norm_num) (by norm_num) isPrimitiveRoot_4134_16_ratio).mpr
    polynomial_4134_sq_pow16_ne

/-- Concrete width-4 scanner failure for the 16-point subgroup of `F₁₂₂₈₉`. -/
theorem sixteen_lt_e2BadScalarSet_mu16_card_zmod12289_width4 :
    16 < (e2BadScalarSet (Polynomial.nthRootsFinset 16 (1 : ZMod 12289)) 4).card :=
  n_lt_e2BadScalarSet_mu_card_of_primitive_zeta_sq_even_ratioPowNeOne
    (F := ZMod 12289) (n := 16) (ζ := (4134 : ZMod 12289))
    (by norm_num) (by norm_num) (by norm_num)
    isPrimitiveRoot_4134_16_ratio
    invariantRatio_4134_sq_pow16_ne_one

/-- The literal `≤ n` width-4 scanner budget is false in the same concrete instance. -/
theorem not_e2BadScalarSet_mu16_card_le_16_zmod12289_width4 :
    ¬ (e2BadScalarSet (Polynomial.nthRootsFinset 16 (1 : ZMod 12289)) 4).card ≤ 16 :=
  not_le.mpr sixteen_lt_e2BadScalarSet_mu16_card_zmod12289_width4

end Concrete12289Ratio

/-! ### A bad-prime collapse of the fixed ratio residual (`n = 16`, `p = 17`) -/

section Concrete17RatioCollapse

local instance fact_prime_17_ratio : Fact (Nat.Prime 17) := ⟨by norm_num⟩

/-- `3` has order `16` in `F₁₇`. -/
theorem orderOf_3_ratio_zmod17 : orderOf (3 : ZMod 17) = 16 := by
  have h8 : ¬ (3 : ZMod 17) ^ (2 : ℕ) ^ 3 = 1 := by decide
  have h16 : (3 : ZMod 17) ^ (2 : ℕ) ^ 4 = 1 := by decide
  have h := orderOf_eq_prime_pow (x := (3 : ZMod 17)) h8 h16
  norm_num at h
  exact h

/-- `3` is a primitive 16-th root in `F₁₇`. -/
theorem isPrimitiveRoot_3_16_ratio_zmod17 : IsPrimitiveRoot (3 : ZMod 17) 16 := by
  rw [IsPrimitiveRoot.iff_orderOf]
  exact orderOf_3_ratio_zmod17

/-- At the bad prime `17`, the canonical ratio for `ζ = 3` is itself a 16-th root. -/
theorem invariantRatio_3_sq_pow16_eq_one_zmod17 :
    invariantRatio (3 : ZMod 17) ((3 : ZMod 17) ^ 2) ^ 16 = 1 := by
  decide

/-- Equivalently, the denominator-cleared polynomial obstruction vanishes in `F₁₇`. -/
theorem polynomial_eq_3_sq_pow16_zmod17 :
    ((3 : ZMod 17) ^ 4 + 1) ^ 16 = ((3 : ZMod 17) ^ 2 + 1) ^ 16 := by
  decide

/-- The concrete collision scalar in `F₁₇` is `5`. -/
theorem invariant_collision_scalar_5_zmod17 :
    (3 : ZMod 17) ^ 2 + ((3 : ZMod 17) ^ 2)⁻¹ =
      (5 : ZMod 17) * ((3 : ZMod 17) + (3 : ZMod 17)⁻¹) := by
  have h32 : ((3 : ZMod 17) ^ 2)⁻¹ = 2 := by
    apply inv_eq_of_mul_eq_one_right
    decide
  have h3 : ((3 : ZMod 17) : ZMod 17)⁻¹ = 6 := by
    apply inv_eq_of_mul_eq_one_right
    decide
  rw [h32, h3]
  decide

/-- The local pairwise residual fails concretely in `F₁₇`: a collision scalar exists. -/
theorem exists_invariant_collision_mu16_zmod17_3 :
    ∃ u ∈ Polynomial.nthRootsFinset 16 (1 : ZMod 17),
      (3 : ZMod 17) ^ 2 + ((3 : ZMod 17) ^ 2)⁻¹ =
        u * ((3 : ZMod 17) + (3 : ZMod 17)⁻¹) := by
  refine ⟨5, ?_, invariant_collision_scalar_5_zmod17⟩
  rw [Polynomial.mem_nthRootsFinset (by norm_num : 0 < 16)]
  decide

/-- Hence the canonical pairwise non-collision residual is false in this bad-prime instance. -/
theorem not_invariantPairNonCollision_mu16_zmod17_3 :
    ¬ InvariantPairNonCollision (Polynomial.nthRootsFinset 16 (1 : ZMod 17))
      (3 : ZMod 17) ((3 : ZMod 17) ^ 2) := by
  exact
    (not_invariantPairNonCollision_iff_exists_collision (F := ZMod 17)
      (Polynomial.nthRootsFinset 16 (1 : ZMod 17)) (3 : ZMod 17)
      ((3 : ZMod 17) ^ 2)).mpr exists_invariant_collision_mu16_zmod17_3

/-- Therefore the fixed canonical residual is not a uniform finite-field theorem without excluding
bad primes. -/
theorem not_forall_primitive_pairNonCollision_zmod17_mu16 :
    ¬ ∀ ζ : ZMod 17, IsPrimitiveRoot ζ 16 →
      InvariantPairNonCollision (Polynomial.nthRootsFinset 16 (1 : ZMod 17)) ζ (ζ ^ 2) := by
  intro h
  exact not_invariantPairNonCollision_mu16_zmod17_3
    (h (3 : ZMod 17) isPrimitiveRoot_3_16_ratio_zmod17)

/-- The bad prime `17` is detected by the canonical cyclotomic resultant. -/
theorem seventeen_dvd_resultant_canonicalRatioPoly_16 :
    (17 : ℤ) ∣ Polynomial.resultant (Polynomial.cyclotomic 16 ℤ) (canonicalRatioPoly 16)
      (Polynomial.cyclotomic 16 ℤ).natDegree (canonicalRatioPoly 16).natDegree :=
  prime_dvd_resultant_canonicalRatioPoly_of_polynomial_eq_zmod
    (p := 17) (n := 16) (by norm_num) isPrimitiveRoot_3_16_ratio_zmod17
    polynomial_eq_3_sq_pow16_zmod17

/-- Consequently the canonical resultant threshold is at least `17` in the first bad-prime
instance. -/
theorem seventeen_le_natAbs_resultant_canonicalRatioPoly_16 :
    17 ≤ (Polynomial.resultant (Polynomial.cyclotomic 16 ℤ) (canonicalRatioPoly 16)
      (Polynomial.cyclotomic 16 ℤ).natDegree (canonicalRatioPoly 16).natDegree).natAbs :=
  prime_le_natAbs_resultant_canonicalRatioPoly_of_polynomial_eq_zmod
    (p := 17) (n := 16) (by norm_num) (by norm_num) isPrimitiveRoot_3_16_ratio_zmod17
    polynomial_eq_3_sq_pow16_zmod17

end Concrete17RatioCollapse

/-- **Fixed primitive-root width-4 refuter.** For even `n > 8`, the canonical witnesses
`quadT 1 ζ` and `quadT 1 ζ²` satisfy all membership, nonzero, distinctness, and sign-quotiented
invariant-separation obligations automatically. Thus the remaining scanner-failure input is the
repaired cyclotomic residual `Cd₀NonCollisionModSign μ_n`. -/
theorem n_lt_e2BadScalarSet_mu_card_of_primitive_zeta_sq_even_modSignNonCollision
    {n : ℕ} {ζ : F} (hn : 0 < n) (heven : 2 ∣ n) (hn8 : 8 < n)
    (hζ : IsPrimitiveRoot ζ n)
    (hNC : Cd₀NonCollisionModSign (Polynomial.nthRootsFinset n (1 : F))) :
    n < (e2BadScalarSet (Polynomial.nthRootsFinset n (1 : F)) 4).card := by
  have heven0 : 2 ∣ n := heven
  obtain ⟨h, hnh⟩ := heven
  have hh : h ≠ 0 := by omega
  have hone : (1 : F) ≠ -1 := one_ne_neg_one_of_primRoot_even hζ hnh hh
  have h1G : (1 : F) ∈ Polynomial.nthRootsFinset n (1 : F) :=
    Polynomial.one_mem_nthRootsFinset hn
  have hζG : ζ ∈ Polynomial.nthRootsFinset n (1 : F) :=
    primRoot_mem_nthRootsFinset hn hζ
  have hζ2G : ζ ^ 2 ∈ Polynomial.nthRootsFinset n (1 : F) :=
    primRoot_pow_mem_nthRootsFinset (k := 2) hn hζ
  have hζne1 : ζ ≠ 1 := by
    simpa [pow_one] using
      primRoot_pow_ne_one_of_lt (F := F) (ζ := ζ) hζ one_ne_zero (by omega : 1 < n)
  have hζneneg1 : ζ ≠ -1 := by
    simpa [pow_one] using
      primRoot_pow_ne_neg_one_of_two_mul_lt (F := F) (ζ := ζ) (k := 1) hζ one_ne_zero
        (by omega : 1 * 2 < n)
  have hζinvne1 : ζ⁻¹ ≠ 1 := by
    intro h
    exact hζne1 (inv_eq_one.mp h)
  have hζinvneneg1 : ζ⁻¹ ≠ -1 := by
    intro h
    exact hζneneg1 (by simpa [inv_neg, inv_one] using congrArg (fun y : F => y⁻¹) h)
  have hζneinv : ζ ≠ ζ⁻¹ := by
    simpa [pow_one] using
      primRoot_pow_ne_inv_of_two_mul_lt (F := F) (ζ := ζ) (k := 1) hn hζ one_ne_zero
        (by omega : 1 * 2 < n)
  have hζ2ne1 : ζ ^ 2 ≠ 1 :=
    primRoot_pow_ne_one_of_lt (F := F) (ζ := ζ) (k := 2) hζ
      (by norm_num : (2 : ℕ) ≠ 0) (by omega : 2 < n)
  have hζ2neneg1 : ζ ^ 2 ≠ -1 :=
    primRoot_pow_ne_neg_one_of_two_mul_lt (F := F) (ζ := ζ) (k := 2) hζ
      (by norm_num : (2 : ℕ) ≠ 0) (by omega : 2 * 2 < n)
  have hζ2invne1 : (ζ ^ 2)⁻¹ ≠ 1 := by
    intro h
    exact hζ2ne1 (inv_eq_one.mp h)
  have hζ2invneneg1 : (ζ ^ 2)⁻¹ ≠ -1 := by
    intro h
    exact hζ2neneg1 (by simpa [inv_neg, inv_one] using congrArg (fun y : F => y⁻¹) h)
  have hζ2neinv : ζ ^ 2 ≠ (ζ ^ 2)⁻¹ :=
    primRoot_pow_ne_inv_of_two_mul_lt (F := F) (ζ := ζ) (k := 2) hn hζ
      (by norm_num : (2 : ℕ) ≠ 0) (by omega : 2 * 2 < n)
  have hc : ζ + ζ⁻¹ ≠ 0 := by
    simpa [pow_one] using
      primRoot_pow_add_inv_ne_zero_of_four_mul_lt (F := F) (ζ := ζ) (k := 1) hn hζ
        one_ne_zero (by omega : 1 * 4 < n)
  have hc' : ζ ^ 2 + (ζ ^ 2)⁻¹ ≠ 0 :=
    primRoot_pow_add_inv_ne_zero_of_four_mul_lt (F := F) (ζ := ζ) (k := 2) hn hζ
      (by norm_num : (2 : ℕ) ≠ 0) (by omega : 2 * 4 < n)
  have hne : ζ + ζ⁻¹ ≠ ζ ^ 2 + (ζ ^ 2)⁻¹ :=
    primRoot_add_inv_ne_sq_add_inv hn hζ (by omega : 1 < n) (by omega : 3 < n)
  have hsign : ζ + ζ⁻¹ ≠ -(ζ ^ 2 + (ζ ^ 2)⁻¹) :=
    primRoot_add_inv_ne_neg_sq_add_inv hn hζ (by omega : 2 < n) (by omega : 6 < n)
  exact n_lt_e2BadScalarSet_mu_card_of_two_quadT_even_modSignNonCollision
    (F := F) (n := n) (ζ := ζ) (x := (1 : F)) (x' := (1 : F)) (t := ζ)
    (t' := ζ ^ 2) hn heven0 hζ hNC h1G h1G hζG hζ2G
    hone
    (by simpa using hζne1)
    (by simpa using hζneneg1)
    (by simpa using hζinvne1)
    (by simpa using hζinvneneg1)
    (by simpa using hζneinv)
    hone
    (by simpa using hζ2ne1)
    (by simpa using hζ2neneg1)
    (by simpa using hζ2invne1)
    (by simpa using hζ2invneneg1)
    (by simpa using hζ2neinv)
    hc hc' hne hsign

/-- **Backwards canonical collision extractor.** If the literal `n` budget survives for the
width-4 `e₂=0` bad-scalar image, then the canonical primitive witnesses must collide:
`ζ² + ζ⁻² = u * (ζ + ζ⁻¹)` for some `u ∈ μ_n`. This is the narrow pointwise residual exposed by
the fixed-witness route. -/
theorem exists_invariant_collision_of_e2BadScalarSet_mu_card_le_n_primitive_zeta_sq_even
    {n : ℕ} {ζ : F} (hn : 0 < n) (heven : 2 ∣ n) (hn8 : 8 < n)
    (hζ : IsPrimitiveRoot ζ n)
    (hbudget : (e2BadScalarSet (Polynomial.nthRootsFinset n (1 : F)) 4).card ≤ n) :
    ∃ u ∈ Polynomial.nthRootsFinset n (1 : F),
      ζ ^ 2 + (ζ ^ 2)⁻¹ = u * (ζ + ζ⁻¹) := by
  by_contra hnone
  have hno :
      ∀ u ∈ Polynomial.nthRootsFinset n (1 : F),
        ζ ^ 2 + (ζ ^ 2)⁻¹ ≠ u * (ζ + ζ⁻¹) := by
    intro u hu hcollision
    exact hnone ⟨u, hu, hcollision⟩
  have hpair :
      InvariantPairNonCollision (Polynomial.nthRootsFinset n (1 : F)) ζ (ζ ^ 2) := hno
  exact
    (not_e2BadScalarSet_mu_card_le_n_of_primitive_zeta_sq_even_pairNonCollision
      hn heven hn8 hζ hpair) hbudget

/-- **Backwards ratio obstruction for the fixed primitive witnesses.** If the literal `n` budget
survives, then the displayed invariant ratio must itself be an `n`-th root. This is the single
polynomial/norm-style obstruction left by the canonical `quadT 1 ζ`, `quadT 1 ζ²` lane. -/
theorem invariantRatio_pow_eq_one_of_e2BadScalarSet_mu_card_le_n_primitive_zeta_sq_even
    {n : ℕ} {ζ : F} (hn : 0 < n) (heven : 2 ∣ n) (hn8 : 8 < n)
    (hζ : IsPrimitiveRoot ζ n)
    (hbudget : (e2BadScalarSet (Polynomial.nthRootsFinset n (1 : F)) 4).card ≤ n) :
    invariantRatio ζ (ζ ^ 2) ^ n = 1 := by
  have hc : ζ + ζ⁻¹ ≠ 0 := by
    simpa [pow_one] using
      primRoot_pow_add_inv_ne_zero_of_four_mul_lt (F := F) (ζ := ζ) (k := 1) hn hζ
        one_ne_zero (by omega : 1 * 4 < n)
  have hnotPair :
      ¬ InvariantPairNonCollision (Polynomial.nthRootsFinset n (1 : F)) ζ (ζ ^ 2) := by
    intro hpair
    exact not_lt_of_ge hbudget
      (n_lt_e2BadScalarSet_mu_card_of_primitive_zeta_sq_even_pairNonCollision
        hn heven hn8 hζ hpair)
  exact (not_invariantPairNonCollision_nthRootsFinset_iff_ratio_pow_eq_one
    (F := F) hn (t := ζ) (t' := ζ ^ 2) hc).mp hnotPair

/-- **Backwards polynomial obstruction for the fixed primitive witnesses.** If the literal
`n` budget survives, then the denominator-free polynomial obstruction must vanish:
`(ζ⁴ + 1)^n = (ζ² + 1)^n`.  Thus a finite-field proof of the negated polynomial equality is
already enough to refute the scanner budget in this canonical width-4 lane. -/
theorem polynomial_eq_of_e2BadScalarSet_mu_card_le_n_primitive_zeta_sq_even
    {n : ℕ} {ζ : F} (hn : 0 < n) (heven : 2 ∣ n) (hn8 : 8 < n)
    (hζ : IsPrimitiveRoot ζ n)
    (hbudget : (e2BadScalarSet (Polynomial.nthRootsFinset n (1 : F)) 4).card ≤ n) :
    (ζ ^ 4 + 1) ^ n = (ζ ^ 2 + 1) ^ n := by
  have hratio :
      invariantRatio ζ (ζ ^ 2) ^ n = 1 :=
    invariantRatio_pow_eq_one_of_e2BadScalarSet_mu_card_le_n_primitive_zeta_sq_even
      hn heven hn8 hζ hbudget
  have hζ2neneg1 : ζ ^ 2 ≠ -1 :=
    primRoot_pow_ne_neg_one_of_two_mul_lt (F := F) (ζ := ζ) (k := 2) hζ
      (by norm_num : (2 : ℕ) ≠ 0) (by omega : 2 * 2 < n)
  have hden : ζ ^ 2 + 1 ≠ 0 := by
    intro h
    exact hζ2neneg1 (eq_neg_of_add_eq_zero_left h)
  exact (invariantRatio_zeta_sq_pow_eq_one_iff_polynomial_eq hn hζ hden).mp hratio

/-- A surviving literal `n` budget in the canonical `ZMod p` width-4 lane forces `p` to divide
the canonical obstruction resultant. -/
theorem prime_dvd_resultant_canonicalRatioPoly_of_e2BadScalarSet_mu_card_le_n_zmod
    {p n : ℕ} [Fact p.Prime] (hn : 0 < n) (heven : 2 ∣ n) (hn8 : 8 < n)
    {ζ : ZMod p} (hζ : IsPrimitiveRoot ζ n)
    (hbudget : (e2BadScalarSet (Polynomial.nthRootsFinset n (1 : ZMod p)) 4).card ≤ n) :
    (p : ℤ) ∣ Polynomial.resultant (Polynomial.cyclotomic n ℤ) (canonicalRatioPoly n)
      (Polynomial.cyclotomic n ℤ).natDegree (canonicalRatioPoly n).natDegree :=
  prime_dvd_resultant_canonicalRatioPoly_of_polynomial_eq_zmod hn hζ
    (polynomial_eq_of_e2BadScalarSet_mu_card_le_n_primitive_zeta_sq_even
      (F := ZMod p) hn heven hn8 hζ hbudget)

/-- Resultant bad-prime certificate for the canonical width-4 lane: if the literal `n` budget
survives over `ZMod p`, then `p` is at most the absolute value of one explicit nonzero integer
resultant. -/
theorem prime_le_natAbs_resultant_canonicalRatioPoly_of_e2BadScalarSet_mu_card_le_n_zmod
    {p n : ℕ} [Fact p.Prime] (hn : 0 < n) (heven : 2 ∣ n) (hn8 : 8 < n)
    {ζ : ZMod p} (hζ : IsPrimitiveRoot ζ n)
    (hbudget : (e2BadScalarSet (Polynomial.nthRootsFinset n (1 : ZMod p)) 4).card ≤ n) :
    p ≤ (Polynomial.resultant (Polynomial.cyclotomic n ℤ) (canonicalRatioPoly n)
      (Polynomial.cyclotomic n ℤ).natDegree (canonicalRatioPoly n).natDegree).natAbs := by
  have hdvd :=
    prime_dvd_resultant_canonicalRatioPoly_of_e2BadScalarSet_mu_card_le_n_zmod
      hn heven hn8 hζ hbudget
  have hne : Polynomial.resultant (Polynomial.cyclotomic n ℤ) (canonicalRatioPoly n)
        (Polynomial.cyclotomic n ℤ).natDegree (canonicalRatioPoly n).natDegree ≠ 0 :=
    resultant_canonicalRatioPoly_ne_zero hn hn8
  exact Nat.le_of_dvd (Int.natAbs_pos.mpr hne) (Int.natAbs_dvd_natAbs.mpr hdvd)

/-- Contrapositive scanner form: once the prize prime exceeds the canonical obstruction
resultant, the canonical width-4 literal `n` budget is impossible. -/
theorem not_e2BadScalarSet_mu_card_le_n_zmod_of_resultant_natAbs_lt_prime
    {p n : ℕ} [Fact p.Prime] (hn : 0 < n) (heven : 2 ∣ n) (hn8 : 8 < n)
    {ζ : ZMod p} (hζ : IsPrimitiveRoot ζ n)
    (hsmall :
      (Polynomial.resultant (Polynomial.cyclotomic n ℤ) (canonicalRatioPoly n)
        (Polynomial.cyclotomic n ℤ).natDegree (canonicalRatioPoly n).natDegree).natAbs < p) :
    ¬ (e2BadScalarSet (Polynomial.nthRootsFinset n (1 : ZMod p)) 4).card ≤ n := by
  intro hbudget
  exact not_lt_of_ge
    (prime_le_natAbs_resultant_canonicalRatioPoly_of_e2BadScalarSet_mu_card_le_n_zmod
      hn heven hn8 hζ hbudget) hsmall

/-! ### Sharp Landau-bound scanner gate for two-power domains -/

/-- The squared Landau/Mahler coefficient bound for the canonical width-4 obstruction
`canonicalRatioPoly (2^m)` against `Φ_{2^m}`. -/
noncomputable def canonicalRatioPolySharpBound (m : ℕ) : ℕ :=
  4 ^ (canonicalRatioPoly (2 ^ m)).natDegree
    * (∑ i ∈ (canonicalRatioPoly (2 ^ m)).support,
        ((canonicalRatioPoly (2 ^ m)).coeff i).natAbs ^ 2) ^ 2 ^ (m - 1)

/-- The canonical obstruction resultant has the same absolute value in either polynomial order. -/
theorem natAbs_resultant_canonicalRatioPoly_comm (n : ℕ) :
    (Polynomial.resultant (Polynomial.cyclotomic n ℤ) (canonicalRatioPoly n)
      (Polynomial.cyclotomic n ℤ).natDegree (canonicalRatioPoly n).natDegree).natAbs =
    (Polynomial.resultant (canonicalRatioPoly n) (Polynomial.cyclotomic n ℤ)
      (canonicalRatioPoly n).natDegree (Polynomial.cyclotomic n ℤ).natDegree).natAbs := by
  rw [Polynomial.resultant_comm]
  rw [Int.natAbs_mul]
  simp

/-- The sharp squared Landau/Mahler bound specialized to the canonical width-4 obstruction. -/
theorem natAbs_resultant_canonicalRatioPoly_twoPow_sq_le {m : ℕ} (hm : 1 ≤ m) :
    (Polynomial.resultant (Polynomial.cyclotomic (2 ^ m) ℤ) (canonicalRatioPoly (2 ^ m))
        (Polynomial.cyclotomic (2 ^ m) ℤ).natDegree
        (canonicalRatioPoly (2 ^ m)).natDegree).natAbs ^ 2
      ≤ canonicalRatioPolySharpBound m := by
  unfold canonicalRatioPolySharpBound
  rw [natAbs_resultant_canonicalRatioPoly_comm]
  exact ArkLib.ProximityGap.SharpResultantBound.natAbs_resultant_cyclotomic_sq_le hm _

/-- If the literal width-4 budget survives over `ZMod p` at `n = 2^m`, then `p²` is bounded by
the sharp coefficient-sum obstruction. -/
theorem prime_sq_le_canonicalRatioPolySharpBound_of_e2BadScalarSet_mu_card_le_twoPow_zmod
    {p m : ℕ} [Fact p.Prime] (hm : 4 ≤ m) {ζ : ZMod p}
    (hζ : IsPrimitiveRoot ζ (2 ^ m))
    (hbudget : (e2BadScalarSet (Polynomial.nthRootsFinset (2 ^ m) (1 : ZMod p)) 4).card
      ≤ 2 ^ m) :
    p ^ 2 ≤ canonicalRatioPolySharpBound m := by
  have hm1 : 1 ≤ m := by omega
  have hn : 0 < 2 ^ m := by positivity
  have heven : 2 ∣ 2 ^ m := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
    refine ⟨2 ^ k, ?_⟩
    rw [pow_succ]
    omega
  have hn8 : 8 < 2 ^ m := by
    calc
      8 = 2 ^ 3 := by norm_num
      _ < 2 ^ m := Nat.pow_lt_pow_right (by norm_num : 1 < 2) (by omega : 3 < m)
  have hleRes :
      p ≤ (Polynomial.resultant (Polynomial.cyclotomic (2 ^ m) ℤ)
        (canonicalRatioPoly (2 ^ m))
        (Polynomial.cyclotomic (2 ^ m) ℤ).natDegree
        (canonicalRatioPoly (2 ^ m)).natDegree).natAbs :=
    prime_le_natAbs_resultant_canonicalRatioPoly_of_e2BadScalarSet_mu_card_le_n_zmod
      (p := p) (n := 2 ^ m) hn heven hn8 hζ hbudget
  have hleSq :
      p ^ 2 ≤ (Polynomial.resultant (Polynomial.cyclotomic (2 ^ m) ℤ)
        (canonicalRatioPoly (2 ^ m))
        (Polynomial.cyclotomic (2 ^ m) ℤ).natDegree
        (canonicalRatioPoly (2 ^ m)).natDegree).natAbs ^ 2 :=
    Nat.pow_le_pow_left hleRes 2
  exact le_trans hleSq (natAbs_resultant_canonicalRatioPoly_twoPow_sq_le hm1)

/-- Scanner-facing contrapositive: if the sharp coefficient-sum obstruction is already below
`p²`, the literal width-4 `≤ n` budget cannot survive at `n = 2^m`. -/
theorem not_e2BadScalarSet_mu_card_le_twoPow_zmod_of_canonicalRatioPolySharpBound_lt_prime_sq
    {p m : ℕ} [Fact p.Prime] (hm : 4 ≤ m) {ζ : ZMod p}
    (hζ : IsPrimitiveRoot ζ (2 ^ m))
    (hsmall : canonicalRatioPolySharpBound m < p ^ 2) :
    ¬ (e2BadScalarSet (Polynomial.nthRootsFinset (2 ^ m) (1 : ZMod p)) 4).card ≤ 2 ^ m := by
  intro hbudget
  exact not_lt_of_ge
    (prime_sq_le_canonicalRatioPolySharpBound_of_e2BadScalarSet_mu_card_le_twoPow_zmod
      hm hζ hbudget) hsmall

/-- Fixed primitive-root scanner-failure form for the canonical witnesses
`quadT 1 ζ` and `quadT 1 ζ²`. -/
theorem not_e2BadScalarSet_mu_card_le_n_of_primitive_zeta_sq_even_modSignNonCollision
    {n : ℕ} {ζ : F} (hn : 0 < n) (heven : 2 ∣ n) (hn8 : 8 < n)
    (hζ : IsPrimitiveRoot ζ n)
    (hNC : Cd₀NonCollisionModSign (Polynomial.nthRootsFinset n (1 : F))) :
    ¬ (e2BadScalarSet (Polynomial.nthRootsFinset n (1 : F)) 4).card ≤ n :=
  not_le.mpr
    (n_lt_e2BadScalarSet_mu_card_of_primitive_zeta_sq_even_modSignNonCollision
      hn heven hn8 hζ hNC)

/-- Budget-positive converse for the fixed primitive-root witnesses: if the literal `n`-budget
holds for `e2BadScalarSet μ_n 4`, then the repaired sign-quotiented residual must fail. -/
theorem not_cd0NonCollisionModSign_of_e2BadScalarSet_mu_card_le_n_primitive_zeta_sq_even
    {n : ℕ} {ζ : F} (hn : 0 < n) (heven : 2 ∣ n) (hn8 : 8 < n)
    (hζ : IsPrimitiveRoot ζ n)
    (hbudget : (e2BadScalarSet (Polynomial.nthRootsFinset n (1 : F)) 4).card ≤ n) :
    ¬ Cd₀NonCollisionModSign (Polynomial.nthRootsFinset n (1 : F)) := by
  intro hNC
  exact
    (not_e2BadScalarSet_mu_card_le_n_of_primitive_zeta_sq_even_modSignNonCollision
      hn heven hn8 hζ hNC) hbudget

/-- A literal `n`-budget for the canonical width-4 witnesses produces an explicit failure witness
for the repaired sign-quotiented residual.  Thus any successful finite scanner in this lane must
return a nonzero, sign-distinct invariant collision in `μ_n`. -/
theorem exists_cd0ModSign_collision_of_e2BadScalarSet_mu_card_le_n_primitive_zeta_sq_even
    {n : ℕ} {ζ : F} (hn : 0 < n) (heven : 2 ∣ n) (hn8 : 8 < n)
    (hζ : IsPrimitiveRoot ζ n)
    (hbudget : (e2BadScalarSet (Polynomial.nthRootsFinset n (1 : F)) 4).card ≤ n) :
    ∃ t ∈ Polynomial.nthRootsFinset n (1 : F), ∃ t' ∈ Polynomial.nthRootsFinset n (1 : F),
      (t + t⁻¹) ≠ 0 ∧
      (t' + t'⁻¹) ≠ 0 ∧
      (t + t⁻¹) ≠ (t' + t'⁻¹) ∧
      (t + t⁻¹) ≠ -(t' + t'⁻¹) ∧
      ∃ u ∈ Polynomial.nthRootsFinset n (1 : F),
        (t' + t'⁻¹) = u * (t + t⁻¹) := by
  have hnot :
      ¬ Cd₀NonCollisionModSign (Polynomial.nthRootsFinset n (1 : F)) :=
    not_cd0NonCollisionModSign_of_e2BadScalarSet_mu_card_le_n_primitive_zeta_sq_even
      hn heven hn8 hζ hbudget
  exact
    (not_cd0NonCollisionModSign_iff_exists_collision (F := F)
      (Polynomial.nthRootsFinset n (1 : F))).mp hnot

end ArkLib.ProximityGap.E2W4CyclotomicNonCollision

/-! ## Axiom audit (expected: `propext`, `Classical.choice`, `Quot.sound` only) -/
namespace ArkLib.ProximityGap.E2W4CyclotomicNonCollision

#print axioms quadT_subset_of_mem
#print axioms neg_one_mem_nthRootsFinset_of_even
#print axioms quadT_subset_nthRootsFinset_of_even
#print axioms quadT_prod_eq
#print axioms quadT_card
#print axioms e1_quadT
#print axioms p2_quadT
#print axioms p2_quadT_eq_e1_sq
#print axioms e2_quadT_zero
#print axioms badScalar_quadT
#print axioms badScalar_quadT_mem_e2BadScalarSet
#print axioms badScalar_quadT_mem_e2BadScalarSet_of_mem
#print axioms orbit_collision_iff
#print axioms cos_invariant_strict_anti
#print axioms cos_invariant_injOn
#print axioms not_cd0NonCollision_iff_exists_collision
#print axioms not_cd0NonCollision_of_collision
#print axioms cd0NonCollision_of_no_collision
#print axioms cd0NonCollisionModSign_of_cd0NonCollision
#print axioms not_cd0NonCollisionModSign_iff_exists_collision
#print axioms not_cd0NonCollisionModSign_of_collision
#print axioms cd0NonCollisionModSign_of_no_collision
#print axioms invariant_neg_eq_neg_invariant
#print axioms invariant_ne_neg_of_two_ne_zero
#print axioms not_cd0NonCollision_of_antipodal_collision
#print axioms not_cd0NonCollision_of_neg_mem
#print axioms not_cd0NonCollision_nthRootsFinset_of_even
#print axioms not_cd0NonCollision_nthRootsFinset_of_even_charZero
#print axioms orbits_distinct_of_nonCollision
#print axioms orbits_distinct_of_nonCollisionModSign
#print axioms not_invariantPairNonCollision_iff_exists_collision
#print axioms invariantPairNonCollision_iff_ratio_notMem
#print axioms not_invariantPairNonCollision_iff_ratio_mem
#print axioms invariantPairNonCollision_nthRootsFinset_iff_ratio_pow_ne_one
#print axioms not_invariantPairNonCollision_nthRootsFinset_iff_ratio_pow_eq_one
#print axioms orbits_distinct_of_pairNonCollision
#print axioms badScalar_orbits_distinct_of_nonCollision
#print axioms badScalar_orbits_distinct_of_nonCollisionModSign
#print axioms badScalar_orbits_distinct_of_pairNonCollision
#print axioms group_card_lt_e2BadScalarSet_card_of_two_quadT_nonCollision
#print axioms group_card_lt_e2BadScalarSet_card_of_two_quadT_modSignNonCollision
#print axioms group_card_lt_e2BadScalarSet_card_of_two_quadT_pairNonCollision
#print axioms group_card_lt_e2BadScalarSet_card_of_two_quadT_mem_nonCollision
#print axioms group_card_lt_e2BadScalarSet_card_of_two_quadT_mem_modSignNonCollision
#print axioms group_card_lt_e2BadScalarSet_card_of_two_quadT_mem_pairNonCollision
#print axioms primRoot_mem_nthRootsFinset
#print axioms primRoot_pow_mem_nthRootsFinset
#print axioms primRoot_ne_zero
#print axioms primRoot_pow_ne_one_of_lt
#print axioms primRoot_pow_ne_neg_one_of_two_mul_lt
#print axioms primRoot_pow_ne_inv_of_two_mul_lt
#print axioms primRoot_pow_add_inv_ne_zero_of_four_mul_lt
#print axioms primRoot_pow_half_eq_neg_one_of_even
#print axioms one_ne_neg_one_of_primRoot_even
#print axioms primRoot_add_inv_ne_sq_add_inv
#print axioms primRoot_add_inv_ne_neg_sq_add_inv
#print axioms complex_root_of_unity_real_eq_one_or_neg_one
#print axioms complex_root_add_inv_im_eq_zero
#print axioms invariantPairNonCollision_complex_primitive_zeta_sq
#print axioms n_lt_e2BadScalarSet_mu_card_of_two_quadT_nonCollision
#print axioms n_lt_e2BadScalarSet_mu_card_of_two_quadT_modSignNonCollision
#print axioms n_lt_e2BadScalarSet_mu_card_of_two_quadT_mem_nonCollision
#print axioms n_lt_e2BadScalarSet_mu_card_of_two_quadT_mem_modSignNonCollision
#print axioms not_e2BadScalarSet_mu_card_le_n_of_two_quadT_nonCollision
#print axioms not_e2BadScalarSet_mu_card_le_n_of_two_quadT_modSignNonCollision
#print axioms not_e2BadScalarSet_mu_card_le_n_of_two_quadT_mem_nonCollision
#print axioms not_e2BadScalarSet_mu_card_le_n_of_two_quadT_mem_modSignNonCollision
#print axioms n_lt_e2BadScalarSet_mu_card_of_two_quadT_even_nonCollision
#print axioms n_lt_e2BadScalarSet_mu_card_of_two_quadT_even_modSignNonCollision
#print axioms not_e2BadScalarSet_mu_card_le_n_of_two_quadT_even_nonCollision
#print axioms not_e2BadScalarSet_mu_card_le_n_of_two_quadT_even_modSignNonCollision
#print axioms n_lt_e2BadScalarSet_mu_card_of_primitive_zeta_sq_even_pairNonCollision
#print axioms not_e2BadScalarSet_mu_card_le_n_of_primitive_zeta_sq_even_pairNonCollision
#print axioms n_lt_e2BadScalarSet_mu_card_of_primitive_zeta_sq_even_ratioPowNeOne
#print axioms not_e2BadScalarSet_mu_card_le_n_of_primitive_zeta_sq_even_ratioPowNeOne
#print axioms invariantRatio_zeta_sq_pow_eq_one_iff_polynomial_eq
#print axioms invariantRatio_zeta_sq_pow_ne_one_iff_polynomial_ne
#print axioms invariantRatio_primitive_zeta_sq_pow_ne_one_iff_polynomial_ne
#print axioms canonicalRatioPoly_eval_map
#print axioms canonicalRatioPoly_monic
#print axioms canonicalRatioPoly_natDegree_map_zmod
#print axioms canonicalRatioPoly_eval_zmod_eq_zero_of_polynomial_eq
#print axioms n_lt_e2BadScalarSet_mu_card_of_primitive_zeta_sq_even_polynomialNe
#print axioms not_e2BadScalarSet_mu_card_le_n_of_primitive_zeta_sq_even_polynomialNe
#print axioms invariantRatio_pow_ne_one_complex_primitive_zeta_sq
#print axioms polynomial_ne_complex_primitive_zeta_sq
#print axioms resultant_canonicalRatioPoly_ne_zero
#print axioms prime_dvd_resultant_canonicalRatioPoly_of_polynomial_eq_zmod
#print axioms prime_le_natAbs_resultant_canonicalRatioPoly_of_polynomial_eq_zmod
#print axioms canonicalRatioPoly_eval_nnnorm_le_two_pow_succ
#print axioms natAbs_resultant_canonicalRatioPoly_le_two_pow_succ_totient
#print axioms polynomial_ne_zmod_of_resultant_natAbs_lt_prime
#print axioms polynomial_ne_zmod_of_two_pow_succ_totient_lt_prime
#print axioms not_e2BadScalarSet_mu_card_le_n_zmod_of_two_pow_succ_totient_lt_prime
#print axioms canonicalRatioPoly16_reduction_zmod
#print axioms canonicalRatioPoly16_bezout
#print axioms polynomial_ne_zmod16_of_prime_gt17
#print axioms not_e2BadScalarSet_mu16_card_le_16_zmod_of_prime_gt17
#print axioms n_lt_e2BadScalarSet_mu_card_of_complex_primitive_zeta_sq_even
#print axioms not_e2BadScalarSet_mu_card_le_n_of_complex_primitive_zeta_sq_even
#print axioms orderOf_4134_ratio
#print axioms isPrimitiveRoot_4134_16_ratio
#print axioms polynomial_4134_sq_pow16_ne
#print axioms invariantRatio_4134_sq_pow16_ne_one
#print axioms sixteen_lt_e2BadScalarSet_mu16_card_zmod12289_width4
#print axioms not_e2BadScalarSet_mu16_card_le_16_zmod12289_width4
#print axioms orderOf_3_ratio_zmod17
#print axioms isPrimitiveRoot_3_16_ratio_zmod17
#print axioms invariantRatio_3_sq_pow16_eq_one_zmod17
#print axioms polynomial_eq_3_sq_pow16_zmod17
#print axioms invariant_collision_scalar_5_zmod17
#print axioms exists_invariant_collision_mu16_zmod17_3
#print axioms not_invariantPairNonCollision_mu16_zmod17_3
#print axioms not_forall_primitive_pairNonCollision_zmod17_mu16
#print axioms seventeen_dvd_resultant_canonicalRatioPoly_16
#print axioms seventeen_le_natAbs_resultant_canonicalRatioPoly_16
#print axioms n_lt_e2BadScalarSet_mu_card_of_primitive_zeta_sq_even_modSignNonCollision
#print axioms exists_invariant_collision_of_e2BadScalarSet_mu_card_le_n_primitive_zeta_sq_even
#print axioms invariantRatio_pow_eq_one_of_e2BadScalarSet_mu_card_le_n_primitive_zeta_sq_even
#print axioms polynomial_eq_of_e2BadScalarSet_mu_card_le_n_primitive_zeta_sq_even
#print axioms prime_dvd_resultant_canonicalRatioPoly_of_e2BadScalarSet_mu_card_le_n_zmod
#print axioms prime_le_natAbs_resultant_canonicalRatioPoly_of_e2BadScalarSet_mu_card_le_n_zmod
#print axioms not_e2BadScalarSet_mu_card_le_n_zmod_of_resultant_natAbs_lt_prime
#print axioms natAbs_resultant_canonicalRatioPoly_comm
#print axioms natAbs_resultant_canonicalRatioPoly_twoPow_sq_le
#print axioms prime_sq_le_canonicalRatioPolySharpBound_of_e2BadScalarSet_mu_card_le_twoPow_zmod
#print axioms not_e2BadScalarSet_mu_card_le_twoPow_zmod_of_canonicalRatioPolySharpBound_lt_prime_sq
#print axioms not_e2BadScalarSet_mu_card_le_n_of_primitive_zeta_sq_even_modSignNonCollision
#print axioms not_cd0NonCollisionModSign_of_e2BadScalarSet_mu_card_le_n_primitive_zeta_sq_even
#print axioms exists_cd0ModSign_collision_of_e2BadScalarSet_mu_card_le_n_primitive_zeta_sq_even

end ArkLib.ProximityGap.E2W4CyclotomicNonCollision
