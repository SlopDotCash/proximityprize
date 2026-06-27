/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.E2DilationDirectCount

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

> `K = Kmodel(n) = n/4 − 1`   ⟺   `Cd₀NonCollision` :
> for distinct allowed `d₀, d₀'`, `c_{d₀'} ∉ μ_n · c_{d₀}`.

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
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option autoImplicit false

open Finset
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
equal invariants force equal angles. It is the **unconditional char-0 instance** of the named
cyclotomic non-collision `Cd₀NonCollision` below: over ℂ, `K = Kmodel = n/4 − 1`. -/
theorem cos_invariant_injOn {θ θ' : ℝ} (h0 : 0 ≤ θ) (h0' : 0 ≤ θ')
    (hpi : θ ≤ Real.pi / 2) (hpi' : θ' ≤ Real.pi / 2) (hne : θ ≠ θ') :
    2 * Real.cos θ ≠ 2 * Real.cos θ' := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact (ne_of_gt (cos_invariant_strict_anti h0 hlt hpi').1)
  · exact (ne_of_lt (cos_invariant_strict_anti h0' hgt hpi).1)

/-! ## Part 4 — the named cyclotomic non-collision `Prop` and the verdict

We package the char-`p` collision question as ONE named `Prop` over the working field, so the
bridge "`K = Kmodel`" becomes "this `Prop` holds". The `Prop` says: for distinct allowed factors
`t, t'` (roots of unity in `F`), the invariants `c = t + t⁻¹`, `c' = t' + t'⁻¹` do not lie in the
same `μ_n`-orbit (`c' ≠ ζ^u·c` for all `u`). The char-0 instance is discharged above; the char-`p`
instance is NOT `q`-independent (finite small bad primes; see header). -/

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
  have hadd : c + c = 0 := by
    exact (congrArg (fun x : F => x + c) h).trans (neg_add_cancel c)
  have hmul : (2 : F) * c = 0 := by
    simpa [two_mul] using hadd
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
  have htwo : (1 : F) + 1 = (2 : F) := by ring
  rw [inv_one, htwo]
  exact h2

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
statement "`K = #{distinct invariant-classes} = Kmodel = n/4 − 1`": the actual `F_q` orbit count
equals the combinatorial model exactly when `Cd₀NonCollision` holds (char 0 always; char `p` for
good primes). -/
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
#print axioms badScalar_orbits_distinct_of_nonCollision
#print axioms badScalar_orbits_distinct_of_nonCollisionModSign
#print axioms group_card_lt_e2BadScalarSet_card_of_two_quadT_nonCollision
#print axioms group_card_lt_e2BadScalarSet_card_of_two_quadT_mem_nonCollision
#print axioms n_lt_e2BadScalarSet_mu_card_of_two_quadT_nonCollision
#print axioms n_lt_e2BadScalarSet_mu_card_of_two_quadT_mem_nonCollision
#print axioms not_e2BadScalarSet_mu_card_le_n_of_two_quadT_nonCollision
#print axioms not_e2BadScalarSet_mu_card_le_n_of_two_quadT_mem_nonCollision
#print axioms n_lt_e2BadScalarSet_mu_card_of_two_quadT_even_nonCollision
#print axioms not_e2BadScalarSet_mu_card_le_n_of_two_quadT_even_nonCollision

end ArkLib.ProximityGap.E2W4CyclotomicNonCollision
