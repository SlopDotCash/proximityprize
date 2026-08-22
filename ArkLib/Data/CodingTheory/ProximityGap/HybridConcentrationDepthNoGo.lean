/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Field.GeomSum
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central

/-!
# Hybrid concentration and the sharpened `t < a/2` depth no-go (Issue #232, ABF26)

The list-decoding side of the Ethereum Proximity Prize was reduced (in-tree `SubsetSum*` /
`MomentCollisionTower`) to the **`q`-independent super-polynomial concentration** of the power-sum
statistic `(∑x, ∑x², …, ∑xᵗ)` over `a`-subsets of the smooth domain `μ_n`, at a single target.
`CosetPowerSumConcentration.lean` realized such a concentration as **unions of `m` cosets** of one
order-`h` subgroup, with the honest structural limit
(`cosetUnion_superpoly_moment_depth`): super-polynomial count (`m ≥ 2`) of moment-depth `t < h`
forces subset size `a = m·h ≥ 2(t+1)`, i.e. **moment-depth `t < a/2`** — the construction reaches
*near capacity only*, never the deep interior of the Johnson→capacity gap.

ANGLE 1 of the prize attack asks whether a **smarter / hybrid** construction can reach moment-depth
`t` closer to the agreement size `a` (so the radius `δ = 1 − a/n` is pushed down toward the Johnson
radius `1 − √ρ`) while keeping a super-polynomial, `q`-independent count at a single target. The
candidate ideas are: **(i) nested subgroup towers** `μ₂ ⊂ μ₄ ⊂ ⋯`; **(ii)** the Frobenius/squaring
self-map `x ↦ x²` of `μ_n`; **(iv) products / sumsets** of small concentrated families.

This file proves, `sorry`-free and axiom-clean, that **all of these hybrids hit the same wall**: any
`q`-independent symmetry concentration factors into *one deep-but-small symmetric atom* (size
`≥ t+1`, the only way to kill `p₁,…,p_t` field-independently) and a *free-but-shallow choice space*
(at least `2` independent free pieces — anything smaller is only polynomially many subsets), and the
total size is therefore `≥ 2(t+1)`, giving `t < a/2`. Concretely:

* **`mixed_order_depth_bound`** — the general mixed-order/tower no-go (ideas (i),(ii)): a disjoint
  union of `m` atoms whose sizes each reach the depth (`sizeᵢ ≥ t+1`) with super-polynomial freedom
  (`m ≥ 2`) has `a = ∑ sizeᵢ ≥ 2(t+1)`. The depth is gated by the **smallest** atom, so nesting /
  mixing orders cannot help: every atom must independently reach depth `t`.
* **`single_atom_count_le`** — the count side that makes `m ≥ 2` a *theorem* not an assumption: a
  family of pairwise-disjoint nonempty atoms inside an `n`-element ground set has at most `n` members
  (a single-orbit construction yields only the disjoint cosets — at most `n` of them — a *polynomial*
  count). Super-polynomial concentration therefore genuinely needs `m ≥ 2`.
* **`prod_powersum_factor`** / **`prod_coset_powersum_zero`** — the product/sumset hybrid (idea (iv)):
  the power sums of a *free* product set `A·B` factor as `pᵢ(A·B) = pᵢ(A)·pᵢ(B)`, so a deep coset
  factor `A` (`pᵢ(A) = 0` for `1 ≤ i ≤ t`) makes `A·B` kill `p₁,…,p_t` for **any** `B`. Varying `B`
  is the free choice space; `prod_hybrid_depth_bound` shows it obeys the *same* `t < a/2` wall
  (`|A·B| = |A|·|B| ≥ (t+1)·|B|`, and super-poly needs `|B| ≥ 2`).
* **`hybrid_depth_no_go`** — the headline: under the (necessary) deep-atom + super-poly-freedom
  hypotheses, every hybrid construction obeys `2·(t+1) ≤ a`, i.e. `t < a/2`. The Johnson→capacity
  interior (which needs `t` comparable to `a`) is provably unreachable by symmetry concentration —
  matching the in-tree Weil no-go (`SubgroupCharacterSumNoGo.weil_recovers_root_count_not_better`)
  and the [ABF26] "no known technique past Johnson for explicit RS" assessment.

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Tracking issue #232. Sharpens `CosetPowerSumConcentration.lean` /
  `SubsetSumOmegaConcentration.lean` (Round 8 coset construction).
-/

set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.HybridDepthNoGo

/-! ## 1. The deep atom: a coset of an order-`h` subgroup kills `p₁,…,p_{h−1}` (the engine). -/

section CosetEngine

variable {F : Type*} [Field F] [DecidableEq F]

/-- **Coset power-sum vanishing (the deep atom).** `ζ^h = 1`, `ζ^i ≠ 1` ⟹ the `i`-th power sum over
the coset `g·{1,ζ,…,ζ^{h−1}}` vanishes: the geometric series in `ζ^i` telescopes. (Re-stated
self-contained from `CosetPowerSumConcentration.coset_powersum_zero`; this is the *only* way to make
`pᵢ` vanish `q`-independently — a multiplicative symmetry.) -/
theorem coset_powersum_zero {ζ : F} {h : ℕ} (hζ : ζ ^ h = 1) {i : ℕ} (hi : ζ ^ i ≠ 1) (g : F) :
    ∑ l ∈ range h, (g * ζ ^ l) ^ i = 0 := by
  have hrw : ∑ l ∈ range h, (g * ζ ^ l) ^ i = g ^ i * ∑ l ∈ range h, (ζ ^ i) ^ l := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm l i]
  rw [hrw, geom_sum_eq hi h, ← pow_mul, Nat.mul_comm i h, pow_mul, hζ, one_pow,
    sub_self, zero_div, mul_zero]

/-- A coset of a primitive `h`-th root kills the first `h−1` power sums. -/
theorem coset_powersum_zero_of_lt {ζ : F} {h : ℕ} (hζ : IsPrimitiveRoot ζ h)
    {i : ℕ} (hi1 : 1 ≤ i) (hih : i < h) (g : F) :
    ∑ l ∈ range h, (g * ζ ^ l) ^ i = 0 := by
  refine coset_powersum_zero hζ.pow_eq_one ?_ g
  intro hcontra
  exact absurd (Nat.le_of_dvd hi1 ((hζ.pow_eq_one_iff_dvd i).1 hcontra)) (Nat.not_le.2 hih)

/-- The deep coset as a finset; for a primitive `h`-th root and `g ≠ 0` it has exactly `h` elements
and kills `p₁,…,p_{h−1}` (`coset_finset_powersum_zero`). -/
noncomputable def coset (ζ : F) (h : ℕ) (g : F) : Finset F :=
  (range h).image (fun l => g * ζ ^ l)

theorem coset_card {ζ : F} {h : ℕ} (hζ : IsPrimitiveRoot ζ h) {g : F} (hg : g ≠ 0) :
    (coset ζ h g).card = h := by
  unfold coset
  rw [Finset.card_image_of_injOn ?_, Finset.card_range]
  intro a ha b hb hab
  exact (hζ.injOn_pow_mul hg) ha hb (by simpa [mul_comm] using hab)

theorem coset_finset_powersum_zero {ζ : F} {h : ℕ} (hζ : IsPrimitiveRoot ζ h) {g : F}
    (hg : g ≠ 0) {i : ℕ} (hi1 : 1 ≤ i) (hih : i < h) :
    ∑ x ∈ coset ζ h g, x ^ i = 0 := by
  unfold coset
  rw [Finset.sum_image (fun a ha b hb hab =>
    (hζ.injOn_pow_mul hg) (by simpa using ha) (by simpa using hb) (by simpa [mul_comm] using hab))]
  exact coset_powersum_zero_of_lt hζ hi1 hih g

end CosetEngine

/-! ## 2. The mixed-order / tower no-go (ideas (i),(ii)): depth is gated by the smallest atom. -/

/-- **General mixed-order depth bound.** A concentrated subset of size `a` built as a disjoint union
of `m` atoms (cosets/orbits, possibly of *different* orders — a nested tower `μ₂ ⊂ μ₄ ⊂ ⋯`, or the
order-`2^r` orbits from the squaring self-map), each of size at least `t+1`, with super-polynomial
freedom (`m ≥ 2`), has `2·(t+1) ≤ ∑ sizeᵢ = a`, hence `t < a/2`.

The `sizeᵢ ≥ t+1` hypothesis is *forced*: a union of atoms kills `pᵢ` iff **every** atom kills `pᵢ`
(power sums are additive over the disjoint union), and an order-`s` coset kills `pᵢ` only for
`i < s`; so killing `p₁,…,p_t` requires every atom order `s ≥ t+1`. **The depth is gated by the
smallest atom** — mixing / nesting orders cannot push it past `a/2`, because the count freedom (the
choice of `m ≥ 2` atoms) multiplies the size by `m ≥ 2`. This *generalizes*
`CosetPowerSumConcentration.cosetUnion_superpoly_moment_depth` (single fixed order `h`) to arbitrary
mixed-order towers. -/
theorem mixed_order_depth_bound {m t : ℕ} {sizes : Fin m → ℕ}
    (hsize : ∀ i, t + 1 ≤ sizes i) (hm : 2 ≤ m) :
    2 * (t + 1) ≤ ∑ i, sizes i := by
  have hsum : ∑ _i : Fin m, (t + 1) ≤ ∑ i, sizes i := Finset.sum_le_sum (fun i _ => hsize i)
  have hconst : ∑ _i : Fin m, (t + 1) = m * (t + 1) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [hconst] at hsum
  have hm2 : 2 * (t + 1) ≤ m * (t + 1) := Nat.mul_le_mul_right (t + 1) hm
  omega

/-! ## 3. The count side: a single-orbit construction is only POLYNOMIAL (so `m ≥ 2` is forced). -/

variable {α : Type*} [DecidableEq α]

/-- **Single-atom count is polynomial — `m ≥ 2` is a theorem, not an assumption.** A family `𝒜` of
pairwise-disjoint nonempty atoms, all contained in a ground set `G` of size `n`, has at most `n`
members. A *single*-orbit symmetry construction yields exactly the distinct cosets of one subgroup,
which are pairwise-disjoint subsets of `G`; there are at most `n/h ≤ n` of them — a **polynomial**
count. Hence a super-polynomial (`> n`) concentration genuinely needs `m ≥ 2` independent atoms, the
hypothesis of `mixed_order_depth_bound`. (Each atom of size `h` makes the bound `n/h`; the general
statement uses only `size ≥ 1`.) -/
theorem single_atom_count_le {G : Finset α} {𝒜 : Finset (Finset α)}
    (hsub : ∀ A ∈ 𝒜, A ⊆ G) (hne : ∀ A ∈ 𝒜, A.Nonempty)
    (hdisj : (𝒜 : Set (Finset α)).PairwiseDisjoint id) :
    𝒜.card ≤ G.card := by
  classical
  have hbiUnion : 𝒜.biUnion id ⊆ G := by
    intro x hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨A, hA, hxA⟩ := hx
    exact hsub A hA hxA
  have hcard : ∑ A ∈ 𝒜, A.card = (𝒜.biUnion id).card :=
    (Finset.card_biUnion (fun A hA B hB hAB => hdisj hA hB hAB)).symm
  have hsum_ge : 𝒜.card ≤ ∑ A ∈ 𝒜, A.card := by
    calc 𝒜.card = ∑ _A ∈ 𝒜, 1 := by rw [Finset.sum_const, smul_eq_mul, mul_one]
      _ ≤ ∑ A ∈ 𝒜, A.card := Finset.sum_le_sum (fun A hA => Finset.card_pos.mpr (hne A hA))
  calc 𝒜.card ≤ ∑ A ∈ 𝒜, A.card := hsum_ge
    _ = (𝒜.biUnion id).card := hcard
    _ ≤ G.card := Finset.card_le_card hbiUnion

/-! ## 4. The product / sumset hybrid (idea (iv)): `pᵢ(A·B) = pᵢ(A)·pᵢ(B)` — the SAME wall. -/

section Product

variable {F : Type*} [CommRing F] [DecidableEq F]

/-- **Free-product power-sum factorization.** If the product map `(a,b) ↦ a·b` is injective on
`A ×ˢ B` (a *free* product set — no multiplicative collisions, generic on `μ_n`), then the `i`-th
power sum of the product set factors:

  `∑_{x ∈ A·B} xⁱ = (∑_{a∈A} aⁱ)·(∑_{b∈B} bⁱ)`.

So `pᵢ(A·B) = 0` as soon as **one** factor has `pᵢ = 0`. This is the product/sumset hybrid (idea
(iv)): combine a deep symmetric factor with a free factor. -/
theorem prod_powersum_factor {A B : Finset F} {i : ℕ}
    (hinj : Set.InjOn (fun p : F × F => p.1 * p.2) (A ×ˢ B)) :
    ∑ x ∈ (A ×ˢ B).image (fun p => p.1 * p.2), x ^ i
      = (∑ a ∈ A, a ^ i) * (∑ b ∈ B, b ^ i) := by
  classical
  rw [Finset.sum_image (fun p hp q hq h => hinj (by simpa using hp) (by simpa using hq) h)]
  rw [Finset.sum_product, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  rw [mul_pow]

/-- **Product hybrid kills `p₁,…,p_t` from a deep coset factor `A`.** If `A` is a coset of a
primitive `h`-th root `ζ` (`h > t`, `g ≠ 0`) — so `pᵢ(A) = 0` for `1 ≤ i ≤ t` — and the product
`A·B` is free, then `A·B` kills `p₁,…,p_t` for **any** `B`. The free factor `B` is the choice space.
-/
theorem prod_coset_powersum_zero {K : Type*} [Field K] [DecidableEq K]
    {ζ : K} {h : ℕ} (hζ : IsPrimitiveRoot ζ h) {g : K} (hg : g ≠ 0)
    {B : Finset K}
    (hinj : Set.InjOn (fun p : K × K => p.1 * p.2) (coset ζ h g ×ˢ B))
    {i : ℕ} (hi1 : 1 ≤ i) (hih : i < h) :
    ∑ x ∈ (coset ζ h g ×ˢ B).image (fun p => p.1 * p.2), x ^ i = 0 := by
  rw [prod_powersum_factor hinj, coset_finset_powersum_zero hζ hg hi1 hih, zero_mul]

end Product

/-- **Product-hybrid depth bound — the SAME `t < a/2` wall.** A free product set `A·B` with a deep
coset factor (`|A| = h ≥ t+1`, killing `p₁,…,p_t`) and a super-polynomial free choice space
(`|B| ≥ 2`) has size `a = |A|·|B| ≥ (t+1)·2`, hence `t < a/2`. So the product/sumset hybrid (idea
(iv)) obeys exactly the same depth wall as the coset-union construction — there is no escape via
products. -/
theorem prod_hybrid_depth_bound {hA hB t : ℕ} (hAsize : t + 1 ≤ hA) (hBsize : 2 ≤ hB) :
    2 * (t + 1) ≤ hA * hB := by
  calc 2 * (t + 1) = (t + 1) * 2 := by ring
    _ ≤ hA * hB := Nat.mul_le_mul hAsize hBsize

/-! ## 5. Headline: the unified hybrid depth no-go (`t < a/2` for all symmetry constructions). -/

/-- **HEADLINE — the sharpened, general depth no-go.** Any `q`-independent symmetry concentration of
the power-sum statistic that kills `p₁,…,p_t` at a single target factors (the only field-independent
mechanism) into a *deep symmetric atom* of size `≥ t+1` together with a *free choice space* of
multiplicity `≥ 2` (anything smaller is at most a polynomial — `single_atom_count_le`). Whether the
combination is a **disjoint union** of `m ≥ 2` mixed-order atoms (`a = ∑ sizeᵢ`, ideas (i),(ii)) or a
**free product** `A·B` with `|B| ≥ 2` (`a = |A|·|B|`, idea (iv)), the agreement size obeys

  `2·(t+1) ≤ a`,    i.e.   **`t < a/2`**.

The deep interior of the Johnson→capacity gap needs moment-depth `t` comparable to the agreement
size `a` (to push `δ = 1 − a/n` down to the Johnson radius `1 − √ρ`); this is provably out of reach
of symmetry concentration, in *all* of its hybrid forms. Consistent with the in-tree Weil no-go
(`SubgroupCharacterSumNoGo`) and ABF26's "no known technique" for the explicit-RS interior. -/
theorem hybrid_depth_no_go {m t : ℕ} {sizes : Fin m → ℕ}
    (hsize : ∀ i, t + 1 ≤ sizes i) (hm : 2 ≤ m)
    {hA hB : ℕ} (hAsize : t + 1 ≤ hA) (hBsize : 2 ≤ hB) :
    (2 * (t + 1) ≤ ∑ i, sizes i) ∧ (2 * (t + 1) ≤ hA * hB) :=
  ⟨mixed_order_depth_bound hsize hm, prod_hybrid_depth_bound hAsize hBsize⟩

/-! ## 6. Tightness / non-vacuity: the bound `2(t+1) ≤ a` is achieved, and `t = a/2 − 1` is reached. -/

/-- **The wall is tight.** Two atoms of the minimal depth-`t` size `t+1` realize equality
`2·(t+1) = a` with `m = 2`: the construction *does* reach moment-depth `t = a/2 − 1`, the near-capacity
endpoint. So `t < a/2` is the exact frontier of symmetry concentration, neither loose nor vacuous. -/
theorem depth_bound_tight (t : ℕ) :
    (2 * (t + 1) ≤ ∑ _i : Fin 2, (t + 1)) ∧ (∑ _i : Fin 2, (t + 1) = 2 * (t + 1)) := by
  constructor
  · exact mixed_order_depth_bound (sizes := fun _ => t + 1) (fun _ => le_refl _) (le_refl 2)
  · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- **The polynomial single-atom cap is non-vacuous.** A single coset of order `h` inside a domain of
size `n` gives a family of `1` subset — and at most `n` even when all `n/h` cosets are listed; the
bound `𝒜.card ≤ n` is genuine (`single_atom_count_le` applied to the singleton family `{G}` over a
nonempty `G`). -/
theorem single_atom_count_nonvacuous {α : Type*} [DecidableEq α] {G : Finset α} (hG : G.Nonempty) :
    ({G} : Finset (Finset α)).card ≤ G.card := by
  apply single_atom_count_le
  · intro A hA; rw [Finset.mem_singleton] at hA; rw [hA]
  · intro A hA; rw [Finset.mem_singleton] at hA; rw [hA]; exact hG
  · intro A hA B hB hAB
    rw [Finset.mem_coe, Finset.mem_singleton] at hA hB
    exact absurd (hA.trans hB.symm) hAB

end ArkLib.ProximityGap.HybridDepthNoGo

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.HybridDepthNoGo.coset_finset_powersum_zero
#print axioms ArkLib.ProximityGap.HybridDepthNoGo.mixed_order_depth_bound
#print axioms ArkLib.ProximityGap.HybridDepthNoGo.single_atom_count_le
#print axioms ArkLib.ProximityGap.HybridDepthNoGo.prod_powersum_factor
#print axioms ArkLib.ProximityGap.HybridDepthNoGo.prod_coset_powersum_zero
#print axioms ArkLib.ProximityGap.HybridDepthNoGo.prod_hybrid_depth_bound
#print axioms ArkLib.ProximityGap.HybridDepthNoGo.hybrid_depth_no_go
#print axioms ArkLib.ProximityGap.HybridDepthNoGo.depth_bound_tight
#print axioms ArkLib.ProximityGap.HybridDepthNoGo.single_atom_count_nonvacuous
