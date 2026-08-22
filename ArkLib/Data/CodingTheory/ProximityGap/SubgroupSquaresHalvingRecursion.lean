/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubsetSumEsymmVanishing
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Algebra.Field.ZMod

/-!
# Round 8 (Issue #232, ABF26) — SEAM A is a RECURSION: the pair-squares of the smooth `2^k`-subgroup
# `G` are *themselves* the order-`2^{k-1}` subgroup of squares `G²`, so the second-coordinate spread
# question reduces to the SAME subset-sum question one level down.

Round 7 (`SubsetSumNegSymmConcentration.lean`) localized the prize-counterexample door to a single
remaining spread. A smooth `2^k`-subgroup `G = ⟨ζ⟩` of order `n = 2m` is closed under negation
(`−1 = ζ^m ∈ G`); a transversal `H` of the `±`-pairs gives `G = H ⊔ (−H)` with `|H| = m`. For a
negation-symmetric subset `S = P ∪ (−P)` (`P ⊆ H`) the first coordinate is *pinned*:
`e_1(S) = ∑_{x∈S} x = 0` (`negSymm_sum_eq_zero`, `q`-independent, count `C(m, t)`). The **only**
remaining spread is the second coordinate

  `p_2(S) = ∑_{x∈S} x² = 2·∑_{g∈P} g²`   (`negClosure_psum2_eq_two_mul`, Round 7).

So a prize counterexample (`q`-independent super-polynomial list) needs the **pair-square set**
`{g² : g ∈ H}` to have *small additive span*: `#{ ∑_{g∈P} g² : P ⊆ H, |P| = t } = O(poly)`. That is
the narrowest door (SEAM A).

A strong *additive* constraint is already in hand: the pair-squares **sum to zero**,
`∑_{g∈H} g² = (1/2)·∑_{x∈G} x² = 0` (`SubsetSumEsymmVanishing`, `p_2(G) = 0`). Round 8 asks: does this
vanishing force concentration?

## What this round proves — the pair-squares ARE a subgroup (SEAM A recurses, it does not close)

The answer is **structural and negative for the "concentration" hope**: the pair-square set is not a
sparse/degenerate set on which subset-sums could collapse — it is itself a full multiplicative
**subgroup**. Concretely, with `n = 2m`:

* `sq_mem_half` / `image_sq_subset_half` — squaring maps `G = nthRootsFinset n 1` **into**
  `nthRootsFinset m 1`: `x^n = 1 ⟹ (x²)^m = x^{2m} = 1`.
* `image_sq_eq_half` — **the headline structural identity**

    `(nthRootsFinset (2m) 1).image (· ²) = nthRootsFinset m 1`     (`m ≥ 1`),

  i.e. the squares of the order-`2m` subgroup are **exactly** the order-`m` subgroup. Surjectivity
  uses that `ζ²` is a primitive `m`-th root (`IsPrimitiveRoot.pow`) and every `m`-th root is a power
  of it (`eq_pow_of_pow_eq_one`), so each `y = (ζ²)^j = (ζ^j)²` is the square of `ζ^j ∈ G`.
* `image_sq_card_eq_half` — the squaring image has card exactly `m = n/2` (the squaring map on the
  even-order cyclic subgroup is exactly `2`-to-`1`).
* `pairSquares_eq_half_subgroup` — the **pair-square set of any transversal `H` equals the order-`m`
  subgroup**: `H.image (· ²) = nthRootsFinset m 1`. (Each `±`-pair `{x, −x}` shares its square, so the
  squares of the half-transversal `H` are all the squares of `G`.) This is the precise statement that
  SEAM A's pair-squares `{g² : g ∈ H}` are the *next* smooth subgroup `G² = nthRootsFinset m 1`.

## The verdict — a structural NO-GO for the concentration door (honest)

The pair-square set `{g² : g ∈ H}` is **not** a small/structured set whose subset-sums collapse:
it is the order-`2^{k-1}` cyclic subgroup `nthRootsFinset (n/2) 1`. Therefore

  `#{ ∑_{g∈P} g² : P ⊆ H, |P| = t }  =  #{ size-`t` subset-sums over `nthRootsFinset (n/2) 1` }`,

which is **the SAME subset-sum spread question, one level down** (`k → k−1`, `n → n/2`). The
vanishing `∑_{g∈H} g² = 0` is exactly the `e_1 = 0` identity *for the smaller subgroup*
(`subgroup_sum_eq_zero` at `n/2`) — it is the recursion's *own* first-coordinate concentration,
not a new collapse of the second. So SEAM A does **not** close: the second coordinate's spread is
governed by the *identical* open subset-sum problem on the half-size smooth subgroup. The door
recurses; it is not walked through.

What this is and is NOT:
* It **IS** a genuine, `sorry`-free, axiom-clean structural identity:
  `(nthRootsFinset (2m) 1).image (· ²) = nthRootsFinset m 1`, and the transversal corollary
  `H.image (· ²) = nthRootsFinset m 1`, exhibiting the pair-squares as the next smooth subgroup.
* It is **NOT** a concentration proof and **NOT** a prize counterexample: it shows the vanishing-sum
  constraint does **not** force `p_2` concentration — instead the question recurses to the same
  subset-sum problem at `n/2`, which remains open. We *characterize* the door, we do not close it.

All headline results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Tracking issue #232.
-/

open Polynomial BigOperators Finset

namespace ArkLib.ProximityGap.Round8SeamARecursion

variable {R : Type*} [CommRing R] [IsDomain R] [DecidableEq R]

/-! ## 1. Squaring maps the order-`2m` subgroup into the order-`m` subgroup. -/

omit [DecidableEq R] in
/-- **Squaring lands in the half-order subgroup.** If `x ∈ G = nthRootsFinset (2m) 1`
(so `x^{2m}=1`), then `x² ∈ nthRootsFinset m 1`, because `(x²)^m = x^{2m} = 1`. This is the *forward*
direction of the structural identity: the squares of the order-`2m` subgroup are `m`-th roots. -/
theorem sq_mem_half {m : ℕ} {x : R} (hx : x ∈ nthRootsFinset (2 * m) (1 : R)) :
    x ^ 2 ∈ nthRootsFinset m (1 : R) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simp only [Nat.mul_zero, nthRootsFinset_zero, Finset.notMem_empty] at hx
  · rw [mem_nthRootsFinset (by omega : 0 < 2 * m)] at hx
    rw [mem_nthRootsFinset hm]
    -- `(x²)^m = x^(2m) = 1`
    calc (x ^ 2) ^ m = x ^ (2 * m) := by rw [← pow_mul, mul_comm]
      _ = 1 := hx

/-- **The squaring image is contained in the half-order subgroup.**
`(nthRootsFinset (2m) 1).image (· ²) ⊆ nthRootsFinset m 1`. -/
theorem image_sq_subset_half {m : ℕ} :
    (nthRootsFinset (2 * m) (1 : R)).image (fun x => x ^ 2) ⊆ nthRootsFinset m (1 : R) := by
  classical
  intro y hy
  rw [Finset.mem_image] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  exact sq_mem_half hx

/-! ## 2. The headline structural identity: the squares of `G` ARE the order-`m` subgroup `G²`. -/

/-- **The squaring image equals the order-`m` subgroup (the SEAM-A recursion identity).** For a
primitive `2m`-th root `ζ` (`m ≥ 1`),

  `(nthRootsFinset (2m) 1).image (· ²) = nthRootsFinset m 1`.

The squares of the order-`2m` smooth subgroup are **exactly** the order-`m` smooth subgroup. The `⊆`
direction is `image_sq_subset_half`. For `⊇`: `ζ²` is a primitive `m`-th root
(`IsPrimitiveRoot.pow` with `2m = 2·m`), so every `y` with `y^m = 1` is a power `y = (ζ²)^j = (ζ^j)²`
(`eq_pow_of_pow_eq_one`), and `ζ^j ∈ G` since `(ζ^j)^{2m} = 1`. Hence `y` is the square of an
element of `G`. -/
theorem image_sq_eq_half {ζ : R} {m : ℕ} (hm : 0 < m) (hζ : IsPrimitiveRoot ζ (2 * m)) :
    (nthRootsFinset (2 * m) (1 : R)).image (fun x => x ^ 2) = nthRootsFinset m (1 : R) := by
  classical
  apply Finset.Subset.antisymm image_sq_subset_half
  -- `ζ²` is a primitive `m`-th root.
  have hζ2 : IsPrimitiveRoot (ζ ^ 2) m :=
    hζ.pow (by omega : 0 < 2 * m) (by rw [mul_comm] : 2 * m = 2 * m)
  haveI : NeZero m := ⟨by omega⟩
  intro y hy
  rw [mem_nthRootsFinset hm] at hy
  -- every `m`-th root `y` is a power of the primitive `m`-th root `ζ²`.
  obtain ⟨j, _, hj⟩ := hζ2.eq_pow_of_pow_eq_one hy
  rw [Finset.mem_image]
  refine ⟨ζ ^ j, ?_, ?_⟩
  · -- `ζ^j ∈ nthRootsFinset (2m) 1` since `(ζ^j)^{2m} = (ζ^{2m})^j = 1`.
    rw [mem_nthRootsFinset (by omega : 0 < 2 * m), ← pow_mul, mul_comm j (2 * m), pow_mul,
      hζ.pow_eq_one, one_pow]
  · -- `(ζ^j)² = (ζ²)^j = y`.
    rw [← pow_mul, mul_comm j 2, pow_mul, hj]

/-! ## 3. Cardinality: the squaring map on the even-order subgroup is exactly `2`-to-`1`. -/

/-- **The squaring image has cardinality `m = n/2`.** Combining `image_sq_eq_half` with
`card_nthRootsFinset` for the primitive `m`-th root `ζ²`:
`#((nthRootsFinset (2m) 1).image (· ²)) = #(nthRootsFinset m 1) = m`. So squaring the order-`2m`
subgroup is exactly `2`-to-`1` onto the order-`m` subgroup — the pair-squares `{g², (−g)² = g²}` of
the `m = n/2` `±`-pairs are the `m` distinct squares. -/
theorem image_sq_card_eq_half {ζ : R} {m : ℕ} (hm : 0 < m) (hζ : IsPrimitiveRoot ζ (2 * m)) :
    ((nthRootsFinset (2 * m) (1 : R)).image (fun x => x ^ 2)).card = m := by
  rw [image_sq_eq_half hm hζ]
  have hζ2 : IsPrimitiveRoot (ζ ^ 2) m :=
    hζ.pow (by omega : 0 < 2 * m) (by rw [mul_comm] : 2 * m = 2 * m)
  exact hζ2.card_nthRootsFinset

/-! ## 4. The pair-square set of a transversal `H` IS the order-`m` subgroup. -/

/-- **The pair-squares of a half-transversal are the full order-`m` subgroup.** Let
`G = nthRootsFinset (2m) 1 = H ∪ (−H)` with `H` a transversal of the `±`-pairs (encoded by
`H ∪ H.image (−·) = G` and disjointness, so `H` meets each pair once). Because `x` and `−x` have the
**same** square, the squares of `H` are all the squares of `G`:

  `H.image (· ²) = (nthRootsFinset (2m) 1).image (· ²) = nthRootsFinset m 1`.

So the SEAM-A pair-square set `{g² : g ∈ H}` is **exactly** the next smooth subgroup `G²` of order
`m = n/2`. The hypothesis `H ∪ H.image (−·) = G` is the transversal/covering property; the
`±`-collapse `(−x)² = x²` does the rest. -/
theorem pairSquares_eq_half_subgroup {ζ : R} {m : ℕ} (hm : 0 < m)
    (hζ : IsPrimitiveRoot ζ (2 * m))
    {H : Finset R} (hcover : H ∪ H.image (fun x => -x) = nthRootsFinset (2 * m) (1 : R)) :
    H.image (fun x => x ^ 2) = nthRootsFinset m (1 : R) := by
  classical
  rw [← image_sq_eq_half hm hζ, ← hcover]
  -- `(H ∪ (−H)).image (·²) = H.image (·²) ∪ (−H).image (·²)`, with `(−H).image (·²) = H.image (·²)`.
  rw [Finset.image_union]
  have hneg : (H.image (fun x => -x)).image (fun x => x ^ 2) = H.image (fun x => x ^ 2) := by
    rw [Finset.image_image]
    apply Finset.image_congr
    intro x _
    simp only [Function.comp_apply, neg_pow, even_two.neg_one_pow, one_mul]
  rw [hneg, Finset.union_idempotent]

/-! ## 5. The recursion statement: SEAM A's second-coordinate spread IS the subset-sum spread on the
half-size smooth subgroup. -/

/-- The **subset-sum value set** of a finite ground set `K` at agreement `t`: the set of values
`∑_{g∈P} g` realized by `t`-subsets `P ⊆ K`. Its cardinality `#{ ∑_{g∈P} g : |P|=t }` is exactly the
"additive span" whose smallness (poly in `|K|`) is what a prize counterexample's *concentration*
needs. -/
noncomputable def subsetSumValues (K : Finset R) (t : ℕ) : Finset R :=
  (K.powersetCard t).image (fun P => ∑ g ∈ P, g)

/-- **SEAM A recurses: the second-coordinate value set of the transversal-pair-squares is the
subset-sum value set of the half-size smooth subgroup `nthRootsFinset (n/2) 1`.** With
`n = 2m`, the pair-square set `{g² : g ∈ H}` equals `nthRootsFinset m 1`
(`pairSquares_eq_half_subgroup`). Hence the set of `t`-subset sums of the pair-squares,
`#{ ∑_{q∈Q} q : Q ⊆ {g² : g∈H}, |Q|=t }`, is **literally** the subset-sum value set of the smaller
smooth subgroup at agreement `t` — the SAME object, one recursion level down (`k → k−1`).

(We phrase the spread over the *image* set `H.image (·²)` of pair-square values; that set equals the
order-`m` subgroup, so its `t`-subset sums are exactly `subsetSumValues (nthRootsFinset m 1) t`.) -/
theorem seamA_psum2_spread_eq_subgroup_subsetSum {ζ : R} {m : ℕ} (hm : 0 < m)
    (hζ : IsPrimitiveRoot ζ (2 * m)) {H : Finset R}
    (hcover : H ∪ H.image (fun x => -x) = nthRootsFinset (2 * m) (1 : R)) (t : ℕ) :
    subsetSumValues (H.image (fun x => x ^ 2)) t
      = subsetSumValues (nthRootsFinset m (1 : R)) t := by
  rw [pairSquares_eq_half_subgroup hm hζ hcover]

/-- **The recursion is into a genuine smooth subgroup (the half-order one is still a subgroup of
roots of unity).** `nthRootsFinset m 1` is the order-`m` smooth subgroup — the SAME *kind* of ground
set the original SEAM-A question is posed over (`nthRootsFinset (2m) 1`), with `m = n/2`. So the
second-coordinate spread is governed by the identical open subset-sum problem at half the size; no
collapse to `O(1)` is implied. We record this as the literal subgroup identity at level `m`. -/
theorem half_is_smooth_subgroup {ζ : R} {m : ℕ} (hm : 0 < m) (hζ : IsPrimitiveRoot ζ (2 * m)) :
    ∃ ζ' : R, IsPrimitiveRoot ζ' m ∧
      (nthRootsFinset (2 * m) (1 : R)).image (fun x => x ^ 2) = nthRootsFinset m (1 : R) := by
  refine ⟨ζ ^ 2, hζ.pow (by omega : 0 < 2 * m) (by rw [mul_comm] : 2 * m = 2 * m), ?_⟩
  exact image_sq_eq_half hm hζ

/-! ## 6. The vanishing-sum is the recursion's OWN first coordinate (not a new collapse). -/

/-- **The pair-square vanishing `∑ g² = 0` is exactly `e_1 = 0` for the half-size subgroup.** The
Round-8 motivating constraint `∑_{g∈H} g² = (1/2)∑_{x∈G} x² = 0` is, under the structural identity
`{g² : g∈H} = nthRootsFinset m 1`, the statement `∑_{y ∈ nthRootsFinset m 1} y = 0` — i.e. the
**first-coordinate** vanishing of the *smaller* subgroup (`subgroup_sum_eq_zero` at level `m`, valid
once `m ≥ 2`). So the vanishing is the recursion's *own* `e_1`-concentration, NOT a second-coord
collapse: it provides no new concentration beyond restarting the same problem at `n/2`.

We prove the clean structural half: the sum over the pair-square *value set* `H.image (·²)` equals
the sum over the order-`m` subgroup, which vanishes for `m ≥ 2`. -/
theorem pairSquares_value_sum_eq_zero {ζ : R} {m : ℕ} (hm2 : 2 ≤ m)
    (hζ : IsPrimitiveRoot ζ (2 * m))
    {H : Finset R} (hcover : H ∪ H.image (fun x => -x) = nthRootsFinset (2 * m) (1 : R)) :
    ∑ y ∈ H.image (fun x => x ^ 2), y = 0 := by
  rw [pairSquares_eq_half_subgroup (by omega : 0 < m) hζ hcover]
  -- `ζ²` is a primitive `m`-th root; its subgroup sum vanishes for `m ≥ 2` — this is exactly the
  -- *first-coordinate* concentration of the SMALLER subgroup (Round 4 `subgroup_sum_eq_zero`).
  have hζ2 : IsPrimitiveRoot (ζ ^ 2) m :=
    hζ.pow (by omega : 0 < 2 * m) (by rw [mul_comm] : 2 * m = 2 * m)
  exact ArkLib.ProximityGap.Round4EsymmGenFun.subgroup_sum_eq_zero hζ2 hm2

/-! ## 7. Non-vacuity: the recursion identity is realized over a genuine smooth domain. -/

/-- `5` is prime, so `ZMod 5` is a field hosting a smooth `2²`-subgroup (`n = 4 = 2·2`). -/
instance primeFact_SubgroupSquaresHalvingRecursion_1 : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- **Non-vacuity: a concrete order-`4` smooth subgroup whose squares are the order-`2` subgroup.**
Over `F = ZMod 5`, `2` is a primitive `4`-th root of unity (`2¹=2, 2²=4, 2³=3, 2⁴=1`), so
`G = nthRootsFinset 4 1 = {1,2,3,4}` and the order-`2` subgroup is `nthRootsFinset 2 1 = {1,4}`
(`4 = −1`). The squaring map sends `{1,2,3,4} ↦ {1,4,4,1} = {1,4}`, exactly the order-`2` subgroup:
`image_sq_eq_half` holds non-vacuously, with the image card `= 2 = 4/2`. So SEAM A at `k=2` recurses
to the genuine order-`2` smooth subgroup — a non-degenerate witness. -/
theorem nonvacuity_zmod5 :
    IsPrimitiveRoot (2 : ZMod 5) (2 * 2) ∧
    ((nthRootsFinset (2 * 2) (1 : ZMod 5)).image (fun x => x ^ 2)).card = 2 := by
  have hroot : IsPrimitiveRoot (2 : ZMod 5) (2 * 2) := by
    have hord : orderOf (2 : ZMod 5) = 2 * 2 := by
      rw [orderOf_eq_iff (by norm_num)]
      refine ⟨by decide, ?_⟩
      intro m hm hm0
      interval_cases m <;> decide
    rw [IsPrimitiveRoot.iff_orderOf, hord]
  exact ⟨hroot, image_sq_card_eq_half (by norm_num) hroot⟩

end ArkLib.ProximityGap.Round8SeamARecursion

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Round8SeamARecursion.sq_mem_half
#print axioms ArkLib.ProximityGap.Round8SeamARecursion.image_sq_subset_half
#print axioms ArkLib.ProximityGap.Round8SeamARecursion.image_sq_eq_half
#print axioms ArkLib.ProximityGap.Round8SeamARecursion.image_sq_card_eq_half
#print axioms ArkLib.ProximityGap.Round8SeamARecursion.pairSquares_eq_half_subgroup
#print axioms ArkLib.ProximityGap.Round8SeamARecursion.seamA_psum2_spread_eq_subgroup_subsetSum
#print axioms ArkLib.ProximityGap.Round8SeamARecursion.half_is_smooth_subgroup
#print axioms ArkLib.ProximityGap.Round8SeamARecursion.pairSquares_value_sum_eq_zero
#print axioms ArkLib.ProximityGap.Round8SeamARecursion.nonvacuity_zmod5
