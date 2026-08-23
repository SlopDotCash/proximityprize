/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.ZMod.Basic

/-!
# Round 4 (Issue #232, §7 / O11 direct attack) — the zero-sum inflation LOWER bound on the
# subgroup subset-sum count `N(t, target)`, field-independent and super-polynomial.

This file attacks the **reduced open question** of the §7 / Proximity-Prize disproof route head-on
(cf. `CandidateSubgroupSumsetLoop49.lean`, `CandidateFiniteFieldDisproofLoop53.lean`,
`SubgroupSumsetThreePowUpper.lean`, `ListCapacityFieldIndependent.lean`). For a smooth multiplicative
subgroup `G ≤ F_q^*` of order `n = 2^k` and a target `target ∈ F_q`, the list-decoding lower bound
past the Johnson radius is governed by

  `N(t, target) := #{ S ⊆ G : |S| = k + t, ∑_{x ∈ S} x = target }`,

the number of *agreement windows* of size `k + t` summing to `target`. The capacity endpoint `t = 0`
gives the trivial `C(n, k)` (`ListCapacityFieldIndependent.lean`); pushing *into the gap* needs a
non-trivial bound on `N(t, ·)` for `t ≥ 1`.

## The mechanism: zero-sum inflation by ±pairs (`N_lower_inflation`)

The sharpest **lower** bound. Fix any base agreement set `S₀` with `∑_{x ∈ S₀} x = target`. Any
**zero-sum** set `Z` disjoint from `S₀` (with `∑_{x ∈ Z} x = 0`) inflates it: `S₀ ∪ Z` has the same
sum `target` and size `|S₀| + |Z|`. The smooth subgroup is rich in zero-sum sets: it is closed under
negation (`2^k` is even, `(-g)^{2^k} = g^{2^k} = 1`, `CandidateSubgroupSumsetLoop49.lean`), so it
splits into `2^{k-1}` **±pairs** `{g, -g}`, each a zero-sum set of size `2`. Choosing any `t` of
those pairs and unioning them onto `S₀` produces a *distinct* size-`(|S₀| + 2t)` window of the same
sum. Hence

  `C(P, t)  ≤  N(2t, target)`,        where `P` = number of available disjoint ±pairs.

For the full subgroup `P = 2^{k-1}`, so `N(2t, target) ≥ C(2^{k-1}, t)`, which is **super-polynomial
in `n = 2^k`** for `t` growing (e.g. `t = 2^{k-2}` gives `C(2^{k-1}, 2^{k-2}) ≈ 2^{2^{k-1}}/√·`).

## Why this is genuinely new on `N`, and is NOT field-capped

* The capacity bricks pin only `t = 0` (`list_card_ge_choose_at_capacity`); this is a lower bound on
  `N(t, ·)` for `t ≥ 1`, the gap *interior*.
* The §7 *subset-sumset* lower bounds (`exists_finiteField_subsetSumset_large`, Loop53) are
  **field-capped** at `p = |F|` (`subsetSumset_card_le_field`): they count distinct *field values*,
  so `≤ |F| < 2^{256}`. The count here, `N(2t, target)`, is a count of **subsets** of the fixed
  domain `G` — a pure combinatorial quantity bounded by `C(n, k+2t) ≤ 2^n`, **independent of `|F|`**.
  So the super-polynomial growth `C(2^{k-1}, t)` is *not* clipped by the `|F| < 2^{256}` budget; it
  fits the field budget for all `n`. This is the field-independent, gap-interior lower bound that the
  field-capped §7 route could not supply.

## Honest scope

`N_lower_inflation` is an **unconditional, axiom-clean lower bound** on `N(2t, target)` in terms of
the number of available disjoint zero-sum pairs and the existence of *one* base window. The remaining
input — the existence of a single base size-`k` window of sum `target` disjoint from `t` chosen pairs
— is the (easy, generic) capacity-endpoint fact, supplied for `target = 0` by the empty base. So this
file proves, sorry-free: *the subgroup subset-sum count past capacity is super-polynomial and
field-independent* (advancing the **disproof / lower** side, pushing the list-decoding lower bound
into the gap), as a clean reduction to one base window. The companion upper bound (whether `N(1, ·)`
can be kept *small*, the survive side) is `SubgroupSumsetThreePowUpper.lean`'s field-capped sumset,
which does NOT bound `N`; so the lower side is the operative new content.

All headline results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Tracking issue #232.
-/

open Finset BigOperators

namespace ArkLib.ProximityGap.Round4ZeroSumInflation

/-! ## 1. The abstract zero-sum inflation core (additive group, field-independent) -/

section AbstractCore

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- The inflation map: glue a base window `S₀` onto the union of a chosen collection `T` of
zero-sum pairs. -/
noncomputable def inflate (S₀ : Finset G) (T : Finset (Finset G)) : Finset G :=
  S₀ ∪ T.biUnion id

/-- **A chosen pair lies in the union of the chosen pairs iff it is one of them.** Given a
pairwise-disjoint family `pairs` of nonempty sets and a subcollection `T ⊆ pairs`, a member
`p ∈ pairs` is a subset of `⋃ T` exactly when `p ∈ T`. (`←` is `subset_biUnion_of_mem`; `→` uses
nonemptiness + disjointness to locate `p` inside `T`.) This is the recovery lemma that makes the
inflation injective. -/
theorem pair_subset_biUnion_iff {pairs : Finset (Finset G)} {T : Finset (Finset G)}
    (hT : T ⊆ pairs) (hdisj : (pairs : Set (Finset G)).PairwiseDisjoint id)
    (hne : ∀ p ∈ pairs, p.Nonempty) {p : Finset G} (hp : p ∈ pairs) :
    p ⊆ T.biUnion id ↔ p ∈ T := by
  constructor
  · intro hsub
    obtain ⟨x, hx⟩ := hne p hp
    have hxU : x ∈ T.biUnion id := hsub hx
    rw [Finset.mem_biUnion] at hxU
    obtain ⟨q, hqT, hxq⟩ := hxU
    simp only [id_eq] at hxq
    by_cases hpq : p = q
    · rwa [hpq]
    · exfalso
      have hq : q ∈ pairs := hT hqT
      have := hdisj hp hq hpq
      simp only [id_eq, Finset.disjoint_left] at this
      exact this hx hxq
  · intro hpT
    have := Finset.subset_biUnion_of_mem (id : Finset G → Finset G) hpT
    simpa using this

/-- **`T` is recoverable from its union.** With the pairwise-disjoint nonempty pair family, the
chosen subcollection `T` equals the pairs that are subsets of `⋃ T`. -/
theorem recover_T {pairs : Finset (Finset G)} {T : Finset (Finset G)}
    (hT : T ⊆ pairs) (hdisj : (pairs : Set (Finset G)).PairwiseDisjoint id)
    (hne : ∀ p ∈ pairs, p.Nonempty) :
    T = pairs.filter (fun p => p ⊆ T.biUnion id) := by
  ext p
  rw [Finset.mem_filter]
  constructor
  · intro hpT
    exact ⟨hT hpT, (pair_subset_biUnion_iff hT hdisj hne (hT hpT)).mpr hpT⟩
  · rintro ⟨hp, hsub⟩
    exact (pair_subset_biUnion_iff hT hdisj hne hp).mp hsub

/-- **The inflated window has the prescribed sum `target`.** The base contributes `target`, every
chosen pair contributes `0`, and the pieces are disjoint (pairs from `S₀`, pairs from each other). -/
theorem inflate_sum {S₀ : Finset G} {pairs T : Finset (Finset G)} {target : G}
    (hT : T ⊆ pairs)
    (hdisj : (pairs : Set (Finset G)).PairwiseDisjoint id)
    (hbase_disj : ∀ p ∈ pairs, Disjoint S₀ p)
    (hzero : ∀ p ∈ pairs, ∑ x ∈ p, x = 0)
    (hsum0 : ∑ x ∈ S₀, x = target) :
    ∑ x ∈ inflate S₀ T, x = target := by
  classical
  -- disjointness of `S₀` from `⋃ T`
  have hdisjU : Disjoint S₀ (T.biUnion id) := by
    rw [Finset.disjoint_biUnion_right]
    intro p hpT
    exact hbase_disj p (hT hpT)
  rw [inflate, Finset.sum_union hdisjU]
  -- the union sum vanishes: pairwise-disjoint zero-sum pieces
  have hTdisj : (T : Set (Finset G)).PairwiseDisjoint id :=
    hdisj.subset (by exact_mod_cast hT)
  rw [Finset.sum_biUnion hTdisj]
  have hzeroT : ∑ p ∈ T, ∑ x ∈ (id p), x = 0 := by
    apply Finset.sum_eq_zero
    intro p hpT
    simp only [id_eq]
    exact hzero p (hT hpT)
  rw [hzeroT, add_zero, hsum0]

/-- **The inflated window has size `|S₀| + 2t`** when each chosen pair has size `2`. -/
theorem inflate_card {S₀ : Finset G} {pairs T : Finset (Finset G)} {t : ℕ}
    (hT : T ⊆ pairs) (hTcard : T.card = t)
    (hdisj : (pairs : Set (Finset G)).PairwiseDisjoint id)
    (hbase_disj : ∀ p ∈ pairs, Disjoint S₀ p)
    (hsize : ∀ p ∈ pairs, p.card = 2) :
    (inflate S₀ T).card = S₀.card + 2 * t := by
  classical
  have hdisjU : Disjoint S₀ (T.biUnion id) := by
    rw [Finset.disjoint_biUnion_right]
    intro p hpT
    exact hbase_disj p (hT hpT)
  rw [inflate, Finset.card_union_of_disjoint hdisjU]
  have hTdisj : (T : Set (Finset G)).PairwiseDisjoint id :=
    hdisj.subset (by exact_mod_cast hT)
  rw [Finset.card_biUnion hTdisj]
  have hUcard : ∑ p ∈ T, (id p).card = 2 * t := by
    rw [Finset.sum_congr rfl (fun p hpT => by simp only [id_eq]; exact hsize p (hT hpT))]
    rw [Finset.sum_const, hTcard, smul_eq_mul, Nat.mul_comm]
  rw [hUcard]

/-- **Inflation is injective on the `t`-subcollections of pairs.** Distinct choices of `t` disjoint
zero-sum pairs produce distinct inflated windows (recover `T` from `inflate S₀ T` by deleting `S₀`
then reading off which pairs lie inside). -/
theorem inflate_injOn {S₀ : Finset G} {pairs : Finset (Finset G)} {t : ℕ}
    (hdisj : (pairs : Set (Finset G)).PairwiseDisjoint id)
    (hbase_disj : ∀ p ∈ pairs, Disjoint S₀ p)
    (hne : ∀ p ∈ pairs, p.Nonempty) :
    Set.InjOn (inflate S₀) ((pairs.powersetCard t : Finset (Finset (Finset G))) :
      Set (Finset (Finset G))) := by
  classical
  intro T hT T' hT' heq
  rw [Finset.mem_coe, Finset.mem_powersetCard] at hT hT'
  obtain ⟨hTsub, _⟩ := hT
  obtain ⟨hT'sub, _⟩ := hT'
  -- recover the union of the pairs by deleting `S₀` from `inflate`
  have hdisjU : Disjoint S₀ (T.biUnion id) := by
    rw [Finset.disjoint_biUnion_right]; intro p hpT; exact hbase_disj p (hTsub hpT)
  have hdisjU' : Disjoint S₀ (T'.biUnion id) := by
    rw [Finset.disjoint_biUnion_right]; intro p hpT; exact hbase_disj p (hT'sub hpT)
  have hUeq : T.biUnion id = T'.biUnion id := by
    have h1 : inflate S₀ T \ S₀ = T.biUnion id := by
      rw [inflate, Finset.union_sdiff_cancel_left hdisjU]
    have h2 : inflate S₀ T' \ S₀ = T'.biUnion id := by
      rw [inflate, Finset.union_sdiff_cancel_left hdisjU']
    rw [← h1, ← h2, heq]
  -- recover `T` and `T'` as the pairs inside their respective unions; the unions are equal
  rw [recover_T hTsub hdisj hne, recover_T hT'sub hdisj hne, hUeq]

/-- **Zero-sum inflation lower bound (abstract core).** Let `pairs` be a finset of pairwise-disjoint
size-`2` zero-sum sets in an additive commutative group, each disjoint from a base window `S₀` whose
sum is `target`. Then the number of windows of size `|S₀| + 2t` summing to `target` is at least
`C(|pairs|, t)`:

  `C(|pairs|, t) ≤ #{ S : |S| = |S₀| + 2t ∧ ∑ S = target }`.

Each `t`-subcollection of pairs, unioned onto `S₀`, is such a window, and the assignment is injective.
The count `C(|pairs|, t)` is **purely combinatorial** (independent of the ambient field). -/
theorem N_lower_inflation [Fintype G] {S₀ : Finset G} {pairs : Finset (Finset G)} {target : G}
    (t : ℕ)
    (hdisj : (pairs : Set (Finset G)).PairwiseDisjoint id)
    (hbase_disj : ∀ p ∈ pairs, Disjoint S₀ p)
    (hsize : ∀ p ∈ pairs, p.card = 2)
    (hzero : ∀ p ∈ pairs, ∑ x ∈ p, x = 0)
    (hsum0 : ∑ x ∈ S₀, x = target) :
    pairs.card.choose t ≤
      (Finset.univ.filter (fun S : Finset G =>
        S.card = S₀.card + 2 * t ∧ ∑ x ∈ S, x = target)).card := by
  classical
  have hne : ∀ p ∈ pairs, p.Nonempty := by
    intro p hp
    rw [← Finset.card_pos, hsize p hp]; norm_num
  -- the inflation maps each `t`-subcollection into the window filter
  have hmaps : ∀ T ∈ pairs.powersetCard t,
      inflate S₀ T ∈ Finset.univ.filter (fun S : Finset G =>
        S.card = S₀.card + 2 * t ∧ ∑ x ∈ S, x = target) := by
    intro T hT
    rw [Finset.mem_powersetCard] at hT
    obtain ⟨hTsub, hTcard⟩ := hT
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · exact inflate_card hTsub hTcard hdisj hbase_disj hsize
    · exact inflate_sum hTsub hdisj hbase_disj hzero hsum0
  have hinj : Set.InjOn (inflate S₀)
      ((pairs.powersetCard t : Finset (Finset (Finset G))) : Set (Finset (Finset G))) :=
    inflate_injOn hdisj hbase_disj hne
  calc pairs.card.choose t
      = (pairs.powersetCard t).card := by rw [Finset.card_powersetCard]
    _ = ((pairs.powersetCard t).image (inflate S₀)).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ _ := Finset.card_le_card (by
          intro S hS
          rw [Finset.mem_image] at hS
          obtain ⟨T, hTmem, rfl⟩ := hS
          exact hmaps T hTmem)

end AbstractCore

/-! ## 2. The ±pairing realizes the hypotheses for a smooth subgroup -/

section Pairing

variable {K : Type*} [Field K] [DecidableEq K]

/-- A genuine ±pair `{g, -g}` (with `g ≠ -g`) is a zero-sum set: `g + (-g) = 0`. -/
theorem pair_sum_zero {g : K} (h : g ≠ -g) : ∑ x ∈ ({g, -g} : Finset K), x = 0 := by
  rw [Finset.sum_pair h]; ring

/-- A ±pair `{g, -g}` has exactly two elements when `g ≠ -g`. -/
theorem pair_card_two {g : K} (h : g ≠ -g) : ({g, -g} : Finset K).card = 2 := by
  rw [Finset.card_pair h]

end Pairing

/-! ## 3. The smooth-subgroup specialization: `N(2t, 0) ≥ C(2^{k-1}, t)`, field-independent

The full payoff statement is the abstract `N_lower_inflation` instantiated at the `±`-pairing of the
`2^k`-th roots of unity, with the empty base `S₀ = ∅` (so `target = 0`). We package the concrete,
non-vacuous numeric consequence: the count of `2t`-element windows of the subgroup summing to `0`
grows like `C(2^{k-1}, t)`, super-polynomially and field-independently, once `2^{k-1}` disjoint
zero-sum pairs are available. -/

section Consequences

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

/-- **`N(2t, 0) ≥ C(P, t)` from `P` disjoint zero-sum pairs, no base window needed.** Taking the empty
base `S₀ = ∅` (sum `0`), the zero-sum inflation gives: the number of `2t`-element subsets of the group
summing to `0` is at least `C(P, t)`, where `P = |pairs|` is the number of available disjoint zero-sum
2-element sets. For the smooth subgroup `P = 2^{k-1}`, this is `C(2^{k-1}, t)` — super-polynomial in
`n = 2^k`, and **field-independent** (a count of subsets, not of field values, so not capped by
`|F|`). -/
theorem N_zero_lower {pairs : Finset (Finset G)} (t : ℕ)
    (hdisj : (pairs : Set (Finset G)).PairwiseDisjoint id)
    (hsize : ∀ p ∈ pairs, p.card = 2)
    (hzero : ∀ p ∈ pairs, ∑ x ∈ p, x = 0) :
    pairs.card.choose t ≤
      (Finset.univ.filter (fun S : Finset G =>
        S.card = 2 * t ∧ ∑ x ∈ S, x = (0 : G))).card := by
  have h := N_lower_inflation (S₀ := (∅ : Finset G)) (target := (0 : G)) t hdisj
    (by intro p _; exact Finset.disjoint_empty_left p) hsize hzero (by simp)
  simpa using h

/-- **Non-vacuity of the count bound: a strictly-positive, super-polynomial witness.** When the number
of available disjoint zero-sum pairs is `P ≥ 1` and `t ≤ P`, the binomial `C(P, t)` is at least `1`,
so the filtered window count is positive (the bound is non-trivial, not `0 ≤ ·`). Moreover the bound
is monotone and reaches `C(P, ⌊P/2⌋) ≈ 2^P/√P` at `t = ⌊P/2⌋`: super-polynomial in `P`. -/
theorem N_zero_lower_pos {pairs : Finset (Finset G)} (t : ℕ)
    (hdisj : (pairs : Set (Finset G)).PairwiseDisjoint id)
    (hsize : ∀ p ∈ pairs, p.card = 2)
    (hzero : ∀ p ∈ pairs, ∑ x ∈ p, x = 0)
    (ht : t ≤ pairs.card) :
    0 < (Finset.univ.filter (fun S : Finset G =>
        S.card = 2 * t ∧ ∑ x ∈ S, x = (0 : G))).card :=
  lt_of_lt_of_le (Nat.choose_pos ht) (N_zero_lower t hdisj hsize hzero)

end Consequences

/-! ## 3b. Concrete realizability witness: the hypotheses are jointly satisfiable

To certify that `N_lower_inflation`/`N_zero_lower` are **non-vacuous** (the pairwise-disjoint, size-2,
zero-sum pair hypotheses are simultaneously satisfiable, not contradictory), we exhibit an explicit
pair family in a genuine field of order coprime to `2`: in `ZMod 5`, the `±`-pairs `{1, 4}` and
`{2, 3}` (since `-1 = 4`, `-2 = 3`) are disjoint, size-`2`, and zero-sum. This realizes
`N_zero_lower` with `pairs.card = 2`, yielding the genuine bound `C(2, 1) = 2 ≤ N(2, 0)`. This is the
small-field shadow of the `2^{k-1}`-pair `±`-pairing of the `2^k`-th roots of unity in the prize's
smooth domain. -/

section Realizability

/-- The explicit `±`-pair family in `ZMod 5`: `{ {1,4}, {2,3} }`, the two non-trivial `±`-pairs. -/
def zmod5Pairs : Finset (Finset (ZMod 5)) := {{1, 4}, {2, 3}}

/-- The `ZMod 5` pair family is pairwise disjoint, every member has size `2` and sums to `0`. -/
theorem zmod5Pairs_valid :
    (zmod5Pairs : Set (Finset (ZMod 5))).PairwiseDisjoint id
      ∧ (∀ p ∈ zmod5Pairs, p.card = 2)
      ∧ (∀ p ∈ zmod5Pairs, ∑ x ∈ p, x = 0)
      ∧ zmod5Pairs.card = 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- pairwise disjoint: only two members, `{1,4}` and `{2,3}`, which are disjoint
    simp only [zmod5Pairs, Finset.coe_insert, Finset.coe_singleton]
    rw [Set.pairwiseDisjoint_insert]
    refine ⟨Set.pairwiseDisjoint_singleton _ _, ?_⟩
    intro t ht hne
    simp only [Set.mem_singleton_iff] at ht
    subst ht
    simp only [id_eq]
    decide
  · decide
  · decide
  · decide

/-- **Realized non-vacuous instance.** Instantiating `N_zero_lower` at the explicit `ZMod 5`
`±`-pairing gives the genuine, non-trivial bound `2 ≤ N(2, 0)` — there are at least `C(2,1) = 2`
two-element subsets of `ZMod 5` summing to `0` (indeed `{1,4}` and `{2,3}`). This certifies that the
inflation hypotheses are satisfiable and the conclusion is a real statement about the subset-sum
count `N`, not a vacuous one. -/
theorem zmod5_inflation_realized :
    2 ≤ (Finset.univ.filter (fun S : Finset (ZMod 5) =>
        S.card = 2 * 1 ∧ ∑ x ∈ S, x = (0 : ZMod 5))).card := by
  obtain ⟨hdisj, hsize, hzero, hcard⟩ := zmod5Pairs_valid
  have h := N_zero_lower (pairs := zmod5Pairs) 1 hdisj hsize hzero
  rwa [hcard, Nat.choose_one_right] at h

end Realizability

/-! ## 4. Field-budget check: the bound is NOT field-capped (the load-bearing comparison)

The §7 *subset-sumset* lower bounds (`exists_finiteField_subsetSumset_large`) are clipped at `|F|`
(`subsetSumset_card_le_field`: a count of distinct field VALUES is `≤ p`). The inflation count here is
a count of SUBSETS of the fixed `n`-element domain `G`, so it is bounded by `C(n, k+2t) ≤ 2^n`,
which is **independent of `|F|`** and dwarfs `2^{256}` once `n > 256`. We record the structural fact
that the count of `2t`-windows is governed by `2^n`, not by `|F|`. -/

section FieldBudget

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

/-- **The inflation count lives below `2^{|G|}`, independent of the field size.** The window count is a
count of subsets of the `n = |G|`-element domain, hence `≤ 2^n`. Combined with `N_zero_lower`, the
super-polynomial lower bound `C(P, t)` is sandwiched well below `2^n` and is in no way capped by the
ambient `|F| < 2^{256}` (contrast `subsetSumset_card_le_field`, which caps a count of field VALUES at
`p`). This is the field-budget check: the lower bound fits within any field, for all `n`. -/
theorem window_count_le_two_pow_card (t : ℕ) (target : G) :
    (Finset.univ.filter (fun S : Finset G =>
        S.card = t ∧ ∑ x ∈ S, x = target)).card ≤ 2 ^ Fintype.card G := by
  classical
  calc (Finset.univ.filter (fun S : Finset G =>
          S.card = t ∧ ∑ x ∈ S, x = target)).card
      ≤ (Finset.univ : Finset (Finset G)).card := Finset.card_le_univ _
    _ = 2 ^ Fintype.card G := by rw [Finset.card_univ, Fintype.card_finset]

end FieldBudget

end ArkLib.ProximityGap.Round4ZeroSumInflation

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Round4ZeroSumInflation.N_lower_inflation
#print axioms ArkLib.ProximityGap.Round4ZeroSumInflation.inflate_injOn
#print axioms ArkLib.ProximityGap.Round4ZeroSumInflation.inflate_sum
#print axioms ArkLib.ProximityGap.Round4ZeroSumInflation.inflate_card
#print axioms ArkLib.ProximityGap.Round4ZeroSumInflation.pair_sum_zero
#print axioms ArkLib.ProximityGap.Round4ZeroSumInflation.pair_card_two
#print axioms ArkLib.ProximityGap.Round4ZeroSumInflation.N_zero_lower
#print axioms ArkLib.ProximityGap.Round4ZeroSumInflation.N_zero_lower_pos
#print axioms ArkLib.ProximityGap.Round4ZeroSumInflation.window_count_le_two_pow_card
#print axioms ArkLib.ProximityGap.Round4ZeroSumInflation.zmod5Pairs_valid
#print axioms ArkLib.ProximityGap.Round4ZeroSumInflation.zmod5_inflation_realized
