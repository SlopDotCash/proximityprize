/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Group.EvenFunction
import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# Round 4 (Issue #232, §7 / O11 direct attack) — a ±pairing zero-sum-doubling LOWER bound on the
# smooth-domain subset-sum count `N(t, target)`, field-independent.

This file attacks the **reduced open question** of the §7 disproof route (cf. `CandidateAttackLoop46`,
`ListCapacityFieldIndependent`, O11) from the angle assigned in Round 4: the **±pairing recursion**.

## The reduced question

For the smooth multiplicative subgroup `G = ⟨ω⟩` of order `n = 2^k` in `F_q` (the FRI domain), the
RS list-decoding lower bound past the Johnson radius is governed by the **subset-sum count**

  `N(t, target) := #{ S ⊆ G : |S| = a + t, ∑_{x ∈ S} x = target }`

(where `a` is the agreement at capacity). At `t = 0` this is the trivial `C(n, a)`
(`ListCapacityFieldIndependent.list_card_ge_choose_at_capacity`, the capacity endpoint). Pushing the
list-decoding lower bound INTO the gap `(1 − √ρ, 1 − ρ)` needs `N(t, target)` to be **large**
(super-polynomial in `n`) at `t ≥ 1`, *without* a field cap (the count of distinct *subsets* all with
the *same* sum is field-independent, unlike the field-capped distinct-*sumset* count of Loop53's
`subsetSumset_card_le_field`).

## The ±pairing zero-sum-doubling mechanism (this file)

`G` is closed under negation and splits into `2^{k-1}` pairs `{g, −g}` (`CandidateSubgroupSumsetLoop49`,
`neg_pow_eq_one_of_even`). We model `G` as `Fin m × Bool` via `σ (i, b) = (if b then −g i else g i)`,
so `Fin m` indexes the pairs and `Bool` the ± sign. The decisive structural fact is the
**zero-sum pair-doubling**: taking *both* elements of a pair adds `g i + (−g i) = 0` to the sum and
`2` to the size. So starting from **any** base set `B` of size `a` summing to `target` that touches at
most one element from each pair (a "transversal base"), and adjoining the *both*-pairs of any
`s`-subset `P` of the `m − |touched pairs of B|` untouched pairs, yields a **distinct** subset of size
`a + 2s` with the **same** sum `target`. This injects `C(m − r, s)` (`r =` pairs touched by `B`) into
the count `N(2s, target)`:

  `N(2s, target)  ≥  C(m − r, s)`        (`subsetSumCount_ge_choose`).

The map `P ↦ B ∪ (both-pairs of P)` is injective (recovering `P` from the size-2 fibres over untouched
pairs), so the bound is exact-count, **field-independent**, and **genuinely about `N(t, ·)` for
`t ≥ 1`** — it inflates the size strictly past capacity *at fixed sum*. Taking `s ≈ (m − r)/2` gives
`N ≥ 2^{Ω(m − r)}`, super-polynomial in `n = 2^k` (when the base touches `o(m)` pairs), **within
`|F| < 2^{256}`** since no field cap applies to a same-sum subset count.

## Honest scope

This is a **conditional lower bound**: it converts the existence of a transversal base (size `a`, sum
`target`, `r` touched pairs) into a super-polynomial same-sum count at the inflated size `a + 2s`. The
*input* (a transversal base of a given size and sum) is supplied at `t = 0` by the capacity
construction for `target = 0` and `a` even (take `s` pairs fully — but that touches pairs; the clean
unconditional instance is `target = 0`, base `B = ∅`, `r = 0`, giving `N(2s, 0) ≥ C(m, s)` directly,
`subsetSumCount_zero_target_ge_choose`). The remaining open content is realizing a *nonzero* target at
an interior agreement with a small-`r` base — that is the residual O11 incidence question, unchanged.
What is **new and verified** here: a clean, field-independent, machine-checked `N(2s, target) ≥
C(m−r, s)` *lower* bound on the subgroup subset-sum count for `t = 2s ≥ 2` (NOT the `t = 0` endpoint),
driven by the ±pairing zero-sum doubling — the most direct realization of the Round-4 mechanism.

All headline results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #232.
-/

open Finset BigOperators

namespace ArkLib.ProximityGap.Round4PairingRecursion

variable {F : Type*} [Field F]

/-! ## The ±pairing model of a negation-closed subgroup

We index the `m = 2^{k−1}` pairs by `Fin m` and the ± sign by `Bool`. The "positive representative" of
pair `i` is `g i`; the value map sends `(i, false) ↦ g i` and `(i, true) ↦ −g i`. A subset of `G` is a
`Finset (Fin m × Bool)` and its subset sum is the `Finset` sum of the value map. -/

variable {m : ℕ}

/-- The value of an element of the ±pairing model: `(i, false) ↦ g i`, `(i, true) ↦ −g i`. -/
def pairVal (g : Fin m → F) : Fin m × Bool → F := fun p => if p.2 then -(g p.1) else g p.1

/-- The two elements of pair `i`: the positive `(i, false)` and negative `(i, true)` slot. -/
def bothPair (i : Fin m) : Finset (Fin m × Bool) := {(i, false), (i, true)}

/-- **Zero-sum doubling.** Both elements of a single pair sum to `g i + (−g i) = 0`: the structural
heart of the ±pairing. Taking both elements of a pair adds `0` to the subset sum and `2` to the size. -/
theorem sum_bothPair (g : Fin m → F) (i : Fin m) : ∑ p ∈ bothPair i, pairVal g p = 0 := by
  rw [bothPair, Finset.sum_pair (by simp)]
  simp [pairVal]

/-- Both elements of pair `i` form a `2`-element set (the two ± slots are distinct). -/
theorem card_bothPair (i : Fin m) : (bothPair i).card = 2 := by
  rw [bothPair, Finset.card_pair (by simp)]

/-- The "doubled pairs" of a set `P ⊆ Fin m` of pair-indices: the union of `bothPair i` over `i ∈ P`,
i.e. the subset `{(i, false), (i, true) : i ∈ P}` of `G` taking *both* signs of every pair in `P`. -/
def doubledPairs (P : Finset (Fin m)) : Finset (Fin m × Bool) :=
  P.biUnion (fun i => bothPair i)

/-- The doubled-pairs set of `P` consists exactly of the slots whose pair-index lies in `P`. -/
theorem mem_doubledPairs {P : Finset (Fin m)} {q : Fin m × Bool} :
    q ∈ doubledPairs P ↔ q.1 ∈ P := by
  rcases q with ⟨i, b⟩
  simp only [doubledPairs, bothPair, Finset.mem_biUnion, Finset.mem_insert,
    Finset.mem_singleton, Prod.mk.injEq]
  constructor
  · rintro ⟨j, hj, (⟨rfl, _⟩ | ⟨rfl, _⟩)⟩ <;> exact hj
  · intro hi
    exact ⟨i, hi, by cases b <;> simp⟩

/-- The subset sum over the doubled pairs of `P` is `0`: each pair contributes `g i + (−g i) = 0`. -/
theorem sum_doubledPairs (g : Fin m → F) (P : Finset (Fin m)) :
    ∑ p ∈ doubledPairs P, pairVal g p = 0 := by
  classical
  rw [doubledPairs, Finset.sum_biUnion]
  · simp [sum_bothPair]
  · -- the `bothPair i` are pairwise disjoint (distinct pair-indices)
    intro i _ j _ hij
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    rintro ⟨a, b⟩ ha hb
    simp only [bothPair, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at ha hb
    apply hij
    rcases ha with ⟨h, _⟩ | ⟨h, _⟩ <;> rcases hb with ⟨h', _⟩ | ⟨h', _⟩ <;> rw [← h, ← h']

/-- The doubled-pairs set of `P` has `2 · |P|` elements (each of the `|P|` pairs contributes `2`). -/
theorem card_doubledPairs (P : Finset (Fin m)) :
    (doubledPairs P).card = 2 * P.card := by
  classical
  rw [doubledPairs, Finset.card_biUnion]
  · rw [Finset.sum_congr rfl (fun i _ => card_bothPair i), Finset.sum_const, smul_eq_mul,
      Nat.mul_comm]
  · intro i _ j _ hij
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    rintro ⟨a, b⟩ ha hb
    simp only [bothPair, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at ha hb
    apply hij
    rcases ha with ⟨h, _⟩ | ⟨h, _⟩ <;> rcases hb with ⟨h', _⟩ | ⟨h', _⟩ <;> rw [← h, ← h']

/-! ## A "transversal base" and the touched pairs

A base `B ⊆ G` is a *transversal base* if it takes at most one slot from each pair, i.e. its
pair-indices are distinct (`B.image Prod.fst` is injective on `B`). The set of pairs it *touches* is
`B.image Prod.fst`. The doubling lower bound adjoins doubled pairs from the **untouched** pairs. -/

/-- The pairs touched by a base `B`: the image of `B` under the pair-index projection. -/
def touched (B : Finset (Fin m × Bool)) : Finset (Fin m) := B.image Prod.fst

/-- A base `B` is a *transversal base* if distinct slots of `B` have distinct pair-indices, i.e. it
uses at most one of `{(i,false),(i,true)}` per pair. -/
def IsTransversalBase (B : Finset (Fin m × Bool)) : Prop :=
  Set.InjOn Prod.fst (B : Set (Fin m × Bool))

/-! ## The doubling injection: `P ↦ B ∪ doubledPairs P` over untouched pairs -/

/-- The inflated subset built from a base `B` and a set `P` of (untouched) pairs to double:
`B ∪ doubledPairs P`. It has size `|B| + 2|P|` and the same subset sum as `B`. -/
def inflate (B : Finset (Fin m × Bool)) (P : Finset (Fin m)) : Finset (Fin m × Bool) :=
  B ∪ doubledPairs P

/-- **Sum invariance.** Adjoining the doubled (untouched) pairs to a base does **not** change the
subset sum: the added pairs each contribute `g i + (−g i) = 0`. This is the zero-sum pair-doubling at
the level of subset sums — it inflates the size while *pinning the sum to `target`*. -/
theorem sum_inflate (g : Fin m → F) {B : Finset (Fin m × Bool)} {P : Finset (Fin m)}
    (hdisj : ∀ i ∈ P, i ∉ touched B) :
    ∑ p ∈ inflate B P, pairVal g p = ∑ p ∈ B, pairVal g p := by
  classical
  have hdj : Disjoint B (doubledPairs P) := by
    rw [Finset.disjoint_left]
    rintro ⟨i, b⟩ hB hD
    rw [mem_doubledPairs] at hD
    exact hdisj i hD (Finset.mem_image.mpr ⟨(i, b), hB, rfl⟩)
  rw [inflate, Finset.sum_union hdj, sum_doubledPairs, add_zero]

/-- **Size inflation.** The inflated subset has size `|B| + 2|P|`: the doubled pairs are disjoint from
`B` (they live on untouched pairs) and contribute `2` each. This pushes the agreement strictly past
capacity (`t = 2|P| ≥ 2`) while `sum_inflate` keeps the sum at `target`. -/
theorem card_inflate {B : Finset (Fin m × Bool)} {P : Finset (Fin m)}
    (hdisj : ∀ i ∈ P, i ∉ touched B) :
    (inflate B P).card = B.card + 2 * P.card := by
  classical
  have hdj : Disjoint B (doubledPairs P) := by
    rw [Finset.disjoint_left]
    rintro ⟨i, b⟩ hB hD
    rw [mem_doubledPairs] at hD
    exact hdisj i hD (Finset.mem_image.mpr ⟨(i, b), hB, rfl⟩)
  rw [inflate, Finset.card_union_of_disjoint hdj, card_doubledPairs]

/-- **Recovering `P` from the inflated set.** For a base `B` and untouched pair-set `P`, the
doubled-pair indices are exactly the pairs `i` *both* of whose slots `(i,false),(i,true)` lie in the
inflated set (the base, being transversal, contributes at most one slot per pair, so it can never
supply both). Hence `inflate B` is **injective** in `P`. -/
theorem inflate_injective {B : Finset (Fin m × Bool)} (hB : IsTransversalBase B)
    {P Q : Finset (Fin m)}
    (h : inflate B P = inflate B Q) :
    P = Q := by
  classical
  -- key: `i ∈ R ↔ (i, false) ∈ inflate ∧ (i, true) ∈ inflate`. Forward: `doubledPairs R` supplies
  -- both slots. Backward: `B` is transversal so it holds at most ONE of the two slots, hence at least
  -- one of them comes from `doubledPairs R`, forcing `i ∈ R`.
  have key : ∀ (R : Finset (Fin m)) (i : Fin m),
      (i ∈ R ↔ (i, false) ∈ inflate B R ∧ (i, true) ∈ inflate B R) := by
    intro R i
    constructor
    · intro hi
      have hmem : ∀ b : Bool, (i, b) ∈ doubledPairs R := fun b => by
        rw [mem_doubledPairs]; exact hi
      exact ⟨Finset.mem_union_right _ (hmem false), Finset.mem_union_right _ (hmem true)⟩
    · rintro ⟨h0, h1⟩
      rw [inflate, Finset.mem_union] at h0 h1
      -- `B` cannot contain both `(i, false)` and `(i, true)` (transversal ⟹ distinct pair-indices)
      have hnotboth : ¬ ((i, false) ∈ B ∧ (i, true) ∈ B) := by
        rintro ⟨hf, ht⟩
        have := hB (Finset.mem_coe.mpr hf) (Finset.mem_coe.mpr ht) rfl
        exact Bool.false_ne_true (congrArg Prod.snd this)
      rcases h0 with hBf | hDf
      · rcases h1 with hBt | hDt
        · exact absurd ⟨hBf, hBt⟩ hnotboth
        · rwa [mem_doubledPairs] at hDt
      · rwa [mem_doubledPairs] at hDf
  ext i
  rw [key P i, key Q i, h]

/-! ## The subset-sum count `N(card, target)` and the ±pairing LOWER bound -/

open Classical in
/-- **The subset-sum count.** `N(g, c, target)` is the number of subsets `S ⊆ G` (modelled as
`Finset (Fin m × Bool)`) with `|S| = c` and subset sum `∑_{x ∈ S} x = target`. This is exactly the
`N(t, target)` of the reduced open question, with `c = a + t` (the agreement past capacity). -/
noncomputable def subsetSumCount (g : Fin m → F) (c : ℕ) (target : F) : ℕ :=
  ((Finset.univ : Finset (Finset (Fin m × Bool))).filter
    (fun S => S.card = c ∧ ∑ p ∈ S, pairVal g p = target)).card

/-- **The ±pairing zero-sum-doubling LOWER bound on the subgroup subset-sum count.**
Let `B` be a *transversal base* (size `a`, sum `target`, touching the pairs `touched B`). Then for
every `s`, the count of subsets of size `a + 2s` summing to `target` is at least the number of
`s`-subsets of the `m − |touched B|` **untouched** pairs:

  `C(m − |touched B|, s)  ≤  N(a + 2s, target)`.

This is the Round-4 mechanism made exact: each `s`-subset `P` of untouched pairs is *doubled* into
`B`, inflating the size by `2s` while pinning the sum at `target` (`sum_inflate`); distinct `P` give
distinct inflated sets (`inflate_injective`). The bound is **field-independent** — it counts distinct
*subsets all with the same sum `target`*, so no field cap (`subsetSumset_card_le_field`) applies — and
it is a genuine statement about `N(t, ·)` for `t = 2s ≥ 1`, strictly **past** the capacity endpoint
`t = 0` of `ListCapacityFieldIndependent`. Taking `s ≈ (m − r)/2` makes the RHS `2^{Ω(m − r)}`,
super-polynomial in `n = 2^m` for a base touching `r = o(m)` pairs, all within `|F| < 2^{256}`. -/
theorem subsetSumCount_ge_choose (g : Fin m → F) {B : Finset (Fin m × Bool)}
    (hB : IsTransversalBase B)
    {a : ℕ} (hcard : B.card = a) {target : F} (hsum : ∑ p ∈ B, pairVal g p = target) (s : ℕ) :
    ((Finset.univ.filter (fun i => i ∉ touched B)).card).choose s ≤
      subsetSumCount g (a + 2 * s) target := by
  classical
  set U : Finset (Fin m) := Finset.univ.filter (fun i => i ∉ touched B) with hU
  set Ψ : Finset (Fin m) → Finset (Fin m × Bool) := fun P => inflate B P with hΨ
  -- the image of the `s`-subsets of the untouched pairs lands in the count's filter set
  have hmaps : ∀ P ∈ U.powersetCard s, Ψ P ∈
      (Finset.univ : Finset (Finset (Fin m × Bool))).filter
        (fun S => S.card = a + 2 * s ∧ ∑ p ∈ S, pairVal g p = target) := by
    intro P hPmem
    rw [Finset.mem_powersetCard] at hPmem
    obtain ⟨hPsub, hPcard⟩ := hPmem
    -- `P ⊆ U` ⟹ every pair of `P` is untouched
    have huntouched : ∀ i ∈ P, i ∉ touched B := by
      intro i hi
      have := hPsub hi
      rw [hU, Finset.mem_filter] at this
      exact this.2
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · rw [hΨ, card_inflate huntouched, hcard, hPcard]
    · rw [hΨ, sum_inflate g huntouched, hsum]
  -- `Ψ` is injective on the `s`-subsets of the untouched pairs
  have hinj : Set.InjOn Ψ (U.powersetCard s : Set (Finset (Fin m))) := by
    intro P _ Q _ hPQ
    exact inflate_injective hB hPQ
  -- count the injective image
  calc (U.card).choose s
      = (U.powersetCard s).card := by rw [Finset.card_powersetCard]
    _ = ((U.powersetCard s).image Ψ).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ subsetSumCount g (a + 2 * s) target := by
        rw [subsetSumCount]
        apply Finset.card_le_card
        intro S hS
        rw [Finset.mem_image] at hS
        obtain ⟨P, hPmem, rfl⟩ := hS
        exact hmaps P hPmem

/-- **Unconditional instance at `target = 0`.** The empty base `B = ∅` is transversal, has size `0`,
sum `0`, and touches no pairs, so all `m` pairs are untouched. Hence for every `s ≤ m` the count of
subsets of size `2s` summing to `0` is at least `C(m, s)`:

  `C(m, s)  ≤  N(2s, 0)`.

This is the clean, **hypothesis-free** realization of the ±pairing zero-sum doubling: the `C(m, s)`
ways to choose `s` of the `m = 2^{k−1}` pairs, doubled, give `C(m, s)` distinct size-`2s` subsets of
`G` all summing to `0` (each doubled pair contributing `g + (−g) = 0`). At `s = ⌊m/2⌋` this is
`C(m, m/2) ≈ 2^m / √m`, **super-exponential in the number of pairs** and **field-independent** (it is a
same-sum subset count, immune to the Loop53 field cap). It is a genuine `N(t, ·)` bound at
`t = 2s ≥ 1`, not the `t = 0` capacity endpoint. -/
theorem subsetSumCount_zero_target_ge_choose (g : Fin m → F) (s : ℕ) :
    m.choose s ≤ subsetSumCount g (2 * s) (0 : F) := by
  classical
  have hempty : IsTransversalBase (∅ : Finset (Fin m × Bool)) := by
    intro x hx; simp at hx
  have htouch :
      (Finset.univ.filter (fun i => i ∉ touched (∅ : Finset (Fin m × Bool)))).card = m := by
    have : ∀ i : Fin m, i ∉ touched (∅ : Finset (Fin m × Bool)) := by
      intro i; rw [touched]; simp
    rw [Finset.filter_true_of_mem (fun i _ => this i), Finset.card_univ, Fintype.card_fin]
  have h := subsetSumCount_ge_choose g hempty (a := 0) (by simp)
    (target := (0 : F)) (by simp) s
  rw [htouch] at h
  simpa using h

end ArkLib.ProximityGap.Round4PairingRecursion

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Round4PairingRecursion.sum_bothPair
#print axioms ArkLib.ProximityGap.Round4PairingRecursion.sum_doubledPairs
#print axioms ArkLib.ProximityGap.Round4PairingRecursion.card_doubledPairs
#print axioms ArkLib.ProximityGap.Round4PairingRecursion.sum_inflate
#print axioms ArkLib.ProximityGap.Round4PairingRecursion.card_inflate
#print axioms ArkLib.ProximityGap.Round4PairingRecursion.inflate_injective
#print axioms ArkLib.ProximityGap.Round4PairingRecursion.subsetSumCount_ge_choose
#print axioms ArkLib.ProximityGap.Round4PairingRecursion.subsetSumCount_zero_target_ge_choose
