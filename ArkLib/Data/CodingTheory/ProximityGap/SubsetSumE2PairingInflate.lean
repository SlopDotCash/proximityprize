/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubsetSumPairingInflate
import ArkLib.Data.CodingTheory.ProximityGap.ListInteriorT2TwoSymmetric
import Mathlib.Data.Finset.Powerset

/-!
# Round 6 (Issue #232, ABF26) — an explicit `t = 2` LOWER bound via ±pairing zero-sum doubling
# that fixes **BOTH** `e_1` and `e_2`, reducing the joint two-symmetric count to a subset-sum count
# on the pair-squares.

Rounds 1–5 reduced the open core of the §7 list-decoding disproof route to a **field-independent
super-polynomial lower bound** on the count of `(k+t)`-subsets of the smooth negation-closed subgroup
`G` with the top `t` elementary symmetric functions `e_1, …, e_t` *jointly* prescribed. Round 4's
`SubsetSumPairingInflate.lean` realized this for `t = 1` (`subsetSumCount_ge_choose`): adjoining a
doubled pair `{g, −g}` adds `0` to `e_1`, so the `e_1`-fiber inflates by `C(m, s)` at the cost of
`+2s` to the size. Round 5's `ListInteriorT2TwoSymmetric.lean` pinned the **exact** `t = 2` joint
condition (`degDrop_t2_iff_two_symmetric`): both top coefficients of `p_S` vanish iff
`e_1(D_S) = c_1 ∧ e_2(D_S) = c_2`.

This round supplies the **first genuine `t = 2` LOWER bound** — a construction of a super-polynomial
family of `(k+2)`-subsets (more generally `(a+2s)`-subsets) with **both** `e_1` and `e_2` prescribed.

## The valuation-weighted symmetric functions (robust index-model bookkeeping)

We work in the Round-4 ±pairing model: a subset of `G` is a `Finset (Fin m × Bool)` (`Fin m` indexes
the `2^{k−1}` pairs, `Bool` the ± sign), valued by `pairVal g (i, b) = if b then −g i else g i`. The
elementary symmetric functions are taken **over the index set** (so multiplicity is honest even when
`g i = 0` or `g` is non-injective):

* `esymm1 v S = ∑_{p∈S} v p`,   `esymm2 v S = ∑_{T⊆S, |T|=2} ∏_{p∈T} v p`.

These match Round 5's `degDrop_t2_iff_two_symmetric` conventions exactly (the `e_1`, `e_2` of the root
multiset).

## The key structural identity (the heart of this file)

* `esymm2_insert` — `e_2(insert p S) = e_2 S + v p · e_1 S` (the Pascal recursion for `e_2`).
* `esymm1_inflate` / `esymm2_inflate` — **the decisive fact**: adjoining the doubled (untouched) pairs
  `doubledPairs P` to a base `B` keeps `e_1` **exactly fixed** (`= e_1 B`) and shifts `e_2` by exactly
  `−∑_{i∈P} g_i²` (the cross terms between the zero-sum pairs and `B`, and between distinct pairs, all
  cancel because each pair sums to `0`):

    `e_1(inflate B P) = e_1 B`,    `e_2(inflate B P) = e_2 B − ∑_{i∈P} g_i²`.

## The headline (`twoSymmetric_count_ge_squareSubsetSum`)

Both `e_1` and `e_2` of `inflate B P` are therefore **constant in `P`** along any family of pair-sets
`P` with the *same square-sum* `∑_{i∈P} g_i² = sq`. So the joint two-symmetric fiber at the inflated
size `a + 2s` contains the injective image of

  `{ P ⊆ untouched pairs : |P| = s, ∑_{i∈P} g_i² = sq }`,

giving the **lower bound**

  `#{ S : |S| = a+2s, e_1(S) = e_1 B, e_2(S) = e_2 B − sq }  ≥  #{ P : |P| = s, ∑_{i∈P} g_i² = sq }`.

This is the precise `t = 2` analogue of Round 4's `subsetSumCount_ge_choose`: the joint
`(e_1, e_2)`-count is bounded below by a **subset-sum count on the pair-squares `{g_i²}`** — itself a
`t = 1`-shaped subset-sum count, *one level down*.

## Honest scope (what this is and is NOT)

* It is the **first machine-checked reduction** of the `t = 2` joint two-symmetric LOWER bound to a
  concrete combinatorial count, the pair-square subset-sum count. The cancellation of all cross terms
  (`esymm2_inflate`) is the genuinely new structural content over Round 4 (which only needed `e_1`).
* The bound is **field-independent** in the count (it counts distinct subsets all with the *same*
  `(e_1, e_2)`), exactly the field-independence the prize-disproof side needs.
* **The honest caveat the brief anticipated (this is a REDUCTION, not a closure).** The pair-square
  subset-sum count `#{P : |P|=s, ∑_{i∈P} g_i² = sq}` is *itself* a subset-sum count, now on the
  squared ground set `{g_i²}`. Whether *it* is super-polynomial — for `sq = 0` or any `sq` — is the
  **same open subset-sum worst-case-spread question one level down**. So this round does NOT by itself
  produce a super-polynomial joint `(e_1, e_2)` family: it **reduces** the `t = 2` joint two-symmetric
  count to the `t = 1`-shaped square-subset-sum count, exactly as the brief predicted ("it may reduce
  to the same open question one level down"). The genuine *advance* is the verified cross-term-cancel
  identity `esymm2_inflate` and the resulting exact reduction; the residual is honestly the open
  square-subset-sum spread.

All headline results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Tracking issue #232.
-/

open Finset BigOperators

namespace ArkLib.CodingTheory.Round6T2Explicit

open ArkLib.ProximityGap.Round4PairingRecursion

variable {ι : Type*} [DecidableEq ι]
variable {F : Type*} [Field F]

/-! ## Valuation-weighted order-1 and order-2 elementary symmetric functions on the index set. -/

/-- The order-1 elementary symmetric function of `S` weighted by a valuation `v`:
`e_1(S) = ∑_{p∈S} v p`. -/
def esymm1 (v : ι → F) (S : Finset ι) : F := ∑ p ∈ S, v p

/-- The order-2 elementary symmetric function of `S` weighted by a valuation `v`:
`e_2(S) = ∑_{T⊆S, |T|=2} ∏_{p∈T} v p`, the sum over unordered index-pairs. -/
def esymm2 (v : ι → F) (S : Finset ι) : F := ∑ T ∈ S.powersetCard 2, ∏ p ∈ T, v p

@[simp] theorem esymm1_empty (v : ι → F) : esymm1 v (∅ : Finset ι) = 0 := by simp [esymm1]

@[simp] theorem esymm2_empty (v : ι → F) : esymm2 v (∅ : Finset ι) = 0 := by
  rw [esymm2, Finset.powersetCard_eq_empty.mpr (by simp)]
  simp

/-- **`e_1` under a single insertion**: `e_1(insert p S) = v p + e_1 S` for `p ∉ S`. -/
theorem esymm1_insert (v : ι → F) {p : ι} {S : Finset ι} (hp : p ∉ S) :
    esymm1 v (insert p S) = v p + esymm1 v S := by
  simp only [esymm1, Finset.sum_insert hp]

/-- **`e_2` under a single insertion (the Pascal recursion)**: `e_2(insert p S) = e_2 S + v p · e_1 S`
for `p ∉ S`. The order-2 symmetric function of `insert p S` splits into the `2`-subsets *avoiding* `p`
(`= e_2 S`) and those *containing* `p` (each `{p, q}` with `q ∈ S`, contributing `v p · v q`, summing
to `v p · e_1 S`). -/
theorem esymm2_insert (v : ι → F) {p : ι} {S : Finset ι} (hp : p ∉ S) :
    esymm2 v (insert p S) = esymm2 v S + v p * esymm1 v S := by
  classical
  unfold esymm2 esymm1
  rw [show (2 : ℕ) = 1 + 1 from rfl, Finset.powersetCard_succ_insert hp]
  have hdisj : Disjoint (S.powersetCard (1 + 1))
      ((S.powersetCard 1).image (insert p)) := by
    rw [Finset.disjoint_left]
    intro T hT hTimg
    rw [Finset.mem_powersetCard] at hT
    rw [Finset.mem_image] at hTimg
    obtain ⟨U, _, rfl⟩ := hTimg
    exact hp (hT.1 (Finset.mem_insert_self p U))
  rw [Finset.sum_union hdisj]
  congr 1
  -- the `p`-containing part: `∑_{U ∈ powersetCard 1 S} ∏ (insert p U) = ∑_{q∈S} v p · v q`
  have hinj : Set.InjOn (insert p) (S.powersetCard 1 : Set (Finset ι)) := by
    intro U hU V hV h
    rw [Finset.mem_coe, Finset.mem_powersetCard] at hU hV
    have hpU : p ∉ U := fun hc => hp (hU.1 hc)
    have hpV : p ∉ V := fun hc => hp (hV.1 hc)
    -- `insert p U = insert p V`, `p ∉ U, V` ⟹ `U = V`
    have := h
    rw [← Finset.erase_insert hpU, ← Finset.erase_insert hpV, this]
  rw [Finset.sum_image hinj, Finset.powersetCard_one, Finset.sum_map, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun q hq => ?_)
  have hpq : p ∉ ({q} : Finset ι) := by
    simp only [Finset.mem_singleton]; rintro rfl; exact hp hq
  simp only [Function.Embedding.coeFn_mk]
  rw [Finset.prod_insert hpq, Finset.prod_singleton]

/-! ## `e_1`, `e_2` of a disjoint union (the additivity used to peel off the doubled pairs). -/

/-- **`e_1` is additive on disjoint unions.** -/
theorem esymm1_union (v : ι → F) {A B : Finset ι} (h : Disjoint A B) :
    esymm1 v (A ∪ B) = esymm1 v A + esymm1 v B := by
  simp only [esymm1, Finset.sum_union h]

/-- **`e_2` of a disjoint union**: `e_2(A ∪ B) = e_2 A + e_2 B + e_1 A · e_1 B`. The order-2 symmetric
function of a disjoint union has the cross term `e_1 A · e_1 B` from pairs straddling `A` and `B`. We
prove it by induction on `B`, peeling one element at a time with the Pascal recursion `esymm2_insert`
and the `e_1` additivity. -/
theorem esymm2_union (v : ι → F) {A B : Finset ι} (h : Disjoint A B) :
    esymm2 v (A ∪ B) = esymm2 v A + esymm2 v B + esymm1 v A * esymm1 v B := by
  classical
  induction B using Finset.induction with
  | empty => simp [esymm2_empty]
  | insert q B hqB ih =>
      have hqA : q ∉ A := fun hc => (Finset.disjoint_left.mp h hc) (Finset.mem_insert_self q B)
      have hdisjB : Disjoint A B :=
        h.mono_right (Finset.subset_insert q B)
      have hqAB : q ∉ A ∪ B := by
        rw [Finset.mem_union]; push Not; exact ⟨hqA, hqB⟩
      have hunion : A ∪ insert q B = insert q (A ∪ B) := by
        rw [Finset.union_insert]
      rw [hunion, esymm2_insert v hqAB, ih hdisjB,
        esymm2_insert v hqB, esymm1_insert v (S := B) hqB,
        esymm1_union v hdisjB]
      ring

/-! ## A single zero-sum ± pair (in the index model): `e_1 = 0`, `e_2 = −g²`. -/

/-- The two slots of pair `i` are distinct as indices, so `e_1(bothPair i) = g i + (−g i) = 0` —
exactly the Round-4 `sum_bothPair`, restated as `esymm1`. -/
theorem esymm1_bothPair {m : ℕ} (g : Fin m → F) (i : Fin m) :
    esymm1 (pairVal g) (bothPair i) = 0 := sum_bothPair g i

/-- **`e_2` of a single zero-sum pair is `−g i²`.** The only `2`-subset of `bothPair i =
{(i,false),(i,true)}` is the whole pair, whose product is `g i · (−g i) = −g i²`. -/
theorem esymm2_bothPair {m : ℕ} (g : Fin m → F) (i : Fin m) :
    esymm2 (pairVal g) (bothPair i) = -(g i) ^ 2 := by
  classical
  unfold esymm2
  -- `bothPair i` has card 2, so `powersetCard 2 (bothPair i) = {bothPair i}`.
  have hps : (bothPair i).powersetCard 2 = {bothPair i} := by
    conv_lhs => rw [← card_bothPair i]
    exact Finset.powersetCard_self _
  rw [hps, Finset.sum_singleton]
  -- the product over both slots is `g i · (−g i) = −g i²`
  rw [bothPair, Finset.prod_pair (by simp)]
  simp only [pairVal]
  norm_num
  ring

/-! ## The doubled pairs `doubledPairs P`: `e_1 = 0`, `e_2 = −∑_{i∈P} g_i²`. -/

/-- `doubledPairs (insert i P) = bothPair i ∪ doubledPairs P`, with the union disjoint when `i ∉ P`
(distinct pair-indices give disjoint slot-sets). -/
theorem doubledPairs_insert {m : ℕ} {i : Fin m} {P : Finset (Fin m)} (hi : i ∉ P) :
    doubledPairs (insert i P) = bothPair i ∪ doubledPairs P := by
  classical
  rw [doubledPairs, Finset.biUnion_insert, doubledPairs]

/-- `bothPair i` is disjoint from `doubledPairs P` when `i ∉ P` (the slots of pair `i` have
pair-index `i ∉ P`, while every slot of `doubledPairs P` has pair-index in `P`). -/
theorem bothPair_disjoint_doubledPairs {m : ℕ} {i : Fin m} {P : Finset (Fin m)} (hi : i ∉ P) :
    Disjoint (bothPair i) (doubledPairs P) := by
  classical
  rw [Finset.disjoint_left]
  rintro ⟨j, b⟩ hj hjD
  rw [mem_doubledPairs] at hjD
  -- `(j, b) ∈ bothPair i` forces `j = i`, but `j ∈ P` and `i ∉ P`.
  simp only [bothPair, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hj
  rcases hj with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> exact hi hjD

/-- **`e_1` of the doubled pairs vanishes**: each pair contributes `g i + (−g i) = 0`. -/
theorem esymm1_doubledPairs {m : ℕ} (g : Fin m → F) (P : Finset (Fin m)) :
    esymm1 (pairVal g) (doubledPairs P) = 0 := by
  classical
  induction P using Finset.induction with
  | empty => simp [doubledPairs, esymm1]
  | insert i P hi ih =>
      rw [doubledPairs_insert hi,
        esymm1_union (pairVal g) (bothPair_disjoint_doubledPairs hi),
        esymm1_bothPair g i, ih, add_zero]

/-- **`e_2` of the doubled pairs is `−∑_{i∈P} g_i²`.** Inducting on `P`: each added pair contributes
`e_2 = −g_i²` (`esymm2_bothPair`), and the cross term `e_1(bothPair i) · e_1(doubledPairs P)` vanishes
because *both* factors are `0` (`esymm1_bothPair`, `esymm1_doubledPairs`). This is the decisive
all-cross-terms-cancel fact. -/
theorem esymm2_doubledPairs {m : ℕ} (g : Fin m → F) (P : Finset (Fin m)) :
    esymm2 (pairVal g) (doubledPairs P) = -∑ i ∈ P, (g i) ^ 2 := by
  classical
  induction P using Finset.induction with
  | empty => simp [doubledPairs]
  | insert i P hi ih =>
      rw [doubledPairs_insert hi,
        esymm2_union (pairVal g) (bothPair_disjoint_doubledPairs hi),
        esymm2_bothPair g i, ih, esymm1_bothPair g i, zero_mul, add_zero,
        Finset.sum_insert hi]
      ring

/-! ## The inflated subset: `e_1` fixed, `e_2` shifted by `−∑_{i∈P} g_i²`. -/

/-- **`e_1(inflate B P) = e_1 B`.** Adjoining the doubled (untouched) pairs to a base does not change
`e_1` (each pair sums to `0`). The valuation analogue of Round-4 `sum_inflate`. -/
theorem esymm1_inflate {m : ℕ} (g : Fin m → F) {B : Finset (Fin m × Bool)} {P : Finset (Fin m)}
    (hdisj : ∀ i ∈ P, i ∉ touched B) :
    esymm1 (pairVal g) (inflate B P) = esymm1 (pairVal g) B := by
  classical
  have hdj : Disjoint B (doubledPairs P) := by
    rw [Finset.disjoint_left]
    rintro ⟨i, b⟩ hB hD
    rw [mem_doubledPairs] at hD
    exact hdisj i hD (Finset.mem_image.mpr ⟨(i, b), hB, rfl⟩)
  rw [inflate, esymm1_union (pairVal g) hdj, esymm1_doubledPairs, add_zero]

/-- **`e_2(inflate B P) = e_2 B − ∑_{i∈P} g_i²`** — the heart of the `t = 2` construction.
By disjoint-union additivity `e_2(B ∪ doubledPairs P) = e_2 B + e_2(doubledPairs P) +
e_1 B · e_1(doubledPairs P)`; the cross term vanishes because `e_1(doubledPairs P) = 0`
(`esymm1_doubledPairs`), and `e_2(doubledPairs P) = −∑_{i∈P} g_i²` (`esymm2_doubledPairs`). So the
doubled pairs shift `e_2` by exactly `−∑_{i∈P} g_i²`, **independently of the base `B`'s `e_1`**. This
is the cross-term cancellation that Round 4's `e_1`-only doubling did not need. -/
theorem esymm2_inflate {m : ℕ} (g : Fin m → F) {B : Finset (Fin m × Bool)} {P : Finset (Fin m)}
    (hdisj : ∀ i ∈ P, i ∉ touched B) :
    esymm2 (pairVal g) (inflate B P) = esymm2 (pairVal g) B - ∑ i ∈ P, (g i) ^ 2 := by
  classical
  have hdj : Disjoint B (doubledPairs P) := by
    rw [Finset.disjoint_left]
    rintro ⟨i, b⟩ hB hD
    rw [mem_doubledPairs] at hD
    exact hdisj i hD (Finset.mem_image.mpr ⟨(i, b), hB, rfl⟩)
  rw [inflate, esymm2_union (pairVal g) hdj, esymm2_doubledPairs,
    esymm1_doubledPairs, mul_zero, add_zero]
  ring

/-! ## The two counts and the headline `t = 2` joint lower bound. -/

open Classical in
/-- **The joint two-symmetric fiber count** `N₂(g, c, t₁, t₂)`: the number of index-subsets
`S ⊆ Fin m × Bool` of size `c` with **both** `e_1(S) = t₁` and `e_2(S) = t₂`. With `c = k+2`,
`t₁ = c_1`, `t₂ = c_2` this is exactly the `t = 2` degree-drop family count of Round 5's
`degDrop_t2_iff_two_symmetric`. -/
noncomputable def twoSymmCount {m : ℕ} (g : Fin m → F) (c : ℕ) (t₁ t₂ : F) : ℕ :=
  ((Finset.univ : Finset (Finset (Fin m × Bool))).filter
    (fun S => S.card = c ∧ esymm1 (pairVal g) S = t₁ ∧ esymm2 (pairVal g) S = t₂)).card

open Classical in
/-- **The pair-square subset-sum count** `Nsq(g, U, s, sq)`: the number of `s`-subsets `P` of the
(untouched) pair-index set `U` whose **squares** sum to `sq`, `∑_{i∈P} g_i² = sq`. This is a
`t = 1`-shaped subset-sum count, *one level down*, on the ground set `{g_i² : i ∈ U}`. -/
noncomputable def squareSubsetSumCount {m : ℕ} (g : Fin m → F) (U : Finset (Fin m)) (s : ℕ)
    (sq : F) : ℕ :=
  ((U.powersetCard s).filter (fun P => ∑ i ∈ P, (g i) ^ 2 = sq)).card

/-- **The `t = 2` joint two-symmetric LOWER bound (the headline).**

Let `B` be a *transversal base* (Round 4), of size `a`, with `e_1(B) = c₁` and `e_2(B) = c₂₀`. Let
`U = { untouched pairs }`. Then for every square-target `sq` and every `s`, the count of size-`(a+2s)`
subsets with **both** `e_1 = c₁` and `e_2 = c₂₀ − sq` is at least the pair-square subset-sum count:

  `Nsq(g, U, s, sq)  ≤  N₂(g, a+2s, c₁, c₂₀ − sq)`.

Each `s`-subset `P ⊆ U` with `∑_{i∈P} g_i² = sq` is doubled into `B`, inflating the size by `2s`
(`card_inflate`) while keeping `e_1` **exactly** at `c₁` (`esymm1_inflate`) and shifting `e_2` to
`c₂₀ − sq` (`esymm2_inflate`); distinct `P` give distinct inflated sets (`inflate_injective`, `B`
transversal). This is the precise `t = 2` analogue of Round 4's `subsetSumCount_ge_choose`: the joint
`(e_1, e_2)` count is bounded below by the **subset-sum count on the pair-squares**, field-
independently. -/
theorem twoSymmCount_ge_squareSubsetSum {m : ℕ} (g : Fin m → F) {B : Finset (Fin m × Bool)}
    (hB : IsTransversalBase B) {a : ℕ} (hcard : B.card = a)
    {c₁ c₂₀ : F} (h1 : esymm1 (pairVal g) B = c₁) (h2 : esymm2 (pairVal g) B = c₂₀)
    (s : ℕ) (sq : F) :
    squareSubsetSumCount g (Finset.univ.filter (fun i => i ∉ touched B)) s sq
      ≤ twoSymmCount g (a + 2 * s) c₁ (c₂₀ - sq) := by
  classical
  set U : Finset (Fin m) := Finset.univ.filter (fun i => i ∉ touched B) with hU
  set Ψ : Finset (Fin m) → Finset (Fin m × Bool) := fun P => inflate B P with hΨ
  -- the image of the square-sum `s`-subsets lands in the joint two-symmetric fiber
  have hmaps : ∀ P ∈ (U.powersetCard s).filter (fun P => ∑ i ∈ P, (g i) ^ 2 = sq), Ψ P ∈
      (Finset.univ : Finset (Finset (Fin m × Bool))).filter
        (fun S => S.card = a + 2 * s ∧ esymm1 (pairVal g) S = c₁ ∧
          esymm2 (pairVal g) S = c₂₀ - sq) := by
    intro P hPmem
    rw [Finset.mem_filter, Finset.mem_powersetCard] at hPmem
    obtain ⟨⟨hPsub, hPcard⟩, hPsq⟩ := hPmem
    -- `P ⊆ U` ⟹ every pair of `P` is untouched
    have huntouched : ∀ i ∈ P, i ∉ touched B := by
      intro i hi
      have := hPsub hi
      rw [hU, Finset.mem_filter] at this
      exact this.2
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, ?_, ?_⟩
    · rw [hΨ, card_inflate huntouched, hcard, hPcard]
    · rw [hΨ, esymm1_inflate g huntouched, h1]
    · rw [hΨ, esymm2_inflate g huntouched, h2, hPsq]
  -- `Ψ = inflate B` is injective on subsets of `U` (`B` transversal)
  have hinj : Set.InjOn Ψ
      ((U.powersetCard s).filter (fun P => ∑ i ∈ P, (g i) ^ 2 = sq) : Set (Finset (Fin m))) := by
    intro P _ Q _ hPQ
    exact inflate_injective hB hPQ
  -- count the injective image
  calc squareSubsetSumCount g U s sq
      = ((U.powersetCard s).filter (fun P => ∑ i ∈ P, (g i) ^ 2 = sq)).card := rfl
    _ = (((U.powersetCard s).filter (fun P => ∑ i ∈ P, (g i) ^ 2 = sq)).image Ψ).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ twoSymmCount g (a + 2 * s) c₁ (c₂₀ - sq) := by
        rw [twoSymmCount]
        apply Finset.card_le_card
        intro S hS
        rw [Finset.mem_image] at hS
        obtain ⟨P, hPmem, rfl⟩ := hS
        exact hmaps P hPmem

/-! ## The unconditional zero-target instance (a genuinely-large joint family, no open hypothesis). -/

/-- **Zero-base, zero-square-target specialization.** With the empty base (`e_1 = e_2 = 0`, all `m`
pairs untouched), the joint `(e_1 = 0, e_2 = 0)` fiber at size `2s` is at least the count of
`s`-subsets of all pairs whose squares sum to `0`:

  `#{ P : |P| = s, ∑_{i∈P} g_i² = 0 }  ≤  N₂(g, 2s, 0, 0)`.

This is the cleanest hypothesis-free `t = 2` joint lower bound: any `s` pairs whose squares cancel,
doubled, give a size-`2s` subset with **both** `e_1 = 0` and `e_2 = 0`. (Whether the square-cancelling
count is itself super-polynomial is the open subset-sum question *one level down* on `{g_i²}` — the
honest residual.) -/
theorem twoSymmCount_zero_ge_squareSubsetSum {m : ℕ} (g : Fin m → F) (s : ℕ) :
    squareSubsetSumCount g Finset.univ s 0 ≤ twoSymmCount g (2 * s) (0 : F) (0 : F) := by
  classical
  have hempty : IsTransversalBase (∅ : Finset (Fin m × Bool)) := by
    intro x hx; simp at hx
  have huniv : (Finset.univ.filter
      (fun i => i ∉ touched (∅ : Finset (Fin m × Bool)))) = (Finset.univ : Finset (Fin m)) := by
    apply Finset.filter_true_of_mem
    intro i _; rw [touched]; simp
  have h := twoSymmCount_ge_squareSubsetSum g hempty (a := 0) (by simp)
    (c₁ := (0 : F)) (c₂₀ := (0 : F)) (by simp [esymm1]) (by simp [esymm2_empty]) s (0 : F)
  rw [huniv] at h
  simpa using h

/-! ## Non-vacuity: the construction produces genuine distinct subsets. -/

/-- **Non-vacuity of the pair-square count at the zero target.** The empty pair-set has square-sum
`0`, so `Nsq(g, univ, 0, 0) ≥ 1`. -/
theorem squareSubsetSumCount_zero_pos {m : ℕ} (g : Fin m → F) :
    1 ≤ squareSubsetSumCount g Finset.univ 0 0 := by
  classical
  rw [squareSubsetSumCount]
  apply Finset.card_pos.mpr
  refine ⟨∅, ?_⟩
  rw [Finset.mem_filter, Finset.mem_powersetCard]
  exact ⟨⟨Finset.empty_subset _, Finset.card_empty⟩, by simp⟩

/-- **The headline hypotheses are jointly satisfiable (non-vacuity of the `t = 2` lower bound).** The
empty base is transversal with `e_1 = e_2 = 0`, so `twoSymmCount_zero_ge_squareSubsetSum` applies; at
`s = 0` it yields `1 ≤ N₂(g, 0, 0, 0)` (`squareSubsetSumCount_zero_pos`), a genuine non-vacuous joint
two-symmetric fiber bound, not `0 ≤ …`. -/
theorem twoSymmCount_nonvacuous {m : ℕ} (g : Fin m → F) :
    1 ≤ twoSymmCount g (2 * 0) (0 : F) (0 : F) :=
  le_trans (squareSubsetSumCount_zero_pos g) (twoSymmCount_zero_ge_squareSubsetSum g 0)

end ArkLib.CodingTheory.Round6T2Explicit

/-! ## Axiom audit -/
#print axioms ArkLib.CodingTheory.Round6T2Explicit.esymm2_insert
#print axioms ArkLib.CodingTheory.Round6T2Explicit.esymm2_union
#print axioms ArkLib.CodingTheory.Round6T2Explicit.esymm2_bothPair
#print axioms ArkLib.CodingTheory.Round6T2Explicit.esymm2_doubledPairs
#print axioms ArkLib.CodingTheory.Round6T2Explicit.esymm1_inflate
#print axioms ArkLib.CodingTheory.Round6T2Explicit.esymm2_inflate
#print axioms ArkLib.CodingTheory.Round6T2Explicit.twoSymmCount_ge_squareSubsetSum
#print axioms ArkLib.CodingTheory.Round6T2Explicit.twoSymmCount_zero_ge_squareSubsetSum
#print axioms ArkLib.CodingTheory.Round6T2Explicit.twoSymmCount_nonvacuous
