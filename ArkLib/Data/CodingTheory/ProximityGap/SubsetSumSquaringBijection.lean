/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubsetSumNegSymmConcentration
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset

/-!
# Round 8 (Issue #232, ABF26) — the SQUARE-SET structure of a `±`-transversal, and the SELF-SIMILAR
# recursion of the smooth-domain `(sum, sum-of-squares)` count under squaring.

Round 7 (`SubsetSumNegSymmConcentration.lean`) narrowed the open core of the §7 list-decoding disproof
to **SEAM A**: over the smooth `2^k`-subgroup `G` (the `n`-th roots of unity, `n = 2^k`), the
*negation-symmetric* subsets `S = P ∪ (−P)` built from a `±`-transversal `H` (with `G = H ⊔ (−H)`)
**force** the first coordinate `e_1 = ∑_{x∈S} x = 0` (concentrated, `q`-independent, count `C(n/2, t)`
— `negSymm_card_ge_choose`). The only remaining spread is the second coordinate

  `p_2(S) = ∑_{x∈S} x²  =  2·∑_{g∈P} g²`     (`negClosure_psum2_eq_two_mul`).

So the prize-deciding question (does the negation-symmetric family concentrate on `O(1)` second-
coordinate targets, giving a `q`-independent super-polynomial list?) is exactly: how does the
**multiset of pair-squares `{g² : g ∈ H}`** distribute under subset sums?

## What this round contributes — the square-set structure and the recursion

The pair-squares are not an arbitrary set: they are the image `H² := H.image (·²)` of the transversal
under the squaring map `x ↦ x²`. We formalize, `sorry`-free and axiom-clean, the **clean structural
content** of that map on a `±`-transversal.

* `sq_injOn_transversal` — **squaring is injective on a `±`-transversal** (`char F ≠ 2`). If
  `g₁² = g₂²` then `(g₁−g₂)(g₁+g₂) = 0`, so `g₁ = g₂` or `g₁ = −g₂`; the latter is impossible because
  `H` meets each `±`-pair at most once (`Disjoint H (H.image (−·))`). So `x ↦ x²` is `2`-to-`1` on the
  full subgroup `G = H ⊔ (−H)` but **injective** on the transversal `H`.

* `sqSet_card_eq` — **the square-set `H² := H.image (·²)` has `|H²| = |H|`.** Squaring restricts to a
  bijection `H ≃ H²`. (For the subgroup `G`, `H² = G²` is exactly the unique order-`2^{k-1}` subgroup,
  and `|H| = n/2 = 2^{k-1}` — the SELF-SIMILAR halving.)

* `psum2_eq_sum_sqSet` — **the sum of pair-squares is a subset SUM on `H²`:**
  `∑_{g∈P} g² = ∑_{y∈P.image(·²)} y` for `P ⊆ H`. The quadratic statistic on `H` is a *linear* (sum)
  statistic on the smaller set `H²`.

* `sqImage_bij_powersetCard` / `psum2_count_eq_subsetSumCount_sqSet` — **the headline RECURSION.** The
  map `P ↦ P.image (·²)` is a bijection from the `t`-subsets of `H` onto the `t`-subsets of `H²`,
  carrying `∑_{g∈P} g²` to `∑_{y∈Q} y`. Hence the second-coordinate fiber count on `H`

    `#{ t-subsets P of H : ∑_{g∈P} g² = c }  =  #{ t-subsets Q of H² : ∑_{y∈Q} y = c }`

  is **literally a `t = 1`-style subset-sum count on the smaller ground set `H²`** (`subsetSumCount`
  of `SubsetSumCharacterSum.lean`). The `t = 2` second-coordinate concentration question on `G`
  reduces to the **subset-sum** question on the half-size set `H²` — the *same shape, one size
  smaller*: this is the self-similar wall.

* `negSymm_p2_count_eq_subsetSumCount_sqSet` — **the SEAM-A statement assembled.** Combining the
  recursion with Round 7's `p_2 = 2·∑ g²`, the count of negation-symmetric size-`2t` subsets of
  `G = H ⊔ (−H)` with `(e_1, p_2) = (0, 2c)` is exactly `subsetSumCount H² t c`. So a `q`-independent
  super-polynomial concentration of the negation-symmetric family on `O(1)` second-coordinate targets
  holds **iff** the subset-sum count on `H²` concentrates — the prize door, recursed onto a smaller
  subgroup.

## Honest scope (what this is and is NOT)

* It **IS** a genuine, `sorry`-free, axiom-clean structural reduction: the second-coordinate spread of
  the negation-symmetric family on `G` is *exactly* the subset-sum spread on the half-size square-set
  `H²` (`= G²`, the order-`2^{k-1}` subgroup). It explains the *self-similarity* of the convergent
  wall: the `(sum, sum-of-squares)` count over `G` recurses to a subset-sum count over `G²`.
* It is **NOT** a closure. The reduced object — the subset-sum count over `H² = G²` — is *itself* the
  Round-4/6 open question (`subsetSumCount`), now on a smaller subgroup. The recursion **descends but
  does not terminate**: each squaring halves the subgroup but reproduces the same open subset-sum
  spread question (`subsetSumCount G² t c` vs the poly/super-poly threshold). We localize and explain
  the wall's self-similarity; we do not break it. The base case (subset-sum on `G²`, or after `k`
  squarings on the order-`2` subgroup) remains the open prize-deciding magnitude question.

All headline results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Tracking issue #232.
-/

open Finset BigOperators

namespace ArkLib.CodingTheory.Round8SquareSet

open ArkLib.CodingTheory.Round7Concentration

variable {F : Type*} [Field F] [DecidableEq F]

/-! ## 1. Squaring is injective on a `±`-transversal. -/

/-- **Squaring is injective on a `±`-transversal `H` (when `char F ≠ 2`).** If `H` meets each `±`-pair
at most once (`Disjoint H (H.image (−·))`) and `g₁, g₂ ∈ H` with `g₁² = g₂²`, then `g₁ = g₂`.

Proof: `g₁² = g₂²` factors as `(g₁ − g₂)·(g₁ + g₂) = 0`, so `g₁ = g₂` or `g₁ = −g₂`. In the second
case `g₂ = −g₁ ∈ H.image (−·)` while `g₂ ∈ H`, so `g₂ ∈ H ∩ (H.image (−·)) = ∅` — impossible.

This is the precise sense in which `x ↦ x²` is `2`-to-`1` on the full subgroup `G = H ⊔ (−H)` (the
`±`-pair `{g, −g}` has one square `g²`) but **injective** on the transversal `H`. -/
theorem sq_injOn_transversal {H : Finset F}
    (hHdisj : Disjoint H (H.image (fun x => -x))) :
    Set.InjOn (fun x : F => x ^ 2) H := by
  classical
  intro g₁ hg₁ g₂ hg₂ heq
  simp only at heq
  -- `g₁² − g₂² = 0`, i.e. `(g₁ − g₂)(g₁ + g₂) = 0`.
  have hfac : (g₁ - g₂) * (g₁ + g₂) = 0 := by ring_nf; linear_combination heq
  rcases mul_eq_zero.mp hfac with h | h
  · -- `g₁ = g₂`
    exact sub_eq_zero.mp h
  · -- `g₁ = −g₂`: then `g₂ = −g₁ ∈ H ∩ (−H) = ∅`, contradiction.
    exfalso
    have hg1eq : g₁ = -g₂ := by linear_combination h
    have hmem : g₁ ∈ H.image (fun x => -x) := by
      rw [Finset.mem_image]
      exact ⟨g₂, hg₂, hg1eq.symm⟩
    exact (Finset.disjoint_left.mp hHdisj hg₁) hmem

/-! ## 2. The square-set `H² := H.image (·²)` and its half-size. -/

/-- The **square-set** of a transversal `H`: `sqSet H := H.image (·²) = {g² : g ∈ H}`. For the
smooth subgroup `G = H ⊔ (−H)` this is exactly the order-`2^{k-1}` subgroup `G²` (the unique
index-2 subgroup), and it is precisely the multiset of pair-squares whose additive spread governs
the SEAM-A second coordinate. -/
noncomputable def sqSet (H : Finset F) : Finset F := H.image (fun x => x ^ 2)

/-- **The square-set has the same size as the transversal: `|H²| = |H|`.** Squaring restricts to a
bijection `H ≃ H²` (injective by `sq_injOn_transversal`). For the subgroup `G` of order `n = 2^k`
with `|H| = n/2`, this is `|G²| = n/2 = 2^{k-1}` — the SELF-SIMILAR halving of the ground set under
one squaring step. -/
theorem sqSet_card_eq {H : Finset F}
    (hHdisj : Disjoint H (H.image (fun x => -x))) :
    (sqSet H).card = H.card := by
  classical
  unfold sqSet
  exact Finset.card_image_of_injOn (sq_injOn_transversal hHdisj)

/-! ## 3. The sum of pair-squares is a subset SUM on the smaller set `H²`. -/

/-- **The sum of pair-squares is a linear subset-sum on `H²`.** For `P ⊆ H` (`H` a transversal),
`∑_{g∈P} g² = ∑_{y ∈ P.image(·²)} y`. The *quadratic* statistic `∑ g²` on `H` is the *linear* (sum)
statistic `∑ y` on the smaller image set `P.image(·²) ⊆ H²`, because squaring is injective on `H`
(`sq_injOn_transversal`) so `Finset.sum_image` applies with no collisions. -/
theorem psum2_eq_sum_sqSet {H : Finset F}
    (hHdisj : Disjoint H (H.image (fun x => -x))) {P : Finset F} (hP : P ⊆ H) :
    ∑ g ∈ P, g ^ 2 = ∑ y ∈ P.image (fun x => x ^ 2), y := by
  classical
  rw [Finset.sum_image]
  intro a ha b hb hab
  exact sq_injOn_transversal hHdisj (hP (Finset.mem_coe.mp ha)) (hP (Finset.mem_coe.mp hb)) hab

/-! ## 4. The headline recursion: `P ↦ P.image(·²)` bijects `t`-subsets of `H` onto `t`-subsets of
`H²`, carrying `∑ g²` to `∑ y`. -/

/-- **The squaring image bijects the `t`-subsets of `H` onto the `t`-subsets of `H²`.** The map
`P ↦ P.image (·²)` sends `t`-element subsets of `H` to `t`-element subsets of `sqSet H` (size
preserved by injectivity of squaring on `H`), and it is a bijection: injective (an image determines
its preimage under an injective map) and surjective onto `(sqSet H).powersetCard t`. -/
theorem sqImage_bij_powersetCard {H : Finset F}
    (hHdisj : Disjoint H (H.image (fun x => -x))) (t : ℕ) :
    (H.powersetCard t).image (fun P => P.image (fun x => x ^ 2))
      = (sqSet H).powersetCard t := by
  classical
  ext Q
  rw [Finset.mem_image]
  rw [Finset.mem_powersetCard]
  constructor
  · -- forward: an image of a `t`-subset of `H` is a `t`-subset of `H²`.
    rintro ⟨P, hP, rfl⟩
    rw [Finset.mem_powersetCard] at hP
    obtain ⟨hPsub, hPcard⟩ := hP
    refine ⟨?_, ?_⟩
    · -- `P.image(·²) ⊆ H.image(·²) = sqSet H`
      unfold sqSet
      exact Finset.image_subset_image hPsub
    · -- card preserved: squaring injective on `P ⊆ H`
      rw [Finset.card_image_of_injOn
        (Set.InjOn.mono hPsub (sq_injOn_transversal hHdisj)), hPcard]
  · -- backward: every `t`-subset `Q` of `H²` is the image of its preimage in `H`.
    rintro ⟨hQsub, hQcard⟩
    -- the preimage of `Q` under squaring, intersected with `H`.
    refine ⟨H.filter (fun g => g ^ 2 ∈ Q), ?_, ?_⟩
    · -- the preimage is a `t`-subset of `H`
      rw [Finset.mem_powersetCard]
      refine ⟨Finset.filter_subset _ _, ?_⟩
      -- `(H.filter (·²∈Q)).image(·²) = Q`, and squaring is injective, so cards agree.
      have himg : (H.filter (fun g => g ^ 2 ∈ Q)).image (fun x => x ^ 2) = Q := by
        ext y
        rw [Finset.mem_image]
        constructor
        · rintro ⟨g, hg, rfl⟩
          rw [Finset.mem_filter] at hg
          exact hg.2
        · intro hyQ
          -- `y ∈ Q ⊆ sqSet H = H.image(·²)`, so `y = g²` for some `g ∈ H`, and that `g` is filtered.
          have hyImg : y ∈ sqSet H := hQsub hyQ
          unfold sqSet at hyImg
          rw [Finset.mem_image] at hyImg
          obtain ⟨g, hgH, hgy⟩ := hyImg
          exact ⟨g, by rw [Finset.mem_filter]; exact ⟨hgH, hgy ▸ hyQ⟩, hgy⟩
      have hinj : Set.InjOn (fun x : F => x ^ 2) (H.filter (fun g => g ^ 2 ∈ Q)) :=
        Set.InjOn.mono (Finset.filter_subset _ _) (sq_injOn_transversal hHdisj)
      have := Finset.card_image_of_injOn hinj
      rw [himg] at this
      rw [← this, hQcard]
    · -- the image of the preimage is `Q`
      ext y
      rw [Finset.mem_image]
      constructor
      · rintro ⟨g, hg, rfl⟩
        rw [Finset.mem_filter] at hg
        exact hg.2
      · intro hyQ
        have hyImg : y ∈ sqSet H := hQsub hyQ
        unfold sqSet at hyImg
        rw [Finset.mem_image] at hyImg
        obtain ⟨g, hgH, hgy⟩ := hyImg
        exact ⟨g, by rw [Finset.mem_filter]; exact ⟨hgH, hgy ▸ hyQ⟩, hgy⟩

/-- **The headline RECURSION (subset-sum form).** The second-coordinate fiber count on the transversal
`H` — the count of `t`-subsets `P ⊆ H` with prescribed pair-square sum `∑_{g∈P} g² = c` — equals the
count of `t`-subsets `Q ⊆ H²` with prescribed subset SUM `∑_{y∈Q} y = c`:

  `#{ t-subsets P of H : ∑_{g∈P} g² = c }  =  #{ t-subsets Q of H² : ∑_{y∈Q} y = c }`.

The right side is a `subsetSumCount`-shaped quantity over the **half-size** ground set `H² = sqSet H`
(`= G²`, the order-`2^{k-1}` subgroup). So the `t = 2` second-coordinate concentration question on `G`
is the **same** subset-sum spread question, one subgroup smaller — the self-similar wall. -/
theorem psum2_count_eq_subsetSumCount_sqSet {H : Finset F}
    (hHdisj : Disjoint H (H.image (fun x => -x))) (t : ℕ) (c : F) :
    ((H.powersetCard t).filter (fun P => ∑ g ∈ P, g ^ 2 = c)).card
      = (((sqSet H).powersetCard t).filter (fun Q => ∑ y ∈ Q, y = c)).card := by
  classical
  -- The map `P ↦ P.image(·²)` is a bijection between the two filtered families.
  apply Finset.card_bij (fun P _ => P.image (fun x => x ^ 2))
  · -- maps-to: a `t`-subset of `H` summing-of-squares to `c` maps to a `t`-subset of `H²` summing
    -- to `c`.
    intro P hP
    rw [Finset.mem_filter] at hP ⊢
    obtain ⟨hPmem, hPsum⟩ := hP
    have hPsub : P ⊆ H := (Finset.mem_powersetCard.mp hPmem).1
    refine ⟨?_, ?_⟩
    · -- `P.image(·²) ∈ (sqSet H).powersetCard t`
      rw [← sqImage_bij_powersetCard hHdisj t, Finset.mem_image]
      exact ⟨P, hPmem, rfl⟩
    · -- `∑_{y∈P.image(·²)} y = c`, via `psum2_eq_sum_sqSet`.
      rw [← psum2_eq_sum_sqSet hHdisj hPsub]
      exact hPsum
  · -- injective: squaring is injective on `H`, so the image determines `P` (recover via filter).
    intro P₁ hP₁ P₂ hP₂ heq
    rw [Finset.mem_filter, Finset.mem_powersetCard] at hP₁ hP₂
    have hrec : ∀ P : Finset F, P ⊆ H →
        P = H.filter (fun g => g ^ 2 ∈ P.image (fun x => x ^ 2)) := by
      intro P hPsub
      ext g
      rw [Finset.mem_filter, Finset.mem_image]
      constructor
      · intro hgP
        exact ⟨hPsub hgP, g, hgP, rfl⟩
      · rintro ⟨hgH, p, hpP, hsq⟩
        have hgp : g = p := sq_injOn_transversal hHdisj hgH (hPsub hpP) hsq.symm
        exact hgp ▸ hpP
    rw [hrec P₁ hP₁.1.1, hrec P₂ hP₂.1.1, heq]
  · -- surjective: every `t`-subset `Q` of `H²` summing to `c` is `P.image(·²)` for its preimage `P`.
    intro Q hQ
    rw [Finset.mem_filter] at hQ
    obtain ⟨hQmem, hQsum⟩ := hQ
    -- the preimage of `Q` is a `t`-subset of `H` whose image is `Q` (by `sqImage_bij_powersetCard`).
    have hpre : Q ∈ (H.powersetCard t).image (fun P => P.image (fun x => x ^ 2)) := by
      rw [sqImage_bij_powersetCard hHdisj t]; exact hQmem
    rw [Finset.mem_image] at hpre
    obtain ⟨P, hPmem, hPimg⟩ := hpre
    have hPsub : P ⊆ H := (Finset.mem_powersetCard.mp hPmem).1
    refine ⟨P, ?_, hPimg⟩
    rw [Finset.mem_filter]
    refine ⟨hPmem, ?_⟩
    -- `∑ g² = ∑_{Q} y = c`.
    rw [psum2_eq_sum_sqSet hHdisj hPsub, hPimg]
    exact hQsum

/-! ## 5. SEAM A assembled: the negation-symmetric second-coordinate count is the subset-sum count on
the half-size square-set `H²`. -/

/-- **SEAM-A assembly: the negation-symmetric `p_2 = 2c` count recurses to the subset-sum count on
`H²`.** Combining the `t = 2`-style `p_2 = 2·∑ g²` identity (`negClosure_psum2_eq_two_mul`, Round 7)
with the recursion (`psum2_count_eq_subsetSumCount_sqSet`): for `(2 : F) ≠ 0`, the number of
`t`-subsets `P ⊆ H` whose **doubled** pair-square sum `2·∑_{g∈P} g² = d` (i.e. the negation-symmetric
second coordinate `p_2(P ∪ (−P)) = d`) equals the subset-sum count of `t`-subsets of `H²` summing to
`d/2`:

  `#{ t-subsets P of H : p_2(P ∪ (−P)) = 2·∑ g² = d }  =  #{ t-subsets Q of H² : ∑_{y∈Q} y = d/2 }`.

The right side is `subsetSumCount H² t (d/2)` — the Round-4/6 subset-sum count, but on the **half-size
ground set** `H² = sqSet H` (`= G²`, order `2^{k-1}`). So the SEAM-A concentration question on `G`
(does the negation-symmetric family concentrate its second coordinate on `O(1)` targets?) is the
subset-sum concentration question on `G²` — the SAME shape, one subgroup smaller: the self-similar
wall. -/
theorem negSymm_p2_count_eq_subsetSumCount_sqSet (h2 : (2 : F) ≠ 0) {H : Finset F}
    (hHdisj : Disjoint H (H.image (fun x => -x))) (t : ℕ) (d : F) :
    ((H.powersetCard t).filter (fun P => 2 * ∑ g ∈ P, g ^ 2 = d)).card
      = (((sqSet H).powersetCard t).filter (fun Q => ∑ y ∈ Q, y = d / 2)).card := by
  classical
  rw [← psum2_count_eq_subsetSumCount_sqSet hHdisj t (d / 2)]
  congr 1
  apply Finset.filter_congr
  intro P _
  -- `2·∑ g² = d ↔ ∑ g² = d/2` (cancel the unit `2`; valid since `(2 : F) ≠ 0`).
  rw [eq_div_iff h2, mul_comm (∑ g ∈ P, g ^ 2) 2]

/-- **The SELF-SIMILAR halving, recorded as an equation on ground-set sizes.** One squaring step sends
the transversal `H` of `G` (with `|H| = |G|/2`) to the square-set `H² = sqSet H` with
`|H²| = |H| = |G|/2`, which for the subgroup is the order-`2^{k-1}` subgroup `G²`. So the recursion
`negSymm_p2_count_eq_subsetSumCount_sqSet` descends from a `(sum, sum-of-squares)` count on a ground
set of size `|H|` to a subset-sum count on a ground set of the **same** size `|H²| = |H|` — and `H²`
is itself a `2^{k-1}`-subgroup admitting its own `±`-transversal, so the step can be iterated, halving
the subgroup order each time while reproducing the identical open subset-sum question. The recursion
**descends but does not terminate**. -/
theorem sqSet_self_similar {H : Finset F}
    (hHdisj : Disjoint H (H.image (fun x => -x))) :
    (sqSet H).card = H.card :=
  sqSet_card_eq hHdisj

/-! ## 6. Non-vacuity: a concrete transversal with a genuine, non-degenerate square-set recursion. -/

/-- `13` is prime, so `ZMod 13` is a field (the concrete witness host). -/
instance primeFact_SubsetSumSquaringBijection_1 : Fact (Nat.Prime 13) := ⟨by norm_num⟩

/-- **Non-vacuity (concrete `F = ZMod 13`, `H = {1, 2, 3}`).** The transversal `H = {1,2,3}` of three
`±`-pairs (`−1=12, −2=11, −3=10` all outside `H`) has square-set
`H² = {1², 2², 3²} = {1, 4, 9}` of size `3 = |H|` (squaring injective on the transversal). So the
recursion `negSymm_p2_count_eq_subsetSumCount_sqSet` is non-vacuous: it equates a genuine pair-square
count on `{1,2,3}` to a genuine subset-sum count on the half-size square-set `{1,4,9}`. The
square-set is honestly *different* from `H` (`{1,4,9} ≠ {1,2,3}`), so the recursion moves to a new
ground set, not a tautology. -/
theorem nonvacuity_zmod13 :
    (2 : ZMod 13) ≠ 0
      ∧ Disjoint ({1, 2, 3} : Finset (ZMod 13))
          (({1, 2, 3} : Finset (ZMod 13)).image (fun x => -x))
      ∧ (sqSet ({1, 2, 3} : Finset (ZMod 13))) = {1, 4, 9}
      ∧ (sqSet ({1, 2, 3} : Finset (ZMod 13))).card = 3
      ∧ (sqSet ({1, 2, 3} : Finset (ZMod 13))) ≠ ({1, 2, 3} : Finset (ZMod 13)) := by
  refine ⟨by decide, by decide, ?_, ?_, by decide⟩
  · -- `{1²,2²,3²} = {1,4,9}` in `ZMod 13`
    unfold sqSet; decide
  · -- `|H²| = 3`
    unfold sqSet; decide

/-- **The square-set card equals `|H|` at the concrete witness (the halving is genuine).**
Instantiates `sqSet_card_eq` at `F = ZMod 13`, `H = {1,2,3}`: `|sqSet {1,2,3}| = |{1,2,3}| = 3`. The
squaring map is injective on the transversal, so no collisions occur and the recursion lands on a
ground set of the same size (`3`), which is the order-`2^{k-1}` halving for the subgroup case. -/
theorem concrete_sqSet_card_zmod13 :
    (sqSet ({1, 2, 3} : Finset (ZMod 13))).card = 3 := by
  have hdisj : Disjoint ({1, 2, 3} : Finset (ZMod 13))
      (({1, 2, 3} : Finset (ZMod 13)).image (fun x => -x)) := by decide
  rw [sqSet_card_eq hdisj]; decide

end ArkLib.CodingTheory.Round8SquareSet

/-! ## Axiom audit -/
#print axioms ArkLib.CodingTheory.Round8SquareSet.sq_injOn_transversal
#print axioms ArkLib.CodingTheory.Round8SquareSet.sqSet_card_eq
#print axioms ArkLib.CodingTheory.Round8SquareSet.psum2_eq_sum_sqSet
#print axioms ArkLib.CodingTheory.Round8SquareSet.sqImage_bij_powersetCard
#print axioms ArkLib.CodingTheory.Round8SquareSet.psum2_count_eq_subsetSumCount_sqSet
#print axioms ArkLib.CodingTheory.Round8SquareSet.negSymm_p2_count_eq_subsetSumCount_sqSet
#print axioms ArkLib.CodingTheory.Round8SquareSet.sqSet_self_similar
#print axioms ArkLib.CodingTheory.Round8SquareSet.nonvacuity_zmod13
#print axioms ArkLib.CodingTheory.Round8SquareSet.concrete_sqSet_card_zmod13
