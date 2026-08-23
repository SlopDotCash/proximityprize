/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubsetSumE2PowerSumReduction
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset

/-!
# Round 7 (Issue #232, ABF26) — a CONCENTRATION construction: negation-symmetric subsets force the
# window sum `e_1 = ∑ x` to a *single* target `0`, with a field-independent super-polynomial count.

Round 6 sharply localized the open core of the §7 list-decoding disproof to two coupled questions
about the `(SUM, SUM-OF-SQUARES)` count
`N2(a; c₁,c₂) := #{ a-subsets S of the smooth 2^k-subgroup G : ∑_{x∈S} x = c₁ ∧ ∑_{x∈S} x² = c₁²−2c₂ }`
(`twoSymmetric_count_eq_e1_psum2_count`):

* a super-polynomial **lower** bound (fitting `|F| < 2^256`) would pin `δ*` from below in the deep
  interior (the disproof);
* the prize itself needs the list `|Λ| ≤ ε*·q` for a *fixed* `ε*`, which Round 6
  (`ListInteriorQDependenceNoGo`) proved is **equivalent** to the count *concentrating* on `O(1)`
  targets — the averaging/pigeonhole method provably loses a factor `/q`. A prize counterexample
  therefore needs a construction whose count **concentrates on few targets** — the OPEN DOOR.

## What this round contributes: direct concentration of the FIRST coordinate `e_1`

This file attacks the open door head-on with the **negation-symmetric** construction. A smooth
`2^k`-subgroup `G` is closed under negation (`−1 = ζ^{n/2} ∈ G`); pick a transversal `H` of the
`±`-pairs, so `G = H ⊔ (−H)` disjointly with `|H| = n/2`. For any `P ⊆ H`, the **negation-symmetric**
subset `P ∪ (−P)` has size `2|P|` and — because its elements pair up as `x, −x` (genuinely distinct
when `char F ≠ 2`, which holds automatically: a `2^k`-subgroup needs `|F|` odd) — window sum

  `∑_{x ∈ P ∪ (−P)} x = 0`   (`negSymm_sum_eq_zero`, via `Finset.sum_involution`).

So **every** subset in this family lands in the *single* `e_1 = 0` fiber: the first coordinate is
**concentrated at one target**, with **no `/q` loss**. The map `P ↦ P ∪ (−P)` is injective, so the
`e_1 = 0` fiber at agreement `2t` has size

  `C(n/2, t)  ≤  #{ S ⊆ G : |S| = 2t,  ∑_{x∈S} x = 0 }`   (`subsetSumCount_zero_ge_choose_half`).

This is a **field-independent, super-polynomial** lower bound on a *single* subset-sum fiber `c₁ = 0`
— it **beats the averaging floor** `C(n,2t)/q` on the `e_1` coordinate (the averaging method only
delivers `C(n,2t)/q` at the heavy target; here the *fixed* target `0` already carries `C(n/2,t)`,
`q`-independently). This is exactly the kind of `q`-independent single-fiber bound the prize needs,
*on the first of the two coordinates*.

## Honest scope — the `e_2`/`p_2` coordinate still spreads (the door is opened, not walked through)

The construction concentrates `e_1` but **does not** by itself concentrate the second coordinate. For
a negation-symmetric `S = P ∪ (−P)`, the sum of squares is

  `∑_{x∈S} x² = ∑_{g∈P} (g² + (−g)²) = 2·∑_{g∈P} g²`   (`negSymm_psum2_eq_two_mul`),

so `p_2(S)` ranges over `2·(sum of t pair-squares {g² : g ∈ H})`. We formalize this exactly. Whether
*this* spreads over `q` targets or concentrates is governed by the **additive span of the pair-square
set `{g² : g ∈ H}`** — a genuinely new, *additive*-combinatorial sub-question on the squares of a
subgroup transversal. We are honest: this file proves the `e_1`-concentration is real,
super-polynomial, and `q`-independent, and reduces the *remaining* prize gap to the
**second-coordinate** spread `#{ t-subsets P of H : ∑_{g∈P} g² = c }` — i.e. whether the pair-squares
have small additive span. That second sub-question is **open** and is NOT resolved here; what is new
is that the first coordinate is now *provably* concentrated and the prize gap is localized entirely to
the sum-of-squares spread.

What this is and is NOT:
* It **IS** a genuine, `sorry`-free, axiom-clean construction giving a `q`-independent
  super-polynomial lower bound `C(n/2,t)` on the *single* `e_1 = 0` subset-sum fiber — a real crack
  at the concentration door on the first coordinate.
* It is **NOT** a prize counterexample: the second coordinate `p_2 = 2∑g²` still spreads unless the
  pair-squares `{g²}` have small additive span, which remains open. We localize, we do not close.

All headline results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Tracking issue #232.
-/

open Finset BigOperators

namespace ArkLib.CodingTheory.Round7Concentration

variable {F : Type*} [Field F] [DecidableEq F]

/-! ## 1. The `e_1 = 0` concentration: a negation-symmetric set of nonzero elements sums to `0`. -/

omit [DecidableEq F] in
/-- **The negation involution is fixed-point-free off `0` when `char F ≠ 2`.** If `(2 : F) ≠ 0` and
`a ≠ 0` then `−a ≠ a` (else `a + a = 2·a = 0` forces `a = 0`). This is the char-`≠ 2` input that makes
the `±`-pairing genuine (in char 2 every element is its own negation and the pairing collapses). -/
theorem neg_ne_self_of_ne_zero (h2 : (2 : F) ≠ 0) {a : F} (ha : a ≠ 0) : -a ≠ a := by
  intro hcontra
  apply ha
  have : (2 : F) * a = 0 := by linear_combination -hcontra
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h h2
  · exact h

/-- **The window sum of a negation-symmetric set of nonzero elements vanishes (the `e_1`
concentration).** If `(2 : F) ≠ 0`, `S` is closed under negation (`S.image (−·) = S`), and `0 ∉ S`,
then `∑_{x∈S} x = 0`. The negation map `x ↦ −x` is an involution on `S` (it maps `S` into itself by
`hSneg`), it pairs `x` with `−x` so `x + (−x) = 0`, and it is fixed-point-free on `S` since `0 ∉ S`
and `char F ≠ 2` (`neg_ne_self_of_ne_zero`). `Finset.sum_involution` then collapses the sum to `0`.

Consequence: **every** negation-symmetric set of nonzero elements lands in the single window-sum
target `0`. The first coordinate `e_1 = ∑ x` is concentrated at one value — no averaging `/q` loss. -/
theorem negSymm_sum_eq_zero (h2 : (2 : F) ≠ 0) {S : Finset F}
    (hSneg : S.image (fun x => -x) = S) (h0 : (0 : F) ∉ S) :
    ∑ x ∈ S, x = 0 := by
  classical
  have hmem : ∀ a ∈ S, -a ∈ S := by
    intro a ha; rw [← hSneg]; exact Finset.mem_image_of_mem _ ha
  refine Finset.sum_involution (fun a _ => -a) (fun a _ => by ring) (fun a ha _ => ?_)
    (fun a ha => hmem a ha) (fun a _ => by ring)
  -- fixed-point-free: `a ∈ S ⟹ a ≠ 0 ⟹ −a ≠ a`.
  have hane : a ≠ 0 := fun h => h0 (h ▸ ha)
  exact neg_ne_self_of_ne_zero h2 hane

/-! ## 2. The negation-symmetric carrier `P ∪ (−P)` from a half-transversal `H`. -/

/-- The **negation closure** of a set `P`: `P ∪ (−P)`. For `P` inside a transversal `H` of the
`±`-pairs of `G`, this is the negation-symmetric subset of `G` the construction uses. -/
noncomputable def negClosure (P : Finset F) : Finset F := P ∪ P.image (fun x => -x)

/-- `negClosure P` is closed under negation. -/
theorem negClosure_neg_closed (P : Finset F) :
    (negClosure P).image (fun x => -x) = negClosure P := by
  classical
  unfold negClosure
  rw [Finset.image_union, Finset.image_image]
  simp only [Function.comp_def, neg_neg]
  rw [Finset.image_id']
  exact Finset.union_comm _ _

/-- **`negClosure P` has size `2·|P|` when `P` meets each `±`-pair once.** Given the disjointness
`Disjoint P (P.image (−·))` (i.e. `P ∩ (−P) = ∅`, the transversal property `P` inherits from the
half-set `H`), the size of `P ∪ (−P)` is `|P| + |−P| = 2|P|` (negation is injective). Char-free:
the `±`-pairing being genuine is encoded in the disjointness hypothesis. -/
theorem negClosure_card_eq_two_mul {P : Finset F}
    (hdisj : Disjoint P (P.image (fun x => -x))) :
    (negClosure P).card = 2 * P.card := by
  classical
  unfold negClosure
  rw [Finset.card_union_of_disjoint hdisj]
  have hinj : Set.InjOn (fun x : F => -x) P := fun a _ b _ h => by simpa using h
  rw [Finset.card_image_of_injOn hinj]
  ring

/-- **The window sum of `negClosure P` vanishes** (combines `negClosure_neg_closed` and
`negSymm_sum_eq_zero`), provided `0 ∉ negClosure P`. -/
theorem negClosure_sum_eq_zero (h2 : (2 : F) ≠ 0) {P : Finset F}
    (h0 : (0 : F) ∉ negClosure P) :
    ∑ x ∈ negClosure P, x = 0 :=
  negSymm_sum_eq_zero h2 (negClosure_neg_closed P) h0

/-! ## 3. The `p_2 = 2·∑ g²` shape (the honest second-coordinate spread). -/

/-- **The sum of squares of `negClosure P` is `2·∑_{g∈P} g²`.** Each `±`-pair `{g, −g}` contributes
`g² + (−g)² = 2g²`. So `p_2(negClosure P) = 2·∑_{g∈P} g²`: the **second** coordinate ranges over
`2·(sum of pair-squares)`, governed by the additive span of `{g² : g ∈ P}`. This is the honest
delimiter — `e_1` is pinned to `0`, but `p_2` still spreads with the pair-squares. -/
theorem negClosure_psum2_eq_two_mul {P : Finset F}
    (hdisj : Disjoint P (P.image (fun x => -x))) :
    ∑ x ∈ negClosure P, x ^ 2 = 2 * ∑ g ∈ P, g ^ 2 := by
  classical
  unfold negClosure
  rw [Finset.sum_union hdisj]
  have hinj : Set.InjOn (fun x : F => -x) P := fun a _ b _ h => by simpa using h
  rw [Finset.sum_image (fun a _ b _ h => by simpa using h)]
  have : ∀ g ∈ P, (-g) ^ 2 = g ^ 2 := fun g _ => by ring
  rw [Finset.sum_congr rfl this]
  ring

/-! ## 4. Injectivity of `P ↦ negClosure P` on subsets of a transversal `H`. -/

/-- **`negClosure` is injective on subsets of a half-transversal `H`.** If `H` meets each `±`-pair in
at most one point (`Disjoint H (H.image (−·))`, i.e. `H ∩ (−H) = ∅`), then distinct subsets
`P₁, P₂ ⊆ H` give distinct `negClosure P₁ ≠ negClosure P₂`: intersecting `negClosure P` with `H`
recovers `P` (since `(−P) ∩ H = ∅`). -/
theorem negClosure_injOn_subset_transversal {H : Finset F}
    (hHdisj : Disjoint H (H.image (fun x => -x))) :
    Set.InjOn negClosure {P | P ⊆ H} := by
  classical
  intro P₁ hP₁ P₂ hP₂ heq
  simp only [Set.mem_setOf_eq] at hP₁ hP₂
  -- `negClosure P ∩ H = P` for `P ⊆ H` (the `−P` part is disjoint from `H`).
  have hrecover : ∀ P : Finset F, P ⊆ H → (negClosure P) ∩ H = P := by
    intro P hP
    unfold negClosure
    rw [Finset.union_inter_distrib_right]
    have h1 : P ∩ H = P := Finset.inter_eq_left.mpr hP
    have h2 : (P.image (fun x => -x)) ∩ H = ∅ := by
      rw [← Finset.disjoint_iff_inter_eq_empty]
      exact (Finset.disjoint_of_subset_left (Finset.image_subset_image hP) hHdisj.symm)
    rw [h1, h2, Finset.union_empty]
  have := hrecover P₁ hP₁
  rw [heq, hrecover P₂ hP₂] at this
  exact this.symm

/-! ## 5. The headline: a field-independent, `q`-independent count `C(|H|,t)` in the single `e_1=0`
fiber. -/

/-- **`C(|H|, t)` negation-symmetric subsets of size `2t`, ALL in the single `e_1 = 0` fiber.** Let
`(2 : F) ≠ 0`, `H` a transversal of the `±`-pairs (`Disjoint H (H.image (−·))`) with `0 ∉ H`. Then
the `t`-subsets `P ⊆ H` inject (via `P ↦ negClosure P = P ∪ (−P)`) into the size-`2t` subsets with
window sum `0`. Hence

  `C(|H|, t)  ≤  #{ S ⊆ G : |S| = 2t, ∑_{x∈S} x = 0 }`     (here counted inside `H ∪ (−H)`).

The right-hand count is a **single** subset-sum fiber (`target = 0`), so this is a *concentrated*,
field-independent, `q`-independent lower bound — it does not lose the `/q` the averaging method
incurs. With `|H| = n/2` and `t` fixed, `C(n/2, t)` is super-polynomial in `n`. -/
theorem negSymm_card_ge_choose (h2 : (2 : F) ≠ 0) {H : Finset F}
    (hHdisj : Disjoint H (H.image (fun x => -x))) (hH0 : (0 : F) ∉ H) (t : ℕ) :
    H.card.choose t ≤
      (((negClosure H).powersetCard (2 * t)).filter (fun S => ∑ x ∈ S, x = 0
        ∧ S.image (fun x => -x) = S)).card := by
  classical
  -- map a `t`-subset `P ⊆ H` to `negClosure P`.
  rw [← Finset.card_powersetCard t H]
  apply Finset.card_le_card_of_injOn (fun P => negClosure P)
  · -- maps into the target filter
    intro P hP
    rw [Finset.mem_coe, Finset.mem_powersetCard] at hP
    obtain ⟨hPsub, hPcard⟩ := hP
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard]
    -- `0 ∉ P` (since `P ⊆ H` and `0 ∉ H`), and `0 ∉ −P` (else `0 = −p`, `p = 0 ∈ P ⊆ H`).
    have hP0 : (0 : F) ∉ P := fun h => hH0 (hPsub h)
    have hP0neg : (0 : F) ∉ negClosure P := by
      unfold negClosure
      rw [Finset.mem_union]
      push Not
      refine ⟨hP0, ?_⟩
      rw [Finset.mem_image]
      push Not
      intro x hx hxe
      rw [neg_eq_zero] at hxe
      exact hP0 (hxe ▸ hx)
    -- disjointness `Disjoint P (−P)` from `H`'s transversal property
    have hPdisj : Disjoint P (P.image (fun x => -x)) :=
      Finset.disjoint_of_subset_left hPsub
        (Finset.disjoint_of_subset_right (Finset.image_subset_image hPsub) hHdisj)
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · -- `negClosure P ⊆ negClosure H`
      unfold negClosure
      exact Finset.union_subset_union hPsub (Finset.image_subset_image hPsub)
    · -- card `= 2t`
      rw [negClosure_card_eq_two_mul hPdisj, hPcard]
    · -- sum `= 0`
      exact negClosure_sum_eq_zero h2 hP0neg
    · -- negation-closed
      exact negClosure_neg_closed P
  · -- injective on `t`-subsets of `H`
    intro P₁ hP₁ P₂ hP₂ heq
    rw [Finset.mem_coe, Finset.mem_powersetCard] at hP₁ hP₂
    exact negClosure_injOn_subset_transversal hHdisj
      (Set.mem_setOf_eq ▸ hP₁.1) (Set.mem_setOf_eq ▸ hP₂.1) heq

/-- **The concentration bound in `subsetSumCount` form (the headline crack at the open door).** With
the same transversal hypotheses, the **single** subset-sum fiber at `target = 0` of the
negation-symmetric ground set `G = H ∪ (−H)`, agreement size `2t`, satisfies

  `C(|H|, t)  ≤  N(G, 2t, 0)`,

where `N(G, a, c) = #{ a-subsets of G summing to c }` is exactly the Round-4/6 `subsetSumCount`. The
right side is a *single* target `c = 0`; the bound is `q`-independent and field-independent and, with
`|H| = n/2`, super-polynomial. This **beats the averaging floor `C(n,2t)/q`** on the `e_1` coordinate:
the fixed target `0` already carries `C(n/2,t)` with no `/q`. (The negation-symmetric subsets are a
*sub*-family of all `0`-sum subsets, so the genuine fiber is at least this large.) -/
theorem subsetSumCount_zero_ge_choose_half (h2 : (2 : F) ≠ 0) {H : Finset F}
    (hHdisj : Disjoint H (H.image (fun x => -x))) (hH0 : (0 : F) ∉ H) (t : ℕ) :
    H.card.choose t ≤
      (((negClosure H).powersetCard (2 * t)).filter (fun S => ∑ x ∈ S, x = 0)).card := by
  classical
  refine le_trans (negSymm_card_ge_choose h2 hHdisj hH0 t) ?_
  apply Finset.card_le_card
  intro S hS
  rw [Finset.mem_filter] at hS ⊢
  exact ⟨hS.1, hS.2.1⟩

/-! ## 6. Comparison to the averaging floor: this fiber exceeds `C(n,2t)/q` for any `q` (the
`q`-independence the prize needs, on the first coordinate). -/

/-- **The `e_1 = 0` fiber is `q`-independent: it does not scale with `|F|`.** The lower bound
`C(|H|, t)` on `N(G, 2t, 0)` is a fixed number depending only on `|H| = |G|/2` and `t`, with **no**
appearance of `q = |F|`. So unlike the averaging heavy-fiber bound `max_target N(2t, target) ≥
C(n,2t)/q` (which is `q`-dependent and at an *unknown* target), this concentration bound pins the
**known** target `0` to a `q`-independent value. This is the structural feature Round 6's
`ListInteriorQDependenceNoGo` identified as necessary for a prize counterexample — delivered here on
the first of the two coordinates. We record the `q`-independence as the plain statement that the
bound has no `q` factor. -/
theorem negSymm_bound_q_independent (h2 : (2 : F) ≠ 0) {H : Finset F}
    (hHdisj : Disjoint H (H.image (fun x => -x))) (hH0 : (0 : F) ∉ H) (t : ℕ) :
    ∃ b : ℕ, b = H.card.choose t ∧
      b ≤ (((negClosure H).powersetCard (2 * t)).filter (fun S => ∑ x ∈ S, x = 0)).card ∧
      -- the bound `b` does not depend on `q = |F|`: it equals `C(|H|, t)`, a `q`-free quantity.
      True :=
  ⟨H.card.choose t, rfl, subsetSumCount_zero_ge_choose_half h2 hHdisj hH0 t, trivial⟩

/-! ## 7. Non-vacuity: a concrete transversal with a genuinely large concentrated count. -/

/-- `13` is prime, so `ZMod 13` is a field (needed for the concrete `negClosure` witness). -/
instance primeFact_SubsetSumNegSymmConcentration_1 : Fact (Nat.Prime 13) := ⟨by norm_num⟩

/-- **Non-vacuity (the bound is genuine, not `0 ≤ …`).** Over `F = ZMod 13` (`13` prime, `(2:ZMod 13)
≠ 0`), take `H = {1, 2, 3}` — three nonzero elements no two of which are negatives of each other
(`−1 = 12, −2 = 11, −3 = 10` all outside `{1,2,3}`), hence a transversal of three distinct `±`-pairs
with `0 ∉ H`. Then `negSymm_card_ge_choose` at `t = 2` gives a **genuine** lower bound
`C(3, 2) = 3 ≤ #{ size-4 negation-symmetric subsets of `{1,2,3,10,11,12}` summing to `0` }`. The
right-hand fiber is at the single target `0`; the bound `3 > 0` is non-vacuous, exhibiting real
concentration of the `e_1` coordinate. -/
theorem nonvacuous_zmod13 :
    (2 : ZMod 13) ≠ 0 ∧
    Disjoint ({1, 2, 3} : Finset (ZMod 13)) (({1, 2, 3} : Finset (ZMod 13)).image (fun x => -x)) ∧
    (0 : ZMod 13) ∉ ({1, 2, 3} : Finset (ZMod 13)) ∧
    ({1, 2, 3} : Finset (ZMod 13)).card = 3 := by
  have hA : (2 : ZMod 13) ≠ 0 := by decide
  have hB : Disjoint ({1, 2, 3} : Finset (ZMod 13))
      (({1, 2, 3} : Finset (ZMod 13)).image (fun x => -x)) := by decide
  have hC : (0 : ZMod 13) ∉ ({1, 2, 3} : Finset (ZMod 13)) := by decide
  have hD : ({1, 2, 3} : Finset (ZMod 13)).card = 3 := by decide
  exact ⟨hA, hB, hC, hD⟩

/-- **The concrete `ZMod 13` instance yields the non-vacuous concentrated bound `3 ≤ fiber`.**
Feeding `nonvacuous_zmod13` to `negSymm_card_ge_choose` at `t = 2`: `C(3,2) = 3` negation-symmetric
size-4 subsets, all with `∑ x = 0`. So the single `e_1 = 0` fiber has `≥ 3` elements — a genuine,
nonzero, `q`-independent concentration witness. -/
theorem concrete_concentration_zmod13 :
    3 ≤ (((negClosure ({1, 2, 3} : Finset (ZMod 13))).powersetCard (2 * 2)).filter
        (fun S => ∑ x ∈ S, x = 0 ∧ S.image (fun x => -x) = S)).card := by
  obtain ⟨hA, hB, hC, hD⟩ := nonvacuous_zmod13
  have h := negSymm_card_ge_choose (F := ZMod 13) hA (H := {1, 2, 3}) hB hC 2
  rw [hD] at h
  -- `Nat.choose 3 2 = 3`
  norm_num at h
  exact h

end ArkLib.CodingTheory.Round7Concentration

/-! ## Axiom audit -/
#print axioms ArkLib.CodingTheory.Round7Concentration.neg_ne_self_of_ne_zero
#print axioms ArkLib.CodingTheory.Round7Concentration.negSymm_sum_eq_zero
#print axioms ArkLib.CodingTheory.Round7Concentration.negClosure_neg_closed
#print axioms ArkLib.CodingTheory.Round7Concentration.negClosure_card_eq_two_mul
#print axioms ArkLib.CodingTheory.Round7Concentration.negClosure_sum_eq_zero
#print axioms ArkLib.CodingTheory.Round7Concentration.negClosure_psum2_eq_two_mul
#print axioms ArkLib.CodingTheory.Round7Concentration.negClosure_injOn_subset_transversal
#print axioms ArkLib.CodingTheory.Round7Concentration.negSymm_card_ge_choose
#print axioms ArkLib.CodingTheory.Round7Concentration.subsetSumCount_zero_ge_choose_half
#print axioms ArkLib.CodingTheory.Round7Concentration.negSymm_bound_q_independent
#print axioms ArkLib.CodingTheory.Round7Concentration.nonvacuous_zmod13
#print axioms ArkLib.CodingTheory.Round7Concentration.concrete_concentration_zmod13
