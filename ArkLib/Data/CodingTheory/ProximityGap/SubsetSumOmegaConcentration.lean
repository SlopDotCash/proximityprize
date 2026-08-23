/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Round 8 (Issue #232, ABF26) — `⟨ω⟩`-symmetric subsets concentrate BOTH `∑x` and `∑x²` at `0`:
# the order-4 root-of-unity construction that resolves Round 7's open `p₂`-spread residual.

Round 7 (`SubsetSumNegSymmConcentration.lean`, `negSymm_card_ge_choose`) cracked the concentration
"open door" on the **first** coordinate: a *negation*-symmetric subset `S = P ∪ (−P)` (closure under
the order-`2` element `−1`) forces `∑_{x∈S} x = 0` at a single target, `q`-independently, with a
super-polynomial count `C(n/2, t)`. Round 7's honest residual: the **second** coordinate
`∑_{x∈S} x² = 2∑_{g∈P} g²` *spreads* — "whether the pair-squares `{g²}` concentrate is open".

## What this round contributes — close the door on BOTH coordinates at once

The Round-7 residual dissolves one level up the root-of-unity tower. The pair-squares `{g² : g∈G}`
are exactly the order-`n/2` subgroup `G²`, *also* negation-closed — so the *same* trick applies to the
squares. Packaged multiplicatively, this is just **closure under the order-4 element** `ω` (`ω² = −1`,
so `ω⁴ = 1`, `⟨ω⟩ = {1, ω, −1, −ω}`). The clean engine:

* `omega_closed_psum_eq_zero` — **the engine.** If `S` is closed under `x ↦ ω·x`
  (`S.image (ω·) = S`), `ω ≠ 0`, and `ω^j ≠ 1`, then `∑_{x∈S} x^j = 0`. Proof: reindex
  `∑_S x^j = ∑_S (ω x)^j = ω^j ∑_S x^j`, so `(1 − ω^j)∑ = 0`, and `ω^j ≠ 1` kills the sum. This is a
  *single* uniform statement that vanishes **every** power sum `p_j` with `ω^j ≠ 1`.

* For an order-4 `ω` (`ω² = −1`): `ω¹ = ω ≠ 1` and `ω² = −1 ≠ 1` (char `≠ 2`), so the engine gives
  `∑_{x∈S} x = 0` **and** `∑_{x∈S} x² = 0` for *every* `⟨ω⟩`-closed `S`
  (`omega4Closure_sum_eq_zero`, `omega4Closure_sumsq_eq_zero`). Hence `e₁(S) = 0` and
  `e₂(S) = (e₁² − p₂)/2 = 0`: **both** symmetric functions are pinned to the single target `(0,0)` —
  exactly the `N2(·; 0, 0)` fiber Round 7 could only pin on its first coordinate.

* `omega4Closure` (`P ∪ ωP ∪ ω²P ∪ ω³P`) is the `⟨ω⟩`-orbit closure of `P`; `omega4Closure_image_eq`
  proves it is `ω`-closed, feeding the engine.

* `omega4_card_eq` / `omega4Closure_injOn` / `card_ge_choose_two_zero` — under a **free-action**
  hypothesis on a transversal `T` of the `⟨ω⟩`-orbits (the four translates `ω^i·T` are independent),
  the `s`-subsets `U ⊆ T` inject (via `U ↦ omega4Closure ω U`) into the size-`4s` subsets with
  `∑x = ∑x² = 0`. Hence `C(|T|, s) ≤ #{ S : |S| = 4s, ∑x = 0 ∧ ∑x² = 0 }`. With `|T| = n/4` this is a
  **`q`-independent, super-polynomial** lower bound on the *single* `(0,0)` fiber of the
  `(sum, sum-of-squares)` count — Round 7's residual coordinate, now concentrated.

## Honest scope — what this does and does NOT do (the depth-collapse wall)

* It **IS** a `sorry`-free, axiom-clean, `q`-independent super-polynomial lower bound on the *single*
  `(∑x, ∑x²) = (0,0)` fiber — closing the Round-7 residual on BOTH coordinates simultaneously, for the
  `t = 2` joint count `N2`.
* It generalizes (the engine is stated for all `j`): closure under a primitive `2^r`-th root of unity
  `ω_r` vanishes every power sum `p_j` with `2^r ∤ j`, hence `p_1, …, p_{2^r−1} = 0`, hence
  `e_1, …, e_{2^r−1} = 0`. So killing the first `t` symmetric functions needs `r = ⌈log₂(t+1)⌉`.
* It is **NOT** a prize counterexample, and this file is honest about *why* (the genuine wall): the
  `⟨ω_r⟩`-orbits have size `2^r`, so a transversal has only `n/2^r` elements and the concentrated
  count is `C(n/2^r, s)`. Reaching the **deep interior** (agreement `≈ √(kn)`, near the Johnson radius)
  forces `2^r ≈ t ≈ √(kn) − k`, i.e. `r ≈ m`, which **collapses** the transversal to `n/2^r = O(1)`
  elements and the count to a *constant*. The root-of-unity depth needed to pin `t` symmetric
  functions eats the subgroup geometrically. This is the precise, structural reason the construction
  concentrates near *capacity* (constant `t`) but cannot pin `δ*` in the deep interior — and it
  matches ABF26's "no known technique past Johnson for explicit RS".

All headline results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Tracking issue #232. Builds on Round 7 `SubsetSumNegSymmConcentration.lean`.
-/

open Finset BigOperators

namespace ArkLib.CodingTheory.Round8OmegaConcentration

variable {F : Type*} [Field F] [DecidableEq F]

/-! ## 1. The engine: a `⟨ω⟩`-closed set vanishes every power sum `p_j` with `ω^j ≠ 1`. -/

/-- **The engine.** If `S` is closed under multiplication by `ω` (`S.image (ω·) = S`), `ω ≠ 0`, and
`ω^j ≠ 1`, then the `j`-th power sum vanishes: `∑_{x∈S} x^j = 0`.

Proof: multiplication by `ω` is a bijection of `S` (injective since `ω ≠ 0`, onto `S` by `hS`), so
reindexing the sum gives `∑_{x∈S} x^j = ∑_{x∈S} (ω x)^j = ω^j ∑_{x∈S} x^j`. Hence
`(1 − ω^j)·∑ = 0`, and `1 − ω^j ≠ 0` (as `ω^j ≠ 1`) forces `∑ = 0`.

This single statement kills **every** power sum whose exponent is not annihilated by `ω`. For `ω` a
primitive `N`-th root of unity it vanishes `p_j` for all `j` with `N ∤ j`. -/
theorem omega_closed_psum_eq_zero {ω : F} {S : Finset F} {j : ℕ}
    (hω0 : ω ≠ 0) (hωj : ω ^ j ≠ 1) (hS : S.image (fun x => ω * x) = S) :
    ∑ x ∈ S, x ^ j = 0 := by
  classical
  have key : ∑ x ∈ S, x ^ j = ω ^ j * ∑ x ∈ S, x ^ j := by
    conv_lhs => rw [← hS]
    rw [Finset.sum_image (fun a _ b _ h => mul_left_cancel₀ hω0 h), Finset.mul_sum]
    exact Finset.sum_congr rfl (fun x _ => by rw [mul_pow])
  have hz : (1 - ω ^ j) * (∑ x ∈ S, x ^ j) = 0 := by linear_combination key
  rcases mul_eq_zero.mp hz with h | h
  · exact absurd (sub_eq_zero.mp h).symm hωj
  · exact h

/-! ## 2. The order-4 root of unity and its basic arithmetic (`ω² = −1`). -/

variable {ω : F}
variable {T : Finset F}

omit [DecidableEq F] in
/-- From `ω² = −1` and char `≠ 2`: `ω ≠ 0`. -/
theorem omega_ne_zero (h2 : (2 : F) ≠ 0) (hω2 : ω ^ 2 = -1) : ω ≠ 0 := by
  rintro rfl
  apply h2
  rw [zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hω2
  linear_combination 2 * hω2

omit [DecidableEq F] in
/-- From `ω² = −1`: `ω⁴ = 1`. -/
theorem omega_pow_four (hω2 : ω ^ 2 = -1) : ω ^ 4 = 1 := by
  have h : ω ^ 4 = (ω ^ 2) ^ 2 := by ring
  rw [h, hω2]; ring

omit [DecidableEq F] in
/-- From `ω² = −1` and char `≠ 2`: `ω ≠ 1` (else `1 = ω² = −1`, so `2 = 0`). -/
theorem omega_ne_one (h2 : (2 : F) ≠ 0) (hω2 : ω ^ 2 = -1) : ω ≠ 1 := by
  rintro rfl
  apply h2
  rw [one_pow] at hω2
  linear_combination hω2

omit [DecidableEq F] in
/-- From `ω² = −1` and char `≠ 2`: `ω² ≠ 1` (else `−1 = 1`, so `2 = 0`). -/
theorem omega_sq_ne_one (h2 : (2 : F) ≠ 0) (hω2 : ω ^ 2 = -1) : ω ^ 2 ≠ 1 := by
  rw [hω2]; intro h; apply h2; linear_combination -h

/-! ## 3. The `⟨ω⟩`-orbit closure and its `ω`-closedness. -/

/-- The **`⟨ω⟩`-orbit closure** of `P`: `P ∪ ωP ∪ ω²P ∪ ω³P`, the union of the four `⟨ω⟩`-translates.
For `P` inside a transversal `T` of the `⟨ω⟩`-orbits of a smooth subgroup `G`, this is the
`⟨ω⟩`-symmetric subset of `G` the construction uses. -/
noncomputable def omega4Closure (ω : F) (P : Finset F) : Finset F :=
  P ∪ P.image (fun x => ω * x) ∪ P.image (fun x => ω ^ 2 * x) ∪ P.image (fun x => ω ^ 3 * x)

/-- The image of `omega4Closure ω P` under `(ω·)` is **contained in** `omega4Closure ω P`: multiplying
each translate by `ω` lands in the next (the `ω³P` translate wraps to `ω⁴P = P` via `ω⁴ = 1`). -/
theorem omega4Closure_image_subset (hω4 : ω ^ 4 = 1) (P : Finset F) :
    (omega4Closure ω P).image (fun x => ω * x) ⊆ omega4Closure ω P := by
  classical
  intro a ha
  rw [Finset.mem_image] at ha
  obtain ⟨b, hb, rfl⟩ := ha
  unfold omega4Closure at hb ⊢
  simp only [Finset.mem_union, Finset.mem_image] at hb ⊢
  have hmul : ω * ω ^ 3 = 1 := by
    have h : ω * ω ^ 3 = ω ^ 4 := by ring
    rw [h, hω4]
  rcases hb with ((hbP | ⟨c, hc, rfl⟩) | ⟨c, hc, rfl⟩) | ⟨c, hc, rfl⟩
  · exact Or.inl (Or.inl (Or.inr ⟨b, hbP, rfl⟩))
  · exact Or.inl (Or.inr ⟨c, hc, by ring⟩)
  · exact Or.inr ⟨c, hc, by ring⟩
  · refine Or.inl (Or.inl (Or.inl ?_))
    have hcc : ω * (ω ^ 3 * c) = c := by rw [← mul_assoc, hmul, one_mul]
    rw [hcc]; exact hc

/-- `omega4Closure ω P` is closed under multiplication by `ω` (using `ω⁴ = 1`, `ω ≠ 0`). Proof: the
image under `(ω·)` is a subset (`omega4Closure_image_subset`) of the same cardinality (`(ω·)` is
injective), hence equal. -/
theorem omega4Closure_image_eq (hω4 : ω ^ 4 = 1) (hω0 : ω ≠ 0) (P : Finset F) :
    (omega4Closure ω P).image (fun x => ω * x) = omega4Closure ω P := by
  classical
  have hinj : Function.Injective (fun x : F => ω * x) := fun a b h => mul_left_cancel₀ hω0 h
  exact Finset.eq_of_subset_of_card_le (omega4Closure_image_subset hω4 P)
    (le_of_eq (Finset.card_image_of_injective _ hinj).symm)

/-! ## 4. The headline coordinate vanishings: `∑x = 0` and `∑x² = 0` for every `⟨ω⟩`-closed set. -/

/-- **The first coordinate vanishes (`e₁ = 0`):** `∑_{x ∈ omega4Closure ω P} x = 0`. -/
theorem omega4Closure_sum_eq_zero (h2 : (2 : F) ≠ 0) (hω2 : ω ^ 2 = -1) (P : Finset F) :
    ∑ x ∈ omega4Closure ω P, x = 0 := by
  have h := omega_closed_psum_eq_zero (j := 1) (omega_ne_zero h2 hω2)
    (by rw [pow_one]; exact omega_ne_one h2 hω2)
    (omega4Closure_image_eq (omega_pow_four hω2) (omega_ne_zero h2 hω2) P)
  simpa using h

/-- **The second coordinate vanishes (`p₂ = 0`, hence `e₂ = 0`):**
`∑_{x ∈ omega4Closure ω P} x² = 0`. This is the Round-7 residual coordinate, now concentrated: the
order-4 closure forces the sum of squares to the single target `0`, with no `/q` loss. -/
theorem omega4Closure_sumsq_eq_zero (h2 : (2 : F) ≠ 0) (hω2 : ω ^ 2 = -1) (P : Finset F) :
    ∑ x ∈ omega4Closure ω P, x ^ 2 = 0 :=
  omega_closed_psum_eq_zero (j := 2) (omega_ne_zero h2 hω2) (omega_sq_ne_one h2 hω2)
    (omega4Closure_image_eq (omega_pow_four hω2) (omega_ne_zero h2 hω2) P)

/-! ## 5. The free-action hypothesis, the cardinality `4|T|`, and injectivity. -/

/-- **The free-action hypothesis on a transversal `T`.** The four `⟨ω⟩`-translates
`T, ωT, ω²T, ω³T` are pairwise disjoint. For the real smooth subgroup `G` with `T` a transversal of
the `⟨ω⟩`-orbits this is freeness of the `⟨ω⟩` action; we take it as an explicit, field-agnostic,
`Decidable` hypothesis (checkable by `decide` on concrete fields). -/
def OmegaFree (ω : F) (T : Finset F) : Prop :=
  Disjoint T (T.image (fun x => ω * x)) ∧
  Disjoint T (T.image (fun x => ω ^ 2 * x)) ∧
  Disjoint T (T.image (fun x => ω ^ 3 * x)) ∧
  Disjoint (T.image (fun x => ω * x)) (T.image (fun x => ω ^ 2 * x)) ∧
  Disjoint (T.image (fun x => ω * x)) (T.image (fun x => ω ^ 3 * x)) ∧
  Disjoint (T.image (fun x => ω ^ 2 * x)) (T.image (fun x => ω ^ 3 * x))

/-- Under `OmegaFree`, `omega4Closure ω P` has card `4|P|` for `P ⊆ T` (four disjoint translates,
each of card `|P|` since `(ω^i·)` is injective). -/
theorem omega4_card_eq (hω0 : ω ≠ 0) (hfree : OmegaFree ω T) {P : Finset F} (hP : P ⊆ T) :
    (omega4Closure ω P).card = 4 * P.card := by
  classical
  obtain ⟨d01, d02, d03, d12, d13, d23⟩ := hfree
  have imgP : ∀ {a b : F}, Disjoint (T.image (fun x => a * x)) (T.image (fun x => b * x)) →
      Disjoint (P.image (fun x => a * x)) (P.image (fun x => b * x)) := fun h =>
    Finset.disjoint_of_subset_left (Finset.image_subset_image hP)
      (Finset.disjoint_of_subset_right (Finset.image_subset_image hP) h)
  have leftP : ∀ {b : F}, Disjoint T (T.image (fun x => b * x)) →
      Disjoint P (P.image (fun x => b * x)) := fun h =>
    Finset.disjoint_of_subset_left hP
      (Finset.disjoint_of_subset_right (Finset.image_subset_image hP) h)
  have r01 : Disjoint P (P.image (fun x => ω * x)) := leftP d01
  have r02 : Disjoint P (P.image (fun x => ω ^ 2 * x)) := leftP d02
  have r03 : Disjoint P (P.image (fun x => ω ^ 3 * x)) := leftP d03
  have r12 := imgP d12
  have r13 := imgP d13
  have r23 := imgP d23
  have inj1 : (P.image (fun x => ω * x)).card = P.card :=
    Finset.card_image_of_injOn (fun a _ b _ h => mul_left_cancel₀ hω0 h)
  have inj2 : (P.image (fun x => ω ^ 2 * x)).card = P.card :=
    Finset.card_image_of_injOn (fun a _ b _ h => mul_left_cancel₀ (pow_ne_zero 2 hω0) h)
  have inj3 : (P.image (fun x => ω ^ 3 * x)).card = P.card :=
    Finset.card_image_of_injOn (fun a _ b _ h => mul_left_cancel₀ (pow_ne_zero 3 hω0) h)
  have hMid : Disjoint (P ∪ P.image (fun x => ω * x)) (P.image (fun x => ω ^ 2 * x)) := by
    rw [Finset.disjoint_union_left]; exact ⟨r02, r12⟩
  have hOuter : Disjoint ((P ∪ P.image (fun x => ω * x)) ∪ P.image (fun x => ω ^ 2 * x))
      (P.image (fun x => ω ^ 3 * x)) := by
    rw [Finset.disjoint_union_left, Finset.disjoint_union_left]; exact ⟨⟨r03, r13⟩, r23⟩
  unfold omega4Closure
  rw [Finset.card_union_of_disjoint hOuter, Finset.card_union_of_disjoint hMid,
      Finset.card_union_of_disjoint r01, inj1, inj2, inj3]
  ring

/-- Under `OmegaFree`, intersecting `omega4Closure ω P` with the transversal `T` recovers `P`
(the `ωP, ω²P, ω³P` translates are disjoint from `T`). Hence `omega4Closure ω ·` is injective on
subsets of `T`. -/
theorem omega4Closure_injOn (hfree : OmegaFree ω T) :
    Set.InjOn (omega4Closure ω) {P | P ⊆ T} := by
  classical
  obtain ⟨d01, d02, d03, _, _, _⟩ := hfree
  have hrecover : ∀ P : Finset F, P ⊆ T → (omega4Closure ω P) ∩ T = P := by
    intro P hP
    unfold omega4Closure
    rw [Finset.union_inter_distrib_right, Finset.union_inter_distrib_right,
        Finset.union_inter_distrib_right]
    have hPT : P ∩ T = P := Finset.inter_eq_left.mpr hP
    have hA1 : (P.image (fun x => ω * x)) ∩ T = ∅ := by
      rw [← Finset.disjoint_iff_inter_eq_empty]
      exact Finset.disjoint_of_subset_left (Finset.image_subset_image hP) d01.symm
    have hA2 : (P.image (fun x => ω ^ 2 * x)) ∩ T = ∅ := by
      rw [← Finset.disjoint_iff_inter_eq_empty]
      exact Finset.disjoint_of_subset_left (Finset.image_subset_image hP) d02.symm
    have hA3 : (P.image (fun x => ω ^ 3 * x)) ∩ T = ∅ := by
      rw [← Finset.disjoint_iff_inter_eq_empty]
      exact Finset.disjoint_of_subset_left (Finset.image_subset_image hP) d03.symm
    rw [hPT, hA1, hA2, hA3, Finset.union_empty, Finset.union_empty, Finset.union_empty]
  intro P₁ hP₁ P₂ hP₂ heq
  simp only [Set.mem_setOf_eq] at hP₁ hP₂
  have e₁ := hrecover P₁ hP₁
  rw [heq, hrecover P₂ hP₂] at e₁
  exact e₁.symm

/-! ## 6. The headline count: `C(|T|, s) ≤ #{ size-4s subsets with ∑x = 0 ∧ ∑x² = 0 }`. -/

/-- **The `t = 2` concentration headline.** Let `(2 : F) ≠ 0`, `ω² = −1`, and `T` a transversal of the
`⟨ω⟩`-orbits satisfying the free-action hypothesis `OmegaFree ω T`. Then the `s`-subsets `U ⊆ T`
inject (via `U ↦ omega4Closure ω U = U ∪ ωU ∪ ω²U ∪ ω³U`) into the size-`4s` subsets of
`omega4Closure ω T` with **both** `∑x = 0` and `∑x² = 0`. Hence

  `C(|T|, s)  ≤  #{ S ⊆ G : |S| = 4s, ∑_{x∈S} x = 0 ∧ ∑_{x∈S} x² = 0 }`.

The right-hand side is the **single** `(∑x, ∑x²) = (0, 0)` fiber of the Round-6/7 `(sum,
sum-of-squares)` count `N2`. With `|T| = n/4` the bound `C(n/4, s)` is **`q`-independent** and
**super-polynomial** in `n` — Round 7's residual coordinate `p₂`, now concentrated at one target with
no `/q` loss. -/
theorem card_ge_choose_two_zero (h2 : (2 : F) ≠ 0) (hω2 : ω ^ 2 = -1)
    (hfree : OmegaFree ω T) (s : ℕ) :
    T.card.choose s ≤
      (((omega4Closure ω T).powersetCard (4 * s)).filter
        (fun S => (∑ x ∈ S, x) = 0 ∧ (∑ x ∈ S, x ^ 2) = 0)).card := by
  classical
  rw [← Finset.card_powersetCard s T]
  apply Finset.card_le_card_of_injOn (fun U => omega4Closure ω U)
  · intro U hU
    rw [Finset.mem_coe, Finset.mem_powersetCard] at hU
    obtain ⟨hUsub, hUcard⟩ := hU
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · unfold omega4Closure
      exact Finset.union_subset_union
        (Finset.union_subset_union
          (Finset.union_subset_union hUsub (Finset.image_subset_image hUsub))
          (Finset.image_subset_image hUsub))
        (Finset.image_subset_image hUsub)
    · rw [omega4_card_eq (omega_ne_zero h2 hω2) hfree hUsub, hUcard]
    · exact omega4Closure_sum_eq_zero h2 hω2 U
    · exact omega4Closure_sumsq_eq_zero h2 hω2 U
  · intro U₁ hU₁ U₂ hU₂ heq
    rw [Finset.mem_coe, Finset.mem_powersetCard] at hU₁ hU₂
    exact omega4Closure_injOn hfree (Set.mem_setOf_eq ▸ hU₁.1) (Set.mem_setOf_eq ▸ hU₂.1) heq

/-! ## 7. Non-vacuity: a concrete `⟨ω⟩`-closed set over `ZMod 5` with `∑x = ∑x² = 0`. -/

/-- `5` is prime, so `ZMod 5` is a field. -/
instance primeFact_SubsetSumOmegaConcentration_1 : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- **Non-vacuity of the coordinate vanishings.** Over `F = ZMod 5`, `ω = 2` is an order-4 root of
unity (`2² = 4 = −1`). The orbit closure of `{1}` is `omega4Closure 2 {1} = {1, 2, 4, 3}` (`= ⟨2⟩`,
all nonzero residues), with `∑ x = 1+2+3+4 = 10 = 0` **and** `∑ x² = 1+4+4+1 = 10 = 0` in `ZMod 5`.
Both coordinate vanishings are genuine (not `0 = 0` artifacts). -/
theorem nonvacuous_zmod5 :
    (2 : ZMod 5) ^ 2 = -1 ∧
    (∑ x ∈ omega4Closure (2 : ZMod 5) {1}, x) = 0 ∧
    (∑ x ∈ omega4Closure (2 : ZMod 5) {1}, x ^ 2) = 0 := by
  refine ⟨by decide, ?_, ?_⟩
  · exact omega4Closure_sum_eq_zero (by decide) (by decide) {1}
  · exact omega4Closure_sumsq_eq_zero (by decide) (by decide) {1}

/-- **The concrete orbit closure is genuinely size 4** (`{1, 2, 3, 4} ⊆ ZMod 5`), so the
`∑ = 0 ∧ ∑² = 0` vanishings are over a real, non-degenerate `⟨ω⟩`-orbit, not a singleton. -/
theorem nonvacuous_zmod5_card :
    (omega4Closure (2 : ZMod 5) {1}).card = 4 := by decide

/-- **Non-vacuity of the count bound.** Over `ZMod 5`, `T = {1}` is a transversal of the single
`⟨2⟩`-orbit, `OmegaFree 2 {1}` holds, and `card_ge_choose_two_zero` at `s = 1` gives the genuine,
non-zero lower bound `C(1, 1) = 1 ≤ #{ size-4 subsets with ∑x = 0 ∧ ∑x² = 0 }`. -/
theorem nonvacuous_count_zmod5 :
    1 ≤ (((omega4Closure (2 : ZMod 5) {1}).powersetCard (4 * 1)).filter
        (fun S => (∑ x ∈ S, x) = 0 ∧ (∑ x ∈ S, x ^ 2) = 0)).card := by
  have hfree : OmegaFree (2 : ZMod 5) {1} := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide
  have h := card_ge_choose_two_zero (F := ZMod 5) (by decide) (by decide) hfree 1
  have hc : (({1} : Finset (ZMod 5)).card).choose 1 = 1 := by decide
  rw [hc] at h; exact h

/-! ## 8. General order-`d`: closure under a primitive `d`-th root of unity vanishes `p_1,…,p_{d−1}`
(the depth-collapse engine; over the smooth `2^k`-domain only `d = 2^r` is available). -/

/-- The **`⟨ω⟩`-coset closure** for a general order-`d` root: `⋃_{i<d} ω^i·P`, the union of the `d`
translates `P, ωP, …, ω^{d−1}P`. (For `d = 4` this is the orbit closure used in §§3–6.) -/
noncomputable def cosetClosure (ω : F) (d : ℕ) (P : Finset F) : Finset F :=
  (Finset.range d).biUnion (fun i => P.image (fun x => ω ^ i * x))

variable {d : ℕ}

/-- The image of `cosetClosure ω d P` under `(ω·)` is contained in it (translate `i` maps to
translate `i+1`, and translate `d−1` wraps to `0` via `ω^d = 1`). -/
theorem cosetClosure_image_subset (hωd : ω ^ d = 1) (P : Finset F) :
    (cosetClosure ω d P).image (fun x => ω * x) ⊆ cosetClosure ω d P := by
  classical
  intro a ha
  rw [Finset.mem_image] at ha
  obtain ⟨b, hb, rfl⟩ := ha
  rw [cosetClosure, Finset.mem_biUnion] at hb ⊢
  obtain ⟨i, hi, hbi⟩ := hb
  rw [Finset.mem_image] at hbi
  obtain ⟨p, hp, rfl⟩ := hbi
  rw [Finset.mem_range] at hi
  by_cases hlt : i + 1 < d
  · refine ⟨i + 1, Finset.mem_range.mpr hlt, ?_⟩
    rw [Finset.mem_image]
    exact ⟨p, hp, by rw [pow_succ]; ring⟩
  · have hid : i + 1 = d := by omega
    refine ⟨0, Finset.mem_range.mpr (by omega), ?_⟩
    rw [Finset.mem_image]
    refine ⟨p, hp, ?_⟩
    have hstep : ω * (ω ^ i * p) = ω ^ (i + 1) * p := by rw [pow_succ]; ring
    rw [pow_zero, one_mul, hstep, hid, hωd, one_mul]

/-- `cosetClosure ω d P` is closed under `(ω·)` (subset of equal card, `(ω·)` injective for `ω ≠ 0`). -/
theorem cosetClosure_image_eq (hωd : ω ^ d = 1) (hω0 : ω ≠ 0) (P : Finset F) :
    (cosetClosure ω d P).image (fun x => ω * x) = cosetClosure ω d P :=
  Finset.eq_of_subset_of_card_le (cosetClosure_image_subset hωd P)
    (le_of_eq (Finset.card_image_of_injective _ (fun _ _ h => mul_left_cancel₀ hω0 h)).symm)

/-- **The general depth-collapse engine.** For `ω` with `ω^d = 1`, `ω ≠ 0`, and any exponent `j` with
`ω^j ≠ 1`, the `j`-th power sum of `cosetClosure ω d P` vanishes. -/
theorem cosetClosure_psum_eq_zero (hωd : ω ^ d = 1) (hω0 : ω ≠ 0) {j : ℕ} (hωj : ω ^ j ≠ 1)
    (P : Finset F) : ∑ x ∈ cosetClosure ω d P, x ^ j = 0 :=
  omega_closed_psum_eq_zero hω0 hωj (cosetClosure_image_eq hωd hω0 P)

/-- **Closure under a primitive `d`-th root vanishes the first `d−1` power sums** `p_1, …, p_{d−1}`
(hence, in large-enough characteristic, `e_1 = … = e_{d−1} = 0` by Newton's identities): a
`cosetClosure` lands in the single joint fiber `(e_1,…,e_{d−1}) = 0`.

**The depth-collapse, now a theorem.** Over the smooth `2^k`-domain `G` the only available roots of
unity have 2-power order, so killing the first `t` symmetric functions forces `d = 2^r ≥ t+1`, orbits
of size `2^r`, and a transversal of only `n/2^r` elements — the concentrated count `C(n/2^r, s)`
collapses to `O(1)` as `t → √(kn) − k` (the deep interior). That is precisely why single-target
symmetry concentration is **capacity-only** and cannot pin `δ*` past the gap interior. -/
theorem cosetClosure_psum_eq_zero_of_lt (hωd : ω ^ d = 1) (hω0 : ω ≠ 0)
    (hprim : ∀ i, 0 < i → i < d → ω ^ i ≠ 1) (P : Finset F) {j : ℕ} (hj0 : 0 < j) (hjd : j < d) :
    ∑ x ∈ cosetClosure ω d P, x ^ j = 0 :=
  cosetClosure_psum_eq_zero hωd hω0 (hprim j hj0 hjd) P

/-- **Non-vacuity (`d = 4` over `ZMod 5`):** the primitive order-4 root `2` makes `cosetClosure 2 4
{1} = {1,2,3,4}` vanish `p_1, p_2, p_3` simultaneously (`∑x = ∑x² = ∑x³ = 0` in `ZMod 5`) — the first
three power sums concentrated at `0` by a single `d = 4` closure. -/
theorem nonvacuous_coset_zmod5 :
    (∑ x ∈ cosetClosure (2 : ZMod 5) 4 {1}, x ^ 1) = 0 ∧
    (∑ x ∈ cosetClosure (2 : ZMod 5) 4 {1}, x ^ 2) = 0 ∧
    (∑ x ∈ cosetClosure (2 : ZMod 5) 4 {1}, x ^ 3) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · exact cosetClosure_psum_eq_zero (by decide) (by decide) (by decide) {1}
  · exact cosetClosure_psum_eq_zero (by decide) (by decide) (by decide) {1}
  · exact cosetClosure_psum_eq_zero (by decide) (by decide) (by decide) {1}

end ArkLib.CodingTheory.Round8OmegaConcentration

/-! ## Axiom audit -/
#print axioms ArkLib.CodingTheory.Round8OmegaConcentration.omega_closed_psum_eq_zero
#print axioms ArkLib.CodingTheory.Round8OmegaConcentration.omega4Closure_image_eq
#print axioms ArkLib.CodingTheory.Round8OmegaConcentration.omega4Closure_sum_eq_zero
#print axioms ArkLib.CodingTheory.Round8OmegaConcentration.omega4Closure_sumsq_eq_zero
#print axioms ArkLib.CodingTheory.Round8OmegaConcentration.omega4_card_eq
#print axioms ArkLib.CodingTheory.Round8OmegaConcentration.omega4Closure_injOn
#print axioms ArkLib.CodingTheory.Round8OmegaConcentration.card_ge_choose_two_zero
#print axioms ArkLib.CodingTheory.Round8OmegaConcentration.nonvacuous_zmod5
#print axioms ArkLib.CodingTheory.Round8OmegaConcentration.nonvacuous_count_zmod5
#print axioms ArkLib.CodingTheory.Round8OmegaConcentration.cosetClosure_image_eq
#print axioms ArkLib.CodingTheory.Round8OmegaConcentration.cosetClosure_psum_eq_zero
#print axioms ArkLib.CodingTheory.Round8OmegaConcentration.cosetClosure_psum_eq_zero_of_lt
#print axioms ArkLib.CodingTheory.Round8OmegaConcentration.nonvacuous_coset_zmod5
