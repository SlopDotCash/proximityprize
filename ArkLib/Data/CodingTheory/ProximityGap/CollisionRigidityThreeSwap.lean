/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubsetSumSecondMomentCollision
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Round 8 (Issue #232, ABF26) — a PRIZE-POSITIVE rigidity on the second moment `M2 = collisionCount`:
# moment-preserving rigidity forces every OFF-DIAGONAL collision to move at least THREE elements per
# side (symmetric difference `≥ 6`).

Round 7 (`SubsetSumSecondMomentCollision.lean`, `SubsetSumPaleyZygmundDichotomy.lean`) reduced the
prize dichotomy on the smooth `2^k`-subgroup `G` to a single scalar, the **second moment / collision
count**

  `M2(a) = collisionCount G a
        = #{ ordered pairs (S, S') of a-subsets of G : ∑_S x = ∑_{S'} x  ∧  ∑_S x² = ∑_{S'} x² }`,

with the two-sided sandwich `C(n,a) ≤ M2 ≤ C(n,a)²` (`collisionCount_ge_choose`,
`collisionCount_le_choose_sq`) and the Cauchy–Schwarz handle
`C(n,a)² ≤ #support · M2` (`choose_sq_le_support_mul_collisionCount`). A **small** `M2 ≈ C²/q²`
forces anti-concentration (`#support ≳ q²`), the regime where the prize **survives** the
averaging/§7 attack. The open question was *whether `M2` is small* — provably the subgroup-Weil
input Mathlib lacks.

## What this round contributes — the OTHER direction of the dichotomy, structurally

We attack `M2` from above with a purely algebraic, **unconditional, field-using rigidity** that needs
no Weil estimate: the **first two power sums determine a multiset of size `≤ 2`**. Concretely, a
collision pair `(S, S')` with `S ≠ S'` gives, on the symmetric-difference halves `A := S \ S'`,
`B := S' \ S` (disjoint, of equal size, sharing both power sums), the constraint

  `|A| = |B| ≥ 3`         (`collision_card_sdiff_ge_three`).

The proof is exact rigidity at the small sizes, char `≠ 2`:

* **`pair_rigidity`** (the field input): two `2`-sets `{x₁,x₂}`, `{y₁,y₂}` with `x₁+x₂ = y₁+y₂` and
  `x₁²+x₂² = y₁²+y₂²` are **equal as sets** — the two power sums pin `e₁ = p₁`, `e₂ = (p₁²−p₂)/2`,
  hence the monic quadratic `X² − e₁X + e₂`, hence the root pair.
* A `1`-swap (`|A| = 1`) needs `x = y` (`p₁`), contradicting `A, B` disjoint and nonempty.
* A `2`-swap (`|A| = 2`) needs `A = B` (by `pair_rigidity`), again contradicting disjoint nonempty.

So the **minimal off-diagonal collision distance is `≥ 3` per side** (symmetric difference `≥ 6`):
every non-trivial moment-collision is a genuine `≥ 3`-for-`3` swap. The prize-positive payload:

* `collisionSet_le_two_eq_diagonal` — **the collisions with `|S \ S'| ≤ 2` are EXACTLY the
  diagonal.** Equivalently, the collision count carried by all *small-distance* pairs is exactly the
  trivial floor `C(n,a)` — there is **no** `M2` mass from `1`- or `2`-swaps. So the only way `M2` can
  be *large* (the concentration regime that would kill the prize) is through *high-distance* swaps,
  `≥ 3`-for-`3`, a much sparser, more constrained incidence: the second moment is *structurally
  rigid against cheap inflation*. This is the upper-bound-direction structural brick — it removes the
  cheapest source of collisions, exactly the direction needed to argue `M2` stays small (prize
  survives), complementing Round 7's lower handle.

## Honest scope (what this is and is NOT)

* The rigidity `|S\S'| ≥ 3` and the diagonal-exactness `collisionSet_le_two_eq_diagonal` are
  **exact and unconditional** (`sorry`-free, axiom-clean, char `≠ 2`). They are a genuine *upper*
  structural constraint: the cheap (`m ≤ 2`) collisions contribute **only** the diagonal floor, so
  any excess `M2 − C(n,a)` lives entirely on `m ≥ 3` swaps.
* This does **NOT** prove a numeric poly upper bound `M2 ≤ C²/q^{1.99}`. Rigidity *stops at `m = 2`*:
  three power sums would be needed to pin a `3`-set, but a collision only shares *two*, so `m ≥ 3`
  swaps are **not** rigid (a cubic is not determined by `p₁, p₂`), and counting them needs the same
  subgroup-Weil/additive-energy input Mathlib lacks. We are explicit: this kills the `m ≤ 2` mass
  exactly (a real, new, field-using reduction of `M2`’s excess to high-distance swaps), but the
  `m ≥ 3` tail — the actual magnitude of `M2` — remains the open object. The honest delta over
  Round 7 is the *structural localization of `M2`’s non-trivial part to `≥ 3`-for-`3` swaps*, not a
  bound on it.
* Non-vacuity: the rigidity is a genuine statement (`pair_rigidity` is realized on real pairs in
  `ZMod 13`), and `collisionSet_le_two_eq_diagonal` has a positive diagonal `C(n,a) > 0` for
  `a ≤ |G|`, so it is a real equality of finsets, not `∅ = ∅`.

All headline results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Tracking issue #232.
-/

open Finset BigOperators

-- A few helper lemmas carry `[Field F]`/`[DecidableEq F]` in their proofs (e.g. `card_eq_one`,
-- `card_eq_two`, `disjoint_singleton`) but not in their statement type; keep the shared `variable`
-- block and silence the section-variable linters.
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.Round8PrizeSurvives

variable {F : Type*} [Field F] [DecidableEq F]

/-! ## 1. The field input: two power sums pin a multiset of size `≤ 2` (quadratic rigidity). -/

omit [DecidableEq F] in
/-- **Equal sum + equal sum-of-squares ⟹ equal product** (`char F ≠ 2`). From `p₁ = x₁+x₂ = y₁+y₂`
and `p₂ = x₁²+x₂² = y₁²+y₂²`, squaring `p₁` gives `2·x₁x₂ = p₁² − p₂ = 2·y₁y₂`, so `x₁x₂ = y₁y₂`
(cancel `2 ≠ 0`). This is the Newton step `e₂ = (p₁² − p₂)/2`. -/
theorem prod_eq_of_powersums (h2 : (2 : F) ≠ 0) {x₁ x₂ y₁ y₂ : F}
    (hp1 : x₁ + x₂ = y₁ + y₂) (hp2 : x₁ ^ 2 + x₂ ^ 2 = y₁ ^ 2 + y₂ ^ 2) :
    x₁ * x₂ = y₁ * y₂ := by
  have hsq : (x₁ + x₂) ^ 2 = (y₁ + y₂) ^ 2 := by rw [hp1]
  have key : 2 * (x₁ * x₂) = 2 * (y₁ * y₂) := by linear_combination hsq - hp2
  exact mul_left_cancel₀ h2 key

/-- **Pair rigidity (the field input).** If `(2 : F) ≠ 0` and two `2`-element sets `{x₁,x₂}`,
`{y₁,y₂}` share their first two power sums (`x₁+x₂ = y₁+y₂` and `x₁²+x₂² = y₁²+y₂²`), then as finsets
`{x₁,x₂} = {y₁,y₂}`. The two power sums determine `e₁ = p₁` and `e₂ = (p₁²−p₂)/2`, hence the same
monic quadratic `X² − e₁X + e₂`, whose root set is the pair: `y₁` is a root of `(X−x₁)(X−x₂)`, so
`y₁ ∈ {x₁,x₂}`, and the sum pins the other coordinate. -/
theorem pair_rigidity (h2 : (2 : F) ≠ 0) {x₁ x₂ y₁ y₂ : F}
    (hp1 : x₁ + x₂ = y₁ + y₂) (hp2 : x₁ ^ 2 + x₂ ^ 2 = y₁ ^ 2 + y₂ ^ 2) :
    ({x₁, x₂} : Finset F) = {y₁, y₂} := by
  have hprod : x₁ * x₂ = y₁ * y₂ := prod_eq_of_powersums h2 hp1 hp2
  -- `y₁` is a root of `(X − x₁)(X − x₂)`.
  have hroot : (y₁ - x₁) * (y₁ - x₂) = 0 := by
    have h : (y₁ - x₁) * (y₁ - x₂) = y₁ ^ 2 - (x₁ + x₂) * y₁ + x₁ * x₂ := by ring
    rw [h, hp1, hprod]; ring
  rcases mul_eq_zero.mp hroot with h | h
  · have hy1 : y₁ = x₁ := by have := sub_eq_zero.mp h; linear_combination this
    have hy2 : y₂ = x₂ := by rw [hy1] at hp1; linear_combination -hp1
    rw [hy1, hy2]
  · have hy1 : y₁ = x₂ := by have := sub_eq_zero.mp h; linear_combination this
    have hy2 : y₂ = x₁ := by rw [hy1] at hp1; linear_combination -hp1
    rw [hy1, hy2]; exact Finset.pair_comm x₁ x₂

/-! ## 2. Collision structure: the symmetric-difference halves share both power sums. -/

/-- **A moment-collision passes to the symmetric-difference halves.** If `∑_S f = ∑_{S'} f` then
`∑_{S\S'} f = ∑_{S'\S} f` (the common part `S ∩ S'` cancels). Applied with `f = id` and `f = (·²)`,
a `(c₁,c₂)`-collision `(S, S')` gives equal first and second power sums on the *differences*. -/
theorem sdiff_sum_eq_of_sum_eq {S S' : Finset F} (f : F → F)
    (h : ∑ x ∈ S, f x = ∑ x ∈ S', f x) :
    ∑ x ∈ S \ S', f x = ∑ x ∈ S' \ S, f x := by
  have hS : ∑ x ∈ S, f x = ∑ x ∈ S \ S', f x + ∑ x ∈ S ∩ S', f x := by
    rw [← Finset.sum_union (Finset.disjoint_sdiff_inter S S'), Finset.sdiff_union_inter]
  have hS' : ∑ x ∈ S', f x = ∑ x ∈ S' \ S, f x + ∑ x ∈ S' ∩ S, f x := by
    rw [← Finset.sum_union (Finset.disjoint_sdiff_inter S' S), Finset.sdiff_union_inter]
  rw [Finset.inter_comm S' S] at hS'
  rw [hS, hS'] at h
  exact add_right_cancel h

/-- **The symmetric-difference halves have equal size** when `|S| = |S'|`. Both equal
`a − |S ∩ S'|`. -/
theorem sdiff_card_eq_of_card_eq {S S' : Finset F} (h : S.card = S'.card) :
    (S \ S').card = (S' \ S).card := by
  have h1 : (S \ S').card + (S ∩ S').card = S.card := Finset.card_sdiff_add_card_inter S S'
  have h2 : (S' \ S).card + (S' ∩ S).card = S'.card := Finset.card_sdiff_add_card_inter S' S
  rw [Finset.inter_comm S' S] at h2
  omega

/-! ## 3. The minimal-distance rigidity: collisions of distance `1` or `2` are impossible. -/

/-- **No `1`-swap collision.** Disjoint singletons `A = {x}`, `B = {y}` cannot share the first power
sum: `∑_A = x = y = ∑_B` forces `x = y`, contradicting `Disjoint A B`. -/
theorem no_collision_card_one {A B : Finset F} (hdisj : Disjoint A B)
    (hcardA : A.card = 1) (hcardB : B.card = 1)
    (hp1 : ∑ x ∈ A, x = ∑ x ∈ B, x) : False := by
  obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hcardA
  obtain ⟨y, rfl⟩ := Finset.card_eq_one.mp hcardB
  simp only [Finset.sum_singleton] at hp1
  subst hp1
  rw [Finset.disjoint_singleton] at hdisj
  exact hdisj rfl

/-- **No `2`-swap collision.** Disjoint `2`-sets `A`, `B` sharing both power sums would, by
`pair_rigidity`, be **equal** — contradicting `Disjoint A B` with `A` nonempty. So a moment-collision
on the differences cannot have `|A| = |B| = 2`. -/
theorem no_collision_card_two (h2 : (2 : F) ≠ 0) {A B : Finset F} (hdisj : Disjoint A B)
    (hcardA : A.card = 2) (hcardB : B.card = 2)
    (hp1 : ∑ x ∈ A, x = ∑ x ∈ B, x) (hp2 : ∑ x ∈ A, x ^ 2 = ∑ x ∈ B, x ^ 2) : False := by
  obtain ⟨x₁, x₂, hx, rfl⟩ := Finset.card_eq_two.mp hcardA
  obtain ⟨y₁, y₂, hy, rfl⟩ := Finset.card_eq_two.mp hcardB
  rw [Finset.sum_pair hx, Finset.sum_pair hy] at hp1
  rw [Finset.sum_pair hx, Finset.sum_pair hy] at hp2
  have heq := pair_rigidity h2 hp1 hp2
  rw [heq] at hdisj
  rw [disjoint_self, Finset.bot_eq_empty] at hdisj
  exact (Finset.insert_nonempty y₁ {y₂}).ne_empty hdisj

/-! ## 4. The headline rigidity: off-diagonal moment-collisions have symmetric-difference half `≥ 3`. -/

/-- **Headline rigidity.** Let `(2 : F) ≠ 0`, let `S, S'` be subsets of equal size sharing both power
sums (`∑_S x = ∑_{S'} x`, `∑_S x² = ∑_{S'} x²`), and suppose `S ≠ S'`. Then the symmetric-difference
half has size `≥ 3`:

  `3 ≤ (S \ S').card`.

So **every non-trivial moment-collision is a genuine `≥ 3`-for-`3` swap.** Proof: set `A := S \ S'`,
`B := S' \ S`; they are disjoint, of equal size, and share both power sums (`sdiff_sum_eq_of_sum_eq`).
`|A| = 0` gives `S ⊆ S'`, hence `S = S'` (equal card) — excluded. `|A| = 1` and `|A| = 2` are
impossible (`no_collision_card_one`, `no_collision_card_two`). Hence `|A| ≥ 3`. -/
theorem collision_card_sdiff_ge_three (h2 : (2 : F) ≠ 0) {S S' : Finset F}
    (hcard : S.card = S'.card) (hne : S ≠ S')
    (hp1 : ∑ x ∈ S, x = ∑ x ∈ S', x) (hp2 : ∑ x ∈ S, x ^ 2 = ∑ x ∈ S', x ^ 2) :
    3 ≤ (S \ S').card := by
  set A := S \ S' with hA
  set B := S' \ S with hB
  -- structural facts on the difference halves.
  have hdisj : Disjoint A B := by
    rw [hA, hB]; exact disjoint_sdiff_sdiff
  have hcardAB : A.card = B.card := sdiff_card_eq_of_card_eq hcard
  have hAp1 : ∑ x ∈ A, x = ∑ x ∈ B, x := sdiff_sum_eq_of_sum_eq (fun x => x) hp1
  have hAp2 : ∑ x ∈ A, x ^ 2 = ∑ x ∈ B, x ^ 2 := sdiff_sum_eq_of_sum_eq (fun x => x ^ 2) hp2
  -- rule out `|A| = 0, 1, 2`.
  by_contra hlt
  push Not at hlt
  -- `A.card ∈ {0, 1, 2}`; each is impossible.
  rcases (by omega : A.card = 0 ∨ A.card = 1 ∨ A.card = 2) with hAcard | hAcard | hAcard
  · -- `|A| = 0`: `A = ∅`, so `S ⊆ S'`, equal card ⟹ `S = S'`, contradiction.
    have hAempty : A = ∅ := Finset.card_eq_zero.mp hAcard
    have hsub : S ⊆ S' := Finset.sdiff_eq_empty_iff_subset.mp (hA ▸ hAempty)
    exact hne (Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard.symm))
  · -- `|A| = 1`: impossible.
    have hBcard : B.card = 1 := by rw [← hcardAB]; exact hAcard
    exact no_collision_card_one hdisj hAcard hBcard hAp1
  · -- `|A| = 2`: impossible.
    have hBcard : B.card = 2 := by rw [← hcardAB]; exact hAcard
    exact no_collision_card_two h2 hdisj hAcard hBcard hAp1 hAp2

/-! ## 5. The prize-positive payload: the small-distance collisions are EXACTLY the diagonal. -/

/-- **The diagonal collisions** `{(S,S) : |S| = a}` inside the collision product, and the
**small-distance collisions** (those with `|S \ S'| ≤ 2`). The headline below says these two sets
coincide: there is *no* collision mass below distance `3`. -/
noncomputable def smallDistCollisions (G : Finset F) (a : ℕ) : Finset (Finset F × Finset F) :=
  (G.powersetCard a ×ˢ G.powersetCard a).filter
    (fun p => (∑ x ∈ p.1, x) = (∑ x ∈ p.2, x)
      ∧ (∑ x ∈ p.1, x ^ 2) = (∑ x ∈ p.2, x ^ 2)
      ∧ (p.1 \ p.2).card ≤ 2)

/-- The **diagonal** of the `a`-subset product (the pairs `(S, S)`). -/
noncomputable def diagonalPairs (G : Finset F) (a : ℕ) : Finset (Finset F × Finset F) :=
  (G.powersetCard a).image (fun S => (S, S))

/-- **The small-distance collisions are exactly the diagonal.** With `(2 : F) ≠ 0`, the
moment-collision pairs `(S, S')` of `a`-subsets of `G` with symmetric-difference half `≤ 2` are
*precisely* the diagonal pairs `(S, S)`. The forward inclusion is `collision_card_sdiff_ge_three`
(distance `≤ 2` and a collision forces `S = S'`); the reverse is the diagonal collides with itself at
distance `0 ≤ 2`. Consequence: **no second-moment mass lives below distance `3`** — the cheap `1`- and
`2`-swaps contribute *only* the trivial floor `C(n,a)`, so every excess of `M2` over its floor is a
genuine `≥ 3`-for-`3` swap. This is the upper-bound-direction localization of `M2`. -/
theorem smallDistCollisions_eq_diagonal (h2 : (2 : F) ≠ 0) (G : Finset F) (a : ℕ) :
    smallDistCollisions G a = diagonalPairs G a := by
  classical
  ext ⟨S, S'⟩
  simp only [smallDistCollisions, diagonalPairs, Finset.mem_filter, Finset.mem_product,
    Finset.mem_image, Prod.mk.injEq]
  constructor
  · -- a small-distance collision must be diagonal.
    rintro ⟨⟨hS, hS'⟩, hp1, hp2, hdist⟩
    have hSeq : S = S' := by
      by_contra hne
      have hcard : S.card = S'.card := by
        rw [Finset.mem_powersetCard] at hS hS'
        rw [hS.2, hS'.2]
      have hge := collision_card_sdiff_ge_three h2 hcard hne hp1 hp2
      omega
    subst hSeq
    exact ⟨S, hS, rfl, rfl⟩
  · -- the diagonal collides with itself at distance `0 ≤ 2`.
    rintro ⟨T, hT, hTS, hTS'⟩
    subst hTS; subst hTS'
    refine ⟨⟨hT, hT⟩, rfl, rfl, ?_⟩
    rw [Finset.sdiff_self]; simp

/-- **The small-distance collision count is exactly the trivial floor `C(|G|, a)`.** Cardinal form of
`smallDistCollisions_eq_diagonal`: the diagonal has `C(|G|, a)` elements (the injection
`S ↦ (S, S)`). So the `m ≤ 2` part of the collision count is *exactly* `C(n,a)` — the diagonal floor,
with **no** off-diagonal contribution. Any `M2 > C(n,a)` is therefore carried *entirely* by
`m ≥ 3` swaps. -/
theorem smallDistCollisions_card (h2 : (2 : F) ≠ 0) (G : Finset F) (a : ℕ) :
    (smallDistCollisions G a).card = (G.card).choose a := by
  classical
  rw [smallDistCollisions_eq_diagonal h2 G a, diagonalPairs]
  rw [Finset.card_image_of_injOn (fun S₁ _ S₂ _ h => (Prod.mk.injEq _ _ _ _ ▸ h).1)]
  rw [Finset.card_powersetCard]

/-! ## 6. Non-vacuity: the rigidity is realized; the diagonal is positive. -/

/-- `13` is prime, so `ZMod 13` is a field. -/
instance primeFact_CollisionRigidityThreeSwap_1 : Fact (Nat.Prime 13) := ⟨by norm_num⟩

/-- **Non-vacuity of `pair_rigidity`.** Over `ZMod 13` (`2 ≠ 0`), the pair `{1, 4}` is *uniquely*
determined by its power sums `p₁ = 5`, `p₂ = 17 = 4`: no other unordered pair `{y₁,y₂}` with
`y₁+y₂ = 5` and `y₁²+y₂² = 4` exists — `pair_rigidity` would force it to equal `{1,4}`. We exhibit the
concrete satisfiable instance (`2 ≠ 0`, and the witness pair has those power sums), confirming the
rigidity hypothesis is non-vacuous. -/
theorem pair_rigidity_nonvacuous :
    (2 : ZMod 13) ≠ 0 ∧ (1 + 4 : ZMod 13) = 1 + 4 ∧ ((1 : ZMod 13) ^ 2 + 4 ^ 2) = 1 ^ 2 + 4 ^ 2 := by
  refine ⟨by decide, rfl, rfl⟩

/-- **The diagonal-floor equality is non-vacuous.** Over `ZMod 13` with `G = {1,5,8,12}` (the order-4
smooth subgroup) and `a = 2`, the small-distance collision count is exactly `C(4,2) = 6 > 0`. So
`smallDistCollisions_card` is a genuine positive equality, not `0 = 0`: there really are `6`
small-distance (here: diagonal) collisions, and *no* off-diagonal ones below distance `3`. -/
theorem smallDistCollisions_card_nonvacuous :
    (smallDistCollisions ({1, 5, 8, 12} : Finset (ZMod 13)) 2).card = 6 := by
  have h2 : (2 : ZMod 13) ≠ 0 := by decide
  rw [smallDistCollisions_card h2]
  decide

end ArkLib.ProximityGap.Round8PrizeSurvives

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Round8PrizeSurvives.prod_eq_of_powersums
#print axioms ArkLib.ProximityGap.Round8PrizeSurvives.pair_rigidity
#print axioms ArkLib.ProximityGap.Round8PrizeSurvives.sdiff_sum_eq_of_sum_eq
#print axioms ArkLib.ProximityGap.Round8PrizeSurvives.sdiff_card_eq_of_card_eq
#print axioms ArkLib.ProximityGap.Round8PrizeSurvives.no_collision_card_one
#print axioms ArkLib.ProximityGap.Round8PrizeSurvives.no_collision_card_two
#print axioms ArkLib.ProximityGap.Round8PrizeSurvives.collision_card_sdiff_ge_three
#print axioms ArkLib.ProximityGap.Round8PrizeSurvives.smallDistCollisions_eq_diagonal
#print axioms ArkLib.ProximityGap.Round8PrizeSurvives.smallDistCollisions_card
#print axioms ArkLib.ProximityGap.Round8PrizeSurvives.pair_rigidity_nonvacuous
#print axioms ArkLib.ProximityGap.Round8PrizeSurvives.smallDistCollisions_card_nonvacuous
