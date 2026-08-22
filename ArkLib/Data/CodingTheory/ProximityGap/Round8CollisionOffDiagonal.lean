/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import ArkLib.Data.CodingTheory.ProximityGap.SubsetSumSecondMomentCollision

/-!
# Round 8 (Issue #232, ABF26) — the OFF-DIAGONAL of `collisionCount` starts at symmetric-difference 3.

Round 7 (`SubsetSumSecondMomentCollision.lean`) reduced the prize-deciding concentration question to
the single scalar `collisionCount G a = ∑_{(c₁,c₂)} N2(c₁,c₂)²`, sandwiched between the diagonal floor
`C(|G|,a)` (every subset collides with itself) and `C(|G|,a)²`. The genuinely-hard content is the
**off-diagonal**: collision pairs `(S, S')` with `S ≠ S'` sharing both `∑ x` and `∑ x²`.

## What this round contributes — the off-diagonal is empty below symmetric-difference 3

For a finite set `G` of **nonzero** field elements (the smooth subgroup, where `0 ∉ G` and `char ≠ 2`),
the map `φ(S) = (∑_{x∈S} x, ∑_{x∈S} x²)` is **injective on subsets of size `≤ 2`**. The heart is the
Vieta lemma `pair_eq_of_sum_sq`: two pairs with equal sum and equal sum-of-squares are equal as
unordered pairs (equal sum + equal sum-of-squares ⟹ equal product ⟹ same monic quadratic ⟹ same
roots).

Consequently (`collision_offdiag`, `collisionCount_smallDiff_eq`), a collision pair `(S, S')` of
equal-size subsets whose symmetric difference is small (`|S \ S'| ≤ 2`) is forced to be **diagonal**
(`S = S'`): subtract the common part `S ∩ S'` to get equal-size symmetric-difference sides `U, V` with
matching `(∑, ∑²)`; by injectivity on `≤ 2`-sets, `U = V`, but `U, V` are disjoint, so `U = V = ∅`.

**The exact localization.** The first nontrivial collisions live at symmetric difference `m = 3`:
two distinct triples can share `(∑, ∑²)` (3 unknowns, 2 constraints). So `collisionCount`'s
off-diagonal is *entirely* the triple-(and-higher)-incidence count — exactly the
`#{(u₁,u₂,u₃),(v₁,v₂,v₃) : ∑u = ∑v, ∑u² = ∑v²}` whose size over the multiplicative subgroup `G` is the
subgroup-restricted second-moment / Weil object Mathlib cannot yet bound. This file does not bound it;
it **isolates** it, proving that everything below `m = 3` is the diagonal.

All headline results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Tracking issue #232.
-/

set_option linter.style.longLine false


open Finset

namespace ArkLib.ProximityGap.Round8CollisionOffDiagonal

/-! ## 1. The Vieta core: pairs are determined by their sum and sum-of-squares. -/

/-- **Vieta.** Two pairs with equal sum and equal sum-of-squares are equal as unordered pairs.
From `a + b = c + d` and `a² + b² = c² + d²` (char `≠ 2`) we get `a·b = c·d`, so `a, b` and `c, d` are
the two roots of the same monic quadratic `X² − (a+b)X + ab`, hence `{a,b} = {c,d}`. -/
theorem pair_eq_of_sum_sq {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) {a b c d : F}
    (hsum : a + b = c + d) (hsq : a ^ 2 + b ^ 2 = c ^ 2 + d ^ 2) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have hprod : a * b = c * d := by
    have e1 : (2 : F) * (a * b) = (2 : F) * (c * d) := by
      linear_combination (a + b + c + d) * hsum - hsq
    exact mul_left_cancel₀ h2 e1
  have hroot : (c - a) * (c - b) = 0 := by
    linear_combination (-c) * hsum + hprod
  rcases mul_eq_zero.mp hroot with hca | hcb
  · have hceq : c = a := sub_eq_zero.mp hca
    left
    refine ⟨hceq.symm, ?_⟩
    have hd : b = d := by
      have h := hsum
      rw [hceq] at h
      exact add_left_cancel h
    exact hd
  · have hceq : c = b := sub_eq_zero.mp hcb
    right
    refine ⟨?_, hceq.symm⟩
    have hd : a = d := by
      have h : b + a = b + d := by linear_combination hsum + hceq
      exact add_left_cancel h
    exact hd

/-- **Two `2`-element subsets with equal sum and equal sum-of-squares are equal.** -/
theorem two_subset_eq_of_phi {F : Type*} [Field F] [DecidableEq F] (h2 : (2 : F) ≠ 0)
    {S S' : Finset F} (hS : S.card = 2) (hS' : S'.card = 2)
    (h1 : ∑ x ∈ S, x = ∑ x ∈ S', x) (h2' : ∑ x ∈ S, x ^ 2 = ∑ x ∈ S', x ^ 2) :
    S = S' := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hS
  obtain ⟨c, d, hcd, rfl⟩ := Finset.card_eq_two.mp hS'
  rw [Finset.sum_pair hab, Finset.sum_pair hcd] at h1
  rw [Finset.sum_pair hab, Finset.sum_pair hcd] at h2'
  rcases pair_eq_of_sum_sq h2 h1 h2' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact Finset.pair_comm a b

/-- **`φ` is injective on subsets of size `≤ 2` of equal cardinality** (cases `0v0`, `1v1`, `2v2`). -/
theorem subset_eq_of_phi_le_two {F : Type*} [Field F] [DecidableEq F] (h2 : (2 : F) ≠ 0)
    {S S' : Finset F} (hcard : S.card = S'.card) (hle : S.card ≤ 2)
    (h1 : ∑ x ∈ S, x = ∑ x ∈ S', x) (h2' : ∑ x ∈ S, x ^ 2 = ∑ x ∈ S', x ^ 2) :
    S = S' := by
  interval_cases hn : S.card
  · rw [Finset.card_eq_zero.mp hn, Finset.card_eq_zero.mp hcard.symm]
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hn
    obtain ⟨b, rfl⟩ := Finset.card_eq_one.mp hcard.symm
    rw [Finset.sum_singleton, Finset.sum_singleton] at h1
    rw [h1]
  · exact two_subset_eq_of_phi h2 hn hcard.symm h1 h2'

/-! ## 2. Off-diagonal collisions need symmetric difference `≥ 3`. -/

/-- **Off-diagonal collisions need `m ≥ 3`.** If `S, S' ⊆ G` (a finite set of nonzero field elements)
have equal size, equal sum, equal sum-of-squares, and *small* symmetric difference (`|S \ S'| ≤ 2`),
then `S = S'`. So two **distinct** equal-size subsets collide under `φ` only when each side of their
symmetric difference has `≥ 3` elements.

The membership hypotheses `0 ∉ G`, `S, S' ⊆ G` describe the intended setting; they are not needed for
the equal-size cases (`|U| = |V|` rules out the singleton-vs-pair configuration where nonzeroness
would matter). They are kept for faithful context. -/
theorem collision_offdiag {F : Type*} [Field F] [DecidableEq F] (h2 : (2 : F) ≠ 0)
    {G : Finset F} (_hG0 : (0 : F) ∉ G) {S S' : Finset F}
    (_hSG : S ⊆ G) (_hSG' : S' ⊆ G)
    (hcard : S.card = S'.card)
    (h1 : ∑ x ∈ S, x = ∑ x ∈ S', x) (h2' : ∑ x ∈ S, x ^ 2 = ∑ x ∈ S', x ^ 2)
    (hsmall : (S \ S').card ≤ 2) :
    S = S' := by
  set U := S \ S' with hU
  set V := S' \ S with hV
  have hUVcard : U.card = V.card := by
    have hS : S.card = (S ∩ S').card + U.card := by
      rw [hU, ← Finset.card_inter_add_card_sdiff S S']
    have hS' : S'.card = (S' ∩ S).card + V.card := by
      rw [hV, ← Finset.card_inter_add_card_sdiff S' S]
    rw [Finset.inter_comm S' S] at hS'
    omega
  have key : ∀ g : F → F, ∑ x ∈ S, g x = ∑ x ∈ S', g x → ∑ x ∈ U, g x = ∑ x ∈ V, g x := by
    intro g hg
    have eS : ∑ x ∈ S, g x = ∑ x ∈ S ∩ S', g x + ∑ x ∈ U, g x := by
      rw [hU, Finset.sum_inter_add_sum_diff S S' g]
    have eS' : ∑ x ∈ S', g x = ∑ x ∈ S' ∩ S, g x + ∑ x ∈ V, g x := by
      rw [hV, Finset.sum_inter_add_sum_diff S' S g]
    rw [Finset.inter_comm S' S] at eS'
    rw [eS, eS'] at hg
    exact add_left_cancel hg
  have hsumU : ∑ x ∈ U, x = ∑ x ∈ V, x := key (fun x => x) h1
  have hsqU : ∑ x ∈ U, x ^ 2 = ∑ x ∈ V, x ^ 2 := key (fun x => x ^ 2) h2'
  have hUV : U = V := subset_eq_of_phi_le_two h2 hUVcard hsmall hsumU hsqU
  have hdisj : Disjoint U V := by
    rw [hU, hV]
    exact disjoint_sdiff_sdiff
  rw [hUV] at hdisj
  have hVempty : V = ∅ := disjoint_self.mp hdisj
  have hUempty : U = ∅ := by rw [hUV]; exact hVempty
  rw [Finset.sdiff_eq_empty_iff_subset] at hUempty hVempty
  exact Finset.Subset.antisymm hUempty hVempty

/-! ## 3. Consequence for Round-7's `collisionCount`. -/

/-- **The small-symmetric-difference part of `collisionCount` is exactly the diagonal.** Over a smooth
subgroup `G` (`0 ∉ G`, `char ≠ 2`), any ordered pair `(S, S')` that contributes to
`Round7SecondMoment.collisionCount G a` (i.e. both are `a`-subsets of `G` agreeing on `∑ x` and
`∑ x²`) and whose symmetric difference is small (`|S \ S'| ≤ 2`) is in fact the diagonal pair
`S = S'`. Hence `collisionCount`'s off-diagonal lives entirely at symmetric difference `≥ 3` — the
triple-incidence (Weil) term. -/
theorem collisionCount_smallDiff_eq {F : Type*} [Field F] [DecidableEq F] (h2 : (2 : F) ≠ 0)
    {G : Finset F} (hG0 : (0 : F) ∉ G) {a : ℕ} {S S' : Finset F}
    (hp : (S, S') ∈ (G.powersetCard a ×ˢ G.powersetCard a).filter
      (fun p => (∑ x ∈ p.1, x) = (∑ x ∈ p.2, x)
        ∧ (∑ x ∈ p.1, x ^ 2) = (∑ x ∈ p.2, x ^ 2)))
    (hsmall : (S \ S').card ≤ 2) :
    S = S' := by
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_powersetCard, Finset.mem_powersetCard] at hp
  obtain ⟨⟨⟨hSsub, hScard⟩, hS'sub, hS'card⟩, h1, h2'⟩ := hp
  exact collision_offdiag h2 hG0 hSsub hS'sub (by rw [hScard, hS'card]) h1 h2' hsmall

end ArkLib.ProximityGap.Round8CollisionOffDiagonal

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Round8CollisionOffDiagonal.pair_eq_of_sum_sq
#print axioms ArkLib.ProximityGap.Round8CollisionOffDiagonal.collision_offdiag
#print axioms ArkLib.ProximityGap.Round8CollisionOffDiagonal.collisionCount_smallDiff_eq
