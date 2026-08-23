/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

/-!
# Issue #232 (ABF26) — the second-moment / collision dichotomy is STATISTIC-AGNOSTIC, and the prize
# at interleaving depth `t` reduces to a single moment-collision scalar.

Round 7 (`SubsetSumSecondMomentCollision.lean`) proved, for the specific `(∑x, ∑x²)` statistic, the
exact identity `∑_c N2(c)² = collisionCount`, the trivial sandwich `C(n,a) ≤ collisionCount ≤
C(n,a)²`, and the Cauchy–Schwarz concentration handle `C(n,a)² ≤ #support · collisionCount`. The
deep-interior prize then reduced to the single open magnitude `collisionCount` (the `t = 2` moment
collision).

This file shows that **entire mechanism depends on nothing about the statistic** — it holds for any
finite-valued statistic `stat : Finset F → τ` — and instantiates it at the **full power-sum moment
tower** `S ↦ (∑x, ∑x², …, ∑xᵗ)`, giving the depth-`t` prize reduction uniformly. This is the
meta-structure behind `ListInteriorUnconditionalGeneralT` (whose `/q^t` averaging loss is the dual of
the depth-`t` moment-collision scalar isolated here), and the abstract home of the round-7/round-8
`(∑x, ∑x²)` and order-4 concentration results.

## Contents

* `statCount`, `statCollision` — the fiber count and collision-pair count for an arbitrary
  `τ`-valued statistic on the `a`-subsets of `G`.
* `statCount_total` — zeroth moment `∑_c statCount c = C(|G|, a)`.
* `statSecondMoment_eq_collision` — **the headline identity** `∑_c (statCount c)² = statCollision`.
* `statCollision_ge_choose`, `statCollision_le_choose_sq` — the sandwich `C(n,a) ≤ statCollision ≤
  C(n,a)²` (diagonal floor; product cap).
* `choose_sq_le_support_mul_collision` — the Cauchy–Schwarz concentration handle
  `C(n,a)² ≤ #support · statCollision`: anti-concentration ⟺ large support ⟺ small collision.
* `moment_tower_dichotomy` — instantiated at `momentVec t : S ↦ (∑x, …, ∑xᵗ)`, the depth-`t` prize
  reduces to the single scalar `statCollision G a (momentVec t)`, sandwiched and concentration-bound
  exactly as the `t = 2` case. Subsumes Round-7's `(∑x, ∑x²)` reduction.

## Honest scope

`sorry`-free, axiom-clean (`[propext, Classical.choice, Quot.sound]`). These are exact, unconditional
identities and bounds; they isolate the open magnitude (the moment-collision scalar at depth `t`) but
do **not** bound it — that is the open Weil-on-curves content.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Tracking issue #232.
-/

open Finset BigOperators

namespace ArkLib.ProximityGap.MomentCollisionTower

variable {F : Type*} [DecidableEq F]
variable {τ : Type*} [Fintype τ] [DecidableEq τ]

/-- Generic fiber count of a `τ`-valued statistic on the `a`-subsets of `G`. -/
noncomputable def statCount (G : Finset F) (a : ℕ) (stat : Finset F → τ) (c : τ) : ℕ :=
  ((G.powersetCard a).filter (fun S => stat S = c)).card

/-- Generic collision-pair count for a `τ`-valued statistic. -/
noncomputable def statCollision (G : Finset F) (a : ℕ) (stat : Finset F → τ) : ℕ :=
  ((G.powersetCard a ×ˢ G.powersetCard a).filter (fun p => stat p.1 = stat p.2)).card

/-- Zeroth moment: every `a`-subset has some statistic value. -/
theorem statCount_total (G : Finset F) (a : ℕ) (stat : Finset F → τ) :
    ∑ c : τ, statCount G a stat c = (G.card).choose a := by
  classical
  have hpart : (G.powersetCard a).card
      = ∑ c : τ, ((G.powersetCard a).filter (fun S => stat S = c)).card :=
    Finset.card_eq_sum_card_fiberwise (f := fun S => stat S)
      (t := (Finset.univ : Finset τ)) (fun S _ => Finset.mem_univ _)
  rw [Finset.card_powersetCard] at hpart
  unfold statCount
  rw [← hpart]

/-- **The second moment of the fiber-size function equals the collision-pair count.** -/
theorem statSecondMoment_eq_collision (G : Finset F) (a : ℕ) (stat : Finset F → τ) :
    ∑ c : τ, (statCount G a stat c) ^ 2 = statCollision G a stat := by
  classical
  unfold statCollision
  have hpart :
      ((G.powersetCard a ×ˢ G.powersetCard a).filter (fun p => stat p.1 = stat p.2)).card
      = ∑ c : τ,
          (((G.powersetCard a ×ˢ G.powersetCard a).filter (fun p => stat p.1 = stat p.2)).filter
            (fun p => stat p.1 = c)).card :=
    Finset.card_eq_sum_card_fiberwise (f := fun p : Finset F × Finset F => stat p.1)
      (t := (Finset.univ : Finset τ)) (fun _ _ => Finset.mem_univ _)
  rw [hpart]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  unfold statCount
  rw [sq, ← Finset.card_product]
  congr 1
  ext ⟨S, S'⟩
  constructor
  · intro h
    obtain ⟨hSf, hS'f⟩ := Finset.mem_product.mp h
    obtain ⟨hS, hSc⟩ := Finset.mem_filter.mp hSf
    obtain ⟨hS', hS'c⟩ := Finset.mem_filter.mp hS'f
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hS, hS'⟩, ?_⟩, hSc⟩
    rw [hSc, hS'c]
  · intro h
    obtain ⟨h1, hc⟩ := Finset.mem_filter.mp h
    obtain ⟨h1a, hcol⟩ := Finset.mem_filter.mp h1
    obtain ⟨hS, hS'⟩ := Finset.mem_product.mp h1a
    refine Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hS, hc⟩, Finset.mem_filter.mpr ⟨hS', ?_⟩⟩
    rw [← hcol]; exact hc

/-- Diagonal lower bound: every subset collides with itself. -/
theorem statCollision_ge_choose (G : Finset F) (a : ℕ) (stat : Finset F → τ) :
    (G.card).choose a ≤ statCollision G a stat := by
  classical
  unfold statCollision
  rw [← Finset.card_powersetCard a G]
  apply Finset.card_le_card_of_injOn (fun S => (S, S))
  · intro S hS
    rw [Finset.mem_coe] at hS
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨hS, hS⟩, rfl⟩
  · intro S₁ _ S₂ _ h
    exact (Prod.mk.injEq _ _ _ _ ▸ h).1

/-- Upper bound: the collision set sits inside the full product. -/
theorem statCollision_le_choose_sq (G : Finset F) (a : ℕ) (stat : Finset F → τ) :
    statCollision G a stat ≤ ((G.card).choose a) ^ 2 := by
  classical
  unfold statCollision
  refine le_trans (Finset.card_filter_le _ _) ?_
  rw [Finset.card_product, Finset.card_powersetCard, sq]

/-- Support of the statistic: the realized values. -/
noncomputable def statSupport (G : Finset F) (a : ℕ) (stat : Finset F → τ) : Finset τ :=
  Finset.univ.filter (fun c => statCount G a stat c ≠ 0)

theorem statCount_total_eq_sum_support (G : Finset F) (a : ℕ) (stat : Finset F → τ) :
    ∑ c : τ, statCount G a stat c = ∑ c ∈ statSupport G a stat, statCount G a stat c := by
  classical
  refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
  intro c _ hc
  unfold statSupport at hc
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq, not_not] using hc

theorem statSecondMoment_eq_sum_support (G : Finset F) (a : ℕ) (stat : Finset F → τ) :
    ∑ c : τ, (statCount G a stat c) ^ 2
      = ∑ c ∈ statSupport G a stat, (statCount G a stat c) ^ 2 := by
  classical
  refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
  intro c _ hc
  unfold statSupport at hc
  have h0 : statCount G a stat c = 0 := by
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq, not_not] using hc
  rw [h0]; ring

/-- **Cauchy–Schwarz concentration handle for an arbitrary statistic.**
`C(|G|,a)² ≤ #support · statCollision`. So concentration on few values forces a large collision
count, and a small collision count forces wide spread (anti-concentration). -/
theorem choose_sq_le_support_mul_collision (G : Finset F) (a : ℕ) (stat : Finset F → τ) :
    ((G.card).choose a) ^ 2 ≤ (statSupport G a stat).card * statCollision G a stat := by
  classical
  have hcs : (∑ c ∈ statSupport G a stat, (statCount G a stat c : ℤ)) ^ 2
      ≤ (statSupport G a stat).card * ∑ c ∈ statSupport G a stat, (statCount G a stat c : ℤ) ^ 2 :=
    sq_sum_le_card_mul_sum_sq (s := statSupport G a stat)
      (f := fun c => (statCount G a stat c : ℤ))
  have htot : (∑ c ∈ statSupport G a stat, (statCount G a stat c : ℤ)) = ((G.card).choose a : ℤ) := by
    calc (∑ c ∈ statSupport G a stat, (statCount G a stat c : ℤ))
        = ((∑ c ∈ statSupport G a stat, statCount G a stat c : ℕ) : ℤ) := by push_cast; rfl
      _ = ((∑ c : τ, statCount G a stat c : ℕ) : ℤ) := by rw [← statCount_total_eq_sum_support]
      _ = ((G.card).choose a : ℤ) := by rw [statCount_total]
  rw [htot] at hcs
  have hsm : (∑ c ∈ statSupport G a stat, (statCount G a stat c : ℤ) ^ 2)
      = ((statCollision G a stat : ℕ) : ℤ) := by
    calc (∑ c ∈ statSupport G a stat, (statCount G a stat c : ℤ) ^ 2)
        = ((∑ c ∈ statSupport G a stat, (statCount G a stat c) ^ 2 : ℕ) : ℤ) := by push_cast; rfl
      _ = ((∑ c : τ, (statCount G a stat c) ^ 2 : ℕ) : ℤ) := by
            rw [← statSecondMoment_eq_sum_support]
      _ = ((statCollision G a stat : ℕ) : ℤ) := by rw [statSecondMoment_eq_collision]
  rw [hsm] at hcs
  have hcs' : (((G.card).choose a) ^ 2 : ℤ)
      ≤ (((statSupport G a stat).card * statCollision G a stat : ℕ) : ℤ) := by
    rw [Nat.cast_mul]; push_cast at hcs ⊢; exact hcs
  exact_mod_cast hcs'

/-! ## Instantiation at the power-sum moment tower. -/

variable [CommRing F]

/-- The depth-`t` power-sum moment vector `S ↦ (∑x, ∑x², …, ∑xᵗ)`. -/
noncomputable def momentVec (t : ℕ) (S : Finset F) : Fin t → F :=
  fun j => ∑ x ∈ S, x ^ (j.val + 1)

/-- **The depth-`t` moment-tower dichotomy.** The prize at interleaving depth `t` reduces to the
single scalar `statCollision G a (momentVec t)`, sandwiched in `[C(n,a), C(n,a)²]` with the
Cauchy–Schwarz concentration handle. This subsumes Round-7's `t = 2` `(∑x, ∑x²)` reduction; the
genuinely open content is the magnitude of that scalar, the depth-`t` Weil point count. -/
theorem moment_tower_dichotomy [Fintype F] (G : Finset F) (a t : ℕ) :
    (G.card).choose a ≤ statCollision G a (momentVec t)
      ∧ statCollision G a (momentVec t) ≤ ((G.card).choose a) ^ 2
      ∧ ((G.card).choose a) ^ 2
          ≤ (statSupport G a (momentVec t)).card * statCollision G a (momentVec t) :=
  ⟨statCollision_ge_choose G a _, statCollision_le_choose_sq G a _,
    choose_sq_le_support_mul_collision G a _⟩

end ArkLib.ProximityGap.MomentCollisionTower

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.MomentCollisionTower.statCount_total
#print axioms ArkLib.ProximityGap.MomentCollisionTower.statSecondMoment_eq_collision
#print axioms ArkLib.ProximityGap.MomentCollisionTower.statCollision_ge_choose
#print axioms ArkLib.ProximityGap.MomentCollisionTower.statCollision_le_choose_sq
#print axioms ArkLib.ProximityGap.MomentCollisionTower.choose_sq_le_support_mul_collision
#print axioms ArkLib.ProximityGap.MomentCollisionTower.moment_tower_dichotomy
