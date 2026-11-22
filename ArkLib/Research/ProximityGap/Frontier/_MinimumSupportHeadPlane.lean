/-
Copyright (c) 2026 Mikhail Izhutkin. All rights reserved.
Released under both MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Mikhail Izhutkin (mashingaan)
-/
import Mathlib.Tactic

/-!
# Affine heads on a minimum-distance support

Relative to a code pencil agreeing with the received pencil off a minimum
support, every decoded head with errors in that support differs by a scalar
multiple of one residual codeword. Agreement at any coordinate of the support
then cuts a single affine line in the resulting two-parameter family.
-/

open scoped BigOperators

set_option autoImplicit false

namespace ProximityGap.MinimumSupportHeadPlane

/-- A nonzero word on a minimum support spans all codewords on that support. -/
theorem residual_on_minimum_support {F X : Type*} [Field F] [DecidableEq X]
    (C : Submodule F (X → F)) (S : Finset X) (D : ℕ) (hS : S.card = D)
    (hdist : ∀ v ∈ C, ∀ B : Finset X, B.card < D → (∀ x ∉ B, v x = 0) → v = 0)
    (v w : X → F) (hv : v ∈ C) (hw : w ∈ C) (hv0 : v ≠ 0)
    (hvS : ∀ x ∉ S, v x = 0) (hwS : ∀ x ∉ S, w x = 0) :
    (∀ x ∈ S, v x ≠ 0) ∧ ∃ a : F, w = a • v := by
  classical
  have vanishes {z : X → F} (hz : z ∈ C) (hzS : ∀ x ∉ S, z x = 0)
      {p : X} (hp : p ∈ S) (hzp : z p = 0) : z = 0 := by
    refine hdist z hz (S.erase p) ?_ ?_
    · rw [Finset.card_erase_of_mem hp, hS]
      have hc := Finset.card_pos.mpr ⟨p, hp⟩
      omega
    · intro x hx
      by_cases hxp : x = p
      · subst x
        exact hzp
      · exact hzS x (fun hxS => hx (Finset.mem_erase.mpr ⟨hxp, hxS⟩))
  have hvnz : ∀ x ∈ S, v x ≠ 0 := fun x hx h => hv0 (vanishes hv hvS hx h)
  have hSnonempty : S.Nonempty := by
    by_contra h
    apply hv0
    funext x
    exact hvS x (fun hx => h ⟨x, hx⟩)
  obtain ⟨p, hp⟩ := hSnonempty
  let a := w p / v p
  refine ⟨hvnz, a, sub_eq_zero.mp (vanishes (C.sub_mem hw (C.smul_mem a hv)) ?_ hp ?_)⟩
  · intro x hx
    simp [Pi.sub_apply, Pi.smul_apply, hvS x hx, hwS x hx]
  · change w p - a * v p = 0
    rw [show a * v p = w p from div_mul_cancel₀ _ (hvnz p hp), sub_self]

/-- All decoded heads supported relative to one code pencil have the same residual direction. -/
theorem affine_heads_on_minimum_support {F X I : Type*} [Field F] [DecidableEq X]
    (C : Submodule F (X → F)) (S : Finset X) (D : ℕ) (hS : S.card = D)
    (hdist : ∀ v ∈ C, ∀ B : Finset X, B.card < D → (∀ x ∉ B, v x = 0) → v = 0)
    (U V v : X → F) (hU : U ∈ C) (hV : V ∈ C) (hv : v ∈ C) (hv0 : v ≠ 0)
    (hvS : ∀ x ∉ S, v x = 0) (γ : I → F) (w : I → X → F) (hw : ∀ i, w i ∈ C)
    (hoff : ∀ i x, x ∉ S → w i x = U x + γ i * V x) :
    (∀ x ∈ S, v x ≠ 0) ∧ ∃ a : I → F, ∀ i, w i = U + γ i • V + a i • v := by
  classical
  have hfull := (residual_on_minimum_support C S D hS hdist v v hv hv hv0 hvS hvS).1
  refine ⟨hfull, ?_⟩
  have hfit (i : I) : ∃ a : F, w i = U + γ i • V + a • v := by
    let r := w i - (U + γ i • V)
    have hr : r ∈ C := C.sub_mem (hw i) (C.add_mem hU (C.smul_mem (γ i) hV))
    have hrS (x : X) (hx : x ∉ S) : r x = 0 := by
      change w i x - (U x + γ i * V x) = 0
      rw [hoff i x hx, sub_self]
    obtain ⟨a, ha⟩ := (residual_on_minimum_support C S D hS hdist v r hv hr hv0 hvS hrS).2
    exact ⟨a, (sub_eq_iff_eq_add.mp ha).trans (add_comm _ _)⟩
  choose a ha using hfit
  exact ⟨a, ha⟩

/-- The agreement condition on one coordinate is affine in the head parameter. -/
theorem agreement_on_residual_line {F : Type*} [Field F]
    (u₀ u₁ U V v γ a : F) (hv : v ≠ 0) :
    U + γ * V + a * v = u₀ + γ * u₁ ↔
      a = (u₀ - U) / v + γ * ((u₁ - V) / v) := by
  rw [← mul_div_assoc, ← add_div, eq_div_iff hv]
  constructor
  · intro h
    linear_combination h
  · intro h
    linear_combination h

/-- Tight triples sharing an edge separate by the distance margin if each
cross triple also satisfies the distance lower bound. -/
theorem tight_support_separation {X : Type*} [Fintype X] [DecidableEq X]
    (A B C E : Finset X) (D t : ℕ)
    (hA : A.card ≤ t) (hB : B.card ≤ t) (hC : C.card ≤ t) (hE : E.card ≤ t)
    (hACE : D ≤ ((A ∪ C) ∪ E).card) (hBCE : D ≤ ((B ∪ C) ∪ E).card)
    (hABC : ((A ∪ B) ∪ C).card = D) (hABE : ((A ∪ B) ∪ E).card = D) :
    D ≤ 2 * t + (((A ∪ B) ∪ C) \ ((A ∪ B) ∪ E)).card := by
  classical
  let S := (A ∪ B) ∪ C
  let T := (A ∪ B) ∪ E
  have charge (x : X) :
      (if x ∈ (A ∪ C) ∪ E then 1 else 0) + (if x ∈ (B ∪ C) ∪ E then 1 else 0) ≤
        (if x ∈ A then 1 else 0) + (if x ∈ B then 1 else 0) +
        (if x ∈ C then 1 else 0) + (if x ∈ E then 1 else 0) +
        (if x ∈ S \ T then 1 else 0) + (if x ∈ T \ S then 1 else 0) := by
    by_cases ha : x ∈ A
    all_goals by_cases hb : x ∈ B
    all_goals by_cases hc : x ∈ C
    all_goals by_cases he : x ∈ E
    all_goals simp [S, T, Finset.mem_union, Finset.mem_sdiff, ha, hb, hc, he]
  have summed := Finset.sum_le_sum (s := (Finset.univ : Finset X)) (fun x _ ↦ charge x)
  have count (P : Finset X) : (∑ x : X, if x ∈ P then 1 else 0) = P.card := by simp
  simp only [Finset.sum_add_distrib, count] at summed
  have split (P Q : Finset X) : (P \ Q).card + (P ∩ Q).card = P.card := by
    have h : P \ (P ∩ Q) = P \ Q := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_inter]
      tauto
    rw [← h]
    exact Finset.card_sdiff_add_card_eq_card Finset.inter_subset_left
  have splitS := split S T
  have splitT := split T S
  rw [Finset.inter_comm T S] at splitT
  change S.card = D at hABC
  change T.card = D at hABE
  change D ≤ 2 * t + (S \ T).card
  omega

end ProximityGap.MinimumSupportHeadPlane

#print axioms ProximityGap.MinimumSupportHeadPlane.residual_on_minimum_support
#print axioms ProximityGap.MinimumSupportHeadPlane.agreement_on_residual_line
#print axioms ProximityGap.MinimumSupportHeadPlane.affine_heads_on_minimum_support
#print axioms ProximityGap.MinimumSupportHeadPlane.tight_support_separation
