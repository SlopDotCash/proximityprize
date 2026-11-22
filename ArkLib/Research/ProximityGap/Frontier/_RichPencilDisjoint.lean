/-
Copyright (c) 2026 Mikhail Izhutkin. All rights reserved.
Released under both MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Mikhail Izhutkin (mashingaan)
-/
import ArkLib.Research.ProximityGap.Frontier._IncidenceDependencyArithmetic

/-!
# Rich pencils are disjoint below half distance

If two rich pencils meet at a selected head, their four other heads alone pay
twice the distance. The shared head need not have any prescribed error weight.
-/

open scoped BigOperators

namespace ProximityGap.RichPencilDisjoint

open ProximityGap.IncidenceDependencyArithmetic

/-- Two distinct affine code pencils sharing a head and having two nearby
evaluations each require twice the radius to reach the code distance. -/
theorem distance_le_twice_radius_of_meeting_rich_pencils {F X : Type*}
    [Field F] [Fintype X] [DecidableEq X] (C : Submodule F (X → F))
    (u₀ u₁ U V U' V' : X → F) (a b c d e : F) (D t : ℕ)
    (hU : U ∈ C) (hV : V ∈ C) (hU' : U' ∈ C) (hV' : V' ∈ C)
    (hne : (U, V) ≠ (U', V'))
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (had : a ≠ d) (hae : a ≠ e) (hde : d ≠ e)
    (hmeet : ∀ x, U x + a * V x = U' x + a * V' x)
    (hb : (affineHeadErrors u₀ u₁ U V b).card ≤ t)
    (hc : (affineHeadErrors u₀ u₁ U V c).card ≤ t)
    (hd : (affineHeadErrors u₀ u₁ U' V' d).card ≤ t)
    (he : (affineHeadErrors u₀ u₁ U' V' e).card ≤ t)
    (hdistance : ∀ v ∈ C, ∀ B : Finset X, B.card < D →
      (∀ x ∉ B, v x = 0) → v = 0) : D ≤ 2 * t := by
  classical
  let S := affineErrorSupport u₀ u₁ U V
  let T := affineErrorSupport u₀ u₁ U' V'
  let H := affineHeadErrors u₀ u₁ U V a
  let B := affineHeadErrors u₀ u₁ U V b
  let K := affineHeadErrors u₀ u₁ U V c
  let L := affineHeadErrors u₀ u₁ U' V' d
  let M := affineHeadErrors u₀ u₁ U' V' e
  have hH : affineHeadErrors u₀ u₁ U' V' a = H := by
    ext x
    simp [H, affineHeadErrors, hmeet x]
  have hHS : H ⊆ S := by
    intro x hx
    by_contra hn
    have h : u₀ x = U x ∧ u₁ x = V x := by
      simpa [S, affineErrorSupport, not_or] using hn
    simpa [H, affineHeadErrors, h.1, h.2] using hx
  have hHT : H ⊆ T := by
    rw [← hH]
    intro x hx
    by_contra hn
    have h : u₀ x = U' x ∧ u₁ x = V' x := by
      simpa [T, affineErrorSupport, not_or] using hn
    simpa [affineHeadErrors, h.1, h.2] using hx
  have sB : S ⊆ H ∪ B := affine_support_pair_cover u₀ u₁ U V a b hab
  have sK : S ⊆ H ∪ K := affine_support_pair_cover u₀ u₁ U V a c hac
  have sBK : S ⊆ B ∪ K := affine_support_pair_cover u₀ u₁ U V b c hbc
  have tL : T ⊆ H ∪ L := by
    rw [← hH]
    exact affine_support_pair_cover u₀ u₁ U' V' a d had
  have tM : T ⊆ H ∪ M := by
    rw [← hH]
    exact affine_support_pair_cover u₀ u₁ U' V' a e hae
  have tLM : T ⊆ L ∪ M := affine_support_pair_cover u₀ u₁ U' V' d e hde
  have charge (x : X) :
      (if x ∈ S ∪ T then 2 else 0) ≤
        (if x ∈ B then 1 else 0) + (if x ∈ K then 1 else 0) +
        (if x ∈ L then 1 else 0) + (if x ∈ M then 1 else 0) := by
    by_cases hz : x ∈ H
    · have h₁ := Finset.mem_union.mp (sBK (hHS hz))
      have h₂ := Finset.mem_union.mp (tLM (hHT hz))
      by_cases hxB : x ∈ B
      all_goals by_cases hxK : x ∈ K
      all_goals by_cases hxL : x ∈ L
      all_goals by_cases hxM : x ∈ M
      all_goals simp [hxB, hxK, hxL, hxM, Finset.mem_union, hHS hz] at h₁ h₂ ⊢
    · by_cases hs : x ∈ S
      · have hxB := (Finset.mem_union.mp (sB hs)).resolve_left hz
        have hxK := (Finset.mem_union.mp (sK hs)).resolve_left hz
        simp only [Finset.mem_union, hs, true_or, if_true, hxB, hxK]
        omega
      · by_cases ht : x ∈ T
        · have hxL := (Finset.mem_union.mp (tL ht)).resolve_left hz
          have hxM := (Finset.mem_union.mp (tM ht)).resolve_left hz
          simp only [Finset.mem_union, ht, or_true, if_true, hxL, hxM]
          omega
        · simp [Finset.mem_union, hs, ht]
  have sumCharge := Finset.sum_le_sum (s := (Finset.univ : Finset X)) (fun x _ ↦ charge x)
  have count (A : Finset X) (k : ℕ) :
      (∑ x : X, if x ∈ A then k else 0) = A.card * k := by
    simp [Finset.sum_ite]
  simp only [Finset.sum_add_distrib, count, mul_one] at sumCharge
  have sep : D ≤ (S ∪ T).card :=
    le_union_card_of_distinct_code_pencils C u₀ u₁ U V U' V' S T D hU hV hU' hV'
      (fun x hx ↦ by simpa [S, affineErrorSupport, not_or, eq_comm] using hx)
      (fun x hx ↦ by simpa [T, affineErrorSupport, not_or, eq_comm] using hx)
      hne hdistance
  change B.card ≤ t at hb
  change K.card ≤ t at hc
  change L.card ≤ t at hd
  change M.card ≤ t at he
  omega

end ProximityGap.RichPencilDisjoint

#print axioms ProximityGap.RichPencilDisjoint.distance_le_twice_radius_of_meeting_rich_pencils
