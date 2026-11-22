/-
Copyright (c) 2026 Mikhail Izhutkin. All rights reserved.
Released under both MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Mikhail Izhutkin (mashingaan)
-/
import ArkLib.Research.ProximityGap.Frontier._IncidenceDependencyArithmetic

/-!
# Error incidence on a cycle of affine triples

A pencil indexed by i uses its private head and the heads on its incoming and
outgoing edges. At an exceptional coordinate at least two of these three heads
are erroneous. Charge the union for each neighboring pair against those heads.
-/

open scoped BigOperators

namespace ProximityGap.RichPencilCycleBudget

/-- The natural-number indicator of a decidable proposition. -/
def bit (p : Prop) [Decidable p] : ℕ := if p then 1 else 0

/-- The adjacent exception unions charge each private or shared head only once. -/
theorem adjacent_exception_mass_le {I X : Type*} [Fintype I] [Fintype X]
    [DecidableEq X] (σ : Equiv.Perm I) (S P H : I → Finset X)
    (hlocal : ∀ i x, x ∈ S i → 2 ≤
      bit (x ∈ P i) + bit (x ∈ H i) + bit (x ∈ H (σ.symm i))) :
    (∑ i, (S i ∪ S (σ i)).card) ≤ (∑ i, (P i).card) + ∑ i, (H i).card := by
  classical
  have point (x : X) :
      (∑ i, bit (x ∈ S i ∪ S (σ i))) ≤
        (∑ i, bit (x ∈ P i)) + ∑ i, bit (x ∈ H i) := by
    let a : I → ℕ := fun i ↦ bit (x ∈ S i)
    let p : I → ℕ := fun i ↦ bit (x ∈ P i)
    let h : I → ℕ := fun i ↦ bit (x ∈ H i)
    have localCharge (i : I) :
        2 * a i ≤ p i + a i * h i + a i * h (σ.symm i) := by
      by_cases hi : x ∈ S i
      · simpa [a, p, h, bit, hi] using hlocal i x hi
      · simp [a, bit, hi]
    have bridgeCharge (i : I) :
        a i * h i + a (σ i) * h i ≤ h i + a i * a (σ i) := by
      by_cases hi : x ∈ S i
      all_goals by_cases hj : x ∈ S (σ i)
      all_goals by_cases hk : x ∈ H i
      all_goals simp [a, h, bit, hi, hj, hk]
    have cover (i : I) :
        bit (x ∈ S i ∪ S (σ i)) + a i * a (σ i) = a i + a (σ i) := by
      by_cases hi : x ∈ S i
      all_goals by_cases hj : x ∈ S (σ i)
      all_goals simp [a, bit, Finset.mem_union, hi, hj]
    have shift :
        (∑ i, a i * h (σ.symm i)) = ∑ i, a (σ i) * h i := by
      simpa only [Equiv.symm_apply_apply] using
        (Equiv.sum_comp σ (fun i ↦ a i * h (σ.symm i))).symm
    have h₁ := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ localCharge i)
    have h₂ := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ bridgeCharge i)
    have h₃ : (∑ i, (bit (x ∈ S i ∪ S (σ i)) + a i * a (σ i))) =
        ∑ i, (a i + a (σ i)) := Finset.sum_congr rfl (fun i _ ↦ cover i)
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, shift, Equiv.sum_comp σ a] at h₁ h₂ h₃
    change (∑ i, bit (x ∈ S i ∪ S (σ i))) ≤ (∑ i, p i) + ∑ i, h i
    omega
  have count (A : Finset X) : (∑ x : X, bit (x ∈ A)) = A.card := by
    simp [bit, Finset.sum_ite]
  have total (A : I → Finset X) :
      (∑ x : X, ∑ i : I, bit (x ∈ A i)) = ∑ i, (A i).card := by
    rw [Finset.sum_comm]
    simp only [count]
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset X)) (fun x _ ↦ point x)
  rw [Finset.sum_add_distrib, total, total, total] at hs
  exact hs

/-- A cyclic family with one private and one shared error row per pencil requires
at least half the pairwise distance budget as its per-head error radius. -/
theorem distance_le_twice_radius_of_cycle {I X : Type*} [Fintype I] [Nonempty I]
    [Fintype X] [DecidableEq X] (σ : Equiv.Perm I) (S P H : I → Finset X)
    (D t : ℕ) (hlocal : ∀ i x, x ∈ S i → 2 ≤
      bit (x ∈ P i) + bit (x ∈ H i) + bit (x ∈ H (σ.symm i)))
    (hpair : ∀ i, D ≤ (S i ∪ S (σ i)).card)
    (hP : ∀ i, (P i).card ≤ t) (hH : ∀ i, (H i).card ≤ t) : D ≤ 2 * t := by
  classical
  have ha := adjacent_exception_mass_le σ S P H hlocal
  have hd := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hpair i)
  have hp := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hP i)
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hH i)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hd hp hh
  have hb : Fintype.card I * D ≤ Fintype.card I * (2 * t) := by
    rw [Nat.mul_comm 2 t, ← Nat.mul_assoc, Nat.mul_two]
    exact hd.trans (ha.trans (Nat.add_le_add hp hh))
  exact Nat.le_of_mul_le_mul_left hb Fintype.card_pos

open ProximityGap.IncidenceDependencyArithmetic

/-- The cycle bound applies to three distinct evaluations of each affine pencil.
The shared head is counted by its outgoing pencil, using the meeting equation
to identify it with the incoming evaluation of the successor. -/
theorem distance_le_twice_radius_of_affine_cycle {F I X : Type*} [Field F]
    [Fintype I] [Nonempty I] [Fintype X] [DecidableEq X]
    (σ : Equiv.Perm I) (u₀ u₁ : X → F) (U V : I → X → F)
    (p a : I → F) (D t : ℕ)
    (hlabels : ∀ i, p i ≠ a i ∧ p i ≠ a (σ.symm i) ∧ a i ≠ a (σ.symm i))
    (hmeet : ∀ i x, U i x + a i * V i x = U (σ i) x + a i * V (σ i) x)
    (hpair : ∀ i, D ≤ ((affineErrorSupport u₀ u₁ (U i) (V i)) ∪
        (affineErrorSupport u₀ u₁ (U (σ i)) (V (σ i)))).card)
    (hp : ∀ i, (affineHeadErrors u₀ u₁ (U i) (V i) (p i)).card ≤ t)
    (ha : ∀ i, (affineHeadErrors u₀ u₁ (U i) (V i) (a i)).card ≤ t) :
    D ≤ 2 * t := by
  classical
  let S := fun i ↦ affineErrorSupport u₀ u₁ (U i) (V i)
  let P := fun i ↦ affineHeadErrors u₀ u₁ (U i) (V i) (p i)
  let H := fun i ↦ affineHeadErrors u₀ u₁ (U i) (V i) (a i)
  have hincoming (i : I) :
      H (σ.symm i) = affineHeadErrors u₀ u₁ (U i) (V i) (a (σ.symm i)) := by
    ext x
    have h := hmeet (σ.symm i) x
    simp only [Equiv.apply_symm_apply] at h
    simp [H, affineHeadErrors, h]
  refine distance_le_twice_radius_of_cycle σ S P H D t ?_ hpair hp ha
  intro i x hx
  obtain ⟨hpa, hpb, hab⟩ := hlabels i
  have pair (b c : F) (hne : b ≠ c) :
      x ∈ affineHeadErrors u₀ u₁ (U i) (V i) b ∨
        x ∈ affineHeadErrors u₀ u₁ (U i) (V i) c :=
    Finset.mem_union.mp (affine_support_pair_cover u₀ u₁ (U i) (V i) b c hne hx)
  have h01 : x ∈ P i ∨ x ∈ H i := pair _ _ hpa
  have h02 : x ∈ P i ∨ x ∈ H (σ.symm i) := by
    rw [hincoming i]
    exact pair _ _ hpb
  have h12 : x ∈ H i ∨ x ∈ H (σ.symm i) := by
    rw [hincoming i]
    exact pair _ _ hab
  by_cases hP : x ∈ P i
  all_goals by_cases hH : x ∈ H i
  all_goals by_cases hI : x ∈ H (σ.symm i)
  all_goals simp [bit, hP, hH, hI] at h01 h02 h12 ⊢


/-- A path is represented by omitting the last-to-first distance constraint.
The bridge row on that edge can combine the two extra private endpoint rows,
so its budget is twice the radius. -/
theorem path_distance_budget {I X : Type*} [Fintype I] [Fintype X] [DecidableEq X]
    (σ : Equiv.Perm I) (S P H : I → Finset X) (last : I) (D t : ℕ)
    (hlocal : ∀ i x, x ∈ S i → 2 ≤
      bit (x ∈ P i) + bit (x ∈ H i) + bit (x ∈ H (σ.symm i)))
    (hpair : ∀ i, i ≠ last → D ≤ (S i ∪ S (σ i)).card)
    (hP : ∀ i, (P i).card ≤ t)
    (hH : ∀ i, i ≠ last → (H i).card ≤ t)
    (hLast : (H last).card ≤ 2 * t) :
    (Fintype.card I - 1) * D ≤ (2 * Fintype.card I + 1) * t := by
  classical
  let rest := (Finset.univ : Finset I).erase last
  let pairSize (i : I) := (S i ∪ S (σ i)).card
  have restCard : rest.card = Fintype.card I - 1 := by
    simp [rest]
  have lower : (Fintype.card I - 1) * D ≤ ∑ i ∈ rest, pairSize i := by
    calc
      _ = ∑ _i ∈ rest, D := by simp [restCard]
      _ ≤ _ := Finset.sum_le_sum fun i hi ↦ hpair i (Finset.mem_erase.mp hi).1
  have extend : (∑ i ∈ rest, pairSize i) ≤ ∑ i, pairSize i := by
    rw [← Finset.sum_erase_add Finset.univ pairSize (Finset.mem_univ last)]
    exact Nat.le_add_right _ _
  have privateUpper : (∑ i, (P i).card) ≤ Fintype.card I * t := by
    calc
      _ ≤ ∑ _i : I, t := Finset.sum_le_sum fun i _ ↦ hP i
      _ = _ := by simp
  have sharedUpper : (∑ i, (H i).card) ≤ (Fintype.card I - 1) * t + 2 * t := by
    rw [← Finset.sum_erase_add Finset.univ (fun i ↦ (H i).card) (Finset.mem_univ last)]
    apply Nat.add_le_add _ hLast
    calc
      _ ≤ ∑ _i ∈ rest, t :=
        Finset.sum_le_sum fun i hi ↦ hH i (Finset.mem_erase.mp hi).1
      _ = _ := by simp [restCard]
  have hpos : 0 < Fintype.card I := Fintype.card_pos_iff.mpr ⟨last⟩
  have hcard : (Fintype.card I - 1) + 1 = Fintype.card I := by omega
  have heq : Fintype.card I * t + ((Fintype.card I - 1) * t + 2 * t) =
      (2 * Fintype.card I + 1) * t := by
    have hm := congrArg (fun k : ℕ ↦ k * t) hcard
    simp only [Nat.add_mul, one_mul, two_mul] at hm ⊢
    omega
  calc
    _ ≤ ∑ i, pairSize i := lower.trans extend
    _ ≤ (∑ i, (P i).card) + ∑ i, (H i).card :=
      adjacent_exception_mass_le σ S P H hlocal
    _ ≤ _ := by
      rw [← heq]
      exact Nat.add_le_add privateUpper sharedUpper

/-- The path budget limits the number of rich pencils at the current first
sponsor radius, once the path has been encoded with its two endpoint rows. -/
theorem first_sponsor_path_card_le_eight (m : ℕ)
    (h : (m - 1) * 536870913 ≤ (2 * m + 1) * 221512373) : m ≤ 8 := by
  omega


/-- For a path of affine triples, the endpoint evaluations are absorbed into the
exceptional bridge row. Every other bridge joins equal evaluations. -/
theorem affine_path_distance_budget {F I X : Type*} [Field F] [Fintype I]
    [Fintype X] [DecidableEq X] (σ : Equiv.Perm I) (last : I)
    (u₀ u₁ : X → F) (U V : I → X → F) (p a b : I → F) (D t : ℕ)
    (hlabels : ∀ i, p i ≠ a i ∧ p i ≠ b i ∧ a i ≠ b i)
    (hmeet : ∀ i, i ≠ last → ∀ x,
      U i x + a i * V i x = U (σ i) x + b (σ i) * V (σ i) x)
    (C : Submodule F (X → F))
    (hU : ∀ i, U i ∈ C) (hV : ∀ i, V i ∈ C)
    (hdistinct : ∀ i, i ≠ last → (U i, V i) ≠ (U (σ i), V (σ i)))
    (hdistance : ∀ v ∈ C, ∀ E : Finset X, E.card < D →
      (∀ x ∉ E, v x = 0) → v = 0)
    (hscalar : ∀ i, i ≠ last → a i = b (σ i))
    (hp : ∀ i, (affineHeadErrors u₀ u₁ (U i) (V i) (p i)).card ≤ t)
    (ha : ∀ i, (affineHeadErrors u₀ u₁ (U i) (V i) (a i)).card ≤ t)
    (hb : ∀ i, (affineHeadErrors u₀ u₁ (U i) (V i) (b i)).card ≤ t) :
    (Fintype.card I - 1) * D ≤ (2 * Fintype.card I + 1) * t := by
  classical
  let S i := affineErrorSupport u₀ u₁ (U i) (V i)
  let P i := affineHeadErrors u₀ u₁ (U i) (V i) (p i)
  let A i := affineHeadErrors u₀ u₁ (U i) (V i) (a i)
  let B i := affineHeadErrors u₀ u₁ (U i) (V i) (b i)
  let H i := if i = last then A i ∪ B (σ i) else A i
  have outgoing (i : I) : A i ⊆ H i := by
    by_cases hi : i = last
    · intro x hx
      simpa only [H, if_pos hi] using (Finset.mem_union.mpr (Or.inl hx) :
        x ∈ A i ∪ B (σ i))
    · simp [H, hi]
  have incoming (i : I) : B (σ i) ⊆ H i := by
    by_cases hi : i = last
    · intro x hx
      simpa only [H, if_pos hi] using (Finset.mem_union.mpr (Or.inr hx) :
        x ∈ A i ∪ B (σ i))
    · have he : A i = B (σ i) := by
        ext x
        have h := hmeet i hi x
        rw [hscalar i hi] at h
        simp [A, B, affineHeadErrors, hscalar i hi, h]
      simp [H, hi, he]
  have agree (i : I) : ∀ x ∉ S i, U i x = u₀ x ∧ V i x = u₁ x := by
    intro x hx
    simpa [S, affineErrorSupport, not_or, eq_comm] using hx
  have hpair (i : I) (hi : i ≠ last) : D ≤ (S i ∪ S (σ i)).card :=
    le_union_card_of_distinct_code_pencils C u₀ u₁ (U i) (V i) (U (σ i)) (V (σ i))
      (S i) (S (σ i)) D (hU i) (hV i) (hU (σ i)) (hV (σ i))
      (agree i) (agree (σ i)) (hdistinct i hi) hdistance
  refine path_distance_budget σ S P H last D t ?_ hpair hp ?_ ?_
  · intro i x hx
    obtain ⟨hpa, hpb, hab⟩ := hlabels i
    have hin : B i ⊆ H (σ.symm i) := by
      simpa only [Equiv.apply_symm_apply] using incoming (σ.symm i)
    have pair (c d : F) (hne : c ≠ d) :
        x ∈ affineHeadErrors u₀ u₁ (U i) (V i) c ∨
          x ∈ affineHeadErrors u₀ u₁ (U i) (V i) d :=
      Finset.mem_union.mp (affine_support_pair_cover u₀ u₁ (U i) (V i) c d hne hx)
    have h01 : x ∈ P i ∨ x ∈ H i := (pair _ _ hpa).imp id (outgoing i)
    have h02 : x ∈ P i ∨ x ∈ H (σ.symm i) := (pair _ _ hpb).imp id hin
    have h12 : x ∈ H i ∨ x ∈ H (σ.symm i) := (pair _ _ hab).imp (outgoing i) hin
    by_cases hP : x ∈ P i
    all_goals by_cases hH : x ∈ H i
    all_goals by_cases hI : x ∈ H (σ.symm i)
    all_goals simp [bit, hP, hH, hI] at h01 h02 h12 ⊢
  · intro i hi
    simpa only [H, if_neg hi] using ha i
  · simp only [H, if_pos rfl, two_mul]
    exact (Finset.card_union_le _ _).trans (Nat.add_le_add (ha last) (hb (σ last)))

end ProximityGap.RichPencilCycleBudget

#print axioms ProximityGap.RichPencilCycleBudget.adjacent_exception_mass_le
#print axioms ProximityGap.RichPencilCycleBudget.distance_le_twice_radius_of_cycle

#print axioms ProximityGap.RichPencilCycleBudget.distance_le_twice_radius_of_affine_cycle
#print axioms ProximityGap.RichPencilCycleBudget.path_distance_budget
#print axioms ProximityGap.RichPencilCycleBudget.first_sponsor_path_card_le_eight
#print axioms ProximityGap.RichPencilCycleBudget.affine_path_distance_budget
