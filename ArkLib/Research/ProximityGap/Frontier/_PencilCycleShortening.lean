/-
Copyright (c) 2026 Mikhail Izhutkin. All rights reserved.
Released under both MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Mikhail Izhutkin (mashingaan)
-/
import Mathlib.Tactic

/-!
# Shortening cycles of meeting affine code pencils

Each meeting scalar expresses the intercept jump as a scalar multiple of the
slope jump. Crossing a closed cycle gives two equations in the slope jumps.
Two jumps at different meeting scalars can therefore be recovered from the
remaining jumps, inside any submodule containing them.
-/

open scoped BigOperators

namespace ProximityGap.PencilCycleShortening

/-- Two distinct meeting scalars let a closed pencil cycle eliminate two slope
jumps. Any submodule containing the remaining slope jumps contains all of them.
The two closure equations are the telescoping sums of the slopes and intercepts. -/
private theorem pencilCycle_slope_mem_of_erase_two {F I M : Type*} [Field F]
    [DecidableEq I] [AddCommGroup M] [Module F M]
    (s : Finset I) (γ : I → F) (v : I → M) (W : Submodule F M)
    (a b : I) (ha : a ∈ s) (hb : b ∈ s) (hab : γ a ≠ γ b)
    (hslopes : ∑ i ∈ s, v i = 0)
    (hintercepts : ∑ i ∈ s, γ i • v i = 0)
    (hrest : ∀ i ∈ s, i ≠ a → i ≠ b → v i ∈ W) :
    ∀ i ∈ s, v i ∈ W := by
  have recover (j k : I) (hj : j ∈ s) (hjk : γ j ≠ γ k)
      (hother : ∀ i ∈ s, i ≠ j → i ≠ k → v i ∈ W) : v j ∈ W := by
    have hz : ∑ i ∈ s, (γ i - γ k) • v i = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, ← Finset.smul_sum,
        hintercepts, hslopes, smul_zero, sub_zero]
    have hsum : (∑ i ∈ s.erase j, (γ i - γ k) • v i) ∈ W := by
      apply W.sum_mem
      intro i hi
      obtain ⟨hij, his⟩ := Finset.mem_erase.mp hi
      by_cases hik : i = k
      · subst i
        simpa only [sub_self, zero_smul] using W.zero_mem
      · exact W.smul_mem _ (hother i his hij hik)
    have hsplit := Finset.sum_erase_add s (fun i ↦ (γ i - γ k) • v i) hj
    rw [hz] at hsplit
    have heq : (γ j - γ k) • v j = -(∑ i ∈ s.erase j, (γ i - γ k) • v i) :=
      eq_neg_of_add_eq_zero_right hsplit
    have hscaled : (γ j - γ k) • v j ∈ W := by
      rw [heq]
      exact W.neg_mem hsum
    have hin := W.smul_mem (γ j - γ k)⁻¹ hscaled
    simpa only [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hjk), one_smul] using hin
  intro i hi
  by_cases hia : i = a
  · subst i
    exact recover a b ha hab hrest
  · by_cases hib : i = b
    · subst i
      exact recover b a hb hab.symm (fun j hj hjb hja ↦ hrest j hj hja hjb)
    · exact hrest i hi hia hib


/-- For an indexed cycle of affine pencils meeting their successors, two slope
jumps at distinct meeting scalars can be omitted when shortening the cycle.
All slope and intercept jumps lie in any submodule containing the others. -/
theorem pencilCycle_jumps_mem {F I M : Type*} [Field F] [Fintype I]
    [AddCommGroup M] [Module F M] (σ : Equiv.Perm I)
    (γ : I → F) (U V : I → M) (W : Submodule F M) (a b : I)
    (hab : γ a ≠ γ b)
    (hmeet : ∀ i, U i + γ i • V i = U (σ i) + γ i • V (σ i))
    (hrest : ∀ i, i ≠ a → i ≠ b → V (σ i) - V i ∈ W) :
    ∀ i, (V (σ i) - V i ∈ W) ∧ (U i - U (σ i) ∈ W) := by
  classical
  have hscaled (i : I) : γ i • (V (σ i) - V i) = U i - U (σ i) := by
    rw [smul_sub]
    calc
      γ i • V (σ i) - γ i • V i =
          (U (σ i) + γ i • V (σ i)) - (U (σ i) + γ i • V i) := by abel
      _ = U i - U (σ i) := by
        rw [← hmeet i]
        abel
  have hs : (∑ i : I, (V (σ i) - V i)) = 0 := by
    rw [Finset.sum_sub_distrib, Equiv.sum_comp σ V, sub_self]
  have hu : (∑ i : I, γ i • (V (σ i) - V i)) = 0 := by
    simp only [hscaled, Finset.sum_sub_distrib, Equiv.sum_comp σ U, sub_self]
  have hmem := pencilCycle_slope_mem_of_erase_two Finset.univ γ
    (fun i ↦ V (σ i) - V i) W a b (Finset.mem_univ a) (Finset.mem_univ b)
    hab hs hu (fun i _ ↦ hrest i)
  intro i
  have hi := hmem i (Finset.mem_univ i)
  exact ⟨hi, hscaled i ▸ W.smul_mem _ hi⟩

end ProximityGap.PencilCycleShortening

#print axioms ProximityGap.PencilCycleShortening.pencilCycle_jumps_mem
