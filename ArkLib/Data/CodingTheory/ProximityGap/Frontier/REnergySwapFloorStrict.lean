/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.REnergySwapFloor

/-!
# The universal swap floor is strict beyond depth two (#466)

`REnergySwapFloor.rEnergy_ge_swap_floor` gives the universal lower bound

`2 * |G|^(m+2) - |G|^(m+1) ≤ rEnergy G (m+2)`.

This file proves that the bound cannot be sharp at depth at least three when `G` contains two
distinct elements:

> **`swap_floor_lt_rEnergy`.** If `2 ≤ |G|`, then
> `2 * |G|^(m+3) - |G|^(m+2) < rEnergy G (m+3)`.

Choose distinct `a, b ∈ G` and a tuple whose first two coordinates are `a` and whose third
coordinate is `b`.  The swap used by the floor fixes this tuple, but swapping its first and third
coordinates gives a second, distinct tuple in the same additive-energy fiber.  Thus this one fiber
strictly exceeds its floor contribution, while every other fiber satisfies the universal floor.

The result is hypothesis-free apart from nondegeneracy of `G`, and is valid in every finite field.
It is a structural permutation statement: it does not assert CORE closure, char-`p` transfer,
capacity, beyond-Johnson list decoding, or the target growth law.
-/

open Finset

namespace ArkLib.ProximityGap.SubgroupGaussSumMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The additive-energy fiber over a tuple `v`. -/
private def fiber (G : Finset F) {r : ℕ} (v : Fin r → F) : Finset (Fin r → F) :=
  (Fintype.piFinset (fun _ : Fin r => G)).filter (fun w => ∑ i, v i = ∑ i, w i)

omit [Fintype F] in
/-- `rEnergy` is the sum of the cardinalities of its additive-energy fibers. -/
private theorem rEnergy_eq_sum_fiber (G : Finset F) (r : ℕ) :
    rEnergy G r = ∑ v ∈ Fintype.piFinset (fun _ : Fin r => G), (fiber G v).card := by
  classical
  unfold rEnergy fiber
  exact Finset.sum_congr rfl (fun v _ => by rw [Finset.sum_boole]; simp)

/-- Every fiber contains the tuple and its swap of the first two coordinates. -/
private theorem fiber_card_ge (G : Finset F) {m : ℕ} {v : Fin (m + 2) → F}
    (hv : v ∈ Fintype.piFinset (fun _ : Fin (m + 2) => G)) :
    (if v 0 = v 1 then (1 : ℕ) else 2) ≤ (fiber G v).card := by
  classical
  rw [Fintype.mem_piFinset] at hv
  have hpair : ({v, swap01 v} : Finset (Fin (m + 2) → F)) ⊆ fiber G v := by
    intro w hw
    rw [Finset.mem_insert, Finset.mem_singleton] at hw
    unfold fiber
    rw [Finset.mem_filter, Fintype.mem_piFinset]
    rcases hw with rfl | rfl
    · exact ⟨fun i => hv i, rfl⟩
    · refine ⟨fun i => ?_, (sum_swap01 v).symm⟩
      show swap01 v i ∈ G
      unfold swap01
      exact hv _
  have hle := Finset.card_le_card hpair
  by_cases heq : v 0 = v 1
  · rw [if_pos heq]
    have hpos : 0 < ({v, swap01 v} : Finset (Fin (m + 2) → F)).card :=
      Finset.card_pos.mpr ⟨v, by simp⟩
    omega
  · rw [if_neg heq]
    have hcard : ({v, swap01 v} : Finset (Fin (m + 2) → F)).card = 2 :=
      Finset.card_pair (Ne.symm (swap01_ne heq))
    omega

/-- **The universal swap floor is strict beyond depth two.** If `G` has at least two elements,
then at every depth `m + 3` its additive energy strictly exceeds the swap floor. -/
theorem swap_floor_lt_rEnergy (G : Finset F) (m : ℕ) (hG : 2 ≤ G.card) :
    2 * G.card ^ (m + 3) - G.card ^ (m + 2) < rEnergy G (m + 3) := by
  classical
  obtain ⟨a, b, ha, hb, hab⟩ := Finset.one_lt_card_iff.mp (by omega : 1 < G.card)
  let two : Fin (m + 3) := ⟨2, by omega⟩
  let v : Fin (m + 3) → F := fun i => if i = two then b else a
  let w : Fin (m + 3) → F := fun i => v (Equiv.swap (0 : Fin (m + 3)) two i)
  have hzero_two : (0 : Fin (m + 3)) ≠ two := by
    intro h
    have := congrArg Fin.val h
    simp [two] at this
  have hone_two : (1 : Fin (m + 3)) ≠ two := by
    intro h
    have := congrArg Fin.val h
    simp [two] at this
  have hvmem : v ∈ Fintype.piFinset (fun _ : Fin (m + 3) => G) := by
    rw [Fintype.mem_piFinset]
    intro i
    by_cases hi : i = two
    · simpa [v, hi] using hb
    · simpa [v, hi] using ha
  have hv01 : v 0 = v 1 := by simp [v, hzero_two, hone_two]
  have hwmem : w ∈ fiber G v := by
    unfold fiber
    rw [Finset.mem_filter, Fintype.mem_piFinset]
    refine ⟨?_, ?_⟩
    · intro i
      rw [Fintype.mem_piFinset] at hvmem
      exact hvmem _
    · exact (Equiv.sum_comp (Equiv.swap (0 : Fin (m + 3)) two) v).symm
  have hvfiber : v ∈ fiber G v := by
    unfold fiber
    exact Finset.mem_filter.mpr ⟨hvmem, rfl⟩
  have hwne : w ≠ v := by
    intro h
    have h0 := congrFun h (0 : Fin (m + 3))
    have hw0 : w 0 = b := by simp [w, v, Equiv.swap_apply_left]
    have hv0 : v 0 = a := by simp [v, hzero_two]
    rw [hw0, hv0] at h0
    exact hab h0.symm
  have hstrict : (if v 0 = v 1 then (1 : ℕ) else 2) < (fiber G v).card := by
    have hsub : ({w, v} : Finset (Fin (m + 3) → F)) ⊆ fiber G v := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hwmem
      · exact hvfiber
    have hle := Finset.card_le_card hsub
    have hcard : ({w, v} : Finset (Fin (m + 3) → F)).card = 2 :=
      Finset.card_pair hwne
    rw [hcard] at hle
    rw [if_pos hv01]
    omega
  have hlt :
      ∑ x ∈ Fintype.piFinset (fun _ : Fin (m + 3) => G),
          (if x 0 = x 1 then (1 : ℕ) else 2)
        < ∑ x ∈ Fintype.piFinset (fun _ : Fin (m + 3) => G), (fiber G x).card := by
    apply Finset.sum_lt_sum (fun x hx => fiber_card_ge G hx)
    exact ⟨v, hvmem, hstrict⟩
  have hlhs :
      ∑ x ∈ Fintype.piFinset (fun _ : Fin (m + 3) => G),
          (if x 0 = x 1 then (1 : ℕ) else 2)
        = 2 * G.card ^ (m + 3) - G.card ^ (m + 2) := by
    have hcard_pi : (Fintype.piFinset (fun _ : Fin (m + 3) => G)).card =
        G.card ^ (m + 3) := by
      rw [Fintype.card_piFinset_const]
    have hpoint : ∀ x : Fin (m + 3) → F, (if x 0 = x 1 then (1 : ℕ) else 2) =
        2 - (if x 0 = x 1 then 1 else 0) := by
      intro x
      by_cases h : x 0 = x 1 <;> simp [h]
    simp_rw [hpoint]
    rw [Finset.sum_tsub_distrib _ (fun x _ => by
      by_cases h : x 0 = x 1 <;> simp [h])]
    rw [Finset.sum_const, hcard_pi, smul_eq_mul]
    have hcount :
        ∑ x ∈ Fintype.piFinset (fun _ : Fin (m + 3) => G),
            (if x 0 = x 1 then (1 : ℕ) else 0) = G.card ^ (m + 2) := by
      rw [Finset.sum_boole]
      simp only [Nat.cast_id]
      exact eqPair_count G (m + 1)
    rw [hcount, Nat.mul_comm]
  rw [hlhs, ← rEnergy_eq_sum_fiber] at hlt
  exact hlt

end ArkLib.ProximityGap.SubgroupGaussSumMoment

-- Axiom audit: must be `[propext, Classical.choice, Quot.sound]` only (no `sorryAx`).
#print axioms ArkLib.ProximityGap.SubgroupGaussSumMoment.swap_floor_lt_rEnergy
