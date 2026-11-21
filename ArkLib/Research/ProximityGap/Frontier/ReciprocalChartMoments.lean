/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.ReciprocalTupleEnergy
import ArkLib.Research.ProximityGap.Frontier.REnergySwapFloorSidonIff

/-! # Additive energy of a projectively equivalent Reed–Solomon domain -/
set_option autoImplicit false
namespace ProximityGap.ReciprocalChartMoments
open Finset ReciprocalTupleEnergy ReciprocalChartMCA
open ArkLib.ProximityGap.SubgroupGaussSumMoment
variable {I F : Type} [Fintype I] [DecidableEq I] [Field F] [Fintype F] [DecidableEq F]

omit [DecidableEq I] [Fintype F] in
/-- If equal sums on an indexed domain only come from permutations, its
r-fold energy is at most the number of ordered tuples times r!. -/
theorem energy_bound (y : I ↪ F) (r : ℕ)
    (h : ∀ a b : Fin r → I, (∑ j, y (a j)) = ∑ j, y (b j) →
      ∃ σ : Equiv.Perm (Fin r), ∀ j, a (σ j) = b j) :
    rEnergy (univ.map y) r ≤ (Fintype.card I)^r * r.factorial := by
  classical
  let G := univ.map y
  let V := Fintype.piFinset fun _ : Fin r => G
  have indices (v : Fin r → F) (hv : v ∈ V) : ∃ a : Fin r → I, ∀ j, y (a j) = v j := by
    have each (j : Fin r) : ∃ i : I, y i = v j := by
      obtain ⟨i,_,eq⟩ := mem_map.mp (Fintype.mem_piFinset.mp hv j)
      exact ⟨i,eq⟩
    choose a ha using each
    exact ⟨a,ha⟩
  have bound (v : Fin r → F) (hv : v ∈ V) :
      (V.filter fun w => (∑ j, v j) = ∑ j, w j).card ≤ r.factorial := by
    obtain ⟨a,ha⟩ := indices v hv
    let permute (σ : Equiv.Perm (Fin r)) := fun j => v (σ j)
    have sub : (V.filter fun w => (∑ j, v j) = ∑ j, w j) ⊆ univ.image permute := by
      intro w hw
      obtain ⟨hw,eq⟩ := mem_filter.mp hw
      obtain ⟨b,hb⟩ := indices w hw
      obtain ⟨σ,hσ⟩ := h a b (by simpa only [ha,hb] using eq)
      exact mem_image.mpr ⟨σ,mem_univ _,funext fun j => by
        change v (σ j) = w j
        rw [← ha,← hb,hσ]⟩
    exact (card_le_card sub).trans (card_image_le.trans_eq (by simp [Fintype.card_perm]))
  have total : rEnergy G r = ∑ v ∈ V, (V.filter fun w => (∑ j, v j) = ∑ j, w j).card := by
    unfold rEnergy
    exact sum_congr rfl fun v _ => by rw [Finset.sum_boole]; simp [V]
  calc rEnergy (univ.map y) r = _ := total
       _ ≤ ∑ _v ∈ V, r.factorial := sum_le_sum bound
       _ = _ := by simp [V,G]

/-- On the transformed RS domain every prime-field tuple relation of this
length is diagonal, and the actual additive energy obeys the factorial bound. -/
theorem prime_energy {p : ℕ} [Fact p.Prime] (x : I ↪ ZMod p) (r : ℕ) (hr : r<p)
    (size : Fintype.card I + ((Fintype.card I)^r)^2*(2*r) < p) :
    ∃ t : ZMod p, (∀ i, t≠x i) ∧
      rEnergy (univ.map (chart x t)) r ≤ (Fintype.card I)^r*r.factorial := by
  obtain ⟨t,ht,he⟩ := prime_chart x r hr size
  exact ⟨t,ht,energy_bound (chart x t) r fun a b eq =>
    perm_of_count_eq a b ((he a b).mp eq)⟩

/-- The transformed chart has exactly 2n²−n ordered additive quadruples. -/
theorem prime_energy_two {p : ℕ} [Fact p.Prime] (x : I ↪ ZMod p) (hp : 2<p)
    (size : Fintype.card I + ((Fintype.card I)^2)^2*4 < p) :
    ∃ t : ZMod p, (∀ i, t≠x i) ∧ rEnergy (univ.map (chart x t)) 2 =
      2*(Fintype.card I)^2-Fintype.card I := by
  obtain ⟨t,ht,he⟩ := prime_chart x 2 hp size
  let y := chart x t
  have sidon : IsSidonSet (univ.map y) := by
    intro a ha b hb c hc d hd eq
    obtain ⟨a,_,rfl⟩ := mem_map.mp ha
    obtain ⟨b,_,rfl⟩ := mem_map.mp hb
    obtain ⟨c,_,rfl⟩ := mem_map.mp hc
    obtain ⟨d,_,rfl⟩ := mem_map.mp hd
    have sumEq : (∑ j : Fin 2, y (![a,b] j)) = ∑ j : Fin 2, y (![c,d] j) := by
      simpa only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons] using eq
    obtain ⟨σ,hs⟩ := perm_of_count_eq _ _ ((he ![a,b] ![c,d]).mp sumEq)
    have ne : σ 0 ≠ σ 1 := σ.injective.ne (by decide)
    have z : σ 0=0 ∨ σ 0=1 := by omega
    rcases z with z|z
    · have o : σ 1=1 := by omega
      exact Or.inl ⟨congrArg y (by simpa [z] using hs 0),congrArg y (by simpa [o] using hs 1)⟩
    · have o : σ 1=0 := by omega
      exact Or.inr ⟨congrArg y (by simpa [o] using hs 1),congrArg y (by simpa [z] using hs 0)⟩
  exact ⟨t,ht,by simpa [y] using isSidonSet_iff_rEnergy_two_eq_swap_floor.mp sidon⟩

end ProximityGap.ReciprocalChartMoments
#print axioms ProximityGap.ReciprocalChartMoments.prime_energy
#print axioms ProximityGap.ReciprocalChartMoments.prime_energy_two
