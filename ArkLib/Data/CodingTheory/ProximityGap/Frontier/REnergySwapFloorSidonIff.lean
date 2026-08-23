/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.REnergySwapFloorSidonSharp

/-!
# The swap floor characterizes Sidon: the converse + the iff (#444, #389, §0)

`REnergySwapFloorSidonSharp.rEnergy_two_eq_swap_floor_of_sidon` proved the **sharp** direction
`IsSidonSet G → rEnergy G 2 = 2|G|² − |G|`.  This file proves the **converse** and packages the
**iff**:

> **`rEnergy_two_gt_swap_floor_of_not_sidon`.**  `¬IsSidonSet G → 2|G|² − |G| < rEnergy G 2`.
> **`isSidonSet_iff_rEnergy_two_eq_swap_floor`.**  `IsSidonSet G ↔ rEnergy G 2 = 2|G|² − |G|`.

Mechanism (converse, contrapositive of sharpness):  a *genuine* (non-swap-trivial) additive
coincidence `a + b = c + d` with `(c,d) ∉ {(a,b),(b,a)}` produces, in the energy fiber over
`v = (a,b)`, a THIRD distinct solution beyond the two guaranteed ones `{v, swap01 v}`, so that
fiber strictly exceeds its swap-floor contribution `if v 0 = v 1 then 1 else 2`, while every other
fiber still meets it (`REnergySwapFloor` per-`v` bound).  Summing with one strict term
(`Finset.sum_lt_sum`) gives `rEnergy G 2 > 2|G|² − |G|`.

Axiom-clean (`propext, Classical.choice, Quot.sound`).  No CORE closure, no char-p transfer, no
capacity / beyond-Johnson / growth-law claim.  Issues #444, #389.
-/

open Finset

namespace ArkLib.ProximityGap.SubgroupGaussSumMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The energy fiber over `v : Fin 2 → F` (the tuples `w` with `∑ w = ∑ v`), as a finset. -/
private def fiber (G : Finset F) (v : Fin 2 → F) : Finset (Fin 2 → F) :=
  (Fintype.piFinset (fun _ : Fin 2 => G)).filter (fun w => ∑ i, v i = ∑ i, w i)

/-- `rEnergy G 2` is the sum of the fiber cardinalities over `v`. -/
private theorem rEnergy_two_eq_sum_fiber (G : Finset F) :
    rEnergy G 2 = ∑ v ∈ Fintype.piFinset (fun _ : Fin 2 => G), (fiber G v).card := by
  classical
  unfold rEnergy fiber
  exact Finset.sum_congr rfl (fun v _ => by rw [Finset.sum_boole]; simp)

/-- Each fiber over `v` always contains `{v, swap01 v}`, so its card is `≥ if v0=v1 then 1 else 2`. -/
private theorem fiber_card_ge (G : Finset F) {v : Fin 2 → F}
    (hv : v ∈ Fintype.piFinset (fun _ : Fin 2 => G)) :
    (if v 0 = v 1 then (1 : ℕ) else 2) ≤ (fiber G v).card := by
  classical
  rw [Fintype.mem_piFinset] at hv
  have hpair : ({v, swap01 v} : Finset (Fin 2 → F)) ⊆ fiber G v := by
    intro w hw
    rw [Finset.mem_insert, Finset.mem_singleton] at hw
    unfold fiber
    rw [Finset.mem_filter, Fintype.mem_piFinset]
    rcases hw with rfl | rfl
    · exact ⟨fun i => hv i, rfl⟩
    · refine ⟨fun i => ?_, (sum_swap01 v).symm⟩
      show swap01 v i ∈ G; unfold swap01; exact hv _
  have hle := Finset.card_le_card hpair
  by_cases heq : v 0 = v 1
  · rw [if_pos heq]
    have hpos : 0 < ({v, swap01 v} : Finset (Fin 2 → F)).card :=
      Finset.card_pos.mpr ⟨v, by simp⟩
    omega
  · rw [if_neg heq]
    have : ({v, swap01 v} : Finset (Fin 2 → F)).card = 2 :=
      Finset.card_pair (Ne.symm (swap01_ne heq))
    omega

/-- **Converse of sharpness.**  If `G` is *not* Sidon then its `r = 2` additive energy strictly
exceeds the swap floor:  `2|G|² − |G| < rEnergy G 2`. -/
theorem rEnergy_two_gt_swap_floor_of_not_sidon {G : Finset F} (hns : ¬ IsSidonSet G) :
    2 * G.card ^ 2 - G.card < rEnergy G 2 := by
  classical
  -- extract a genuine coincidence witness
  rw [IsSidonSet] at hns
  push_neg at hns
  obtain ⟨a, ha, b, hb, c, hc, d, hd, hsum, hnac, hnad⟩ := hns
  -- the witness tuple v = ![a,b] and the genuine partner w = ![c,d]
  set v : Fin 2 → F := ![a, b] with hvdef
  have hvmem : v ∈ Fintype.piFinset (fun _ : Fin 2 => G) := by
    rw [Fintype.mem_piFinset]; intro i; fin_cases i <;> simpa [hvdef]
  -- v's fiber strictly exceeds its swap-floor contribution: contains v, swap01 v, AND ![c,d]
  have hwit : (![c, d] : Fin 2 → F) ∈ fiber G v := by
    unfold fiber
    rw [Finset.mem_filter, Fintype.mem_piFinset]
    refine ⟨fun i => ?_, ?_⟩
    · fin_cases i
      · simpa using hc
      · simpa using hd
    · simp only [hvdef, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons]
      exact hsum
  -- ![c,d] ∉ {v, swap01 v}
  have hwit_new : (![c, d] : Fin 2 → F) ∉ ({v, swap01 v} : Finset (Fin 2 → F)) := by
    rw [Finset.mem_insert, Finset.mem_singleton]
    push_neg
    constructor
    · -- ![c,d] ≠ v = ![a,b]  (else a=c ∧ b=d, contradicting hnac : a=c → b≠d)
      intro h
      have h0 : c = a := by have := congrFun h 0; simpa [hvdef] using this
      have h1 : d = b := by have := congrFun h 1; simpa [hvdef] using this
      exact hnac h0.symm h1.symm
    · -- ![c,d] ≠ swap01 v   (swap01 ![a,b] = ![b,a]; else a=d ∧ b=c, contradicting hnad)
      intro h
      have hsw0 : swap01 v 0 = b := by
        show swap01 v 0 = b; unfold swap01; rw [Equiv.swap_apply_left]; simp [hvdef]
      have hsw1 : swap01 v 1 = a := by
        show swap01 v 1 = a; unfold swap01; rw [Equiv.swap_apply_right]; simp [hvdef]
      have h0 : c = b := by have := congrFun h 0; rw [hsw0] at this; simpa using this
      have h1 : d = a := by have := congrFun h 1; rw [hsw1] at this; simpa using this
      exact hnad h1.symm h0.symm
  -- so fiber card > swap-floor contribution at v
  have hstrict : (if v 0 = v 1 then (1 : ℕ) else 2) < (fiber G v).card := by
    -- {v, swap01 v, ![c,d]} ⊆ fiber G v has card ≥ (floor at v) + 1
    have hsub : (insert (![c, d] : Fin 2 → F) ({v, swap01 v} : Finset (Fin 2 → F))) ⊆ fiber G v := by
      intro w hw
      rw [Finset.mem_insert] at hw
      rcases hw with rfl | hw
      · exact hwit
      · -- the {v, swap01 v} part
        rw [Finset.mem_insert, Finset.mem_singleton] at hw
        unfold fiber
        rw [Finset.mem_filter, Fintype.mem_piFinset]
        have hvmem' : ∀ i, v i ∈ G := by rw [Fintype.mem_piFinset] at hvmem; exact hvmem
        rcases hw with rfl | rfl
        · refine ⟨fun i => hvmem' i, ?_⟩; rfl
        · refine ⟨fun i => ?_, (sum_swap01 v).symm⟩
          show swap01 v i ∈ G; unfold swap01; exact hvmem' _
    have hcard_insert : (insert (![c, d] : Fin 2 → F)
        ({v, swap01 v} : Finset (Fin 2 → F))).card
        = ({v, swap01 v} : Finset (Fin 2 → F)).card + 1 := by
      rw [Finset.card_insert_of_notMem hwit_new]
    have hle := Finset.card_le_card hsub
    rw [hcard_insert] at hle
    by_cases heq : v 0 = v 1
    · rw [if_pos heq]
      have hpos : 0 < ({v, swap01 v} : Finset (Fin 2 → F)).card :=
        Finset.card_pos.mpr ⟨v, by simp⟩
      omega
    · rw [if_neg heq]
      have : ({v, swap01 v} : Finset (Fin 2 → F)).card = 2 :=
        Finset.card_pair (Ne.symm (swap01_ne heq))
      omega
  -- sum with one strict term
  have hlt : ∑ x ∈ Fintype.piFinset (fun _ : Fin 2 => G), (if x 0 = x 1 then (1 : ℕ) else 2)
      < ∑ x ∈ Fintype.piFinset (fun _ : Fin 2 => G), (fiber G x).card := by
    apply Finset.sum_lt_sum (fun x hx => fiber_card_ge G hx)
    exact ⟨v, hvmem, hstrict⟩
  -- evaluate the LHS sum = swap floor, RHS = rEnergy
  have hlhs : ∑ x ∈ Fintype.piFinset (fun _ : Fin 2 => G), (if x 0 = x 1 then (1 : ℕ) else 2)
      = 2 * G.card ^ 2 - G.card := by
    have hcard_pi : (Fintype.piFinset (fun _ : Fin 2 => G)).card = G.card ^ 2 := by
      rw [Fintype.card_piFinset_const]
    have hpoint : ∀ x : Fin 2 → F, (if x 0 = x 1 then (1 : ℕ) else 2)
        = 2 - (if x 0 = x 1 then 1 else 0) := by
      intro x; by_cases h : x 0 = x 1 <;> simp [h]
    simp_rw [hpoint]
    rw [Finset.sum_tsub_distrib _ (fun x _ => by by_cases h : x 0 = x 1 <;> simp [h])]
    rw [Finset.sum_const, hcard_pi, smul_eq_mul]
    have hcount : ∑ x ∈ Fintype.piFinset (fun _ : Fin 2 => G),
        (if x 0 = x 1 then (1 : ℕ) else 0) = G.card := by
      rw [Finset.sum_boole]; simp only [Nat.cast_id]; simpa using eqPair_count G 0
    rw [hcount, Nat.mul_comm]
  rw [hlhs, ← rEnergy_two_eq_sum_fiber] at hlt
  exact hlt

/-- **The swap floor characterizes Sidon at `r = 2`.**  `IsSidonSet G ↔ rEnergy G 2 = 2|G|² − |G|`. -/
theorem isSidonSet_iff_rEnergy_two_eq_swap_floor {G : Finset F} :
    IsSidonSet G ↔ rEnergy G 2 = 2 * G.card ^ 2 - G.card := by
  constructor
  · exact rEnergy_two_eq_swap_floor_of_sidon
  · intro heq
    by_contra hns
    have := rEnergy_two_gt_swap_floor_of_not_sidon hns
    omega

end ArkLib.ProximityGap.SubgroupGaussSumMoment

-- Axiom audit: must be `[propext, Classical.choice, Quot.sound]` only (no sorryAx).
#print axioms ArkLib.ProximityGap.SubgroupGaussSumMoment.isSidonSet_iff_rEnergy_two_eq_swap_floor
