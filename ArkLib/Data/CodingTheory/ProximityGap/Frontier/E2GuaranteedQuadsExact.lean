/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.E2GenuineQuadStrictExcess

/-!
# Exact count of the three guaranteed `E₂` families (#444)

`E2GenuineQuadStrictExcess` names the guaranteed additive-energy families
`T1 ∪ T2 ∪ T3` and proves the lower count
`3|S|² - 3|S| ≤ card (guaranteedQuads S)`.

For the actual multiplicative-subgroup applications, `S` is negation-closed and has no element
with `x + x = 0` (in particular `0 ∉ S` in odd characteristic).  Under exactly that local
no-two-torsion hypothesis, the probe-observed count is machine checked here:

> `card (guaranteedQuads S) = 3|S|² - 3|S|`.

This turns the named genuine count into the literal additive-energy excess
`E₂(S) - (3|S|² - 3|S|)` whenever the guaranteed families inject into energy.  It is still only
combinatorial bookkeeping: no upper bound on `E₂`, no CORE closure, no capacity claim.
-/

open Finset

namespace ArkLib.ProximityGap.E2CharFree

variable {F : Type*} [AddCommGroup F] [DecidableEq F]

private theorem diag_inter_swap_card_ge (S : Finset F) :
    S.card ≤ (diagQuads S ∩ swapQuads S).card := by
  classical
  let C : Finset (F × F × F × F) := S.image (fun a => (a, a, a, a))
  have hCcard : C.card = S.card := by
    unfold C
    rw [Finset.card_image_of_injective]
    intro a b h
    exact ((by simpa only [Prod.mk.injEq] using h) : a = b ∧ a = b ∧ a = b ∧ a = b).1
  have hCsub : C ⊆ diagQuads S ∩ swapQuads S := by
    intro q hq
    rw [Finset.mem_image] at hq
    obtain ⟨a, ha, rfl⟩ := hq
    rw [Finset.mem_inter]
    constructor
    · rw [mem_diagQuads]
      exact ⟨a, ha, a, ha, rfl⟩
    · rw [mem_swapQuads]
      exact ⟨a, ha, a, ha, rfl⟩
  calc
    S.card = C.card := hCcard.symm
    _ ≤ (diagQuads S ∩ swapQuads S).card := Finset.card_le_card hCsub

/-- The diagonal/swap overlap is exactly the constant quadruples, hence has cardinality `|S|`. -/
theorem diag_inter_swap_card_eq (S : Finset F) :
    (diagQuads S ∩ swapQuads S).card = S.card := by
  exact le_antisymm (diag_inter_swap_card_le S) (diag_inter_swap_card_ge S)

private theorem diag_inter_anti_card_ge (S : Finset F) (hS : ∀ x ∈ S, -x ∈ S) :
    S.card ≤ (diagQuads S ∩ antiQuads S).card := by
  classical
  let C : Finset (F × F × F × F) := S.image (fun a => (a, -a, a, -a))
  have hCcard : C.card = S.card := by
    unfold C
    rw [Finset.card_image_of_injective]
    intro a b h
    exact ((by simpa only [Prod.mk.injEq] using h) : a = b ∧ -a = -b ∧ a = b ∧ -a = -b).1
  have hCsub : C ⊆ diagQuads S ∩ antiQuads S := by
    intro q hq
    rw [Finset.mem_image] at hq
    obtain ⟨a, ha, rfl⟩ := hq
    rw [Finset.mem_inter]
    constructor
    · rw [mem_diagQuads]
      exact ⟨a, ha, -a, hS a ha, rfl⟩
    · rw [mem_antiQuads]
      exact ⟨a, ha, a, ha, rfl⟩
  calc
    S.card = C.card := hCcard.symm
    _ ≤ (diagQuads S ∩ antiQuads S).card := Finset.card_le_card hCsub

/-- For a negation-closed set, the diagonal/antipodal overlap has cardinality `|S|`. -/
theorem diag_inter_anti_card_eq (S : Finset F) (hS : ∀ x ∈ S, -x ∈ S) :
    (diagQuads S ∩ antiQuads S).card = S.card := by
  exact le_antisymm (diag_inter_anti_card_le S) (diag_inter_anti_card_ge S hS)

private theorem swap_inter_anti_card_ge (S : Finset F) (hS : ∀ x ∈ S, -x ∈ S) :
    S.card ≤ (swapQuads S ∩ antiQuads S).card := by
  classical
  let C : Finset (F × F × F × F) := S.image (fun a => (a, -a, -a, a))
  have hCcard : C.card = S.card := by
    unfold C
    rw [Finset.card_image_of_injective]
    intro a b h
    exact ((by simpa only [Prod.mk.injEq] using h) : a = b ∧ -a = -b ∧ -a = -b ∧ a = b).1
  have hCsub : C ⊆ swapQuads S ∩ antiQuads S := by
    intro q hq
    rw [Finset.mem_image] at hq
    obtain ⟨a, ha, rfl⟩ := hq
    rw [Finset.mem_inter]
    constructor
    · rw [mem_swapQuads]
      exact ⟨a, ha, -a, hS a ha, rfl⟩
    · rw [mem_antiQuads]
      exact ⟨a, ha, -a, hS a ha, by simp⟩
  calc
    S.card = C.card := hCcard.symm
    _ ≤ (swapQuads S ∩ antiQuads S).card := Finset.card_le_card hCsub

/-- For a negation-closed set, the swap/antipodal overlap has cardinality `|S|`. -/
theorem swap_inter_anti_card_eq (S : Finset F) (hS : ∀ x ∈ S, -x ∈ S) :
    (swapQuads S ∩ antiQuads S).card = S.card := by
  exact le_antisymm (swap_inter_anti_card_le S) (swap_inter_anti_card_ge S hS)

private theorem triple_inter_card_eq_zero (S : Finset F)
    (h2 : ∀ x ∈ S, x + x ≠ 0) :
    ((diagQuads S ∩ swapQuads S) ∩ antiQuads S).card = 0 := by
  classical
  rw [Finset.card_eq_zero]
  ext q
  constructor
  · intro hq
    rw [Finset.mem_inter] at hq
    obtain ⟨a, ha, hqa⟩ := inter_eq_const hq.1
    obtain ⟨c, _, d, _, hanti⟩ := mem_antiQuads.mp hq.2
    rw [hqa] at hanti
    simp only [Prod.mk.injEq] at hanti
    have ha_neg : a = -a := by
      calc
        a = -c := hanti.2.1
        _ = -a := by rw [hanti.1]
    have hzero : a + a = 0 := by
      simpa [← ha_neg] using add_neg_cancel a
    exact False.elim (h2 a ha hzero)
  · intro hq
    simp at hq

/-- Exact combinatorial count of the three guaranteed families under the local hypotheses valid
for odd-characteristic multiplicative subgroups: negation closure and no element satisfying
`x+x=0`. -/
theorem guaranteedQuads_card_eq_floor (S : Finset F) (hS : ∀ x ∈ S, -x ∈ S)
    (h2 : ∀ x ∈ S, x + x ≠ 0) :
    (guaranteedQuads S).card = 3 * (S.card * S.card) - 3 * S.card := by
  classical
  set A := diagQuads S
  set B := swapQuads S
  set C := antiQuads S
  have hAcard : A.card = S.card * S.card := by simpa [A] using diagQuads_card S
  have hBcard : B.card = S.card * S.card := by simpa [B] using swapQuads_card S
  have hCcard : C.card = S.card * S.card := by simpa [C] using antiQuads_card S
  have hAB : (A ∩ B).card = S.card := by simpa [A, B] using diag_inter_swap_card_eq S
  have hAC : (A ∩ C).card = S.card := by simpa [A, C] using diag_inter_anti_card_eq S hS
  have hBC : (B ∩ C).card = S.card := by simpa [B, C] using swap_inter_anti_card_eq S hS
  have hABC : ((A ∩ B) ∩ C).card = 0 := by
    simpa [A, B, C] using triple_inter_card_eq_zero S h2
  have hABcard : (A ∪ B).card = A.card + B.card - (A ∩ B).card := Finset.card_union A B
  have hUC : ((A ∪ B) ∪ C).card = (A ∪ B).card + C.card - ((A ∪ B) ∩ C).card :=
    Finset.card_union _ _
  have hdist : (A ∪ B) ∩ C = (A ∩ C) ∪ (B ∩ C) := Finset.union_inter_distrib_right A B C
  have hACBC : ((A ∩ C) ∪ (B ∩ C)).card = (A ∩ C).card + (B ∩ C).card - ((A ∩ C) ∩ (B ∩ C)).card :=
    Finset.card_union _ _
  have htriple : ((A ∩ C) ∩ (B ∩ C)).card = 0 := by
    have hsets : (A ∩ C) ∩ (B ∩ C) = (A ∩ B) ∩ C := by
      ext q; simp [and_left_comm, and_comm]
    rw [hsets, hABC]
  have hABCunion : ((A ∪ B) ∪ C).card = 3 * (S.card * S.card) - 3 * S.card := by
    rw [hUC, hdist, hACBC, htriple, hABcard, hAcard, hBcard, hCcard, hAB, hAC, hBC]
    omega
  simpa [guaranteedQuads, A, B, C] using hABCunion


/-- Exact additive-energy decomposition into the char-free floor plus the named genuine excess.
Under negation closure and the local no-two-torsion condition, the partition theorem becomes the
literal formula `E₂(S) = (3|S|²-3|S|) + G(S)`. -/
theorem E2_eq_floor_add_genuine (S : Finset F) (hS : ∀ x ∈ S, -x ∈ S)
    (h2 : ∀ x ∈ S, x + x ≠ 0) :
    E2 S = (3 * (S.card * S.card) - 3 * S.card) + (genuineQuads S).card := by
  rw [E2_eq_guaranteed_add_genuine S hS, guaranteedQuads_card_eq_floor S hS h2]

/-- With the exact guaranteed-family count, the named genuine count is literally the additive
energy excess over `3|S|²-3|S|`. -/
theorem genuineQuads_card_eq_E2_sub_floor (S : Finset F) (hS : ∀ x ∈ S, -x ∈ S)
    (h2 : ∀ x ∈ S, x + x ≠ 0) :
    (genuineQuads S).card = E2 S - (3 * (S.card * S.card) - 3 * S.card) := by
  rw [genuineQuads_card_eq S hS, guaranteedQuads_card_eq_floor S hS h2]

end ArkLib.ProximityGap.E2CharFree

#print axioms ArkLib.ProximityGap.E2CharFree.diag_inter_swap_card_eq
#print axioms ArkLib.ProximityGap.E2CharFree.diag_inter_anti_card_eq
#print axioms ArkLib.ProximityGap.E2CharFree.swap_inter_anti_card_eq
#print axioms ArkLib.ProximityGap.E2CharFree.guaranteedQuads_card_eq_floor
#print axioms ArkLib.ProximityGap.E2CharFree.E2_eq_floor_add_genuine
#print axioms ArkLib.ProximityGap.E2CharFree.genuineQuads_card_eq_E2_sub_floor
