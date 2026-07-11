/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G138CyclotomicLiftHandoff
import ArkLib.Data.CodingTheory.ProximityGap.KKH26CharZeroCollisionLaw

/-!
# G139: entropy obstruction to accident-free cyclotomic lifting

G138 isolates a useful sufficient hypothesis for the fully-disjoint census: every modular
vanishing multiset of weight at most `220` should also vanish after cyclotomic lifting.  This file
shows that the hypothesis is too strong at production scale.

If `H ⊆ G` is a slice on which characteristic-zero `r`-subset sums are injective, then absence of
accidents through weight `2r` makes the finite-field subset-sum map injective as well.  Consequently

`choose (#H) r ≤ #F`.

For a canonical antipodal half of `μ_(2^30)`, characteristic-zero injectivity follows from the
Lam--Leung collision law and `#H = 2^29`.  At `r = 110`, however,
`choose (2^29) 110 > 2^160`.  Thus a production field of size at most `2^160` must contain a
weight-`220` reduction accident.  The viable residual is quantitative control of the accident
census, not its vanishing.

Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G139NoAccidentEntropyObstruction

open ArkLib.ProximityGap.Frontier.G138CyclotomicLiftHandoff
open ProximityGap.KKH26CharZeroCollisionLaw
open scoped BigOperators

variable {F L : Type*} [Field F] [DecidableEq F] [Fintype F]
  [Field L] [CharZero L] [DecidableEq L]

/-- A source slice containing no antipodal pair has injective lifted subset sums. -/
theorem lifted_subsetSum_injOn_of_antipodalFree
    {G H : Finset F} {k r : ℕ} (hk : 1 ≤ k)
    (D : CyclotomicLiftData (L := L) G k) (hHG : H ⊆ G)
    (hfree : ∀ x ∈ H, -x ∉ H) :
    Set.InjOn (fun S : Finset F => ∑ x ∈ S, D.lift x)
      (↑(H.powersetCard r) : Set (Finset F)) := by
  intro S hS T hT hsum
  have hSsub : S ⊆ H := (Finset.mem_powersetCard.mp hS).1
  have hTsub : T ⊆ H := (Finset.mem_powersetCard.mp hT).1
  have himageFree (U : Finset F) (hU : U ⊆ H) :
      freePart (U.image D.lift) = U.image D.lift := by
    apply Finset.filter_eq_self.mpr
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    intro hneg
    obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hneg
    have : y = -x := D.injective (by simpa [D.map_neg] using hyx)
    exact hfree x (hU hx) (by simpa [← this] using hU hy)
  have hSroots : ∀ z ∈ S.image D.lift, z ^ (2 ^ k) = 1 := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    exact D.root x (hHG (hSsub hx))
  have hTroots : ∀ z ∈ T.image D.lift, z ^ (2 ^ k) = 1 := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    exact D.root x (hHG (hTsub hx))
  have himageSum : ∑ z ∈ S.image D.lift, z = ∑ z ∈ T.image D.lift, z := by
    simpa [Finset.sum_image (fun x _ y _ hxy => D.injective hxy)] using hsum
  have himage := sum_injOn_antipodalFree hk hSroots hTroots
    (himageFree S hSsub) (himageFree T hTsub) himageSum
  exact Finset.image_injective D.injective himage

/-- No short reduction accidents transfer characteristic-zero subset-sum injectivity back to the
finite field. -/
theorem subsetSum_injOn_of_noShortReductionAccidents
    {G H : Finset F} {k limit r : ℕ}
    (D : CyclotomicLiftData (L := L) G k)
    (hacc : NoShortReductionAccidents G D limit)
    (hHG : H ⊆ G) (hneg : ∀ x ∈ G, -x ∈ G) (hr : 2 * r ≤ limit)
    (hlift : Set.InjOn (fun S : Finset F => ∑ x ∈ S, D.lift x)
      (↑(H.powersetCard r) : Set (Finset F))) :
    Set.InjOn (fun S : Finset F => ∑ x ∈ S, x)
      (↑(H.powersetCard r) : Set (Finset F)) := by
  intro S hS T hT hsum
  have hScard : S.card = r := (Finset.mem_powersetCard.mp hS).2
  have hTcard : T.card = r := (Finset.mem_powersetCard.mp hT).2
  have hSsub : S ⊆ H := (Finset.mem_powersetCard.mp hS).1
  have hTsub : T ⊆ H := (Finset.mem_powersetCard.mp hT).1
  let M : Multiset F := S.1 + T.1.map fun x => -x
  have hMcard : M.card ≤ limit := by
    simpa [M, hScard, hTcard, two_mul] using hr
  have hMsupp : ∀ x ∈ M, x ∈ G := by
    intro x hx
    simp only [M, Multiset.mem_add, Multiset.mem_map] at hx
    rcases hx with hx | ⟨y, hy, rfl⟩
    · exact hHG (hSsub hx)
    · exact hneg y (hHG (hTsub hy))
  have hMsum : M.sum = 0 := by
    have hneg : ∑ x ∈ T, -x = -(∑ x ∈ T, x) :=
      Finset.sum_neg_distrib (fun x : F => x)
    simp [M, ← Finset.sum_eq_multiset_sum, hneg, hsum]
  have hLiftZero := hacc M hMcard hMsupp hMsum
  have hLiftEq : ∑ x ∈ S, D.lift x = ∑ x ∈ T, D.lift x := by
    simp only [M, Multiset.map_add, Multiset.sum_add, Multiset.map_map] at hLiftZero
    rw [← Finset.sum_eq_multiset_sum, ← Finset.sum_eq_multiset_sum] at hLiftZero
    simp only [Function.comp_apply, D.map_neg, Finset.sum_neg_distrib] at hLiftZero
    exact sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hLiftZero)
  exact hlift hS hT hLiftEq

/-- **Entropy obstruction.** Accident-free lifting through weight `2r` forces the number of
`r`-subsets in every characteristic-zero dissociated slice to fit inside the finite field. -/
theorem choose_le_fieldCard_of_noShortReductionAccidents
    {G H : Finset F} {k limit r : ℕ}
    (D : CyclotomicLiftData (L := L) G k)
    (hacc : NoShortReductionAccidents G D limit)
    (hHG : H ⊆ G) (hneg : ∀ x ∈ G, -x ∈ G) (hr : 2 * r ≤ limit)
    (hlift : Set.InjOn (fun S : Finset F => ∑ x ∈ S, D.lift x)
      (↑(H.powersetCard r) : Set (Finset F))) :
    H.card.choose r ≤ Fintype.card F := by
  let f : Finset F → F := fun S => ∑ x ∈ S, x
  have hinj : Set.InjOn f (↑(H.powersetCard r) : Set (Finset F)) :=
    subsetSum_injOn_of_noShortReductionAccidents D hacc hHG hneg hr hlift
  calc
    H.card.choose r = (H.powersetCard r).card := (Finset.card_powersetCard r H).symm
    _ = ((H.powersetCard r).image f).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.univ : Finset F).card := Finset.card_le_card (Finset.subset_univ _)
    _ = Fintype.card F := Finset.card_univ

/-- The literal production arithmetic contradicts the entropy consequence. -/
theorem production_choose_gt_fieldCap :
    2 ^ 160 < (2 ^ 29).choose 110 := by
  have hsmall : 2 ^ 160 < Nat.choose 322 110 := by
    set_option maxRecDepth 10000 in
      norm_num [Nat.choose]
  exact hsmall.trans_le (Nat.choose_le_choose 110 (by norm_num))

/-- **G139 capstone.** A production-sized dissociated half-slice refutes G138's weight-220
no-accident hypothesis. -/
theorem not_noShortReductionAccidents_220_of_production_half
    (G H : Finset F) (D : CyclotomicLiftData (L := L) G 30)
    (hHG : H ⊆ G) (hneg : ∀ x ∈ G, -x ∈ G)
    (hHcard : H.card = 2 ^ 29) (hq : Fintype.card F ≤ 2 ^ 160)
    (hlift : Set.InjOn (fun S : Finset F => ∑ x ∈ S, D.lift x)
      (↑(H.powersetCard 110) : Set (Finset F))) :
    ¬ NoShortReductionAccidents G D 220 := by
  intro hacc
  have hle := choose_le_fieldCard_of_noShortReductionAccidents D hacc hHG hneg (by norm_num) hlift
  rw [hHcard] at hle
  exact (Nat.not_lt_of_ge (hle.trans hq)) production_choose_gt_fieldCap

/-- Structural form of the G139 capstone: an antipodal-free half of size `2^29` already forces a
weight-220 accident. -/
theorem not_noShortReductionAccidents_220_of_antipodalFree_half
    (G H : Finset F) (D : CyclotomicLiftData (L := L) G 30)
    (hHG : H ⊆ G) (hneg : ∀ x ∈ G, -x ∈ G) (hfree : ∀ x ∈ H, -x ∉ H)
    (hHcard : H.card = 2 ^ 29) (hq : Fintype.card F ≤ 2 ^ 160) :
    ¬ NoShortReductionAccidents G D 220 := by
  apply not_noShortReductionAccidents_220_of_production_half G H D hHG hneg hHcard hq
  exact lifted_subsetSum_injOn_of_antipodalFree (by norm_num) D hHG hfree

#print axioms lifted_subsetSum_injOn_of_antipodalFree
#print axioms subsetSum_injOn_of_noShortReductionAccidents
#print axioms choose_le_fieldCard_of_noShortReductionAccidents
#print axioms production_choose_gt_fieldCap
#print axioms not_noShortReductionAccidents_220_of_production_half
#print axioms not_noShortReductionAccidents_220_of_antipodalFree_half

end ArkLib.ProximityGap.Frontier.G139NoAccidentEntropyObstruction
