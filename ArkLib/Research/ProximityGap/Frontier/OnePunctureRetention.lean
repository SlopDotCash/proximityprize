/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Extensions.Data.CodingTheory.ProximityGap.Errors
import ArkLib.Data.CodingTheory.ProximityGap.BelowUDRPuncture

/-! # An MCA witness survives all but one ordinary puncture -/
set_option autoImplicit false
noncomputable section
open Finset Polynomial Code
open scoped NNReal
namespace ArkLib.ProximityGap.Frontier.OnePunctureRetention
open _root_.ProximityGap _root_.ProximityGap.Ownership
variable {F I : Type} [Field F] [Fintype I] [DecidableEq I]

omit [Fintype I] [DecidableEq I] in
private theorem word_iff (dom : I ↪ F) (k : ℕ) (v : I → F) :
    v∈ReedSolomon.code dom k ↔ ∃ p : F[X], p.degree<(k:ℕ) ∧ ∀ i, v i=p.eval (dom i) := by
  rw [ReedSolomon.mem_code_iff_exists_polynomial]
  exact ⟨fun ⟨p,hp,hv⟩ => ⟨p,hp,fun i => congrFun hv i⟩,
    fun ⟨p,hp,hv⟩ => ⟨p,hp,funext hv⟩⟩

omit [Fintype I] in
private theorem lose_le_one (S : Finset I) (x : I) : S.card ≤ (S.erase x).card+1 := by
  by_cases hx : x∈S
  · exact (card_erase_add_one hx).symm.le
  · rw [erase_eq_of_notMem hx]; omega

open Classical in
/-- Two distinct one-site deletions that admit joint explanations already give
a joint explanation of the original support. -/
theorem at_most_one_repair (dom : I ↪ F) (k : ℕ) (S : Finset I) (u v : I → F)
    (hk : k+2≤S.card) (hno : ¬pairJointAgreesOn (ReedSolomon.code dom k : Set (I → F)) S u v) :
    let repairs := univ.filter fun i => pairJointAgreesOn (ReedSolomon.code dom k : Set (I → F)) (S.erase i) u v
    repairs.card≤1 := by
  classical
  apply card_le_one.mpr
  intro i hi j hj
  by_contra hij
  obtain ⟨a,ha,b,hb,hfit⟩ := (mem_filter.mp hi).2
  obtain ⟨c,hc,d,hd,hfit'⟩ := (mem_filter.mp hj).2
  let T := (S.erase i).erase j
  have hT : k≤T.card := by have := lose_le_one S i; have := lose_le_one (S.erase i) j; dsimp [T]; omega
  have hpart (x : I) (hx : x∈T) : x∈S.erase i ∧ x∈S.erase j := by
    obtain ⟨hj,hi⟩ := mem_erase.mp hx
    exact ⟨hi,mem_erase.mpr ⟨hj,(mem_erase.mp hi).2⟩⟩
  have eq₁ := ReedSolomon.eq_of_agree_of_card_le ha hc hT (fun x hx =>
    (hfit x (hpart x hx).1).1.trans (hfit' x (hpart x hx).2).1.symm)
  have eq₂ := ReedSolomon.eq_of_agree_of_card_le hb hd hT (fun x hx =>
    (hfit x (hpart x hx).1).2.trans (hfit' x (hpart x hx).2).2.symm)
  apply hno
  refine ⟨a,ha,b,hb,?_⟩
  intro x hx
  by_cases hxi : x=i
  · subst x; rw [eq₁,eq₂]; exact hfit' i (mem_erase.mpr ⟨hij,hx⟩)
  · exact hfit x (mem_erase.mpr ⟨hxi,hx⟩)

private def childSet {m : ℕ} (i : Fin (m+1)) (S : Finset (Fin (m+1))) :=
  univ.filter fun j => i.succAbove j∈S

private theorem child_card {m : ℕ} (i : Fin (m+1)) (S : Finset (Fin (m+1))) :
    S.card ≤ (childSet i S).card+1 := by
  have himg : (childSet i S).image i.succAbove=S.erase i := by
    ext x
    simp only [childSet,mem_image,mem_filter,mem_univ,true_and,mem_erase]
    exact ⟨fun ⟨j,hj,h⟩ => h ▸ And.intro (Fin.succAbove_ne i j) hj,
      fun ⟨hx,hs⟩ => by obtain ⟨j,rfl⟩ := Fin.exists_succAbove_eq hx; exact ⟨j,hs,rfl⟩⟩
  have bound := lose_le_one S i
  rwa [←himg,card_image_of_injective _ Fin.succAbove_right_injective] at bound

private theorem enough {m e : ℕ} (hm : 0 < m) : (1-(e:ℝ≥0)/m)*(m:ℝ≥0)=((m-e:ℕ):ℝ≥0) := by
  rw [tsub_mul,one_mul,div_mul_cancel₀ _ (by exact_mod_cast hm.ne'),Nat.cast_tsub]


open Classical in
/-- On deleting each coordinate, keep the same error count and polynomial degree
bound and restrict both received words. Every bad label survives at least `m`
of the `m+1` deletions if the agreement threshold is at least `k+2`. -/
theorem retained {m k e : ℕ} (hm : 0 < m) (hk : k + 2 ≤ m + 1 - e) (dom : Fin (m+1) ↪ F)
    (u v : Fin (m+1) → F) (g : F)
    (hg : mcaEvent (ReedSolomon.code dom k : Set (Fin (m+1) → F))
      ((e:ℝ≥0)/(m+1:ℕ)) u v g) :
    m≤(univ.filter fun i : Fin (m+1) => mcaEvent
      (ReedSolomon.code (punctureDom dom i) k : Set (Fin m → F)) ((e:ℝ≥0)/m)
      (u ∘ i.succAbove) (v ∘ i.succAbove) g).card := by
  classical
  obtain ⟨S,hs,⟨w,hw,hfold⟩,hnj⟩ := hg
  rw [Fintype.card_fin,enough (by omega)] at hs
  have size : m+1-e≤S.card := by exact_mod_cast hs
  let R := univ.filter fun i => pairJointAgreesOn (ReedSolomon.code dom k : Set (Fin (m+1) → F)) (S.erase i) u v
  have hr : R.card≤1 := at_most_one_repair dom k S u v (hk.trans size) hnj
  have hleft : m≤Rᶜ.card := by rw [card_compl,Fintype.card_fin]; omega
  apply hleft.trans (card_le_card ?_)
  intro i hi
  have hnon : ¬pairJointAgreesOn (ReedSolomon.code dom k : Set (Fin (m+1) → F)) (S.erase i) u v := by
    intro h
    exact (mem_compl.mp hi) (mem_filter.mpr ⟨mem_univ _,h⟩)
  apply mem_filter.mpr
  refine ⟨mem_univ _,childSet i S,?_,?_,?_⟩
  · rw [Fintype.card_fin,enough hm]
    exact_mod_cast (show m-e≤(childSet i S).card by have := child_card i S; omega)
  · obtain ⟨p,hp,he⟩ := (word_iff dom k w).mp hw
    refine ⟨w ∘ i.succAbove,(word_iff _ _ _).mpr ⟨p,hp,fun j => he (i.succAbove j)⟩,?_⟩
    exact fun j hj => hfold _ (mem_filter.mp hj).2
  · rintro ⟨a,ha,b,hb,hfit⟩
    obtain ⟨p,hp,he⟩ := (word_iff _ _ _).mp ha
    obtain ⟨q,hq,he'⟩ := (word_iff _ _ _).mp hb
    apply hnon
    refine ⟨fun x => p.eval (dom x),(word_iff _ _ _).mpr ⟨p,hp,fun _ => rfl⟩,
      fun x => q.eval (dom x),(word_iff _ _ _).mpr ⟨q,hq,fun _ => rfl⟩,?_⟩
    intro x hx
    obtain ⟨hne,hxs⟩ := mem_erase.mp hx
    obtain ⟨j,rfl⟩ := Fin.exists_succAbove_eq hne
    have h := hfit j (mem_filter.mpr ⟨mem_univ _,hxs⟩)
    exact ⟨(he j).symm.trans h.1,(he' j).symm.trans h.2⟩

variable [Fintype F]

open Classical in
/-- Double counting all bad-label/puncture pairs at fixed dimension and error
count. A uniform bound on child scalar counts costs a factor of at most $(m+1)/m$. -/
theorem count {m k e B : ℕ} (hm : 0 < m) (hk : k + 2 ≤ m + 1 - e) (dom : Fin (m+1) ↪ F)
    (u v : Fin (m+1) → F)
    (child : ∀ i : Fin (m+1), (univ.filter fun g : F => mcaEvent
      (ReedSolomon.code (punctureDom dom i) k : Set (Fin m → F))
      ((e:ℝ≥0)/m) (u ∘ i.succAbove) (v ∘ i.succAbove) g).card≤B) :
    (univ.filter fun g : F => mcaEvent (ReedSolomon.code dom k : Set (Fin (m+1) → F))
      ((e:ℝ≥0)/(m+1:ℕ)) u v g).card*m ≤ (m+1)*B := by
  classical
  let G := univ.filter fun g : F => mcaEvent (ReedSolomon.code dom k : Set (Fin (m+1) → F))
    ((e:ℝ≥0)/(m+1:ℕ)) u v g
  let P (i : Fin (m+1)) (g : F) := mcaEvent (ReedSolomon.code (punctureDom dom i) k : Set (Fin m → F))
    ((e:ℝ≥0)/m) (u ∘ i.succAbove) (v ∘ i.succAbove) g
  have each (g : F) (hg : g∈G) : m≤(univ.filter fun i => P i g).card :=
    retained hm hk dom u v g (mem_filter.mp hg).2
  calc G.card*m = ∑ _g ∈ G, m := by simp
       _ ≤ ∑ g∈G, (univ.filter fun i => P i g).card := sum_le_sum each
       _ = ∑ i : Fin (m+1), (G.filter fun g => P i g).card := by simp only [card_filter]; rw [sum_comm]
       _ ≤ ∑ _i : Fin (m+1), B := by
         apply sum_le_sum
         intro i _
         exact (card_le_card (filter_subset_filter _ (subset_univ G))).trans (child i)
       _ = (m+1)*B := by simp

#print axioms at_most_one_repair
#print axioms retained
#print axioms count
end ArkLib.ProximityGap.Frontier.OnePunctureRetention
