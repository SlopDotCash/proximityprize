/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.FourHeadCoreDeterminant
import ArkLib.Research.ProximityGap.Frontier._HalfPredecessorSecantLines

/-! # The predecessor cap for four heads with noncollinear cubic residuals -/
set_option autoImplicit false
noncomputable section
open Finset Polynomial Code
open scoped NNReal
open _root_.ProximityGap
namespace ArkLib.ProximityGap.Frontier.FourHeadCommonRootObstruction
open HalfPredecessorBadEventRichPointBridge HalfPredecessorSecantLines HalfPredecessorLineCoreGeometry

variable {I F : Type} [Fintype I] [DecidableEq I] [Field F]

/-- Four noncollinear residual heads of degree at most `d` have at most
`n+3|R|+4d` core incidences when agreement with each residual is required
only off the set `R`. All four heads may agree on every site of `R`. -/
theorem incidence (dom : I ↪ F) (u v : I → F) (A B : Fin 4 → F[X]) (R : Finset I)
    (C : Fin 4 → Finset I) (d : ℕ) (ha : ∀ i, (A i).natDegree≤d) (hb : ∀ i, (B i).natDegree≤d)
    (htr : (A 1-A 0)*(B 2-B 0)-(B 1-B 0)*(A 2-A 0)≠0)
    (hne : ∀ i : Fin 3, (A 3,B 3)≠(A i.castSucc,B i.castSucc))
    (hc : ∀ i x, x∈C i → x∉R → (A i).eval (dom x)=u x ∧ (B i).eval (dom x)=v x) :
    (∑ i, (C i).card) ≤ Fintype.card I+3*R.card+4*d := by
  classical
  let E (i : Fin 4) := C i \ R
  have h := FourHeadCoreDeterminant.core_union_bound dom u v A B d ha hb htr hne E
    (fun i x hx => hc i x (mem_sdiff.mp hx).1 (mem_sdiff.mp hx).2)
  have hsub : univ.biUnion E ⊆ Rᶜ := by
    intro x hx
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp hx
    exact mem_compl.mpr (mem_sdiff.mp hi).2
  have cap := card_le_card hsub
  rw [card_compl] at cap
  have each (i : Fin 4) : (C i).card ≤ (E i).card+R.card := by
    have h := card_sdiff_add_card_inter (C i) R
    have z : (C i ∩ R).card ≤ R.card := card_le_card inter_subset_right
    dsimp [E]; omega
  have sum := sum_le_sum (s:=univ) (fun i _ => each i)
  rw [sum_add_distrib] at sum
  have total : (∑ _ : Fin 4, R.card)=4*R.card := by simp
  rw [total] at sum
  have hr := card_le_univ R
  omega

private theorem capacity {L t e c : ℕ} (hp : L*max 1 (t-c)+c ≤ t+e) :
    L≤e+1 ∧ (c+2≤t → 2*L≤e+2) := by
  cases L with
  | zero => simp
  | succ L =>
    by_cases near : t≤c
    · have h := Nat.mul_le_mul_left (L+1) (Nat.le_max_left 1 (t-c))
      simp only [Nat.mul_one] at h
      constructor <;> omega
    · have h := Nat.mul_le_mul_left (L+1) (Nat.le_max_right 1 (t-c))
      rw [Nat.add_mul,one_mul] at h
      have small := Nat.mul_le_mul_left L (show 1≤t-c by omega)
      simp only [Nat.mul_one] at small
      refine ⟨by omega,?_⟩
      intro hc
      have smaller := Nat.mul_le_mul_left L (show 2≤t-c by omega)
      omega

variable [Nonempty I] [Fintype F] [DecidableEq F]

/-- At the predecessor to the saturated quartet, four covering secants cannot exhaust
the second-prime budget if their values off `R` are common pointwise injective images
of noncollinear degree-`d` residual heads and `3|R|+4d+5 ≤ 60m`. This includes
degree `12m` residuals outside `4m−2` common roots. -/
theorem predecessor_cap {m k : ℕ} (hm : 0 < m) {dom : I ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin 2) I} (fam : BadScalarRichPointFamily dom k δ u)
    (hn : Fintype.card I=64*m) (ht : ⌈(1-δ)*(Fintype.card I : ℝ≥0)⌉₊=31*m)
    (L : Fin 4 → LineParameter F) (hl : ∀ i, (L i).1.natDegree<k ∧ (L i).2.natDegree<k)
    (G : Finset F) (cover : G ⊆ univ.biUnion (fun i => pointsOn fam (L i)))
    (A B : Fin 4 → F[X]) (R : Finset I) (d : ℕ) (hr : 3*R.card+4*d+5≤60*m)
    (ha : ∀ i, (A i).natDegree≤d) (hb : ∀ i, (B i).natDegree≤d)
    (htr : (A 1-A 0)*(B 2-B 0)-(B 1-B 0)*(A 2-A 0)≠0)
    (hne : ∀ i : Fin 3, (A 3,B 3)≠(A i.castSucc,B i.castSucc))
    (T : I → (F × F) → (F × F)) (hinj : ∀ x, x∉R → Function.Injective (T x))
    (hval : ∀ i x, x∉R → ((L i).1.eval (dom x),(L i).2.eval (dom x)) =
      T x ((A i).eval (dom x),(B i).eval (dom x))) :
    2*G.card ≤ 231*m+8 ∧ G.card ≤ 128*m := by
  classical
  let C (i : Fin 4) := jointCore dom (u 0) (u 1) (L i).1 (L i).2
  let P (x : I) := Function.invFun (T x) (u 0 x,u 1 x)
  have bound := incidence dom (fun x => (P x).1) (fun x => (P x).2) A B R C d ha hb htr hne
    (by
      intro i x hC hR
      obtain ⟨h1,h2⟩ := (mem_filter.mp hC).2
      have hp : T x ((A i).eval (dom x),(B i).eval (dom x))=(u 0 x,u 1 x) :=
        (hval i x hR).symm.trans (Prod.ext h1 h2)
      have inv : ((A i).eval (dom x),(B i).eval (dom x))=P x := by
        unfold P
        rw [← hp,Function.leftInverse_invFun (hinj x hR)]
      exact ⟨congrArg Prod.fst inv,congrArg Prod.snd inv⟩)
  rw [hn] at bound
  have small : ∃ i, (C i).card+2≤31*m := by
    by_contra! h
    simp [Fin.sum_univ_succ] at bound
    change (C 0).card + ((C 1).card + ((C 2).card + (C 3).card)) ≤ _ at bound
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    have h3 := h 3
    omega
  let K (i : Fin 4) := (pointsOn fam (L i)).card
  have cap (i : Fin 4) : K i ≤ 33*m+1 ∧ ((C i).card+2≤31*m → 2*K i≤33*m+2) := by
    apply capacity
    have h := fam.line_core_packing (L i).1 (L i).2 (pointsOn fam (L i)) (hl i).1 (hl i).2
      (pointsOn_subset_G fam (L i)) (fun g hg => ((mem_pointsOn_iff fam (L i) g).mp hg).2)
    rw [ht,hn] at h
    exact h.trans_eq (by omega)
  obtain ⟨i,hi⟩ := small
  have h := (cap i).2 hi
  have total : G.card≤∑ i, K i := (card_le_card cover).trans card_biUnion_le
  have h0 := (cap 0).1
  have h1 := (cap 1).1
  have h2 := (cap 2).1
  have h3 := (cap 3).1
  simp [Fin.sum_univ_succ] at total
  change G.card ≤ K 0 + (K 1 + (K 2 + K 3)) at total
  fin_cases i
  · change 2*K 0 ≤ _ at h; omega
  · change 2*K 1 ≤ _ at h; omega
  · change 2*K 2 ≤ _ at h; omega
  · change 2*K 3 ≤ _ at h; omega

#print axioms incidence
#print axioms predecessor_cap
end ArkLib.ProximityGap.Frontier.FourHeadCommonRootObstruction
