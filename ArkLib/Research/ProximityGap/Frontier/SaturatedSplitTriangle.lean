/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Data.Polynomial.FiniteDomainQuotient
import ArkLib.Research.ProximityGap.Frontier.SaturatedListCliques
import Mathlib.Tactic

/-! # Three disjoint fibers forced by a saturated four-clique

Cancel the common locator of three selected Reed–Solomon differences.
The residual polynomials have three disjoint, fully split level sets.
-/
namespace ProximityGap.SaturatedSplitTriangle

open Finset Polynomial
variable {F I : Type*} [Field F] [Fintype I] [DecidableEq I]

/-- A four-clique contains a triple with a small common core. -/
theorem small_triple (S : Fin 4 → Finset I) {t d : ℕ}
    (hs : ∀ i, t ≤ (S i).card) (hp : ∀ i j, i ≠ j → (S i ∩ S j).card = d) :
    ∃ i j l, i ≠ j ∧ i ≠ l ∧ j ≠ l ∧
      3*(S i ∩ S j ∩ S l).card+4*t ≤ Fintype.card I+6*d := by
  classical
  let hit (s : Finset I) (x : I) : ℕ := if x ∈ s then 1 else 0
  have total (s : Finset I) : ∑ x, hit s x = s.card := by simp [hit]
  have point (x : I) : 3*(hit (S 0 ∩ S 1 ∩ S 2) x+hit (S 0 ∩ S 1 ∩ S 3) x+hit (S 0 ∩ S 2 ∩ S 3) x+hit (S 1 ∩ S 2 ∩ S 3) x)+
      4*(hit (S 0) x+hit (S 1) x+hit (S 2) x+hit (S 3) x) ≤ 4+4*(hit (S 0 ∩ S 1) x+hit (S 0 ∩ S 2) x+hit (S 0 ∩ S 3) x+hit (S 1 ∩ S 2) x+hit (S 1 ∩ S 3) x+hit (S 2 ∩ S 3) x) := by
    by_cases a : x ∈ S 0 <;> by_cases b : x ∈ S 1 <;> by_cases c : x ∈ S 2 <;>
      by_cases e : x ∈ S 3 <;> simp [hit,a,b,c,e]
  have count := Finset.sum_le_sum (s := univ) (fun x _ => point x)
  simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, card_univ,
    nsmul_eq_mul, Nat.cast_id, total] at count
  have p01 := hp 0 1 (by decide)
  have p02 := hp 0 2 (by decide)
  have p03 := hp 0 3 (by decide)
  have p12 := hp 1 2 (by decide)
  have p13 := hp 1 3 (by decide)
  have p23 := hp 2 3 (by decide)
  have h0 := hs 0
  have h1 := hs 1
  have h2 := hs 2
  have h3 := hs 3
  by_cases h012 : 3*(S 0 ∩ S 1 ∩ S 2).card+4*t ≤ Fintype.card I+6*d
  · exact ⟨0,1,2,by decide,by decide,by decide,h012⟩
  by_cases h013 : 3*(S 0 ∩ S 1 ∩ S 3).card+4*t ≤ Fintype.card I+6*d
  · exact ⟨0,1,3,by decide,by decide,by decide,h013⟩
  by_cases h023 : 3*(S 0 ∩ S 2 ∩ S 3).card+4*t ≤ Fintype.card I+6*d
  · exact ⟨0,2,3,by decide,by decide,by decide,h023⟩
  by_cases h123 : 3*(S 1 ∩ S 2 ∩ S 3).card+4*t ≤ Fintype.card I+6*d
  · exact ⟨1,2,3,by decide,by decide,by decide,h123⟩
  omega

omit [Fintype I] [DecidableEq I] in
/-- A polynomial attaining its root bound is a nonzero scalar times its nodal polynomial. -/
theorem saturated_factor (D : I ↪ F) (A : Finset I) {f : F[X]} (hn : f ≠ 0)
    (hd : f.natDegree ≤ A.card) (hf : ∀ i ∈ A, f.eval (D i) = 0) :
    ∃ b : F, b ≠ 0 ∧ f = C b * Lagrange.nodal A D := by
  obtain ⟨Q,hQ⟩ := Polynomial.prod_X_sub_C_dvd A D D.injective.injOn f hf
  change f = Lagrange.nodal A D * Q at hQ
  have hnQ : Q ≠ 0 := fun he => hn (by simpa [he] using hQ)
  rw [hQ,natDegree_mul Lagrange.nodal_ne_zero hnQ,Lagrange.natDegree_nodal] at hd
  have he := eq_C_of_natDegree_eq_zero (show Q.natDegree = 0 by omega)
  refine ⟨Q.coeff 0, fun h => hnQ (by simpa [h] using he), ?_⟩
  rw [mul_comm,hQ]
  conv_lhs => rhs; rw [he]

omit [Fintype I] in
private theorem nodal_split (D : I ↪ F) {U T : Finset I} (h : U ⊆ T) :
    Lagrange.nodal T D = Lagrange.nodal (T \ U) D * Lagrange.nodal U D := by
  conv_lhs => rw [← Finset.sdiff_union_of_subset h]
  exact Finset.prod_union disjoint_sdiff_self_left

/-- A fully saturated four-clique yields a nontrivial linear relation among
three monic products on disjoint domain sets of the same controlled size. Their
scaled ratio therefore has three complete fibers above zero, infinity and one. -/
theorem from_four (D : I ↪ F) (S : Fin 4 → Finset I) (P : Fin 4 → F[X]) (y : I → F)
    {t d : ℕ} (hin : Function.Injective P) (hdeg : ∀ i, (P i).natDegree ≤ d)
    (hsize : ∀ i, t ≤ (S i).card) (hag : ∀ i x, x ∈ S i → (P i).eval (D x) = y x)
    (hp : ∀ i j, i ≠ j → (S i ∩ S j).card = d) :
    ∃ (U V W : Finset I) (a b c : F), a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧
      Disjoint U V ∧ Disjoint U W ∧ Disjoint V W ∧ U.card = V.card ∧ U.card = W.card ∧
      4*t ≤ Fintype.card I+3*d+3*U.card ∧
      C a * Lagrange.nodal U D + C b * Lagrange.nodal V D = C c * Lagrange.nodal W D := by
  classical
  obtain ⟨i,j,l,hij,hil,hjl,hcore⟩ := small_triple S hsize hp
  let T := S i ∩ S j ∩ S l
  have ti : T ⊆ S i ∩ S j := inter_subset_left
  have tj : T ⊆ S j ∩ S l := by intro x h; simp only [T,mem_inter] at h ⊢; tauto
  have tl : T ⊆ S i ∩ S l := by intro x h; simp only [T,mem_inter] at h ⊢; tauto
  let A := (S i ∩ S j) \ T
  let B := (S j ∩ S l) \ T
  let E := (S i ∩ S l) \ T
  have hdA : A.card = d-T.card := by rw [card_sdiff_of_subset ti,hp i j hij]
  have hdB : B.card = d-T.card := by rw [card_sdiff_of_subset tj,hp j l hjl]
  have hdE : E.card = d-T.card := by rw [card_sdiff_of_subset tl,hp i l hil]
  have factor (a b : Fin 4) (hab : a ≠ b) : ∃ u : F, u ≠ 0 ∧
      P a - P b = C u * Lagrange.nodal (S a ∩ S b) D := by
    apply saturated_factor D _ (sub_ne_zero.mpr (hin.ne hab))
    · rw [hp a b hab]
      exact (natDegree_sub_le _ _).trans (max_le (hdeg _) (hdeg _))
    · intro x hx
      rw [eval_sub,hag a x (mem_inter.mp hx).1,hag b x (mem_inter.mp hx).2,sub_self]
  obtain ⟨a,na,ha⟩ := factor i j hij
  obtain ⟨b,nb,hb⟩ := factor j l hjl
  obtain ⟨c,nc,hc⟩ := factor i l hil
  refine ⟨A,B,E,a,b,c,na,nb,nc,?_,?_,?_,hdA.trans hdB.symm,hdA.trans hdE.symm,?_,?_⟩
  · apply disjoint_left.mpr
    intro x hx hy
    simp_all [A,B,T]
  · apply disjoint_left.mpr
    intro x hx hy
    simp_all [A,E,T]
  · apply disjoint_left.mpr
    intro x hx hy
    simp_all [B,E,T]
  · rw [hdA]
    have hle : T.card ≤ d := (Finset.card_le_card ti).trans_eq (hp i j hij)
    change 3*T.card+4*t ≤ _ at hcore
    omega
  · have he : (P i-P j)+(P j-P l)=P i-P l := by abel
    rw [ha,hb,hc,nodal_split D ti,nodal_split D tj,nodal_split D tl,
      ← mul_assoc,← mul_assoc,← mul_assoc,← add_mul] at he
    exact mul_right_cancel₀ Lagrange.nodal_ne_zero he

/-- Overshooting the first named production list budget by even one word forces
a polynomial pencil with at least 14,035,080 distinct sites on each of three full fibers. -/
theorem first_budget {I F : Type} [Fintype I] [DecidableEq I] [Field F]
    (D : I ↪ F) (hn : Fintype.card I = 1073741824)
    (hlarge : (1073741824 : ℕ∞) <
      Code.Lambda (ReedSolomon.code D 134217728 : Set (I → F)) (694116763/1073741824)) :
    ∃ (U V W : Finset I) (a b c : F), a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧
      Disjoint U V ∧ Disjoint U W ∧ Disjoint V W ∧ U.card = V.card ∧ U.card = W.card ∧
      14035080 ≤ U.card ∧
      C a * Lagrange.nodal U D + C b * Lagrange.nodal V D = C c * Lagrange.nodal W D := by
  classical
  obtain ⟨y,P,S,hin,hdeg,hs,hag,cl⟩ := SaturatedListCliques.from_list D
    (k := 134217728) (t := 379625061) (r := 4) (B := 1073741824) (by decide)
    (by rw [hn]; decide) (by rw [hn]; decide)
    (fun S hs hp => SaturatedListCliques.first_budget S hn (fun j => (hs j).ge) hp)
    (by rw [hn]; exact hlarge)
  let e := SimpleGraph.topEmbeddingOfNotCliqueFree cl
  have cap (i j : Fin 4) (hij : i ≠ j) : (S (e i) ∩ S (e j)).card = 134217727 := by
    have hlow := (e.map_rel_iff.mpr (show (SimpleGraph.completeGraph (Fin 4)).Adj i j from hij)).2
    apply le_antisymm _ hlow
    let T := S (e i) ∩ S (e j)
    have hne := sub_ne_zero.mpr (hin.ne (e.injective.ne hij))
    have hdvd : Lagrange.nodal T D ∣ P (e i)-P (e j) := by
      apply Polynomial.prod_X_sub_C_dvd T D D.injective.injOn
      intro x hx
      rw [eval_sub,hag _ x (mem_inter.mp hx).1,hag _ x (mem_inter.mp hx).2,sub_self]
    have hlo := natDegree_le_of_dvd hdvd hne
    rw [Lagrange.natDegree_nodal] at hlo
    exact hlo.trans ((natDegree_sub_le _ _).trans (max_le (by have := hdeg (e i); omega)
      (by have := hdeg (e j); omega)))
  obtain ⟨U,V,W,a,b,c,na,nb,nc,uv,uw,vw,huv,huw,hbound,rel⟩ := from_four D
    (fun i => S (e i)) (fun i => P (e i)) y (d := 134217727) (t := 379625061)
    (hin.comp e.injective) (fun i => by have := hdeg (e i); omega)
    (fun i => (hs (e i)).ge) (fun i => hag (e i)) cap
  rw [hn] at hbound
  exact ⟨U,V,W,a,b,c,na,nb,nc,uv,uw,vw,huv,huw,by omega,rel⟩

#print axioms from_four
#print axioms first_budget

end ProximityGap.SaturatedSplitTriangle
