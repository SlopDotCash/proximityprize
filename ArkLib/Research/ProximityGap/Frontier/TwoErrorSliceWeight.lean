/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.TwoErrorSlice
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-! # Weights of local two-error witnesses -/
namespace ProximityGap.TwoErrorSlice

open Finset Polynomial

variable {I J F : Type*} [Fintype I] [DecidableEq I] [Field F]

omit [Fintype I] in
private theorem choose_pair {A : Finset I} (h : A.card=2) :
    ∃ p : I × I, p.1 ≠ p.2 ∧ A={p.1,p.2} := by
  obtain ⟨u,v,hne,huv⟩ := card_eq_two.mp h
  exact ⟨(u,v),hne,huv⟩

/-- An ordering of a two-element error set, fixed independently of the sample. -/
noncomputable def ends (A : Finset I) (h : A.card=2) : I×I :=
  Classical.choose (choose_pair h)

omit [Fintype I] in
theorem ends_spec {A : Finset I} (h : A.card=2) :
    (ends A h).1 ≠ (ends A h).2 ∧ A={(ends A h).1,(ends A h).2} :=
  Classical.choose_spec (choose_pair h)

/-- Evaluate a local reward when exactly two nonantipodal errors remain. -/
noncomputable def sampleWeight (D : I ↪ F) (reward : I → I → F → ℕ)
    (E : Finset I) (err : I → F) (R : Finset I) : ℕ := by
  classical
  exact if h : (E \ R).card=2 then
    let p := ends (E \ R) h
    if D p.1 = -D p.2 then 0 else
      reward p.1 p.2 ((err p.2 / err p.1) * ∏ x ∈ (univ \ E) \ R, ratio D p.1 p.2 x)
    else 0

/-- Weight given by the first word's two residual errors and the unaffected sites. -/
noncomputable abbrev credit (D : I ↪ F) :=
  sampleWeight D (fun u v t => 3-penalty (alternatives D u v t).card)

/-- Every column has total weight at most six if each alternative is accounted
for by the supplied multiplicity. -/
private theorem sum_credit_six (T : Finset J) (w r : J → ℕ)
    (hw : ∀ j ∈ T, w j ≤ 3-penalty (r j))
    (hr : ∀ j ∈ T, T.card ≤ r j+1) : (∑ j ∈ T, w j) ≤ 6 := by
  have hcap (b : ℕ) (hh : ∀ j ∈ T, w j ≤ b) : (∑ j ∈ T, w j) ≤ T.card*b :=
    (sum_le_sum hh).trans_eq (by simp)
  by_cases h2 : T.card ≤ 2
  · have h := hcap 3 fun j hj => (hw j hj).trans (Nat.sub_le _ _)
    omega
  by_cases h3 : T.card ≤ 3
  · have h := hcap 2 fun j hj => by
      have hj' := hr j hj
      have hj'' := hw j hj
      simp only [penalty] at hj''
      split_ifs at hj'' <;> omega
    omega
  have h := hcap 0 fun j hj => by
    have hj' := hr j hj
    have hj'' := hw j hj
    simp only [penalty] at hj''
    split_ifs at hj'' <;> omega
  simpa using h.trans (by simp)

/-- In a length-(k+3) puncture, the number of words with two errors
is at most one more than the pair-product fiber witnessed by any such word. -/
theorem local_population (D : I ↪ F) (P : J → F[X]) (hin : Function.Injective P) (W : I → F)
    (T : Finset J) (E : J → Finset I) (hE : ∀ j ∈ T, ∀ x, x ∈ E j ↔ (P j).eval (D x) ≠ W x)
    {k : ℕ} (hdeg : ∀ j ∈ T, (P j).natDegree < k) (R : Finset I)
    (hU : (univ \ R).card=k+3) (pairSize : ∀ {j}, j∈T → (E j\R).card=2) (j : J) (hj : j∈T) :
    let p := ends (E j\R) (pairSize hj)
    T.card ≤ (alternatives D p.1 p.2
      (((P j).eval (D p.2)-W p.2)/((P j).eval (D p.1)-W p.1) *
       ∏ x ∈ (univ \ E j) \ R, ratio D p.1 p.2 x)).card+1 := by
  classical
  let A j := E j \ R
  let U := (univ : Finset I) \ R
  have size {j} (hj : j∈T) : (A j).card=2 := pairSize hj
  have hk : 0<k := (Nat.zero_le _).trans_lt (hdeg _ hj)
  have sub (j) : A j ⊆ U := by intro x hx; exact mem_sdiff.mpr ⟨mem_univ _, (mem_sdiff.mp hx).2⟩
  have agree {j x} (hj : j ∈ T) (hx : x ∈ U) (ha : x ∉ A j) : (P j).eval (D x) = W x := by
    by_contra he
    exact ha (mem_sdiff.mpr ⟨(hE j hj x).mpr he,(mem_sdiff.mp hx).2⟩)
  have roots {i j} (hi : i ∈ T) (hj : j ∈ T) (x) (hx : x ∈ U \ (A i ∪ A j)) :
      ((P i)-(P j)).eval (D x) = 0 := by
    obtain ⟨hxu,hx'⟩ := mem_sdiff.mp hx
    rw [eval_sub,agree hi hxu (fun h => hx' (mem_union_left _ h)),
      agree hj hxu (fun h => hx' (mem_union_right _ h)),sub_self]
  have cap {i j} (hi : i ∈ T) (hj : j ∈ T) (hne : i ≠ j) :
      Disjoint (A i) (A j) := by
    have hn := sub_ne_zero.mpr (hin.ne hne)
    have hd := natDegree_le_of_dvd (Polynomial.prod_X_sub_C_dvd _ D D.injective.injOn _ (roots hi hj)) hn
    change (Lagrange.nodal (U \ (A i ∪ A j)) D).natDegree ≤ _ at hd
    rw [Lagrange.natDegree_nodal,card_sdiff_of_subset (union_subset (sub i) (sub j)),hU] at hd
    have hlt := hd.trans ((natDegree_sub_le _ _).trans (max_le
      (Nat.le_sub_one_of_lt (hdeg _ hi)) (Nat.le_sub_one_of_lt (hdeg _ hj))))
    have hh := card_union_add_card_inter (A i) (A j)
    rw [size hi,size hj] at hh
    exact disjoint_iff_inter_eq_empty.mpr (card_eq_zero.mp (by omega))
  have inj : (↑T : Set J).InjOn A := by
    intro i hi j hj he
    by_contra hne
    have h := cap hi hj hne
    rw [he,disjoint_self] at h
    have sj := size hj
    rw [h] at sj
    simp at sj
  let p := ends (A j) (size hj)
  obtain ⟨hnep,hpair⟩ := ends_spec (size hj)
  change p.1 ≠ p.2 at hnep
  change A j={p.1,p.2} at hpair
  have hu : p.1 ∈ A j := hpair ▸ mem_insert_self ..
  have hv : p.2 ∈ A j := hpair ▸ mem_insert_of_mem (mem_singleton_self _)
  let V := (univ \ E j) \ R
  let target := (((P j).eval (D p.2)-W p.2)/((P j).eval (D p.1)-W p.1)) *
      ∏ x ∈ V, ratio D p.1 p.2 x
  have hh : (T.erase j).card ≤ (alternatives D p.1 p.2 target).card := by
    apply card_le_card_of_injOn A _ (inj.mono (by exact_mod_cast erase_subset j T))
    intro l hl
    obtain ⟨hnej,hl⟩ := mem_erase.mp hl
    have dis := cap hj hl hnej.symm
    have dis' := disjoint_left.mp dis
    have subV : A l ⊆ V := by
      intro x hx
      obtain ⟨_,hr⟩ := mem_sdiff.mp hx
      apply mem_sdiff.mpr
      exact ⟨mem_sdiff.mpr ⟨mem_univ _,fun he => dis' (mem_sdiff.mpr ⟨he,hr⟩) hx⟩,hr⟩
    have heq : V \ A l = U \ (A j ∪ A l) := by ext x; simp [V,U,A]; tauto
    have cV : (V \ A l).card = k-1 := by
      rw [heq, card_sdiff_of_subset (union_subset (sub j) (sub l)),hU,card_union_of_disjoint dis,
        size hj,size hl]
      omega
    have altRem (x) (hx : x ∈ A j) : (P l).eval (D x)=W x :=
      agree hl (sub j hx) (dis' hx)
    have ea (x) (hx : x ∈ A j) : ((P j)-(P l)).eval (D x) = (P j).eval (D x)-W x := by
      rw [eval_sub,altRem x hx]
    have nz (x) (hx : x ∈ A j) : ((P j)-(P l)).eval (D x) ≠ 0 := by
      rw [ea x hx]
      exact sub_ne_zero.mpr ((hE _ hj _).mp (mem_sdiff.mp hx).1)
    have key := alternative_product D p.1 p.2 V (A l) subV (P j-P l)
      (by rw [cV]; exact (natDegree_sub_le _ _).trans (max_le
            (Nat.le_sub_one_of_lt (hdeg _ hj)) (Nat.le_sub_one_of_lt (hdeg _ hl))))
      (by rw [heq]; exact roots hj hl) (nz _ hu) (nz _ hv)
    apply mem_filter.mpr
    refine ⟨mem_powersetCard.mpr ⟨?_,size hl⟩,?_⟩
    · intro x hx
      simp only [mem_erase,mem_univ,and_true]
      exact ⟨fun h => dis' hv (h ▸ hx), fun h => dis' hu (h ▸ hx)⟩
    · simpa only [target,ea _ hv,ea _ hu] using key
  rw [card_erase_of_mem hj] at hh
  change T.card ≤ (alternatives D p.1 p.2 target).card+1
  omega

/-- The column bound on actual Reed–Solomon list members at an arbitrary word. -/
theorem column (D : I ↪ F) (P : J → F[X]) (hin : Function.Injective P) (W : I → F)
    (T : Finset J) (E : J → Finset I) (hE : ∀ j ∈ T, ∀ x, x ∈ E j ↔ (P j).eval (D x) ≠ W x)
    (hdeg : ∀ j ∈ T, (P j).natDegree < 64) (R : Finset I)
    (hU : (univ \ R).card=67) :
    (∑ j ∈ T, credit D (E j) (fun x => (P j).eval (D x)-W x) R) ≤ 6 := by
  classical
  let A j := E j \ R
  let U := (univ : Finset I) \ R
  let T' := T.filter fun j => (A j).card=2
  let w j := credit D (E j) (fun x => (P j).eval (D x)-W x) R
  have hzero (j) (hj : j ∈ T) (hn : j ∉ T') : w j = 0 := by
    have h : (E j \ R).card ≠ 2 := fun he => hn (mem_filter.mpr ⟨hj,he⟩)
    simp [w,credit,sampleWeight,h]
  have eqsum : (∑ j ∈ T', w j) = ∑ j ∈ T, w j :=
    sum_subset (filter_subset _ _) hzero
  rw [← eqsum]
  have size {j} (hj : j ∈ T') : (A j).card=2 := (mem_filter.mp hj).2
  let r (j : J) := if hj : j ∈ T' then
    let p := ends (A j) (size hj)
    (alternatives D p.1 p.2 (((P j).eval (D p.2)-W p.2)/((P j).eval (D p.1)-W p.1) *
        ∏ x ∈ (univ \ E j) \ R, ratio D p.1 p.2 x)).card else 0
  apply sum_credit_six T' w r
  · intro j hj
    simp only [w,credit,sampleWeight,r,show (E j \ R).card=2 from size hj,dite_eq_left hj, dite_true]
    split_ifs <;> simp_all [A]
  intro j hj
  have count := local_population D P hin W T' E (fun i hi => hE i (mem_filter.mp hi).1)
    (fun i hi => hdeg i (mem_filter.mp hi).1) R hU (fun {i} hi => size hi) j hj
  simpa [r,hj,A] using count

end ProximityGap.TwoErrorSlice

#print axioms ProximityGap.TwoErrorSlice.column
