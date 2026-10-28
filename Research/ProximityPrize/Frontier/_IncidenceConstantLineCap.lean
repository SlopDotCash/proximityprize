/-
Copyright (c) 2026 Mikhail Izhutkin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mikhail Izhutkin (mashingaan, @mashingaan)
-/
import Research.ProximityPrize.Frontier._IncidenceWeightedTriples

set_option autoImplicit false
attribute [local instance] Classical.propDecidable

namespace ProximityGap.IncidenceConstantLineCap

open ProximityGap.IncidenceAffineLines

/-- Outside joint agreement, at most one head on a scalar-injective line agrees.
The resulting incidence count charges the complement to the heads' errors. -/
theorem line_agreement_mass
    {F I Coord A : Type} [Field F] [DecidableEq I]
    [Fintype Coord] [DecidableEq Coord] [AddCommGroup A] [Module F A]
    (gamma : I → F) (w : I → (Coord → A)) (hinj : Function.Injective gamma)
    (B : Finset I) (T : I → Finset Coord) (u0 u1 U D : Coord → A)
    (hline : ∀ i ∈ B, OnLine gamma w U D i)
    (hag : ∀ i ∈ B, ∀ x ∈ T i, w i x = u0 x + gamma i • u1 x) :
    let Q := Finset.univ.filter (fun x => ¬ (u0 x = U x ∧ u1 x = D x))
    B.card * Q.card ≤ Q.card + ∑ i ∈ B, (T i)ᶜ.card := by
  classical
  let Q := Finset.univ.filter (fun x => ¬ (u0 x = U x ∧ u1 x = D x))
  change B.card * Q.card ≤ Q.card + ∑ i ∈ B, (T i)ᶜ.card
  have hpin : ∀ i ∈ B, ∀ j ∈ B, i ≠ j → ∀ x ∈ T i ∩ T j,
      u0 x = U x ∧ u1 x = D x := by
    intro i hi j hj hij x hx
    obtain ⟨hxi,hxj⟩ := Finset.mem_inter.mp hx
    have ei := (hag i hi x hxi).symm.trans (congrFun (hline i hi) x)
    have ej := (hag j hj x hxj).symm.trans (congrFun (hline j hj) x)
    simp only [Pi.add_apply,Pi.smul_apply] at ei ej
    have hn : gamma i - gamma j ≠ 0 := sub_ne_zero.mpr (fun h => hij (hinj h))
    have hz : (gamma i - gamma j) • (u1 x - D x) = 0 := by
      calc
        _ = (u0 x + gamma i • u1 x - (U x + gamma i • D x)) -
            (u0 x + gamma j • u1 x - (U x + gamma j • D x)) := by module
        _ = 0 := by
          rw [ei,ej]
          abel
    have hu1 : u1 x = D x := by
      rcases smul_eq_zero.mp hz with h | h
      · exact False.elim (hn h)
      · exact sub_eq_zero.mp h
    rw [hu1] at ei
    exact ⟨add_right_cancel ei,hu1⟩
  let privateSet := fun i => Q ∩ T i
  have hdisj : (↑B : Set I).PairwiseDisjoint privateSet := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro x hxi hxj
    have hxQ := (Finset.mem_inter.mp hxi).1
    have hnot := (Finset.mem_filter.mp hxQ).2
    exact hnot (hpin i hi j hj hij x
      (Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hxi).2,(Finset.mem_inter.mp hxj).2⟩))
  have hsum : (∑ i ∈ B, (privateSet i).card) ≤ Q.card := by
    rw [← Finset.card_biUnion hdisj]
    apply Finset.card_le_card
    intro x hx
    obtain ⟨i,_,hxi⟩ := Finset.mem_biUnion.mp hx
    exact (Finset.mem_inter.mp hxi).1
  have hpoint : ∀ i ∈ B, Q.card ≤ (privateSet i).card + (T i)ᶜ.card := by
    intro i _
    have hp := Finset.card_inter_add_card_sdiff Q (T i)
    have he : (Q \ T i).card ≤ (T i)ᶜ.card := by
      apply Finset.card_le_card
      intro x hx
      exact Finset.mem_compl.mpr (Finset.mem_sdiff.mp hx).2
    dsimp [privateSet]
    omega
  have htot := Finset.sum_le_sum hpoint
  simp only [Finset.sum_const,smul_eq_mul,Finset.sum_add_distrib] at htot
  omega

/-- At `7t < 3(d+1)`, an outside bad witness excludes four heads on any line. -/
theorem bad_witness_line_cap_three
    {F I Coord A : Type} [Field F] [DecidableEq I]
    [Fintype Coord] [DecidableEq Coord] [AddCommGroup A] [Module F A]
    (gamma : I → F) (w : I → (Coord → A)) (hinj : Function.Injective gamma)
    (S : Finset I) (C : Submodule F (Coord → A)) (d t : ℕ)
    (hsize : t+1 < S.card) (ht : 7*t < 3*(d+1))
    (hC : ∀ z ∈ C, (∃ B : Finset Coord, B.card ≤ d ∧ ∀ x ∉ B, z x = 0) → z = 0)
    (T : I → Finset Coord) (u0 u1 : Coord → A)
    (hwC : ∀ i ∈ S, w i ∈ C)
    (hcompl : ∀ i ∈ S, (T i)ᶜ.card ≤ t)
    (hwag : ∀ i ∈ S, ∀ x ∈ T i, w i x = u0 x + gamma i • u1 x)
    (hno : ∀ i ∈ S, ¬ ∃ f0 ∈ C, ∃ f1 ∈ C,
      ∀ x ∈ T i, f0 x = u0 x ∧ f1 x = u1 x)
    (U D : Coord → A) : (S.filter (OnLine gamma w U D)).card ≤ 3 := by
  classical
  let B := S.filter (OnLine gamma w U D)
  change B.card ≤ 3
  by_contra hn
  have hlarge : 4 ≤ B.card := by omega
  have hBsub : B ⊆ S := Finset.filter_subset _ _
  obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp (by omega : 1 < B.card)
  have haL := (Finset.mem_filter.mp ha).2
  have hbL := (Finset.mem_filter.mp hb).2
  obtain ⟨hUC,hDC⟩ := params_mem_code_of_two gamma w hinj C hab haL hbL
    (hwC a (hBsub ha)) (hwC b (hBsub hb))
  have hcap : B.card ≤ t+1 :=
    bad_witness_line_cap t gamma w hinj S C T u0 u1 hwC hcompl hwag hno U D
  have hout : ∃ c ∈ S, c ∉ B := by
    by_contra h
    push Not at h
    have hc := Finset.card_le_card (show S ⊆ B from fun c hc => h c hc)
    omega
  obtain ⟨c,hc,hcB⟩ := hout
  let Q := Finset.univ.filter (fun x => ¬ (u0 x = U x ∧ u1 x = D x))
  have hdist : d+1 ≤ Q.card + t := by
    let z := w c - (U + gamma c • D)
    have hzC : z ∈ C := C.sub_mem (hwC c hc) (C.add_mem hUC (C.smul_mem _ hDC))
    have hvan : ∀ x ∉ Q ∪ (T c)ᶜ, z x = 0 := by
      intro x hx
      have hxQ : x ∉ Q := fun h => hx (Finset.mem_union.mpr (Or.inl h))
      have hxT : x ∈ T c := by
        by_contra hnT
        exact hx (Finset.mem_union.mpr (Or.inr (Finset.mem_compl.mpr hnT)))
      have hj : u0 x = U x ∧ u1 x = D x := by simpa [Q] using hxQ
      change w c x - (U x + gamma c • D x) = 0
      rw [hwag c hc x hxT,hj.1,hj.2,sub_self]
    have hbig : d < (Q ∪ (T c)ᶜ).card := by
      by_contra h
      have hz := hC z hzC ⟨Q ∪ (T c)ᶜ,by omega,hvan⟩
      have he : OnLine gamma w U D c := sub_eq_zero.mp hz
      exact hcB (Finset.mem_filter.mpr ⟨hc,he⟩)
    have hu := Finset.card_union_le Q (T c)ᶜ
    have hcT := hcompl c hc
    omega
  have hmass := line_agreement_mass gamma w hinj B T u0 u1 U D
    (fun i hi => (Finset.mem_filter.mp hi).2) (fun i hi => hwag i (hBsub hi))
  change B.card * Q.card ≤ Q.card + ∑ i ∈ B, (T i)ᶜ.card at hmass
  have herr : (∑ i ∈ B, (T i)ᶜ.card) ≤ B.card * t := by
    simpa only [Finset.sum_const,smul_eq_mul] using
      Finset.sum_le_sum (fun i hi => hcompl i (hBsub hi))
  have hqt : t ≤ Q.card := by omega
  have hsplit := Nat.sub_add_cancel hqt
  have hgap : B.card * (Q.card-t) ≤ (Q.card-t)+t := by
    rw [← hsplit,Nat.mul_add] at hmass
    omega
  have hmul := Nat.mul_le_mul_right (Q.card-t) hlarge
  omega

/-- Every distinct pair of canonical bad witnesses has a large error union.
An outside witness turns the pair into a noncollinear distance certificate. -/
theorem bad_witness_pair_union_distance
    {F I Coord A : Type} [Field F] [DecidableEq I]
    [Fintype Coord] [DecidableEq Coord] [AddCommGroup A] [Module F A]
    (gamma : I → F) (w : I → (Coord → A)) (hinj : Function.Injective gamma)
    (S : Finset I) (C : Submodule F (Coord → A)) (d t : ℕ)
    (hsize : t+1 < S.card)
    (hC : ∀ z ∈ C, (∃ B : Finset Coord, B.card ≤ d ∧ ∀ x ∉ B, z x = 0) → z = 0)
    (T : I → Finset Coord) (u0 u1 : Coord → A)
    (hwC : ∀ i ∈ S, w i ∈ C)
    (hcompl : ∀ i ∈ S, (T i)ᶜ.card ≤ t)
    (hwag : ∀ i ∈ S, ∀ x ∈ T i, w i x = u0 x + gamma i • u1 x)
    (hno : ∀ i ∈ S, ¬ ∃ f0 ∈ C, ∃ f1 ∈ C,
      ∀ x ∈ T i, f0 x = u0 x ∧ f1 x = u1 x)
    {a b : I} (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) :
    d+1 ≤ ((T a)ᶜ ∪ (T b)ᶜ).card + t := by
  classical
  obtain ⟨U,D,haL,hbL⟩ := exists_line_through_two gamma w hinj hab
  let B := S.filter (OnLine gamma w U D)
  have hcap : B.card ≤ t+1 :=
    bad_witness_line_cap t gamma w hinj S C T u0 u1 hwC hcompl hwag hno U D
  have hout : ∃ c ∈ S, c ∉ B := by
    by_contra h
    push Not at h
    have hc := Finset.card_le_card (show S ⊆ B from fun c hc => h c hc)
    omega
  obtain ⟨c,hc,hcB⟩ := hout
  have hnc : ¬ CollinearTriple gamma w a b c := by
    intro h
    exact hcB (Finset.mem_filter.mpr
      ⟨hc,collinear_triple_forces_onLine gamma w hinj hab haL hbL h⟩)
  have hdist := error_union_gt_of_noncollinear gamma w hinj C d hC T u0 u1 hab
    (hwC a ha) (hwC b hb) (hwC c hc)
    (hwag a ha) (hwag b hb) (hwag c hc) hnc
  have hu := Finset.card_union_le ((T a)ᶜ ∪ (T b)ᶜ) (T c)ᶜ
  have he := hcompl c hc
  omega

/-- With at most three heads on a line, an ordered distinct pair has at most
one collinear completion in the family. -/
theorem collinearTriples_card_le_square_of_line_cap_three
    {F I V : Type} [Field F] [DecidableEq I] [AddCommGroup V] [Module F V]
    (gamma : I → F) (w : I → V) (hinj : Function.Injective gamma)
    (S : Finset I)
    (hcap : ∀ U D, (S.filter (OnLine gamma w U D)).card ≤ 3) :
    (collinearTriples gamma w S).card ≤ S.card ^ 2 := by
  classical
  have hsum : (collinearTriples gamma w S).card =
      ∑ a ∈ S, ∑ b ∈ S,
        (S.filter (fun c => a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ CollinearTriple gamma w a b c)).card := by
    simp only [collinearTriples,Finset.product_eq_sprod,Finset.card_filter,Finset.sum_product]
  have hrow : ∀ a ∈ S, ∀ b ∈ S,
      (S.filter (fun c => a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ CollinearTriple gamma w a b c)).card ≤ 1 := by
    intro a ha b hb
    by_cases hab : a = b
    · subst b
      simp
    · obtain ⟨U,D,haL,hbL⟩ := exists_line_through_two gamma w hinj hab
      let B := S.filter (OnLine gamma w U D)
      have hp : ({a,b} : Finset I) ⊆ B := by
        intro x hx
        rcases Finset.mem_insert.mp hx with h | h
        · subst x
          exact Finset.mem_filter.mpr ⟨ha,haL⟩
        · have he := Finset.mem_singleton.mp h
          subst x
          exact Finset.mem_filter.mpr ⟨hb,hbL⟩
      have hpart := Finset.card_sdiff_add_card_eq_card hp
      have hpair : ({a,b} : Finset I).card = 2 := by simp [hab]
      have hbcap : B.card ≤ 3 := hcap U D
      have hrest : (B \ {a,b}).card ≤ 1 := by omega
      apply le_trans (Finset.card_le_card ?_) hrest
      intro c hc
      obtain ⟨hcS,_,hac,hbc,hcol⟩ := Finset.mem_filter.mp hc
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_filter.mpr ⟨hcS,
        collinear_triple_forces_onLine gamma w hinj hab haL hbL hcol⟩,?_⟩
      simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using
        (show c ≠ a ∧ c ≠ b from ⟨Ne.symm hac,Ne.symm hbc⟩)
  rw [hsum]
  calc
    _ ≤ ∑ a ∈ S, ∑ b ∈ S, (1 : ℕ) :=
      Finset.sum_le_sum (fun a ha => Finset.sum_le_sum (fun b hb => hrow a ha b hb))
    _ = _ := by simp [pow_two]

/-- A pair-union certificate reduces the penalty for every nondiagonal
degenerate triple from distance to the error budget. -/
theorem triple_mass_lower_of_pair_union
    {F I V X : Type} [Field F] [DecidableEq I] [DecidableEq X]
    [AddCommGroup V] [Module F V]
    (gamma : I → F) (w : I → V) (S : Finset I) (E : I → Finset X) (D t : ℕ)
    (hpair : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → D ≤ (E a ∪ E b).card+t)
    (hlow : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S,
      a ≠ b → a ≠ c → b ≠ c → ¬ CollinearTriple gamma w a b c →
      D ≤ (E a ∪ E b ∪ E c).card) :
    D*S.card^3 ≤ (∑ a ∈ S, ∑ b ∈ S, ∑ c ∈ S, (E a ∪ E b ∪ E c).card) +
      t*((collinearTriples gamma w S).card+3*S.card^2)+D*S.card := by
  classical
  let P := S ×ˢ (S ×ˢ S)
  let R := P.filter (fun p => p.1 = p.2.1 ∨ p.1 = p.2.2 ∨ p.2.1 = p.2.2)
  let B := R ∪ collinearTriples gamma w S
  let J := P.filter (fun p => p.1 = p.2.1 ∧ p.1 = p.2.2)
  have hBsub : B ⊆ P := Finset.union_subset (Finset.filter_subset _ _)
    (Finset.filter_subset _ _)
  have hB : B.card ≤ (collinearTriples gamma w S).card+3*S.card^2 := by
    have hr : R.card ≤ 3*S.card^2 := by
      simpa only [R,P] using repeated_triples_card_le S
    have hu := Finset.card_union_le R (collinearTriples gamma w S)
    dsimp only [B]
    omega
  have hJ : J.card ≤ S.card := by
    apply Finset.card_le_card_of_injOn (fun p : I × (I × I) => p.1)
    · intro p hp
      exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
    · intro p hp q hq he
      have ep := (Finset.mem_filter.mp hp).2
      have eq := (Finset.mem_filter.mp hq).2
      exact Prod.ext he (Prod.ext (ep.1.symm.trans (he.trans eq.1))
        (ep.2.symm.trans (he.trans eq.2)))
  have hpoint : ∀ p ∈ P, D ≤ (E p.1 ∪ E p.2.1 ∪ E p.2.2).card +
      (if p ∈ B then t else 0)+(if p ∈ J then D else 0) := by
    intro p hp
    obtain ⟨ha,hbc⟩ := Finset.mem_product.mp hp
    obtain ⟨hb,hc⟩ := Finset.mem_product.mp hbc
    by_cases hj : p ∈ J
    · simp only [if_pos hj]
      omega
    · simp only [if_neg hj,add_zero]
      by_cases hpb : p ∈ B
      · simp only [if_pos hpb]
        by_cases hab : p.1 = p.2.1
        · have hac : p.1 ≠ p.2.2 := by
            intro he
            exact hj (Finset.mem_filter.mpr ⟨hp,hab,he⟩)
          have h := hpair _ ha _ hc hac
          have hm := Finset.card_le_card (show E p.1 ∪ E p.2.2 ⊆
            E p.1 ∪ E p.2.1 ∪ E p.2.2 by
              intro x hx
              rcases Finset.mem_union.mp hx with hx | hx
              · exact Finset.mem_union_left _ (Finset.mem_union_left _ hx)
              · exact Finset.mem_union_right _ hx)
          omega
        · have h := hpair _ ha _ hb hab
          have hm := Finset.card_le_card (Finset.subset_union_left
            (s₁ := E p.1 ∪ E p.2.1) (s₂ := E p.2.2))
          omega
      · simp only [if_neg hpb,add_zero]
        have hr : p ∉ R := fun h => hpb (Finset.mem_union_left _ h)
        have hl : p ∉ collinearTriples gamma w S :=
          fun h => hpb (Finset.mem_union_right _ h)
        have hne : p.1 ≠ p.2.1 ∧ p.1 ≠ p.2.2 ∧ p.2.1 ≠ p.2.2 := by
          simpa only [R,Finset.mem_filter,hp,true_and,not_or] using hr
        have hnc : ¬ CollinearTriple gamma w p.1 p.2.1 p.2.2 := by
          intro h
          exact hl (Finset.mem_filter.mpr ⟨hp,hne.1,hne.2.1,hne.2.2,h⟩)
        exact hlow _ ha _ hb _ hc hne.1 hne.2.1 hne.2.2 hnc
  have hsum := Finset.sum_le_sum hpoint
  have hind (K : Finset (I × (I × I))) (hK : K ⊆ P) (v : ℕ) :
      (∑ p ∈ P, if p ∈ K then v else 0) = K.card*v := by
    rw [← Finset.sum_filter]
    have hf : P.filter (fun p => p ∈ K) = K := by
      ext p
      simp only [Finset.mem_filter]
      exact ⟨fun h => h.2,fun h => ⟨hK h,h⟩⟩
    rw [hf,Finset.sum_const,smul_eq_mul]
  simp only [Finset.sum_add_distrib] at hsum
  rw [hind B hBsub t,hind J (Finset.filter_subset _ _) D] at hsum
  have hcP : P.card = S.card^3 := by
    simp only [P,Finset.card_product]
    ring
  simp only [Finset.sum_const,smul_eq_mul,hcP] at hsum
  have hm : (∑ p ∈ P, (E p.1 ∪ E p.2.1 ∪ E p.2.2).card) =
      ∑ a ∈ S, ∑ b ∈ S, ∑ c ∈ S, (E a ∪ E b ∪ E c).card := by
    simp only [P,Finset.sum_product]
  rw [hm] at hsum
  nlinarith [Nat.mul_le_mul_left t hB,Nat.mul_le_mul_left D hJ]

end ProximityGap.IncidenceConstantLineCap

#print axioms ProximityGap.IncidenceConstantLineCap.line_agreement_mass
#print axioms ProximityGap.IncidenceConstantLineCap.bad_witness_pair_union_distance
#print axioms ProximityGap.IncidenceConstantLineCap.triple_mass_lower_of_pair_union
#print axioms ProximityGap.IncidenceConstantLineCap.bad_witness_line_cap_three
#print axioms ProximityGap.IncidenceConstantLineCap.collinearTriples_card_le_square_of_line_cap_three
