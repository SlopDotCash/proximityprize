/-
Copyright (c) 2026 Mikhail Izhutkin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mikhail Izhutkin (mashingaan, @mashingaan)
-/
import Research.ProximityPrize.Frontier._IncidenceWeightedTriples

set_option autoImplicit false
attribute [local instance] Classical.propDecidable
namespace ProximityGap.IncidenceExteriorLineCap
open ProximityGap.IncidenceAffineLines

/-- Private coordinates on a canonical bad-witness line except at most two are contained in the
error intersection of every two distinct heads. This uses the same canonical assumptions
as the occupancy cap, with no additional Reed-Solomon hypothesis. -/
theorem line_card_le_pair_error_intersection_add_two
    {F I Coord A : Type} [Field F] [DecidableEq I]
    [Fintype Coord] [DecidableEq Coord] [AddCommGroup A] [Module F A]
    (gamma : I → F) (w : I → (Coord → A)) (hinj : Function.Injective gamma)
    (B : Finset I) (C : Submodule F (Coord → A)) (T : I → Finset Coord)
    (u0 u1 U D : Coord → A)
    (hline : ∀ i ∈ B, OnLine gamma w U D i)
    (hwC : ∀ i ∈ B, w i ∈ C)
    (hag : ∀ i ∈ B, ∀ x ∈ T i, w i x = u0 x + gamma i • u1 x)
    (hno : ∀ i ∈ B, ¬ ∃ f0 ∈ C, ∃ f1 ∈ C,
      ∀ x ∈ T i, f0 x = u0 x ∧ f1 x = u1 x)
    {a b : I} (ha : a ∈ B) (hb : b ∈ B) (hab : a ≠ b) :
    B.card ≤ ((T a)ᶜ ∩ (T b)ᶜ).card + 2 := by
  classical
  obtain ⟨hUC,hDC⟩ := params_mem_code_of_two gamma w hinj C hab
    (hline a ha) (hline b hb) (hwC a ha) (hwC b hb)
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
  have hex : ∀ i : ↥B, ∃ x ∈ T i.val, ¬ (u0 x = U x ∧ u1 x = D x) := by
    intro i
    by_contra hn
    push Not at hn
    apply hno i.val i.property
    refine ⟨U,hUC,D,hDC,?_⟩
    intro x hx
    exact ⟨(hn x hx).1.symm,(hn x hx).2.symm⟩
  choose xs hxsT hxsNot using hex
  have hxinj : Function.Injective xs := by
    intro i j he
    by_contra hn
    have hv : i.val ≠ j.val := fun h => hn (Subtype.ext h)
    have hxj : xs i ∈ T j.val := by
      rw [he]
      exact hxsT j
    exact hxsNot i (hpin i.val i.property j.val j.property hv (xs i)
      (Finset.mem_inter.mpr ⟨hxsT i,hxj⟩))
  let J : Finset ↥B := Finset.univ.filter (fun i => i.val ≠ a ∧ i.val ≠ b)
  have hsub : J.image xs ⊆ (T a)ᶜ ∩ (T b)ᶜ := by
    intro x hx
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨_,hia,hib⟩ := Finset.mem_filter.mp hi
    have hxa : xs i ∉ T a := by
      intro hx
      exact hxsNot i (hpin i.val i.property a ha hia (xs i)
        (Finset.mem_inter.mpr ⟨hxsT i,hx⟩))
    have hxb : xs i ∉ T b := by
      intro hx
      exact hxsNot i (hpin i.val i.property b hb hib (xs i)
        (Finset.mem_inter.mpr ⟨hxsT i,hx⟩))
    exact Finset.mem_inter.mpr ⟨Finset.mem_compl.mpr hxa,Finset.mem_compl.mpr hxb⟩
  let ia : ↥B := ⟨a,ha⟩
  let ib : ↥B := ⟨b,hb⟩
  have hsmall : Jᶜ ⊆ {ia,ib} := by
    intro i hi
    have hn : ¬ (i.val ≠ a ∧ i.val ≠ b) := by simpa [J] using hi
    have he : i.val = a ∨ i.val = b := by tauto
    rcases he with h | h
    · exact Finset.mem_insert.mpr (Or.inl (Subtype.ext h))
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (Subtype.ext h)))
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hxinj] at hc
  have hj := Finset.card_add_card_compl J
  rw [Fintype.card_coe] at hj
  have htwo : ({ia,ib} : Finset ↥B).card ≤ 2 := by
    simpa only [Finset.card_singleton] using Finset.card_insert_le ia ({ib} : Finset ↥B)
  have hcompl : Jᶜ.card ≤ 2 := (Finset.card_le_card hsmall).trans htwo
  omega

/-- A witness outside a line sharpens the line occupancy cap through distance. -/
theorem bad_witness_exterior_line_cap
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
    (U D : Coord → A) : (S.filter (OnLine gamma w U D)).card ≤ 3*t-d+1 := by
  classical
  let B := S.filter (OnLine gamma w U D)
  change B.card ≤ 3*t-d+1
  by_cases hsmall : B.card ≤ 1
  · omega
  · obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp (by omega : 1 < B.card)
    have hBsub : B ⊆ S := Finset.filter_subset _ _
    have hcap : B.card ≤ t+1 :=
      bad_witness_line_cap t gamma w hinj S C T u0 u1 hwC hcompl hwag hno U D
    have houtside : ∃ c ∈ S, c ∉ B := by
      by_contra h
      push Not at h
      have hsub : S ⊆ B := fun c hc => h c hc
      have hcard := Finset.card_le_card hsub
      omega
    obtain ⟨c,hc,hcB⟩ := houtside
    have haL := (Finset.mem_filter.mp ha).2
    have hbL := (Finset.mem_filter.mp hb).2
    have hnc : ¬ CollinearTriple gamma w a b c := by
      intro h
      exact hcB (Finset.mem_filter.mpr ⟨hc,
        collinear_triple_forces_onLine gamma w hinj hab haL hbL h⟩)
    have hdist := error_union_gt_of_noncollinear gamma w hinj C d hC T u0 u1 hab
      (hwC a (hBsub ha)) (hwC b (hBsub hb)) (hwC c hc)
      (hwag a (hBsub ha)) (hwag b (hBsub hb)) (hwag c hc) hnc
    have hint := line_card_le_pair_error_intersection_add_two gamma w hinj B C T u0 u1 U D
      (fun i hi => (Finset.mem_filter.mp hi).2)
      (fun i hi => hwC i (hBsub hi)) (fun i hi => hwag i (hBsub hi))
      (fun i hi => hno i (hBsub hi)) ha hb hab
    have hpair := Finset.card_union_add_card_inter (T a)ᶜ (T b)ᶜ
    have htriple := Finset.card_union_le ((T a)ᶜ ∪ (T b)ᶜ) (T c)ᶜ
    have hta := hcompl a (hBsub ha)
    have htb := hcompl b (hBsub hb)
    have htc := hcompl c hc
    omega

end ProximityGap.IncidenceExteriorLineCap
#print axioms ProximityGap.IncidenceExteriorLineCap.line_card_le_pair_error_intersection_add_two
#print axioms ProximityGap.IncidenceExteriorLineCap.bad_witness_exterior_line_cap
