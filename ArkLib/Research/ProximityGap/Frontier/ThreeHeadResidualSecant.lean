/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.ThreeHeadDeterminantCover
import ArkLib.Research.ProximityGap.Frontier.FourHeadCoreDeterminant
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeQuarticInterpolation

/-! # The residual secant of three large noncollinear heads

Three outside sections agree on the complement of the joint cores. When this
forces more shared sites than the degree, all outside sections lie on the
secant of any two of them. A four-head determinant then bounds its population.
-/
set_option autoImplicit false
open Finset Polynomial Code
open scoped NNReal
namespace ArkLib.ProximityGap.Frontier.ThreeHeadResidualSecant
open HalfPredecessorLineCoreGeometry HalfPredecessorSecantLines HalfPredecessorBadEventRichPointBridge
open HalfPredecessorRateEighthFullWiring HalfPredecessorLineCorePacking
open HalfPredecessorRateQuarterDeterminantMultiplicity

variable {I F : Type} [Fintype I] [DecidableEq I] [Nonempty I] [Field F] [Fintype F] [DecidableEq F]
variable {dom : I ↪ F} {k : ℕ} {δ : ℝ≥0} {u : WordStack F (Fin 2) I}

private abbrev core (dom : I ↪ F) (u : WordStack F (Fin 2) I) (l : LineParameter F) := jointCore dom (u 0) (u 1) l.1 l.2

/-- On the complement of three cores an outside section retains all but three
degree budgets of its agreements. -/
private theorem off_card (fam : BadScalarRichPointFamily dom k δ u)
    (hk : 1 ≤ k) (a b c : LineParameter F)
    (hl : ∀ l ∈ ({a,b,c} : Finset _), l ∈ lineParameters fam) {z : F}
    (hz : z ∈ fam.G \ (pointsOn fam a ∪ pointsOn fam b ∪ pointsOn fam c)) :
    ⌈(1-δ)*(Fintype.card I:ℝ≥0)⌉₊ - 3*(k-1) ≤
      (fullAgreement dom (u 0) (u 1) z (fam.q z) \
        (core dom u a ∪ core dom u b ∪ core dom u c)).card := by
  classical
  let D := fun l => core dom u l
  let A := fullAgreement dom (u 0) (u 1) z (fam.q z)
  have hG := (mem_sdiff.mp hz).1
  have hoff := (mem_sdiff.mp hz).2
  simp only [mem_union, not_or] at hoff
  have hi (l : LineParameter F) (h : l ∈ ({a,b,c} : Finset _)) (hn : z ∉ pointsOn fam l) :
      (A ∩ D l).card ≤ k-1 := by
    have hd := lineParameter_degree_lt fam (hl l h)
    exact fullAgreement_inter_jointCore_card_le dom (u 0) (u 1) hk (fam.degree_lt z hG)
      hd.1 hd.2 (fun he => hn ((mem_pointsOn_iff fam l z).2 ⟨hG,he⟩))
  have h1 := hi a (by simp) hoff.1.1
  have h2 := hi b (by simp) hoff.1.2
  have h3 := hi c (by simp) hoff.2
  have h4 := card_union_le (A ∩ D a) (A ∩ D b)
  have h5 := card_union_le ((A ∩ D a) ∪ (A ∩ D b)) (A ∩ D c)
  have h6 := card_sdiff_add_card_inter A (D a ∪ D b ∪ D c)
  simp only [inter_union_distrib_left] at h6
  have ht := fam.threshold_le z hG
  change _ ≤ A.card at ht
  change _ ≤ (A \ (D a ∪ D b ∪ D c)).card
  omega

/-- If the complementary agreement sets of every three outside sections have
more than a degree's worth of common sites, they all belong to a fourth head. -/
theorem outside_secant (fam : BadScalarRichPointFamily dom k δ u)
    (hk : 1 ≤ k) (a b c : LineParameter F)
    (hl : ∀ l ∈ ({a,b,c} : Finset _), l ∈ lineParameters fam)
    (hgap : 2*(Fintype.card I -
      (core dom u a ∪ core dom u b ∪ core dom u c).card)+(k-1) <
      3*(⌈(1-δ)*(Fintype.card I:ℝ≥0)⌉₊-3*(k-1)))
    {g h : F} (hne : g ≠ h)
    (hg : g ∈ fam.G \ (pointsOn fam a ∪ pointsOn fam b ∪ pointsOn fam c))
    (hh : h ∈ fam.G \ (pointsOn fam a ∪ pointsOn fam b ∪ pointsOn fam c)) :
    fam.G \ (pointsOn fam a ∪ pointsOn fam b ∪ pointsOn fam c) ⊆
      pointsOn fam (secantParameter fam g h) := by
  classical
  let U := core dom u a ∪ core dom u b ∪ core dom u c
  let A := fun z => fullAgreement dom (u 0) (u 1) z (fam.q z)
  let J := fun z => A z \ U
  have sub (z : F) : J z ⊆ Uᶜ := by
    intro i hi
    exact mem_compl.mpr (mem_sdiff.mp hi).2
  intro z hz
  have zg := (mem_sdiff.mp hz).1
  have gg := (mem_sdiff.mp hg).1
  have gh := (mem_sdiff.mp hh).1
  by_cases he : z = g
  · subst z
    exact first_point_mem_pointsOn_secant fam gg
  by_cases hf : z = h
  · subst z
    exact second_point_mem_pointsOn_secant fam gh hne
  have htri := three_set_inter_card_gt (Uᶜ) (J g) (J h) (J z) _ (k-1)
    (sub _) (sub _) (sub _) (off_card fam hk a b c hl hg)
    (off_card fam hk a b c hl hh) (off_card fam hk a b c hl hz) (by rw [card_compl]; exact hgap)
  have inc : J g ∩ J h ∩ J z ⊆ A g ∩ A h ∩ A z := by
    exact inter_subset_inter (inter_subset_inter sdiff_subset sdiff_subset) sdiff_subset
  have hp := htri.trans_le (card_le_card inc)
  have slope : slopePolynomial g h (fam.q g) (fam.q h) = slopePolynomial g z (fam.q g) (fam.q z) := by
    by_contra hn
    exact (Nat.not_lt_of_ge (triple_fullAgreement_card_le_pred_of_slope_ne dom (u 0) (u 1)
      hk hne (Ne.symm he) (fam.degree_lt g gg) (fam.degree_lt h gh) (fam.degree_lt z zg) hn)) hp
  exact (mem_pointsOn_iff fam _ z).mpr ⟨zg,by
    simpa only [secantParameter] using third_point_on_secant_line_of_slope_eq (Ne.symm he) slope.symm⟩

/-- The fourth head pays for the first three core sizes in the four-head determinant. -/
theorem fourth_core (fam : BadScalarRichPointFamily dom k δ u) (a b c l : LineParameter F)
    (hl : ∀ x ∈ ({a,b,c,l} : Finset _), x ∈ lineParameters fam)
    (hdet : threeLineDeterminant a b c ≠ 0) (ha : l ≠ a) (hb : l ≠ b) (hc : l ≠ c) :
    (core dom u a).card + (core dom u b).card + (core dom u c).card +
      (core dom u l).card ≤ Fintype.card I + 4*(k-1) := by
  classical
  let L : Fin 4 → LineParameter F := ![a,b,c,l]
  let D := fun i => core dom u (L i)
  have hd (i : Fin 4) := lineParameter_degree_lt fam (hl (L i) (by fin_cases i <;> simp [L]))
  have h := _root_.ProximityGap.FourHeadCoreDeterminant.core_union_bound dom (u 0) (u 1)
    (fun i => (L i).1) (fun i => (L i).2) (k-1)
    (fun i => Nat.le_pred_of_lt (hd i).1) (fun i => Nat.le_pred_of_lt (hd i).2)
    hdet (by
      intro i
      fin_cases i
      · exact ha
      · exact hb
      · exact hc) D
    (fun _ _ hx => (mem_filter.mp hx).2)
  have hu := card_le_univ (univ.biUnion D)
  have hs : (∑ i, (D i).card) = (core dom u a).card + (core dom u b).card +
      (core dom u c).card + (core dom u l).card := by simp [D,L,Fin.sum_univ_succ,Nat.add_assoc]
  omega

private abbrev n : ℕ := 1073741824
private abbrev t : ℕ := 357913947
private abbrev d : ℕ := 76695847

/-- In the production window every bad label outside the three saturated heads
belongs to a common fourth head if there are at least two. It carries at most 14. -/
theorem fourteen_outside (fam : BadScalarRichPointFamily dom k δ u) (hk : 1 ≤ k)
    (hdim : k-1 ≤ d) (hn : Fintype.card I = n)
    (ht : ⌈(1-δ)*(Fintype.card I:ℝ≥0)⌉₊ = t) (a b c : LineParameter F)
    (hl : ∀ x ∈ ({a,b,c} : Finset _), x ∈ lineParameters fam)
    (hdet : threeLineDeterminant a b c ≠ 0)
    (cores : ∀ x ∈ ({a,b,c} : Finset _), t-1 ≤ (core dom u x).card) :
    (fam.G \ (pointsOn fam a ∪ pointsOn fam b ∪ pointsOn fam c)).card ≤ 14 := by
  classical
  let S := fam.G \ (pointsOn fam a ∪ pointsOn fam b ∪ pointsOn fam c)
  by_contra! hbig
  have htwo : 1 < S.card := by change 14 < S.card at hbig; omega
  obtain ⟨g,hg,h,hh,hne⟩ := one_lt_card.mp htwo
  let l := secantParameter fam g h
  have gg := (mem_sdiff.mp hg).1
  have hl' : l ∈ lineParameters fam := secantParameter_mem_lineParameters fam gg (mem_sdiff.mp hh).1 hne
  have hga := first_point_mem_pointsOn_secant fam (beta:=h) gg
  change g ∈ pointsOn fam l at hga
  have hnot := (mem_sdiff.mp hg).2
  simp only [mem_union,not_or] at hnot
  have la : l ≠ a := fun e => hnot.1.1 (e ▸ hga)
  have lb : l ≠ b := fun e => hnot.1.2 (e ▸ hga)
  have lc : l ≠ c := fun e => hnot.2 (e ▸ hga)
  have ha := cores a (by simp)
  have hb := cores b (by simp)
  have hc := cores c (by simp)
  have deg (x : LineParameter F) (hx : x ∈ ({a,b,c} : Finset _)) := lineParameter_degree_lt fam (hl x hx)
  have hD := natDegree_threeLineDeterminant_le_two_mul_sub_two
    (deg a (by simp)).1 (deg a (by simp)).2 (deg b (by simp)).1 (deg b (by simp)).2
    (deg c (by simp)).1 (deg c (by simp)).2
  have hU := ThreeHeadDeterminantCover.core_sum_le_union_add_degree dom (u 0) (u 1) a b c hdet
  simp only [coreSet_eq_jointCore] at hU
  change (core dom u a).card + (core dom u b).card + (core dom u c).card ≤
    (core dom u a ∪ core dom u b ∪ core dom u c).card + _ at hU
  have hgaps : 2*(Fintype.card I-(core dom u a ∪ core dom u b ∪ core dom u c).card)+(k-1) <
      3*(⌈(1-δ)*(Fintype.card I:ℝ≥0)⌉₊ - 3*(k-1)) := by
    rw [ht,hn]
    dsimp [n,t,d] at *
    omega
  have hcap := card_le_card (outside_secant fam hk a b c hl hgaps hne hg hh)
  have hf := fourth_core fam a b c l (by
    intro x hx
    by_cases he : x = l
    · simpa [he] using hl'
    · apply hl
      simpa [Finset.mem_insert,Finset.mem_singleton,he] using hx) hdet la lb lc
  have hpack := pointsOn_card_mul_max_add_core_le fam hl'
  rw [ht,hn] at hpack
  rw [hn] at hf
  change S.card ≤ (pointsOn fam l).card at hcap
  change 14 < S.card at hbig
  have h15 : 15 ≤ (pointsOn fam l).card := by omega
  have hlow := Nat.mul_le_mul_right (max 1 (t-(core dom u l).card)) h15
  change (pointsOn fam l).card * max 1 (t-(core dom u l).card) + (core dom u l).card ≤ n at hpack
  dsimp [n,t,d] at *
  omega

/-- The seven-value-degree double interpolation at the final dimension. -/
theorem surface (dom : I ↪ F) (v w : I → F) (hn : Fintype.card I = n) :
    ∃ Q : Polynomial (Polynomial F[X]), Q ≠ 0 ∧
      (∀ j i a, ((Q.coeff j).coeff i).coeff a ≠ 0 → j ≤ 7 ∧ i+j ≤ 25 ∧ a+j*d < 2*t) ∧
      ∀ z : F, ∀ q : F[X], q.natDegree ≤ d → ∀ S : Finset I, t ≤ S.card →
        (∀ i ∈ S, q.eval (dom i) = v i + z*w i) → Q.eval₂ (evalRingHom (C z)) q = 0 := by
  open SecondPrimeQuarticInterpolation in
    obtain ⟨c,hc,hall⟩ := exists_curve_double (s:=25) (v:=7) (d:=d) (t:=t)
      dom v w (by decide) (by decide) (by
        rw [hn]
        simp only [Monomials,Fintype.card_sigma,Fintype.card_prod,Fintype.card_fin]
        norm_num [Fin.sum_univ_succ,n,t,d])
    exact ⟨SecondPrimeQuarticInterpolation.surface c,surface_ne_zero hc,
      fun _ _ _ h => surface_support c h,fun z q hq S hS ha => by
        rw [surface_eval]; exact hall z q hq S hS ha⟩

/-- Three saturated noncollinear heads already imply the real family is within
the named budget, including the labels off all three. -/
theorem core_budget (fam : BadScalarRichPointFamily dom k δ u) (hk : 1 ≤ k)
    (hdim : k-1 ≤ d) (hn : Fintype.card I = n)
    (ht : ⌈(1-δ)*(Fintype.card I:ℝ≥0)⌉₊ = t) (a b c : LineParameter F)
    (hl : ∀ x ∈ ({a,b,c} : Finset _), x ∈ lineParameters fam)
    (hdet : threeLineDeterminant a b c ≠ 0)
    (cores : ∀ x ∈ ({a,b,c} : Finset _), t-1 ≤ (core dom u x).card) :
    fam.G.card ≤ 2147483648 := by
  classical
  have h := fourteen_outside fam hk hdim hn ht a b c hl hdet cores
  let U := pointsOn fam a ∪ pointsOn fam b ∪ pointsOn fam c
  have sub : U ⊆ fam.G := union_subset (union_subset
    (pointsOn_subset_G fam a) (pointsOn_subset_G fam b)) (pointsOn_subset_G fam c)
  have h₁ := card_union_le (pointsOn fam a) (pointsOn fam b)
  have h₂ := card_union_le (pointsOn fam a ∪ pointsOn fam b) (pointsOn fam c)
  change U.card ≤ _ at h₂
  have h₃ := card_sdiff_add_card_eq_card sub
  have bound (x : LineParameter F) (hx : x ∈ ({a,b,c} : Finset _)) :
      (pointsOn fam x).card ≤ n-t+1 := by
    have hp := pointsOn_card_mul_max_add_core_le fam (hl x hx)
    rw [ht,hn] at hp
    have hg := cores x hx
    change (pointsOn fam x).card * max 1 (t-(core dom u x).card) + (core dom u x).card ≤ n at hp
    have hm : (pointsOn fam x).card ≤ (pointsOn fam x).card * max 1 (t-(core dom u x).card) :=
      Nat.le_mul_of_pos_right _ (by omega)
    dsimp [t,n] at *
    omega
  have ha := bound a (by simp)
  have hb := bound b (by simp)
  have hc := bound c (by simp)
  change (fam.G \ U).card ≤ 14 at h
  dsimp [t,n] at *
  omega

/-- Worst prices of nonlinear factors and collinear allocations at the endpoint. -/
theorem factor_allocations :
    (∀ b : Fin 8, 2 ≤ b.val →
      let a := (2*b.val-2)*(2*t-1)-b.val*(b.val-1)*d
      let g := (2*b.val-2)*25-b.val*(b.val-1)
      g+2*b.val*25+(2*t*(g+25)*n+n*(4*a*g+4*(2*t-1)*25+25*n))/(t*t-n*d) ≤ 137704) ∧
    (∀ j : Fin 8, 3 ≤ j.val →
      let c := t-(n-t)/499999
      let den := c+(j.val-1)*d
      let union := max (j.val*c-j.val.choose 2*d) ((j.val*c*c+den-1)/den)
      j.val*n-(j.val-1)*union+(7-j.val)*500000+25 ≤ 1535925483) := by decide

#print axioms core_budget
#print axioms factor_allocations
#print axioms outside_secant
#print axioms fourteen_outside
#print axioms surface
end ArkLib.ProximityGap.Frontier.ThreeHeadResidualSecant
