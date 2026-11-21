/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.TerminalCollinearHeadCount

/-! # Counting three polynomial heads just below five-eighths radius

Three noncollinear joint cores lose at least two locations relative to
the three one-fresh-site sizes. Distinct scalar parameters on the same
head must use disjoint fresh agreements. This bounds the entire population.
-/

set_option autoImplicit false
noncomputable section
open Polynomial Finset Code
open scoped NNReal
open _root_.ProximityGap
namespace ArkLib.ProximityGap.Frontier.PlateauThreeHeadPredecessor
open HalfPredecessorBadEventRichPointBridge HalfPredecessorLineCoreGeometry
open HalfPredecessorSecantLines HalfPredecessorRateEighthFullWiring
open HalfPredecessorRateQuarterDeterminantMultiplicity HalfPredecessorRateQuarterPrimitiveDirection
open HalfPredecessorRateQuarterDeterminantCollapse
open ThreeHeadDeterminantCover TerminalCollinearHeadCount

/-- Every additional scalar on the same secant uses its own fresh sites. -/
theorem fresh {m c t n e j : ℕ} (ht : t+e=n) (hj : c+j≤t)
    (h : m*max 1 (t-c)+c ≤ n) : (m-1)*j ≤ e := by
  cases m with
  | zero => simp
  | succ m =>
    have hh := Nat.mul_le_mul_left (m+1) (Nat.le_max_right 1 (t-c))
    rw [Nat.succ_mul] at hh
    have hv := Nat.mul_le_mul_left m (show j ≤ t-c by omega)
    simp only [Nat.add_one_sub_one]
    omega

/-- A determinant deficit on the sum of the three cores bounds their total occupancy. -/
theorem count_deficit {c₁ c₂ c₃ m₁ m₂ m₃ t e x : ℕ} (hx : 0<x) (ht : t=402653184+x)
    (hs : c₁+c₂+c₃ ≤ 1207959550) (h₁ : m₁≤e+1) (h₂ : m₂≤e+1) (h₃ : m₃≤e+1)
    (f₁ : ∀ j, c₁+j≤t → (m₁-1)*j ≤ e) (f₂ : ∀ j, c₂+j≤t → (m₂-1)*j ≤ e)
    (f₃ : ∀ j, c₃+j≤t → (m₃-1)*j ≤ e) :
    m₁+m₂+m₃ ≤ 2*(e+1)+(1+e/(3*x)) := by
  have hpos : 0<3*x := by omega
  have a := f₁ 2
  have b := f₂ 2
  have c := f₃ 2
  have d (hc : c₁+3*x≤t) := (Nat.le_div_iff_mul_le hpos).2 (f₁ _ hc)
  have g (hc : c₂+3*x≤t) := (Nat.le_div_iff_mul_le hpos).2 (f₂ _ hc)
  have h (hc : c₃+3*x≤t) := (Nat.le_div_iff_mul_le hpos).2 (f₃ _ hc)
  generalize e/(3*x) = allowance at d g h ⊢
  omega

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I] [Field F] [Fintype F] [DecidableEq F]
    {dom : I ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin 2) I}

/-- A deficit of x agreements from the plateau forces a noncollinear triple to
spend at least 3x fresh sites per label on one head, or two fresh sites on two heads. -/
theorem cap_at_small_deficit (fam : BadScalarRichPointFamily dom 67108864 δ u) (hn : Fintype.card I=1073741824)
    {e x : ℕ} (he : e+x=671088640) (hx : 0<x) (hl : 610000000≤e)
    (ht : ⌈(1-δ)*(Fintype.card I : ℝ≥0)⌉₊=402653184+x) (H : Finset (LineParameter F))
    (hH : H ⊆ lineParameters fam) (hthree : H.card ≤ 3)
    (hbig : ∀ c ∈ H, 48 < (pointsOn fam c).card)
    {allowance : ℕ} (hdef : 1+e/(3*x)≤allowance)
    (hex : (fam.G \ H.biUnion (pointsOn fam)).card ≤ allowance) :
    fam.G.card ≤ 2*(e+1)+allowance := by
  classical
  have hdef := Nat.le_max_right 525 (1+e/(3*x))
  let D (l : LineParameter F) := jointCore dom (u 0) (u 1) l.1 l.2
  let B := H.biUnion (pointsOn fam)
  let U := H.biUnion D
  have ht' : ⌈(1-δ)*(Fintype.card I : ℝ≥0)⌉₊ = Fintype.card I - e := by rw [ht,hn]; omega
  have hline (l : LineParameter F) (hl : l ∈ H) : (pointsOn fam l).card ≤ e+1 :=
    TwoLargeCoreCount.line_occupancy_le fam (e:=e) (by omega) ht' (hH hl)
  have htotal : fam.G.card ≤ allowance+B.card := by
    have h : fam.G ⊆ (fam.G \ B) ∪ B := by
      intro x hx
      by_cases hB : x ∈ B
      · exact mem_union_right _ hB
      · exact mem_union_left _ (mem_sdiff.mpr ⟨hx,hB⟩)
    exact (card_le_card h).trans ((card_union_le ..).trans (Nat.add_le_add_right hex B.card))
  by_cases hfew : H.card ≤ 2
  · have hm : B.card ≤ H.card*(e+1) := card_biUnion_le.trans
      ((sum_le_sum (fun l hl => hline l hl)).trans_eq (by simp))
    have hh := Nat.mul_le_mul_right (e+1) hfew
    omega
  have H3 : H.card=3 := by omega
  have budget (l : LineParameter F) (hl : l ∈ H) :
      (pointsOn fam l).card*max 1 ((402653184+x)-(D l).card)+(D l).card ≤ 1073741824 := by
    have h := pointsOn_card_mul_max_add_core_le fam (hH hl)
    rwa [ht,hn] at h
  have hcore (l : LineParameter F) (hl : l ∈ H) : (1059741824-e) ≤ (D l).card := by
    have h := budget l hl
    have hm := Nat.mul_le_mul (hbig l hl) (Nat.le_max_right 1 ((402653184+x)-(D l).card))
    omega
  obtain ⟨a,ha,b,hb,hab⟩ := one_lt_card.mp (show 1 < H.card by omega)
  by_cases det : ∀ c ∈ H, lineDeterminant a b c = 0
  · have hc := collinear_card fam H hH a b hab det
    change B.card ≤ U.card + (Fintype.card I-U.card)*H.card at hc
    have hp (i : LineParameter F) (hi : i ∈ H) (j : LineParameter F) (hj : j ∈ H) (hij : i≠j) :
        (D i ∩ D j).card ≤ 67108863 := by
      have h₁ := lineParameter_degree_lt fam (hH hi)
      have h₂ := lineParameter_degree_lt fam (hH hj)
      exact FSMBCoreAbsorptionLadder.jointCore_inter_jointCore_card_le dom (u 0) (u 1)
        (by decide : 1 ≤ 67108864) h₁.1 h₁.2 h₂.1 h₂.2 (by by_contra! h; exact hij (Prod.ext h.1 h.2))
    have hu := union_lower H D hcore hp
    change H.card*(1059741824-e) ≤ U.card + H.card.choose 2*67108863 at hu
    have hnU := card_le_univ U
    rw [hn,H3] at hc
    rw [hn] at hnU
    rw [H3] at hu
    norm_num [Nat.choose] at hu
    omega
  · push Not at det
    obtain ⟨c,hc,hdet⟩ := det
    have det' : threeLineDeterminant a b c ≠ 0 := by simpa only [threeLineDeterminant,lineDeterminant,mul_comm] using hdet
    have ha' := lineParameter_degree_lt fam (hH ha)
    have hb' := lineParameter_degree_lt fam (hH hb)
    have hc' := lineParameter_degree_lt fam (hH hc)
    have hdeg := natDegree_threeLineDeterminant_le_two_mul_sub_two ha'.1 ha'.2 hb'.1 hb'.2 hc'.1 hc'.2
    have hsum := core_sum_le_union_add_degree dom (u 0) (u 1) a b c det'
    simp only [coreSet_eq_jointCore] at hsum
    change (D a).card+(D b).card+(D c).card ≤ (D a ∪ D b ∪ D c).card+_ at hsum
    have hu := card_le_univ (D a ∪ D b ∪ D c)
    rw [hn] at hu
    have cov := cover_of_three_noncollinear fam (by decide) a b c (hH ha) (hH hb) (hH hc) det' (by
      have h₁ := hcore a ha
      have h₂ := hcore b hb
      have h₃ := hcore c hc
      rw [ht,hn]
      change _ < _ + (D a).card + (D b).card + (D c).card
      omega)
    have hd (l : LineParameter F) (hl : l ∈ H) (j : ℕ) (hj : (D l).card+j≤402653184+x) :
        ((pointsOn fam l).card-1)*j ≤ e := fresh (by omega) hj (budget l hl)
    have h := count_deficit (x:=x) hx rfl (by omega : (D a).card+(D b).card+(D c).card≤1207959550)
      (hline a ha) (hline b hb) (hline c hc) (hd a ha) (hd b hb) (hd c hc)
    have h1 := (card_le_card cov).trans (card_union_le ..)
    have h2 := card_union_le (pointsOn fam a) (pointsOn fam b)
    omega

/-- A deficit of x agreements from the plateau forces a noncollinear triple to
spend at least 3x fresh sites per label on one head, or two fresh sites on two heads. -/
theorem cap_at_deficit (fam : BadScalarRichPointFamily dom 67108864 δ u) (hn : Fintype.card I=1073741824)
    {e x : ℕ} (he : e+x=671088640) (hx : 0<x) (hl : 610000000≤e)
    (ht : ⌈(1-δ)*(Fintype.card I : ℝ≥0)⌉₊=402653184+x) (H : Finset (LineParameter F))
    (hH : H ⊆ lineParameters fam) (hthree : H.card ≤ 3)
    (hbig : ∀ c ∈ H, 184 < (pointsOn fam c).card)
    (hex : (fam.G \ H.biUnion (pointsOn fam)).card ≤ max 197 (1+e/(3*x))) :
    fam.G.card ≤ 2*(e+1)+max 197 (1+e/(3*x)) := by
  exact cap_at_small_deficit fam hn he hx hl ht H hH hthree
    (fun c hc => (by decide : 48≤184).trans_lt (hbig c hc)) (Nat.le_max_right ..) hex

/-- The specialized cap at the final predecessor of the five-eighths plateau. -/
theorem cap (fam : BadScalarRichPointFamily dom 67108864 δ u) (hn : Fintype.card I=1073741824)
    (ht : ⌈(1-δ)*(Fintype.card I : ℝ≥0)⌉₊=402653185) (H : Finset (LineParameter F))
    (hH : H ⊆ lineParameters fam) (hthree : H.card ≤ 3)
    (hbig : ∀ c ∈ H, 512 < (pointsOn fam c).card)
    (hex : (fam.G \ H.biUnion (pointsOn fam)).card ≤ 12397) :
    fam.G.card ≤ 1565873494 := by
  apply cap_at_deficit fam hn (e:=671088639) (x:=1) (by decide) (by decide) (by decide) ht H hH hthree (fun c hc => (by decide : 184≤512).trans_lt (hbig c hc))
  exact hex.trans (by decide)

#print axioms cap_at_deficit
#print axioms cap
end ArkLib.ProximityGap.Frontier.PlateauThreeHeadPredecessor
