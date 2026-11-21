/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.QuarterSuccessorSiteBudget
import ArkLib.Research.ProximityGap.Frontier._HalfPredecessorRateQuarterPrimitiveDirection
import ArkLib.Research.ProximityGap.Frontier.QuarterRateSaturatedCores

/-! # A quarter-rate successor violation has exactly one uncovered position -/

namespace ArkLib.ProximityGap.Frontier.QuarterSuccessorOneHole

open Polynomial Finset Code HalfPredecessorBadEventRichPointBridge HalfPredecessorSecantLines
open HalfPredecessorLineCoreGeometry HalfPredecessorRateQuarterDeterminantCollapse
open HalfPredecessorRateQuarterDeterminantMultiplicity HalfPredecessorRateQuarterPrimitiveDirection
open HalfPredecessorRateQuarterCollapsedClusterInjection
open QuarterRateSaturatedCores
open scoped NNReal ENNReal

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I] [Field F] [Finite F] [DecidableEq F]
variable {dom : I ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin 2) I}

/-- An assigned scalar on a short core consumes the full number of distinct extra
agreements it needs, while covered sites carry only their common primitive scalar. -/
theorem incidence_budget {k t : ℕ} (fam : BadScalarRichPointFamily dom k δ u)
    (a b : LineParameter F) (hab : a ≠ b) (H : Finset (LineParameter F))
    (valid : ∀ g ∈ H, g ∈ lineParameters fam)
    (col : ∀ g ∈ H, lineDeterminant a b g = 0) (src : F → LineParameter F)
    (srcH : ∀ z ∈ fam.G, src z ∈ H) (srcZ : ∀ z ∈ fam.G, z ∈ pointsOn fam (src z))
    (ht : t ≤ ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊) :
    let D (g : LineParameter F) := jointCore dom (u 0) (u 1) g.1 g.2
    let U := H.biUnion D
    ∑ z ∈ fam.G, max 1 (t - (D (src z)).card) ≤ U.card + H.card * Uᶜ.card := by
  classical
  let _ := Fintype.ofFinite F
  let D (g : LineParameter F) := jointCore dom (u 0) (u 1) g.1 g.2
  let U := H.biUnion D
  let common (i : I) := primitiveScalarAt a b (dom i)
  let key (g : LineParameter F) (i : I) :=
    (u 0 i - g.1.eval (dom i)) / (g.2.eval (dom i) - u 1 i)
  let keys (i : I) := if i ∈ U then {common i} else H.image (fun h => key h i)
  let fresh (z : F) := fullAgreement dom (u 0) (u 1) z (fam.q z) \ D (src z)
  have allowed (z : F) (hz : z ∈ fam.G) (i : I) (h : i ∈ fresh z) : z ∈ keys i := by
    obtain ⟨hit, out⟩ := mem_sdiff.mp h
    let s := src z
    have hS := srcH z hz
    rw [((mem_pointsOn_iff fam s z).mp (srcZ z hz)).2] at hit
    by_cases hi : i ∈ U
    · obtain ⟨t, ht, inT⟩ := mem_biUnion.mp hi
      have h := gamma_eq_primitiveScalarAt_of_pairEquation a b s t hab (col s hS) (col t ht)
        (transverse_of_mem_fullAgreement_mem_targetCore_not_mem_sourceCore
          dom (u 0) (u 1) s t z hit inT out)
        (pairEquation_of_mem_fullAgreement_of_mem_jointCore dom (u 0) (u 1) s t z hit inT)
      simpa only [keys, ite_eq_left hi, mem_singleton, common] using h
    · have h := (mem_filter.mp hit).2
      simp only [eval_add, eval_mul, eval_C] at h
      have hd : s.2.eval (dom i) - u 1 i ≠ 0 := by
        intro he
        have he' := sub_eq_zero.mp he
        apply out
        rw [he'] at h
        exact mem_filter.mpr ⟨mem_univ _, add_right_cancel h, he'⟩
      have eq : key s i = z := ((eq_div_iff hd).mpr (by linear_combination h)).symm
      simpa only [keys, ite_eq_right hi] using
        (mem_image.mpr ⟨s, hS, eq⟩ : z ∈ H.image (fun h => key h i))
  have low (z : F) (hz : z ∈ fam.G) : max 1 (t - (D (src z)).card) ≤ (fresh z).card := by
    let A := fullAgreement dom (u 0) (u 1) z (fam.q z)
    have rich : t ≤ A.card := ht.trans (fam.threshold_le z hz)
    have size := card_sdiff_add_card_inter A (D (src z))
    have hi : (A ∩ D (src z)).card ≤ (D (src z)).card := card_le_card inter_subset_right
    have deg := lineParameter_degree_lt fam (valid _ (srcH z hz))
    have hne := not_subset_jointCore_of_not_pairJointAgreesOn dom (u 0) (u 1) _ _ _
      deg.1 deg.2 (fam.noJoint z hz)
    obtain ⟨i, hA, out⟩ := not_subset.mp hne
    have hpos : 0 < (fresh z).card := card_pos.mpr ⟨i, mem_sdiff.mpr ⟨hA,out⟩⟩
    change max 1 (t - (D (src z)).card) ≤ (A \ D (src z)).card
    change 0 < (A \ D (src z)).card at hpos
    omega
  have swap : ∑ z ∈ fam.G, (fresh z).card =
      ∑ i : I, (fam.G.filter (fun z => i ∈ fresh z)).card := by
    have h (z : F) : (fresh z).card = ∑ i : I, if i ∈ fresh z then 1 else 0 := by simp
    simp_rw [h, card_filter]
    rw [sum_comm]
  have high (i : I) : (fam.G.filter (fun z => i ∈ fresh z)).card ≤
      if i ∈ U then 1 else H.card := by
    have h := card_le_card (show fam.G.filter (fun z => i ∈ fresh z) ⊆ keys i from
      fun z hz => allowed z (mem_filter.mp hz).1 i (mem_filter.mp hz).2)
    by_cases hi : i ∈ U
    · simpa [keys, hi] using h
    · simpa only [ite_eq_right hi] using h.trans
        (show (keys i).card ≤ H.card by
          simpa [keys, hi] using (card_image_le (s := H) (f := fun h => key h i)))
  have total := (sum_le_sum low).trans (swap.le.trans (sum_le_sum (s := univ) fun i _ => high i))
  have endcount : ∑ i : I, (if i ∈ U then 1 else H.card) = U.card + H.card * Uᶜ.card := by
    rw [sum_ite]
    simp [Finset.filter_not, compl_eq_univ_sdiff, mul_comm]
  exact total.trans_eq endcount

/-- At the first open successor a counterexample forces one uncovered coordinate,
no triple overlaps, and three exact pairwise overlaps of size 268435454. Each core
has exactly 626349395 coordinates and the same three heads have nonconstant direction. -/
theorem one_hole {p : ℕ} [CharP F p] (hp : 132 < p)
    (fam : BadScalarRichPointFamily dom 268435456 δ u) (hn : Fintype.card I = 1073741824)
    (ht : ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊ = 626349396)
    (hG : 1073741824 < fam.G.card) :
    ∃ a b c : LineParameter F, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      (∀ h ∈ ({a,b,c} : Finset _), h ∈ lineParameters fam ∧ 178956951 ≤ (pointsOn fam h).card) ∧
      threeLineDeterminant a b c = 0 ∧
      ((primitiveIntercept a b).natDegree ≠ 0 ∨ (primitiveSlope a b).natDegree ≠ 0) ∧
      fam.G = pointsOn fam a ∪ pointsOn fam b ∪ pointsOn fam c ∧
      fam.G.card ≤ 1073741826 ∧
      let D (h : LineParameter F) := jointCore dom (u 0) (u 1) h.1 h.2
      (D a ∪ D b ∪ D c)ᶜ.card = 1 ∧ (D a ∩ D b ∩ D c).card = 0 ∧
      (D a).card = 626349395 ∧ (D b).card = 626349395 ∧ (D c).card = 626349395 ∧
      (D a ∩ D b).card = 268435454 ∧ (D a ∩ D c).card = 268435454 ∧
      (D b ∩ D c).card = 268435454 := by
  classical
  let _ := Fintype.ofFinite F
  obtain ⟨a,b,c,hab,hac,hbc,valid,det,cover,ha,hb,hc,slack⟩ :=
    QuarterSuccessorCoreGeometry.actual_full_cover hp fam hn ht hG
  let H : Finset (LineParameter F) := {a,b,c}
  let D (g : LineParameter F) := jointCore dom (u 0) (u 1) g.1 g.2
  let U := D a ∪ D b ∪ D c
  change Uᶜ.card + (D a ∩ D b ∩ D c).card + (268435455 - (D a ∩ D b).card) +
    (268435455 - (D a ∩ D c).card) + (268435455 - (D b ∩ D c).card) +
    ((D a).card - 626349394) + ((D b).card - 626349394) + ((D c).card - 626349394) = 7 at slack
  change 626349394 ≤ (D a).card at ha
  change 626349394 ≤ (D b).card at hb
  change 626349394 ≤ (D c).card at hc
  have eq : H.card = 3 := by simp [H, hab, hac, hbc]
  have sites : H.biUnion D = U := by simp [U,H,union_assoc]
  have hval (g) (hg : g ∈ H) := (valid g hg).1
  have col (g) (hg : g ∈ H) : lineDeterminant a b g = 0 := by
    simp only [H, mem_insert, mem_singleton] at hg
    rcases hg with rfl | rfl | rfl
    · simp [lineDeterminant]
    · simp [lineDeterminant]
    · simpa only [threeLineDeterminant, lineDeterminant, mul_comm] using det
  have hcov : fam.G ⊆ H.biUnion (pointsOn fam) := by simpa [H, union_assoc] using cover.le
  have src' (z : F) (hz : z ∈ fam.G) := mem_biUnion.mp (hcov hz)
  choose! src srcH srcZ using src'
  have inc := incidence_budget fam a b hab H hval col src srcH srcZ ht.ge
  let cost (z : F) := max 1 (626349396 - (D (src z)).card)
  change ∑ z ∈ fam.G, cost z ≤ (H.biUnion D).card + H.card * (H.biUnion D)ᶜ.card at inc
  rw [sites, eq] at inc
  have full := card_compl_add_card U
  rw [hn] at full
  have room : Uᶜ.card ≤ 7 := by omega
  have tight (h : LineParameter F) (hh : h ∈ H) : 626349395 ≤ (D h).card := by
    by_contra! short
    let others := (H.erase h).biUnion (pointsOn fam)
    let assigned := fam.G \ others
    have one (g) (hg : g ∈ H.erase h) : (pointsOn fam g).card ≤ 447392429 :=
      TwoLargeCoreCount.line_occupancy_le fam (e := 447392428) hn ht
        (hval g (mem_of_mem_erase hg))
    have cnt : others.card ≤ 2 * 447392429 := by
      have h := card_biUnion_le (s := H.erase h) (t := pointsOn fam)
      have rhs := h.trans (sum_le_sum one)
      simpa only [sum_const, smul_eq_mul, card_erase_of_mem hh, eq] using rhs
    have Zcard := card_le_card_sdiff_add_card (s := fam.G) (t := others)
    have rich : 178956967 ≤ assigned.card := by dsimp only [assigned]; omega
    have expense (z : F) (hz : z ∈ fam.G) : 1 + (if z ∈ assigned then 1 else 0) ≤ cost z := by
      by_cases zz : z ∈ assigned
      · have matchHead : src z = h := by
          by_contra ne
          exact (mem_sdiff.mp zz).2 (mem_biUnion.mpr
            ⟨src z, mem_erase.mpr ⟨ne, srcH z hz⟩, srcZ z hz⟩)
        simp only [cost, matchHead, ite_eq_left zz]
        omega
      · simp only [cost, ite_eq_right zz, add_zero, le_max_iff, le_refl, true_or]
    have bound := (sum_le_sum expense).trans inc
    have sub : assigned ⊆ fam.G := sdiff_subset
    simp only [sum_add_distrib, sum_const, smul_eq_mul, mul_one, sum_boole] at bound
    rw [filter_mem_eq_inter, inter_eq_right.mpr sub] at bound
    change fam.G.card + assigned.card ≤ U.card + 3 * Uᶜ.card at bound
    omega
  have lowerA := tight a (by simp [H])
  have lowerB := tight b (by simp [H])
  have lowerC := tight c (by simp [H])
  have overlap {x y : LineParameter F} (hx : x ∈ H) (hy : y ∈ H) (hne : x ≠ y)
      (hDx : 626349395 ≤ (D x).card) (hDy : 626349395 ≤ (D y).card) :
      (D x ∩ D y).card ≤ 268435454 := by
    by_contra! sat
    have bound := points_on_saturated fam (hval x hx) (hval y hy) hne sat
    change (pointsOn fam x).card ≤ (univ \ (D x ∪ D y)).card + 1 at bound
    rw [card_sdiff_of_subset (subset_univ _), card_univ, hn] at bound
    have unionCard := card_union_add_card_inter (D x) (D y)
    have cap := HalfPredecessorRateEighthFullWiring.jointCore_inter_card_le_degree_pred
      fam (by decide) (hval x hx) (hval y hy) hne
    change (D x ∩ D y).card ≤ 268435455 at cap
    have pop := (valid x hx).2
    omega
  have ab := overlap (by simp [H]) (by simp [H]) hab lowerA lowerB
  have ac := overlap (by simp [H]) (by simp [H]) hac lowerA lowerC
  have bc := overlap (by simp [H]) (by simp [H]) hbc lowerB lowerC
  have cap := QuarterSuccessorSiteBudget.cluster_image_budget fam a b hab H hval col hcov
  let vals := U.image (fun i => primitiveScalarAt a b (dom i))
  change fam.G.card ≤ ((H.biUnion D).image _).card + H.card * (H.biUnion D)ᶜ.card at cap
  rw [sites,eq] at cap
  change fam.G.card ≤ vals.card + 3 * Uᶜ.card at cap
  have images : vals.card ≤ U.card := card_image_le
  have dir : (primitiveIntercept a b).natDegree ≠ 0 ∨ (primitiveSlope a b).natDegree ≠ 0 := by
    by_contra! both
    have hsingle : vals.card ≤ 1 := by
      apply card_le_one.mpr
      intro x hx y hy
      obtain ⟨i,_,rfl⟩ := mem_image.mp hx
      obtain ⟨j,_,rfl⟩ := mem_image.mp hy
      have same (f : F[X]) (hf : f.natDegree = 0) : f.eval (dom i) = f.eval (dom j) := by
        have h₁ := congrArg (fun q : F[X] => q.eval (dom i)) (eq_C_of_natDegree_eq_zero hf)
        have h₂ := congrArg (fun q : F[X] => q.eval (dom j)) (eq_C_of_natDegree_eq_zero hf)
        exact h₁.trans ((eval_C.trans eval_C.symm).trans h₂.symm)
      change -(_ / _) = -(_ / _)
      rw [same _ both.1, same _ both.2]
    omega
  refine ⟨a,b,c,hab,hac,hbc,valid,det,dir,cover, ?_, ?_⟩
  · omega
  · change Uᶜ.card = 1 ∧ (D a ∩ D b ∩ D c).card = 0 ∧
      (D a).card = 626349395 ∧ (D b).card = 626349395 ∧ (D c).card = 626349395 ∧
      (D a ∩ D b).card = 268435454 ∧ (D a ∩ D c).card = 268435454 ∧
      (D b ∩ D c).card = 268435454
    omega

omit [DecidableEq I] in
/-- At the successor, the excess over the first designated field budget is at most two. -/
theorem family_cap {p : ℕ} [CharP F p] (hp : 132 < p)
    (fam : BadScalarRichPointFamily dom 268435456 δ u) (hn : Fintype.card I = 1073741824)
    (ht : ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊ = 626349396) :
    fam.G.card ≤ 1073741826 := by
  classical
  by_cases h : 1073741824 < fam.G.card
  · obtain ⟨_,_,_,_,_,_,_,_,_,_,cap,_⟩ := one_hole hp fam hn ht h
    exact cap
  · omega

/-- Bounds on the worst-pair MCA probability at exactly 447392428 errors, for every
finite field of characteristic greater than 132 and every injection of the stated length. -/
theorem mass_bounds {K J : Type} [Field K] [Fintype K] [Fintype J] [Nonempty J]
    {p : ℕ} [CharP K p] (hp : 132 < p) (D : J ↪ K) (hn : Fintype.card J = 1073741824) :
    let mass := _root_.ProximityGap.epsMCA (F := K) (ReedSolomon.code D 268435456 : Set (J → K))
      (447392428 / 1073741824)
    (894784858 : ℝ≥0∞) / Fintype.card K ≤ mass ∧
      mass ≤ (1073741826 : ℝ≥0∞) / Fintype.card K := by
  classical
  constructor
  · have low := _root_.ProximityGap.TwoHeadLinearBudget.errors D (k := 268435456) (e := 447392428)
      (by omega) (by omega) (by omega)
    rw [hn] at low
    exact low
  · apply _root_.ProximityGap.epsMCA_le_of_badCount_le _ _ 1073741826
    intro v
    let fam := canonicalBadScalarRichPointFamily D (447392428 / 1073741824) v
      (by decide : 1 ≤ 268435456)
    apply family_cap hp fam hn
    rw [hn]
    change ⌈(1 - ((447392428 : ℕ) : ℝ≥0) / ((1073741824 : ℕ) : ℝ≥0)) *
      ((1073741824 : ℕ) : ℝ≥0)⌉₊ = 626349396
    rw [tsub_mul, one_mul, div_mul_cancel₀ _ (by norm_num), ← Nat.cast_tsub, Nat.ceil_natCast]

end ArkLib.ProximityGap.Frontier.QuarterSuccessorOneHole
