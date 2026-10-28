/-
Copyright (c) 2026 Mikhail Izhutkin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mikhail Izhutkin (mashingaan, @mashingaan)
-/
import ArkLib.Data.CodingTheory.ProximityGap.UniversalStaircaseCollapse
import ArkLib.Data.CodingTheory.ProximityGap.GranularityLadderRS
import ArkLib.Data.CodingTheory.ProximityGap.OpenCoreConditionalPin
import Research.ProximityPrize.Frontier._PrizeShapeRateHalfBracket

/-!
# Anchor-pair incidence collapse

The affine-head and covered-witness proof is adapted from
UniversalStaircaseCollapse.badScalars_card_le by ArkLib Contributors.
The anchor-pair argument weakens its distance premise by one coordinate.
-/

set_option autoImplicit false

open Finset
open scoped NNReal ENNReal

attribute [local instance] Classical.propDecidable

namespace ProximityGap.IncidenceAnchorPair

open ProximityGap ProximityGap.SpikeFloor Code

theorem exists_small_pair_union
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (t m : ℕ) (E : Fin m → Finset ι)
    (hm : 2 ≤ m) (hsmall : ∀ i, (E i).card ≤ t)
    (hspread : Fintype.card ι < m * t) :
    ∃ a b, a ≠ b ∧ (E a ∪ E b).card ≤ 2 * t - 1 := by
  classical
  by_contra hnone
  have hlarge : ∀ a b, a ≠ b → 2 * t ≤ (E a ∪ E b).card := by
    intro a b hab
    have hnot : ¬ (E a ∪ E b).card ≤ 2 * t - 1 := by
      intro h
      exact hnone ⟨a, b, hab, h⟩
    omega
  have ht : 0 < t := by
    by_contra h
    have hz : t = 0 := by omega
    simp [hz] at hspread
  have hcard : ∀ a, (E a).card = t := by
    intro a
    let z : Fin m := ⟨0, by omega⟩
    let o : Fin m := ⟨1, by omega⟩
    have hzo : z ≠ o := by
      intro h
      have hv := congrArg Fin.val h
      norm_num [z, o] at hv
    obtain ⟨b, hab⟩ : ∃ b : Fin m, a ≠ b := by
      by_cases ha : a = z
      · exact ⟨o, ha ▸ hzo⟩
      · exact ⟨z, ha⟩
    have hl := hlarge a b hab
    have hu := Finset.card_union_le (E a) (E b)
    have ha := hsmall a
    have hb := hsmall b
    omega
  have hdis : ∀ a b, a ≠ b → Disjoint (E a) (E b) := by
    intro a b hab
    have hsum := Finset.card_union_add_card_inter (E a) (E b)
    have hl := hlarge a b hab
    rw [hcard a, hcard b] at hsum
    have hz : (E a ∩ E b).card = 0 := by omega
    exact Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp hz)
  have hbi : (Finset.univ.biUnion E).card = m * t := by
    rw [Finset.card_biUnion]
    · simp [hcard]
    · intro a ha b hb hab
      exact hdis a b hab
  have hbound : (Finset.univ.biUnion E).card ≤ Fintype.card ι := Finset.card_le_univ _
  omega

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]
variable {j : ℕ}

theorem badScalars_card_le_anchor (C : Submodule F (ι → A))
    (hC3 : NoWeightLE C (3 * (j - 1) - 1))
    (hspread : Fintype.card ι < (j + 1) * (j - 1)) {δ : ℝ≥0}
    (hδ : δ * (Fintype.card ι : ℝ≥0) < j) (u₀ u₁ : ι → A) :
    (Finset.univ.filter
      (fun γ : F => mcaEvent (C : Set (ι → A)) δ u₀ u₁ γ)).card ≤ j := by
  by_contra hgt
  push Not at hgt
  have hj1 : 1 ≤ j := by
    by_contra hj
    have hj0 : j = 0 := by omega
    rw [hj0] at hδ
    exact absurd hδ (by simp)
  -- extract j+1 distinct bad scalars, enumerated
  obtain ⟨s, hs_sub, hs_card⟩ := Finset.exists_subset_card_eq
    (s := Finset.univ.filter (fun γ : F => mcaEvent (C : Set (ι → A)) δ u₀ u₁ γ))
    (n := j + 1) (by omega)
  set γfun : Fin (j + 1) → F :=
    fun i => (s.equivFin.symm (Fin.cast hs_card.symm i) : F) with hγfun
  have hγinj : Function.Injective γfun := fun a b hab => by
    have h1 := Subtype.val_injective hab
    have h2 := s.equivFin.symm.injective h1
    exact Fin.cast_injective _ h2
  have hbad : ∀ i, mcaEvent (C : Set (ι → A)) δ u₀ u₁ (γfun i) := fun i =>
    (Finset.mem_filter.mp (hs_sub (s.equivFin.symm (Fin.cast hs_card.symm i)).2)).2
  choose T hTsz hwEx hno using hbad
  choose w hwC hwAg using hwEx
  have hcompl : ∀ i, (T i)ᶜ.card ≤ j - 1 := fun i =>
    witness_compl_card_le hδ (hTsz i)
  -- step 1: difference codewords
  set dd : Fin (j + 1) → Fin (j + 1) → (ι → A) :=
    fun i k => (γfun i - γfun k)⁻¹ • (w i - w k) with hdd
  have hddC : ∀ i k, dd i k ∈ C := fun i k =>
    C.smul_mem _ (C.sub_mem (hwC i) (hwC k))
  have hγne : ∀ {i k : Fin (j + 1)}, i ≠ k → γfun i - γfun k ≠ 0 :=
    fun {i k} hik => sub_ne_zero.mpr (fun h => hik (hγinj h))
  have hdd_agree : ∀ i k, i ≠ k → ∀ x ∈ T i ∩ T k, dd i k x = u₁ x := by
    intro i k hik x hx
    obtain ⟨hxi, hxk⟩ := Finset.mem_inter.mp hx
    have hdiff : w i x - w k x = (γfun i - γfun k) • u₁ x := by
      rw [hwAg i x hxi, hwAg k x hxk, sub_smul]
      abel
    calc dd i k x = (γfun i - γfun k)⁻¹ • (w i x - w k x) := rfl
      _ = (γfun i - γfun k)⁻¹ • ((γfun i - γfun k) • u₁ x) := by rw [hdiff]
      _ = u₁ x := by rw [smul_smul, inv_mul_cancel₀ (hγne hik), one_smul]
  have hdd_symm : ∀ i k, dd i k = dd k i := by
    intro i k
    funext x
    show (γfun i - γfun k)⁻¹ • (w i x - w k x)
      = (γfun k - γfun i)⁻¹ • (w k x - w i x)
    rw [show γfun k - γfun i = -(γfun i - γfun k) by ring,
      show w k x - w i x = -(w i x - w k x) by abel, inv_neg, neg_smul_neg]
  obtain ⟨i₀, i₁, hi01, hanchor⟩ :=
    exists_small_pair_union (j - 1) (j + 1) (fun i => (T i)ᶜ)
      (by omega) hcompl hspread
  have hforce_anchor : ∀ i, i ≠ i₀ → i ≠ i₁ → dd i₀ i₁ = dd i₀ i := by
    intro i hi0 hi1
    refine codeword_eq_of_eq_off C hC3 (hddC i₀ i₁) (hddC i₀ i)
      (B := ((T i₀)ᶜ ∪ (T i₁)ᶜ) ∪ (T i)ᶜ) ?_ ?_
    · have hu := Finset.card_union_le ((T i₀)ᶜ ∪ (T i₁)ᶜ) ((T i)ᶜ)
      have hci := hcompl i
      omega
    · intro x hx
      simp only [Finset.mem_union, Finset.mem_compl, not_or, not_not] at hx
      obtain ⟨⟨hx0, hx1⟩, hxi⟩ := hx
      rw [hdd_agree i₀ i₁ hi01 x (Finset.mem_inter.mpr ⟨hx0, hx1⟩),
        hdd_agree i₀ i (Ne.symm hi0) x (Finset.mem_inter.mpr ⟨hx0, hxi⟩)]
  set D : ι → A := dd i₀ i₁ with hD
  set U : ι → A := w i₀ - γfun i₀ • D with hU
  have hDC : D ∈ C := hddC i₀ i₁
  have hUC : U ∈ C := C.sub_mem (hwC i₀) (C.smul_mem _ hDC)
  have hwD : ∀ i, w i = U + γfun i • D := by
    intro i
    by_cases hi : i = i₀
    · subst i
      funext x
      show w i₀ x = (w i₀ x - γfun i₀ • D x) + γfun i₀ • D x
      abel
    · have hddD : dd i i₀ = D := by
        by_cases hi1 : i = i₁
        · subst i
          change dd i₁ i₀ = dd i₀ i₁
          exact hdd_symm i₁ i₀
        · calc dd i i₀ = dd i₀ i := hdd_symm i i₀
               _ = dd i₀ i₁ := (hforce_anchor i hi hi1).symm
               _ = D := rfl
      funext x
      have hmul : w i x - w i₀ x = (γfun i - γfun i₀) • D x := by
        rw [← hddD]
        show w i x - w i₀ x
          = (γfun i - γfun i₀) • ((γfun i - γfun i₀)⁻¹ • (w i x - w i₀ x))
        rw [smul_smul, mul_inv_cancel₀ (hγne hi), one_smul]
      show w i x = (w i₀ x - γfun i₀ • D x) + γfun i • D x
      have hwix : w i x = w i₀ x + (γfun i - γfun i₀) • D x := by
        rw [← hmul]; abel
      rw [hwix, sub_smul]
      abel
  -- step 3: pointwise pinning on pairwise intersections
  have hpin : ∀ i k, i ≠ k → ∀ x ∈ T i ∩ T k, u₁ x = D x ∧ u₀ x = U x := by
    intro i k hik x hx
    obtain ⟨hxi, hxk⟩ := Finset.mem_inter.mp hx
    have ei : u₀ x + γfun i • u₁ x = U x + γfun i • D x := by
      rw [← hwAg i x hxi, hwD i]
      simp [Pi.add_apply, Pi.smul_apply]
    have ek : u₀ x + γfun k • u₁ x = U x + γfun k • D x := by
      rw [← hwAg k x hxk, hwD k]
      simp [Pi.add_apply, Pi.smul_apply]
    have hsub : (γfun i - γfun k) • (u₁ x - D x) = 0 := by
      have hkey : (γfun i - γfun k) • (u₁ x - D x)
          = (u₀ x + γfun i • u₁ x - (U x + γfun i • D x))
            - (u₀ x + γfun k • u₁ x - (U x + γfun k • D x)) := by
        module
      rw [hkey, ei, ek]
      abel
    have hu1 : u₁ x = D x := by
      rcases smul_eq_zero.mp hsub with h | h
      · exact absurd h (hγne hik)
      · exact sub_eq_zero.mp h
    refine ⟨hu1, ?_⟩
    have := ei
    rw [hu1] at this
    have h3 : u₀ x + γfun i • D x = U x + γfun i • D x := this
    exact add_right_cancel h3
  -- step 4: some witness has no strays
  have hstray : ∃ i, ∀ x ∈ T i, ∃ k, k ≠ i ∧ x ∈ T k := by
    by_contra hall
    push Not at hall
    choose xs hxsT hxsNot using hall
    have hinj : Function.Injective xs := by
      intro a b hab
      by_contra hne
      have h1 : xs a ∈ T a := hxsT a
      have h2 : xs b ∉ T a := hxsNot b a hne
      rw [hab] at h1
      exact h2 h1
    have hlow : ∀ i, j ≤ (Finset.univ.filter
        (fun k : Fin (j + 1) => xs i ∈ (T k)ᶜ)).card := by
      intro i
      have hsub2 : Finset.univ.filter (fun k : Fin (j + 1) => k ≠ i)
          ⊆ Finset.univ.filter (fun k => xs i ∈ (T k)ᶜ) := by
        intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
        rw [Finset.mem_compl]
        exact hxsNot i k hk
      calc j = (Finset.univ.filter (fun k : Fin (j + 1) => k ≠ i)).card := by
            rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ i),
              Finset.card_univ, Fintype.card_fin]
            omega
        _ ≤ _ := Finset.card_le_card hsub2
    have hup : ∀ k : Fin (j + 1), (Finset.univ.filter
        (fun i => xs i ∈ (T k)ᶜ)).card ≤ (T k)ᶜ.card := by
      intro k
      have himg : (Finset.univ.filter (fun i => xs i ∈ (T k)ᶜ)).card
          = ((Finset.univ.filter (fun i => xs i ∈ (T k)ᶜ)).image xs).card :=
        (Finset.card_image_of_injective _ hinj).symm
      rw [himg]
      apply Finset.card_le_card
      intro y hy
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
      exact (Finset.mem_filter.mp hi).2
    have hswap : ∑ i : Fin (j + 1), (Finset.univ.filter
          (fun k => xs i ∈ (T k)ᶜ)).card
        = ∑ k : Fin (j + 1), (Finset.univ.filter
          (fun i => xs i ∈ (T k)ᶜ)).card := by
      simp_rw [Finset.card_filter]
      exact Finset.sum_comm
    have hsum1 : (j + 1) * j ≤ ∑ i : Fin (j + 1), (Finset.univ.filter
        (fun k => xs i ∈ (T k)ᶜ)).card := by
      calc (j + 1) * j = ∑ _i : Fin (j + 1), j := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
        _ ≤ _ := Finset.sum_le_sum (fun i _ => hlow i)
    have hsum2 : ∑ k : Fin (j + 1), (Finset.univ.filter
        (fun i => xs i ∈ (T k)ᶜ)).card ≤ (j + 1) * (j - 1) := by
      calc ∑ k : Fin (j + 1), (Finset.univ.filter
            (fun i => xs i ∈ (T k)ᶜ)).card
          ≤ ∑ _k : Fin (j + 1), (j - 1) :=
            Finset.sum_le_sum (fun k _ => le_trans (hup k) (hcompl k))
        _ = (j + 1) * (j - 1) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    have hcontra : (j + 1) * j ≤ (j + 1) * (j - 1) :=
      le_trans hsum1 (le_trans (le_of_eq hswap) hsum2)
    have hjj : j ≤ j - 1 := Nat.le_of_mul_le_mul_left hcontra (by omega)
    omega
  -- step 5: the covered witness yields a joint explanation — contradiction
  obtain ⟨i, hcov⟩ := hstray
  apply hno i
  refine ⟨U, hUC, D, hDC, fun x hx => ?_⟩
  obtain ⟨k, hki, hxk⟩ := hcov x hx
  have hp := hpin i k (Ne.symm hki) x (Finset.mem_inter.mpr ⟨hx, hxk⟩)
  exact ⟨hp.2.symm, hp.1.symm⟩

open Classical in

theorem rs_badScalars_card_le_anchor
    {n : ℕ} [NeZero n] (dom : Fin n ↪ F) {k t : ℕ}
    (hroot : 3 * t - 1 + k ≤ n)
    (hspread : n < (t + 2) * t)
    {δ : ℝ≥0} (hδ : δ * (n : ℝ≥0) < t + 1)
    (u₀ u₁ : Fin n → F) :
    (Finset.univ.filter fun γ : F =>
      mcaEvent ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F))
        δ u₀ u₁ γ).card ≤ t + 1 := by
  classical
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero (NeZero.ne n))
  apply badScalars_card_le_anchor
    (C := rsCode dom k) (j := t + 1)
  · simpa using (rsCode_noWeightLE dom hroot)
  · simpa using hspread
  · simpa using hδ

open ProximityGap.Ownership

private abbrev sponsorP := ArkLib.ProximityGap.PrizeShapePrimeP30.P
private abbrev sponsorG := ArkLib.ProximityGap.PrizeShapePrimeP30.g

private instance sponsorPrime : Fact sponsorP.Prime :=
  ⟨ArkLib.ProximityGap.PrizeShapePrimeP30.prime_P⟩

theorem firstPrime_incidence_at_ladder_boundary :
    ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
      (F := ZMod sponsorP) (A := ZMod sponsorP)
      (ArkLib.ProximityGap.KKH26.evalCode sponsorG (2 ^ 30) (2 ^ 29 - 1))
      ((178956971 : ℝ≥0) / (2 ^ 30 : ℝ≥0)) 178956972 := by
  classical
  letI : NeZero (2 ^ 30 : ℕ) := ⟨by norm_num⟩
  let dom : Fin (2 ^ 30) ↪ ZMod sponsorP :=
    smoothDom sponsorG (2 ^ 30) ArkLib.ProximityGap.PrizeShapePrimeP30.orderOf_g
  have hcode : ArkLib.ProximityGap.KKH26.evalCode sponsorG (2 ^ 30) (2 ^ 29 - 1) =
      ((rsCode dom (2 ^ 29) : Submodule (ZMod sponsorP) (Fin (2 ^ 30) → ZMod sponsorP)) :
        Set (Fin (2 ^ 30) → ZMod sponsorP)) := by
    simpa only [dom, Nat.sub_add_cancel (by norm_num : 1 ≤ 2 ^ 29)] using
      (evalCode_eq_rsCode ArkLib.ProximityGap.PrizeShapePrimeP30.orderOf_g (2 ^ 29 - 1))
  intro u
  rw [hcode]
  exact rs_badScalars_card_le_anchor dom (k := 2 ^ 29) (t := 178956971)
    (by norm_num) (by norm_num) (by norm_num) (u 0) (u 1)

open ProximityGap.MCAThresholdLedger
open ArkLib.ProximityGap.Frontier.PrizeShapeRateHalfBracket

/-- The anchor count at the old ladder boundary fills the next Hamming interval. -/
theorem firstPrime_anchor_ladder_floor :
    ((178956972 : ℝ≥0) / (2 ^ 30 : ℝ≥0)) ≤
      mcaDeltaStar (F := ZMod sponsorP) (A := ZMod sponsorP)
        (ArkLib.ProximityGap.KKH26.evalCode sponsorG (2 ^ 30) (2 ^ 29 - 1))
        (ProximityGap.epsStar : ℝ≥0∞) := by
  classical
  letI : NeZero (2 ^ 30 : ℕ) := ⟨by norm_num⟩
  have hbudget : (178956972 : ℝ≥0∞) / (sponsorP : ℝ≥0∞) ≤
      (ProximityGap.epsStar : ℝ≥0∞) := by
    have hb := natCast_div_le_inv_of_mul_le
      (E := 178956972) (Q := 2 ^ 128) (p := sponsorP)
      (by norm_num) ArkLib.ProximityGap.PrizeShapePrimeP30.prime_P.pos
      (by norm_num [sponsorP, ArkLib.ProximityGap.PrizeShapePrimeP30.P])
    rwa [epsStar_coe_eq_natCast_inv]
  have hgood : epsMCA (F := ZMod sponsorP) (A := ZMod sponsorP)
      (ArkLib.ProximityGap.KKH26.evalCode sponsorG (2 ^ 30) (2 ^ 29 - 1))
      (predecessorRadius (2 ^ 30) 178956972) ≤
      (ProximityGap.epsStar : ℝ≥0∞) := by
    have hc := ProximityGap.OpenCoreConditionalPin.epsMCA_le_of_worstCaseIncidence
      (ArkLib.ProximityGap.KKH26.evalCode sponsorG (2 ^ 30) (2 ^ 29 - 1))
      ((178956971 : ℝ≥0) / (2 ^ 30 : ℝ≥0))
      firstPrime_incidence_at_ladder_boundary
    rw [ZMod.card] at hc
    have hpred : predecessorRadius (2 ^ 30) 178956972 =
        ((178956971 : ℝ≥0) / (2 ^ 30 : ℝ≥0)) := by
      norm_num [predecessorRadius]
    rw [hpred]
    exact hc.trans hbudget
  have hfloor := latticeBoundary_le_mcaDeltaStar_of_predecessor_good
    (F := ZMod sponsorP) (n := 2 ^ 30) (a := 178956972)
    (by norm_num) (by norm_num)
    (ArkLib.ProximityGap.KKH26.evalCode sponsorG (2 ^ 30) (2 ^ 29 - 1))
    (ProximityGap.epsStar : ℝ≥0∞) hgood
  convert hfloor using 1
  norm_num

end ProximityGap.IncidenceAnchorPair

#print axioms ProximityGap.IncidenceAnchorPair.exists_small_pair_union
#print axioms ProximityGap.IncidenceAnchorPair.badScalars_card_le_anchor
#print axioms ProximityGap.IncidenceAnchorPair.firstPrime_incidence_at_ladder_boundary
#print axioms ProximityGap.IncidenceAnchorPair.firstPrime_anchor_ladder_floor
