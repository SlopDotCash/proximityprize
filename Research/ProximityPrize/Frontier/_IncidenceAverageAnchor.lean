/-
Copyright (c) 2026 Mikhail Izhutkin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mikhail Izhutkin (mashingaan, @mashingaan)
-/
import Research.ProximityPrize.Frontier._IncidenceAnchorPair
import ArkLib.Data.CodingTheory.ProximityGap.CoveragePigeonhole

/-!
# Production incidence through an averaged anchor

The affine-head and covered-witness proof is adapted from the checked
IncidenceAnchorPair module and UniversalStaircaseCollapse by ArkLib Contributors.
The quantitative overlap is supplied by the existing Coverage lemma.
-/

set_option autoImplicit false
attribute [local instance] Classical.propDecidable
open Finset
open scoped NNReal ENNReal
namespace ProximityGap.IncidenceAverageAnchor
open ProximityGap ProximityGap.SpikeFloor Code

theorem pair_union_le_of_coverage
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (t h m : ℕ) (E : Fin m → Finset ι)
    (htn : t ≤ Fintype.card ι) (hht : h ≤ 2 * t)
    (hsmall : ∀ i, (E i).card ≤ t)
    (hbig : m ^ 2 * (h - 1) * Fintype.card ι + Fintype.card ι * (m * t)
      < (m * t) ^ 2) :
    ∃ a b, a ≠ b ∧ (E a ∪ E b).card ≤ 2 * t - h := by
  classical
  have hpad : ∀ i, ∃ S : Finset ι, E i ⊆ S ∧ S.card = t := by
    intro i
    obtain ⟨S, hES, _, hcard⟩ := Finset.exists_subsuperset_card_eq
      (Finset.subset_univ (E i)) (hsmall i) (by simpa using htn)
    exact ⟨S, hES, hcard⟩
  choose S hES hcard using hpad
  have hsum : (∑ i, (S i).card) = m * t := by simp [hcard]
  have hm : (Fintype.card (Fin m)) ^ 2 * (h - 1) * Fintype.card ι +
      Fintype.card ι * (∑ i, (S i).card) < (∑ i, (S i).card) ^ 2 := by
    simpa only [Fintype.card_fin, hsum] using hbig
  obtain ⟨a, b, hab, hinter⟩ := ArkLib.Coverage.exists_pair_inter_gt S (h - 1) hm
  refine ⟨a, b, hab, ?_⟩
  have hu := Finset.card_union_add_card_inter (S a) (S b)
  rw [hcard a, hcard b] at hu
  have hbound : (S a ∪ S b).card ≤ 2 * t - h := by omega
  exact (Finset.card_le_card (Finset.union_subset_union (hES a) (hES b))).trans hbound

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]
variable {j : ℕ}

theorem badScalars_card_le_of_anchor (C : Submodule F (ι → A))
    {t U : ℕ} (hC3 : NoWeightLE C (U + t)) (hcount : t < j)
    (hpair : ∀ E : Fin (j + 1) → Finset ι, (∀ i, (E i).card ≤ t) →
      ∃ a b, a ≠ b ∧ (E a ∪ E b).card ≤ U)
    {δ : ℝ≥0} (hδ : δ * (Fintype.card ι : ℝ≥0) < t + 1)
    (u₀ u₁ : ι → A) :
    (Finset.univ.filter fun γ : F => mcaEvent (C : Set (ι → A)) δ u₀ u₁ γ).card ≤ j := by
  by_contra hgt
  push Not at hgt
  have hj1 : 1 ≤ j := by omega
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
  have hcompl : ∀ i, (T i)ᶜ.card ≤ t := by
    intro i
    simpa using (witness_compl_card_le (j := t + 1) (by simpa using hδ) (hTsz i))
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
  obtain ⟨i₀, i₁, hi01, hanchor⟩ := hpair (fun i => (T i)ᶜ) hcompl
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
        (fun i => xs i ∈ (T k)ᶜ)).card ≤ (j + 1) * t := by
      calc ∑ k : Fin (j + 1), (Finset.univ.filter
            (fun i => xs i ∈ (T k)ᶜ)).card
          ≤ ∑ _k : Fin (j + 1), t :=
            Finset.sum_le_sum (fun k _ => le_trans (hup k) (hcompl k))
        _ = (j + 1) * t := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    have hcontra : (j + 1) * j ≤ (j + 1) * t :=
      le_trans hsum1 (le_trans (le_of_eq hswap) hsum2)
    have hjj : j ≤ t := Nat.le_of_mul_le_mul_left hcontra (by omega)
    omega
  -- step 5: the covered witness yields a joint explanation — contradiction
  obtain ⟨i, hcov⟩ := hstray
  apply hno i
  refine ⟨U, hUC, D, hDC, fun x hx => ?_⟩
  obtain ⟨k, hki, hxk⟩ := hcov x hx
  have hp := hpin i k (Ne.symm hki) x (Finset.mem_inter.mpr ⟨hx, hxk⟩)
  exact ⟨hp.2.symm, hp.1.symm⟩

open ProximityGap.Ownership
private abbrev sponsorP := ArkLib.ProximityGap.PrizeShapePrimeP30.P
private abbrev sponsorG := ArkLib.ProximityGap.PrizeShapePrimeP30.g
private instance sponsorPrime : Fact sponsorP.Prime :=
  ⟨ArkLib.ProximityGap.PrizeShapePrimeP30.prime_P⟩

theorem firstPrime_average_incidence :
    ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
      (F := ZMod sponsorP) (A := ZMod sponsorP)
      (ArkLib.ProximityGap.KKH26.evalCode sponsorG (2 ^ 30) (2 ^ 29 - 1))
      ((190185817 : ℝ≥0) / (2 ^ 30 : ℝ≥0)) (2 ^ 30) := by
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
  apply badScalars_card_le_of_anchor (j := 2 ^ 30)
    (t := 190185817) (U := 2 * 190185817 - 33686539)
  · exact rsCode_noWeightLE dom (by norm_num)
  · norm_num
  · intro E hsmall
    exact pair_union_le_of_coverage 190185817 33686539 (2 ^ 30 + 1) E
      (by norm_num) (by norm_num) hsmall (by norm_num)
  · norm_num

open ProximityGap.MCAThresholdLedger
open ArkLib.ProximityGap.Frontier.PrizeShapeRateHalfBracket

/-- The averaged-anchor incidence budget yields an unconditional sponsor floor. -/
theorem firstPrime_average_anchor_floor :
    ((190185818 : ℝ≥0) / (2 ^ 30 : ℝ≥0)) ≤
      mcaDeltaStar (F := ZMod sponsorP) (A := ZMod sponsorP)
        (ArkLib.ProximityGap.KKH26.evalCode sponsorG (2 ^ 30) (2 ^ 29 - 1))
        (ProximityGap.epsStar : ℝ≥0∞) := by
  classical
  letI : NeZero (2 ^ 30 : ℕ) := ⟨by norm_num⟩
  have hbudget : ((2 ^ 30 : ℕ) : ℝ≥0∞) / (sponsorP : ℝ≥0∞) ≤
      (ProximityGap.epsStar : ℝ≥0∞) := by
    have hb := natCast_div_le_inv_of_mul_le
      (E := 2 ^ 30) (Q := 2 ^ 128) (p := sponsorP)
      (by norm_num) ArkLib.ProximityGap.PrizeShapePrimeP30.prime_P.pos
      (by norm_num [sponsorP, ArkLib.ProximityGap.PrizeShapePrimeP30.P])
    rwa [epsStar_coe_eq_natCast_inv]
  have hgood : epsMCA (F := ZMod sponsorP) (A := ZMod sponsorP)
      (ArkLib.ProximityGap.KKH26.evalCode sponsorG (2 ^ 30) (2 ^ 29 - 1))
      (predecessorRadius (2 ^ 30) 190185818) ≤
      (ProximityGap.epsStar : ℝ≥0∞) := by
    have hc := ProximityGap.OpenCoreConditionalPin.epsMCA_le_of_worstCaseIncidence
      (ArkLib.ProximityGap.KKH26.evalCode sponsorG (2 ^ 30) (2 ^ 29 - 1))
      ((190185817 : ℝ≥0) / (2 ^ 30 : ℝ≥0))
      firstPrime_average_incidence
    rw [ZMod.card] at hc
    have hpred : predecessorRadius (2 ^ 30) 190185818 =
        ((190185817 : ℝ≥0) / (2 ^ 30 : ℝ≥0)) := by
      norm_num [predecessorRadius]
    rw [hpred]
    exact hc.trans hbudget
  have hfloor := latticeBoundary_le_mcaDeltaStar_of_predecessor_good
    (F := ZMod sponsorP) (n := 2 ^ 30) (a := 190185818)
    (by norm_num) (by norm_num)
    (ArkLib.ProximityGap.KKH26.evalCode sponsorG (2 ^ 30) (2 ^ 29 - 1))
    (ProximityGap.epsStar : ℝ≥0∞) hgood
  convert hfloor using 1
  norm_num


end ProximityGap.IncidenceAverageAnchor
#print axioms ProximityGap.IncidenceAverageAnchor.pair_union_le_of_coverage
#print axioms ProximityGap.IncidenceAverageAnchor.badScalars_card_le_of_anchor
#print axioms ProximityGap.IncidenceAverageAnchor.firstPrime_average_incidence
#print axioms ProximityGap.IncidenceAverageAnchor.firstPrime_average_anchor_floor
