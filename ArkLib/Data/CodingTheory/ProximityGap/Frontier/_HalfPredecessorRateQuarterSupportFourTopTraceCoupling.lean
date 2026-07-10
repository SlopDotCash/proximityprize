/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterSupportFourSafeLine
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterSupportThreeSafeLine

/-!
# Rate-quarter support-four coupling from a top trace

Fix a support-four line at `n = 16`, `k = 4`, and threshold `9`.  Its zero-coordinate universe
has size twelve.  If a `t = 8` codeword exists, write `A` for its eight-coordinate trace and
`K = A^c` for the four-coordinate complement.

Every `t = 7` trace meets `A` in at most three coordinates by the Reed--Solomon root cap, so it
must contain all four coordinates of `K`.  Two such traces would intersect in at least four
coordinates, again contradicting the root cap.  Thus the top-trace branch has `#t7 <= 1`.

Together with the existing `#t5 <= 4` and `#t8 <= 1` bounds, this sharpens the punctured line
budget from `#t6 + 14` to `#t6 + 10`.  Consequently `#t6 <= 6` is the exact remaining numerical
condition needed to reach sixteen in this branch.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open Finset

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterSupportFourTopTraceCoupling

open _root_.ProximityGap _root_.ProximityGap.Ownership _root_.ProximityGap.SpikeFloor
open _root_.ProximityGap.LargeZeroWitnessSplit _root_.ProximityGap.LineListMCAWeld
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterSparseSafeLine
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterSupportFourSafeLine
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterSupportThreeSafeLine

attribute [local instance] Classical.propDecidable

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- A seven-subset meeting an eight-subset in at most three points contains the entire
four-point complement in a twelve-point universe. -/
theorem complement_subset_seven_of_eight
    {U : Type} [Fintype U] [DecidableEq U]
    (hU : Fintype.card U = 12) (A B : Finset U)
    (hA : A.card = 8) (hB : B.card = 7)
    (hinter : (A ∩ B).card ≤ 3) :
    Finset.univ \ A ⊆ B := by
  have hKcard : (Finset.univ \ A).card = 4 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ A),
      Finset.card_univ, hU, hA]
  have hsplit := Finset.card_sdiff_add_card_inter B A
  have hinter' : (B ∩ A).card ≤ 3 := by
    simpa only [Finset.inter_comm] using hinter
  have hdiffCard : 4 ≤ (B \ A).card := by omega
  have hsub : B \ A ⊆ Finset.univ \ A := by
    intro i hi
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hi).2⟩
  have heq : B \ A = Finset.univ \ A := by
    apply Finset.eq_of_subset_of_card_le hsub
    omega
  intro i hi
  have : i ∈ B \ A := by rw [heq]; exact hi
  exact (Finset.mem_sdiff.mp this).1

/-- Arithmetic core of the four-plus-eight incidence split. -/
theorem twentySeven_mul_sq_le_two_mul_sq_add_sq
    {M r p : Nat} (hr : 3 * M ≤ r) (hpartition : r + p = 6 * M) :
    27 * M ^ 2 ≤ 2 * r ^ 2 + p ^ 2 := by
  obtain ⟨d, hrd⟩ := Nat.exists_eq_add_of_le hr
  have hpd : p + d = 3 * M := by omega
  have hrpd : r = p + 2 * d := by omega
  nlinarith

open Classical in
/-- **Four-complement six-trace packing.**  In a twelve-point universe, a family of
six-subsets with pair intersections at most three has size at most eight if every member
uses at least three points of one fixed four-subset. -/
theorem six_family_card_le_eight_of_three_in_four
    {I U : Type} [Fintype I] [Fintype U] [DecidableEq U]
    (S : I → Finset U) (K : Finset U)
    (hU : Fintype.card U = 12) (hK : K.card = 4)
    (hsize : ∀ i, (S i).card = 6)
    (hpair : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 3)
    (hthree : ∀ i, 3 ≤ (S i ∩ K).card) :
    Fintype.card I ≤ 8 := by
  let C : Finset U := Finset.univ \ K
  let R : I → Finset {x : U // x ∈ K} := fun i ↦
    restrictToFinsetSubtype K (S i ∩ K)
  let P : I → Finset {x : U // x ∈ C} := fun i ↦
    restrictToFinsetSubtype C (S i \ K)
  let M := Fintype.card I
  let r := ∑ i, (R i).card
  let p := ∑ i, (P i).card
  let rMass := ∑ i, ∑ j, (R i ∩ R j).card
  let pMass := ∑ i, ∑ j, (P i ∩ P j).card
  let totalMass := ∑ i, ∑ j, (S i ∩ S j).card
  have hC : C.card = 8 := by
    rw [show C = Finset.univ \ K by rfl,
      Finset.card_sdiff_of_subset (Finset.subset_univ K),
      Finset.card_univ, hU, hK]
  have hRambient : Fintype.card {x : U // x ∈ K} = 4 := by
    simpa only [Fintype.card_coe] using hK
  have hPambient : Fintype.card {x : U // x ∈ C} = 8 := by
    simpa only [Fintype.card_coe] using hC
  have hRcard : ∀ i, (R i).card = (S i ∩ K).card := by
    intro i
    apply restrictToFinsetSubtype_card
    exact Finset.inter_subset_right
  have hPcard : ∀ i, (P i).card = (S i \ K).card := by
    intro i
    apply restrictToFinsetSubtype_card
    intro x hx
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hx).2⟩
  have hrLower : 3 * M ≤ r := by
    calc
      3 * M = ∑ _i : I, 3 := by simp [M, mul_comm]
      _ ≤ ∑ i, (R i).card := by
        apply Finset.sum_le_sum
        intro i _hi
        rw [hRcard]
        exact hthree i
      _ = r := rfl
  have hrp : r + p = 6 * M := by
    calc
      r + p = ∑ i, ((R i).card + (P i).card) := by
        simp only [r, p, Finset.sum_add_distrib]
      _ = ∑ _i : I, 6 := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [hRcard, hPcard]
        have hsplit := Finset.card_sdiff_add_card_inter (S i) K
        have hs := hsize i
        omega
      _ = 6 * M := by simp [M, mul_comm]
  have hRinter : ∀ i j,
      (R i ∩ R j).card = ((S i ∩ S j) ∩ K).card := by
    intro i j
    change (restrictToFinsetSubtype K (S i ∩ K) ∩
      restrictToFinsetSubtype K (S j ∩ K)).card = _
    rw [← restrictToFinsetSubtype_inter,
      restrictToFinsetSubtype_card]
    · congr 1
      ext x
      simp only [Finset.mem_inter]
      tauto
    · intro x hx
      exact (Finset.mem_inter.mp (Finset.mem_inter.mp hx).1).2
  have hPinter : ∀ i j,
      (P i ∩ P j).card = ((S i ∩ S j) \ K).card := by
    intro i j
    change (restrictToFinsetSubtype C (S i \ K) ∩
      restrictToFinsetSubtype C (S j \ K)).card = _
    rw [← restrictToFinsetSubtype_inter,
      restrictToFinsetSubtype_card]
    · congr 1
      ext x
      simp only [Finset.mem_inter, Finset.mem_sdiff]
      tauto
    · intro x hx
      have hx' := Finset.mem_inter.mp hx |>.1
      exact Finset.mem_sdiff.mpr
        ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hx').2⟩
  have hmassPartition : rMass + pMass = totalMass := by
    calc
      rMass + pMass =
          ∑ i, ∑ j, ((R i ∩ R j).card + (P i ∩ P j).card) := by
        simp only [rMass, pMass, Finset.sum_add_distrib]
      _ = ∑ i, ∑ j, (S i ∩ S j).card := by
        apply Finset.sum_congr rfl
        intro i _hi
        apply Finset.sum_congr rfl
        intro j _hj
        rw [hRinter, hPinter]
        have hsplit := Finset.card_sdiff_add_card_inter (S i ∩ S j) K
        omega
      _ = totalMass := rfl
  have hRCauchy := ArkLib.Coverage.sq_sum_card_le_card_mul_sum_inter R
  have hPCauchy := ArkLib.Coverage.sq_sum_card_le_card_mul_sum_inter P
  have hRCauchy' : r ^ 2 ≤ 4 * rMass := by
    simpa only [r, rMass, hRambient] using hRCauchy
  have hPCauchy' : p ^ 2 ≤ 8 * pMass := by
    simpa only [p, pMass, hPambient] using hPCauchy
  have hquadraticUpper : 2 * r ^ 2 + p ^ 2 ≤ 8 * totalMass := by
    rw [← hmassPartition]
    omega
  have htotalUpper : totalMass ≤ M * (6 + (M - 1) * 3) := by
    have hinner : ∀ i : I,
        (∑ j, (S i ∩ S j).card) ≤ 6 + (M - 1) * 3 := by
      intro i
      rw [← Finset.add_sum_erase Finset.univ
        (fun j ↦ (S i ∩ S j).card) (Finset.mem_univ i)]
      apply Nat.add_le_add
      · simpa only [Finset.inter_self] using (hsize i).le
      · calc
          ∑ j ∈ Finset.univ.erase i, (S i ∩ S j).card ≤
              ∑ _j ∈ Finset.univ.erase i, 3 := by
            apply Finset.sum_le_sum
            intro j hj
            have hji : j ≠ i := (Finset.mem_erase.mp hj).1
            exact hpair i j hji.symm
          _ = (M - 1) * 3 := by
            simp [M, Finset.card_erase_of_mem]
    calc
      totalMass = ∑ i, ∑ j, (S i ∩ S j).card := rfl
      _ ≤ ∑ _i : I, (6 + (M - 1) * 3) :=
        Finset.sum_le_sum fun i _hi ↦ hinner i
      _ = M * (6 + (M - 1) * 3) := by simp [M]
  have hlower := twentySeven_mul_sq_le_two_mul_sq_add_sq hrLower hrp
  have hkey : 27 * M ^ 2 ≤ 8 * (M * (6 + (M - 1) * 3)) :=
    hlower.trans (hquadraticUpper.trans (Nat.mul_le_mul_left 8 htotalUpper))
  by_cases hM : M = 0
  · simp [M, hM]
  have hMpos : 0 < M := Nat.pos_of_ne_zero hM
  have hpred : (M - 1) + 1 = M := by omega
  have hformula : 8 * (M * (6 + (M - 1) * 3)) = 24 * M ^ 2 + 24 * M := by
    nlinarith
  change M ≤ 8
  rw [hformula] at hkey
  nlinarith

open Classical in
/-- If the top stratum is nonempty, the seven-agreement stratum has at most one codeword. -/
theorem zeroAgreementStratum_seven_card_le_one_of_eight_nonempty
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 → F)
    (hsupport : (directionSupportSet u1).card = 4)
    (htop : (zeroAgreementStratum dom 4 9 u0 u1 8).Nonempty) :
    (zeroAgreementStratum dom 4 9 u0 u1 7).card ≤ 1 := by
  obtain ⟨top, htopMem⟩ := htop
  by_contra hnot
  have htwo : 1 < (zeroAgreementStratum dom 4 9 u0 u1 7).card := by omega
  obtain ⟨c, hc, d, hd, hcd⟩ := Finset.one_lt_card.mp htwo
  let U := {i : Fin 16 // i ∈ directionZeroSet u1}
  let A : Finset U := zeroAgreementTrace top u0 u1
  let B : Finset U := zeroAgreementTrace c u0 u1
  let C : Finset U := zeroAgreementTrace d u0 u1
  have hU : Fintype.card U = 12 := by
    have hpartition := directionSupportSet_card_eq (n := 16) u1
    have hz : (directionZeroSet u1).card = 12 := by omega
    simpa [U] using hz
  have hA : A.card = 8 := by
    rw [show A = zeroAgreementTrace top u0 u1 by rfl,
      zeroAgreementTrace_card]
    exact (Finset.mem_filter.mp htopMem).2
  have hB : B.card = 7 := by
    rw [show B = zeroAgreementTrace c u0 u1 by rfl,
      zeroAgreementTrace_card]
    exact (Finset.mem_filter.mp hc).2
  have hC : C.card = 7 := by
    rw [show C = zeroAgreementTrace d u0 u1 by rfl,
      zeroAgreementTrace_card]
    exact (Finset.mem_filter.mp hd).2
  have htopApp : top ∈ lineAppearingCodewords dom 4 9 u0 u1 :=
    (Finset.mem_filter.mp htopMem).1
  have hcApp : c ∈ lineAppearingCodewords dom 4 9 u0 u1 :=
    (Finset.mem_filter.mp hc).1
  have hdApp : d ∈ lineAppearingCodewords dom 4 9 u0 u1 :=
    (Finset.mem_filter.mp hd).1
  have htopc : top ≠ c := by
    intro heq
    subst top
    have h8 := (Finset.mem_filter.mp htopMem).2
    have h7 := (Finset.mem_filter.mp hc).2
    omega
  have htopd : top ≠ d := by
    intro heq
    subst top
    have h8 := (Finset.mem_filter.mp htopMem).2
    have h7 := (Finset.mem_filter.mp hd).2
    omega
  have hAB : (A ∩ B).card ≤ 3 := by
    simpa only [A, B] using
      zeroAgreementTrace_pair_card_le_three_of_appearing
        dom u0 u1 htopApp hcApp htopc
  have hAC : (A ∩ C).card ≤ 3 := by
    simpa only [A, C] using
      zeroAgreementTrace_pair_card_le_three_of_appearing
        dom u0 u1 htopApp hdApp htopd
  have hKsubB : Finset.univ \ A ⊆ B :=
    complement_subset_seven_of_eight hU A B hA hB hAB
  have hKsubC : Finset.univ \ A ⊆ C :=
    complement_subset_seven_of_eight hU A C hA hC hAC
  have hKcard : (Finset.univ \ A).card = 4 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ A),
      Finset.card_univ, hU, hA]
  have hfour : 4 ≤ (B ∩ C).card := by
    rw [← hKcard]
    exact Finset.card_le_card (fun i hi ↦
      Finset.mem_inter.mpr ⟨hKsubB hi, hKsubC hi⟩)
  have hBC : (B ∩ C).card ≤ 3 := by
    simpa only [B, C] using
      zeroAgreementTrace_pair_card_le_three dom u0 u1 7 hc hd hcd
  omega

open Classical in
/-- A top trace also bounds the six-agreement stratum by eight.  This is a direct consequence
of the trace-only four-plus-eight moment count; it uses no support-fiber algebra. -/
theorem zeroAgreementStratum_six_card_le_eight_of_eight_nonempty
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 → F)
    (hsupport : (directionSupportSet u1).card = 4)
    (htop : (zeroAgreementStratum dom 4 9 u0 u1 8).Nonempty) :
    (zeroAgreementStratum dom 4 9 u0 u1 6).card ≤ 8 := by
  obtain ⟨top, htopMem⟩ := htop
  let I := {c : Fin 16 → F // c ∈ zeroAgreementStratum dom 4 9 u0 u1 6}
  let U := {i : Fin 16 // i ∈ directionZeroSet u1}
  let A : Finset U := zeroAgreementTrace top u0 u1
  let K : Finset U := Finset.univ \ A
  let S : I → Finset U := fun c ↦ zeroAgreementTrace c.1 u0 u1
  have hU : Fintype.card U = 12 := by
    have hpartition := directionSupportSet_card_eq (n := 16) u1
    have hz : (directionZeroSet u1).card = 12 := by omega
    simpa [U] using hz
  have hA : A.card = 8 := by
    rw [show A = zeroAgreementTrace top u0 u1 by rfl,
      zeroAgreementTrace_card]
    exact (Finset.mem_filter.mp htopMem).2
  have hK : K.card = 4 := by
    rw [show K = Finset.univ \ A by rfl,
      Finset.card_sdiff_of_subset (Finset.subset_univ A),
      Finset.card_univ, hU, hA]
  have hsize : ∀ c : I, (S c).card = 6 := by
    intro c
    rw [show S c = zeroAgreementTrace c.1 u0 u1 by rfl,
      zeroAgreementTrace_card]
    exact (Finset.mem_filter.mp c.2).2
  have hpair : ∀ c d : I, c ≠ d → (S c ∩ S d).card ≤ 3 := by
    intro c d hcd
    exact zeroAgreementTrace_pair_card_le_three dom u0 u1 6 c.2 d.2
      (fun h ↦ hcd (Subtype.ext h))
  have htopApp : top ∈ lineAppearingCodewords dom 4 9 u0 u1 :=
    (Finset.mem_filter.mp htopMem).1
  have hthree : ∀ c : I, 3 ≤ (S c ∩ K).card := by
    intro c
    have hcApp : c.1 ∈ lineAppearingCodewords dom 4 9 u0 u1 :=
      (Finset.mem_filter.mp c.2).1
    have htopc : top ≠ c.1 := by
      intro heq
      subst top
      have h8 := (Finset.mem_filter.mp htopMem).2
      have h6 := (Finset.mem_filter.mp c.2).2
      omega
    have hinter : (A ∩ S c).card ≤ 3 := by
      simpa only [A, S] using
        zeroAgreementTrace_pair_card_le_three_of_appearing
          dom u0 u1 htopApp hcApp htopc
    have hinter' : (S c ∩ A).card ≤ 3 := by
      simpa only [Finset.inter_comm] using hinter
    have hsplit := Finset.card_sdiff_add_card_inter (S c) A
    have hdiff : 3 ≤ (S c \ A).card := by
      have hs := hsize c
      omega
    have heq : S c ∩ K = S c \ A := by
      ext i
      simp only [K, Finset.mem_inter, Finset.mem_sdiff, Finset.mem_univ,
        true_and]
    rw [heq]
    exact hdiff
  have hpacking := six_family_card_le_eight_of_three_in_four
    S K hU hK hsize hpair hthree
  simpa only [I, Fintype.card_coe] using hpacking

open Classical in
/-- In the top-trace branch, the only uncontrolled punctured-weight term is `#t6`, with
additive overhead ten from the other three strata. -/
theorem lineBadScalars_card_le_six_stratum_add_ten_of_support_four_of_eight_nonempty
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 → F)
    (hsafe : ZeroDirectionSafeLine dom 4 9 u0 u1)
    (hsupport : (directionSupportSet u1).card = 4)
    (htop : (zeroAgreementStratum dom 4 9 u0 u1 8).Nonempty) :
    (lineBadScalars dom 4 9 u0 u1).card ≤
      (zeroAgreementStratum dom 4 9 u0 u1 6).card + 10 := by
  apply (lineBadScalars_card_le_puncturedZeroStratifiedLineWeight
    dom 4 9 u0 u1 hsafe).trans
  rw [puncturedZeroStratifiedLineWeight_eq_sum_zeroAgreementStrata
    dom 4 9 u0 u1 hsafe]
  have hempty : ∀ t, t < 5 →
      zeroAgreementStratum dom 4 9 u0 u1 t = ∅ := by
    intro t ht
    apply zeroAgreementStratum_eq_empty_of_add_support_lt dom 4 9 u0 u1
    omega
  have hfive := zeroAgreementStratum_five_card_le_four_of_support_four
    dom u0 u1 hsupport
  have hsixSeven := zeroAgreementStratum_seven_card_le_one_of_eight_nonempty
    dom u0 u1 hsupport htop
  have height := zeroAgreementStratum_eight_card_le_one_of_support_four
    dom u0 u1 hsupport
  have hweight :
      (∑ t ∈ Finset.range 9,
        (zeroAgreementStratum dom 4 9 u0 u1 t).card *
          ((directionSupportSet u1).card / (9 - t))) =
        (zeroAgreementStratum dom 4 9 u0 u1 5).card +
          (zeroAgreementStratum dom 4 9 u0 u1 6).card +
          (zeroAgreementStratum dom 4 9 u0 u1 7).card * 2 +
          (zeroAgreementStratum dom 4 9 u0 u1 8).card * 4 := by
    norm_num [Finset.sum_range_succ, hempty, hsupport]
  rw [hweight]
  omega

/-- Fully numerical trace-only ceiling in the top-stratum branch. -/
theorem lineBadScalars_card_le_eighteen_of_support_four_of_eight_nonempty
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 → F)
    (hsafe : ZeroDirectionSafeLine dom 4 9 u0 u1)
    (hsupport : (directionSupportSet u1).card = 4)
    (htop : (zeroAgreementStratum dom 4 9 u0 u1 8).Nonempty) :
    (lineBadScalars dom 4 9 u0 u1).card ≤ 18 := by
  have hsix := zeroAgreementStratum_six_card_le_eight_of_eight_nonempty
    dom u0 u1 hsupport htop
  exact (lineBadScalars_card_le_six_stratum_add_ten_of_support_four_of_eight_nonempty
    dom u0 u1 hsafe hsupport htop).trans (by omega)

/-- Exact residual consumer for reaching sixteen in the top-trace branch. -/
theorem lineBadScalars_card_le_sixteen_of_support_four_of_eight_nonempty_of_six_card_le_six
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 → F)
    (hsafe : ZeroDirectionSafeLine dom 4 9 u0 u1)
    (hsupport : (directionSupportSet u1).card = 4)
    (htop : (zeroAgreementStratum dom 4 9 u0 u1 8).Nonempty)
    (hsix : (zeroAgreementStratum dom 4 9 u0 u1 6).card ≤ 6) :
    (lineBadScalars dom 4 9 u0 u1).card ≤ 16 := by
  exact (lineBadScalars_card_le_six_stratum_add_ten_of_support_four_of_eight_nonempty
    dom u0 u1 hsafe hsupport htop).trans (by omega)

#print axioms zeroAgreementStratum_seven_card_le_one_of_eight_nonempty
#print axioms six_family_card_le_eight_of_three_in_four
#print axioms zeroAgreementStratum_six_card_le_eight_of_eight_nonempty
#print axioms lineBadScalars_card_le_six_stratum_add_ten_of_support_four_of_eight_nonempty
#print axioms lineBadScalars_card_le_eighteen_of_support_four_of_eight_nonempty
#print axioms
  lineBadScalars_card_le_sixteen_of_support_four_of_eight_nonempty_of_six_card_le_six

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterSupportFourTopTraceCoupling
