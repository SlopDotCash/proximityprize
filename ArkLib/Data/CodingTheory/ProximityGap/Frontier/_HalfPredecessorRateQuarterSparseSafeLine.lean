/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ConstantWeightPlotkinBound
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R2B_LargeZeroWitnessSplit

/-!
# Sparse safe lines at the rate-one-quarter half predecessor

At `n = 16`, `k = 4`, and agreement threshold `a = 9`, a direction of support one or two
has a large zero set.  On a zero-direction-safe line, the witness split forces every appearing
codeword into only the top zero-agreement strata:

* support one: only `t = 8`, with scalar weight one;
* support two: only `t = 7, 8`, with scalar weights one and two.

Inside a fixed stratum, the zero-agreement traces have constant weight `t` in a universe of
size `15` or `14`.  Distinct RS codewords have trace intersection at most `k - 1 = 3`.
The exact-diagonal constant-weight Plotkin bound therefore gives the stratum caps

```text
(z,t,lambda) = (15,8,3): 3
(z,t,lambda) = (14,7,3): 8
(z,t,lambda) = (14,8,3): 3.
```

Regrouping the punctured line weight proves `#badScalars <= 3` for support one and
`#badScalars <= 8 + 2*3 = 14` for support two.  No field-size or smooth-domain input is used.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterSparseSafeLine

open _root_.ProximityGap _root_.ProximityGap.Ownership _root_.ProximityGap.SpikeFloor
open _root_.ProximityGap.LargeZeroWitnessSplit _root_.ProximityGap.LineListMCAWeld
open ArkLib.ProximityGap.Frontier.ConstantWeightPlotkinBound

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

open Classical in
/-- A zero-agreement trace, regarded as a subset of the direction's zero-coordinate subtype.
Using this subtype keeps the Plotkin ambient size equal to the actual zero-set size. -/
noncomputable def zeroAgreementTrace (c u0 u1 : Fin 16 -> F) :
    Finset {i : Fin 16 // i ∈ directionZeroSet u1} :=
  (Finset.univ : Finset {i : Fin 16 // i ∈ directionZeroSet u1}).filter
    (fun i => c i.1 = u0 i.1)

open Classical in
/-- Passing to the zero-coordinate subtype preserves the zero-agreement cardinality. -/
theorem zeroAgreementTrace_card (c u0 u1 : Fin 16 -> F) :
    (zeroAgreementTrace c u0 u1).card =
      (directionZeroAgreementSet c u0 u1).card := by
  let e : {i : Fin 16 // i ∈ directionZeroSet u1} ↪ Fin 16 :=
    ⟨fun i => i.1, fun _ _ h => Subtype.ext h⟩
  have hmap : (zeroAgreementTrace c u0 u1).map e =
      directionZeroAgreementSet c u0 u1 := by
    ext i
    simp [zeroAgreementTrace, directionZeroAgreementSet, e, and_comm]
  calc
    (zeroAgreementTrace c u0 u1).card =
        ((zeroAgreementTrace c u0 u1).map e).card := by rw [Finset.card_map]
    _ = (directionZeroAgreementSet c u0 u1).card := congrArg Finset.card hmap

open Classical in
/-- Distinct codewords in a zero-agreement stratum have traces meeting in at most three
coordinates, the `k-1` root-counting cap for `RS[16,4]`. -/
theorem zeroAgreementTrace_pair_card_le_three
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 -> F) (t : Nat)
    {c c' : Fin 16 -> F}
    (hc : c ∈ zeroAgreementStratum dom 4 9 u0 u1 t)
    (hc' : c' ∈ zeroAgreementStratum dom 4 9 u0 u1 t)
    (hne : c ≠ c') :
    (zeroAgreementTrace c u0 u1 ∩ zeroAgreementTrace c' u0 u1).card <= 3 := by
  let e : {i : Fin 16 // i ∈ directionZeroSet u1} ↪ Fin 16 :=
    ⟨fun i => i.1, fun _ _ h => Subtype.ext h⟩
  have hsub : (zeroAgreementTrace c u0 u1 ∩ zeroAgreementTrace c' u0 u1).map e ⊆
      agreeSet c c' := by
    intro i hi
    rw [Finset.mem_map] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    rw [Finset.mem_inter] at hj
    have hjc := (Finset.mem_filter.mp hj.1).2
    have hjc' := (Finset.mem_filter.mp hj.2).2
    rw [agreeSet, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hjc.trans hjc'.symm⟩
  have hcCode : c ∈ (rsCode dom 4 : Submodule F (Fin 16 -> F)) := by
    rw [zeroAgreementStratum, Finset.mem_filter] at hc
    rw [lineAppearingCodewords, Finset.mem_filter] at hc
    exact hc.1.2.1
  have hc'Code : c' ∈ (rsCode dom 4 : Submodule F (Fin 16 -> F)) := by
    rw [zeroAgreementStratum, Finset.mem_filter] at hc'
    rw [lineAppearingCodewords, Finset.mem_filter] at hc'
    exact hc'.1.2.1
  calc
    (zeroAgreementTrace c u0 u1 ∩ zeroAgreementTrace c' u0 u1).card =
        ((zeroAgreementTrace c u0 u1 ∩ zeroAgreementTrace c' u0 u1).map e).card := by
          rw [Finset.card_map]
    _ <= (agreeSet c c').card := Finset.card_le_card hsub
    _ <= 4 - 1 := rsCode_pairwise_agreeSet_card_le dom (by omega) hcCode hc'Code hne
    _ = 3 := by omega

open Classical in
/-- Plotkin cap for the only surviving support-one stratum. -/
theorem zeroAgreementStratum_eight_card_le_three_of_support_one
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 -> F)
    (hsupport : (directionSupportSet u1).card = 1) :
    (zeroAgreementStratum dom 4 9 u0 u1 8).card <= 3 := by
  let I := {c : Fin 16 -> F // c ∈ zeroAgreementStratum dom 4 9 u0 u1 8}
  let U := {i : Fin 16 // i ∈ directionZeroSet u1}
  let S : I -> Finset U := fun c => zeroAgreementTrace c.1 u0 u1
  have hU : Fintype.card U = 15 := by
    have hpartition := directionSupportSet_card_eq (n := 16) u1
    have hz : (directionZeroSet u1).card = 15 := by omega
    simpa [U] using hz
  have hsize : forall c : I, (S c).card = 8 := by
    intro c
    rw [zeroAgreementTrace_card]
    exact (Finset.mem_filter.mp c.2).2
  have hpair : forall c c' : I, c ≠ c' -> (S c ∩ S c').card <= 3 := by
    intro c c' hne
    apply zeroAgreementTrace_pair_card_le_three dom u0 u1 8 c.2 c'.2
    exact fun h => hne (Subtype.ext h)
  have hplotkin := constantWeight_plotkin_div S 8 3 hsize hpair (by
    rw [hU]
    norm_num)
  norm_num [hU] at hplotkin
  simpa [I] using hplotkin

open Classical in
/-- Plotkin cap for the lower support-two stratum. -/
theorem zeroAgreementStratum_seven_card_le_eight_of_support_two
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 -> F)
    (hsupport : (directionSupportSet u1).card = 2) :
    (zeroAgreementStratum dom 4 9 u0 u1 7).card <= 8 := by
  let I := {c : Fin 16 -> F // c ∈ zeroAgreementStratum dom 4 9 u0 u1 7}
  let U := {i : Fin 16 // i ∈ directionZeroSet u1}
  let S : I -> Finset U := fun c => zeroAgreementTrace c.1 u0 u1
  have hU : Fintype.card U = 14 := by
    have hpartition := directionSupportSet_card_eq (n := 16) u1
    have hz : (directionZeroSet u1).card = 14 := by omega
    simpa [U] using hz
  have hsize : forall c : I, (S c).card = 7 := by
    intro c
    rw [zeroAgreementTrace_card]
    exact (Finset.mem_filter.mp c.2).2
  have hpair : forall c c' : I, c ≠ c' -> (S c ∩ S c').card <= 3 := by
    intro c c' hne
    apply zeroAgreementTrace_pair_card_le_three dom u0 u1 7 c.2 c'.2
    exact fun h => hne (Subtype.ext h)
  have hplotkin := constantWeight_plotkin_div S 7 3 hsize hpair (by
    rw [hU]
    norm_num)
  norm_num [hU] at hplotkin
  simpa [I] using hplotkin

open Classical in
/-- Plotkin cap for the upper support-two stratum. -/
theorem zeroAgreementStratum_eight_card_le_three_of_support_two
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 -> F)
    (hsupport : (directionSupportSet u1).card = 2) :
    (zeroAgreementStratum dom 4 9 u0 u1 8).card <= 3 := by
  let I := {c : Fin 16 -> F // c ∈ zeroAgreementStratum dom 4 9 u0 u1 8}
  let U := {i : Fin 16 // i ∈ directionZeroSet u1}
  let S : I -> Finset U := fun c => zeroAgreementTrace c.1 u0 u1
  have hU : Fintype.card U = 14 := by
    have hpartition := directionSupportSet_card_eq (n := 16) u1
    have hz : (directionZeroSet u1).card = 14 := by omega
    simpa [U] using hz
  have hsize : forall c : I, (S c).card = 8 := by
    intro c
    rw [zeroAgreementTrace_card]
    exact (Finset.mem_filter.mp c.2).2
  have hpair : forall c c' : I, c ≠ c' -> (S c ∩ S c').card <= 3 := by
    intro c c' hne
    apply zeroAgreementTrace_pair_card_le_three dom u0 u1 8 c.2 c'.2
    exact fun h => hne (Subtype.ext h)
  have hplotkin := constantWeight_plotkin_div S 8 3 hsize hpair (by
    rw [hU]
    norm_num)
  norm_num [hU] at hplotkin
  simpa [I] using hplotkin

open Classical in
/-- A zero-safe `RS[16,4]` line with zero direction support has no bad scalars.  The witness
split empties every zero-agreement stratum below the safety threshold `9`, so the exact
punctured stratum sum vanishes. -/
theorem lineBadScalars_card_eq_zero_of_support_zero
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 -> F)
    (hsafe : ZeroDirectionSafeLine dom 4 9 u0 u1)
    (hsupport : (directionSupportSet u1).card = 0) :
    (lineBadScalars dom 4 9 u0 u1).card = 0 := by
  have hbad := lineBadScalars_card_le_puncturedZeroStratifiedLineWeight
    dom 4 9 u0 u1 hsafe
  rw [puncturedZeroStratifiedLineWeight_eq_sum_zeroAgreementStrata
    dom 4 9 u0 u1 hsafe] at hbad
  have hempty : forall t, t < 9 -> zeroAgreementStratum dom 4 9 u0 u1 t = ∅ := by
    intro t ht
    apply zeroAgreementStratum_eq_empty_of_add_support_lt dom 4 9 u0 u1
    omega
  have hweight :
      (∑ t ∈ Finset.range 9,
        (zeroAgreementStratum dom 4 9 u0 u1 t).card *
          ((directionSupportSet u1).card / (9 - t))) = 0 := by
    norm_num [Finset.sum_range_succ, hempty, hsupport]
  rw [hweight] at hbad
  omega

open Classical in
/-- A zero-safe `RS[16,4]` line of direction support one has at most three bad scalars. -/
theorem lineBadScalars_card_le_three_of_support_one
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 -> F)
    (hsafe : ZeroDirectionSafeLine dom 4 9 u0 u1)
    (hsupport : (directionSupportSet u1).card = 1) :
    (lineBadScalars dom 4 9 u0 u1).card <= 3 := by
  apply (lineBadScalars_card_le_puncturedZeroStratifiedLineWeight
    dom 4 9 u0 u1 hsafe).trans
  rw [puncturedZeroStratifiedLineWeight_eq_sum_zeroAgreementStrata
    dom 4 9 u0 u1 hsafe]
  have hempty : forall t, t < 8 -> zeroAgreementStratum dom 4 9 u0 u1 t = ∅ := by
    intro t ht
    apply zeroAgreementStratum_eq_empty_of_add_support_lt dom 4 9 u0 u1
    omega
  have htop := zeroAgreementStratum_eight_card_le_three_of_support_one
    dom u0 u1 hsupport
  have hweight :
      (∑ t ∈ Finset.range 9,
        (zeroAgreementStratum dom 4 9 u0 u1 t).card *
          ((directionSupportSet u1).card / (9 - t))) =
        (zeroAgreementStratum dom 4 9 u0 u1 8).card := by
    norm_num [Finset.sum_range_succ, hempty, hsupport]
  rw [hweight]
  exact htop

open Classical in
/-- A zero-safe `RS[16,4]` line of direction support two has at most fourteen bad scalars. -/
theorem lineBadScalars_card_le_fourteen_of_support_two
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 -> F)
    (hsafe : ZeroDirectionSafeLine dom 4 9 u0 u1)
    (hsupport : (directionSupportSet u1).card = 2) :
    (lineBadScalars dom 4 9 u0 u1).card <= 14 := by
  apply (lineBadScalars_card_le_puncturedZeroStratifiedLineWeight
    dom 4 9 u0 u1 hsafe).trans
  rw [puncturedZeroStratifiedLineWeight_eq_sum_zeroAgreementStrata
    dom 4 9 u0 u1 hsafe]
  have hempty : forall t, t < 7 -> zeroAgreementStratum dom 4 9 u0 u1 t = ∅ := by
    intro t ht
    apply zeroAgreementStratum_eq_empty_of_add_support_lt dom 4 9 u0 u1
    omega
  have hseven := zeroAgreementStratum_seven_card_le_eight_of_support_two
    dom u0 u1 hsupport
  have height := zeroAgreementStratum_eight_card_le_three_of_support_two
    dom u0 u1 hsupport
  have hweight :
      (∑ t ∈ Finset.range 9,
        (zeroAgreementStratum dom 4 9 u0 u1 t).card *
          ((directionSupportSet u1).card / (9 - t))) =
        (zeroAgreementStratum dom 4 9 u0 u1 7).card +
          (zeroAgreementStratum dom 4 9 u0 u1 8).card * 2 := by
    norm_num [Finset.sum_range_succ, hempty, hsupport]
  rw [hweight]
  omega

/-- Every zero-safe `RS[16,4]` line whose direction has support at most two has at most
fourteen bad scalars.  The exact support-zero, support-one, and support-two endpoints are
`0`, `3`, and `14`, respectively. -/
theorem lineBadScalars_card_le_fourteen_of_support_le_two
    (dom : Fin 16 ↪ F) (u0 u1 : Fin 16 -> F)
    (hsafe : ZeroDirectionSafeLine dom 4 9 u0 u1)
    (hsupport : (directionSupportSet u1).card <= 2) :
    (lineBadScalars dom 4 9 u0 u1).card <= 14 := by
  have hcases : (directionSupportSet u1).card = 0 ∨
      (directionSupportSet u1).card = 1 ∨
      (directionSupportSet u1).card = 2 := by
    omega
  rcases hcases with hzero | hone | htwo
  · rw [lineBadScalars_card_eq_zero_of_support_zero dom u0 u1 hsafe hzero]
    omega
  · exact (lineBadScalars_card_le_three_of_support_one dom u0 u1 hsafe hone).trans (by omega)
  · exact lineBadScalars_card_le_fourteen_of_support_two dom u0 u1 hsafe htwo

#print axioms zeroAgreementTrace_card
#print axioms zeroAgreementTrace_pair_card_le_three
#print axioms zeroAgreementStratum_eight_card_le_three_of_support_one
#print axioms zeroAgreementStratum_seven_card_le_eight_of_support_two
#print axioms zeroAgreementStratum_eight_card_le_three_of_support_two
#print axioms lineBadScalars_card_eq_zero_of_support_zero
#print axioms lineBadScalars_card_le_three_of_support_one
#print axioms lineBadScalars_card_le_fourteen_of_support_two
#print axioms lineBadScalars_card_le_fourteen_of_support_le_two

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterSparseSafeLine
