/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterComplementaryCores

/-!
# Rate-quarter half predecessor: overlap-three rigidity

At the saturated rate `h = 2k`, two half-domain line cores with a
three-coordinate intersection leave exactly three coordinates uncovered.  A
rich point off both lines has at most `k-1` agreements in each core.  These two
root caps and the three uncovered coordinates sum to the required `h+1`
agreements exactly, so every inequality is forced to be an equality.

Consequently the point saturates both off-line root caps, avoids the common
three-coordinate core, contains the whole complement of the two cores, and
has no other agreement coordinates.  The first theorem below isolates the
finite-set equality case; the second supplies its hypotheses from the
Reed--Solomon line-core geometry.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

open Finset Polynomial
open _root_.ProximityGap Code
open scoped NNReal Polynomial
open ArkLib.ProximityGap.Frontier.HalfPredecessorLineCoreGeometry
open ArkLib.ProximityGap.Frontier.HalfPredecessorSecantLines
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterOverlapThreeRigidity

attribute [local instance] Classical.propDecidable

/-- The exact set-theoretic shape forced by the saturated overlap-three
arithmetic. -/
structure OverlapThreeRigidity {I : Type} [Fintype I] [DecidableEq I]
    (A D1 D2 : Finset I) (k h : Nat) : Prop where
  agreement_card : A.card = h + 1
  first_root_cap : (A ∩ D1).card = k - 1
  second_root_cap : (A ∩ D2).card = k - 1
  uncovered_card : (Finset.univ \ (D1 ∪ D2)).card = 3
  no_common_core_agreement : A ∩ (D1 ∩ D2) = ∅
  uncovered_subset : Finset.univ \ (D1 ∪ D2) ⊆ A
  agreement_partition :
    A = ((A ∩ D1) ∪ (A ∩ D2)) ∪ (Finset.univ \ (D1 ∪ D2))

variable {I : Type} [Fintype I] [DecidableEq I]

/-- **Saturated two-half-core equality case.**  If a set has at least `h+1`
points, meets each of two `h`-sets in at most `k-1` points, and the two
`h`-sets overlap in exactly three points inside a `2h`-point universe, then at
`h=2k` all bounds saturate and the set has the rigid partition recorded by
`OverlapThreeRigidity`. -/
theorem saturated_half_core_overlap_three_rigidity
    {A D1 D2 : Finset I} {k h : Nat}
    (hn : Fintype.card I = 2 * h) (hsaturated : h = 2 * k)
    (hcore1 : D1.card = h) (hcore2 : D2.card = h)
    (hinter : (D1 ∩ D2).card = 3)
    (hlower : h + 1 ≤ A.card)
    (hcap1 : (A ∩ D1).card ≤ k - 1)
    (hcap2 : (A ∩ D2).card ≤ k - 1) :
    OverlapThreeRigidity A D1 D2 k h := by
  let B1 := A ∩ D1
  let B2 := A ∩ D2
  let R := Finset.univ \ (D1 ∪ D2)
  let U := B1 ∪ B2
  have hinterLe : (D1 ∩ D2).card ≤ D1.card :=
    Finset.card_le_card Finset.inter_subset_left
  have hk : 1 ≤ k := by omega
  have hunionInter := Finset.card_union_add_card_inter D1 D2
  have hunionCard : (D1 ∪ D2).card + 3 = 2 * h := by omega
  have hRcard : R.card = 3 := by
    have hcomplement : R.card = Fintype.card I - (D1 ∪ D2).card := by
      simp [R, Finset.card_sdiff]
    omega
  have hB1cap : B1.card ≤ k - 1 := by simpa only [B1] using hcap1
  have hB2cap : B2.card ≤ k - 1 := by simpa only [B2] using hcap2
  have hcover : A ⊆ U ∪ R := by
    intro i hi
    by_cases hi1 : i ∈ D1
    · exact Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hi, hi1⟩))
    by_cases hi2 : i ∈ D2
    · exact Finset.mem_union_left _
        (Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hi, hi2⟩))
    · exact Finset.mem_union_right _
        (Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, by simp [hi1, hi2]⟩)
  have hAtoUnion : A.card ≤ U.card + R.card :=
    (Finset.card_le_card hcover).trans (Finset.card_union_le U R)
  have hUcap : U.card ≤ B1.card + B2.card := Finset.card_union_le B1 B2
  have hAcard : A.card = h + 1 := by omega
  have hB1card : B1.card = k - 1 := by omega
  have hB2card : B2.card = k - 1 := by omega
  have hUcard : U.card = B1.card + B2.card := by omega
  have hBinterCard : (B1 ∩ B2).card = 0 := by
    have hcard : U.card + (B1 ∩ B2).card = B1.card + B2.card := by
      simpa only [U] using Finset.card_union_add_card_inter B1 B2
    omega
  have hBinter : B1 ∩ B2 = ∅ := Finset.card_eq_zero.mp hBinterCard
  have hcommon : A ∩ (D1 ∩ D2) = ∅ := by
    have heq : B1 ∩ B2 = A ∩ (D1 ∩ D2) := by
      ext i
      simp only [B1, B2, Finset.mem_inter]
      tauto
    rw [← heq]
    exact hBinter
  have hpartition : A = U ∪ R := by
    apply Finset.eq_of_subset_of_card_le hcover
    have hVcap : (U ∪ R).card ≤ U.card + R.card := Finset.card_union_le U R
    omega
  have hRsub : R ⊆ A := by
    rw [hpartition]
    exact Finset.subset_union_right
  refine
    { agreement_card := hAcard
      first_root_cap := ?_
      second_root_cap := ?_
      uncovered_card := ?_
      no_common_core_agreement := hcommon
      uncovered_subset := ?_
      agreement_partition := ?_ }
  · simpa only [B1] using hB1card
  · simpa only [B2] using hB2card
  · simpa only [R] using hRcard
  · simpa only [R] using hRsub
  · simpa only [U, B1, B2, R] using hpartition

variable {iota F : Type} [Fintype iota] [Nonempty iota] [DecidableEq iota]
variable [Field F] [Fintype F] [DecidableEq F]

/-- **Rate-quarter overlap-three rigidity.**  Let two relevant polynomial
lines have half-domain cores intersecting in three coordinates.  At the
saturated rate, every selected rich point off both lines has exactly `h+1`
agreements, saturates both degree-`<k` root caps, avoids the common core, and
contains every coordinate outside the two cores. -/
theorem fullAgreement_overlap_three_rigidity
    {dom : iota ↪ F} {k h : Nat} {delta : NNReal}
    {u : WordStack F (Fin 2) iota}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k) (hn : Fintype.card iota = 2 * h)
    (hsaturated : h = 2 * k)
    (hthreshold : h + 1 ≤
      ⌈(1 - delta) * (Fintype.card iota : NNReal)⌉₊)
    (line1 line2 : LineParameter F)
    (hline1 : line1 ∈ lineParameters family)
    (hline2 : line2 ∈ lineParameters family)
    (hcore1 :
      (jointCore dom (u 0) (u 1) line1.1 line1.2).card = h)
    (hcore2 :
      (jointCore dom (u 0) (u 1) line2.1 line2.2).card = h)
    (hinter :
      (jointCore dom (u 0) (u 1) line1.1 line1.2 ∩
        jointCore dom (u 0) (u 1) line2.1 line2.2).card = 3)
    {gamma : F} (hgamma : gamma ∈ family.G)
    (hoff1 : family.q gamma ≠ line1.1 + C gamma * line1.2)
    (hoff2 : family.q gamma ≠ line2.1 + C gamma * line2.2) :
    OverlapThreeRigidity
      (fullAgreement dom (u 0) (u 1) gamma (family.q gamma))
      (jointCore dom (u 0) (u 1) line1.1 line1.2)
      (jointCore dom (u 0) (u 1) line2.1 line2.2) k h := by
  have hdegq := family.degree_lt gamma hgamma
  have hdeg1 := lineParameter_degree_lt family hline1
  have hdeg2 := lineParameter_degree_lt family hline2
  apply saturated_half_core_overlap_three_rigidity
    hn hsaturated hcore1 hcore2 hinter
  · exact hthreshold.trans (family.threshold_le gamma hgamma)
  · exact fullAgreement_inter_jointCore_card_le
      dom (u 0) (u 1) hk hdegq hdeg1.1 hdeg1.2 hoff1
  · exact fullAgreement_inter_jointCore_card_le
      dom (u 0) (u 1) hk hdegq hdeg2.1 hdeg2.2 hoff2

/-- In particular, the two off-line polynomial root bounds are attained
simultaneously in the overlap-three equality case. -/
theorem off_line_root_caps_saturated_of_overlap_three
    {dom : iota ↪ F} {k h : Nat} {delta : NNReal}
    {u : WordStack F (Fin 2) iota}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k) (hn : Fintype.card iota = 2 * h)
    (hsaturated : h = 2 * k)
    (hthreshold : h + 1 ≤
      ⌈(1 - delta) * (Fintype.card iota : NNReal)⌉₊)
    (line1 line2 : LineParameter F)
    (hline1 : line1 ∈ lineParameters family)
    (hline2 : line2 ∈ lineParameters family)
    (hcore1 :
      (jointCore dom (u 0) (u 1) line1.1 line1.2).card = h)
    (hcore2 :
      (jointCore dom (u 0) (u 1) line2.1 line2.2).card = h)
    (hinter :
      (jointCore dom (u 0) (u 1) line1.1 line1.2 ∩
        jointCore dom (u 0) (u 1) line2.1 line2.2).card = 3)
    {gamma : F} (hgamma : gamma ∈ family.G)
    (hoff1 : family.q gamma ≠ line1.1 + C gamma * line1.2)
    (hoff2 : family.q gamma ≠ line2.1 + C gamma * line2.2) :
    (fullAgreement dom (u 0) (u 1) gamma (family.q gamma) ∩
      jointCore dom (u 0) (u 1) line1.1 line1.2).card = k - 1 ∧
    (fullAgreement dom (u 0) (u 1) gamma (family.q gamma) ∩
      jointCore dom (u 0) (u 1) line2.1 line2.2).card = k - 1 := by
  have hrigid := fullAgreement_overlap_three_rigidity
    family hk hn hsaturated hthreshold line1 line2 hline1 hline2
      hcore1 hcore2 hinter hgamma hoff1 hoff2
  exact ⟨hrigid.first_root_cap, hrigid.second_root_cap⟩

#print axioms saturated_half_core_overlap_three_rigidity
#print axioms fullAgreement_overlap_three_rigidity
#print axioms off_line_root_caps_saturated_of_overlap_three

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterOverlapThreeRigidity
