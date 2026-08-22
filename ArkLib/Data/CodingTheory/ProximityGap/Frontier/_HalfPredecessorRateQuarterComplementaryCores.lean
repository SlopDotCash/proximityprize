/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorLargeCoreCollapse

/-!
# Rate-quarter half predecessor: complementary-core collapse

Two decoded polynomial lines with joint cores covering almost all coordinates
already force the sharp domain-size bound at rate at most one quarter.  A rich
point off both lines meets each core in at most `k-1` coordinates.  Adding the
coordinates missed by both cores still leaves it below the half-predecessor
threshold whenever

```text
|univ \\ (D1 union D2)| + 2 * (k - 1) < h + 1.
```

Thus every selected point lies on one of the two lines, and the line-core
packing theorem bounds each line subfamily by `h`.  In particular, this closes
the complementary two-half-core architecture attaining equality in the known
packing construction.  At the saturated rate `h=2k`, the same argument allows
the two cores to miss as many as two coordinates.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial
open _root_.ProximityGap Code
open scoped NNReal Polynomial
open ArkLib.ProximityGap.Frontier.HalfPredecessorLineCoreGeometry
open ArkLib.ProximityGap.Frontier.HalfPredecessorSecantLines
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge
open ArkLib.ProximityGap.Frontier.HalfPredecessorLargeCoreCollapse

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterComplementaryCores

attribute [local instance] Classical.propDecidable

variable {iota F : Type} [Fintype iota] [Nonempty iota] [DecidableEq iota]
variable [Field F] [Fintype F] [DecidableEq F]

/-- A quantitative version of the two-core cover argument.  A point off both
lines has at most `k-1` agreements in each core, plus every coordinate missed
by their union.  If that total is below the rich threshold, no such point
exists. -/
theorem G_subset_two_lines_of_small_core_complement
    {dom : iota ↪ F} {k h : Nat} {delta : NNReal}
    {u : WordStack F (Fin 2) iota}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k)
    (hthreshold : h + 1 ≤
      ⌈(1 - delta) * (Fintype.card iota : NNReal)⌉₊)
    (line1 line2 : LineParameter F)
    (hline1 : line1 ∈ lineParameters family)
    (hline2 : line2 ∈ lineParameters family)
    (hmissing :
      (Finset.univ \ (
        jointCore dom (u 0) (u 1) line1.1 line1.2 ∪
          jointCore dom (u 0) (u 1) line2.1 line2.2)).card +
          2 * (k - 1) < h + 1) :
    family.G ⊆ pointsOn family line1 ∪ pointsOn family line2 := by
  intro gamma hgamma
  by_contra hnot
  simp only [Finset.mem_union, not_or] at hnot
  have hnot1 : family.q gamma ≠ line1.1 + C gamma * line1.2 := by
    intro heq
    exact hnot.1 ((mem_pointsOn_iff family line1 gamma).mpr ⟨hgamma, heq⟩)
  have hnot2 : family.q gamma ≠ line2.1 + C gamma * line2.2 := by
    intro heq
    exact hnot.2 ((mem_pointsOn_iff family line2 gamma).mpr ⟨hgamma, heq⟩)
  have hdegq := family.degree_lt gamma hgamma
  have hdeg1 := lineParameter_degree_lt family hline1
  have hdeg2 := lineParameter_degree_lt family hline2
  let A := fullAgreement dom (u 0) (u 1) gamma (family.q gamma)
  let D1 := jointCore dom (u 0) (u 1) line1.1 line1.2
  let D2 := jointCore dom (u 0) (u 1) line2.1 line2.2
  let R : Finset iota := Finset.univ \ (D1 ∪ D2)
  have hcap1 : (A ∩ D1).card ≤ k - 1 := by
    simpa only [A, D1] using
      fullAgreement_inter_jointCore_card_le dom (u 0) (u 1) hk
        hdegq hdeg1.1 hdeg1.2 hnot1
  have hcap2 : (A ∩ D2).card ≤ k - 1 := by
    simpa only [A, D2] using
      fullAgreement_inter_jointCore_card_le dom (u 0) (u 1) hk
        hdegq hdeg2.1 hdeg2.2 hnot2
  have hAsub : A ⊆ ((A ∩ D1) ∪ (A ∩ D2)) ∪ R := by
    intro i hi
    by_cases hi1 : i ∈ D1
    · exact Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hi, hi1⟩))
    by_cases hi2 : i ∈ D2
    · exact Finset.mem_union_left _
        (Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hi, hi2⟩))
    · exact Finset.mem_union_right _
        (Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, by simp [hi1, hi2]⟩)
  have hAupper : A.card ≤ 2 * (k - 1) + R.card := by
    calc
      A.card ≤ (((A ∩ D1) ∪ (A ∩ D2)) ∪ R).card :=
        Finset.card_le_card hAsub
      _ ≤ ((A ∩ D1) ∪ (A ∩ D2)).card + R.card :=
        Finset.card_union_le _ _
      _ ≤ ((A ∩ D1).card + (A ∩ D2).card) + R.card := by
        gcongr
        exact Finset.card_union_le _ _
      _ ≤ 2 * (k - 1) + R.card := by omega
  have hAlower : h + 1 ≤ A.card :=
    hthreshold.trans (family.threshold_le gamma hgamma)
  have hmissing' : R.card + 2 * (k - 1) < h + 1 := by
    simpa only [R, D1, D2] using hmissing
  omega

/-- Two almost-complementary cores force the sharp family bound whenever the
uncovered-coordinate budget is below the off-line agreement deficit. -/
theorem card_le_two_mul_of_small_core_complement
    {dom : iota ↪ F} {k h : Nat} {delta : NNReal}
    {u : WordStack F (Fin 2) iota}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k)
    (hn : Fintype.card iota = 2 * h)
    (hthreshold : h + 1 ≤
      ⌈(1 - delta) * (Fintype.card iota : NNReal)⌉₊)
    (line1 line2 : LineParameter F)
    (hline1 : line1 ∈ lineParameters family)
    (hline2 : line2 ∈ lineParameters family)
    (hmissing :
      (Finset.univ \ (
        jointCore dom (u 0) (u 1) line1.1 line1.2 ∪
          jointCore dom (u 0) (u 1) line2.1 line2.2)).card +
          2 * (k - 1) < h + 1) :
    family.G.card ≤ 2 * h := by
  have hsub := G_subset_two_lines_of_small_core_complement
    family hk hthreshold line1 line2 hline1 hline2 hmissing
  have hcardSub := Finset.card_le_card hsub
  have hunion := Finset.card_union_le
    (pointsOn family line1) (pointsOn family line2)
  have hcard1 := pointsOn_card_le_half family hn hthreshold hline1
  have hcard2 := pointsOn_card_le_half family hn hthreshold hline2
  omega

/-- At the saturated quarter rate `h = 2k`, two line cores missing at most two
coordinates already cover every selected rich point by their line subfamilies. -/
theorem G_subset_two_lines_of_saturated_small_complement
    {dom : iota ↪ F} {k h : Nat} {delta : NNReal}
    {u : WordStack F (Fin 2) iota}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k) (hsaturated : h = 2 * k)
    (hthreshold : h + 1 ≤
      ⌈(1 - delta) * (Fintype.card iota : NNReal)⌉₊)
    (line1 line2 : LineParameter F)
    (hline1 : line1 ∈ lineParameters family)
    (hline2 : line2 ∈ lineParameters family)
    (hmissing :
      (Finset.univ \ (
        jointCore dom (u 0) (u 1) line1.1 line1.2 ∪
          jointCore dom (u 0) (u 1) line2.1 line2.2)).card ≤ 2) :
    family.G ⊆ pointsOn family line1 ∪ pointsOn family line2 := by
  apply G_subset_two_lines_of_small_core_complement
    family hk hthreshold line1 line2 hline1 hline2
  omega

/-- **Saturated complementary-core stability.**  At `h = 2k`, two relevant
line cores whose union misses at most two coordinates force `|G| <= 2h`. -/
theorem card_le_two_mul_of_saturated_small_complement
    {dom : iota ↪ F} {k h : Nat} {delta : NNReal}
    {u : WordStack F (Fin 2) iota}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k) (hsaturated : h = 2 * k)
    (hn : Fintype.card iota = 2 * h)
    (hthreshold : h + 1 ≤
      ⌈(1 - delta) * (Fintype.card iota : NNReal)⌉₊)
    (line1 line2 : LineParameter F)
    (hline1 : line1 ∈ lineParameters family)
    (hline2 : line2 ∈ lineParameters family)
    (hmissing :
      (Finset.univ \ (
        jointCore dom (u 0) (u 1) line1.1 line1.2 ∪
          jointCore dom (u 0) (u 1) line2.1 line2.2)).card ≤ 2) :
    family.G.card ≤ 2 * h := by
  apply card_le_two_mul_of_small_core_complement
    family hk hn hthreshold line1 line2 hline1 hline2
  omega

/-- For two half-domain cores, an intersection of at most two coordinates is
equivalent to an uncovered-coordinate budget of at most two.  At the saturated
quarter rate this closes the two-core family. -/
theorem card_le_two_mul_of_saturated_half_cores_inter_le_two
    {dom : iota ↪ F} {k h : Nat} {delta : NNReal}
    {u : WordStack F (Fin 2) iota}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k) (hsaturated : h = 2 * k)
    (hn : Fintype.card iota = 2 * h)
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
        jointCore dom (u 0) (u 1) line2.1 line2.2).card ≤ 2) :
    family.G.card ≤ 2 * h := by
  let D1 := jointCore dom (u 0) (u 1) line1.1 line1.2
  let D2 := jointCore dom (u 0) (u 1) line2.1 line2.2
  have hunionInter := Finset.card_union_add_card_inter D1 D2
  have hcore1' : D1.card = h := by simpa only [D1] using hcore1
  have hcore2' : D2.card = h := by simpa only [D2] using hcore2
  have hinter' : (D1 ∩ D2).card ≤ 2 := by simpa only [D1, D2] using hinter
  have hmissing : (Finset.univ \ (D1 ∪ D2)).card ≤ 2 := by
    have hcomplement :
        (Finset.univ \ (D1 ∪ D2)).card =
          Fintype.card iota - (D1 ∪ D2).card := by
      simp [Finset.card_sdiff]
    rw [hcomplement, hn]
    omega
  apply card_le_two_mul_of_saturated_small_complement
    family hk hsaturated hn hthreshold line1 line2 hline1 hline2
  simpa only [D1, D2] using hmissing

/-- If two relevant decoded-line cores cover the whole domain at rate at most
one quarter, every rich point lies on one of the two lines. -/
theorem G_subset_two_lines_of_core_union_eq_univ
    {dom : iota ↪ F} {k h : Nat} {delta : NNReal}
    {u : WordStack F (Fin 2) iota}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k) (hrate : 2 * k ≤ h)
    (hthreshold : h + 1 ≤
      ⌈(1 - delta) * (Fintype.card iota : NNReal)⌉₊)
    (line1 line2 : LineParameter F)
    (hline1 : line1 ∈ lineParameters family)
    (hline2 : line2 ∈ lineParameters family)
    (hcover :
      jointCore dom (u 0) (u 1) line1.1 line1.2 ∪
        jointCore dom (u 0) (u 1) line2.1 line2.2 = Finset.univ) :
    family.G ⊆ pointsOn family line1 ∪ pointsOn family line2 := by
  intro gamma hgamma
  by_contra hnot
  simp only [Finset.mem_union, not_or] at hnot
  have hnot1 : family.q gamma ≠ line1.1 + C gamma * line1.2 := by
    intro heq
    exact hnot.1 ((mem_pointsOn_iff family line1 gamma).mpr ⟨hgamma, heq⟩)
  have hnot2 : family.q gamma ≠ line2.1 + C gamma * line2.2 := by
    intro heq
    exact hnot.2 ((mem_pointsOn_iff family line2 gamma).mpr ⟨hgamma, heq⟩)
  have hdegq := family.degree_lt gamma hgamma
  have hdeg1 := lineParameter_degree_lt family hline1
  have hdeg2 := lineParameter_degree_lt family hline2
  let A := fullAgreement dom (u 0) (u 1) gamma (family.q gamma)
  let D1 := jointCore dom (u 0) (u 1) line1.1 line1.2
  let D2 := jointCore dom (u 0) (u 1) line2.1 line2.2
  have hcap1 : (A ∩ D1).card ≤ k - 1 := by
    simpa only [A, D1] using
      fullAgreement_inter_jointCore_card_le dom (u 0) (u 1) hk
        hdegq hdeg1.1 hdeg1.2 hnot1
  have hcap2 : (A ∩ D2).card ≤ k - 1 := by
    simpa only [A, D2] using
      fullAgreement_inter_jointCore_card_le dom (u 0) (u 1) hk
        hdegq hdeg2.1 hdeg2.2 hnot2
  have hAsub : A ⊆ (A ∩ D1) ∪ (A ∩ D2) := by
    intro i hi
    have hiCover : i ∈ D1 ∪ D2 := by
      have : i ∈ (Finset.univ : Finset iota) := Finset.mem_univ i
      simpa only [D1, D2, hcover] using this
    rcases Finset.mem_union.mp hiCover with hi1 | hi2
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hi, hi1⟩)
    · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hi, hi2⟩)
  have hAupper : A.card ≤ 2 * (k - 1) := by
    calc
      A.card ≤ ((A ∩ D1) ∪ (A ∩ D2)).card := Finset.card_le_card hAsub
      _ ≤ (A ∩ D1).card + (A ∩ D2).card := Finset.card_union_le _ _
      _ ≤ 2 * (k - 1) := by omega
  have hAlower : h + 1 ≤ A.card := by
    exact hthreshold.trans (family.threshold_le gamma hgamma)
  omega

/-- **Complementary-core rate-quarter branch.** If two relevant decoded-line
cores cover the domain, their two line subfamilies cover `G`; line-core packing
bounds each by `h`, hence `|G| <= 2h`. -/
theorem card_le_two_mul_of_core_union_eq_univ
    {dom : iota ↪ F} {k h : Nat} {delta : NNReal}
    {u : WordStack F (Fin 2) iota}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k) (hrate : 2 * k ≤ h)
    (hn : Fintype.card iota = 2 * h)
    (hthreshold : h + 1 ≤
      ⌈(1 - delta) * (Fintype.card iota : NNReal)⌉₊)
    (line1 line2 : LineParameter F)
    (hline1 : line1 ∈ lineParameters family)
    (hline2 : line2 ∈ lineParameters family)
    (hcover :
      jointCore dom (u 0) (u 1) line1.1 line1.2 ∪
        jointCore dom (u 0) (u 1) line2.1 line2.2 = Finset.univ) :
    family.G.card ≤ 2 * h := by
  have hsub := G_subset_two_lines_of_core_union_eq_univ
    family hk hrate hthreshold line1 line2 hline1 hline2 hcover
  have hcardSub := Finset.card_le_card hsub
  have hunion := Finset.card_union_le
    (pointsOn family line1) (pointsOn family line2)
  have hcard1 := pointsOn_card_le_half family hn hthreshold hline1
  have hcard2 := pointsOn_card_le_half family hn hthreshold hline2
  omega

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterComplementaryCores

#print axioms
  ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterComplementaryCores.card_le_two_mul_of_small_core_complement
#print axioms
  ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterComplementaryCores.card_le_two_mul_of_saturated_small_complement
#print axioms
  ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterComplementaryCores.card_le_two_mul_of_saturated_half_cores_inter_le_two
#print axioms
  ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterComplementaryCores.G_subset_two_lines_of_core_union_eq_univ
#print axioms
  ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterComplementaryCores.card_le_two_mul_of_core_union_eq_univ
