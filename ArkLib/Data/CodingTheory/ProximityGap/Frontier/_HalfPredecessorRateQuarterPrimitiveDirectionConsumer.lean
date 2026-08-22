/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterPrimitiveDirection
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterHighCoreFreshPetalDichotomy

/-!
# Primitive injection for a two-core three-hole cover

The primitive-direction injection removes the roots of the raw reference
slope difference from the exceptional coordinate set.  This file records the
resulting concrete consequence for two determinant-collapsed reference lines.

Suppose every selected scalar lies on one of the two lines.  If its agreement
set has a coordinate outside its source core and outside the coordinates
missed by both reference cores, that coordinate lies in the other reference
core and is a fresh cross-core petal.  Primitive injection then bounds all
selected scalars by the domain size.  Consequently, in an oversized family,
one scalar has every agreement outside its source core trapped in the common
hole set.

When the two exact half-cores miss exactly three coordinates, the remaining
scalar has between one and three agreements outside its source core.  This removes the previous
reference-slope root-avoidance loss, but it does not rule out the three-hole
trapping alternative and therefore does not close the high-core branch.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open Finset Polynomial
open _root_.ProximityGap Code
open scoped NNReal Polynomial
open ArkLib.ProximityGap.Frontier.HalfPredecessorLineCoreGeometry
open ArkLib.ProximityGap.Frontier.HalfPredecessorSecantLines
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterDeterminantCollapse
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterPrimitiveDirection
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterHighCoreFreshPetalDichotomy
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterCoreBandSynthesis

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterPrimitiveDirectionConsumer

attribute [local instance] Classical.propDecidable

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I]
variable [Field F] [Fintype F] [DecidableEq F]

/-- Agreements of a selected scalar outside the core of a chosen source
line. -/
noncomputable def outsideSourceAgreements
    {dom : I ↪ F} {k : Nat} {delta : NNReal}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom k delta u) (gamma : F)
    (source : LineParameter F) : Finset I :=
  fullAgreement dom (u 0) (u 1) gamma (family.q gamma) \
    jointCore dom (u 0) (u 1) source.1 source.2

/-- If an outside-source agreement is not in the two-core hole set, it gives
a nonempty fresh fibre into the other reference core. -/
theorem exists_reference_fresh_target_of_not_subset_holes
    {dom : I ↪ F} {k : Nat} {delta : NNReal}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom k delta u)
    (line0 line1 source : LineParameter F) (gamma : F)
    (hsource : source = line0 ∨ source = line1)
    (hescape : ¬ outsideSourceAgreements family gamma source ⊆
      uncoveredByTwoLineCores dom (u 0) (u 1) line0 line1) :
    ∃ target : LineParameter F,
      (target = line0 ∨ target = line1) ∧
        (familyFreshCrossCore family gamma source target).Nonempty := by
  classical
  simp only [Finset.not_subset] at hescape
  obtain ⟨i, hiOutside, hiHoles⟩ := hescape
  have hiOutside' := Finset.mem_sdiff.mp hiOutside
  have hiUnion : i ∈
      jointCore dom (u 0) (u 1) line0.1 line0.2 ∪
        jointCore dom (u 0) (u 1) line1.1 line1.2 := by
    by_contra hiNotUnion
    apply hiHoles
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hiNotUnion⟩
  rcases hsource with rfl | rfl
  · have hiTarget : i ∈ jointCore dom (u 0) (u 1) line1.1 line1.2 := by
      rcases Finset.mem_union.mp hiUnion with hiSource | hiTarget
      · exact False.elim (hiOutside'.2 hiSource)
      · exact hiTarget
    refine ⟨line1, Or.inr rfl, ⟨i, ?_⟩⟩
    rw [familyFreshCrossCore]
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_inter.mpr ⟨hiOutside'.1, hiTarget⟩, hiOutside'.2⟩
  · have hiTarget : i ∈ jointCore dom (u 0) (u 1) line0.1 line0.2 := by
      rcases Finset.mem_union.mp hiUnion with hiTarget | hiSource
      · exact hiTarget
      · exact False.elim (hiOutside'.2 hiSource)
    refine ⟨line0, Or.inl rfl, ⟨i, ?_⟩⟩
    rw [familyFreshCrossCore]
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_inter.mpr ⟨hiOutside'.1, hiTarget⟩, hiOutside'.2⟩

/-- A two-reference-line cover with one nonempty fresh fibre per scalar is a
direct consumer of primitive collapsed-cluster injection.  No coordinate is
required to avoid the roots of the raw reference slope difference. -/
theorem card_le_domain_of_primitive_two_line_fresh_cover
    {dom : I ↪ F} {k : Nat} {delta : NNReal}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom k delta u)
    (line0 line1 : LineParameter F) (hne : line0 ≠ line1)
    (source : F → LineParameter F)
    (hsourceRef : ∀ gamma ∈ family.G,
      source gamma = line0 ∨ source gamma = line1)
    (hsourceOn : ∀ gamma ∈ family.G,
      gamma ∈ pointsOn family (source gamma))
    (htargetSupply : ∀ gamma ∈ family.G,
      ∃ target : LineParameter F,
        (target = line0 ∨ target = line1) ∧
          (familyFreshCrossCore family gamma
            (source gamma) target).Nonempty) :
    family.G.card ≤ Fintype.card I := by
  classical
  let target : F → LineParameter F := fun gamma =>
    if hgamma : gamma ∈ family.G then
      Classical.choose (htargetSupply gamma hgamma)
    else
      line0
  have htargetSpec : ∀ gamma ∈ family.G,
      (target gamma = line0 ∨ target gamma = line1) ∧
        (familyFreshCrossCore family gamma
          (source gamma) (target gamma)).Nonempty := by
    intro gamma hgamma
    simpa only [target, dif_pos hgamma] using
      (Classical.choose_spec (htargetSupply gamma hgamma))
  let coord : F → I := fun gamma =>
    if hgamma : gamma ∈ family.G then
      Classical.choose (htargetSpec gamma hgamma).2
    else
      Classical.choice (inferInstance : Nonempty I)
  have hcoord : ∀ gamma ∈ family.G,
      coord gamma ∈ familyFreshCrossCore family gamma
        (source gamma) (target gamma) := by
    intro gamma hgamma
    simp only [coord, dif_pos hgamma]
    exact Classical.choose_spec (htargetSpec gamma hgamma).2
  apply card_le_domain_of_primitive_collapsed_fresh_petals
    dom (u 0) (u 1) family.G line0 line1 source target coord hne
  · intro gamma hgamma
    rcases hsourceRef gamma hgamma with hsource | hsource
    · rw [hsource]
      simp [lineDeterminant]
    · rw [hsource]
      simp [lineDeterminant]
  · intro gamma hgamma
    rcases (htargetSpec gamma hgamma).1 with htarget | htarget
    · rw [htarget]
      simp [lineDeterminant]
    · rw [htarget]
      simp [lineDeterminant]
  · intro gamma hgamma
    have hm := Finset.mem_sdiff.mp (hcoord gamma hgamma)
    have hagree := (Finset.mem_inter.mp hm.1).1
    have hline := (mem_pointsOn_iff family (source gamma) gamma).mp
      (hsourceOn gamma hgamma) |>.2
    simpa only [familyFreshCrossCore, hline] using hagree
  · intro gamma hgamma
    have hm := Finset.mem_sdiff.mp (hcoord gamma hgamma)
    exact (Finset.mem_inter.mp hm.1).2
  · intro gamma hgamma
    exact (Finset.mem_sdiff.mp (hcoord gamma hgamma)).2

/-- **Primitive two-core hole-trapping dichotomy.**  If every selected point
is covered by one of two distinct reference lines, either the family is
domain-bounded or one covered point has no agreement outside its source core
except possibly in the coordinates missed by both reference cores. -/
theorem card_le_domain_or_exists_two_core_hole_trapped_scalar
    {dom : I ↪ F} {k : Nat} {delta : NNReal}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom k delta u)
    (line0 line1 : LineParameter F) (hne : line0 ≠ line1)
    (hcover : ∀ gamma ∈ family.G,
      gamma ∈ pointsOn family line0 ∨ gamma ∈ pointsOn family line1) :
    family.G.card ≤ Fintype.card I ∨
      ∃ gamma ∈ family.G, ∃ source : LineParameter F,
        (source = line0 ∨ source = line1) ∧
          gamma ∈ pointsOn family source ∧
          outsideSourceAgreements family gamma source ⊆
            uncoveredByTwoLineCores dom (u 0) (u 1) line0 line1 := by
  classical
  by_cases htrapped :
      ∃ gamma ∈ family.G, ∃ source : LineParameter F,
        (source = line0 ∨ source = line1) ∧
          gamma ∈ pointsOn family source ∧
          outsideSourceAgreements family gamma source ⊆
            uncoveredByTwoLineCores dom (u 0) (u 1) line0 line1
  · exact Or.inr htrapped
  apply Or.inl
  let source : F → LineParameter F := fun gamma =>
    if hgamma : gamma ∈ family.G then
      if hline : gamma ∈ pointsOn family line0 then line0 else line1
    else
      line0
  have hsourceSpec : ∀ gamma ∈ family.G,
      (source gamma = line0 ∨ source gamma = line1) ∧
        gamma ∈ pointsOn family (source gamma) := by
    intro gamma hgamma
    by_cases hline : gamma ∈ pointsOn family line0
    · have hsource : source gamma = line0 := by
        simp only [source, dif_pos hgamma, dif_pos hline]
      exact ⟨Or.inl hsource, hsource.symm ▸ hline⟩
    · have hline1 := (hcover gamma hgamma).resolve_left hline
      have hsource : source gamma = line1 := by
        simp only [source, dif_pos hgamma, dif_neg hline]
      exact ⟨Or.inr hsource, hsource.symm ▸ hline1⟩
  apply card_le_domain_of_primitive_two_line_fresh_cover
    family line0 line1 hne source
    (fun gamma hgamma => (hsourceSpec gamma hgamma).1)
    (fun gamma hgamma => (hsourceSpec gamma hgamma).2)
  intro gamma hgamma
  apply exists_reference_fresh_target_of_not_subset_holes
    family line0 line1 (source gamma) gamma (hsourceSpec gamma hgamma).1
  intro hsubset
  exact htrapped ⟨gamma, hgamma, source gamma,
    (hsourceSpec gamma hgamma).1,
    (hsourceSpec gamma hgamma).2, hsubset⟩

/-- **Three-hole high-core consumer.**  For two distinct half-domain core
lines whose union misses exactly three coordinates and covers every selected
point, primitive injection leaves only a scalar with between one and three
agreements outside its chosen source core, all supported on those holes.

This theorem eliminates the raw reference-slope root-avoidance hypothesis. It
does not eliminate the displayed hole-trapping alternative. -/
theorem card_le_two_mul_or_exists_three_hole_trapped_scalar
    {dom : I ↪ F} {k h : Nat} {delta : NNReal}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom k delta u)
    (hn : Fintype.card I = 2 * h)
    (hthreshold : h + 1 ≤
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊)
    (line0 line1 : LineParameter F)
    (hne : line0 ≠ line1)
    (hcore0 :
      (jointCore dom (u 0) (u 1) line0.1 line0.2).card = h)
    (hcore1 :
      (jointCore dom (u 0) (u 1) line1.1 line1.2).card = h)
    (hholes :
      (uncoveredByTwoLineCores dom (u 0) (u 1) line0 line1).card = 3)
    (hcover : ∀ gamma ∈ family.G,
      gamma ∈ pointsOn family line0 ∨ gamma ∈ pointsOn family line1) :
    family.G.card ≤ 2 * h ∨
      ∃ gamma ∈ family.G, ∃ source : LineParameter F,
        (source = line0 ∨ source = line1) ∧
          gamma ∈ pointsOn family source ∧
          outsideSourceAgreements family gamma source ⊆
            uncoveredByTwoLineCores dom (u 0) (u 1) line0 line1 ∧
          1 ≤ (outsideSourceAgreements family gamma source).card ∧
          (outsideSourceAgreements family gamma source).card ≤ 3 := by
  rcases card_le_domain_or_exists_two_core_hole_trapped_scalar
      family line0 line1 hne hcover with hcard | htrapped
  · exact Or.inl (by simpa only [hn] using hcard)
  · obtain ⟨gamma, hgamma, source, hsource, hsourceOn, hsubset⟩ := htrapped
    have hsourceCard :
        (jointCore dom (u 0) (u 1) source.1 source.2).card = h := by
      rcases hsource with rfl | rfl
      · exact hcore0
      · exact hcore1
    have hlineEq := (mem_pointsOn_iff family source gamma).mp hsourceOn |>.2
    have hcoreSubset :
        jointCore dom (u 0) (u 1) source.1 source.2 ⊆
          fullAgreement dom (u 0) (u 1) gamma (family.q gamma) := by
      simpa only [hlineEq] using
        (jointCore_subset_fullAgreement dom (u 0) (u 1)
          source.1 source.2 gamma)
    have hlarge : h + 1 ≤
        (fullAgreement dom (u 0) (u 1) gamma
          (family.q gamma)).card :=
      hthreshold.trans (family.threshold_le gamma hgamma)
    have hlower : 1 ≤
        (outsideSourceAgreements family gamma source).card := by
      rw [outsideSourceAgreements,
        Finset.card_sdiff_of_subset hcoreSubset, hsourceCard]
      omega
    apply Or.inr
    refine ⟨gamma, hgamma, source, hsource, hsourceOn, hsubset,
      hlower, ?_⟩
    exact (Finset.card_le_card hsubset).trans_eq hholes

#print axioms exists_reference_fresh_target_of_not_subset_holes
#print axioms card_le_domain_of_primitive_two_line_fresh_cover
#print axioms card_le_domain_or_exists_two_core_hole_trapped_scalar
#print axioms card_le_two_mul_or_exists_three_hole_trapped_scalar

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterPrimitiveDirectionConsumer
