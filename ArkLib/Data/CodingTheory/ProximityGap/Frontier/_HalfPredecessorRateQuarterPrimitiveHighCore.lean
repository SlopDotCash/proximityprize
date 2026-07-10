/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterPrimitiveDirection
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterHighCoreFreshPetalDichotomy

/-!
# Primitive-direction closure of the nonempty-fresh high-core branch

The raw-reference high-core argument needed `k` fresh cross-core coordinates
per scalar in order to avoid up to `k-1` roots of a reference slope
difference.  The primitive-direction theorem removes the common gcd of the
two reference components.  Consequently one transverse fresh coordinate is
enough, and equal raw slope polynomials require no separate treatment as long
as the two reference polynomial pairs are distinct.

The final theorem reduces the high-core population to two genuinely
incidence-theoretic residuals: a scalar not covered by any half-core line, or
a covered scalar whose chosen half-core source has no fresh agreement in any
other half-core target.
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

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterPrimitiveHighCore

attribute [local instance] Classical.propDecidable

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I]
variable [Field F] [Fintype F] [DecidableEq F]

/-- One nonempty fresh cross-core fibre per scalar closes a determinant-
collapsed cluster after primitive normalization. -/
theorem card_le_domain_of_primitive_collapsed_nonempty_freshCrossCores
    (dom : I ↪ F) (u0 u1 : I → F) (G : Finset F)
    (line0 line1 : PolynomialLine F)
    (source target : F → PolynomialLine F)
    (hne : line0 ≠ line1)
    (hsource : ∀ gamma ∈ G,
      lineDeterminant line0 line1 (source gamma) = 0)
    (htarget : ∀ gamma ∈ G,
      lineDeterminant line0 line1 (target gamma) = 0)
    (hsupply : ∀ gamma ∈ G,
      (freshCrossCore dom u0 u1 gamma
        (source gamma) (target gamma)).Nonempty) :
    G.card ≤ Fintype.card I := by
  let coord : F → I := fun gamma =>
    if hgamma : gamma ∈ G then
      Classical.choose (hsupply gamma hgamma)
    else
      Classical.choice (inferInstance : Nonempty I)
  have hcoord : ∀ gamma ∈ G,
      coord gamma ∈ freshCrossCore dom u0 u1 gamma
        (source gamma) (target gamma) := by
    intro gamma hgamma
    simp only [coord, dif_pos hgamma]
    exact Classical.choose_spec (hsupply gamma hgamma)
  apply card_le_domain_of_primitive_collapsed_fresh_petals
    dom u0 u1 G line0 line1 source target coord hne hsource htarget
  · intro gamma hgamma
    have hm := hcoord gamma hgamma
    rw [freshCrossCore] at hm
    exact (Finset.mem_inter.mp (Finset.mem_sdiff.mp hm).1).1
  · intro gamma hgamma
    have hm := hcoord gamma hgamma
    rw [freshCrossCore] at hm
    exact (Finset.mem_inter.mp (Finset.mem_sdiff.mp hm).1).2
  · intro gamma hgamma
    have hm := hcoord gamma hgamma
    rw [freshCrossCore] at hm
    exact (Finset.mem_sdiff.mp hm).2

/-- Family-level form: two distinct relevant half-core references collapse
every chosen half-core source and target into one primitive cluster.  A single
fresh target coordinate for each selected scalar bounds the family by `n`. -/
theorem card_le_two_mul_of_distinct_half_core_nonempty_fresh_target_supply
    {dom : I ↪ F} {k h : Nat} {delta : NNReal}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k) (hn : Fintype.card I = 2 * h) (hrate : 2 * k ≤ h)
    (line0 line1 : LineParameter F)
    (hline0 : line0 ∈ lineParameters family)
    (hline1 : line1 ∈ lineParameters family)
    (hne : line0 ≠ line1)
    (hcore0 : h ≤
      (jointCore dom (u 0) (u 1) line0.1 line0.2).card)
    (hcore1 : h ≤
      (jointCore dom (u 0) (u 1) line1.1 line1.2).card)
    (source : F → LineParameter F)
    (hsourceLine : ∀ gamma ∈ family.G,
      source gamma ∈ lineParameters family)
    (hsourceCore : ∀ gamma ∈ family.G, h ≤
      (jointCore dom (u 0) (u 1)
        (source gamma).1 (source gamma).2).card)
    (hsourceOn : ∀ gamma ∈ family.G,
      gamma ∈ pointsOn family (source gamma))
    (htargetSupply : ∀ gamma ∈ family.G,
      ∃ target ∈ lineParameters family,
        h ≤ (jointCore dom (u 0) (u 1) target.1 target.2).card ∧
        (familyFreshCrossCore family gamma
          (source gamma) target).Nonempty) :
    family.G.card ≤ 2 * h := by
  let target : F → LineParameter F := fun gamma =>
    if hgamma : gamma ∈ family.G then
      Classical.choose (htargetSupply gamma hgamma)
    else
      line0
  have htargetSpec : ∀ gamma ∈ family.G,
      target gamma ∈ lineParameters family ∧
        h ≤ (jointCore dom (u 0) (u 1)
          (target gamma).1 (target gamma).2).card ∧
        (familyFreshCrossCore family gamma
          (source gamma) (target gamma)).Nonempty := by
    intro gamma hgamma
    simp only [target, dif_pos hgamma]
    exact Classical.choose_spec (htargetSupply gamma hgamma)
  have hbound :=
    card_le_domain_of_primitive_collapsed_nonempty_freshCrossCores
      dom (u 0) (u 1) family.G line0 line1 source target hne
      (fun gamma hgamma =>
        lineDeterminant_eq_zero_of_three_relevant_half_core_lines
          family hk hn hrate line0 line1 (source gamma)
            hline0 hline1 (hsourceLine gamma hgamma)
            hcore0 hcore1 (hsourceCore gamma hgamma))
      (fun gamma hgamma =>
        lineDeterminant_eq_zero_of_three_relevant_half_core_lines
          family hk hn hrate line0 line1 (target gamma)
            hline0 hline1 (htargetSpec gamma hgamma).1
            hcore0 hcore1 (htargetSpec gamma hgamma).2.1)
      (fun gamma hgamma => by
        rw [← familyFreshCrossCore_eq_freshCrossCore_of_mem_pointsOn
          family (source gamma) (target gamma) (hsourceOn gamma hgamma)]
        exact (htargetSpec gamma hgamma).2.2)
  simpa only [hn] using hbound

/-- With fixed distinct half-core references and a chosen half-core source for
each scalar, the only obstruction left by primitive injection is a scalar
whose fresh fibre into every half-core target is literally empty. -/
theorem card_le_two_mul_or_exists_half_core_target_isolated_scalar
    {dom : I ↪ F} {k h : Nat} {delta : NNReal}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k) (hn : Fintype.card I = 2 * h) (hrate : 2 * k ≤ h)
    (line0 line1 : LineParameter F)
    (hline0 : line0 ∈ lineParameters family)
    (hline1 : line1 ∈ lineParameters family)
    (hne : line0 ≠ line1)
    (hcore0 : h ≤
      (jointCore dom (u 0) (u 1) line0.1 line0.2).card)
    (hcore1 : h ≤
      (jointCore dom (u 0) (u 1) line1.1 line1.2).card)
    (source : F → LineParameter F)
    (hsourceLine : ∀ gamma ∈ family.G,
      source gamma ∈ lineParameters family)
    (hsourceCore : ∀ gamma ∈ family.G, h ≤
      (jointCore dom (u 0) (u 1)
        (source gamma).1 (source gamma).2).card)
    (hsourceOn : ∀ gamma ∈ family.G,
      gamma ∈ pointsOn family (source gamma)) :
    family.G.card ≤ 2 * h ∨
      ∃ gamma ∈ family.G, ∀ target ∈ lineParameters family,
        h ≤ (jointCore dom (u 0) (u 1) target.1 target.2).card →
          familyFreshCrossCore family gamma (source gamma) target = ∅ := by
  by_cases hcard : family.G.card ≤ 2 * h
  · exact Or.inl hcard
  apply Or.inr
  by_contra hresidual
  have htargetSupply : ∀ gamma ∈ family.G,
      ∃ target ∈ lineParameters family,
        h ≤ (jointCore dom (u 0) (u 1) target.1 target.2).card ∧
        (familyFreshCrossCore family gamma
          (source gamma) target).Nonempty := by
    intro gamma hgamma
    by_contra hnone
    apply hresidual
    refine ⟨gamma, hgamma, ?_⟩
    intro target htargetLine htargetCore
    apply Finset.not_nonempty_iff_eq_empty.mp
    intro hnonempty
    exact hnone ⟨target, htargetLine, htargetCore, hnonempty⟩
  exact hcard <|
    card_le_two_mul_of_distinct_half_core_nonempty_fresh_target_supply
      family hk hn hrate line0 line1 hline0 hline1 hne hcore0 hcore1
        source hsourceLine hsourceCore hsourceOn htargetSupply

/-- **Primitive high-core cover/isolation trichotomy.**  Given two distinct
relevant half-core references, either the family is domain-bounded, a scalar
lies on no half-core line, or a covered scalar has a half-core source whose
fresh cross-core fibre into every half-core target is empty.  There is no
equal-slope branch and no `k-1` root-exception branch. -/
theorem card_le_or_uncovered_or_half_core_isolated_scalar
    {dom : I ↪ F} {k h : Nat} {delta : NNReal}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k) (hn : Fintype.card I = 2 * h) (hrate : 2 * k ≤ h)
    (line0 line1 : LineParameter F)
    (hline0 : line0 ∈ lineParameters family)
    (hline1 : line1 ∈ lineParameters family)
    (hne : line0 ≠ line1)
    (hcore0 : h ≤
      (jointCore dom (u 0) (u 1) line0.1 line0.2).card)
    (hcore1 : h ≤
      (jointCore dom (u 0) (u 1) line1.1 line1.2).card) :
    family.G.card ≤ 2 * h ∨
      (∃ gamma ∈ family.G, ∀ source ∈ lineParameters family,
        h ≤ (jointCore dom (u 0) (u 1) source.1 source.2).card →
          gamma ∉ pointsOn family source) ∨
      ∃ gamma ∈ family.G, ∃ source ∈ lineParameters family,
        h ≤ (jointCore dom (u 0) (u 1) source.1 source.2).card ∧
        gamma ∈ pointsOn family source ∧
        ∀ target ∈ lineParameters family,
          h ≤ (jointCore dom (u 0) (u 1) target.1 target.2).card →
            familyFreshCrossCore family gamma source target = ∅ := by
  by_cases hcoverage : ∀ gamma ∈ family.G,
      ∃ source ∈ lineParameters family,
        h ≤ (jointCore dom (u 0) (u 1) source.1 source.2).card ∧
        gamma ∈ pointsOn family source
  · let source : F → LineParameter F := fun gamma =>
      if hgamma : gamma ∈ family.G then
        Classical.choose (hcoverage gamma hgamma)
      else
        line0
    have hsourceSpec : ∀ gamma ∈ family.G,
        source gamma ∈ lineParameters family ∧
          h ≤ (jointCore dom (u 0) (u 1)
            (source gamma).1 (source gamma).2).card ∧
          gamma ∈ pointsOn family (source gamma) := by
      intro gamma hgamma
      simp only [source, dif_pos hgamma]
      exact Classical.choose_spec (hcoverage gamma hgamma)
    rcases card_le_two_mul_or_exists_half_core_target_isolated_scalar
        family hk hn hrate line0 line1 hline0 hline1 hne hcore0 hcore1
          source
          (fun gamma hgamma => (hsourceSpec gamma hgamma).1)
          (fun gamma hgamma => (hsourceSpec gamma hgamma).2.1)
          (fun gamma hgamma => (hsourceSpec gamma hgamma).2.2) with
      hcard | ⟨gamma, hgamma, hisolated⟩
    · exact Or.inl hcard
    · exact Or.inr <| Or.inr ⟨gamma, hgamma, source gamma,
        (hsourceSpec gamma hgamma).1,
        (hsourceSpec gamma hgamma).2.1,
        (hsourceSpec gamma hgamma).2.2, hisolated⟩
  · apply Or.inr
    apply Or.inl
    push Not at hcoverage
    obtain ⟨gamma, hgamma, huncovered⟩ := hcoverage
    exact ⟨gamma, hgamma, huncovered⟩

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterPrimitiveHighCore

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterPrimitiveHighCore
#print axioms card_le_domain_of_primitive_collapsed_nonempty_freshCrossCores
#print axioms card_le_two_mul_of_distinct_half_core_nonempty_fresh_target_supply
#print axioms card_le_two_mul_or_exists_half_core_target_isolated_scalar
#print axioms card_le_or_uncovered_or_half_core_isolated_scalar
