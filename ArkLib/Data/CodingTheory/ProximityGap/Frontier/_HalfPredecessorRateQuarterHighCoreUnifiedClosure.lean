/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterEqualSlopeJohnsonClosure
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterHighCoreUnionSupply

/-!
# Rate-quarter high cores: unified slope closure

Two distinct relevant half-core reference lines split the saturated
rate-quarter frontier by whether their slope polynomials agree.

* Equal slopes put every relevant half core in one Johnson cluster.  The
  scalars covered by those lines are domain-bounded, so either the whole
  family is bounded or a selected scalar lies on no half-core line.
* Unequal slopes feed the aggregate high-core residual decomposition.  It
  gives the same first two alternatives, or an explicit covered scalar whose
  agreement-set cardinality is at most the size of the union of its source
  core, the reference singular locus, and the coordinates missed by every
  high core.

The final theorem keeps the slope inequality attached to that last witness,
so all surviving information from the branch split is available downstream.
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
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterEqualSlopeHighCores
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterEqualSlopeJohnsonClosure
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterHighCoreUnionSupply

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterHighCoreUnifiedClosure

attribute [local instance] Classical.propDecidable

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I]
variable [Field F] [Fintype F] [DecidableEq F]

/-- The independently introduced equal-slope and aggregate-union notions of
a relevant half-core line are definitionally the same finite set. -/
theorem halfCoreLines_eq_highCoreLines
    {dom : I ↪ F} {k : Nat} {delta : NNReal}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom k delta u) (h : Nat) :
    halfCoreLines family h = highCoreLines family h := by
  rfl

/-- **Equal-slope high-core alternative.**  Two distinct half-core references
with the same slope either close the family at the domain bound or leave a
selected scalar uncovered by every relevant half-core line. -/
theorem card_le_two_mul_or_uncovered_of_equalSlope_highCores
    {dom : I ↪ F} {k h : Nat} {delta : NNReal}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k) (hn : Fintype.card I = 2 * h)
    (hsaturated : h = 2 * k)
    (line0 line1 : LineParameter F)
    (hline0 : line0 ∈ highCoreLines family h)
    (hline1 : line1 ∈ highCoreLines family h)
    (hne : line0 ≠ line1) (hslope : line1.2 = line0.2) :
    family.G.card ≤ 2 * h ∨
      ∃ gamma ∈ family.G, ∀ source ∈ highCoreLines family h,
        gamma ∉ pointsOn family source := by
  have hline0' := (mem_highCoreLines_iff family h line0).mp hline0
  have hline1' := (mem_highCoreLines_iff family h line1).mp hline1
  by_cases hcover : family.G ⊆ halfCoreCoveredScalars family h
  · exact Or.inl <| G_card_le_two_mul_of_equalSlope_halfCore_cover
      family hk hn hsaturated line0 line1 hline0'.1 hline1'.1
        hne hslope hline0'.2 hline1'.2 hcover
  · apply Or.inr
    simp only [Finset.not_subset] at hcover
    obtain ⟨gamma, hgamma, hgammaUncovered⟩ := hcover
    refine ⟨gamma, hgamma, ?_⟩
    intro source hsource hgammaOn
    apply hgammaUncovered
    simp only [halfCoreCoveredScalars, Finset.mem_biUnion]
    refine ⟨source, ?_, hgammaOn⟩
    rw [halfCoreLines_eq_highCoreLines family h]
    exact hsource

/-- **Unified high-core slope trichotomy.**  At the saturated quarter rate,
two distinct reference half cores force at least one of the following useful
outcomes:

1. the selected scalar family is domain-bounded;
2. some selected scalar lies on no relevant half-core line;
3. the reference slopes differ and an explicit covered scalar saturates the
   aggregate forbidden-capacity obstruction.
-/
theorem card_le_two_mul_or_uncovered_or_nonEqualSlope_forbidden_capacity
    {dom : I ↪ F} {k h : Nat} {delta : NNReal}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k) (hn : Fintype.card I = 2 * h)
    (hsaturated : h = 2 * k)
    (line0 line1 : LineParameter F)
    (hline0 : line0 ∈ highCoreLines family h)
    (hline1 : line1 ∈ highCoreLines family h)
    (hne : line0 ≠ line1) :
    family.G.card ≤ 2 * h ∨
      (∃ gamma ∈ family.G, ∀ source ∈ highCoreLines family h,
        gamma ∉ pointsOn family source) ∨
      (line1.2 ≠ line0.2 ∧
        ∃ gamma ∈ family.G, ∃ source ∈ highCoreLines family h,
          gamma ∈ pointsOn family source ∧
          (fullAgreement dom (u 0) (u 1) gamma (family.q gamma)).card ≤
            (highCoreTransverseForbidden family h line0 line1 source).card) := by
  by_cases hslope : line1.2 = line0.2
  · rcases card_le_two_mul_or_uncovered_of_equalSlope_highCores
      family hk hn hsaturated line0 line1 hline0 hline1 hne hslope with
      hcard | huncovered
    · exact Or.inl hcard
    · exact Or.inr (Or.inl huncovered)
  · have hrate : 2 * k ≤ h := by omega
    have htrichotomy := card_le_two_mul_or_uncovered_or_forbidden_capacity
      family hk hn hrate line0 line1 hline0 hline1
    rcases htrichotomy with hcard | hrest
    · exact Or.inl hcard
    · rcases hrest with huncovered | hforbidden
      · exact Or.inr (Or.inl huncovered)
      · exact Or.inr (Or.inr ⟨hslope, hforbidden⟩)

#print axioms card_le_two_mul_or_uncovered_of_equalSlope_highCores
#print axioms card_le_two_mul_or_uncovered_or_nonEqualSlope_forbidden_capacity

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterHighCoreUnifiedClosure
