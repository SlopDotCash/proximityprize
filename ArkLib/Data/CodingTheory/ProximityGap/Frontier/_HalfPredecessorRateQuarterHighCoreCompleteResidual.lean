/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterHighCorePetalGrowth
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterHighCoreUnifiedClosure

/-!
# Rate-quarter high cores: complete one-reference residual

At the saturated quarter rate, a family larger than the domain and containing
one relevant half-core line has no vague one-reference branch.  The reduced
universe petal argument either fails by one explicit arithmetic inequality or
produces a second distinct half-core reference.  In the latter case the
unified slope closure applies: its domain-bound branch contradicts the strict
family-size hypothesis, leaving either an uncovered selected scalar or an
unequal-slope forbidden-capacity witness.

Thus all surviving information is an explicit finite-set or natural-number
obstruction.
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
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterHighCorePetalGrowth
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterHighCoreUnionSupply
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterHighCoreUnifiedClosure

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterHighCoreCompleteResidual

attribute [local instance] Classical.propDecidable

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I]
variable [Field F] [Fintype F] [DecidableEq F]

/-- **Complete saturated high-core residual.**  From one relevant half-core
reference in a family larger than the domain, at least one of the following
explicit obstructions occurs:

1. the reduced-universe budget for forcing a second half core fails;
2. a selected scalar lies on no relevant half-core line;
3. there is a distinct second half-core reference with unequal slope and a
   covered scalar satisfying the aggregate forbidden-capacity inequality.
-/
theorem reduced_budget_failure_or_uncovered_or_nonEqualSlope_forbidden_capacity
    {dom : I ↪ F} {k h : Nat} {delta : NNReal}
    {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom k delta u)
    (hk : 1 ≤ k) (hn : Fintype.card I = 2 * h)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊ = h + 1)
    (hsaturated : h = 2 * k) (hcard : 2 * h < family.G.card)
    (line0 : LineParameter F)
    (hline0 : line0 ∈ highCoreLines family h) :
    (h + 1 - (k - 1)) ^ 2 - 1 <
        (2 * h -
          (jointCore dom (u 0) (u 1) line0.1 line0.2).card) * (h - 1) ∨
      (∃ gamma ∈ family.G, ∀ source ∈ highCoreLines family h,
        gamma ∉ pointsOn family source) ∨
      ∃ line1 ∈ highCoreLines family h, line1 ≠ line0 ∧
        line1.2 ≠ line0.2 ∧
        ∃ gamma ∈ family.G, ∃ source ∈ highCoreLines family h,
          gamma ∈ pointsOn family source ∧
          (fullAgreement dom (u 0) (u 1) gamma (family.q gamma)).card ≤
            (highCoreTransverseForbidden family h line0 line1 source).card := by
  have hline0' := (mem_highCoreLines_iff family h line0).mp hline0
  have hrate : 2 * k ≤ h := by omega
  have hgrowth := second_high_core_or_reduced_budget_failure
    family hk hn hthreshold hrate hcard hline0'.1 hline0'.2
  rcases hgrowth with hsecond | hbudgetFailure
  · obtain ⟨line1, hline1Param, hlineNe, hline1Core⟩ := hsecond
    have hline1 : line1 ∈ highCoreLines family h :=
      (mem_highCoreLines_iff family h line1).mpr
        ⟨hline1Param, hline1Core⟩
    have hunified :=
      card_le_two_mul_or_uncovered_or_nonEqualSlope_forbidden_capacity
        family hk hn hsaturated line0 line1 hline0 hline1 hlineNe.symm
    rcases hunified with hdomain | hrest
    · omega
    · rcases hrest with huncovered | hforbidden
      · exact Or.inr (Or.inl huncovered)
      · exact Or.inr (Or.inr
          ⟨line1, hline1, hlineNe, hforbidden.1, hforbidden.2⟩)
  · exact Or.inl hbudgetFailure

#print axioms
  reduced_budget_failure_or_uncovered_or_nonEqualSlope_forbidden_capacity

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterHighCoreCompleteResidual
