/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterKFourSyndromeDegeneracy
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterKFourDependentSyndromeCollapse
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterKFourTwoColumnCollapse

/-!
# Rate-quarter `n = 16`, `k = 4`: the unique eight-core branch is closed

The strict syndrome-chord theorem reduces a unique-eight-core residual to
dependent quotient rows or a coordinate column in the quotient row plane.
The dependent-row compact-edge theorem rules out the first branch.

The quotient rows are therefore independent.  If their plane contains
exactly one coordinate column, deleting it leaves a seven-column transitive
chord graph with at most six edges, so there are at most seven regular
outsiders.  If it contains a second coordinate column, the two MDS columns
span the plane and every regular missed edge is their common pair; compact
edge collinearity then produces a forbidden second eight-core.

Thus the unique-eight-core residual is empty.  The global `n = 16`, `k = 4`
classification now has only the domain bound and the no-eight intermediate
core residual.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open Finset Module Submodule
open _root_.ProximityGap Code
open scoped NNReal
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourGlobalCoreSynthesis
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourWeightTwoSyndrome
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourUniqueCoreSyndrome
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourSyndromeDegeneracy
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourDependentSyndromeCollapse
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourTwoColumnCollapse

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourUniqueCoreClosed

attribute [local instance] Classical.propDecidable

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I]
variable [Field F] [Fintype F] [DecidableEq F]

/-- **Unique-eight-core closure.**  No unique-eight-core residual exists at
the length-sixteen, threshold-nine endpoint. -/
theorem uniqueEightCoreResidual_false
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (hthreshold : 9 ≤
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊)
    (residual : UniqueEightCoreResidual family) :
    False := by
  classical
  have hrows : QuotientRowsIndependent
      (sourceComplementCode family residual.source)
      (sourceComplementRow0 family residual.source)
      (sourceComplementRow1 family residual.source) :=
    uniqueEightCoreResidual_quotientRowsIndependent
      family hn hthreshold residual
  rcases uniqueEightCoreResidual_quotient_degenerate
      family hn residual with hdep | ⟨key, hkey⟩
  · exact hdep hrows
  · by_cases hnoOther :
        ∀ i : ↑(sourceComplement family residual.source),
          i ≠ key →
            quotientColumn (sourceComplementCode family residual.source) i ∉
              span F ({
                (sourceComplementCode family residual.source).mkQ
                  (sourceComplementRow0 family residual.source),
                (sourceComplementCode family residual.source).mkQ
                  (sourceComplementRow1 family residual.source)} :
                    Set ((↑(sourceComplement family residual.source) → F) ⧸
                      sourceComplementCode family residual.source))
    · exact uniqueEightCoreResidual_not_exactly_one_contained_column
        family hn residual hrows key hkey hnoOther
    · push Not at hnoOther
      obtain ⟨key2, hkey2Ne, hkey2⟩ := hnoOther
      exact uniqueEightCoreResidual_false_of_two_contained_columns
        family hn hthreshold residual key key2 (Ne.symm hkey2Ne) hkey hkey2

/-- **Sharpened global classification.**  The unique-eight-core alternative
is gone; only the no-eight intermediate-core package remains beyond the
domain bound. -/
theorem card_le_sixteen_or_no_eight_intermediate
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (hthreshold :
      ⌈(1 - delta) * (Fintype.card I : NNReal)⌉₊ = 9) :
    family.G.card ≤ 16 ∨
      Nonempty (NoEightCoreIntermediateResidual family) := by
  rcases card_le_sixteen_or_unique_eight_core_or_no_eight_intermediate
      family hn hthreshold with hle | hresidual
  · exact Or.inl hle
  · rcases hresidual with hunique | hnoEight
    · obtain ⟨residual⟩ := hunique
      exact (uniqueEightCoreResidual_false
        family hn hthreshold.ge residual).elim
    · exact Or.inr hnoEight

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourUniqueCoreClosed

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourUniqueCoreClosed
#print axioms uniqueEightCoreResidual_false
#print axioms card_le_sixteen_or_no_eight_intermediate
