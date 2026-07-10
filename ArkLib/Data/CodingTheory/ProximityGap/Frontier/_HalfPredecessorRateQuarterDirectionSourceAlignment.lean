/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterDirectionCapGlobalConsumer

/-!
# Rate-quarter direction/source alignment at the top of the exceptional band

The exceptional direction produced by direction-cap failure is not completely
independent of a large residual source line.  If the source joint core has
cardinality `c` and the exceptional direction core has cardinality `z`, their
intersection has size at least `c + z - n`.  Two distinct degree-`<4` slope
polynomials can agree on at most three domain coordinates.  Consequently

```text
20 <= c + z,  n = 16  ==>  exceptional direction = source slope.
```

In particular, the unique-eight-core residual is aligned at exceptional core
sizes 12 and 13; a size-seven no-eight source is aligned at size 13.  This does
not close those aligned cases, but it removes the claim that the two directions
are wholly unrelated throughout the surviving band.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open Finset Polynomial
open _root_.ProximityGap Code
open scoped NNReal Polynomial
open ArkLib.ProximityGap.Frontier.HalfPredecessorLineCoreGeometry
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge
open ArkLib.ProximityGap.Frontier.HalfPredecessorSecantLines
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterDirectionCapDichotomy
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterDirectionCapGlobalConsumer
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterKFourGlobalCoreSynthesis

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterDirectionSourceAlignment

attribute [local instance] Classical.propDecidable

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I]
variable [Field F] [Fintype F] [DecidableEq F]

/-- Distinct degree-below-four slopes can coincide on at most three coordinates
of a source joint core and an exceptional direction core. -/
theorem jointCore_inter_directionAgreement_card_le_three_of_ne
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    {source : LineParameter F} (hsource : source ∈ lineParameters family)
    {r : F[X]} (hr : r.natDegree < 4) (hne : source.2 ≠ r) :
    (jointCore dom (u 0) (u 1) source.1 source.2 ∩
      directionAgreement dom (u 1) r).card <= 3 := by
  let p : F[X] := source.2 - r
  have hp0 : p ≠ 0 := sub_ne_zero.mpr hne
  have hsourceDeg := (lineParameter_degree_lt family hsource).2
  have hpdeg : p.natDegree < 4 :=
    lt_of_le_of_lt (natDegree_sub_le _ _) (max_lt hsourceDeg hr)
  have hsub :
      jointCore dom (u 0) (u 1) source.1 source.2 ∩
          directionAgreement dom (u 1) r ⊆
        Finset.univ.filter (fun i => p.eval (dom i) = 0) := by
    intro i hi
    have hi' := Finset.mem_inter.mp hi
    have hsourceEval := (Finset.mem_filter.mp hi'.1).2.2
    have hrEval := (Finset.mem_filter.mp hi'.2).2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, p, eval_sub]
    rw [hsourceEval, hrEval, sub_self]
  calc
    (jointCore dom (u 0) (u 1) source.1 source.2 ∩
        directionAgreement dom (u 1) r).card <=
      (Finset.univ.filter (fun i => p.eval (dom i) = 0)).card :=
        Finset.card_le_card hsub
    _ <= 4 - 1 := domain_root_card_le_pred dom (by norm_num) p hp0 hpdeg
    _ = 3 := by norm_num

/-- If the two core cardinalities sum to at least twenty at length sixteen,
the exceptional direction is the source-line slope. -/
theorem direction_eq_sourceSlope_of_twenty_le_core_add
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    {source : LineParameter F} (hsource : source ∈ lineParameters family)
    {r : F[X]} (hr : r.natDegree < 4)
    (hsum : 20 <=
      (jointCore dom (u 0) (u 1) source.1 source.2).card +
        (directionAgreement dom (u 1) r).card) :
    r = source.2 := by
  by_contra hne
  have hinter := jointCore_inter_directionAgreement_card_le_three_of_ne
    family hsource hr (Ne.symm hne)
  have hunion :
      (jointCore dom (u 0) (u 1) source.1 source.2 ∪
        directionAgreement dom (u 1) r).card <= 16 := by
    have hle := Finset.card_le_card
      (Finset.subset_univ
        (jointCore dom (u 0) (u 1) source.1 source.2 ∪
          directionAgreement dom (u 1) r))
    simpa only [Finset.card_univ, hn] using hle
  have hbook := Finset.card_union_add_card_inter
    (jointCore dom (u 0) (u 1) source.1 source.2)
    (directionAgreement dom (u 1) r)
  omega

/-- The top two exceptional sizes align with a unique size-eight source. -/
theorem uniqueEight_direction_eq_sourceSlope_of_twelve_le
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (residual : UniqueEightCoreResidual family)
    {r : F[X]} (hr : r.natDegree < 4)
    (hdir : 12 <= (directionAgreement dom (u 1) r).card) :
    r = residual.source.2 := by
  apply direction_eq_sourceSlope_of_twenty_le_core_add
    family hn residual.source_mem hr
  rw [residual.source_core_card]
  omega

/-- A size-seven no-eight source aligns with an exceptional core of size
thirteen. -/
theorem noEightSeven_direction_eq_sourceSlope_of_thirteen_le
    {dom : I ↪ F} {delta : NNReal} {u : WordStack F (Fin 2) I}
    (family : BadScalarRichPointFamily dom 4 delta u)
    (hn : Fintype.card I = 16)
    (residual : NoEightCoreIntermediateResidual family)
    (hsource :
      (jointCore dom (u 0) (u 1)
        residual.source.1 residual.source.2).card = 7)
    {r : F[X]} (hr : r.natDegree < 4)
    (hdir : 13 <= (directionAgreement dom (u 1) r).card) :
    r = residual.source.2 := by
  apply direction_eq_sourceSlope_of_twenty_le_core_add
    family hn residual.source_mem hr
  rw [hsource]
  omega

#print axioms jointCore_inter_directionAgreement_card_le_three_of_ne
#print axioms direction_eq_sourceSlope_of_twenty_le_core_add
#print axioms uniqueEight_direction_eq_sourceSlope_of_twelve_le
#print axioms noEightSeven_direction_eq_sourceSlope_of_thirteen_le

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterDirectionSourceAlignment
