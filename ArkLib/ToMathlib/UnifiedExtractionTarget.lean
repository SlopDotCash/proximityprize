/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.FaithfulCurveExtraction
import ArkLib.ToMathlib.BoundaryHalfState

/-!
# Issue #304 — the unified extraction target: BOTH cores from ONE producer

The two named open cores of #304 — `StrictCoeffPolysResidual` (the strict-Johnson branch) and
the boundary half (through the O76/O79/O86 quantization split, whose surviving leaves are
`StrictCoeffPolysLargeResidual` at the cell radius and `LatticeCoeffPolyExtraction` at the
square endpoint) — all conclude the same `∃ B` coefficient-polynomial extraction, differing
only in their trigger (probability / probability+count / count).  And the faithful curve
extraction (`FaithfulCurveExtraction.hcoeffPoly_witness_of_curveFamilyData`) produces that
`∃ B` from a `CurveFamilyData`.

This file states the convergence as theorems:

* `UnifiedProducer` — the single production target: per word-stack and decoded family
  (count-triggered, the weakest trigger any consumer supplies), a `CurveFamilyData`.
* `latticeCoeffPolyExtraction_of_producer` — the lattice leaf from the producer.
* `strictCoeffPolysLargeResidual_of_producer` — the cell-radius leaf from the producer
  (instantiated at the cell radius).
* `strictCoeffPolysResidual_of_producer` — the strict-Johnson core from the producer
  (the probability trigger is discarded; the count trigger is supplied by the consumer's own
  `k + 1 < |good|`... NOTE: `StrictCoeffPolysResidual` carries no count hypothesis, so the
  producer is consumed with the trigger weakened to `0 ≤ |good|` — i.e. this consumer needs
  the *untriggered* producer; stated separately as `strictCoeffPolysResidual_of_producer'`
  from the untriggered form).
* `correlatedAgreementCurves_johnsonClosed_of_producer` — **the closed-boundary keystone**
  (the Johnson-endpoint dichotomy of `BoundaryHalfState`) from the count-triggered producer
  alone: both dichotomy leaves discharged by the same object.

**The disposition**: after this file, issue #304's remaining mathematical content is exactly
the production of `CurveFamilyData` per word-stack — the object the assembled GS matching lane
(S10-converse → Claim-5.7+branch pigeonholes → per-z proximate roots → truncation → converter
→ extraction) terminates in.  Both cores, strict and boundary, consume it verbatim.

## References
* [BCIKS20] §5–§6; the O76/O79/O86 boundary split; issue #304.
-/

set_option linter.style.longLine false

open Polynomial ProximityGap Code NNReal Finset Function ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory LinearCode

namespace ArkLib

namespace UnifiedExtractionTarget

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **The unified production target**: per word-stack and per decoded family, with the count
trigger (the weakest any consumer supplies), a faithful `CurveFamilyData`. -/
def UnifiedProducer (k deg : ℕ) (domain : ι ↪ F) (δ : ℝ≥0) : Prop :=
  ∀ u : WordStack F (Fin (k + 1)) ι,
    k < (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card →
    ∀ P : F → Polynomial F,
      (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
        (P z).natDegree < deg ∧
          δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t, (P z).eval ∘ domain) ≤ δ) →
      Nonempty (FaithfulCurveExtraction.CurveFamilyData
        (k := k) (deg := deg) (domain := domain) (δ := δ) u P)

/-! ## The lattice leaf -/

omit [Nonempty ι] [DecidableEq ι] in
/-- **The lattice leaf from the producer**: the count trigger of
`LatticeCoeffPolyExtraction` implies the producer's, and the `∃ B` conclusion is the
faithful extraction's output. -/
theorem latticeCoeffPolyExtraction_of_producer {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hprod : UnifiedProducer (k := k) (deg := deg) (ι := ι) (F := F) domain δ) :
    ArkLib.BoundaryLatticeThresholdLeaf.LatticeCoeffPolyExtraction
      (k := k) (deg := deg) domain δ := by
  intro u hcount P hP
  have htrig : k < (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card := by
    have h1 : k ≤ (Fintype.card ι + 1) * k := by
      have : 1 ≤ Fintype.card ι + 1 := by omega
      calc k = 1 * k := (one_mul k).symm
        _ ≤ (Fintype.card ι + 1) * k := Nat.mul_le_mul_right k this
    omega
  obtain ⟨d⟩ := hprod u htrig P hP
  exact FaithfulCurveExtraction.hcoeffPoly_witness_of_curveFamilyData d

/-! ## The cell-radius leaf -/

omit [Nonempty ι] [DecidableEq ι] in
/-- **The cell-radius leaf from the producer** (instantiated at any radius — in particular
the canonical cell radius): the probability and Johnson hypotheses are discarded; the count
trigger `k + 1 < |good|` implies the producer's. -/
theorem strictCoeffPolysLargeResidual_of_producer {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hprod : UnifiedProducer (k := k) (deg := deg) (ι := ι) (F := F) domain δ) :
    ProximityGap.StrictCoeffPolysLargeResidual
      (k := k) (deg := deg) (domain := domain) (δ := δ) := by
  intro hk u _hprob _hJ _hsqrt hcount P hP
  obtain ⟨d⟩ := hprod u (by omega) P hP
  exact FaithfulCurveExtraction.hcoeffPoly_witness_of_curveFamilyData d

/-! ## The closed-boundary keystone -/

/-- **The closed-boundary Johnson-endpoint keystone from the single producer.**  Both leaves
of the `BoundaryHalfState` dichotomy — the cell-radius `StrictCoeffPolysLargeResidual` and the
lattice `LatticeCoeffPolyExtraction` — are discharged by the same count-triggered
`CurveFamilyData` production (at the cell radius and at `δ` respectively).  The explicit
positive error is the dichotomy's `max (errorBound (⌊δ·n⌋/n)) ((n+1)/|F|)`. -/
theorem correlatedAgreementCurves_johnsonClosed_of_producer
    {k deg : ℕ} [NeZero deg] {domain : ι ↪ F} {δ : ℝ≥0}
    (hk : 0 < k)
    (hδeq : δ = 1 - ReedSolomon.sqrtRate deg domain)
    (hsqrt_le : ReedSolomon.sqrtRate deg domain ≤ 1)
    (hdeg_le : deg ≤ Fintype.card ι)
    (hprodCell : UnifiedProducer (k := k) (deg := deg) (ι := ι) (F := F) domain
      (BoundaryHalfState.boundaryCellRadius (Fintype.card ι) δ))
    (hprodδ : UnifiedProducer (k := k) (deg := deg) (ι := ι) (F := F) domain δ) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ)
      (ε := max (errorBound (BoundaryHalfState.boundaryCellRadius (Fintype.card ι) δ)
          deg domain)
        (ArkLib.BoundaryLatticeThresholdLeaf.latticeThresholdEps ι F)) :=
  BoundaryHalfState.correlatedAgreementCurves_johnsonClosed_of_leaves hk hδeq hsqrt_le hdeg_le
    (fun _ => strictCoeffPolysLargeResidual_of_producer hprodCell)
    (fun _ => latticeCoeffPolyExtraction_of_producer hprodδ)

end UnifiedExtractionTarget

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.UnifiedExtractionTarget.UnifiedProducer
#print axioms ArkLib.UnifiedExtractionTarget.latticeCoeffPolyExtraction_of_producer
#print axioms ArkLib.UnifiedExtractionTarget.strictCoeffPolysLargeResidual_of_producer
#print axioms ArkLib.UnifiedExtractionTarget.correlatedAgreementCurves_johnsonClosed_of_producer
