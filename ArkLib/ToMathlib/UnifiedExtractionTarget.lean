/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.FaithfulCurveExtraction
import ArkLib.ToMathlib.BoundaryHalfState

/-!
# Issue #304 — the count-triggered unified extraction interface (conditional reductions)

The two named open cores of #304 — `StrictCoeffPolysResidual` (the strict-Johnson branch) and
the boundary half (through the O76/O79/O86 quantization split, whose surviving leaves are
`StrictCoeffPolysLargeResidual` at the cell radius and `LatticeCoeffPolyExtraction` at the
square endpoint) — all conclude the same `∃ B` coefficient-polynomial extraction, differing
only in their trigger (probability / probability+count / count).  And the faithful curve
extraction (`FaithfulCurveExtraction.hcoeffPoly_witness_of_curveFamilyData`) produces that
`∃ B` from a `CurveFamilyData`.

This file states the convergence as **conditional** theorems:

* `UnifiedProducer` — a single count-triggered production *interface*: per word-stack and
  decoded family with `k < |good|`, a `CurveFamilyData`.  It is the weakest trigger any
  consumer supplies, which makes it the *strongest* producer statement, and it is **false in
  general** (see "Honest status" below).
* `latticeCoeffPolyExtraction_of_producer` — the lattice leaf from the producer.
* `strictCoeffPolysLargeResidual_of_producer` — the cell-radius leaf from the producer
  (instantiated at the cell radius).
* `correlatedAgreementCurves_johnsonClosed_of_producer` — the closed-boundary keystone
  (the Johnson-endpoint dichotomy of `BoundaryHalfState`) from the count-triggered producer
  at the two fixed radii it consumes (the boundary cell radius and `δ` itself).
* `no_affine_values_zmod5` — the kernel-checked arithmetic core of the counterexample below.

`StrictCoeffPolysResidual` carries no count hypothesis, so it is **not** derived here from the
count-triggered producer; it has its own probability-triggered faithful interface
(`FaithfulCurveExtraction.strictCoeffPolysResidual_of_curveFamilyData`).

## Honest status: the bare count-only producer is false inside the Johnson window

`UnifiedProducer` drops the high-probability trigger retained by the faithful producer
interfaces of `FaithfulCurveExtraction` (`Pr[…] > k · errorBound δ`), and `k < |good|` cannot
replace it in general.  Counterexample (exact enumeration, source-derived translation;
the arithmetic contradiction is `no_affine_values_zmod5`): `F = 𝔽₅`, domain `(0, 1, 2)`,
`deg = 1` (the constant code, rate `1/3`), `k = 1`, `δ = 7/20`, stack `u₀ = (0,0,1)`,
`u₁ = (0,1,2)`.  The words `u₀ + z·u₁` for `z = 0,…,4` are `(0,0,1), (0,1,3), (0,2,0),
(0,3,2), (0,4,4)`; exactly `z ∈ {0, 2, 4}` are within `δ` of a constant (the constants
`0, 0, 4`, at distance `1/3`), so `|good| = 3 > k`.  The radius lies strictly inside the
Johnson window: `(1 − ρ)/2 = 1/3 < 7/20 < 1 − √(1/3)`.  But `CurveFamilyData` forces
`n < k + 2 = 2` curve coefficients, so the constant coefficient of the decoded family would
be an affine function `B` of `z` with `B 0 = B 2 = 0`, `B 4 = 4` — impossible over `𝔽₅`.
Hence `UnifiedProducer 1 1 domain (7/20)` is **false** there, and every theorem below that
assumes it is a valid implication from a false premise in such regimes.

What this does **not** refute: the original high-probability BCIKS20 statement, the
probability-triggered faithful producers, or the instantiated producers of the
closed-boundary consumer at its own fixed radii (the counterexample is not at a closed
Johnson boundary).  Known true instances: `UnifiedProducerWindowGlue.unifiedProducer_of_window`
proves `UnifiedProducer` on the unique-decoding window
`(k+1)·n + deg ≤ (k+2)·(n − ⌊δ·n⌋)` (the counterexample violates it: `7 > 6`).  A genuine
production target outside that window must restore the probability / radius / parameter
triggers each consumer actually supplies (or prove a justified larger count threshold, such
as the lattice leaf's `(n+1)·k < |good|`, which the counterexample does not meet); the bare
count-only producer is **not** equivalent to the original mathematical task, and future
target strengthenings should be checked against the counterexample above.

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

-- These historical finite-field statements use the uniform finite sampler.
private noncomputable local instance : SampleableType F := SampleableType.ofFintype F

/-- **The count-triggered unified production interface**: per word-stack and per decoded
family, with the count trigger `k < |good|` (the weakest any consumer supplies), a faithful
`CurveFamilyData`.

**Not a viable unconditional target**: this all-input count-only form is false in general,
even strictly inside the Johnson window (`F = 𝔽₅`, `deg = 1`, `k = 1`, `δ = 7/20`; see the
module docstring and `no_affine_values_zmod5`).  It is proved on the unique-decoding window
(`UnifiedProducerWindowGlue.unifiedProducer_of_window`); outside it, consumers must be fed
producers carrying their actual probability / radius / parameter triggers. -/
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

/-- **The closed-boundary Johnson-endpoint keystone from the count-triggered producer
(conditional).**  Both leaves
of the `BoundaryHalfState` dichotomy — the cell-radius `StrictCoeffPolysLargeResidual` and the
lattice `LatticeCoeffPolyExtraction` — are discharged by the same count-triggered
`CurveFamilyData` production (at the cell radius and at `δ` respectively).  The explicit
positive error is the dichotomy's `max (errorBound (⌊δ·n⌋/n)) ((n+1)/|F|)`.  The hypotheses
are count-only producers at these two fixed radii; such producers are false in general (see
`UnifiedProducer`), so this is a reduction, not evidence that the hypotheses are inhabited
beyond the proved unique-decoding window. -/
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

/-! ## The counterexample's arithmetic core (kernel-checked)

The decoded constants of the `𝔽₅` counterexample in the module docstring take the values
`0, 0, 4` at `z = 0, 2, 4`; no polynomial of degree `< 2` (what `CurveFamilyData` with `k = 1`
forces for each coefficient, via `FaithfulCurveExtraction.hcoeffPoly_witness_of_curveFamilyData`)
interpolates them.  The full translation of the enumerated instance into a refutation of the
Lean `UnifiedProducer` declaration remains source-derived. -/

private instance fact_prime_five : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- No polynomial of degree `< 2` over `𝔽₅` takes the values `0, 0, 4` at `0, 2, 4`. -/
theorem no_affine_values_zmod5 (B : (ZMod 5)[X]) (hdeg : B.natDegree < 2)
    (h0 : B.eval 0 = 0) (h2 : B.eval 2 = 0) (h4 : B.eval 4 = 4) : False := by
  have hlin (x : ZMod 5) : B.eval x = B.coeff 0 + B.coeff 1 * x := by
    rw [Polynomial.eval_eq_sum_range' hdeg]
    simp [Finset.sum_range_succ]
  have hc0 : B.coeff 0 = 0 := by simpa [hlin] using h0
  have hc1 : B.coeff 1 = 0 := by
    have h : B.coeff 1 * (2 : ZMod 5) = 0 := by simpa [hlin, hc0] using h2
    exact (mul_eq_zero.mp h).resolve_right (by decide)
  have h : (0 : ZMod 5) = 4 := by simpa [hlin, hc0, hc1] using h4
  exact (by decide : (0 : ZMod 5) ≠ 4) h

end UnifiedExtractionTarget

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.UnifiedExtractionTarget.UnifiedProducer
#print axioms ArkLib.UnifiedExtractionTarget.latticeCoeffPolyExtraction_of_producer
#print axioms ArkLib.UnifiedExtractionTarget.strictCoeffPolysLargeResidual_of_producer
#print axioms ArkLib.UnifiedExtractionTarget.correlatedAgreementCurves_johnsonClosed_of_producer
#print axioms ArkLib.UnifiedExtractionTarget.no_affine_values_zmod5
