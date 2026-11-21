/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeCubicReceivedOrder
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeCubicIntrinsicEscape
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeActualPopulations

/-! # A received-family population bound for large-weight proper cubics

The cubic's own translated Hessian controls its true jet orders. In the upper
weight interval this supplies enough independent interpolation constraints to cap
the population using the original polynomial selections throughout.
-/

namespace ArkLib.ProximityGap.Frontier.SecondPrimeActualCubicCap

open Finset Polynomial SecondPrimeCoordinateWeight SecondPrimeScalarChart
open HalfPredecessorBadEventRichPointBridge SecondPrimeActualPopulations
open MovingCubicVanishingBranch CanonicalQuarticSiteOrder
open scoped NNReal

variable {I F K : Type} [Fintype I] [Field F] [DecidableEq F] [Field K]
  {dom : I ↪ F} {δ : ℝ≥0} {u : Code.WordStack F (Fin 2) I}

/-- The proper cubic cannot carry the population required by the original factorization
when its coordinate/value weight reaches 220 million. -/
theorem population_cap (fam : Family dom δ u) (φ : F →+* K)
    (hn : Fintype.card I = 1073741824)
    (ht : 357913943 ≤ ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊)
    (Q f : Surface K) (hQ : Q ≠ 0) (hdiv : f ∣ Q) (hi : Irreducible f) (hc : f.natDegree = 3)
    (htri : ∀ j i a, ((Q.coeff j).coeff i).coeff a ≠ 0 → i + j ≤ 34)
    (wlarge : 220000000 ≤ weight 67108863 f)
    (hnd : ¬ genericEquation (scalarChart f) ∣
      genericEquation (scalarFieldHessian (scalarChart f))) :
    (population fam φ f).card ≤ 1200005270 := by
  classical
  let D := dom.trans (⟨φ, φ.injective⟩ : F ↪ K)
  have h := SecondPrimeCubicReceivedOrder.actual_received_budget f hi hc D
    (fun i => φ (u 0 i)) (fun i => φ (u 1 i)) 67108863 hnd
  rw [hn] at h
  exact SecondPrimeCubicIntrinsicEscape.actual_cubic_cap φ dom δ u hn ht fam Q f hQ hdiv hi
    hc htri _ (filter_subset _ _) (fun _ hz => (mem_filter.mp hz).2) (.inr ⟨wlarge, h⟩)

#print axioms population_cap
end ArkLib.ProximityGap.Frontier.SecondPrimeActualCubicCap
