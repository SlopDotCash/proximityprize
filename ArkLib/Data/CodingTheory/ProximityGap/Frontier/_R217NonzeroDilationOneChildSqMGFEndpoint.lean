/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (R217 nonzero one-child square MGF endpoint)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R213NonzeroNormalizedSqQuarterMGFResidualConsumer
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R215OneChildDirectMGFLaw

/-!
# R217 (#466): nonzero Gauss-period one-child square-MGF endpoint

The direct square-MGF residual must live on the nonprincipal spectrum.  The full
frequency set contains the DC term `b = 0`, where `η_G(0) = |G|`; that is not
the prize-facing concentration target.

This file composes the nonzero normalized-square residual from R213 with the
R215 one-child permutation consumer.  Multiplication by `ζ ≠ 0` preserves
`nonzeroFreqs`, so one R213 residual for `G` supplies both dyadic children for
the concrete dilation parent.
-/

open Finset AddChar
open Real
open scoped BigOperators

set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R217NonzeroDilationOneChildSqMGFEndpoint

open ArkLib.ProximityGap.Frontier.R204PrizeTowerLargeIndex
open ArkLib.ProximityGap.Frontier.R207NonzeroGaussPeriodDilationConsumer
open ArkLib.ProximityGap.Frontier.R213NonzeroNormalizedSqQuarterMGFResidualConsumer
open ArkLib.ProximityGap.Frontier.R214DirectChildMGFLaw
open ArkLib.ProximityGap.Frontier.R215OneChildDirectMGFLaw
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable section

/-- Multiplication by a nonzero field element as a permutation of frequency
space. -/
def mulLeftPerm (ζ : F) (hζ : ζ ≠ 0) : Equiv.Perm F where
  toFun b := ζ * b
  invFun b := ζ⁻¹ * b
  left_inv b := by
    simp [hζ]
  right_inv b := by
    field_simp [hζ]

/-- The multiplicative-frequency permutation preserves the nonzero carrier. -/
theorem mulLeftPerm_mem_nonzeroFreqs {ζ : F} (hζ : ζ ≠ 0) (b : F) :
    mulLeftPerm ζ hζ b ∈ nonzeroFreqs (F := F) ↔
      b ∈ nonzeroFreqs (F := F) := by
  rw [mem_nonzeroFreqs, mem_nonzeroFreqs]
  constructor
  · intro h hb0
    exact h (by simp [mulLeftPerm, hb0])
  · intro hb
    exact mul_ne_zero hζ hb

/-- R213's named residual is exactly the R214/R215 direct child law on the
nonzero carrier. -/
theorem largeIndexChildQuarterMGF_of_nonzeroNormalizedSqResidual
    (ψ : AddChar F ℂ) (G : Finset F) {σ : ℝ}
    (hMGF : NonzeroNormalizedSqQuarterMGFResidual ψ G σ) :
    LargeIndexChildQuarterMGFLaw (nonzeroFreqs (F := F))
      (fun b => ‖eta ψ G b‖) σ := by
  exact hMGF

/-- Concrete nonprincipal dilation endpoint from one normalized-square MGF
residual.  The `hcard` hypothesis keeps the theorem in the same prize-tower
shape as R215; the deterministic proof only uses the nonzero carrier and the
standard moment bridge. -/
theorem prize_sq_of_nonzero_dilation_one_child_sqMGFResidual
    (ψ : AddChar F ℂ) (G : Finset F) {ζ : F}
    (hζ : ζ ≠ 0) (hdisj : Disjoint G (dilate ζ G))
    (depth : ℕ) {σR Mmax n Q : ℝ} {r : ℕ}
    (hσR : 0 < σR)
    (hcard : (nonzeroFreqs (F := F)).card = DyadicTowerIndex PrizeTopIndex depth)
    (hMGF : NonzeroNormalizedSqQuarterMGFResidual ψ G σR)
    (hMmax : 0 ≤ Mmax) (hn : 0 ≤ n) (hQ : 0 < Q)
    (hP : 0 < ((nonzeroFreqs (F := F)).card : ℝ))
    (hr : 1 ≤ r) (hrQ : Real.log Q ≤ r)
    (hmoment : Mmax ^ (2 * r) ≤
      Q * (n ^ r *
        ((∑ b ∈ nonzeroFreqs (F := F),
            (‖eta ψ (G ∪ dilate ζ G) b‖ ^ 2 / (2 * σR ^ 2)) ^ r) /
          ((nonzeroFreqs (F := F)).card : ℝ)))) :
    Mmax ^ 2 ≤ 2 * Real.exp 1 * (2 / (1 / 8 : ℝ)) * n * (r : ℝ) := by
  let shift : Equiv.Perm F := mulLeftPerm ζ hζ
  refine prize_sq_of_raw_dyadic_prizeTower_one_child_quarterMGF
    (nonzeroFreqs (F := F))
    (fun b => ‖eta ψ (G ∪ dilate ζ G) b‖)
    (fun b => ‖eta ψ G b‖)
    (fun b => ‖eta ψ G (ζ * b)‖)
    shift depth hσR hcard ?_ ?_ ?_ ?_ ?_
    hMmax hn hQ hP hr hrQ hmoment
  · intro b _
    exact norm_nonneg _
  · intro b _
    exact eta_union_dilate_norm_le ψ G hζ hdisj b
  · intro b
    exact mulLeftPerm_mem_nonzeroFreqs hζ b
  · intro b _
    rfl
  · exact largeIndexChildQuarterMGF_of_nonzeroNormalizedSqResidual ψ G hMGF

end

end ArkLib.ProximityGap.Frontier.R217NonzeroDilationOneChildSqMGFEndpoint

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R217NonzeroDilationOneChildSqMGFEndpoint.mulLeftPerm_mem_nonzeroFreqs
#print axioms
  ArkLib.ProximityGap.Frontier.R217NonzeroDilationOneChildSqMGFEndpoint.largeIndexChildQuarterMGF_of_nonzeroNormalizedSqResidual
#print axioms
  ArkLib.ProximityGap.Frontier.R217NonzeroDilationOneChildSqMGFEndpoint.prize_sq_of_nonzero_dilation_one_child_sqMGFResidual
