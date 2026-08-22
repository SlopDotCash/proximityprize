/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (R216 Gauss-period one-child square MGF)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R215OneChildDirectMGFLaw
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumDilationRecursion

/-!
# R216 (#466): concrete Gauss-period dilation endpoint for one square-MGF child

R215 proves the abstract one-child direct-MGF consumer under a permutation of
the two normalized-square child spectra.  In the concrete Gauss-period dilation
recursion the children are

```text
rawLeft  b = ‖η_G(b)‖
rawRight b = ‖η_G(ζ * b)‖
```

and multiplication by nonzero `ζ` is a permutation of the full frequency set.
This file wires that structural fact into the R215 square-normalized endpoint.
The remaining analytic input is exactly the one-child law

```text
LargeIndexChildQuarterMGFLaw univ (fun b => ‖η_G(b)‖) σ.
```
-/

open Finset AddChar
open Real
open scoped BigOperators

set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R216GaussPeriodDilationOneChildSqMGF

open ArkLib.ProximityGap.Frontier.R204PrizeTowerLargeIndex
open ArkLib.ProximityGap.Frontier.R214DirectChildMGFLaw
open ArkLib.ProximityGap.Frontier.R215OneChildDirectMGFLaw
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable section

/-- Concrete prize-square endpoint for the actual dilation-recursion parent,
using only the one-child square-normalized quarter-MGF law for `G`. -/
theorem prize_sq_of_gaussPeriod_dilation_one_child_sqMGF
    (ψ : AddChar F ℂ) (G : Finset F) {ζ : F}
    (hζ : ζ ≠ 0) (hdisj : Disjoint G (dilate ζ G))
    (depth : ℕ) {σR Mmax n Q : ℝ} {r : ℕ}
    (hσR : 0 < σR)
    (hcard : (Finset.univ : Finset F).card = DyadicTowerIndex PrizeTopIndex depth)
    (hLeft : LargeIndexChildQuarterMGFLaw
      (Finset.univ : Finset F) (fun b => ‖eta ψ G b‖) σR)
    (hMmax : 0 ≤ Mmax) (hn : 0 ≤ n) (hQ : 0 < Q)
    (hP : 0 < (Fintype.card F : ℝ))
    (hr : 1 ≤ r) (hrQ : Real.log Q ≤ r)
    (hmoment : Mmax ^ (2 * r) ≤
      Q * (n ^ r *
        ((∑ b : F, (‖eta ψ (G ∪ dilate ζ G) b‖ ^ 2 / (2 * σR ^ 2)) ^ r) /
          (Fintype.card F : ℝ)))) :
    Mmax ^ 2 ≤ 2 * Real.exp 1 * (2 / (1 / 8 : ℝ)) * n * (r : ℝ) := by
  let shift : Equiv.Perm F :=
    { toFun := fun b => ζ * b
      invFun := fun c => ζ⁻¹ * c
      left_inv := by
        intro b
        simp [hζ]
      right_inv := by
        intro c
        field_simp [hζ] }
  refine prize_sq_of_raw_dyadic_prizeTower_one_child_quarterMGF
    (Finset.univ : Finset F)
    (fun b => ‖eta ψ (G ∪ dilate ζ G) b‖)
    (fun b => ‖eta ψ G b‖)
    (fun b => ‖eta ψ G (ζ * b)‖)
    shift depth hσR hcard ?_ ?_ ?_ ?_ hLeft hMmax hn hQ ?_ hr hrQ ?_
  · intro b _
    exact norm_nonneg _
  · intro b _
    exact eta_union_dilate_norm_le ψ G hζ hdisj b
  · intro b
    simp [shift]
  · intro b _
    rfl
  · simpa using hP
  · simpa using hmoment

end

end ArkLib.ProximityGap.Frontier.R216GaussPeriodDilationOneChildSqMGF

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R216GaussPeriodDilationOneChildSqMGF.prize_sq_of_gaussPeriod_dilation_one_child_sqMGF
