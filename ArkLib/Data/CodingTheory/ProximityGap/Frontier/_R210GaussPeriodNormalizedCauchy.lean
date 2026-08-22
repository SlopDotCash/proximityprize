/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (R210 Gauss-period normalized Cauchy)
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumTowerL2
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R209DyadicCauchyNormalization

/-!
# R210 (#466): normalized Cauchy for concrete Gauss-period dilation steps

R209 isolates the real-variable normalization

```text
parent² / (2σ²) ≤ left² / σ² + right² / σ²
```

from a raw triangle bound `parent ≤ left + right`.  The dilation recursion
already proves that triangle bound for Gauss periods:

```text
‖η_{G∪ζG}(b)‖ ≤ ‖η_G(b)‖ + ‖η_G(ζb)‖.
```

This file composes the two, both for a single concrete dilation step and for
the packaged valid tower step.  No concentration estimate is hidden here; this
only converts the exact recursion into the variance-normalized squared
spectrum interface used by the MGF tower route.
-/

set_option linter.style.longLine false
set_option linter.unusedFintypeInType false

open Finset AddChar

namespace ArkLib.ProximityGap.Frontier.R210GaussPeriodNormalizedCauchy

open ArkLib.ProximityGap.Frontier.R209DyadicCauchyNormalization
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Concrete normalized-square Cauchy inequality for one Gauss-period dilation step. -/
theorem normalized_sq_eta_union_dilate_le_child_sum
    (ψ : AddChar F ℂ) (G : Finset F) {ζ : F} {σ : ℝ}
    (hζ : ζ ≠ 0) (hdisj : Disjoint G (dilate ζ G)) (hσ : 0 < σ) (b : F) :
    ‖eta ψ (G ∪ dilate ζ G) b‖ ^ 2 / (2 * σ ^ 2) ≤
      ‖eta ψ G b‖ ^ 2 / σ ^ 2 + ‖eta ψ G (ζ * b)‖ ^ 2 / σ ^ 2 := by
  exact normalized_parent_sq_le_child_sq_sum hσ (norm_nonneg _)
    (eta_union_dilate_norm_le ψ G hζ hdisj b)

/-- Finite-family form over all frequencies. -/
theorem normalized_sq_eta_union_dilate_le_child_sum_on_univ
    (ψ : AddChar F ℂ) (G : Finset F) {ζ : F} {σ : ℝ}
    (hζ : ζ ≠ 0) (hdisj : Disjoint G (dilate ζ G)) (hσ : 0 < σ) :
    ∀ b ∈ (Finset.univ : Finset F),
      ‖eta ψ (G ∪ dilate ζ G) b‖ ^ 2 / (2 * σ ^ 2) ≤
        ‖eta ψ G b‖ ^ 2 / σ ^ 2 + ‖eta ψ G (ζ * b)‖ ^ 2 / σ ^ 2 := by
  intro b _hb
  exact normalized_sq_eta_union_dilate_le_child_sum ψ G hζ hdisj hσ b

/-- Valid-tower version of the normalized-square Cauchy inequality at step `k`. -/
theorem normalized_sq_eta_towerStep_succ_le_child_sum
    (ψ : AddChar F ℂ) (G₀ : Finset F) (ζ : ℕ → F) {μ k : ℕ} {σ : ℝ}
    (hvalid : ValidTower G₀ ζ μ) (hk : k < μ) (hσ : 0 < σ) (b : F) :
    ‖eta ψ (towerStep G₀ ζ (k + 1)) b‖ ^ 2 / (2 * σ ^ 2) ≤
      ‖eta ψ (towerStep G₀ ζ k) b‖ ^ 2 / σ ^ 2 +
        ‖eta ψ (towerStep G₀ ζ k) (ζ k * b)‖ ^ 2 / σ ^ 2 := by
  simpa [towerStep_succ] using
    normalized_sq_eta_union_dilate_le_child_sum ψ (towerStep G₀ ζ k)
      (hvalid.ne_zero k hk) (hvalid.disjoint k hk) hσ b

/-- Finite-family valid-tower version over all frequencies. -/
theorem normalized_sq_eta_towerStep_succ_le_child_sum_on_univ
    (ψ : AddChar F ℂ) (G₀ : Finset F) (ζ : ℕ → F) {μ k : ℕ} {σ : ℝ}
    (hvalid : ValidTower G₀ ζ μ) (hk : k < μ) (hσ : 0 < σ) :
    ∀ b ∈ (Finset.univ : Finset F),
      ‖eta ψ (towerStep G₀ ζ (k + 1)) b‖ ^ 2 / (2 * σ ^ 2) ≤
        ‖eta ψ (towerStep G₀ ζ k) b‖ ^ 2 / σ ^ 2 +
          ‖eta ψ (towerStep G₀ ζ k) (ζ k * b)‖ ^ 2 / σ ^ 2 := by
  intro b _hb
  exact normalized_sq_eta_towerStep_succ_le_child_sum ψ G₀ ζ hvalid hk hσ b

end ArkLib.ProximityGap.Frontier.R210GaussPeriodNormalizedCauchy

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.R210GaussPeriodNormalizedCauchy.normalized_sq_eta_union_dilate_le_child_sum
#print axioms ArkLib.ProximityGap.Frontier.R210GaussPeriodNormalizedCauchy.normalized_sq_eta_union_dilate_le_child_sum_on_univ
#print axioms ArkLib.ProximityGap.Frontier.R210GaussPeriodNormalizedCauchy.normalized_sq_eta_towerStep_succ_le_child_sum
#print axioms ArkLib.ProximityGap.Frontier.R210GaussPeriodNormalizedCauchy.normalized_sq_eta_towerStep_succ_le_child_sum_on_univ
