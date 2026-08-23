/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenges

/-!
# The Grand MCA threshold is bracketed by one-sided witnesses (#232)

The positive-side resolution framework records *one-sided progress* on the Grand MCA threshold `δ*`
via `MCALowerWitness` (`ε_mca(δ) ≤ ε*` ⇒ `δ* ≥ δ`) and `MCAUpperWitness` (`ε_mca(δ) > ε*` ⇒
`δ* ≤ δ`). This file proves they genuinely squeeze any resolution's threshold:

  `delta_star_bracket` — for any `GrandMCAResolution R`, lower witness `Wl`, upper witness `Wu`:
  `Wl.δ ≤ R.δStar < Wu.δ`.

Instantiated with the from-scratch witnesses
`ProximityGap.UDRwire.rs_mcaLowerWitness_udr` (`δ ≲ (1−ρ)/3`) and
`ProximityGap.GrandChallenges.rs_mcaUpperWitness` (`δ = 1−(k+1)/n`), this pins any Reed–Solomon
resolution's threshold to the admit-free interval `(1−ρ)/3 ≲ δ* ≤ 1−(k+1)/n`. The proof uses
monotonicity of `ε_mca` in the radius (`ProximityGap.epsMCA_mono`) and the maximality clause of the
resolution. Axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #232.
-/

namespace ProximityGap.GrandChallenges

open scoped NNReal ENNReal

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **The `δ*` bracket.** Any `GrandMCAResolution`'s threshold lies between a lower witness radius
and an upper witness radius: `Wl.δ ≤ δ* < Wu.δ`. -/
theorem delta_star_bracket {C : Set (ι → F)} {ε_star : ℝ≥0}
    (R : GrandMCAResolution C ε_star) (Wl : MCALowerWitness C ε_star)
    (Wu : MCAUpperWitness C ε_star) :
    Wl.δ ≤ R.δStar ∧ R.δStar < Wu.δ := by
  refine ⟨?_, ?_⟩
  · by_contra h
    push_neg at h
    exact absurd Wl.bound (not_le.mpr (R.maximal Wl.δ h Wl.le_one))
  · by_contra h
    push_neg at h
    exact absurd Wu.exceeds
      (not_lt.mpr (le_trans (epsMCA_mono (F := F) (A := F) C h) R.bound))

#print axioms delta_star_bracket

end ProximityGap.GrandChallenges
