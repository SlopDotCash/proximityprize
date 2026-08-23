/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Whir.MutualCorrAgreement
import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenges

/-! Reduction scaffold for the MCA Johnson conjecture (affine-line / parℓ=2 case):
the WHIR proximityCondition probability over the affine-line generator is bounded
by any `E` that bounds `epsMCA C δ`. Combined with a Johnson-radius epsMCA bound
(rs_epsMCA_johnson_range_bchks25, the GS-core result) this discharges the
affine-line instance of `hasMutualCorrAgreement` with that error function. -/

namespace MCAJohnsonReduction

noncomputable section

open MutualCorrAgreement ProbabilityTheory
open scoped NNReal ENNReal

variable {ι : Type} [Fintype ι] [Nonempty ι]
variable {F : Type} [Field F] [Fintype F]

local instance : DecidableEq F := Classical.decEq F

/-- **Affine-line MCA from an epsMCA bound.** If `epsMCA C δ ≤ E δ` for every
`δ < 1`, then the affine-line proximity-condition probability is `≤ E δ`. This is
the structural connector: it reduces the parℓ=2 MCA Johnson conjecture to a bound
on `epsMCA` at the Johnson radius (the GS-core content). -/
theorem mca_affineLine_of_epsMCA_bound
    {C : LinearCode ι F} {E : ℝ≥0 → ENNReal}
    (hbound : ∀ δ : ℝ≥0, δ < 1 → ProximityGap.epsMCA (F := F) (A := F)
      ((C : Set (ι → F))) δ ≤ E δ)
    (f : Fin 2 → ι → F) (δ : ℝ≥0) (hδ : δ < 1) :
    Pr_{
      let γ ← $ᵖ F}[proximityCondition (parℓ := Fin 2) f δ
        (fun j ↦ if j = 0 then 1 else γ) C] ≤ E δ :=
  le_trans (Pr_proximityCondition_le_epsMCA hδ f) (hbound δ hδ)

/-- **Affine-line MCA from a Grand Challenge lower witness.** A certified
`MCALowerWitness` for the ABF26 grand challenge immediately bounds WHIR's
affine-line `proximityCondition` probability at the witness radius. -/
theorem mca_affineLine_of_mcaLowerWitness
    {C : LinearCode ι F} {ε_star : ℝ≥0}
    (w : ProximityGap.GrandChallenges.MCALowerWitness
      ((C : Set (ι → F))) ε_star)
    (hδ : w.δ < 1)
    (f : Fin 2 → ι → F) :
    Pr_{
      let γ ← $ᵖ F}[proximityCondition (parℓ := Fin 2) f w.δ
        (fun j ↦ if j = 0 then 1 else γ) C] ≤ (ε_star : ENNReal) :=
  le_trans (Pr_proximityCondition_le_epsMCA hδ f) w.bound

end

end MCAJohnsonReduction
