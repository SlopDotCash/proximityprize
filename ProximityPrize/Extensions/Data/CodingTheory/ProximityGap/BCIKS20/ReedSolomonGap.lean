/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ReedSolomonGap

/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Katerina Hristova, František Silváši, Julian Sutherland,
         Ilia Vlasov, Chung Thai Nguyen
-/

import ProximityPrize.Extensions.Data.CodingTheory.ProximityGap.BCIKS20.AffineSpaces
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ErrorBound
import ArkLib.Data.Probability.Notation

/-! # BCIKS20 Reed-Solomon Proximity Gaps -/

namespace ProximityGap

open NNReal Finset Function ProbabilityTheory Code
open scoped BigOperators LinearCode ProbabilityTheory

section CoreResults

variable {ι : Type} [Fintype ι] [Nonempty ι]
         {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Theorem 1.2 front door with the affine-line Johnson residual supplied by the verified
`betaRec` capsule at every radius `δ' ≤ δ` needed by the affine-space argument. -/
theorem proximity_gap_RSCodes_johnson_of_betaRec [SampleableType F] {k t : ℕ} [NeZero k] [NeZero t]
    {deg : ℕ} {domain : ι ↪ F}
    (hdeg : 0 < deg)
    (hRS : deg + 1 ≤ Fintype.card ι)
    (C : Fin t → (Fin k → (ι → F))) {δ : ℝ≥0}
    (hδ_pos : 0 < δ)
    (hInput : ∀ δ' : ℝ≥0, δ' ≤ δ →
      ∀ (_hk : 0 < 1) (u : WordStack F (Fin 2) ι),
        Pr_{
          let z ← $ᵖ F}[δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u t,
            ReedSolomon.code domain deg) ≤ δ'] >
            (((1 : ℕ) : ENNReal) * (errorBound δ' deg domain : ENNReal)) →
        (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ' →
        δ' < 1 - ReedSolomon.sqrtRate deg domain →
        ArkLib.KeystoneStrictResidual.BetaCurveInput
          (k := 1) (deg := deg) (domain := domain) (δ := δ') u)
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain)
    (hε : errorBound δ deg domain < 1) :
    δ_ε_proximityGap
      (ReedSolomon.toFinset domain deg)
      (Affine.AffSpanFinsetCollection C)
      δ
      (errorBound δ deg domain) :=
  -- The canonical theorem is stronger; the retained legacy hInput is unused.
  proximity_gap_RSCodes (ι := ι) (F := F) (k := k) (t := t) (deg := deg)
    (domain := domain) hdeg hRS C hδ_pos
    hδ hε

end CoreResults

end ProximityGap

#print axioms ProximityGap.proximity_gap_RSCodes_johnson_of_betaRec
