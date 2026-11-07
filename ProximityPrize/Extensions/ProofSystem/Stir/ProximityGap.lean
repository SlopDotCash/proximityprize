/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.ProofSystem.Stir.ProximityGap

/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mirco Richter, Poulami Das (Least Authority)
-/

import ArkLib.Data.CodingTheory.Basic.DecodingRadius
import ProximityPrize.Extensions.Data.CodingTheory.Basic.Distance
import ProximityPrize.Extensions.Data.CodingTheory.Basic.LinearCode
import ProximityPrize.Extensions.Data.CodingTheory.Basic.RelativeDistance
import ProximityPrize.Extensions.Data.CodingTheory.ReedSolomon
import ProximityPrize.Extensions.Data.CodingTheory.InterleavedCode
import ArkLib.Data.Probability.Notation
import ArkLib.ProofSystem.Stir.ProximityBound

/-!
# STIR proximity gap for Reed-Solomon codes

This file states the proximity-gap theorem for Reed-Solomon codes used by STIR (Theorem 4.1),
relating the probability that a random linear combination of words is close to the code to the
existence of a common large agreement set for the individual words.

## References

* [Ben-Sasson, E., Carmon, D., Ishai, Y., Kopparty, S., and Saraf, S., *Proximity Gaps
    for Reed-Solomon Codes*][BCIKS20]
* [Arnon, G., Chiesa, A., Fenzi, G., and Yogev, E., *STIR: Reed-Solomon proximity testing
    with fewer queries*][ACFY24stir]
-/

open NNReal ProbabilityTheory ReedSolomon

namespace STIR

/-- The STIR proximity-gap front-door conclusion is exactly `Code.jointAgreement` for the
Reed-Solomon code, via the per-word `∀∃` bridge `Code.jointAgreement_iff_forall_exists`.  This
connects the bespoke STIR conclusion to the shared `jointAgreement` API (its `_mono`,
`_mono_code`, `_iff_jointProximity` lemmas), matching the FRI/WHIR proximity-gap conclusion shape.
Upstream now proves `STIR.proximity_gap`, so its conclusion is stated explicitly here rather than
using the former proposition-valued front door. The equivalence holds unconditionally. -/
theorem proximity_gap_iff_jointAgreement
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {ι : Type} [Fintype ι] [Nonempty ι] {φ : ι ↪ F}
    {degree m : ℕ} {δ : ℝ≥0} {f : Fin m → ι → F} :
    (∃ S : Finset ι, (S.card : ℝ≥0) ≥ (1 - δ) * (Fintype.card ι) ∧
      ∀ i : Fin m, ∃ u : ι → F, u ∈ code φ degree ∧ ∀ x ∈ S, f i x = u x) ↔
      Code.jointAgreement (C := (↑(code φ degree) : Set (ι → F))) (δ := δ) (W := f) := by
  rw [Code.jointAgreement_iff_forall_exists]
  simp only [SetLike.mem_coe]

end STIR

/- Axiom audit for the STIR proximity-gap residual front door (#24). -/
#print axioms STIR.proximity_gap
#print axioms STIR.proximity_gap_iff_jointAgreement
