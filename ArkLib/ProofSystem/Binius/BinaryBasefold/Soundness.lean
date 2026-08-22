/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.Basic
import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.QueryPhasePrelims
import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.QueryPhaseFirstOracle
import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.QueryPhaseFoldBridge
import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.QueryPhaseFoldedValue
import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.QueryPhaseHelpers
import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.SuffixFiberAlignment
import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.Lift
import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.SoundnessProposition
import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.SoundnessCase1Discharge
import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.Incremental
import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.PreTensorMultilinear
import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.SoundnessCase2Assembly
import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.SoundnessCase2Probability
import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.FoldDistance
import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.BadBlocks
import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.QueryPhaseSoundness
import ArkLib.Data.Probability.PrUnionBound
import ArkLib.ToMathlib.KStateWeaken

/-!
## Re-exported Binary Basefold Soundness tools

Public entry point for the split Binary Basefold soundness development.
This module packages the central bad-sumcheck probability estimate and re-exports the semantic
soundness submodules:
1. `Soundness.QueryPhasePrelims` for query-phase helper definitions and logical/monadic
   alignment
2. `Soundness.Lift`, `Soundness.Proposition421`, `Soundness.Incremental`, and
   `Soundness.FoldDistance` for the folding and distance lemmas behind archived-DP24
   Propositions/Lemmas 4.21-4.25, with the full incremental Proposition 4.21.2 argument now
   living in `Soundness.Incremental`
3. `Soundness.BadBlocks` and `Soundness.QueryPhaseSoundness` for bad-block analysis and the
   final query-phase soundness statement

Generic block-index and oracle-index arithmetic used across these files lives upstream in
`ArkLib.ProofSystem.Binius.BinaryBasefold.Basic`.

## References

* [Diamond, B.E. and Posen, J., *Polylogarithmic proofs for multilinears over binary towers*][DP24]
  Statement numbering follows the archived revision of [DP24].
-/

namespace Binius.BinaryBasefold

open scoped NNReal ProbabilityTheory Polynomial

variable {L : Type} [Field L] [Fintype L]

/-- **Probability bound for the bad sumcheck event** (Schwartz-Zippel).
When the verifier challenge `r_i'` is uniform over `L`, the probability that two distinct
degree-≤2 round polynomials agree at `r_i'` is at most `2 / |L|`. -/
lemma probability_bound_badSumcheckEventProp (h_i h_star : L⦃≤ 2⦄[X]) :
    Pr_{ let r_i' ← $ᵖ L }[
      badSumcheckEventProp r_i' h_i h_star ] ≤
      (2 : ℝ≥0) / Fintype.card L := by
  classical
  have h_i_deg : h_i.val.natDegree ≤ 2 :=
    Polynomial.natDegree_le_of_degree_le (Polynomial.mem_degreeLE.1 h_i.property)
  have h_star_deg : h_star.val.natDegree ≤ 2 :=
    Polynomial.natDegree_le_of_degree_le (Polynomial.mem_degreeLE.1 h_star.property)
  have hmono :
      Pr_{ let r_i' ← $ᵖ L }[
        badSumcheckEventProp r_i' h_i h_star ] ≤
        Pr_{ let r_i' ← $ᵖ L }[
          KStateWeaken.badPolyAgreement r_i' h_i.val h_star.val ] :=
    PrUnion.Pr_mono ($ᵖ L)
      (fun r_i' => badSumcheckEventProp r_i' h_i h_star)
      (fun r_i' => KStateWeaken.badPolyAgreement r_i' h_i.val h_star.val)
      (by
        intro r_i' hbad
        exact ⟨fun h_eq => hbad.1 (Subtype.ext h_eq), hbad.2⟩)
  exact le_trans hmono
    (KStateWeaken.prob_badPolyAgreement_degree_two_le h_i_deg h_star_deg)

end Binius.BinaryBasefold
