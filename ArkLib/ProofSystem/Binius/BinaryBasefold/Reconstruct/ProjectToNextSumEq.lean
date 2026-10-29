/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Sumcheck.Structured.RoundLemmas
import ArkLib.ProofSystem.RingSwitching.Prelude

/-!
# Round-poly marginal at the verifier challenge (`projectToNextSumcheckPoly_sum_eq`)

This file supplies the single missing lemma `projectToNextSumcheckPoly_sum_eq` consumed by
`Binius.BinaryBasefold.ReductionLogic` (the `foldStep_is_logic_complete` output-relation step) and
by `Binius.RingSwitching.SumcheckPhase` / `Binius.BinaryBasefold.Steps.Fold`.

It is the *challenge-evaluation* analogue of the proven verifier-check identity
`Sumcheck.Structured.getSumcheckRoundPoly_sum_eq`: instead of summing the round univariate over the
two Boolean points `𝓑 0, 𝓑 1`, we evaluate it at the verifier's challenge `rᵢ`, and the survivor
sum is taken of the *projected next-round* polynomial `projectToNextSumcheckPoly i Hᵢ rᵢ` over the
smaller Boolean cube `(univ.map 𝓑) ^ᶠ (ℓ - i.succ)`.

The proof delegates to the canonical `sum_projectToNextSumcheckPoly_uniform` identity, whose
prefix restriction and variable-0 marginal use the same surviving coordinates.
-/

namespace Sumcheck.Structured

open OracleSpec OracleComp ProtocolSpec Finset Polynomial MvPolynomial

noncomputable section

variable {L : Type} [CommRing L] {ℓ : ℕ} [NeZero ℓ]

theorem projectToNextSumcheckPoly_sum_eq {𝓑 : Fin 2 ↪ L} (i : Fin ℓ)
    (Hᵢ : MultiquadraticPoly L (ℓ - i)) (rᵢ : L) :
    (getSumcheckRoundPoly ℓ (SumcheckDomain.uniform 𝓑 ℓ) (i := i) Hᵢ).val.eval rᵢ =
      ∑ x ∈ (Finset.univ.map 𝓑) ^ᶠ (ℓ - i.succ),
        (projectToNextSumcheckPoly (L := L) (ℓ := ℓ) (i := i) (Hᵢ := Hᵢ)
          (rᵢ := rᵢ)).val.eval x :=
  (sum_projectToNextSumcheckPoly_uniform ℓ 𝓑 i Hᵢ rᵢ).symm

end

end Sumcheck.Structured

#print axioms Sumcheck.Structured.projectToNextSumcheckPoly_sum_eq
