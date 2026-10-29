/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.RingSwitching.Prelude
import ArkLib.ProofSystem.Sumcheck.Structured.RoundLemmas

/-!
# `projectToMidSumcheckPoly` at the last round — evaluation

This file supplies `Sumcheck.Structured.projectToMidSumcheckPoly_at_last_eval`, the
final-round evaluation of the projected sumcheck polynomial.

At round `i = Fin.last ℓ`, `projectToMidSumcheckPoly ℓ t m (Fin.last ℓ) challenges` is the
result of fixing **all** `ℓ` variables of the initial round polynomial `m · t` to the accumulated
challenges. The surviving variable set is `Fin (ℓ - ℓ) = Fin 0`, so the polynomial is a constant.
Evaluating it at the (only) `0`-variate point reproduces `(m · t)(challenges)`, i.e.
`m(challenges) * t(challenges)`.

This is the bridge consumed by the final-sumcheck-step completeness proofs in
`Binius.BinaryBasefold.ReductionLogic`, `Binius.RingSwitching.SumcheckPhase`, and
`Binius.FRIBinius.CoreInteractionPhase`.
-/

namespace Sumcheck.Structured

open MvPolynomial

/-- **Evaluation of `projectToMidSumcheckPoly` at the last round (`i = Fin.last ℓ`).**

The fully-projected round polynomial (all `ℓ` variables fixed to `challenges`) evaluates, at the
`0`-variate point, to the product of the multiplier and the witness multilinear, each evaluated at
the accumulated challenges. -/
theorem projectToMidSumcheckPoly_at_last_eval {L : Type} [CommRing L] (ℓ : ℕ) [NeZero ℓ]
    (t m : MultilinearPoly L ℓ) (challenges : Fin (Fin.last ℓ) → L) :
    (projectToMidSumcheckPoly ℓ t m (Fin.last ℓ) challenges).val.eval (fun _ => 0)
      = m.val.eval challenges * t.val.eval challenges := by
  change (MvPolynomial.fixPrefix ℓ (Fin.last ℓ)
    (computeInitialSumcheckPoly ℓ t m) challenges).val.eval (fun _ => 0) = _
  exact eval_fixPrefix_initial_last ℓ t m challenges (fun _ => 0)

#print axioms Sumcheck.Structured.projectToMidSumcheckPoly_at_last_eval

end Sumcheck.Structured
