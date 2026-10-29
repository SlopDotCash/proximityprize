/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/

import ArkLib.ProofSystem.Sumcheck.Spec.SingleRound
import Mathlib.Data.ZMod.Basic

/-!
# The canonical sumcheck verifier observes the prover's message

Over `ZMod 2`, the input polynomial is `X`, the summation domain is `{1}`, and the claimed sum is
`0`. This input claim is false. A prover message `0` passes the sum check, and at challenge `0`
the resulting output claim is true. This guards against the retired input-only rejection and
constant-knowledge arguments, without adding any alternative verifier implementation.
-/

open Polynomial OracleComp OracleSpec ProtocolSpec

namespace ArkLibTest.Compatibility.SumcheckMessageSemantics

noncomputable section

local instance : SampleableType (ZMod 2) := SampleableType.ofFintype (ZMod 2)

private def domain : Fin 1 ↪ ZMod 2 :=
  ⟨fun _ => 1, fun _ _ _ => Subsingleton.elim _ _⟩

private def inputPolynomial : (ZMod 2)⦃≤ 1⦄[X] :=
  ⟨X, by simp [mem_degreeLE]⟩

private def zeroMessage : (ZMod 2)⦃≤ 1⦄[X] :=
  ⟨0, by simp⟩

/-- The input polynomial's sum on the chosen domain is not the claimed target. -/
theorem input_claim_is_false :
    (((0, fun _ => inputPolynomial), ())) ∉
      Sumcheck.Spec.SingleRound.Simple.inputRelation (ZMod 2) 1 domain := by
  change (∑ x ∈ Finset.univ.map domain, Polynomial.eval x inputPolynomial.val) ≠ 0
  simp only [domain, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Finset.map_singleton,
    inputPolynomial, eval_X, Finset.sum_singleton, ne_eq]
  change (1 : ZMod 2) ≠ 0
  decide

/-- A message with the claimed sum is accepted even when the input claim is false. -/
theorem canonical_verifier_accepts_message :
    ((Sumcheck.Spec.SingleRound.Simple.oracleVerifier (ZMod 2) 1 domain []ₒ).toVerifier).run
        (0, fun _ => inputPolynomial)
        (FullTranscript.mk2 (pSpec := Sumcheck.Spec.SingleRound.pSpec (ZMod 2) 1)
          zeroMessage (0 : ZMod 2)) =
      pure ((0, 0), fun _ => inputPolynomial) := by
  rw [Sumcheck.Spec.SingleRound.Simple.oracleVerifier_eq_verifier]
  simp [Verifier.run, Sumcheck.Spec.SingleRound.Simple.verifier, FullTranscript.mk2,
    domain, zeroMessage]

/-- The accepted output in the preceding client satisfies the actual output relation. -/
theorem accepted_output_claim_is_true :
    ((((0, 0), fun _ => inputPolynomial), ())) ∈
      Sumcheck.Spec.SingleRound.Simple.outputRelation (ZMod 2) 1 := by
  change Polynomial.eval (0 : ZMod 2) inputPolynomial.val = 0
  simp [inputPolynomial]

#print axioms input_claim_is_false
#print axioms canonical_verifier_accepts_message
#print axioms accepted_output_claim_is_true

end

end ArkLibTest.Compatibility.SumcheckMessageSemantics
