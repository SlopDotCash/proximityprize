/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Security.MarginalBridgeProof
import ArkLib.ProofSystem.Logup.Security.RbrToSoundBridge

/-!
# Per-round plain soundness of the Simple sum-check round, error `0` (issue #13)

The keystone-free route to the LogUp embedded sum-check soundness starts here: each Simple
single-round sum-check **oracle** verifier is *plainly* sound with error `0`.

This is legitimate (not laundering) in the IOR model: the Simple oracle verifier checks the
`D`-sum of its **input** oracle statement directly against the claimed target — a claim outside
the input language is *rejected outright* (the run is `failure`), independent of the prover's
message. The familiar `deg/|R|` round error materialises only under compilation (when the oracle
is replaced by a commitment), which is outside the IOR.

Route: the proven transcript-independent knowledge state function
(`simpleKnowledgeStateFunction`, whose `toFun_full` carries the genuine rejection argument) is
weakened to a plain `StateFunction` (`KnowledgeStateFunction.toStateFunction`); its per-round flip
event is identically `False` (transcript independence), giving `rbrSoundness` with error `0`; the
proven `Verifier.marginalBridge_holds` + `rbrSoundness_imp_soundness_of_marginal` then deliver
plain soundness with error `∑ 0 = 0`.

No `sorry`; the axiom audit at the bottom must print `[propext, Classical.choice, Quot.sound]`.
-/

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal ENNReal

namespace Sumcheck.Spec.SingleRound.Simple

variable {ι : Type} (oSpec : OracleSpec ι)
variable (R : Type) [CommSemiring R] (deg : ℕ) {m : ℕ} (D : Fin m ↪ R)
  [DecidableEq R] [SampleableType R]
variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- **Round-by-round plain soundness of the Simple sum-check round with error `0`.** The plain
state function is the witness-quantified `simpleKnowledgeStateFunction` (transcript-independent:
its `toFun` is `∃ _ : Unit, (stmtIn, ()) ∈ inputRelation`), so the per-round flip event
`¬ toFun ∧ toFun` is identically `False` and every flip probability is `0`. -/
theorem oracleVerifier_rbrSoundness_zero :
    ((oracleVerifier R deg D oSpec).toVerifier).rbrSoundness init impl
      (inputRelation R deg D).language (outputRelation R deg).language (fun _ => 0) := by
  refine ⟨(simpleKnowledgeStateFunction R deg D oSpec).toStateFunction, ?_⟩
  intro stmtIn _ WitIn WitOut witIn prover i
  refine le_of_eq (probEvent_eq_zero ?_)
  rintro ⟨tr, chal⟩ - ⟨hneg, hpos⟩
  -- The state function is transcript- and round-independent; a flip is impossible.
  obtain ⟨w, hw⟩ := hpos
  exact hneg ⟨w, hw⟩

/-- **Plain soundness of the Simple sum-check round with error `0`** — the per-round input to the
keystone-free sequential-composition route. Assembled from `oracleVerifier_rbrSoundness_zero` and
the proven `Verifier.marginalBridge_holds` via `rbrSoundness_imp_soundness_of_marginal`; the
summed error is `∑ i, 0 = 0`. -/
theorem oracleVerifier_soundness_zero
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    (himplVB : ∀ (t : oSpec.Domain) (s s' : σ),
      evalDist ((impl t).run' s) = evalDist ((impl t).run' s')) :
    ((oracleVerifier R deg D oSpec).toVerifier).soundness init impl
      (inputRelation R deg D).language (outputRelation R deg).language 0 := by
  have h := Verifier.rbrSoundness_imp_soundness_of_marginal init impl
    (oracleVerifier_rbrSoundness_zero oSpec R deg D)
    (Verifier.marginalBridge_holds himplSP himplNF himplVB)
  simpa using h

end Sumcheck.Spec.SingleRound.Simple

/- Axiom audit: must be [propext, Classical.choice, Quot.sound] with NO sorryAx. -/
#print axioms Sumcheck.Spec.SingleRound.Simple.oracleVerifier_rbrSoundness_zero
#print axioms Sumcheck.Spec.SingleRound.Simple.oracleVerifier_soundness_zero
