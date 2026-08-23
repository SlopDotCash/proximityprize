/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Security.OuterMarginalBound
import ArkLib.ProofSystem.Logup.Security.OuterRunSamplesChallenge

/-!
# LogUp outer verifier: support-level output facts (issue #13, `hsupp` verifier half)

The support-level consequences of the proven outer-verifier closed form
(`simulateQ_outerVerify_eq`), at the **plain (`toVerifier`) level** consumed by the soundness
game:

* `outer_toVerifier_verify_support` — every surviving (`some`) output of
  `(outerVerifier).toVerifier.verify (stmt, oStmt) transcript` carries
  `xChallenge = chalX transcript.challenges` (the round-1 challenge read off the transcript) and
  passes the input oracles through unchanged (`oStmtOut (.input i) = oStmt i`).

* `outer_toVerifier_accept_pins_challenge` — hence acceptance into the **sharp** protocol-level
  claim language pins the transcript's round-1 challenge into the challenge-level sharp language
  `midSoundnessLanguageSharp oStmt`.  This is exactly the verifier half of the `hsupp` side
  condition of the run-marginal capstone
  `outer_bad_accept_le_outerSoundnessError_sharp_comap`: composed with the prover-side
  transcript-extension fact (the round-1 entry of the final transcript is the round-1 challenge
  drawn during the run), it forces the drawn challenge into the sharp language on every accepting
  outcome.
-/

open OracleComp OracleSpec ProtocolSpec
open scoped ENNReal NNReal

namespace Logup

section OuterSupport

variable {ι : Type} {oSpec : OracleSpec ι}
variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)]
variable {n M : ℕ} {params : ProtocolParams M}

/-- **Support-level output facts of the compiled (plain) outer verifier.**  Every surviving
output carries the transcript's round-1 challenge in its `xChallenge` field and passes the input
oracles through unchanged. -/
theorem outer_toVerifier_verify_support
    (stmt : StmtIn F n M) (oStmt : ∀ i, OStmtIn F n M i)
    (transcript : FullTranscript (outerPSpec F n params))
    (res : StmtAfterOuter F n M params × (∀ i, OStmtAfterOuter F n M params i))
    (hres : some res ∈ support
      (((outerVerifier oSpec F n M params).toVerifier.verify
        (stmt, oStmt) transcript).run)) :
    res.1.xChallenge = chalX F n M params (transcript.challenges) ∧
      ∀ i, res.2 (.input i) = oStmt i := by
  classical
  simp only [OracleVerifier.toVerifier] at hres
  rw [simulateQ_outerVerify_eq (oSpec := oSpec) (F := F) (n := n) (M := M) (params := params) (stmt := stmt) (oStmt := oStmt) (chal := transcript.challenges) (msgs := transcript.messages)] at hres
  by_cases hacc : ∀ u : Hypercube n,
      chalX F n M params transcript.challenges + evalOnHypercube (tableOracle oStmt) u ≠ 0
  · rw [if_pos hacc] at hres
    simp only [OptionT.run_pure, pure_bind, support_pure,
      Set.mem_singleton_iff, Option.some.injEq] at hres
    subst hres
    refine ⟨rfl, fun i => ?_⟩
    rfl
  · rw [if_neg hacc] at hres
    simp only [OptionT.run_failure, failure_bind] at hres
    simp at hres

/-- **Acceptance into the sharp protocol language pins the transcript challenge.**  The verifier
half of the run-marginal `hsupp` side condition: any surviving output of the compiled outer
verifier that lands in `midSoundnessProtocolLanguageSharp` forces the transcript's round-1
challenge into the challenge-level sharp language. -/
theorem outer_toVerifier_accept_pins_challenge
    (stmt : StmtIn F n M) (oStmt : ∀ i, OStmtIn F n M i)
    (transcript : FullTranscript (outerPSpec F n params))
    (res : StmtAfterOuter F n M params × (∀ i, OStmtAfterOuter F n M params i))
    (hres : some res ∈ support
      (((outerVerifier oSpec F n M params).toVerifier.verify
        (stmt, oStmt) transcript).run))
    (hmem : res ∈ midSoundnessProtocolLanguageSharp F n M params) :
    chalX F n M params (transcript.challenges) ∈ midSoundnessLanguageSharp oStmt := by
  obtain ⟨hx, hin⟩ := outer_toVerifier_verify_support stmt oStmt transcript res hres
  rw [← hx]
  exact (mem_midSoundnessProtocolLanguageSharp_iff oStmt res.1 res.2 hin).mp hmem

end OuterSupport

end Logup

/-! ### Axiom audit (issue #13 outer verifier support facts) -/

#print axioms Logup.outer_toVerifier_verify_support
#print axioms Logup.outer_toVerifier_accept_pins_challenge
