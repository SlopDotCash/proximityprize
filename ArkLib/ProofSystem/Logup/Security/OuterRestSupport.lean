/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.ContinueFromToSupport
import ArkLib.ProofSystem.Logup.Security.OuterVerifierSupport

/-!
# LogUp outer soundness game: the post-challenge tail pins the challenge (issue #13)

The complete `hsupp` support fact for the outer run-marginal: the tail of the outer soundness
game after the round-1 challenge (rounds 2–3 of the malicious prover, the prover's output, the
compiled verifier, and the `getM` assembly of `Reduction.run`) can only produce an output landing
in the sharp protocol claim language if the *carried* round-1 challenge already lies in the
challenge-level sharp language `midSoundnessLanguageSharp`.

This composes the two landed support bricks:
* `Prover.continueFromTo_two_last_entry_one` — rounds 2–3 preserve the round-1 entry;
* `Logup.outer_toVerifier_accept_pins_challenge` — the compiled verifier's acceptance into the
  sharp language pins the transcript's round-1 challenge;
through the `support`-level plumbing of `Reduction.run`'s tail (`liftComp`, `getM`).
-/

open OracleComp OracleSpec ProtocolSpec
open scoped ENNReal NNReal

namespace Logup

section RestSupport

variable {ι : Type} {oSpec : OracleSpec ι}
variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)]
variable {n M : ℕ} {params : ProtocolParams M}
variable {WitIn WitOut : Type}

local instance instOuterChallengeOI :
    ∀ i, OracleInterface ((outerPSpec F n params).Challenge i) :=
  ProtocolSpec.challengeOracleInterface

/-- The post-challenge tail of the outer soundness game: rounds 2–3 of the (malicious) prover,
the prover's output, the compiled outer verifier on the full transcript, and the `getM`
assembly — exactly the continuation of `(Reduction.run …).run` after the round-2 prefix. -/
noncomputable def outerRestGame
    (prover : Prover oSpec (StmtIn F n M × (∀ i, OStmtIn F n M i)) WitIn
      (StmtAfterOuter F n M params × (∀ i, OStmtAfterOuter F n M params i)) WitOut
      (outerPSpec F n params))
    (stmtIn : StmtIn F n M × (∀ i, OStmtIn F n M i)) (witIn : WitIn)
    (rk : (outerPSpec F n params).Transcript (2 : Fin 5) × prover.PrvState (2 : Fin 5)) :
    OracleComp (oSpec + [(outerPSpec F n params).Challenge]ₒ)
      (Option ((FullTranscript (outerPSpec F n params) ×
          (StmtAfterOuter F n M params × (∀ i, OStmtAfterOuter F n M params i)) × WitOut) ×
        (StmtAfterOuter F n M params × (∀ i, OStmtAfterOuter F n M params i)))) := do
  let ts ← prover.continueFromTo stmtIn witIn (2 : Fin 5) (Fin.last 4) rk
  let ctxOut ← prover.output ts.2
  let o ← (((outerVerifier oSpec F n M params).toVerifier.run stmtIn ts.1).run).liftComp
    (oSpec + [(outerPSpec F n params).Challenge]ₒ)
  match o with
  | none => pure none
  | some stmtOut => pure (some ((ts.1, ctxOut), stmtOut))

/-- **The tail pins the carried challenge (full `hsupp` support fact).**  Every surviving output
of the post-challenge tail whose verdict lands in the sharp protocol language forces the carried
round-1 challenge into the challenge-level sharp language. -/
theorem outerRestGame_pins_challenge
    (prover : Prover oSpec (StmtIn F n M × (∀ i, OStmtIn F n M i)) WitIn
      (StmtAfterOuter F n M params × (∀ i, OStmtAfterOuter F n M params i)) WitOut
      (outerPSpec F n params))
    (stmt : StmtIn F n M) (oStmt : ∀ i, OStmtIn F n M i) (witIn : WitIn)
    (rk : (outerPSpec F n params).Transcript (2 : Fin 5) × prover.PrvState (2 : Fin 5))
    (res : (FullTranscript (outerPSpec F n params) ×
        (StmtAfterOuter F n M params × (∀ i, OStmtAfterOuter F n M params i)) × WitOut) ×
      (StmtAfterOuter F n M params × (∀ i, OStmtAfterOuter F n M params i)))
    (hres : some res ∈ support (outerRestGame prover (stmt, oStmt) witIn rk))
    (hmem : res.2 ∈ midSoundnessProtocolLanguageSharp F n M params) :
    rk.1 ⟨1, by decide⟩ ∈ midSoundnessLanguageSharp oStmt := by
  classical
  unfold outerRestGame at hres
  simp only [support_bind, Set.mem_iUnion, exists_prop] at hres
  obtain ⟨ts, hts, ctxOut, -, o, ho, hres⟩ := hres
  match o with
  | none => simp at hres
  | some stmtOut =>
    simp only [support_pure, Set.mem_singleton_iff, Option.some.injEq] at hres
    subst hres
    -- the verifier stage pins the transcript's round-1 challenge
    rw [OracleComp.support_liftComp] at ho
    have hpin := outer_toVerifier_accept_pins_challenge stmt oStmt ts.1 stmtOut ho hmem
    -- the transcript's round-1 entry is the carried challenge
    have hentry := Prover.continueFromTo_two_last_entry_one prover (stmt, oStmt) witIn rk ts hts
    -- `chalX (ts.1.challenges)` is definitionally the round-1 entry of `ts.1`
    rw [← hentry]
    exact hpin

end RestSupport

end Logup

/-! ### Axiom audit -/

#print axioms Logup.outerRestGame_pins_challenge
