/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Stir.BlockCompleteness
import ArkLib.ProofSystem.Component.SendWitness

/-!
# RBR knowledge soundness of the initial `[C_fold]` STIR block (#301)

First round-by-round knowledge-soundness brick for the STIR chain: the initial block
`stirInitReduction` (a pure relay verifier: it reads the standalone fold challenge off the
transcript and forwards the input oracle unchanged) satisfies `rbrKnowledgeSoundness` with
**zero** error per challenge round, against the uniform proximity relations
`stirOStmtRel Unit` / `stirOStmtRel F` of `BlockCompleteness`.

Witnesses are `Unit` throughout, so the round-by-round extractor is trivial and the knowledge
state function tracks exactly "the (statement, oracle) input pair is in the input relation".
The challenge round cannot break the state: the relation ignores the statement and the oracle
is unchanged, so the "state flips from false to true" event is pointwise contradictory and has
probability `0`.
-/

namespace StirIOP

namespace Round3

open OracleSpec OracleComp ProtocolSpec STIR ReedSolomon NNReal StirIOP.Round

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))

/-- The deterministic statement map computed by the initial block's relay verifier: read the
fold challenge off the transcript and forward the input oracle unchanged. -/
def stirInitVerify (stmtIn : Unit × ∀ i, OStmt ι F i)
    (tr : (pSpecInit F).FullTranscript) : F × ∀ i, OStmt ι F i :=
  (tr.challenges ⟨0, pSpecInit_dir_zero⟩, stmtIn.2)

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
/-- Running the initial block's (oracle) verifier deterministically returns the fold challenge
together with the unchanged input oracle. -/
theorem stirInitVerifier_toVerifier_run (u : Unit) (oStmt : ∀ i, OStmt ι F i)
    (tr : (pSpecInit F).FullTranscript) :
    (stirInitVerifier (ι := ι) (F := F)).toVerifier.run (u, oStmt) tr =
      (pure (tr.challenges ⟨0, pSpecInit_dir_zero⟩, oStmt) :
        OptionT (OracleComp []ₒ) _) := by
  simp only [Verifier.run, OracleVerifier.toVerifier, stirInitVerifier]
  erw [simulateQ_pure]
  rfl

set_option linter.unusedSectionVars false in
/-- The initial block's relay verifier, seen as a non-oracle verifier, is the *pure*
deterministic verifier computing `stirInitVerify` — the exact `hVerify` shape consumed by the
append keystone `Verifier.append_rbrKnowledgeSoundness_keystone_unconditional`. -/
theorem stirInitVerifier_toVerifier_eq :
    (stirInitVerifier (ι := ι) (F := F)).toVerifier =
      ⟨fun stmtIn tr => pure (stirInitVerify stmtIn tr)⟩ := by
  unfold OracleVerifier.toVerifier stirInitVerifier stirInitVerify
  congr 1

set_option linter.unusedSectionVars false in
/-- **RBR knowledge soundness of the initial `[C_fold]` block, with zero error.**

The verifier is a pure relay (the output statement is the fold challenge, the oracle is
forwarded unchanged), and the proximity relations `stirOStmtRel` ignore the statement; hence
the knowledge state function "the input (statement, oracle) pair is in the input relation"
survives every round, the trivial `Unit` extractor works, and the per-challenge error is `0`. -/
theorem stirInitVerifier_rbrKnowledgeSoundness (φ : ι ↪ F) (deg : ℕ) (δ : ℝ≥0) :
    (stirInitVerifier (ι := ι) (F := F)).rbrKnowledgeSoundness init impl
      (stirOStmtRel Unit φ deg δ) (stirOStmtRel F φ deg δ) 0 := by
  simp only [OracleVerifier.rbrKnowledgeSoundness]
  refine ⟨fun _ => Unit, {
    eqIn := rfl
    extractMid := fun _ _ _ _ => ()
    extractOut := fun _ _ _ => ()
  }, {
    -- The knowledge state function: the input (statement, oracle) pair is in the input
    -- relation. It ignores the round, the transcript, and the (trivial) witness.
    toFun := fun _ stmtIn _ _ => (stmtIn, ()) ∈ stirOStmtRel Unit φ deg δ
    toFun_empty := fun _ _ => Iff.rfl
    -- The state is constant across rounds, so any extension preserves it.
    toFun_next := fun _ _ _ _ _ _ h => h
    toFun_full := fun stmtIn tr witOut hpr => by
      -- The verifier deterministically outputs (challenge, input oracle); a
      -- positive-probability output in `stirOStmtRel F` therefore witnesses that the *input*
      -- oracle is `δ`-close to the code, which is the goal.
      obtain ⟨u, oStmt⟩ := stmtIn
      rw [gt_iff_lt, probEvent_pos_iff] at hpr
      obtain ⟨x, hx, hrel⟩ := hpr
      rw [OptionT.mem_support_iff] at hx
      simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hx
      obtain ⟨s, _, hx⟩ := hx
      erw [stirInitVerifier_toVerifier_run, simulateQ_optionT_pure_run'] at hx
      cases (Option.some.inj hx)
      exact hrel
  }, ?_⟩
  -- Per-challenge bound: the event "state false before the challenge, true after" is
  -- pointwise contradictory (the state ignores the transcript), so its probability is 0.
  intro stmtIn witIn prover i
  refine le_trans (le_of_eq ?_) (zero_le _)
  rw [probEvent_eq_zero_iff]
  rintro ⟨transcript, challenge, log⟩ _ ⟨witMid, hnot, hyes⟩
  exact hnot hyes

set_option linter.unusedSectionVars false in
/-- RBR knowledge soundness of the initial block, phrased on `stirInitReduction`'s verifier. -/
theorem stirInitReduction_rbrKnowledgeSoundness (φ : ι ↪ F) (deg : ℕ) (δ : ℝ≥0) :
    (stirInitReduction (ι := ι) (F := F)).verifier.rbrKnowledgeSoundness init impl
      (stirOStmtRel Unit φ deg δ) (stirOStmtRel F φ deg δ) 0 :=
  stirInitVerifier_rbrKnowledgeSoundness init impl φ deg δ

end Round3

end StirIOP

#print axioms StirIOP.Round3.stirInitVerifier_toVerifier_run
#print axioms StirIOP.Round3.stirInitVerifier_toVerifier_eq
#print axioms StirIOP.Round3.stirInitVerifier_rbrKnowledgeSoundness
#print axioms StirIOP.Round3.stirInitReduction_rbrKnowledgeSoundness
