/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Stir.BlockCompleteness
import ArkLib.ProofSystem.Component.SendWitness
import ArkLib.OracleReduction.Composition.Sequential.AppendRbrKnowledgeStateFunction

/-!
# STIR chain first seam: init-block RBR through the append keystone (#301)

Composes the zero-error round-by-round knowledge soundness of the initial `[C_fold]` STIR
block through the unconditional append RBR knowledge keystone
(`Verifier.append_rbrKnowledgeSoundness_keystone_unconditional`,
`AppendRbrKnowledgeStateFunction.lean`), for an **arbitrary** tail verifier over an
**arbitrary** (generic, opaque) tail protocol spec `pSpec₂`.

NOTE: `ArkLib.ProofSystem.Stir.InitRbrSoundness` has no compiled `.olean` in the current
build tree (`object file does not exist`), so its contents (the pure-verifier factoring
`stirInitVerify` / `stirInitVerifier_toVerifier_eq` and the zero-error RBR knowledge
soundness `stirInitVerifier_rbrKnowledgeSoundness`) are inlined verbatim below from
`ArkLib/ProofSystem/Stir/InitRbrSoundness.lean` (its two prerequisites, `BlockCompleteness`
and `Component.SendWitness`, are compiled and imported).

Instantiated shapes: `relIn = stirOStmtRel Unit`, `relMid = stirOStmtRel F`, `relOut`
arbitrary.  The init block supplies *both* keystone inputs for `V₁`: the pure-verifier
factoring (`hVerify`) and the zero-error RBR knowledge soundness (`h₁`); the tail's RBR
knowledge soundness is a hypothesis (`h₂`), as is the keystone's single remaining phase-2
seam residual (`hPhase2`, `appendRbrKnowledgeSoundnessPhase2Residual`, quantified over the
destructured inner extractors / knowledge state functions — exactly the shape the keystone
consumes).  The composite chain error is the tail's error reindexed
(`Sum.elim 0 rbrKnowledgeError₂ ∘ ChallengeIdx.sumEquiv.symm`): the init block contributes
**zero** error on its single challenge round.
-/

namespace StirIOP

namespace Round3

open OracleSpec OracleComp ProtocolSpec STIR ReedSolomon NNReal StirIOP.Round Verifier

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))

/-! ## Inlined from `ArkLib/ProofSystem/Stir/InitRbrSoundness.lean` (olean missing) -/

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

/-! ## The composition theorem (#301): init block ∘ arbitrary tail, through the keystone -/

variable {n : ℕ} {pSpec₂ : ProtocolSpec n} [∀ i, SampleableType (pSpec₂.Challenge i)]
variable {Stmt₃ Wit₃ : Type}

/-- **RBR knowledge soundness of the STIR chain's first seam (init block ∘ arbitrary tail).**

For an arbitrary tail verifier `V₂` over an arbitrary `pSpec₂`, given `V₂`'s RBR knowledge
soundness (`h₂`) and the keystone's phase-2 seam residual (`hPhase2`), the appended verifier
`stirInitVerifier.toVerifier.append V₂` is RBR knowledge sound from `stirOStmtRel Unit` to
`rel₃`, with the tail's error reindexed (the init block's per-round error is `0`).

This is the keystone instantiation that turns the per-block init RBR fact into a chain RBR
fact: `V₁ := stirInitVerifier.toVerifier` with its proven pure-verifier factoring
(`stirInitVerifier_toVerifier_eq`) and zero-error RBR knowledge soundness
(`stirInitVerifier_rbrKnowledgeSoundness`). -/
theorem stirInit_append_rbrKnowledgeSoundness
    (V₂ : Verifier []ₒ (F × ∀ i, OStmt ι F i) Stmt₃ pSpec₂)
    {rel₃ : Set (Stmt₃ × Wit₃)}
    {rbrKnowledgeError₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (φ : ι ↪ F) (deg : ℕ) (δ : ℝ≥0)
    (hInit : ∃ s, s ∈ support init)
    (h₂ : V₂.rbrKnowledgeSoundness init impl (stirOStmtRel F φ deg δ) rel₃ rbrKnowledgeError₂)
    (hPhase2 : ∀ {WitMid₁ : Fin (1 + 1) → Type} {WitMid₂ : Fin (n + 1) → Type}
      {E₁ : Extractor.RoundByRound []ₒ (Unit × ∀ i, OStmt ι F i) Unit Unit
        (pSpecInit F) WitMid₁}
      {E₂ : Extractor.RoundByRound []ₒ (F × ∀ i, OStmt ι F i) Unit Wit₃ pSpec₂ WitMid₂}
      (kSF₁ : (stirInitVerifier (ι := ι) (F := F)).toVerifier.KnowledgeStateFunction init impl
        (stirOStmtRel Unit φ deg δ) (stirOStmtRel F φ deg δ) E₁)
      (kSF₂ : V₂.KnowledgeStateFunction init impl (stirOStmtRel F φ deg δ) rel₃ E₂),
      Verifier.appendRbrKnowledgeSoundnessPhase2Residual (init := init) (impl := impl)
        (stirInitVerifier (ι := ι) (F := F)).toVerifier V₂ kSF₁ kSF₂
        stirInitVerify stirInitVerifier_toVerifier_eq hInit
        (rbrKnowledgeError₂ := rbrKnowledgeError₂)) :
    @Verifier.rbrKnowledgeSoundness PEmpty.{1} []ₒ (Unit × ((i : Unit) → OStmt ι F i)) Unit
      Stmt₃ Wit₃ (1 + n) (pSpecInit F ++ₚ pSpec₂)
      (fun i => instSampleableTypeChallengeAppend i) σ init impl
      (stirOStmtRel Unit φ deg δ) rel₃
      ((stirInitVerifier (ι := ι) (F := F)).toVerifier.append V₂)
      (Sum.elim 0 rbrKnowledgeError₂ ∘ ChallengeIdx.sumEquiv.symm) :=
  Verifier.append_rbrKnowledgeSoundness_keystone_unconditional
    (stirInitVerifier (ι := ι) (F := F)).toVerifier V₂
    stirInitVerify stirInitVerifier_toVerifier_eq hInit
    ⟨(0, fun _ _ => (0 : F))⟩ ⟨()⟩
    (stirInitVerifier_rbrKnowledgeSoundness init impl φ deg δ)
    h₂ hPhase2

end Round3

end StirIOP

#print axioms StirIOP.Round3.stirInitVerifier_toVerifier_eq
#print axioms StirIOP.Round3.stirInitVerifier_rbrKnowledgeSoundness
#print axioms StirIOP.Round3.stirInit_append_rbrKnowledgeSoundness
