/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Stir.RealBudgetRbr
import ArkLib.ProofSystem.Stir.InitAppendRbr

/-!
# The STIR seam composition at REAL budgets: init ++ checked final block (#301)

**The first real-budget seam composition of the STIR chain**: the unconditional append RBR
knowledge keystone (`Verifier.append_rbrKnowledgeSoundness_keystone_unconditional`,
`AppendRbrKnowledgeStateFunction.lean`) instantiated with

* `V₁` := the initial `[C_fold]` relay at the PACKED oracle format (`VOStmt`), and
* `V₂` := the CHECKED final block's verifier
  (`stirFinalVectorVerifierChecked.toVerifier`, `CheckedFinalBlock.lean`), whose RBR knowledge
  soundness at the REAL spot-check budget is the landed
  `stirFinalVectorVerifierChecked_toVerifier_rbrKnowledgeSoundness` (`RealBudgetRbr.lean`),

producing RBR knowledge soundness of the appended verifier `init ++ checkedFinal` at the
composed budget `Sum.elim 0 (C_fin ↦ stirSpotBudget) ∘ ChallengeIdx.sumEquiv.symm` — i.e.
**zero** error at the fold challenge `C_fold` and the genuine spot-check budget
`(1−δ)·|ι|·⌈|F|/|ι|⌉/|F|` at the repetition challenge `C_fin` (exactly `1−δ` in the divisible
regime `|ι| ∣ |F|`, the final corollary).

## The type bridge (why this is NOT a literal instantiation of `InitAppendRbr`)

`stirInit_append_rbrKnowledgeSoundness` (`InitAppendRbr.lean`) quantifies its tail verifier
`V₂` over the statement type `F × ∀ i, OStmt ι F i` with `OStmt ι F = fun _ => ι → F` (the
FUNCTION oracle format), while the checked final block lives at
`F × ∀ i, VOStmt ι F i` with `VOStmt ι F = fun _ => Vector F (Fintype.card ι)` (the PACKED
format of the vectorised chain) — and its proven RBR input relation is the δ-positivity gate
`stirSpotRelIn`, not the proximity relation `stirOStmtRel`.  Neither mismatch is bridgeable
in place, so this file does what `InitAppendRbr` prescribes for that case: it rebuilds the
init relay AT the packed format (`stirInitVerifierPacked`, the `VOStmt` mirror of
`stirInitVerifier` — same pure relay, same zero-error RBR proof shape, now at the gate
relations) and instantiates the keystone DIRECTLY with the two concrete verifiers.

As in `InitAppendRbr`, the keystone's single phase-2 seam-crossing leg is taken as the named
typed hypothesis `hPhase2` (`appendRbrKnowledgeSoundnessPhase2Residual`), quantified over the
destructured inner extractors / knowledge state functions — exactly the shape the keystone
consumes.  Everything else is proven.
-/

namespace StirIOP

namespace Round3

open OracleSpec OracleComp ProtocolSpec STIR ReedSolomon NNReal StirIOP.Round Verifier

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))

/-! ## Part 1 — the initial `[C_fold]` relay at the PACKED oracle format -/

/-- **The packed-format initial block verifier** (the `VOStmt` mirror of `stirInitVerifier`):
outputs the fold challenge as the statement and forwards the input PACKED oracle unchanged —
the wire format of the checked final block. -/
def stirInitVerifierPacked :
    OracleVerifier []ₒ Unit (VOStmt ι F) F (VOStmt ι F) (pSpecInit F) where
  verify := fun _ chals => pure (chals ⟨0, pSpecInit_dir_zero⟩)
  embed := ⟨fun _ => Sum.inl (), fun _ _ _ => rfl⟩
  hEq := fun _ => rfl

/-- The deterministic statement map computed by the packed init relay: read the fold
challenge off the transcript and forward the packed input oracle unchanged. -/
def stirInitVerifyPacked (stmtIn : Unit × ∀ i, VOStmt ι F i)
    (tr : (pSpecInit F).FullTranscript) : F × ∀ i, VOStmt ι F i :=
  (tr.challenges ⟨0, pSpecInit_dir_zero⟩, stmtIn.2)

/-- The packed init relay, seen as a non-oracle verifier, is the *pure* deterministic
verifier computing `stirInitVerifyPacked` — the exact `hVerify` shape consumed by the append
keystone `Verifier.append_rbrKnowledgeSoundness_keystone_unconditional`. -/
theorem stirInitVerifierPacked_toVerifier_eq :
    (stirInitVerifierPacked (ι := ι) (F := F)).toVerifier =
      ⟨fun stmtIn tr => pure (stirInitVerifyPacked stmtIn tr)⟩ := by
  unfold OracleVerifier.toVerifier stirInitVerifierPacked stirInitVerifyPacked
  congr 1

/-! ## Part 2 — the seam relations and the zero-error RBR of the packed init relay

The checked final block's PROVEN input relation (`RealBudgetRbr.lean`) is the
statement-independent δ-positivity gate `stirSpotRelIn` (see that file's HONESTY note for why
no statement-dependent relation can sit at that seam: the final block's input statement
carries no final word).  The composable input relation of the chain prefix is therefore the
same gate at the init block's input type. -/

/-- **The input relation of the composed seam**: the δ-positivity gate at the packed init
block's input statement type (the `stirSpotRelIn` mirror one seam earlier). -/
def stirSeamRelInit (ι F : Type) [Fintype ι] [Field F] [Fintype F] (δ : ℝ≥0) :
    Set ((Unit × ∀ i, VOStmt ι F i) × Unit) :=
  {_x | 0 < δ}

/-- **RBR knowledge soundness of the packed init relay, with zero error**, from the seam gate
to the checked final block's proven input gate `stirSpotRelIn`.  The verifier is a pure relay
and both relations are the statement-independent δ-positivity gate, so the constant knowledge
state function survives every round, the trivial `Unit` extractor works, and the
per-challenge error is `0` (the `stirInitVerifier_rbrKnowledgeSoundness` proof shape). -/
theorem stirInitVerifierPacked_rbrKnowledgeSoundness (δ : ℝ≥0) :
    (stirInitVerifierPacked (ι := ι) (F := F)).toVerifier.rbrKnowledgeSoundness init impl
      (stirSeamRelInit ι F δ) (stirSpotRelIn ι F δ) 0 := by
  refine ⟨fun _ => Unit, {
    eqIn := rfl
    extractMid := fun _ _ _ _ => ()
    extractOut := fun _ _ _ => ()
  }, {
    -- The knowledge state function: the δ-positivity gate (statement-independent, constant
    -- across rounds).
    toFun := fun _ stmtIn _ _ => (stmtIn, ()) ∈ stirSeamRelInit ι F δ
    toFun_empty := fun _ _ => Iff.rfl
    toFun_next := fun _ _ _ _ _ _ h => h
    toFun_full := fun stmtIn tr witOut hpr => by
      -- A positive-probability output in `stirSpotRelIn` IS the gate `0 < δ`, which is the
      -- (statement-independent) goal.
      rw [gt_iff_lt, probEvent_pos_iff] at hpr
      obtain ⟨x, _hx, hrel⟩ := hpr
      exact hrel
  }, ?_⟩
  -- Per-challenge bound: the event "state false before the challenge, true after" is
  -- pointwise contradictory (the state ignores the transcript), so its probability is 0.
  intro stmtIn witIn prover i
  refine le_trans (le_of_eq ?_) (zero_le _)
  rw [probEvent_eq_zero_iff]
  rintro ⟨transcript, challenge, log⟩ _ ⟨witMid, hnot, hyes⟩
  exact hnot hyes

/-! ## Part 3 — the generic-tail packed seam keystone (the `InitAppendRbr` mirror at the
packed format and gate relations) -/

section GenericTail

variable {n : ℕ} {pSpec₂ : ProtocolSpec n} [∀ i, SampleableType (pSpec₂.Challenge i)]
variable {Stmt₃ Wit₃ : Type}

/-- **RBR knowledge soundness of the packed STIR first seam (packed init ∘ arbitrary tail).**

The `InitAppendRbr` keystone instantiation rebuilt at the PACKED oracle format and the gate
relations: for an arbitrary tail verifier `V₂` over `F × ∀ i, VOStmt ι F i` (the checked
final block's wire format), given `V₂`'s RBR knowledge soundness from the gate `stirSpotRelIn`
(`h₂`) and the keystone's phase-2 seam residual (`hPhase2`), the appended verifier
`stirInitVerifierPacked.toVerifier.append V₂` is RBR knowledge sound from the seam gate
`stirSeamRelInit` to `rel₃`, with the tail's error reindexed (the init block contributes
**zero** error on `C_fold`). -/
theorem stirInitPacked_append_rbrKnowledgeSoundness
    (V₂ : Verifier []ₒ (F × ∀ i, VOStmt ι F i) Stmt₃ pSpec₂)
    {rel₃ : Set (Stmt₃ × Wit₃)}
    {rbrKnowledgeError₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (δ : ℝ≥0)
    (hInit : ∃ s, s ∈ support init)
    (h₂ : V₂.rbrKnowledgeSoundness init impl (stirSpotRelIn ι F δ) rel₃ rbrKnowledgeError₂)
    (hPhase2 : ∀ {WitMid₁ : Fin (1 + 1) → Type} {WitMid₂ : Fin (n + 1) → Type}
      {E₁ : Extractor.RoundByRound []ₒ (Unit × ∀ i, VOStmt ι F i) Unit Unit
        (pSpecInit F) WitMid₁}
      {E₂ : Extractor.RoundByRound []ₒ (F × ∀ i, VOStmt ι F i) Unit Wit₃ pSpec₂ WitMid₂}
      (kSF₁ : (stirInitVerifierPacked (ι := ι) (F := F)).toVerifier.KnowledgeStateFunction
        init impl (stirSeamRelInit ι F δ) (stirSpotRelIn ι F δ) E₁)
      (kSF₂ : V₂.KnowledgeStateFunction init impl (stirSpotRelIn ι F δ) rel₃ E₂),
      Verifier.appendRbrKnowledgeSoundnessPhase2Residual (init := init) (impl := impl)
        (stirInitVerifierPacked (ι := ι) (F := F)).toVerifier V₂ kSF₁ kSF₂
        stirInitVerifyPacked stirInitVerifierPacked_toVerifier_eq hInit
        (rbrKnowledgeError₂ := rbrKnowledgeError₂)) :
    @Verifier.rbrKnowledgeSoundness PEmpty.{1} []ₒ (Unit × ((i : Unit) → VOStmt ι F i)) Unit
      Stmt₃ Wit₃ (1 + n) (pSpecInit F ++ₚ pSpec₂)
      (fun i => instSampleableTypeChallengeAppend i) σ init impl
      (stirSeamRelInit ι F δ) rel₃
      ((stirInitVerifierPacked (ι := ι) (F := F)).toVerifier.append V₂)
      (Sum.elim 0 rbrKnowledgeError₂ ∘ ChallengeIdx.sumEquiv.symm) :=
  Verifier.append_rbrKnowledgeSoundness_keystone_unconditional
    (stirInitVerifierPacked (ι := ι) (F := F)).toVerifier V₂
    stirInitVerifyPacked stirInitVerifierPacked_toVerifier_eq hInit
    ⟨(0, fun _ => Vector.replicate (Fintype.card ι) 0)⟩ ⟨()⟩
    (stirInitVerifierPacked_rbrKnowledgeSoundness init impl δ)
    h₂ hPhase2

end GenericTail

/-! ## Part 4 — THE SEAM: init ++ checked final block at the REAL spot-check budget -/

open scoped Classical in
/-- **The first REAL-BUDGET SEAM COMPOSITION of the STIR chain (#301)**: the packed init
relay appended with the CHECKED final block's verifier is RBR knowledge sound at the composed
budget `Sum.elim 0 (C_fin ↦ stirSpotBudget) ∘ ChallengeIdx.sumEquiv.symm` — **zero** error at
the fold challenge `C_fold`, the genuine spot-check budget
`(1−δ)·|ι|·⌈|F|/|ι|⌉/|F|` at the repetition challenge `C_fin`.

`V₂`'s RBR leg (`h₂` of the keystone) is the LANDED
`stirFinalVectorVerifierChecked_toVerifier_rbrKnowledgeSoundness` (`RealBudgetRbr.lean`) —
no hypothesis; the phase-2 seam residual is the single named hypothesis `hPhase2`, exactly as
in `InitAppendRbr`. -/
theorem stirSeam_initPacked_append_checkedFinal_rbrKnowledgeSoundness
    (δ : ℝ≥0)
    (hInit : ∃ s, s ∈ support init)
    (hPhase2 : ∀ {WitMid₁ : Fin (1 + 1) → Type} {WitMid₂ : Fin (2 + 1) → Type}
      {E₁ : Extractor.RoundByRound []ₒ (Unit × ∀ i, VOStmt ι F i) Unit Unit
        (pSpecInit F) WitMid₁}
      {E₂ : Extractor.RoundByRound []ₒ (F × ∀ i, VOStmt ι F i) Unit Unit
        ((stirFinalVSpec ι F).toProtocolSpec F) WitMid₂}
      (kSF₁ : (stirInitVerifierPacked (ι := ι) (F := F)).toVerifier.KnowledgeStateFunction
        init impl (stirSeamRelInit ι F δ) (stirSpotRelIn ι F δ) E₁)
      (kSF₂ : (stirFinalVectorVerifierChecked (ι := ι)
          (F := F)).toVerifier.KnowledgeStateFunction
        init impl (stirSpotRelIn ι F δ)
        (Set.univ : Set ((((F × F) × ∀ i, VOStmt ι F i)) × Unit)) E₂),
      Verifier.appendRbrKnowledgeSoundnessPhase2Residual (init := init) (impl := impl)
        (stirInitVerifierPacked (ι := ι) (F := F)).toVerifier
        (stirFinalVectorVerifierChecked (ι := ι) (F := F)).toVerifier kSF₁ kSF₂
        stirInitVerifyPacked stirInitVerifierPacked_toVerifier_eq hInit
        (rbrKnowledgeError₂ := fun i =>
          if i = ⟨1, stirFinalVSpec_dir_one⟩ then stirSpotBudget ι F δ else 0)) :
    @Verifier.rbrKnowledgeSoundness PEmpty.{1} []ₒ (Unit × ((i : Unit) → VOStmt ι F i)) Unit
      ((F × F) × ∀ i, VOStmt ι F i) Unit (1 + 2)
      (pSpecInit F ++ₚ (stirFinalVSpec ι F).toProtocolSpec F)
      (fun i => instSampleableTypeChallengeAppend i) σ init impl
      (stirSeamRelInit ι F δ)
      (Set.univ : Set ((((F × F) × ∀ i, VOStmt ι F i)) × Unit))
      ((stirInitVerifierPacked (ι := ι) (F := F)).toVerifier.append
        (stirFinalVectorVerifierChecked (ι := ι) (F := F)).toVerifier)
      (Sum.elim 0
          (fun i => if i = ⟨1, stirFinalVSpec_dir_one⟩ then stirSpotBudget ι F δ else 0)
        ∘ ChallengeIdx.sumEquiv.symm) :=
  stirInitPacked_append_rbrKnowledgeSoundness init impl
    (stirFinalVectorVerifierChecked (ι := ι) (F := F)).toVerifier δ hInit
    (stirFinalVectorVerifierChecked_toVerifier_rbrKnowledgeSoundness init impl δ)
    hPhase2

open scoped Classical in
/-- **The divisible-regime seam corollary at the task's budget shape**: when `|ι| ∣ |F|`
(the spot-check index marginal is exactly uniform), the seam composition holds at the budget
`(C_fold ↦ 0, C_fin ↦ 1 − δ)` exactly. -/
theorem stirSeam_initPacked_append_checkedFinal_rbrKnowledgeSoundness_of_dvd
    (δ : ℝ≥0) (hdvd : Fintype.card ι ∣ Fintype.card F)
    (hInit : ∃ s, s ∈ support init)
    (hPhase2 : ∀ {WitMid₁ : Fin (1 + 1) → Type} {WitMid₂ : Fin (2 + 1) → Type}
      {E₁ : Extractor.RoundByRound []ₒ (Unit × ∀ i, VOStmt ι F i) Unit Unit
        (pSpecInit F) WitMid₁}
      {E₂ : Extractor.RoundByRound []ₒ (F × ∀ i, VOStmt ι F i) Unit Unit
        ((stirFinalVSpec ι F).toProtocolSpec F) WitMid₂}
      (kSF₁ : (stirInitVerifierPacked (ι := ι) (F := F)).toVerifier.KnowledgeStateFunction
        init impl (stirSeamRelInit ι F δ) (stirSpotRelIn ι F δ) E₁)
      (kSF₂ : (stirFinalVectorVerifierChecked (ι := ι)
          (F := F)).toVerifier.KnowledgeStateFunction
        init impl (stirSpotRelIn ι F δ)
        (Set.univ : Set ((((F × F) × ∀ i, VOStmt ι F i)) × Unit)) E₂),
      Verifier.appendRbrKnowledgeSoundnessPhase2Residual (init := init) (impl := impl)
        (stirInitVerifierPacked (ι := ι) (F := F)).toVerifier
        (stirFinalVectorVerifierChecked (ι := ι) (F := F)).toVerifier kSF₁ kSF₂
        stirInitVerifyPacked stirInitVerifierPacked_toVerifier_eq hInit
        (rbrKnowledgeError₂ := fun i =>
          if i = ⟨1, stirFinalVSpec_dir_one⟩ then stirSpotBudget ι F δ else 0)) :
    @Verifier.rbrKnowledgeSoundness PEmpty.{1} []ₒ (Unit × ((i : Unit) → VOStmt ι F i)) Unit
      ((F × F) × ∀ i, VOStmt ι F i) Unit (1 + 2)
      (pSpecInit F ++ₚ (stirFinalVSpec ι F).toProtocolSpec F)
      (fun i => instSampleableTypeChallengeAppend i) σ init impl
      (stirSeamRelInit ι F δ)
      (Set.univ : Set ((((F × F) × ∀ i, VOStmt ι F i)) × Unit))
      ((stirInitVerifierPacked (ι := ι) (F := F)).toVerifier.append
        (stirFinalVectorVerifierChecked (ι := ι) (F := F)).toVerifier)
      (Sum.elim 0
          (fun i => if i = ⟨1, stirFinalVSpec_dir_one⟩ then (1 - δ : ℝ≥0) else 0)
        ∘ ChallengeIdx.sumEquiv.symm) := by
  have h := stirSeam_initPacked_append_checkedFinal_rbrKnowledgeSoundness
    (ι := ι) (F := F) init impl δ hInit hPhase2
  rwa [stirSpotBudget_eq_of_dvd ι F δ hdvd] at h

end Round3

end StirIOP

/-! ## Axiom audit -/

#print axioms StirIOP.Round3.stirInitVerifierPacked_toVerifier_eq
#print axioms StirIOP.Round3.stirInitVerifierPacked_rbrKnowledgeSoundness
#print axioms StirIOP.Round3.stirInitPacked_append_rbrKnowledgeSoundness
#print axioms StirIOP.Round3.stirSeam_initPacked_append_checkedFinal_rbrKnowledgeSoundness
#print axioms StirIOP.Round3.stirSeam_initPacked_append_checkedFinal_rbrKnowledgeSoundness_of_dvd
