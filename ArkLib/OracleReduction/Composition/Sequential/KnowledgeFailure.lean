/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.Composition.Sequential.AppendRbrKnowledgeOracleLift
import ArkLib.OracleReduction.Composition.Sequential.AppendRbrKnowledgeChallenge
import ArkLib.OracleReduction.Composition.Sequential.AppendRbrKnowledgeEmpty

/-!
# Sequential knowledge soundness with deterministic failure

Reduction to total determinism and knowledge-soundness composition across challenge and empty seams.
-/

section AppendRbrKnowledgeFailingDet

/-!
## Reduction from failing to total determinism.
-/

/-!
# The optionization reduction: failing-deterministic seams reduce to total-deterministic ones

The rbr (knowledge) soundness append keystone takes a *total* determinism witness
`hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩`. RingSwitching's sumcheck-side verifiers are
**failing**-deterministic (`else failure`), so that witness is unavailable for the
`coreInteraction`/`full` seams.

This file implements the **optionization reduction** (issue #29): a failing-deterministic left
verifier `⟨fun s t => OptionT.mk (pure (verify? s t))⟩` (with `verify? : Stmt₁ → FullTranscript →
Option Stmt₂`) factors through the *total*-deterministic verifier over the optionized intermediate
statement `Option Stmt₂`, with the right phase lifted by `Verifier.optionLift` (fail on `none`,
defer on `some`). The appended verifiers are **equal** (`append_failingDet_eq_optionized`), so the
existing total-det keystone applies at the intermediate type `Option Stmt₂` — no re-threading of the
state-function chain, no protocol change.
-/

open OracleComp OracleSpec ProtocolSpec
open scoped ENNReal NNReal

universe u

namespace Verifier

variable {ι : Type} {oSpec : OracleSpec ι} {Stmt₁ Stmt₂ Stmt₃ : Type}
    {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

/-- **Option-lift of a verifier.** Runs `V` on `some` inputs and fails on `none` — the right-phase
companion of the optionization reduction: a failing-deterministic left phase hands `V₂.optionLift`
its (possibly absent) intermediate statement. -/
def optionLift (V : Verifier oSpec Stmt₂ Stmt₃ pSpec₂) :
    Verifier oSpec (Option Stmt₂) Stmt₃ pSpec₂ :=
  ⟨fun s? tr => match s? with
    | none => failure
    | some s => V.verify s tr⟩

@[simp] theorem optionLift_verify_some (V : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (s : Stmt₂) (tr : pSpec₂.FullTranscript) :
    (V.optionLift).verify (some s) tr = V.verify s tr := rfl

@[simp] theorem optionLift_verify_none (V : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (tr : pSpec₂.FullTranscript) :
    (V.optionLift).verify (none : Option Stmt₂) tr = failure := rfl

/-- **The optionization seam-rewrite.** Appending a *failing*-deterministic left verifier to `V₂`
equals appending its *total*-deterministic optionization (the same `verify?`, now as an honest
output statement) to `V₂.optionLift`. This rewrites a failing-det seam into a total-det seam over
the intermediate type `Option Stmt₂`, where the rbr (knowledge) soundness append keystone's
`hVerify` is available. -/
theorem append_failingDet_eq_optionized
    (verify? : Stmt₁ → pSpec₁.FullTranscript → Option Stmt₂)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂) :
    Verifier.append (⟨fun s tr => OptionT.mk (pure (verify? s tr))⟩ :
        Verifier oSpec Stmt₁ Stmt₂ pSpec₁) V₂
      = Verifier.append (⟨fun s tr => pure (verify? s tr)⟩ :
          Verifier oSpec Stmt₁ (Option Stmt₂) pSpec₁) V₂.optionLift := by
  unfold Verifier.append
  congr 1
  funext s tr
  refine OptionT.ext ?_
  simp only [OptionT.run_bind, OptionT.run_mk, OptionT.run_pure, Option.elimM, pure_bind]
  cases h : verify? s tr.fst with
  | none => simp [optionLift]
  | some s₂ => simp [optionLift]

/-- The optionized intermediate relation: `(s?, w)` is related iff `s?` is `some s` with `(s, w)`
in the underlying relation. The `none` (failed-crossing) statement is related to nothing — it is
*doomed*, which is what makes the `optionLift` transports sound. -/
def optionRel {Stmt₂ Wit₂ : Type} (r : Set (Stmt₂ × Wit₂)) : Set (Option Stmt₂ × Wit₂) :=
  {p | ∃ s, p.1 = some s ∧ (s, p.2) ∈ r}

@[simp] theorem mem_optionRel_some {Stmt₂ Wit₂ : Type} {r : Set (Stmt₂ × Wit₂)}
    {s : Stmt₂} {w : Wit₂} : ((some s, w) ∈ optionRel r) ↔ (s, w) ∈ r := by
  simp [optionRel]

@[simp] theorem not_mem_optionRel_none {Stmt₂ Wit₂ : Type} {r : Set (Stmt₂ × Wit₂)}
    {w : Wit₂} : ((none, w) ∈ optionRel r) ↔ False := by
  simp [optionRel]

variable {Wit₂ Wit₃ : Type} {σ : Type} {init : ProbComp σ}
    {impl : QueryImpl oSpec (StateT σ ProbComp)}
    [∀ i, SampleableType (pSpec₂.Challenge i)]

/-- **Statement-precomposition of a prover.** Reindexes a prover over `Option Stmt₂`-statements to a
prover over `Stmt₂` by wrapping the input statement in `some`; all rounds and the output are
untouched, so all partial runs agree definitionally. -/
def _root_.Prover.someStmt {Stmt₃' Wit₃' : Type}
    (P : Prover oSpec (Option Stmt₂) Wit₂ Stmt₃' Wit₃' pSpec₂) :
    Prover oSpec Stmt₂ Wit₂ Stmt₃' Wit₃' pSpec₂ where
  PrvState := P.PrvState
  input := fun ctx => P.input (some ctx.1, ctx.2)
  sendMessage := P.sendMessage
  receiveChallenge := P.receiveChallenge
  output := P.output

@[simp] theorem _root_.Prover.someStmt_runWithLogToRound {Stmt₃' Wit₃' : Type}
    (P : Prover oSpec (Option Stmt₂) Wit₂ Stmt₃' Wit₃' pSpec₂)
    (i : Fin (n + 1)) (s : Stmt₂) (w : Wit₂) :
    (P.someStmt).runWithLogToRound i s w = P.runWithLogToRound i (some s) w := rfl

/-- **`optionLift` preserves round-by-round knowledge soundness** (with the optionized input
relation). The knowledge state function sends `none`-statement states to `False` (the failed
crossing is doomed); the extractor reads the `some`-component (with an `Inhabited` default on the
irrelevant `none` leg); the per-round bound at a `none` statement is the probability of an
event with a `False` conjunct, and at `some s` defers to the inner bound via statement
precomposition. -/
theorem optionLift_rbrKnowledgeSoundness [Inhabited Stmt₂]
    (V : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}
    {err : pSpec₂.ChallengeIdx → ℝ≥0}
    (h : V.rbrKnowledgeSoundness init impl rel₂ rel₃ err) :
    (V.optionLift).rbrKnowledgeSoundness init impl (optionRel rel₂) rel₃ err := by
  obtain ⟨WitMid, E, kSF, hBound⟩ := h
  refine ⟨WitMid,
    { eqIn := E.eqIn
      extractMid := fun m s? tr w => E.extractMid m (s?.getD default) tr w
      extractOut := fun s? tr w => E.extractOut (s?.getD default) tr w },
    { toFun := fun m s? tr w => match s? with
        | some s => kSF.toFun m s tr w
        | none => False
      toFun_empty := fun s? w => by
        cases s? with
        | some s => simpa using kSF.toFun_empty s w
        | none => simp
      toFun_next := fun m hDir s? tr msg w hnext => by
        cases s? with
        | some s => exact kSF.toFun_next m hDir s tr msg w hnext
        | none => exact hnext.elim
      toFun_full := fun s? tr w hPos => by
        cases s? with
        | some s => exact kSF.toFun_full s tr w hPos
        | none =>
          -- `optionLift.run none = failure`: the run always yields `none`, so the acceptance
          -- probability is `0`, contradicting `hPos`.
          exfalso
          rw [gt_iff_lt, probEvent_pos_iff] at hPos
          obtain ⟨x, hx, -⟩ := hPos
          rw [OptionT.mem_support_iff] at hx
          simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hx
          obtain ⟨s, -, hmem⟩ := hx
          -- the simulated `failure` run is definitionally the constant-`none` computation
          rw [show ((simulateQ impl ((V.optionLift).run (none : Option Stmt₂) tr)).run' s :
                ProbComp (Option Stmt₃))
              = pure none from rfl] at hmem
          simp at hmem },
    ?_⟩
  intro s? w P i
  cases s? with
  | none =>
    -- the flip event's second conjunct is `False` at a `none` statement: probability `0`.
    refine le_trans (le_of_eq (probEvent_eq_zero ?_)) (zero_le _)
    rintro ⟨tr, ch, log⟩ _
    rintro ⟨wm, -, hsucc⟩
    exact hsucc
  | some s =>
    -- precompose the prover and defer to the inner per-round bound at `s`.
    simpa using hBound s w P.someStmt i

/-- **Output-statement adaptation of a prover.** Replaces the prover's output statement type
(discarding the statement to `default`); the interaction rounds are untouched, so all partial runs
agree definitionally. The rbr per-round flip events never read the prover's output, so this is a
free adaptation for the per-round bounds. -/
def _root_.Prover.defaultOutputStmt {Stmt₁ Wit₁ StmtA StmtB Wit' : Type} [Inhabited StmtB]
    (P : Prover oSpec Stmt₁ Wit₁ StmtA Wit' pSpec₁) :
    Prover oSpec Stmt₁ Wit₁ StmtB Wit' pSpec₁ where
  PrvState := P.PrvState
  input := P.input
  sendMessage := P.sendMessage
  receiveChallenge := P.receiveChallenge
  output := fun st => (fun ow => (default, ow.2)) <$> P.output st

@[simp] theorem _root_.Prover.defaultOutputStmt_runWithLogToRound
    {Stmt₁ Wit₁ StmtA StmtB Wit' : Type} [Inhabited StmtB]
    (P : Prover oSpec Stmt₁ Wit₁ StmtA Wit' pSpec₁)
    (i : Fin (m + 1)) (s : Stmt₁) (w : Wit₁) :
    (P.defaultOutputStmt (StmtB := StmtB)).runWithLogToRound i s w
      = P.runWithLogToRound i s w := rfl

/-- **The h₁ transport of the optionization reduction.** A *failing*-deterministic verifier's rbr
knowledge soundness transfers to its *total*-deterministic optionization (output statement
`Option Stmt₂`, relation `optionRel rel₂`): the knowledge state function and extractor are
unchanged (they are input-statement-indexed), `toFun_full` transfers because the two runs hit
their respective output relations with the same probability (`verify? = some s₂ ∧ (s₂, w) ∈ rel₂`
in both cases), and the per-round bounds transfer by output-statement adaptation of the prover. -/
theorem failingDet_optionized_rbrKnowledgeSoundness [Inhabited Stmt₂]
    {Wit₁ : Type}
    (verify? : Stmt₁ → pSpec₁.FullTranscript → Option Stmt₂)
    {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)}
    {err₁ : pSpec₁.ChallengeIdx → ℝ≥0}
    [∀ i, SampleableType (pSpec₁.Challenge i)]
    (h₁ : Verifier.rbrKnowledgeSoundness init impl rel₁ rel₂
      (⟨fun s tr => OptionT.mk (pure (verify? s tr))⟩ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) err₁) :
    Verifier.rbrKnowledgeSoundness init impl rel₁ (optionRel rel₂)
      (⟨fun s tr => pure (verify? s tr)⟩ : Verifier oSpec Stmt₁ (Option Stmt₂) pSpec₁) err₁ := by
  obtain ⟨WitMid, E, kSF, hBound⟩ := h₁
  refine ⟨WitMid, E,
    { toFun := kSF.toFun
      toFun_empty := kSF.toFun_empty
      toFun_next := kSF.toFun_next
      toFun_full := fun s tr w hPos => by
        refine kSF.toFun_full s tr w ?_
        -- positivity transfers: both runs hit their output relations exactly when
        -- `verify? s tr = some s₂` with `(s₂, w) ∈ rel₂`.
        rw [gt_iff_lt, probEvent_pos_iff] at hPos ⊢
        obtain ⟨x?, hx, hrel⟩ := hPos
        obtain ⟨s₂, hsome, hs₂⟩ := hrel
        -- the total run always outputs `verify? s tr`; membership pins `x? = verify? s tr`.
        rw [OptionT.mem_support_iff] at hx
        simp only [Verifier.run, OptionT.run_mk, support_bind, Set.mem_iUnion] at hx
        obtain ⟨st, hst, hmem⟩ := hx
        rw [show ((simulateQ impl
              ((⟨fun s tr => pure (verify? s tr)⟩ :
                Verifier oSpec Stmt₁ (Option Stmt₂) pSpec₁).run s tr)).run' st :
              ProbComp (Option (Option Stmt₂)))
            = pure (some (verify? s tr)) from rfl] at hmem
        simp only [support_pure, Set.mem_singleton_iff, Option.some.injEq] at hmem
        subst hmem
        -- now exhibit `s₂` in the failing run's support
        refine ⟨s₂, ?_, hs₂⟩
        rw [OptionT.mem_support_iff]
        simp only [Verifier.run, OptionT.run_mk, support_bind, Set.mem_iUnion]
        refine ⟨st, hst, ?_⟩
        rw [show ((simulateQ impl
              ((⟨fun s tr => OptionT.mk (pure (verify? s tr))⟩ :
                Verifier oSpec Stmt₁ Stmt₂ pSpec₁).run s tr)).run' st :
              ProbComp (Option Stmt₂))
            = pure (verify? s tr) from rfl]
        simp only [support_pure, Set.mem_singleton_iff]
        first | exact hsome.symm | exact hsome },
    ?_⟩
  intro s w P i
  simpa using hBound s w (P.defaultOutputStmt (StmtB := Stmt₂)) i

/-- **The failing-deterministic rbr knowledge-soundness append keystone (`Subsingleton σ`,
message seam).** The capstone of the optionization reduction: appending a *failing*-deterministic
left verifier (the shape of the RingSwitching round/finalSumcheck verifiers, `else failure`) to
`V₂` is round-by-round knowledge sound with the additive `Sum.elim` error — **no residual
hypotheses** beyond the per-phase bounds, the failing-determinism shape itself, and the stateless
regime's side conditions.

Proof: rewrite the seam by `append_failingDet_eq_optionized` into the total-deterministic seam over
`Option Stmt₂` (where the determinism witness is `rfl` and `Nonempty (Option Stmt₂)` is free via
`none`), transport `h₁`/`h₂` by `failingDet_optionized_rbrKnowledgeSoundness` /
`optionLift_rbrKnowledgeSoundness`, and apply the unconditional total-deterministic keystone. -/
theorem append_rbrKnowledgeSoundness_failingDet_subsingleton
    [Subsingleton σ] [Inhabited Stmt₂]
    {Stmt₃ Wit₁ Wit₃ : Type} {n : ℕ} {pSpec₂ : ProtocolSpec n}
    [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
    (verify? : Stmt₁ → pSpec₁.FullTranscript → Option Stmt₂)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}
    {err₁ : pSpec₁.ChallengeIdx → ℝ≥0} {err₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (hInit : ∃ s, s ∈ support init) (hInitNF : Pr[⊥ | init] = 0)
    (hNEW₂ : Nonempty Wit₂)
    (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .P_to_V)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .P_to_V)
    (h₁ : Verifier.rbrKnowledgeSoundness init impl rel₁ rel₂
      (⟨fun s tr => OptionT.mk (pure (verify? s tr))⟩ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) err₁)
    (h₂ : V₂.rbrKnowledgeSoundness init impl rel₂ rel₃ err₂) :
    (Verifier.append
        (⟨fun s tr => OptionT.mk (pure (verify? s tr))⟩ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
        V₂).rbrKnowledgeSoundness init impl rel₁ rel₃
      (Sum.elim err₁ err₂ ∘ ChallengeIdx.sumEquiv.symm) := by
  rw [append_failingDet_eq_optionized]
  exact append_rbrKnowledgeSoundness_keystone_subsingleton_unconditional
    (⟨fun s tr => pure (verify? s tr)⟩ : Verifier oSpec Stmt₁ (Option Stmt₂) pSpec₁)
    V₂.optionLift verify? rfl hInit hInitNF ⟨none⟩ hNEW₂ hn hDir hDir₂
    (failingDet_optionized_rbrKnowledgeSoundness verify? h₁)
    (optionLift_rbrKnowledgeSoundness V₂ h₂)

section Composition

variable {Stmt₃ : Type} {n : ℕ} {pSpec₂ : ProtocolSpec n}

/-- **Failing-deterministic verifiers compose.** The append of two failing-deterministic verifiers
is failing-deterministic, with the composed partial verdict given by `Option.bind`: run `v₁?` on the
first half; on success feed the intermediate statement to `v₂?` on the second half. Together with
`append_pure_pure` (and the mixed variants below) this builds the failing-determinism witnesses for
all *composite* RingSwitching verifiers (`sumcheckLoop`, `coreInteraction`, `batchingCore`). -/
theorem append_failingDet_failingDet
    (v₁? : Stmt₁ → pSpec₁.FullTranscript → Option Stmt₂)
    (v₂? : Stmt₂ → pSpec₂.FullTranscript → Option Stmt₃) :
    Verifier.append
        (⟨fun s tr => OptionT.mk (pure (v₁? s tr))⟩ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
        (⟨fun s tr => OptionT.mk (pure (v₂? s tr))⟩ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
      = ⟨fun s tr => OptionT.mk (pure ((v₁? s tr.fst).bind (fun s₂ => v₂? s₂ tr.snd)))⟩ := by
  unfold Verifier.append
  congr 1
  funext s tr
  refine OptionT.ext ?_
  simp only [OptionT.run_bind, OptionT.run_mk, Option.elimM, pure_bind]
  cases h : v₁? s tr.fst with
  | none => simp
  | some s₂ => simpa using (by cases h₂ : v₂? s₂ tr.snd <;> rfl :
      ((v₂? s₂ tr.snd).elim (pure none) fun x => pure (some x) :
        OracleComp oSpec (Option Stmt₃)) = pure (v₂? s₂ tr.snd))

/-- **Total-deterministic left, failing-deterministic right.** The mixed composition: a total left
verdict feeds the failing right verdict directly. (The RingSwitching `batchingCore` seam: batching
is total, `coreInteraction` fails.) -/
theorem append_pure_failingDet
    (v₁ : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (v₂? : Stmt₂ → pSpec₂.FullTranscript → Option Stmt₃) :
    Verifier.append
        (⟨fun s tr => pure (v₁ s tr)⟩ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
        (⟨fun s tr => OptionT.mk (pure (v₂? s tr))⟩ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
      = ⟨fun s tr => OptionT.mk (pure (v₂? (v₁ s tr.fst) tr.snd))⟩ := by
  unfold Verifier.append
  congr 1
  funext s tr
  refine OptionT.ext ?_
  simp only [OptionT.run_bind, OptionT.run_pure, OptionT.run_mk, Option.elimM, pure_bind,
    Option.elim_some]
  cases h : v₂? (v₁ s tr.fst) tr.snd <;> simp

/-- **Failing-deterministic left, total-deterministic right.** -/
theorem append_failingDet_pure
    (v₁? : Stmt₁ → pSpec₁.FullTranscript → Option Stmt₂)
    (v₂ : Stmt₂ → pSpec₂.FullTranscript → Stmt₃) :
    Verifier.append
        (⟨fun s tr => OptionT.mk (pure (v₁? s tr))⟩ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
        (⟨fun s tr => pure (v₂ s tr)⟩ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
      = ⟨fun s tr => OptionT.mk (pure ((v₁? s tr.fst).map (fun s₂ => v₂ s₂ tr.snd)))⟩ := by
  unfold Verifier.append
  congr 1
  funext s tr
  refine OptionT.ext ?_
  simp only [OptionT.run_bind, OptionT.run_mk, Option.elimM, pure_bind]
  cases h : v₁? s tr.fst <;> simp

end Composition

end Verifier

namespace OracleVerifier

variable {ι : Type} {oSpec : OracleSpec ι}

/-- **Failing-determinism witness from an `Option`-valued `simulateQ` collapse.** The failing
analogue of `toVerifier_eq_pure_of_collapse`: if an oracle verifier's `verify`, simulated against
the transcript-message oracle, collapses to `OptionT.mk (pure (v? (stmt, oStmt) tr))` (the shape of
the RingSwitching round/finalSumcheck `*_verify_collapse` lemmas, with `v? = if check then some …
else none`), then its compiled `toVerifier` is failing-deterministic with the `Option.map`-ped
verdict (the deterministic `oStmtOut` routing rides along on success). -/
theorem toVerifier_eq_failingDet_of_collapse
    {ιₛᵢ ιₛₒ : Type} {StmtIn StmtOut : Type}
    {OStmtIn : ιₛᵢ → Type} [Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)]
    {OStmtOut : ιₛₒ → Type}
    {n' : ℕ} {pSpec : ProtocolSpec n'} [Oₘ : ∀ i, OracleInterface (pSpec.Message i)]
    (V : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec)
    (v? : (StmtIn × ∀ i, OStmtIn i) → pSpec.FullTranscript → Option StmtOut)
    (hcollapse : ∀ (stmt : StmtIn) (oStmt : ∀ i, OStmtIn i) (tr : pSpec.FullTranscript),
      simulateQ (OracleInterface.simOracle2 oSpec oStmt tr.messages)
          (V.verify stmt tr.challenges)
        = (OptionT.mk (pure (v? (stmt, oStmt) tr)) : OptionT (OracleComp oSpec) StmtOut)) :
    V.toVerifier = ⟨fun p tr => OptionT.mk (pure ((v? p tr).map (fun s => (s,
      fun i => match h : V.embed i with
        | Sum.inl j => (V.hEq i ▸ h ▸ p.2 j : OStmtOut i)
        | Sum.inr j => (V.hEq i ▸ h ▸ tr.messages j : OStmtOut i)))))⟩ := by
  unfold OracleVerifier.toVerifier
  congr 1
  funext p tr
  obtain ⟨stmt, oStmt⟩ := p
  simp only [hcollapse stmt oStmt tr]
  refine OptionT.ext ?_
  simp only [OptionT.run_bind, OptionT.run_mk, Option.elimM, pure_bind]
  cases h : v? (stmt, oStmt) tr <;> simp <;> rfl

variable {Stmt₁ : Type} {ιₛ₁ : Type} {OStmt₁ : ιₛ₁ → Type}
    [Oₛ₁ : ∀ i, OracleInterface (OStmt₁ i)]
    {Wit₁ : Type}
    {Stmt₂ : Type} {ιₛ₂ : Type} {OStmt₂ : ιₛ₂ → Type}
    [Oₛ₂ : ∀ i, OracleInterface (OStmt₂ i)]
    {Wit₂ : Type}
    {Stmt₃ : Type} {ιₛ₃ : Type} {OStmt₃ : ιₛ₃ → Type}
    [Oₛ₃ : ∀ i, OracleInterface (OStmt₃ i)]
    {Wit₃ : Type}
    {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
    [Oₘ₁ : ∀ i, OracleInterface (pSpec₁.Message i)]
    [Oₘ₂ : ∀ i, OracleInterface (pSpec₂.Message i)]
    [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel₁ : Set ((Stmt₁ × ∀ i, OStmt₁ i) × Wit₁)}
    {rel₂ : Set ((Stmt₂ × ∀ i, OStmt₂ i) × Wit₂)}
    {rel₃ : Set ((Stmt₃ × ∀ i, OStmt₃ i) × Wit₃)}

/-- **OracleVerifier-level failing-deterministic rbr knowledge-soundness append keystone
(`Subsingleton σ`, message seam).** The OracleVerifier companion of
`Verifier.append_rbrKnowledgeSoundness_failingDet_subsingleton`: discharges the
`OracleVerifier.appendRbrKnowledgeSoundnessResidual` for seams whose left verifier compiles to a
*failing*-deterministic `toVerifier` (the RingSwitching sumcheck-side shape, witnesses supplied by
`toVerifier_eq_failingDet_of_collapse` + the composition combinators). One-shot from
`oracleVerifier_append_toVerifier` + the Protocol-level failing-det capstone. -/
theorem append_rbrKnowledgeSoundness_failingDet_subsingleton
    [Subsingleton σ] [Inhabited (Stmt₂ × ∀ i, OStmt₂ i)]
    (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    [OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) V₁]
    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂)
    {rbrKnowledgeError₁ : pSpec₁.ChallengeIdx → ℝ≥0}
    {rbrKnowledgeError₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (verify? : (Stmt₁ × ∀ i, OStmt₁ i) → pSpec₁.FullTranscript →
      Option (Stmt₂ × ∀ i, OStmt₂ i))
    (hVerify : V₁.toVerifier = ⟨fun p tr => OptionT.mk (pure (verify? p tr))⟩)
    (hInit : ∃ s, s ∈ support init) (hInitNF : Pr[⊥ | init] = 0)
    (hNEW₂ : Nonempty Wit₂)
    (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .P_to_V)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .P_to_V)
    (h₁ : V₁.rbrKnowledgeSoundness init impl rel₁ rel₂ rbrKnowledgeError₁)
    (h₂ : V₂.rbrKnowledgeSoundness init impl rel₂ rel₃ rbrKnowledgeError₂) :
      (OracleVerifier.append (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) V₁ V₂).rbrKnowledgeSoundness
        init impl rel₁ rel₃
        (Sum.elim rbrKnowledgeError₁ rbrKnowledgeError₂ ∘ ChallengeIdx.sumEquiv.symm) := by
  unfold OracleVerifier.rbrKnowledgeSoundness at h₁ h₂ ⊢
  rw [OracleReduction.oracleVerifier_append_toVerifier, hVerify]
  rw [hVerify] at h₁
  exact Verifier.append_rbrKnowledgeSoundness_failingDet_subsingleton verify? V₂.toVerifier
    hInit hInitNF hNEW₂ hn hDir hDir₂ h₁ h₂

end OracleVerifier

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms Verifier.append_failingDet_eq_optionized
#print axioms Verifier.optionLift_rbrKnowledgeSoundness
#print axioms Verifier.failingDet_optionized_rbrKnowledgeSoundness
#print axioms Verifier.append_rbrKnowledgeSoundness_failingDet_subsingleton
#print axioms Verifier.append_failingDet_failingDet
#print axioms Verifier.append_pure_failingDet
#print axioms Verifier.append_failingDet_pure
#print axioms OracleVerifier.toVerifier_eq_failingDet_of_collapse
#print axioms OracleVerifier.append_rbrKnowledgeSoundness_failingDet_subsingleton

end AppendRbrKnowledgeFailingDet

section AppendRbrKnowledgeFailingDetChallenge

/-!
## Knowledge soundness across a challenge seam.
-/

/-!
# Failing-deterministic rbr knowledge-soundness append keystone — CHALLENGE seam

The `V_to_P`-seam companion of `AppendRbrKnowledgeFailingDet.lean` (issue #313, BinaryBasefold
closeout): round-by-round knowledge soundness of `append` when the first round of `pSpec₂` is a
**challenge** round and the left verifier is only **failing**-deterministic
(`verify? : Stmt₁ → FullTranscript → Option Stmt₂`, i.e. `⟨fun s tr => OptionT.mk (pure
(verify? s tr))⟩`).

The proof replays the **optionization reduction** verbatim against the challenge-seam total-det
keystone: rewrite the seam by `Verifier.append_failingDet_eq_optionized` into the
total-deterministic seam over `Option Stmt₂` (determinism witness `rfl`, `Nonempty (Option Stmt₂)`
free via `none`), transport the per-phase hypotheses by
`Verifier.failingDet_optionized_rbrKnowledgeSoundness` / `Verifier.optionLift_rbrKnowledgeSoundness`
(both seam-direction-agnostic), and close with the residual-free challenge-seam keystone
`Verifier.append_rbrKnowledgeSoundness_keystone_subsingleton_challenge`
(`AppendRbrKnowledgeChallenge.lean`).

**Consumer shape (BinaryBasefold).** The full protocol is
`append(coreInteraction, queryPhase)` with `pSpecQuery = ⟨![.V_to_P], …⟩` (the seam round is the
verifier's batch of query challenges) and a failing-deterministic core verifier. The keystone's
error output `Sum.elim err₁ err₂ ∘ ChallengeIdx.sumEquiv.symm` matches the front door's
`fullRbrKnowledgeError = fun i => Sum.elim err₁ err₂ (ChallengeIdx.sumEquiv.symm i)`
definitionally; the flattening is recorded as `Verifier.sumElim_comp_sumEquiv_symm`.
-/

open OracleComp OracleSpec ProtocolSpec
open scoped ENNReal NNReal

namespace Verifier

variable {ι : Type} {oSpec : OracleSpec ι} {Stmt₁ Stmt₂ Stmt₃ : Type}
    {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

/-- **Error-form flattening.** The keystone's composed error `Sum.elim err₁ err₂ ∘
ChallengeIdx.sumEquiv.symm` is definitionally the pointwise `Sum.elim`-of-`sumEquiv.symm` form
used by consumer-side error definitions (e.g. BinaryBasefold's `fullRbrKnowledgeError`). -/
theorem sumElim_comp_sumEquiv_symm
    (err₁ : pSpec₁.ChallengeIdx → ℝ≥0) (err₂ : pSpec₂.ChallengeIdx → ℝ≥0) :
    (Sum.elim err₁ err₂ ∘ ChallengeIdx.sumEquiv.symm
        : (pSpec₁ ++ₚ pSpec₂).ChallengeIdx → ℝ≥0)
      = fun i => Sum.elim err₁ err₂ (ChallengeIdx.sumEquiv.symm i) := rfl

variable {Wit₂ : Type} {σ : Type} {init : ProbComp σ}
    {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- **The failing-deterministic rbr knowledge-soundness append keystone (`Subsingleton σ`,
CHALLENGE seam).** The `V_to_P`-seam capstone of the optionization reduction: appending a
*failing*-deterministic left verifier (the BinaryBasefold `coreInteraction` shape, `else failure`)
to `V₂` across a challenge seam (first round of `pSpec₂` is `.V_to_P`) is round-by-round knowledge
sound with the additive `Sum.elim` error — **no residual hypotheses** beyond the per-phase bounds,
the failing-determinism shape itself, and the stateless regime's side conditions.

Proof: rewrite the seam by `append_failingDet_eq_optionized` into the total-deterministic seam over
`Option Stmt₂` (where the determinism witness is `rfl` and `Nonempty (Option Stmt₂)` is free via
`none`), transport `h₁`/`h₂` by `failingDet_optionized_rbrKnowledgeSoundness` /
`optionLift_rbrKnowledgeSoundness`, and apply the residual-free total-deterministic challenge-seam
keystone `append_rbrKnowledgeSoundness_keystone_subsingleton_challenge`. -/
theorem append_rbrKnowledgeSoundness_failingDet_subsingleton_challenge
    [Subsingleton σ] [Inhabited Stmt₂]
    {Stmt₃ Wit₁ Wit₃ : Type} {n : ℕ} {pSpec₂ : ProtocolSpec n}
    [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
    (verify? : Stmt₁ → pSpec₁.FullTranscript → Option Stmt₂)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}
    {err₁ : pSpec₁.ChallengeIdx → ℝ≥0} {err₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (hInit : ∃ s, s ∈ support init) (hInitNF : Pr[⊥ | init] = 0)
    (hNEW₂ : Nonempty Wit₂)
    (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .V_to_P)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .V_to_P)
    (h₁ : Verifier.rbrKnowledgeSoundness init impl rel₁ rel₂
      (⟨fun s tr => OptionT.mk (pure (verify? s tr))⟩ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) err₁)
    (h₂ : V₂.rbrKnowledgeSoundness init impl rel₂ rel₃ err₂) :
    (Verifier.append
        (⟨fun s tr => OptionT.mk (pure (verify? s tr))⟩ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
        V₂).rbrKnowledgeSoundness init impl rel₁ rel₃
      (Sum.elim err₁ err₂ ∘ ChallengeIdx.sumEquiv.symm) := by
  rw [append_failingDet_eq_optionized]
  exact append_rbrKnowledgeSoundness_keystone_subsingleton_challenge
    (⟨fun s tr => pure (verify? s tr)⟩ : Verifier oSpec Stmt₁ (Option Stmt₂) pSpec₁)
    V₂.optionLift verify? rfl hInit hInitNF ⟨none⟩ hNEW₂ hn hDir hDir₂
    (failingDet_optionized_rbrKnowledgeSoundness verify? h₁)
    (optionLift_rbrKnowledgeSoundness V₂ h₂)

end Verifier

namespace OracleVerifier

variable {ι : Type} {oSpec : OracleSpec ι}
    {Stmt₁ : Type} {ιₛ₁ : Type} {OStmt₁ : ιₛ₁ → Type}
    [Oₛ₁ : ∀ i, OracleInterface (OStmt₁ i)]
    {Wit₁ : Type}
    {Stmt₂ : Type} {ιₛ₂ : Type} {OStmt₂ : ιₛ₂ → Type}
    [Oₛ₂ : ∀ i, OracleInterface (OStmt₂ i)]
    {Wit₂ : Type}
    {Stmt₃ : Type} {ιₛ₃ : Type} {OStmt₃ : ιₛ₃ → Type}
    [Oₛ₃ : ∀ i, OracleInterface (OStmt₃ i)]
    {Wit₃ : Type}
    {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
    [Oₘ₁ : ∀ i, OracleInterface (pSpec₁.Message i)]
    [Oₘ₂ : ∀ i, OracleInterface (pSpec₂.Message i)]
    [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel₁ : Set ((Stmt₁ × ∀ i, OStmt₁ i) × Wit₁)}
    {rel₂ : Set ((Stmt₂ × ∀ i, OStmt₂ i) × Wit₂)}
    {rel₃ : Set ((Stmt₃ × ∀ i, OStmt₃ i) × Wit₃)}

/-- **OracleVerifier-level failing-deterministic rbr knowledge-soundness append keystone
(`Subsingleton σ`, CHALLENGE seam).** The OracleVerifier companion of
`Verifier.append_rbrKnowledgeSoundness_failingDet_subsingleton_challenge` and the `V_to_P`-seam
companion of `OracleVerifier.append_rbrKnowledgeSoundness_failingDet_subsingleton`: discharges the
rbr knowledge soundness of `OracleVerifier.append` for seams whose left verifier compiles to a
*failing*-deterministic `toVerifier` (witnesses supplied by `toVerifier_eq_failingDet_of_collapse`
+ the composition combinators) and whose right phase opens with a challenge round — the
BinaryBasefold `append(coreInteraction, queryPhase)` shape. One-shot from
`oracleVerifier_append_toVerifier` + the Protocol-level challenge-seam failing-det capstone. -/
theorem append_rbrKnowledgeSoundness_failingDet_subsingleton_challenge
    [Subsingleton σ] [Inhabited (Stmt₂ × ∀ i, OStmt₂ i)]
    (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    [OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) V₁]
    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂)
    {rbrKnowledgeError₁ : pSpec₁.ChallengeIdx → ℝ≥0}
    {rbrKnowledgeError₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (verify? : (Stmt₁ × ∀ i, OStmt₁ i) → pSpec₁.FullTranscript →
      Option (Stmt₂ × ∀ i, OStmt₂ i))
    (hVerify : V₁.toVerifier = ⟨fun p tr => OptionT.mk (pure (verify? p tr))⟩)
    (hInit : ∃ s, s ∈ support init) (hInitNF : Pr[⊥ | init] = 0)
    (hNEW₂ : Nonempty Wit₂)
    (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .V_to_P)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .V_to_P)
    (h₁ : V₁.rbrKnowledgeSoundness init impl rel₁ rel₂ rbrKnowledgeError₁)
    (h₂ : V₂.rbrKnowledgeSoundness init impl rel₂ rel₃ rbrKnowledgeError₂) :
      (OracleVerifier.append (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) V₁ V₂).rbrKnowledgeSoundness
        init impl rel₁ rel₃
        (Sum.elim rbrKnowledgeError₁ rbrKnowledgeError₂ ∘ ChallengeIdx.sumEquiv.symm) := by
  unfold OracleVerifier.rbrKnowledgeSoundness at h₁ h₂ ⊢
  rw [OracleReduction.oracleVerifier_append_toVerifier, hVerify]
  rw [hVerify] at h₁
  exact Verifier.append_rbrKnowledgeSoundness_failingDet_subsingleton_challenge verify?
    V₂.toVerifier hInit hInitNF hNEW₂ hn hDir hDir₂ h₁ h₂

end OracleVerifier

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms Verifier.sumElim_comp_sumEquiv_symm
#print axioms Verifier.append_rbrKnowledgeSoundness_failingDet_subsingleton_challenge
#print axioms OracleVerifier.append_rbrKnowledgeSoundness_failingDet_subsingleton_challenge

end AppendRbrKnowledgeFailingDetChallenge

section AppendRbrKnowledgeFailingDetEmpty

/-!
## Knowledge soundness across an empty seam.
-/

/-!
# Failing-deterministic empty-seam rbr knowledge-soundness append keystone

Combines the **optionization reduction** (`AppendRbrKnowledgeFailingDet.lean`) with the
**residual-free empty-seam keystone** (`AppendRbrKnowledgeEmpty.lean`): appending a
*failing*-deterministic left verifier (`⟨fun s tr => OptionT.mk (pure (verify? s tr))⟩`) to a
0-round right phase is round-by-round knowledge sound with the additive `Sum.elim` error,
with **no** `Subsingleton σ`, **no** lossless-`init` (`hInitNF`), and **no** seam-direction
hypotheses: the phase-2 residual quantifies over the (empty) `pSpec₂.ChallengeIdx`, so it is
vacuous, and the optionization transports are state-regime-free.

Proof shape (mirroring `Verifier.append_rbrKnowledgeSoundness_failingDet_subsingleton`): rewrite
the failing-det seam into the total-det seam over `Option Stmt₂` via
`append_failingDet_eq_optionized` (where the determinism witness is `rfl` and
`Nonempty (Option Stmt₂)` is free via `none`), transport the per-phase bounds by
`failingDet_optionized_rbrKnowledgeSoundness` / `optionLift_rbrKnowledgeSoundness`, and apply
`append_rbrKnowledgeSoundness_keystone_empty`. The `OracleVerifier` lift is the standard 3-line
`oracleVerifier_append_toVerifier` plumbing.
-/

open OracleComp OracleSpec ProtocolSpec
open scoped ENNReal NNReal

universe u

namespace Verifier

variable {ι : Type} {oSpec : OracleSpec ι} {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
    {m : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec 0}
    [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- **Failing-deterministic empty-seam rbr knowledge-soundness append keystone
(residual-free).** Appending a *failing*-deterministic left verifier to a 0-round right phase is
round-by-round knowledge sound with the additive `Sum.elim` error — no `Subsingleton σ`, no
lossless-`init`, and no seam-direction hypotheses: the empty keystone's phase-2 residual is
vacuous (no phase-2 challenges) and the optionization transports are state-regime-free.

Proof: rewrite the seam by `append_failingDet_eq_optionized` into the total-deterministic seam
over `Option Stmt₂` (where the determinism witness is `rfl` and `Nonempty (Option Stmt₂)` is free
via `none`), transport `h₁`/`h₂` by `failingDet_optionized_rbrKnowledgeSoundness` /
`optionLift_rbrKnowledgeSoundness`, and apply the residual-free empty keystone. -/
theorem append_rbrKnowledgeSoundness_failingDet_empty
    [Inhabited Stmt₂]
    (verify? : Stmt₁ → pSpec₁.FullTranscript → Option Stmt₂)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}
    {err₁ : pSpec₁.ChallengeIdx → ℝ≥0} {err₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (hInit : ∃ s, s ∈ support init)
    (hNEW₂ : Nonempty Wit₂)
    (h₁ : Verifier.rbrKnowledgeSoundness init impl rel₁ rel₂
      (⟨fun s tr => OptionT.mk (pure (verify? s tr))⟩ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) err₁)
    (h₂ : V₂.rbrKnowledgeSoundness init impl rel₂ rel₃ err₂) :
    (Verifier.append
        (⟨fun s tr => OptionT.mk (pure (verify? s tr))⟩ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
        V₂).rbrKnowledgeSoundness init impl rel₁ rel₃
      (Sum.elim err₁ err₂ ∘ ChallengeIdx.sumEquiv.symm) := by
  rw [append_failingDet_eq_optionized]
  exact append_rbrKnowledgeSoundness_keystone_empty
    (⟨fun s tr => pure (verify? s tr)⟩ : Verifier oSpec Stmt₁ (Option Stmt₂) pSpec₁)
    V₂.optionLift verify? rfl hInit ⟨none⟩ hNEW₂
    (failingDet_optionized_rbrKnowledgeSoundness verify? h₁)
    (optionLift_rbrKnowledgeSoundness V₂ h₂)

end Verifier

namespace OracleVerifier

variable {ι : Type} {oSpec : OracleSpec ι}
    {Stmt₁ : Type} {ιₛ₁ : Type} {OStmt₁ : ιₛ₁ → Type}
    [Oₛ₁ : ∀ i, OracleInterface (OStmt₁ i)]
    {Wit₁ : Type}
    {Stmt₂ : Type} {ιₛ₂ : Type} {OStmt₂ : ιₛ₂ → Type}
    [Oₛ₂ : ∀ i, OracleInterface (OStmt₂ i)]
    {Wit₂ : Type}
    {Stmt₃ : Type} {ιₛ₃ : Type} {OStmt₃ : ιₛ₃ → Type}
    [Oₛ₃ : ∀ i, OracleInterface (OStmt₃ i)]
    {Wit₃ : Type}
    {m : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec 0}
    [Oₘ₁ : ∀ i, OracleInterface (pSpec₁.Message i)]
    [Oₘ₂ : ∀ i, OracleInterface (pSpec₂.Message i)]
    [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel₁ : Set ((Stmt₁ × ∀ i, OStmt₁ i) × Wit₁)}
    {rel₂ : Set ((Stmt₂ × ∀ i, OStmt₂ i) × Wit₂)}
    {rel₃ : Set ((Stmt₃ × ∀ i, OStmt₃ i) × Wit₃)}

/-- **OracleVerifier-level failing-deterministic empty-seam rbr knowledge-soundness append
keystone (residual-free).** The OracleVerifier companion of
`Verifier.append_rbrKnowledgeSoundness_failingDet_empty`: discharges the
`OracleVerifier.appendRbrKnowledgeSoundnessResidual` for seams whose left verifier compiles to a
*failing*-deterministic `toVerifier` and whose right phase is 0-round — with no `Subsingleton σ`,
no lossless-`init`, and no seam-direction hypotheses. One-shot from
`oracleVerifier_append_toVerifier` + the Protocol-level failing-det empty capstone. -/
theorem append_rbrKnowledgeSoundness_failingDet_empty
    [Inhabited (Stmt₂ × ∀ i, OStmt₂ i)]
    (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    [OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) V₁]
    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂)
    {rbrKnowledgeError₁ : pSpec₁.ChallengeIdx → ℝ≥0}
    {rbrKnowledgeError₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (verify? : (Stmt₁ × ∀ i, OStmt₁ i) → pSpec₁.FullTranscript →
      Option (Stmt₂ × ∀ i, OStmt₂ i))
    (hVerify : V₁.toVerifier = ⟨fun p tr => OptionT.mk (pure (verify? p tr))⟩)
    (hInit : ∃ s, s ∈ support init)
    (hNEW₂ : Nonempty Wit₂)
    (h₁ : V₁.rbrKnowledgeSoundness init impl rel₁ rel₂ rbrKnowledgeError₁)
    (h₂ : V₂.rbrKnowledgeSoundness init impl rel₂ rel₃ rbrKnowledgeError₂) :
      (OracleVerifier.append (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) V₁ V₂).rbrKnowledgeSoundness
        init impl rel₁ rel₃
        (Sum.elim rbrKnowledgeError₁ rbrKnowledgeError₂ ∘ ChallengeIdx.sumEquiv.symm) := by
  unfold OracleVerifier.rbrKnowledgeSoundness at h₁ h₂ ⊢
  rw [OracleReduction.oracleVerifier_append_toVerifier, hVerify]
  rw [hVerify] at h₁
  exact Verifier.append_rbrKnowledgeSoundness_failingDet_empty verify? V₂.toVerifier
    hInit hNEW₂ h₁ h₂

end OracleVerifier

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms Verifier.append_rbrKnowledgeSoundness_failingDet_empty
#print axioms OracleVerifier.append_rbrKnowledgeSoundness_failingDet_empty

end AppendRbrKnowledgeFailingDetEmpty
