/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.Append

/-!
# Verifier-fusion building blocks for the sequential-composition keystone

The oracle-level append perfect-completeness keystone reduces (see
`OracleReduction.verifier_append_eq_iff_verify`) to showing, per input/transcript, that the appended
oracle-verifier's `toVerifier.verify` — one `simulateQ` over the joint `simOracle2` running
`OracleVerifier.Append.verify` (a `router₁`/`router₂`-routed two-stage run) — equals the two-stage
composite `V₂.toVerifier ∘ V₁.toVerifier`. With the universal-fold fusion law
`simulateQ_simulateQ`, that collapses to two per-router handler equalities
`(fun q => simulateQ S (routerᵢ q)) = simOracle2 …`.

This file proves the **first** of those (`router₁_handler_eq`) outright, together with the per-query
routing facts it rests on: simulating the `emitMessageQuery` / `emitOStmtQuery{Inl}` routers through
`simOracle2` yields the corresponding in-the-clear oracle answer. The message case uses the
transcript seam-split `ProtocolSpec.messages_inl`.
-/

open OracleComp OracleSpec ProtocolSpec OracleVerifier.Append

namespace OracleVerifier.Append

variable {ι : Type} {oSpec : OracleSpec ι}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  [Oₘ₁ : ∀ i, OracleInterface (pSpec₁.Message i)]
  [Oₘ₂ : ∀ i, OracleInterface (pSpec₂.Message i)]
  {ιₛ₁ : Type} {OStmt₁ : ιₛ₁ → Type} [Oₛ₁ : ∀ i, OracleInterface (OStmt₁ i)]

/-- Simulating `emitMessageQuery` through `simOracle2` yields the message answer: `subst` the type
and instance equalities, after which the emitted query is answered directly by `simOracle2`'s
message half. -/
lemma simulateQ_emitMessageQuery
    {T₁ : Type} (O₁ : OracleInterface T₁)
    (j : (pSpec₁ ++ₚ pSpec₂).MessageIdx)
    (hMsg : (pSpec₁ ++ₚ pSpec₂).Message j = T₁)
    (hO : O₁ = cast (congrArg OracleInterface hMsg)
      (instOracleInterfaceMessageAppend j))
    (q : O₁.Query)
    (oStmt : ∀ i, OStmt₁ i) (msgs : ∀ j, (pSpec₁ ++ₚ pSpec₂).Message j) :
    simulateQ (OracleInterface.simOracle2 oSpec oStmt msgs)
        (emitMessageQuery (oSpec := oSpec) (OStmt₁ := OStmt₁) O₁ j hMsg hO q)
      = (pure (O₁.answer (hMsg ▸ msgs j) q) : OracleComp oSpec _) := by
  subst hMsg
  subst hO
  simp only [emitMessageQuery, simulateQ_spec_query, OracleInterface.simOracle2,
    OracleInterface.simOracle0, QueryImpl.add, QueryImpl.addLift, QueryImpl.liftTarget,
    QueryImpl.id]
  rfl

/-- Simulating `emitOStmtQueryInl` through `simOracle2` yields the `OStmt₁`-answer (the query is
routed straight into `[OStmt₁]ₒ` at index `k`). -/
lemma simulateQ_emitOStmtQueryInl
    {T : Type} (O : OracleInterface T) (k : ιₛ₁) (hSt : OStmt₁ k = T)
    (hO : O = cast (congrArg OracleInterface hSt) (Oₛ₁ k)) (q : O.Query)
    (oStmt : ∀ i, OStmt₁ i) (msgs : ∀ j, (pSpec₁ ++ₚ pSpec₂).Message j) :
    simulateQ (OracleInterface.simOracle2 oSpec oStmt msgs)
        (emitOStmtQueryInl (oSpec := oSpec) (pSpec₂ := pSpec₂) O k hSt hO q)
      = (pure (O.answer (hSt ▸ oStmt k) q) : OracleComp oSpec _) := by
  subst hSt
  subst hO
  simp only [emitOStmtQueryInl, simulateQ_spec_query, OracleInterface.simOracle2,
    OracleInterface.simOracle0, QueryImpl.add, QueryImpl.addLift, QueryImpl.liftTarget,
    QueryImpl.id]
  rfl

/-- **router₁ handler equality.** Routing `V₁`'s queries via `router₁` and answering through the
joint-transcript `simOracle2` (which knows the appended messages) equals answering directly through
the first-half `simOracle2`. The `oSpec` and `[OStmt₁]ₒ` cases are passthrough; the message case
routes to `MessageIdx.inl` and is reconciled by the seam-split `ProtocolSpec.messages_inl`. -/
theorem router₁_handler_eq (oStmt : ∀ i, OStmt₁ i)
    (T : FullTranscript (pSpec₁ ++ₚ pSpec₂)) :
    (fun q => simulateQ (OracleInterface.simOracle2 oSpec oStmt T.messages)
        (router₁ (oSpec := oSpec) (OStmt₁ := OStmt₁) (pSpec₂ := pSpec₂) q))
      = OracleInterface.simOracle2 oSpec oStmt T.fst.messages := by
  funext q
  rcases q with t | t
  · simp [router₁, OracleInterface.simOracle2]
  · rcases t with t | ⟨i, qq⟩
    · simp [router₁, OracleInterface.simOracle2, QueryImpl.add]
    · change simulateQ _ (emitMessageInl i qq) = _
      rw [emitMessageInl, simulateQ_emitMessageQuery]
      simp only [OracleInterface.simOracle2, OracleInterface.simOracle0, QueryImpl.add,
        QueryImpl.addLift, QueryImpl.liftTarget, QueryImpl.id]
      congr 1

end OracleVerifier.Append
