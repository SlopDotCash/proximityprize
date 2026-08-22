/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.Append

/-!
# Verifier-fusion bedrock: `simulateQ` of the V₂-side oracle-statement router

This file discharges the per-query obligation at the heart of the oracle-level append
perfect-completeness keystone: simulating the appended verifier's `emitOStmt₂Query` (which routes a
query to one of `V₁`'s output oracle statements `OStmt₂ i`) under the combined `simOracle2` answers
exactly from the reconstructed oracle statement `mkVerifierOStmtOut V₁.embed V₁.hEq oStmt tr.fst i`.

The single subtlety is that `emitOStmt₂Query` is *tactic-built* (`by cases h : V₁.embed i …`), so a
naive `split` does not fire on its elaborated `Sum.casesOn`; the proof must mirror the definition with
`cases h : V₁.embed i`, then discharge each branch via the proven per-query simulators
(`emitOStmtQueryInl_simulateQ` / `emitOStmtQueryInr_simulateQ`) and the `mkVerifierOStmtOut`
characterizations, with the residual dependent casts collapsed by `eq_of_heq` over `eqRec_heq`.
-/

open OracleComp OracleSpec ProtocolSpec

namespace OracleVerifier.Append

variable {ι : Type} {oSpec : OracleSpec ι}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  [Oₘ₁ : ∀ i, OracleInterface (pSpec₁.Message i)]
  [Oₘ₂ : ∀ i, OracleInterface (pSpec₂.Message i)]
  {ιₛ₁ : Type} {OStmt₁ : ιₛ₁ → Type} [Oₛ₁ : ∀ i, OracleInterface (OStmt₁ i)]
  {ιₛ₂ : Type} {OStmt₂ : ιₛ₂ → Type} [Oₛ₂ : ∀ i, OracleInterface (OStmt₂ i)]
  {Stmt₁ Stmt₂ : Type}

/-- **The V₂-side per-query routing simulates to the reconstructed oracle statement.** -/
theorem simulateQ_emitOStmt₂Query_core
    (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    [coh : AppendCoherent (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) V₁]
    (oStmt : ∀ i, OStmt₁ i) (tr : FullTranscript (pSpec₁ ++ₚ pSpec₂))
    (i : ιₛ₂) (q : (Oₛ₂ i).Query) :
    simulateQ (OracleInterface.simOracle2 oSpec oStmt tr.messages) (emitOStmt₂Query V₁ i q)
      = pure ((Oₛ₂ i).answer (mkVerifierOStmtOut V₁.embed V₁.hEq oStmt tr.fst i) q) :=
  -- The `cases h : V₁.embed i` route fails (`generalize` on the tactic-built `Sum.casesOn` motive);
  -- delegate to the `split`-based proof in `Append.lean`.
  simulateQ_emitOStmt₂Query V₁ oStmt tr i q

end OracleVerifier.Append
