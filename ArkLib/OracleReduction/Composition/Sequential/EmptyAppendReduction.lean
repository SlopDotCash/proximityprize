/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.EmptyAppend

/-!
# Reduction-level run factoring for an empty trailing protocol

Lifts the prover-level `Prover.append_run_empty` to the full `Reduction.run`: when the trailing
protocol `pSpec₂` is empty, running the appended reduction factors into running `R₁`'s prover, then
`R₂`'s prover, then the appended verifier on the concatenated transcript. This is the run-shape used
by the sequential-composition completeness proof for a 0-round trailing phase.
-/

open OracleSpec OracleComp ProtocolSpec

namespace Reduction

variable {ι : Type} {oSpec : OracleSpec ι} {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec 0}
  {R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁}
  {R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂}

/-- **Reduction-level run factoring for an empty trailing protocol.** Running `R₁.append R₂` (with
`pSpec₂` empty) runs `R₁`'s prover, then `R₂`'s prover, then the appended verifier on the
concatenated transcript — the prover side via `Prover.append_run_empty`. -/
theorem run_append_empty (stmt : Stmt₁) (wit : Wit₁) :
    (R₁.append R₂).run stmt wit = (do
      let x ← liftM (liftM (R₁.prover.run stmt wit) :
        OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _)
      let x_1 ← liftM (liftM (R₂.prover.run x.2.1 x.2.2) :
        OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _)
      let stmtOut ← @liftM (OracleComp oSpec)
        (OptionT (OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)))
        (instMonadLiftTOfMonadLift (OracleComp oSpec) (OptionT (OracleComp oSpec))
          (OptionT (OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ))))
        (Option Stmt₃) ((R₁.verifier.append R₂.verifier).run stmt (x.1 ++ₜ x_1.1)).run
      return ((x.1 ++ₜ x_1.1, x_1.2.1, x_1.2.2), ← stmtOut.getM)) := by
  unfold Reduction.run Reduction.append
  rw [Prover.append_run_empty]
  simp only [liftM_bind, bind_assoc, liftM_pure, pure_bind]

end Reduction
