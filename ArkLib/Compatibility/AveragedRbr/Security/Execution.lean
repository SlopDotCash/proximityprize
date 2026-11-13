/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Alexander Hicks, Devon Tuma, Pietro Monticone, Tobias Rothmann
-/

import ArkLib.OracleReduction.Execution

/-!
# Historical partial-run logging projection

This identity is retained from ArkLib 1040ed0e6f208de9afd1a1aa56888ccd830c0964 for
downstream completeness and prover-averaged security proofs.
-/

open OracleComp OracleSpec SubSpec ProtocolSpec

namespace Prover

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}

@[simp]
lemma runWithLogToRound_discard_log_eq_runToRound (i : Fin (n + 1))
    (stmt : StmtIn) (wit : WitIn) (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) :
      Prod.fst <$> prover.runWithLogToRound i stmt wit =
        prover.runToRound i stmt wit := by
  simp [runWithLogToRound, runToRound]

end Prover
