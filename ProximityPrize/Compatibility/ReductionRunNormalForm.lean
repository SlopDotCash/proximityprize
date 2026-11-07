/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Execution

/-!
# Compatibility name for the canonical optional reduction run

The reusable execution normal form belongs to canonical `Reduction.run_run_eq_bind`.
Keep the downstream verifier-facing name independent of LogUp security proofs.
-/

open OracleComp OracleSpec ProtocolSpec

namespace Verifier

/-- The prover/verifier boundary, retaining every optional verifier outcome. -/
theorem reduction_run_run_nf
    {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut : Type}
    {n : ℕ} {pSpec : ProtocolSpec n}
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn) :
    ((Reduction.mk prover verifier).run stmtIn witIn).run =
      prover.run stmtIn witIn >>= fun pr =>
        OracleComp.liftComp ((verifier.run stmtIn pr.1).run) (oSpec + [pSpec.Challenge]ₒ)
          >>= fun o =>
        (pure (o.map (fun v => (pr, v))) :
          OracleComp (oSpec + [pSpec.Challenge]ₒ)
            (Option ((FullTranscript pSpec × StmtOut × WitOut) × StmtOut))) :=
  Reduction.run_run_eq_bind (Reduction.mk prover verifier) stmtIn witIn

end Verifier

#print axioms Verifier.reduction_run_run_nf
