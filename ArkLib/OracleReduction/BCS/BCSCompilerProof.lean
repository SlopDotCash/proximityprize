/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Master Cryptographer
-/
import ArkLib.OracleReduction.BCS.Basic

/-!
# BCS Compiler Preservation residual checkpoint (Issue #62)

This file records the *named-residual checkpoint* for the generic BCS compiler preservation
obligation. **The theorem below carries zero mathematical content**: it is the identity on its
own hypothesis (`hReady ↦ hReady`), kept only so the remaining obligation has a stable,
greppable name. The actual preservation theorem still has to establish
`BCSCompilerFrontierReady` from concrete phase/security hypotheses (commitment
binding/extractability + the query-log realization of the two phases); that work is open and
tracked by `BCSSecurityFrontier` in `ArkLib.OracleReduction.BCS.Basic`.

The parts of the #62 compiler obligation that *are* genuine theorems live elsewhere:
* completeness composition — `OracleReduction.BCSTransform_perfectCompleteness`
  (`ArkLib.OracleReduction.BCS.CompletenessPreservation`), unconditional;
* soundness composition — `OracleReduction.BCSCompiledPhases.toReduction_soundness_of_append_msg`
  (`ArkLib.OracleReduction.BCS.AppendSoundnessMsg`), unconditional for the message seam.
-/

namespace BCSCompiler

open scoped NNReal ProbabilityTheory

/-- **Issue #62 named-residual checkpoint (no content).** This is literally the identity on the
hypothesis `hReady`; it proves nothing. It exists only to keep the open
`BCSCompilerFrontierReady` obligation named and visible. Do not cite this as a result. -/
theorem bcs_compiler_preservation_residual_passthrough
    {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
    [∀ i, OracleInterface (pSpec.Message i)]
    {m : ℕ} {nCom : pSpec.MessageIdx → ℕ} {pSpecCom : ∀ i, ProtocolSpec (nCom i)}
    {StmtIn StmtOut WitIn WitOut StmtMid WitMid : Type}
    {CommitmentType : pSpec.MessageIdx → Type} {e : pSpec.MessageIdx ≃ Fin m}
    (phases : OracleReduction.BCSCompiledPhases (oSpec := oSpec) (pSpec := pSpec)
      (pSpecCom := pSpecCom) (StmtIn := StmtIn) (WitIn := WitIn)
      (StmtOut := StmtOut) (WitOut := WitOut) (StmtMid := StmtMid)
      (WitMid := WitMid) CommitmentType e)
    (frontier : OracleReduction.BCSSecurityFrontier (oSpec := oSpec) (pSpec := pSpec)
      (pSpecCom := pSpecCom) (StmtIn := StmtIn) (WitIn := WitIn)
      (StmtOut := StmtOut) (WitOut := WitOut) (StmtMid := StmtMid)
      (WitMid := WitMid) phases)
    (hReady : OracleReduction.BCSCompilerFrontierReady phases frontier) :
    OracleReduction.BCSCompilerFrontierReady phases frontier :=
  hReady

#print axioms BCSCompiler.bcs_compiler_preservation_residual_passthrough

end BCSCompiler
