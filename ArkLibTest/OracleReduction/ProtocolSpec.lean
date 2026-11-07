/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.ProtocolSpec.Basic
/-! Type-based query and answer instances after retiring the bundled OracleSpec classes. -/

set_option autoImplicit false
open ProtocolSpec
variable {n : ℕ} {pSpec : ProtocolSpec n} {Statement : Type}
example [DecidableEq Statement] [∀ i, DecidableEq (pSpec.Message i)] :
    DecidableEq (srChallengeOracle Statement pSpec).Domain := by
  dsimp only [srChallengeOracle, OracleInterface.toOracleSpec,
    challengeOracleInterfaceSR, OracleSpec.Domain, OracleInterface.Query]
  infer_instance
example [∀ i, DecidableEq (pSpec.Challenge i)]
    (q : (srChallengeOracle Statement pSpec).Domain) :
    DecidableEq ((srChallengeOracle Statement pSpec).Range q) := by
  dsimp only [srChallengeOracle, OracleInterface.toOracleSpec,
    challengeOracleInterfaceSR, OracleSpec.Range, OracleInterface.Response]
  infer_instance
example [∀ i, VCVCompatible (pSpec.Challenge i)]
    (q : (srChallengeOracle Statement pSpec).Domain) :
    Fintype ((srChallengeOracle Statement pSpec).Range q) := by
  dsimp only [srChallengeOracle, OracleInterface.toOracleSpec,
    challengeOracleInterfaceSR, OracleSpec.Range, OracleInterface.Response]
  infer_instance
