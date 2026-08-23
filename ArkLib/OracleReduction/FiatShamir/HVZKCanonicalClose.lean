/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.FiatShamir.HVZKKernelClose

/-!
# End-to-end canonical Fiat-Shamir HVZK (#116)

Final-layer corollaries of the discharged basic Fiat-Shamir HVZK transfer residual
(`fiatShamir_hvzkTransferResidual_canonical_proved`, in `HVZKKernelClose.lean`), packaged at
the user-facing `isHVZK` / statistical-residual surface:

- `fiatShamir_isHVZK_canonical`: perfect HVZK of an interactive reduction `R` transfers
  *unconditionally* to its Fiat-Shamir transform `R.fiatShamir` under the canonical lazy
  random-oracle challenge implementation (`canonicalFSInit` / `canonicalFSImpl`).
- `fiatShamir_isStatHVZK_canonical`: hence statistical HVZK at every error budget `ε`.
- `fiatShamir_statisticalHVZKTransferResidual_canonical_proved`: the statistical transfer
  residual (`fiatShamir_statisticalHVZKTransferResidual`) holds unconditionally at every `ε`
  for the canonical implementation.

This closes #116-HVZK end to end. A complementary *lazy-route* reduction of the same per-state
coupling kernel — to a single full-transcript coupling hypothesis — lives in
`HVZKPerStateClose.lean` (see `canonicalFSPerStateCoupling_of_fullTranscriptCoupling`).
-/

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace Reduction

set_option linter.unusedSectionVars false

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [DecidableEq StmtIn] [∀ i, DecidableEq (pSpec.Message i)]
  [∀ i, VCVCompatible (pSpec.Message i)]

-- Register, with high priority, the very `SampleableType` instance that `FiatShamir/Basic.lean`
-- used (locally) when elaborating the residual definitions, so that the `isHVZK`/`isStatHVZK`
-- conclusions below re-elaborate with the *same* instance and match definitionally rather than
-- picking up the generic `ProtocolSpec` no-challenge instance (same device as
-- `ZKResidualBridge.lean`).
attribute [local instance 10000] Reduction.fiatShamirZKNoChallengeSampleable

/-- **Canonical Fiat-Shamir perfect HVZK transfer, unconditional.** If the interactive reduction
`R` is honest-verifier zero-knowledge for `rel` (under `init`/`impl`), then its Fiat-Shamir
transform `R.fiatShamir` is honest-verifier zero-knowledge for `rel` under the canonical lazy
random-oracle challenge implementation. -/
theorem fiatShamir_isHVZK_canonical
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rel : Set (StmtIn × WitIn))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hHVZK : Reduction.isHVZK init impl rel R) :
    Reduction.isHVZK (canonicalFSInit (StmtIn := StmtIn) (pSpec := pSpec) init)
      (canonicalFSImpl (StmtIn := StmtIn) impl) rel R.fiatShamir := by
  classical
  exact fiatShamir_hvzkTransferResidual_canonical_proved init impl rel R hHVZK

/-- **Canonical Fiat-Shamir statistical HVZK, unconditional.** Perfect HVZK of the interactive
source yields statistical HVZK of the Fiat-Shamir transform at every error budget `ε`, under the
canonical lazy random-oracle challenge implementation. -/
theorem fiatShamir_isStatHVZK_canonical
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rel : Set (StmtIn × WitIn)) (ε : ℝ≥0)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hHVZK : Reduction.isHVZK init impl rel R) :
    Reduction.isStatHVZK (canonicalFSInit (StmtIn := StmtIn) (pSpec := pSpec) init)
      (canonicalFSImpl (StmtIn := StmtIn) impl) rel R.fiatShamir ε :=
  (fiatShamir_isHVZK_canonical init impl rel R hHVZK).isStatHVZK ε

/-- **The statistical Fiat-Shamir HVZK transfer residual holds unconditionally** at every error
budget `ε` for the canonical lazy random-oracle challenge implementation: the statistical-form
counterpart of `fiatShamir_hvzkTransferResidual_canonical_proved`. -/
theorem fiatShamir_statisticalHVZKTransferResidual_canonical_proved
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rel : Set (StmtIn × WitIn)) (ε : ℝ≥0)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) :
    fiatShamir_statisticalHVZKTransferResidual init impl
      (canonicalFSInit (StmtIn := StmtIn) (pSpec := pSpec) init)
      (canonicalFSImpl (StmtIn := StmtIn) impl) rel ε R := by
  classical
  exact fiatShamir_statisticalHVZKTransferResidual.of_perfectTransfer init impl _ _ rel ε R
    (fiatShamir_hvzkTransferResidual_canonical_proved init impl rel R)

#print axioms fiatShamir_isHVZK_canonical
#print axioms fiatShamir_isStatHVZK_canonical
#print axioms fiatShamir_statisticalHVZKTransferResidual_canonical_proved

end Reduction
