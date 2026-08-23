/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.FiatShamir.Basic

/-!
  # Basic Fiat-Shamir: perfect ⇔ zero-error HVZK transfer residual bridge (#116)

  `ArkLib/OracleReduction/FiatShamir/Basic.lean` names two Fiat-Shamir zero-knowledge transfer
  obligations:

  - `fiatShamir_hvzkTransferResidual` — the *perfect* form: `isHVZK R → isHVZK R.fiatShamir`.
  - `fiatShamir_statisticalHVZKTransferResidual ... ε` — the *statistical* form:
    `isHVZK R → isStatHVZK R.fiatShamir ε`.

  The file there proves the perfect HVZK conclusion can be obtained from the statistical residual at
  `ε = 0` (`fiatShamir_isHVZK_of_HVZK_zero`), but never identifies the two *residual hypotheses*
  themselves. This module closes that gap: the perfect transfer residual is logically equivalent to
  the zero-error statistical transfer residual. So a future simulator-transfer proof discharged in
  either form immediately supplies the other, and downstream wrappers can pick whichever residual is
  convenient.

  These are pure equivalences over the existing residual definitions and the promoted
  `Reduction.isStatHVZK_zero.isHVZK` / `Reduction.isHVZK.isStatHVZK` bridges; they construct no
  simulator and discharge no residual.
-/

noncomputable section

open ProtocolSpec OracleComp OracleSpec
open scoped NNReal

namespace Reduction

variable {n : ℕ}
variable {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [∀ i, SampleableType (pSpec.Challenge i)]
  {σ τ : Type}

-- Register, with high priority, the very `SampleableType` instance that
-- `FiatShamir/Basic.lean` used (locally) when elaborating the residual definitions, so that the
-- conclusions below re-elaborate with the *same* instance and match definitionally rather than
-- picking up the generic `ProtocolSpec` no-challenge instance.
attribute [local instance 10000] Reduction.fiatShamirZKNoChallengeSampleable

/-- **The zero-error statistical FS HVZK transfer residual implies the perfect one.** If the
Fiat-Shamir simulator transfer is dischargeable at statistical error `0`, then the exact-distribution
(perfect) transfer residual holds: discharging the statistical residual at `0` already proves perfect
HVZK of the transformed reduction. -/
theorem fiatShamir_hvzkTransferResidual_of_statisticalHVZKTransferResidual_zero
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (fsInit : ProbComp τ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT τ ProbComp))
    (rel : Set (StmtIn × WitIn))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hStat : fiatShamir_statisticalHVZKTransferResidual init impl fsInit fsImpl rel 0 R) :
    fiatShamir_hvzkTransferResidual init impl fsInit fsImpl rel R := by
  intro hHVZK
  exact _root_.Reduction.isStatHVZK_zero.isHVZK (hStat hHVZK)

/-- **The perfect FS HVZK transfer residual implies the zero-error statistical one.** A perfect
simulator transfer yields exact distribution equality, hence statistical distance `0`. -/
theorem fiatShamir_statisticalHVZKTransferResidual_zero_of_hvzkTransferResidual
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (fsInit : ProbComp τ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT τ ProbComp))
    (rel : Set (StmtIn × WitIn))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hPerf : fiatShamir_hvzkTransferResidual init impl fsInit fsImpl rel R) :
    fiatShamir_statisticalHVZKTransferResidual init impl fsInit fsImpl rel 0 R := by
  intro hHVZK
  exact (hPerf hHVZK).isStatHVZK 0

/-- **The perfect FS HVZK transfer residual is equivalent to the zero-error statistical one.**
A simulator-transfer argument discharged in either form supplies the other. -/
theorem fiatShamir_hvzkTransferResidual_iff_statisticalHVZKTransferResidual_zero
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (fsInit : ProbComp τ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT τ ProbComp))
    (rel : Set (StmtIn × WitIn))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) :
    fiatShamir_hvzkTransferResidual init impl fsInit fsImpl rel R ↔
      fiatShamir_statisticalHVZKTransferResidual init impl fsInit fsImpl rel 0 R :=
  ⟨fiatShamir_statisticalHVZKTransferResidual_zero_of_hvzkTransferResidual
      init impl fsInit fsImpl rel R,
    fiatShamir_hvzkTransferResidual_of_statisticalHVZKTransferResidual_zero
      init impl fsInit fsImpl rel R⟩

/-- **Perfect FS HVZK from the perfect transfer residual, routed through the statistical residual.**
A convenience wrapper combining the residual bridge with the existing
`fiatShamir_isHVZK_of_transfer`, so a caller holding the *statistical* residual at `0` can conclude
perfect HVZK of the transformed reduction without first converting the residual by hand. (This is
definitionally the same conclusion as `fiatShamir_isHVZK_of_HVZK_zero`; it is provided as the
residual-bridge-facing entry point.) -/
theorem fiatShamir_isHVZK_of_perfectTransfer
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (fsInit : ProbComp τ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT τ ProbComp))
    (rel : Set (StmtIn × WitIn))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hPerf : fiatShamir_hvzkTransferResidual init impl fsInit fsImpl rel R)
    (hHVZK : Reduction.isHVZK init impl rel R) :
    Reduction.isHVZK fsInit fsImpl rel R.fiatShamir :=
  fiatShamir_isHVZK_of_transfer init impl fsInit fsImpl rel R hPerf hHVZK

#print axioms fiatShamir_hvzkTransferResidual_of_statisticalHVZKTransferResidual_zero
#print axioms fiatShamir_statisticalHVZKTransferResidual_zero_of_hvzkTransferResidual
#print axioms fiatShamir_hvzkTransferResidual_iff_statisticalHVZKTransferResidual_zero
#print axioms fiatShamir_isHVZK_of_perfectTransfer

end Reduction
