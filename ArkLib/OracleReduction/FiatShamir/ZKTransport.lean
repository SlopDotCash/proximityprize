/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.FiatShamir.Basic

/-!
# Basic Fiat-Shamir ZK Pre-Transport Wrappers (#116)

`FiatShamir/Basic.lean` exposes wrappers that apply a discharged HVZK simulator-transfer
residual on a larger relation and then restrict the Fiat-Shamir conclusion. This companion
module provides the dual consumer shape: first restrict the source `Reduction.isHVZK` proof to
the relation where the transfer residual is stated, then apply that residual.

These declarations are API plumbing over the existing residual surfaces. They do not construct a
Fiat-Shamir simulator or discharge the semantic HVZK transfer residual.
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

attribute [local instance 10000] Reduction.fiatShamirZKNoChallengeSampleable

/-- Basic Fiat-Shamir statistical HVZK from a transfer residual stated on a sub-relation, after
first restricting the source HVZK proof to that sub-relation. -/
theorem fiatShamir_isStatHVZK_of_HVZK_pre_mono_relation
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (fsInit : ProbComp τ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT τ ProbComp))
    {relSource relTransfer : Set (StmtIn × WitIn)} (hsub : relTransfer ⊆ relSource)
    (ε : ℝ≥0)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hTransfer :
      fiatShamir_statisticalHVZKTransferResidual init impl fsInit fsImpl relTransfer ε R)
    (hHVZK : Reduction.isHVZK init impl relSource R) :
    Reduction.isStatHVZK fsInit fsImpl relTransfer R.fiatShamir ε :=
  fiatShamir_isStatHVZK_of_HVZK init impl fsInit fsImpl relTransfer ε R hTransfer
    (hHVZK.mono_relation hsub)

/-- Basic Fiat-Shamir statistical HVZK from a transfer residual stated on a sub-relation, after
first restricting the source HVZK proof and then relaxing the target error budget. -/
theorem fiatShamir_isStatHVZK_of_HVZK_pre_mono_relation_error
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (fsInit : ProbComp τ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT τ ProbComp))
    {relSource relTransfer : Set (StmtIn × WitIn)} (hsub : relTransfer ⊆ relSource)
    {ε₁ ε₂ : ℝ≥0}
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hTransfer :
      fiatShamir_statisticalHVZKTransferResidual init impl fsInit fsImpl relTransfer ε₁ R)
    (hle : ε₁ ≤ ε₂)
    (hHVZK : Reduction.isHVZK init impl relSource R) :
    Reduction.isStatHVZK fsInit fsImpl relTransfer R.fiatShamir ε₂ :=
  (fiatShamir_isStatHVZK_of_HVZK_pre_mono_relation init impl fsInit fsImpl hsub ε₁ R
    hTransfer hHVZK).mono_error hle

/-- Basic Fiat-Shamir perfect HVZK from a perfect transfer residual stated on a sub-relation, after
first restricting the source HVZK proof to that sub-relation. -/
theorem fiatShamir_isHVZK_of_transfer_pre_mono_relation
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (fsInit : ProbComp τ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT τ ProbComp))
    {relSource relTransfer : Set (StmtIn × WitIn)} (hsub : relTransfer ⊆ relSource)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hTransfer : fiatShamir_hvzkTransferResidual init impl fsInit fsImpl relTransfer R)
    (hHVZK : Reduction.isHVZK init impl relSource R) :
    Reduction.isHVZK fsInit fsImpl relTransfer R.fiatShamir :=
  fiatShamir_isHVZK_of_transfer init impl fsInit fsImpl relTransfer R hTransfer
    (hHVZK.mono_relation hsub)

/-- Basic Fiat-Shamir statistical HVZK from a perfect transfer residual stated on a sub-relation,
after first restricting the source HVZK proof to that sub-relation. -/
theorem fiatShamir_isStatHVZK_of_transfer_pre_mono_relation
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (fsInit : ProbComp τ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT τ ProbComp))
    {relSource relTransfer : Set (StmtIn × WitIn)} (hsub : relTransfer ⊆ relSource)
    (ε : ℝ≥0)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hTransfer : fiatShamir_hvzkTransferResidual init impl fsInit fsImpl relTransfer R)
    (hHVZK : Reduction.isHVZK init impl relSource R) :
    Reduction.isStatHVZK fsInit fsImpl relTransfer R.fiatShamir ε :=
  (fiatShamir_isHVZK_of_transfer_pre_mono_relation init impl fsInit fsImpl hsub R
    hTransfer hHVZK).isStatHVZK ε

/-- Basic Fiat-Shamir perfect HVZK from a zero-error statistical transfer residual stated on a
sub-relation, after first restricting the source HVZK proof to that sub-relation. -/
theorem fiatShamir_isHVZK_of_HVZK_zero_pre_mono_relation
    (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (fsInit : ProbComp τ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT τ ProbComp))
    {relSource relTransfer : Set (StmtIn × WitIn)} (hsub : relTransfer ⊆ relSource)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hTransfer :
      fiatShamir_statisticalHVZKTransferResidual init impl fsInit fsImpl relTransfer 0 R)
    (hHVZK : Reduction.isHVZK init impl relSource R) :
    Reduction.isHVZK fsInit fsImpl relTransfer R.fiatShamir :=
  fiatShamir_isHVZK_of_HVZK_zero init impl fsInit fsImpl relTransfer R hTransfer
    (hHVZK.mono_relation hsub)

/-- Basic Fiat-Shamir statistical HVZK at any error from a zero-error statistical transfer residual
stated on a sub-relation, after first restricting the source HVZK proof to that sub-relation. -/
theorem fiatShamir_isStatHVZK_of_HVZK_zero_pre_mono_relation
    (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (fsInit : ProbComp τ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT τ ProbComp))
    {relSource relTransfer : Set (StmtIn × WitIn)} (hsub : relTransfer ⊆ relSource)
    (ε : ℝ≥0)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hTransfer :
      fiatShamir_statisticalHVZKTransferResidual init impl fsInit fsImpl relTransfer 0 R)
    (hHVZK : Reduction.isHVZK init impl relSource R) :
    Reduction.isStatHVZK fsInit fsImpl relTransfer R.fiatShamir ε :=
  (fiatShamir_isHVZK_of_HVZK_zero_pre_mono_relation init impl fsInit fsImpl hsub R
    hTransfer hHVZK).isStatHVZK ε

/-- Basic Fiat-Shamir statistical HVZK from a transfer residual stated on an intermediate
relation: first restrict the source HVZK proof to the transfer relation, apply the residual, then
restrict and relax the Fiat-Shamir conclusion. -/
theorem fiatShamir_isStatHVZK_of_HVZK_prepost_mono_relation_error
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (fsInit : ProbComp τ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT τ ProbComp))
    {relSource relTransfer relTarget : Set (StmtIn × WitIn)}
    (hpre : relTransfer ⊆ relSource) (hpost : relTarget ⊆ relTransfer)
    {ε₁ ε₂ : ℝ≥0}
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hTransfer :
      fiatShamir_statisticalHVZKTransferResidual init impl fsInit fsImpl relTransfer ε₁ R)
    (hle : ε₁ ≤ ε₂)
    (hHVZK : Reduction.isHVZK init impl relSource R) :
    Reduction.isStatHVZK fsInit fsImpl relTarget R.fiatShamir ε₂ :=
  (fiatShamir_isStatHVZK_of_HVZK_pre_mono_relation init impl fsInit fsImpl hpre ε₁ R
    hTransfer hHVZK).mono_relation_error hpost hle

/-- Basic Fiat-Shamir perfect HVZK from a perfect transfer residual stated on an intermediate
relation, followed by restriction to a final target relation. -/
theorem fiatShamir_isHVZK_of_transfer_prepost_mono_relation
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (fsInit : ProbComp τ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT τ ProbComp))
    {relSource relTransfer relTarget : Set (StmtIn × WitIn)}
    (hpre : relTransfer ⊆ relSource) (hpost : relTarget ⊆ relTransfer)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hTransfer : fiatShamir_hvzkTransferResidual init impl fsInit fsImpl relTransfer R)
    (hHVZK : Reduction.isHVZK init impl relSource R) :
    Reduction.isHVZK fsInit fsImpl relTarget R.fiatShamir :=
  (fiatShamir_isHVZK_of_transfer_pre_mono_relation init impl fsInit fsImpl hpre R
    hTransfer hHVZK).mono_relation hpost

/-- Basic Fiat-Shamir statistical HVZK at any target error from a perfect transfer residual stated
on an intermediate relation, with both source and target relation transport. -/
theorem fiatShamir_isStatHVZK_of_transfer_prepost_mono_relation_error
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (fsInit : ProbComp τ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT τ ProbComp))
    {relSource relTransfer relTarget : Set (StmtIn × WitIn)}
    (hpre : relTransfer ⊆ relSource) (hpost : relTarget ⊆ relTransfer)
    (ε : ℝ≥0)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hTransfer : fiatShamir_hvzkTransferResidual init impl fsInit fsImpl relTransfer R)
    (hHVZK : Reduction.isHVZK init impl relSource R) :
    Reduction.isStatHVZK fsInit fsImpl relTarget R.fiatShamir ε :=
  (fiatShamir_isHVZK_of_transfer_prepost_mono_relation init impl fsInit fsImpl hpre hpost R
    hTransfer hHVZK).isStatHVZK ε

/-- A zero-error statistical Fiat-Shamir transfer residual preserves perfect HVZK after first
restricting the source relation and then restricting the Fiat-Shamir conclusion. -/
theorem fiatShamir_isHVZK_of_HVZK_zero_prepost_mono_relation
    (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (fsInit : ProbComp τ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT τ ProbComp))
    {relSource relTransfer relTarget : Set (StmtIn × WitIn)}
    (hpre : relTransfer ⊆ relSource) (hpost : relTarget ⊆ relTransfer)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hTransfer :
      fiatShamir_statisticalHVZKTransferResidual init impl fsInit fsImpl relTransfer 0 R)
    (hHVZK : Reduction.isHVZK init impl relSource R) :
    Reduction.isHVZK fsInit fsImpl relTarget R.fiatShamir :=
  (fiatShamir_isHVZK_of_HVZK_zero_pre_mono_relation init impl fsInit fsImpl hpre R
    hTransfer hHVZK).mono_relation hpost

/-- A zero-error statistical Fiat-Shamir transfer residual gives statistical HVZK at any target
error after source-side and target-side relation transport. -/
theorem fiatShamir_isStatHVZK_of_HVZK_zero_prepost_mono_relation
    (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (fsInit : ProbComp τ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT τ ProbComp))
    {relSource relTransfer relTarget : Set (StmtIn × WitIn)}
    (hpre : relTransfer ⊆ relSource) (hpost : relTarget ⊆ relTransfer)
    (ε : ℝ≥0)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hTransfer :
      fiatShamir_statisticalHVZKTransferResidual init impl fsInit fsImpl relTransfer 0 R)
    (hHVZK : Reduction.isHVZK init impl relSource R) :
    Reduction.isStatHVZK fsInit fsImpl relTarget R.fiatShamir ε :=
  (fiatShamir_isHVZK_of_HVZK_zero_prepost_mono_relation init impl fsInit fsImpl hpre hpost R
    hTransfer hHVZK).isStatHVZK ε

/-- Basic Fiat-Shamir statistical HVZK from a source zero-error statistical HVZK proof. The
source proof is first converted back to perfect HVZK, restricted to the transfer relation, and
then fed to the statistical simulator-transfer residual. -/
theorem fiatShamir_isStatHVZK_of_sourceStatHVZK_zero_pre_mono_relation
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (fsInit : ProbComp τ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT τ ProbComp))
    {relSource relTransfer : Set (StmtIn × WitIn)} (hsub : relTransfer ⊆ relSource)
    (ε : ℝ≥0)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hTransfer :
      fiatShamir_statisticalHVZKTransferResidual init impl fsInit fsImpl relTransfer ε R)
    (hSource : Reduction.isStatHVZK init impl relSource R 0) :
    Reduction.isStatHVZK fsInit fsImpl relTransfer R.fiatShamir ε :=
  fiatShamir_isStatHVZK_of_HVZK_pre_mono_relation init impl fsInit fsImpl hsub ε R
    hTransfer (_root_.Reduction.isStatHVZK_zero.isHVZK hSource)

/-- Source zero-error statistical HVZK with source-side relation transport, followed by target-side
relation restriction and error relaxation after applying the Fiat-Shamir statistical transfer
residual. -/
theorem fiatShamir_isStatHVZK_of_sourceStatHVZK_zero_prepost_mono_relation_error
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (fsInit : ProbComp τ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT τ ProbComp))
    {relSource relTransfer relTarget : Set (StmtIn × WitIn)}
    (hpre : relTransfer ⊆ relSource) (hpost : relTarget ⊆ relTransfer)
    {ε₁ ε₂ : ℝ≥0}
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hTransfer :
      fiatShamir_statisticalHVZKTransferResidual init impl fsInit fsImpl relTransfer ε₁ R)
    (hle : ε₁ ≤ ε₂)
    (hSource : Reduction.isStatHVZK init impl relSource R 0) :
    Reduction.isStatHVZK fsInit fsImpl relTarget R.fiatShamir ε₂ :=
  fiatShamir_isStatHVZK_of_HVZK_prepost_mono_relation_error init impl fsInit fsImpl
    hpre hpost R hTransfer hle (_root_.Reduction.isStatHVZK_zero.isHVZK hSource)

/-- Basic Fiat-Shamir perfect HVZK from a perfect transfer residual and a source zero-error
statistical HVZK proof on a larger relation. -/
theorem fiatShamir_isHVZK_of_transfer_sourceStatHVZK_zero_pre_mono_relation
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (fsInit : ProbComp τ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT τ ProbComp))
    {relSource relTransfer : Set (StmtIn × WitIn)} (hsub : relTransfer ⊆ relSource)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hTransfer : fiatShamir_hvzkTransferResidual init impl fsInit fsImpl relTransfer R)
    (hSource : Reduction.isStatHVZK init impl relSource R 0) :
    Reduction.isHVZK fsInit fsImpl relTransfer R.fiatShamir :=
  fiatShamir_isHVZK_of_transfer_pre_mono_relation init impl fsInit fsImpl hsub R hTransfer
    (_root_.Reduction.isStatHVZK_zero.isHVZK hSource)

/-- Basic Fiat-Shamir perfect HVZK from a perfect transfer residual, with source zero-error
statistical HVZK converted to perfect HVZK before the transfer and the conclusion restricted to a
target subrelation. -/
theorem fiatShamir_isHVZK_of_transfer_sourceStatHVZK_zero_prepost_mono_relation
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (fsInit : ProbComp τ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT τ ProbComp))
    {relSource relTransfer relTarget : Set (StmtIn × WitIn)}
    (hpre : relTransfer ⊆ relSource) (hpost : relTarget ⊆ relTransfer)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hTransfer : fiatShamir_hvzkTransferResidual init impl fsInit fsImpl relTransfer R)
    (hSource : Reduction.isStatHVZK init impl relSource R 0) :
    Reduction.isHVZK fsInit fsImpl relTarget R.fiatShamir :=
  fiatShamir_isHVZK_of_transfer_prepost_mono_relation init impl fsInit fsImpl
    hpre hpost R hTransfer (_root_.Reduction.isStatHVZK_zero.isHVZK hSource)

/-- A zero-error statistical Fiat-Shamir transfer residual gives perfect HVZK when the source
relation is only known through zero-error statistical HVZK on a larger relation. -/
theorem fiatShamir_isHVZK_of_transfer_zero_sourceStatHVZK_zero_pre_mono_relation
    (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (fsInit : ProbComp τ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT τ ProbComp))
    {relSource relTransfer : Set (StmtIn × WitIn)} (hsub : relTransfer ⊆ relSource)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hTransfer :
      fiatShamir_statisticalHVZKTransferResidual init impl fsInit fsImpl relTransfer 0 R)
    (hSource : Reduction.isStatHVZK init impl relSource R 0) :
    Reduction.isHVZK fsInit fsImpl relTransfer R.fiatShamir :=
  fiatShamir_isHVZK_of_HVZK_zero_pre_mono_relation init impl fsInit fsImpl hsub R hTransfer
    (_root_.Reduction.isStatHVZK_zero.isHVZK hSource)

/-- A zero-error statistical Fiat-Shamir transfer residual gives perfect HVZK after source
zero-error conversion, source-side relation transport, and target-side relation restriction. -/
theorem fiatShamir_isHVZK_of_transfer_zero_sourceStatHVZK_zero_prepost_mono_relation
    (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (fsInit : ProbComp τ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT τ ProbComp))
    {relSource relTransfer relTarget : Set (StmtIn × WitIn)}
    (hpre : relTransfer ⊆ relSource) (hpost : relTarget ⊆ relTransfer)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hTransfer :
      fiatShamir_statisticalHVZKTransferResidual init impl fsInit fsImpl relTransfer 0 R)
    (hSource : Reduction.isStatHVZK init impl relSource R 0) :
    Reduction.isHVZK fsInit fsImpl relTarget R.fiatShamir :=
  fiatShamir_isHVZK_of_HVZK_zero_prepost_mono_relation init impl fsInit fsImpl
    hpre hpost R hTransfer (_root_.Reduction.isStatHVZK_zero.isHVZK hSource)

/-- A zero-error statistical Fiat-Shamir transfer residual gives statistical HVZK at any target
error after source zero-error conversion and both relation transports. -/
theorem fiatShamir_isStatHVZK_of_transfer_zero_sourceStatHVZK_zero_prepost_mono_relation
    (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (fsInit : ProbComp τ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT τ ProbComp))
    {relSource relTransfer relTarget : Set (StmtIn × WitIn)}
    (hpre : relTransfer ⊆ relSource) (hpost : relTarget ⊆ relTransfer)
    (ε : ℝ≥0)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hTransfer :
      fiatShamir_statisticalHVZKTransferResidual init impl fsInit fsImpl relTransfer 0 R)
    (hSource : Reduction.isStatHVZK init impl relSource R 0) :
    Reduction.isStatHVZK fsInit fsImpl relTarget R.fiatShamir ε :=
  (fiatShamir_isHVZK_of_transfer_zero_sourceStatHVZK_zero_prepost_mono_relation
    init impl fsInit fsImpl hpre hpost R hTransfer hSource).isStatHVZK ε

/-- Basic Fiat-Shamir statistical HVZK from a fixed-simulator zero-error statistical source proof.
The source proof is first restricted to the transfer relation and converted back to perfect HVZK
for the same simulator. -/
theorem fiatShamir_isStatHVZK_of_sourceStatHVZK_zero_sim_pre_mono_relation
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (fsInit : ProbComp τ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT τ ProbComp))
    {relSource relTransfer : Set (StmtIn × WitIn)} (hsub : relTransfer ⊆ relSource)
    {sim : Reduction.TranscriptSimulator oSpec StmtIn pSpec} (ε : ℝ≥0)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hTransfer :
      fiatShamir_statisticalHVZKTransferResidual init impl fsInit fsImpl relTransfer ε R)
    (hSource : Reduction.statisticalHVZK init impl relSource R sim 0) :
    Reduction.isStatHVZK fsInit fsImpl relTransfer R.fiatShamir ε :=
  fiatShamir_isStatHVZK_of_HVZK init impl fsInit fsImpl relTransfer ε R hTransfer
    ⟨sim, _root_.Reduction.statisticalHVZK_zero.perfectHVZK_mono_relation
      (rel' := relTransfer) hSource hsub⟩

/-- Fixed-simulator source zero-error statistical HVZK with source-side relation transport,
followed by target-side relation restriction and error relaxation after the Fiat-Shamir
statistical transfer residual. -/
theorem fiatShamir_isStatHVZK_of_sourceStatHVZK_zero_sim_prepost_mono_relation_error
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (fsInit : ProbComp τ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT τ ProbComp))
    {relSource relTransfer relTarget : Set (StmtIn × WitIn)}
    (hpre : relTransfer ⊆ relSource) (hpost : relTarget ⊆ relTransfer)
    {sim : Reduction.TranscriptSimulator oSpec StmtIn pSpec} {ε₁ ε₂ : ℝ≥0}
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hTransfer :
      fiatShamir_statisticalHVZKTransferResidual init impl fsInit fsImpl relTransfer ε₁ R)
    (hle : ε₁ ≤ ε₂)
    (hSource : Reduction.statisticalHVZK init impl relSource R sim 0) :
    Reduction.isStatHVZK fsInit fsImpl relTarget R.fiatShamir ε₂ :=
  (fiatShamir_isStatHVZK_of_HVZK init impl fsInit fsImpl relTransfer ε₁ R hTransfer
    ⟨sim, _root_.Reduction.statisticalHVZK_zero.perfectHVZK_mono_relation
      (rel' := relTransfer) hSource hpre⟩).mono_relation_error hpost hle

/-- Basic Fiat-Shamir perfect HVZK from a perfect transfer residual and a fixed-simulator
zero-error statistical source proof on a larger relation. -/
theorem fiatShamir_isHVZK_of_transfer_sourceStatHVZK_zero_sim_pre_mono_relation
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (fsInit : ProbComp τ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT τ ProbComp))
    {relSource relTransfer : Set (StmtIn × WitIn)} (hsub : relTransfer ⊆ relSource)
    {sim : Reduction.TranscriptSimulator oSpec StmtIn pSpec}
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hTransfer : fiatShamir_hvzkTransferResidual init impl fsInit fsImpl relTransfer R)
    (hSource : Reduction.statisticalHVZK init impl relSource R sim 0) :
    Reduction.isHVZK fsInit fsImpl relTransfer R.fiatShamir :=
  fiatShamir_isHVZK_of_transfer init impl fsInit fsImpl relTransfer R hTransfer
    ⟨sim, _root_.Reduction.statisticalHVZK_zero.perfectHVZK_mono_relation
      (rel' := relTransfer) hSource hsub⟩

/-- Basic Fiat-Shamir perfect HVZK from a perfect transfer residual, with fixed-simulator
zero-error source conversion before transfer and target-side relation restriction after transfer.
-/
theorem fiatShamir_isHVZK_of_transfer_sourceStatHVZK_zero_sim_prepost_mono_relation
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (fsInit : ProbComp τ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT τ ProbComp))
    {relSource relTransfer relTarget : Set (StmtIn × WitIn)}
    (hpre : relTransfer ⊆ relSource) (hpost : relTarget ⊆ relTransfer)
    {sim : Reduction.TranscriptSimulator oSpec StmtIn pSpec}
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hTransfer : fiatShamir_hvzkTransferResidual init impl fsInit fsImpl relTransfer R)
    (hSource : Reduction.statisticalHVZK init impl relSource R sim 0) :
    Reduction.isHVZK fsInit fsImpl relTarget R.fiatShamir :=
  (fiatShamir_isHVZK_of_transfer init impl fsInit fsImpl relTransfer R hTransfer
    ⟨sim, _root_.Reduction.statisticalHVZK_zero.perfectHVZK_mono_relation
      (rel' := relTransfer) hSource hpre⟩).mono_relation hpost

/-- A zero-error statistical Fiat-Shamir transfer residual gives perfect HVZK from a
fixed-simulator zero-error statistical source proof on a larger relation. -/
theorem fiatShamir_isHVZK_of_transfer_zero_sourceStatHVZK_zero_sim_pre_mono_relation
    (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (fsInit : ProbComp τ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT τ ProbComp))
    {relSource relTransfer : Set (StmtIn × WitIn)} (hsub : relTransfer ⊆ relSource)
    {sim : Reduction.TranscriptSimulator oSpec StmtIn pSpec}
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hTransfer :
      fiatShamir_statisticalHVZKTransferResidual init impl fsInit fsImpl relTransfer 0 R)
    (hSource : Reduction.statisticalHVZK init impl relSource R sim 0) :
    Reduction.isHVZK fsInit fsImpl relTransfer R.fiatShamir :=
  fiatShamir_isHVZK_of_HVZK_zero init impl fsInit fsImpl relTransfer R hTransfer
    ⟨sim, _root_.Reduction.statisticalHVZK_zero.perfectHVZK_mono_relation
      (rel' := relTransfer) hSource hsub⟩

/-- A zero-error statistical Fiat-Shamir transfer residual gives perfect HVZK after fixed-simulator
zero-error source conversion, source-side relation transport, and target-side restriction. -/
theorem fiatShamir_isHVZK_of_transfer_zero_sourceStatHVZK_zero_sim_prepost_mono_relation
    (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (fsInit : ProbComp τ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT τ ProbComp))
    {relSource relTransfer relTarget : Set (StmtIn × WitIn)}
    (hpre : relTransfer ⊆ relSource) (hpost : relTarget ⊆ relTransfer)
    {sim : Reduction.TranscriptSimulator oSpec StmtIn pSpec}
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hTransfer :
      fiatShamir_statisticalHVZKTransferResidual init impl fsInit fsImpl relTransfer 0 R)
    (hSource : Reduction.statisticalHVZK init impl relSource R sim 0) :
    Reduction.isHVZK fsInit fsImpl relTarget R.fiatShamir :=
  (fiatShamir_isHVZK_of_HVZK_zero init impl fsInit fsImpl relTransfer R hTransfer
    ⟨sim, _root_.Reduction.statisticalHVZK_zero.perfectHVZK_mono_relation
      (rel' := relTransfer) hSource hpre⟩).mono_relation hpost

/-- A zero-error statistical Fiat-Shamir transfer residual gives statistical HVZK at any target
error after fixed-simulator zero-error source conversion and both relation transports. -/
theorem fiatShamir_isStatHVZK_of_transfer_zero_sourceStatHVZK_zero_sim_prepost_mono_relation
    (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (fsInit : ProbComp τ)
    (fsImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) (StateT τ ProbComp))
    {relSource relTransfer relTarget : Set (StmtIn × WitIn)}
    (hpre : relTransfer ⊆ relSource) (hpost : relTarget ⊆ relTransfer)
    {sim : Reduction.TranscriptSimulator oSpec StmtIn pSpec} (ε : ℝ≥0)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hTransfer :
      fiatShamir_statisticalHVZKTransferResidual init impl fsInit fsImpl relTransfer 0 R)
    (hSource : Reduction.statisticalHVZK init impl relSource R sim 0) :
    Reduction.isStatHVZK fsInit fsImpl relTarget R.fiatShamir ε :=
  (fiatShamir_isHVZK_of_transfer_zero_sourceStatHVZK_zero_sim_prepost_mono_relation
    init impl fsInit fsImpl hpre hpost R hTransfer hSource).isStatHVZK ε

#print axioms fiatShamir_isStatHVZK_of_HVZK_pre_mono_relation
#print axioms fiatShamir_isStatHVZK_of_HVZK_pre_mono_relation_error
#print axioms fiatShamir_isHVZK_of_transfer_pre_mono_relation
#print axioms fiatShamir_isStatHVZK_of_transfer_pre_mono_relation
#print axioms fiatShamir_isHVZK_of_HVZK_zero_pre_mono_relation
#print axioms fiatShamir_isStatHVZK_of_HVZK_zero_pre_mono_relation
#print axioms fiatShamir_isStatHVZK_of_HVZK_prepost_mono_relation_error
#print axioms fiatShamir_isHVZK_of_transfer_prepost_mono_relation
#print axioms fiatShamir_isStatHVZK_of_transfer_prepost_mono_relation_error
#print axioms fiatShamir_isHVZK_of_HVZK_zero_prepost_mono_relation
#print axioms fiatShamir_isStatHVZK_of_HVZK_zero_prepost_mono_relation
#print axioms fiatShamir_isStatHVZK_of_sourceStatHVZK_zero_pre_mono_relation
#print axioms fiatShamir_isStatHVZK_of_sourceStatHVZK_zero_prepost_mono_relation_error
#print axioms fiatShamir_isHVZK_of_transfer_sourceStatHVZK_zero_pre_mono_relation
#print axioms fiatShamir_isHVZK_of_transfer_sourceStatHVZK_zero_prepost_mono_relation
#print axioms fiatShamir_isHVZK_of_transfer_zero_sourceStatHVZK_zero_pre_mono_relation
#print axioms fiatShamir_isHVZK_of_transfer_zero_sourceStatHVZK_zero_prepost_mono_relation
#print axioms fiatShamir_isStatHVZK_of_transfer_zero_sourceStatHVZK_zero_prepost_mono_relation
#print axioms fiatShamir_isStatHVZK_of_sourceStatHVZK_zero_sim_pre_mono_relation
#print axioms fiatShamir_isStatHVZK_of_sourceStatHVZK_zero_sim_prepost_mono_relation_error
#print axioms fiatShamir_isHVZK_of_transfer_sourceStatHVZK_zero_sim_pre_mono_relation
#print axioms fiatShamir_isHVZK_of_transfer_sourceStatHVZK_zero_sim_prepost_mono_relation
#print axioms fiatShamir_isHVZK_of_transfer_zero_sourceStatHVZK_zero_sim_pre_mono_relation
#print axioms fiatShamir_isHVZK_of_transfer_zero_sourceStatHVZK_zero_sim_prepost_mono_relation
#print axioms fiatShamir_isStatHVZK_of_transfer_zero_sourceStatHVZK_zero_sim_prepost_mono_relation

end Reduction
