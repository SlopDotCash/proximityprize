/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Security.BridgeAndAppendResiduals
import ArkLib.OracleReduction.Composition.Sequential.AppendToVerifierKeystone

/-!
# Discharging the seqCompose verifier-fusion `hBridge` of multi-round sum-check (#13)

`Sumcheck.Spec.oracleReduction_perfectCompleteness_of_bridge` (in `OracleCompleteness.lean`) proves the full
multi-round sum-check perfect completeness at the **oracle** reduction level *modulo* the single
named bridge

  `hBridge : oracleReductionToReductionResidual R deg D n oSpec`
        i.e. `(oracleReduction R deg D n oSpec).toReduction = reduction R deg D n oSpec`.

That bridge was shown in `BridgeAndAppendResiduals.lean` to factor (via
`Sumcheck.Spec.oracleReductionToReductionResidual_of_binary`) as

1. the deep, **unbounded-round** verifier-side `seqCompose` fusion, fed by the binary fusion law
   `OracleVerifier.BinaryVerifierFusion oSpec`
     `(OracleVerifier.append V₁ V₂).toVerifier = Verifier.append V₁.toVerifier V₂.toVerifier`     (★)
   (the verifier analogue of `Prover.append_run`, instantiated at every round); and

2. the orthogonal, **single-round** `liftContext`-commutation fact
     `hPerRound : ∀ i, (SingleRound.oracleReduction R n deg D oSpec i).toReduction =
                       SingleRound.reduction R n deg D oSpec i`.

## What this file changes

The binary fusion `(★)` is now **PROVEN** (sorry-free, axiom-clean) as
`OracleReduction.oracleVerifier_append_toVerifier` in `AppendToVerifierKeystone.lean`. This file
discharges the named hypothesis `OracleVerifier.BinaryVerifierFusion oSpec` directly from it
(`binaryVerifierFusion_proof`), and feeds that into `oracleReductionToReductionResidual_of_binary`
to obtain the Sumcheck bridge `hBridge` from `hPerRound` *alone*
(`oracleReductionToReduction_of_perRound`).

Consequently the multi-round oracle-level completeness theorem
`oracleReduction_perfectCompleteness_uncond` no longer carries `hBridge`: the only remaining
hypothesis (besides the unchanged `hInit`/`hImplSupp` data facts of the proven
`reduction_perfectCompleteness`) is `hPerRound`, the single-round `liftContext`-commutation fact.
That fact is *orthogonal* to the seqCompose fusion — it is the per-round
`OracleVerifier.LiftContextCoherent`-gated bridge relating each round's oracle reduction's
`toReduction` to the corresponding plain reduction — and is supplied on the nose by any concrete
instantiation whose single-round lens discharges its `LiftContextCoherent` side condition (as the
LogUp / Spartan lenses do).

No `sorry`/`admit`; the one genuinely-deep residual that this file does **not** internally close is
kept as the explicit named hypothesis `hPerRound`.
-/

open ProtocolSpec OracleComp OracleSpec
open scoped NNReal

namespace Sumcheck.Spec

variable {R : Type} [CommSemiring R] [SampleableType R] [DecidableEq R] [Fintype R] [Inhabited R]
  {n : ℕ} {deg : ℕ} {m : ℕ} {D : Fin m ↪ R}
  {ι : Type} {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- **The binary verifier-fusion named residual is discharged for every oracle spec.**

`OracleVerifier.BinaryVerifierFusion oSpec` is the universally-quantified binary fusion law
`(OracleVerifier.append V₁ V₂).toVerifier = Verifier.append V₁.toVerifier V₂.toVerifier`. Its single
per-pair instance is exactly the now-proven `OracleReduction.oracleVerifier_append_toVerifier`
(`AppendToVerifierKeystone.lean`), so the universally-quantified `BinaryVerifierFusion` holds by
introducing all the type / protocol / interface data and applying that keystone. -/
theorem binaryVerifierFusion_proof (oSpec : OracleSpec ι) :
    OracleVerifier.BinaryVerifierFusion oSpec := by
  intro Stmt₁ ιₛ₁ OStmt₁ Oₛ₁ Stmt₂ ιₛ₂ OStmt₂ Oₛ₂ Stmt₃ ιₛ₃ OStmt₃ Oₛ₃
    p q pSpec₁ pSpec₂ Oₘ₁ Oₘ₂ V₁ c₁ V₂
  exact OracleReduction.oracleVerifier_append_toVerifier
    (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) V₁ V₂

set_option linter.unusedSectionVars false in
/-- **The Sumcheck `hBridge` from the per-round bridge alone.**

`oracleReductionToReductionResidual_of_binary` reduces the bridge `hBridge` to the two ingredients
`hBinaryFusion` and `hPerRound`. The first is now discharged unconditionally
(`binaryVerifierFusion_proof`), so the whole bridge follows from the single-round
`liftContext`-commutation fact `hPerRound`.

**LEGACY (audit 2026-06-10).** The target Prop `oracleReductionToReductionResidual` is
superseded and suspected false as stated (its per-round input `hPerRound` is the documented
suspected-false single-round `oracleReduction_eq_reduction`; see the note on the residual def
in `OracleCompleteness.lean`).  The binary-fusion half proven here is genuine
(`binaryVerifierFusion_proof` via `oracleVerifier_append_toVerifier`), but nothing on the live
path consumes this implication — the bridge-free apex is
`oracleReduction_perfectCompleteness_unconditional` (`OracleCompletenessUncondCorrect.lean`).
Kept as a historical reduction record. -/
theorem oracleReductionToReduction_of_perRound
    (hPerRound : ∀ i, (SingleRound.oracleReduction R n deg D oSpec i).toReduction =
      SingleRound.reduction R n deg D oSpec i) :
    oracleReductionToReductionResidual R deg D n oSpec :=
  oracleReductionToReductionResidual_of_binary (binaryVerifierFusion_proof oSpec) hPerRound

/-- **Full multi-round sum-check perfect completeness (oracle level) — no `hBridge`.**

The seqCompose verifier-fusion bridge `hBridge` of `oracleReduction_perfectCompleteness_of_bridge` is now
discharged internally from the per-round single-round bridge `hPerRound` (via the proven binary
verifier-fusion `OracleReduction.oracleVerifier_append_toVerifier` lifted along the seqCompose
induction `seqCompose_toVerifier_of_binary`). The remaining hypotheses are exactly:

* `hPerRound` — the per-round `liftContext`-commutation fact (orthogonal to the seqCompose fusion;
  supplied on the nose by any concrete single-round lens discharging its `LiftContextCoherent` side
  condition);
* `hInit` / `hImplSupp` — the `NeverFail` / support data facts already required by the proven
  `reduction_perfectCompleteness`.

No `appendToReductionResidual` / verifier-fusion `hBridge` obligation remains. -/
theorem oracleReduction_perfectCompleteness_uncond
    (hPerRound : ∀ i, (SingleRound.oracleReduction R n deg D oSpec i).toReduction =
      SingleRound.reduction R n deg D oSpec i)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β)) :
    (oracleReduction R deg D n oSpec).perfectCompleteness init impl
      (relationRound R n deg D 0) (relationRound R n deg D (Fin.last n)) :=
  oracleReduction_perfectCompleteness_of_bridge
    (oracleReductionToReduction_of_perRound hPerRound) hInit hImplSupp

end Sumcheck.Spec

#print axioms Sumcheck.Spec.binaryVerifierFusion_proof
#print axioms Sumcheck.Spec.oracleReductionToReduction_of_perRound
#print axioms Sumcheck.Spec.oracleReduction_perfectCompleteness_uncond
