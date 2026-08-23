/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Security.SubPhaseSplit
import ArkLib.ProofSystem.Logup.Security.OuterMaliciousSoundness

/-!
# LogUp Protocol 2 — discharging the named soundness residual `Prop`s (issue #13)

`Security/SubPhaseSplit.lean` names the split soundness residual surface of LogUp Protocol 2:

* `OuterSoundnessResidual` — the outer phase is sound from the input language into the
  zero-mid-claim `midLanguage` with the paper error `outerSoundnessError`;
* `SumcheckSoundnessResidual` — the embedded sumcheck is sound from `midLanguage` into the
  output language;
* `AppendSoundnessResidual` — the composed `logupVerifier` headline soundness;
* `SubPhaseSoundnessResidual` / `LogupSoundnessBrickResidual` — the bundles.

All of these are now **theorems**.  This file plugs the proven dischargers into the named
residual `Prop`s, closing the residual surface they name:

* `outerSoundnessResidual_holds` — from `outerVerifier_soundness_mid`
  (`OuterMaliciousSoundness.lean`): the claim-based two-challenge RBR state function
  (`outerMidStateFunction`) whose round-1 flip is the per-`m` bad-challenge count
  (`outerBadChallenges_card_le`) and whose round-3 flip is the `(z, λ)` Schwartz–Zippel count
  (`card_filter_claimZero_mul_card_le` + `claim_not_identicallyZero`), composed with the proven
  marginal bridge `Verifier.marginalBridge_holds`.
* `sumcheckSoundnessResidual_holds_pointwise` — re-export of the discharged
  `sumcheckSoundnessResidual_pointwise` (error-`0` RBR via pointwise rejection).
* `subPhaseSoundnessResidual_holds` — the conjunction of the two.
* `appendSoundnessResidual_holds` — from `logup_soundness_end_to_end` (message-seam append +
  oracle-routing fusion on top of the two halves).
* `logupSoundnessBrickResidual_holds` — the full split-brick bundle.

Remaining hypotheses are *side conditions only*, not protocol obligations:

* `hn : 0 < n` (nonempty cube), `hpole : 2 ^ n < Fintype.card F` (field beats the hypercube),
  `hnK : n ≤ params.numGroups` (enough batching groups for the `(z, λ)` Schwartz–Zippel budget
  `(n + 1)/|F| ≤ (numGroups + 1)/|F|` of the paper error shape);
* `himplSP` / `himplNF` / `himplVB` — the standard state-preserving, never-failing,
  value-blind shared-oracle implementation conditions consumed by the marginal bridge.

No `sorry`; axiom audit at the bottom.
-/

open scoped NNReal ENNReal
open OracleComp OracleSpec ProtocolSpec

namespace Logup

section ResidualDischarge

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)]
  [SampleableType F]
variable (n M : ℕ)
variable (params : ProtocolParams M)
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- `F` is inhabited (by `0`), matching the local instance used when the residual `Prop`s were
named in `SubPhaseSplit.lean`. -/
local instance instInhabitedFieldResidualDischarge : Inhabited F := ⟨0⟩

/-- **`OuterSoundnessResidual` is a theorem** (issue #13, outer half): the outer LogUp verifier
is sound from the input language into the zero-mid-claim `midLanguage` with the paper error
`outerSoundnessError`, via the claim-based two-challenge RBR state function and the proven
marginal bridge (`outerVerifier_soundness_mid`). -/
theorem outerSoundnessResidual_holds
    (hpole : 2 ^ n < Fintype.card F) (hnK : n ≤ params.numGroups)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    (himplVB : ∀ (t : oSpec.Domain) (s s' : σ),
      evalDist ((impl t).run' s) = evalDist ((impl t).run' s')) :
    OuterSoundnessResidual oSpec F n M params init impl :=
  outerVerifier_soundness_mid oSpec F n M params init impl hpole hnK himplSP himplNF himplVB

/-- **`SumcheckSoundnessResidual` is a theorem** (issue #13, embedded-sumcheck half): re-export
of the discharged pointwise route at the `SubPhaseSplit` naming site. -/
theorem sumcheckSoundnessResidual_holds_pointwise [oSpec.Fintype] [oSpec.Inhabited]
    (sumcheckSoundnessError : ℝ≥0) (hn : 0 < n)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    (himplVB : ∀ (t : oSpec.Domain) (s s' : σ),
      evalDist ((impl t).run' s) = evalDist ((impl t).run' s')) :
    SumcheckSoundnessResidual oSpec F n M params init impl sumcheckSoundnessError :=
  sumcheckSoundnessResidual_pointwise oSpec F n M params hn sumcheckSoundnessError
    himplSP himplNF himplVB

/-- **`SubPhaseSoundnessResidual` is a theorem** (issue #13): both sub-phase soundness halves of
the LogUp composition hold — the outer half by the claim-based RBR route, the embedded-sumcheck
half by the pointwise route. -/
theorem subPhaseSoundnessResidual_holds [oSpec.Fintype] [oSpec.Inhabited]
    (sumcheckSoundnessError : ℝ≥0) (hn : 0 < n)
    (hpole : 2 ^ n < Fintype.card F) (hnK : n ≤ params.numGroups)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    (himplVB : ∀ (t : oSpec.Domain) (s s' : σ),
      evalDist ((impl t).run' s) = evalDist ((impl t).run' s')) :
    SubPhaseSoundnessResidual oSpec F n M params init impl sumcheckSoundnessError :=
  ⟨outerSoundnessResidual_holds oSpec F n M params init impl hpole hnK
      himplSP himplNF himplVB,
    sumcheckSoundnessResidual_holds_pointwise oSpec F n M params init impl
      sumcheckSoundnessError hn himplSP himplNF himplVB⟩

/-- **`AppendSoundnessResidual` is a theorem** (issue #13): the composed `logupVerifier` headline
soundness, from `logup_soundness_end_to_end` (the two discharged halves + the proven message-seam
append keystone + the proven oracle-routing fusion). -/
theorem appendSoundnessResidual_holds [oSpec.Fintype] [oSpec.Inhabited]
    (sumcheckSoundnessError : ℝ≥0) (hn : 0 < n)
    (hpole : 2 ^ n < Fintype.card F) (hnK : n ≤ params.numGroups)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    (himplVB : ∀ (t : oSpec.Domain) (s s' : σ),
      evalDist ((impl t).run' s) = evalDist ((impl t).run' s')) :
    AppendSoundnessResidual oSpec F n M params init impl sumcheckSoundnessError :=
  logup_soundness_end_to_end oSpec F n M params init impl sumcheckSoundnessError hn
    hpole hnK himplSP himplNF himplVB

/-- **`LogupSoundnessBrickResidual` is a theorem** (issue #13): the fully split soundness
residual surface — outer half, embedded-sumcheck half, and append-composition headline — holds
under the standard side conditions only. -/
theorem logupSoundnessBrickResidual_holds [oSpec.Fintype] [oSpec.Inhabited]
    (sumcheckSoundnessError : ℝ≥0) (hn : 0 < n)
    (hpole : 2 ^ n < Fintype.card F) (hnK : n ≤ params.numGroups)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    (himplVB : ∀ (t : oSpec.Domain) (s s' : σ),
      evalDist ((impl t).run' s) = evalDist ((impl t).run' s')) :
    LogupSoundnessBrickResidual oSpec F n M params init impl sumcheckSoundnessError :=
  ⟨outerSoundnessResidual_holds oSpec F n M params init impl hpole hnK
      himplSP himplNF himplVB,
    sumcheckSoundnessResidual_holds_pointwise oSpec F n M params init impl
      sumcheckSoundnessError hn himplSP himplNF himplVB,
    appendSoundnessResidual_holds oSpec F n M params init impl sumcheckSoundnessError hn
      hpole hnK himplSP himplNF himplVB⟩

end ResidualDischarge

end Logup

/-! ### Axiom audit (issue #13 named soundness residual dischargers) -/

#print axioms Logup.outerSoundnessResidual_holds
#print axioms Logup.sumcheckSoundnessResidual_holds_pointwise
#print axioms Logup.subPhaseSoundnessResidual_holds
#print axioms Logup.appendSoundnessResidual_holds
#print axioms Logup.logupSoundnessBrickResidual_holds
