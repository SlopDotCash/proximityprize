/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Security.SubPhaseSplit
import ArkLib.ProofSystem.Logup.Security.OuterMaliciousSoundness

/-!
# Logup facts and conditional protocol interfaces

The old input-only sumcheck rejection, zero-error closure, and dependent unconditional soundness
capstones were retired during canonical message-polynomial integration. This module retains its
independent outer-phase mathematics and explicit conditional protocol interfaces. It does not
claim the retired embedded-sumcheck soundness completion. Exact former commands and the checked
finite regression are recorded in
`scripts/integration/sumcheck-message-semantics-retirements.json`.
-/

open scoped NNReal ENNReal
open OracleComp OracleSpec ProtocolSpec

-- Preserve the original whole-value equality observation within this module.
private local instance (A : Type) : MeasurableSpace A := ⊤
private local instance (A : Type) : @DiscreteMeasurableSpace A ⊤ :=
  ⟨fun _ => True.intro⟩

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
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), prFail ((impl t).run s) = 0)
    (himplVB : ∀ (t : oSpec.Domain) (s s' : σ),
      evalDist ((impl t).run' s) = evalDist ((impl t).run' s')) :
    OuterSoundnessResidual oSpec F n M params init impl :=
  outerVerifier_soundness_mid oSpec F n M params init impl hpole hnK himplSP himplNF himplVB

end ResidualDischarge

end Logup

/-! ### Axiom audit (issue #13 named soundness residual dischargers) -/

#print axioms Logup.outerSoundnessResidual_holds
