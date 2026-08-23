/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Security.SubPhaseSplit
import ArkLib.OracleReduction.Composition.Sequential.AppendCompletenessMsgKeystone

/-!
# LogUp Protocol 2 — the append-completeness blocker CLOSED (message seam, issue #13)

`Logup.AppendCompletenessResidual` (`Security/SubPhaseSplit.lean`) — the sequential-composition
completeness brick of issue #13 — is **no longer a residual**: LogUp's outer → sumcheck seam is a
prover message (the embedded sumcheck opens with the round-0 univariate polynomial), so the proven
unconditional message-seam keystone `OracleReduction.appendCompletenessResidual_msg`
(`Composition/Sequential/AppendCompletenessMsgKeystone.lean`) discharges it from the two sub-phase
completeness facts plus `0 < n` and the three standard honest-`impl` side conditions
(state-preserving / never-failing / value-blind — the same triple carried by the proven soundness
keystone `Verifier.append_soundness_msg`).

The completeness analogue of `LogupSoundnessMsgSeam.lean`. The three structural seam facts
(`length_pos` / `seam_dir` / `first_dir`) are re-proved here in the `Logup.CompletenessSeam`
namespace rather than imported: they live in the soundness close cone
(`LogupSoundnessMsgSeam.lean`), which cannot be co-imported with the completeness close cone
(`SumcheckCompletenessClose.lean`) due to the documented anonymous-`local instance` environment
clash (`Issue13Status.lean`), and this file must remain importable from the completeness side.

## Headline

* `Logup.appendCompletenessResidual_msgSeam` — the exact `AppendCompletenessResidual` of
  `SubPhaseSplit.lean`, discharged.
* `Logup.logup_completeness_msgSeam` — LogUp Protocol 2 completeness with **both** the outer half
  and the append blocker closed: residual surface = `{hSumcheck}` (the embedded-sumcheck
  completeness half) plus `NeverFail init`, `0 < n`, and the honest-`impl` side conditions.

Caveat on the remaining `hSumcheck`: as currently *stated*, `SumcheckCompletenessResidual`
ranges over `midRelation = Set.univ` and is therefore unsatisfiable in general (the completeness
twin of the fixed soundness `midLanguage` degeneracy noted in the 2026-06-09 issue-#13 audit).
The append discharge below is relation-agnostic (the keystone
`OracleReduction.append_completeness_msg` is generic in the relations), so it survives the
upcoming corrected claim-true `midRelation` unchanged; only the *consumer* statements
re-elaborate against the corrected relation.

No `sorry`, no new axioms.
-/

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal ENNReal

namespace Logup

section CompletenessMsgSeam

variable {ι : Type} (oSpec : OracleSpec ι) [oSpec.Fintype] [oSpec.Inhabited]
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)]
  [SampleableType F]
variable (n M : ℕ)
variable (params : ProtocolParams M)
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- `F` is inhabited (by `0`), matching the local instances used throughout the LogUp security
development. -/
local instance instInhabitedFieldCompletenessSeam : Inhabited F := ⟨0⟩

namespace CompletenessSeam

/-- The embedded sumcheck phase has positive length whenever `0 < n`. (Local copy of the
soundness-cone fact, see the module docstring.) -/
theorem length_pos (hn : 0 < n) : 0 < Fin.vsum (fun _ : Fin n => 2) := by
  cases n with
  | zero => omega
  | succ n' => simp [Fin.vsum_succ]

omit [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)] [SampleableType F] in
/-- The embedded sumcheck phase opens with a prover message: round 0 of
`Sumcheck.Spec.pSpec` is the prover's univariate polynomial. (Local copy.) -/
theorem first_dir (hn : 0 < n) :
    (logupSumcheckPSpec F n M params).dir
      ⟨0, length_pos n hn⟩ = .P_to_V := by
  cases n with
  | zero => omega
  | succ n' =>
    rw [show (logupSumcheckPSpec F (n' + 1) M params).dir =
        Fin.vflatten (fun _ : Fin (n' + 1) =>
          (Sumcheck.Spec.SingleRound.pSpec F (logupSumcheckDegree M params)).dir) from
      ProtocolSpec.seqCompose_dir]
    rw [Fin.vflatten_succ]
    rw [Fin.vappend_left_of_lt _ _ _ (by norm_num)]
    rfl

omit [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)] [SampleableType F] in
/-- The outer → sumcheck seam round of the full LogUp transcript is a prover message.
(Local copy.) -/
theorem seam_dir (hn : 0 < n) :
    ((outerPSpec F n params) ++ₚ (logupSumcheckPSpec F n M params)).dir
      ⟨4, by have := length_pos n hn; omega⟩ = .P_to_V := by
  cases n with
  | zero => omega
  | succ n' =>
    change Fin.vappend (outerPSpec F (n' + 1) params).dir
      (logupSumcheckPSpec F (n' + 1) M params).dir _ = _
    rw [Fin.vappend_right_of_not_lt _ _ _ (by norm_num)]
    exact first_dir F (n' + 1) M params (by omega)

end CompletenessSeam

/-- **The LogUp append-completeness residual is a theorem (message seam).**

The exact `AppendCompletenessResidual` of `SubPhaseSplit.lean`, discharged by the unconditional
oracle-level message-seam keystone `OracleReduction.appendCompletenessResidual_msg`: LogUp's
outer → sumcheck seam opens with a prover message, so the appended LogUp oracle reduction is
complete with the additive error `logupCompletenessError F n + 0` from the two sub-phase
completeness facts. Remaining inputs: `0 < n` and the three honest-`impl` side conditions. -/
theorem appendCompletenessResidual_msgSeam
    (hn : 0 < n)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    (himplVB : ∀ (t : oSpec.Domain) (s s' : σ),
      evalDist ((impl t).run' s) = evalDist ((impl t).run' s'))
    (hOuter : OuterCompletenessResidual oSpec F n M params init impl)
    (hSumcheck : SumcheckCompletenessResidual oSpec F n M params init impl) :
    AppendCompletenessResidual oSpec F n M params init impl hOuter hSumcheck :=
  OracleReduction.appendCompletenessResidual_msg.{0, 0}
    (outerOracleReduction oSpec F n M params)
    (sumcheckOracleReduction oSpec F n M params)
    hOuter hSumcheck
    (CompletenessSeam.length_pos n hn)
    (CompletenessSeam.seam_dir F n M params hn)
    (CompletenessSeam.first_dir F n M params hn)
    himplSP himplNF himplVB

/-- **LogUp Protocol 2 completeness with the outer half and the append blocker both closed
(issue #13).**

The full LogUp oracle reduction is complete with error `logupCompletenessError F n`. The outer
completeness half is the proven `outerCompletenessResidual_of_neverFail`; the append-composition
brick is the proven message-seam keystone. The honest completeness residual surface of issue #13
is now `{hSumcheck}` (the embedded-sumcheck completeness half) plus `NeverFail init`, `0 < n`,
and the three standard honest-`impl` side conditions. -/
theorem logup_completeness_msgSeam
    (hn : 0 < n) (hInit : NeverFail init)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    (himplVB : ∀ (t : oSpec.Domain) (s s' : σ),
      evalDist ((impl t).run' s) = evalDist ((impl t).run' s'))
    (hSumcheck : SumcheckCompletenessResidual oSpec F n M params init impl) :
    (logupOracleReduction oSpec F n M params).completeness init impl
      (inputRelation F n M) outputRelation (logupCompletenessError F n) :=
  logup_completeness_of_sumcheck_append oSpec F n M params init impl hInit hSumcheck
    (appendCompletenessResidual_msgSeam oSpec F n M params init impl hn
      himplSP himplNF himplVB
      (outerCompletenessResidual_of_neverFail oSpec F n M params init impl hInit) hSumcheck)

end CompletenessMsgSeam

end Logup

/-! ## Axiom audit (must be axiom-clean: `propext`, `Classical.choice`, `Quot.sound` only) -/
#print axioms Logup.appendCompletenessResidual_msgSeam
#print axioms Logup.logup_completeness_msgSeam
