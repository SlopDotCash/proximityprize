/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Security.SumcheckSoundnessPointwise
import ArkLib.ProofSystem.Logup.Security.LogupSoundnessUncond
import ArkLib.ProofSystem.Logup.Security.LogupSoundnessMsgSeam

/-!
# LogUp Protocol 2 soundness, assembled over `midLanguage` (issue #13)

The end-to-end LogUp soundness with the embedded sum-check half **discharged** (the pointwise
`sumcheckSoundnessResidual_pointwise`) and the append composition **discharged** (the proven
message-seam keystone `append_soundness_msg` + the proven oracle-routing fusion). The honest
residual surface is exactly:

* `hOuter` — the outer phase's malicious-prover soundness *into `midLanguage`* (from a bad lookup
  input, the outer phase lands a *zero* mid-claim with probability ≤ `outerSoundnessError`): the
  grand-sum batching/zero-check probabilistic argument. This is the single remaining genuine
  mathematical obligation of issue #13's soundness side.
* `0 < n` and the three standard honest-`impl` side conditions.

The mid language used throughout the seam is `midLanguage` (the zero-mid-claim language) — the
honest per-statement carrier for the lens projection soundness; the corrected
`midSoundnessProtocolLanguage` variant is *provably not* per-statement projectable (see the scope
note in `SumcheckSoundnessProjClosed.lean`), its probabilistic content belonging to `hOuter`.

No `sorry`; axiom audit at the bottom.
-/

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal ENNReal

namespace Logup

noncomputable section

variable {ι : Type} (oSpec : OracleSpec ι) [oSpec.Fintype] [oSpec.Inhabited]
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [Inhabited F] [SampleableType F]
  [Fact ((-1 : F) ≠ 1)]
variable (n M : ℕ) (params : ProtocolParams M)
variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- **LogUp Protocol 2 soundness, modulo only the outer mid-claim soundness (issue #13).**

From `hOuter` (the outer phase maps bad lookups to *zero* mid-claims with probability at most
`outerSoundnessError` — the batching/zero-check argument) plus `0 < n` and the standard
honest-`impl` side conditions, the full LogUp verifier is sound with the paper-shaped error
`logupSoundnessError = outerSoundnessError + sumcheckSoundnessError`. The embedded sum-check half
is supplied by the discharged `sumcheckSoundnessResidual_pointwise`; the append composition by the
proven message-seam keystone + oracle-routing fusion. -/
theorem logup_soundness_pointwiseSumcheck (sumcheckSoundnessError : ℝ≥0) (hn : 0 < n)
    (hOuter :
      (outerVerifier oSpec F n M params).soundness init impl
        (inputRelation F n M).language (midLanguage F n M params)
        (outerSoundnessError F n M params))
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    (himplVB : ∀ (t : oSpec.Domain) (s s' : σ),
      evalDist ((impl t).run' s) = evalDist ((impl t).run' s')) :
    (logupVerifier oSpec F n M params).soundness init impl
      (inputRelation F n M).language outputRelation.language
      (logupSoundnessError F n M params sumcheckSoundnessError) := by
  -- The discharged sum-check half (from `midLanguage`).
  have hSumcheck : (sumcheckVerifier oSpec F n M params).soundness init impl
      (midLanguage F n M params) outputRelation.language sumcheckSoundnessError :=
    sumcheckSoundnessResidual_pointwise oSpec F n M params hn sumcheckSoundnessError
      himplSP himplNF himplVB
  -- The plain appended soundness (the proven message-seam keystone is mid-language generic).
  have hPlainAppend :
      (Verifier.append (outerVerifier oSpec F n M params).toVerifier
          (sumcheckVerifier oSpec F n M params).toVerifier).soundness init impl
        (inputRelation F n M).language outputRelation.language
        (outerSoundnessError F n M params + sumcheckSoundnessError) :=
    _root_.Verifier.append_soundness_msg
      (outerVerifier oSpec F n M params).toVerifier
      (sumcheckVerifier oSpec F n M params).toVerifier
      hOuter hSumcheck
      (logupSumcheck_length_pos n hn)
      (logup_seam_dir F n M params hn)
      (logupSumcheckPSpec_first_dir F n M params hn)
      himplSP himplNF himplVB
  -- The oracle-level append residual (proven oracle-routing fusion) and the final assembly.
  have hOracle : OracleVerifier.appendSoundnessResidual (init := init) (impl := impl)
      (outerVerifier oSpec F n M params) (sumcheckVerifier oSpec F n M params)
      hOuter hSumcheck :=
    OracleVerifier.oracleAppendSoundnessResidual_of_plain.{0, 0}
      (outerVerifier oSpec F n M params) (sumcheckVerifier oSpec F n M params)
      hOuter hSumcheck hPlainAppend
  exact OracleVerifier.append_soundness.{0, 0}
    (outerVerifier oSpec F n M params) (sumcheckVerifier oSpec F n M params)
    hOuter hSumcheck hOracle

end

end Logup

/- Axiom audit. -/
#print axioms Logup.logup_soundness_pointwiseSumcheck
