/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Security.LogupSoundnessUncond
import ArkLib.OracleReduction.Composition.Sequential.AppendSoundnessMsgProof

/-!
# LogUp Protocol 2: the plain-verifier append-soundness residual is a theorem (issue #13)

`logup_soundness_uncond` (`LogupSoundnessUncond.lean`) reduced LogUp Protocol 2 soundness to the
residual set `{hOuter, hSumcheck, hPlainAppend}`, where `hPlainAppend` — the malicious-prover seam
decomposition + union bound for `Verifier.append outerVerifier.toVerifier
sumcheckVerifier.toVerifier` — was the deep open composition obligation (issue #13 blocker 3).

LogUp's seam is **message-first**: the embedded sumcheck phase opens with the prover sending the
round-0 univariate polynomial (`Sumcheck.Spec.pSpec` round 0 is `.P_to_V`).  Hence the proven
unconditional message-seam keystone `Verifier.append_soundness_msg`
(`Composition/Sequential/AppendSoundnessMsgProof.lean`, axiom-clean) applies, and `hPlainAppend`
is *discharged* — for `0 < n` — from the two per-phase soundness facts plus the standard honest
`impl` side conditions (state-preserving / never-failing / value-blind).

The headline `logup_soundness_msgSeam` therefore carries the shrunken residual surface
`{hOuter, hSumcheck}` + the three `impl` side conditions: the append-composition blocker of
issue #13 is closed on the soundness side.
-/

open OracleComp OracleSpec ProtocolSpec
open scoped ENNReal NNReal

namespace Logup

section MsgSeam

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)]
  [SampleableType F]
variable (n M : ℕ)
variable (params : ProtocolParams M)
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

local instance instInhabitedFieldMsgSeam : Inhabited F := ⟨0⟩

/-! ### Structural seam facts -/

/-- The embedded sumcheck phase has positive length whenever `0 < n`. -/
theorem logupSumcheck_length_pos (hn : 0 < n) :
    0 < Fin.vsum (fun _ : Fin n => 2) := by
  cases n with
  | zero => omega
  | succ n' => simp [Fin.vsum_succ]

omit [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)] [SampleableType F] in
/-- The embedded sumcheck phase opens with a prover message: round 0 of
`Sumcheck.Spec.pSpec` is the prover's univariate polynomial. -/
theorem logupSumcheckPSpec_first_dir (hn : 0 < n) :
    (logupSumcheckPSpec F n M params).dir
      ⟨0, logupSumcheck_length_pos n hn⟩ = .P_to_V := by
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
/-- The outer → sumcheck seam round of the full LogUp transcript is a prover message. -/
theorem logup_seam_dir (hn : 0 < n) :
    ((outerPSpec F n params) ++ₚ (logupSumcheckPSpec F n M params)).dir
      ⟨4, by have := logupSumcheck_length_pos n hn; omega⟩ = .P_to_V := by
  cases n with
  | zero => omega
  | succ n' =>
    show Fin.vappend (outerPSpec F (n' + 1) params).dir
      (logupSumcheckPSpec F (n' + 1) M params).dir _ = _
    rw [Fin.vappend_right_of_not_lt _ _ _ (by norm_num)]
    exact logupSumcheckPSpec_first_dir F (n' + 1) M params (by omega)

/-- The mid statement (post-outer-phase statement plus retained oracles) is inhabited. -/
instance instInhabitedStmtAfterOuterProd :
    Inhabited (StmtAfterOuter F n M params × ∀ i, OStmtAfterOuter F n M params i) :=
  ⟨⟨{ xChallenge := 0, zChallenge := fun _ => 0, batchingScalars := fun _ => 0 },
    fun i => match i with
      | .input (.table) => (⟨fun _ => 0⟩ : LagrangeOracle F n)
      | .input (.column _) => (⟨fun _ => 0⟩ : LagrangeOracle F n)
      | .multiplicity => (⟨fun _ => 0⟩ : LagrangeOracle F n)
      | .helpers => fun _ => (⟨fun _ => 0⟩ : LagrangeOracle F n)⟩⟩

/-! ### The discharge -/

/-- **The LogUp plain-verifier append-soundness obligation is a theorem (message seam).**

The exact `hPlainAppend` consumed by `logup_soundness_uncond`, proved from the two per-phase
soundness facts via the unconditional message-seam keystone `Verifier.append_soundness_msg`.
Remaining inputs: `0 < n` (the sumcheck phase is nonempty) and the three standard honest-`impl`
side conditions. -/
theorem logup_plainAppend_msg (sumcheckSoundnessError : ℝ≥0)
    (hn : 0 < n)
    (hOuter :
      (outerVerifier oSpec F n M params).soundness init impl
        (inputRelation F n M).language (midSoundnessProtocolLanguage F n M params)
        (outerSoundnessError F n M params))
    (hSumcheck :
      (sumcheckVerifier oSpec F n M params).soundness init impl
        (midSoundnessProtocolLanguage F n M params) outputRelation.language
        sumcheckSoundnessError)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    (himplVB : ∀ (t : oSpec.Domain) (s s' : σ),
      evalDist ((impl t).run' s) = evalDist ((impl t).run' s')) :
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

/-! ### The headline: residual surface `{hOuter, hSumcheck}` + `impl` side conditions -/

/-- **LogUp Protocol 2 soundness with the append-composition blocker closed (issue #13).**

The full LogUp verifier is sound with the paper-shaped error
`logupSoundnessError = outerSoundnessError + sumcheckSoundnessError`.  Compared to
`logup_soundness_uncond`, the deep plain-verifier append residual `hPlainAppend` (malicious-prover
seam decomposition + union bound) is **no longer a hypothesis**: LogUp's outer → sumcheck seam is a
prover message, so the proven message-seam keystone discharges it.  The honest residual surface is
now exactly the two per-phase soundness facts

* `hOuter` — outer Schwartz–Zippel soundness over `midSoundnessProtocolLanguage`;
* `hSumcheck` — embedded-sumcheck soundness over `midSoundnessProtocolLanguage`;

plus `0 < n` and the three standard honest-`impl` side conditions (state-preserving /
never-failing / value-blind — all hold for the canonical interactive implementation). -/
theorem logup_soundness_msgSeam (sumcheckSoundnessError : ℝ≥0)
    (hn : 0 < n)
    (hOuter :
      (outerVerifier oSpec F n M params).soundness init impl
        (inputRelation F n M).language (midSoundnessProtocolLanguage F n M params)
        (outerSoundnessError F n M params))
    (hSumcheck :
      (sumcheckVerifier oSpec F n M params).soundness init impl
        (midSoundnessProtocolLanguage F n M params) outputRelation.language
        sumcheckSoundnessError)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    (himplVB : ∀ (t : oSpec.Domain) (s s' : σ),
      evalDist ((impl t).run' s) = evalDist ((impl t).run' s')) :
    (logupVerifier oSpec F n M params).soundness init impl
      (inputRelation F n M).language outputRelation.language
      (logupSoundnessError F n M params sumcheckSoundnessError) :=
  logup_soundness_uncond oSpec F n M params init impl sumcheckSoundnessError
    hOuter hSumcheck
    (logup_plainAppend_msg oSpec F n M params init impl sumcheckSoundnessError hn
      hOuter hSumcheck himplSP himplNF himplVB)

end MsgSeam

end Logup

/-! ### Axiom audit (issue #13 message-seam append discharge) -/

#print axioms Logup.logupSumcheck_length_pos
#print axioms Logup.logupSumcheckPSpec_first_dir
#print axioms Logup.logup_seam_dir
#print axioms Logup.logup_plainAppend_msg
#print axioms Logup.logup_soundness_msgSeam

namespace Logup

section EmptyOracle

variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)]
  [SampleableType F]
variable (n M : ℕ)
variable (params : ProtocolParams M)
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))

local instance instInhabitedFieldMsgSeamEmpty : Inhabited F := ⟨0⟩

/-- **LogUp Protocol 2 soundness over the empty ambient oracle: residual surface exactly
`{hOuter, hSumcheck}`.**

At the canonical ambient specification `oSpec = []ₒ` (no shared oracles — the setting of the
self-contained interactive protocol), the three honest-`impl` side conditions of
`logup_soundness_msgSeam` are *vacuous* (`([]ₒ).Domain = PEmpty`), so the only remaining
obligations are the two per-phase soundness facts and `0 < n`. -/
theorem logup_soundness_msgSeam_emptyOracle (sumcheckSoundnessError : ℝ≥0)
    (hn : 0 < n)
    (hOuter :
      (outerVerifier []ₒ F n M params).soundness init impl
        (inputRelation F n M).language (midSoundnessProtocolLanguage F n M params)
        (outerSoundnessError F n M params))
    (hSumcheck :
      (sumcheckVerifier []ₒ F n M params).soundness init impl
        (midSoundnessProtocolLanguage F n M params) outputRelation.language
        sumcheckSoundnessError) :
    (logupVerifier []ₒ F n M params).soundness init impl
      (inputRelation F n M).language outputRelation.language
      (logupSoundnessError F n M params sumcheckSoundnessError) :=
  logup_soundness_msgSeam []ₒ F n M params init impl sumcheckSoundnessError hn
    hOuter hSumcheck
    (fun t => t.elim) (fun t => t.elim) (fun t => t.elim)

end EmptyOracle

end Logup

#print axioms Logup.logup_soundness_msgSeam_emptyOracle

namespace Logup

section AnyMid

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)]
  [SampleableType F]
variable (n M : ℕ)
variable (params : ProtocolParams M)
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

local instance instInhabitedFieldMsgSeamAnyMid : Inhabited F := ⟨0⟩

/-- **Language-generic LogUp soundness composition (message seam).**

The full LogUp verifier is sound from the input language into the output language with additive
error `e₁ + e₂`, for **any** intermediate language `langMid` threading the outer → sumcheck seam:
the seam routing (binary verifier fusion + the proven message-seam append keystone) is entirely
independent of the choice of intermediate language.  This is the future-proof composition front
door: in particular it accepts the *sharp* corrected intermediate language
`midSoundnessProtocolLanguageSharp` (`OuterSoundnessSharp.lean`) directly, whereas the pinned
`logup_soundness_msgSeam` is stated over `midSoundnessProtocolLanguage` (whose unrestricted
denominator-clearing makes its outer obligation unsatisfiable in the typical regime — see
`prob_midSoundnessLanguage_ge_compl_support`). -/
theorem logup_soundness_msgSeam_anyMid
    (langMid : Set (StmtAfterOuter F n M params × ∀ i, OStmtAfterOuter F n M params i))
    (e₁ e₂ : ℝ≥0)
    (hn : 0 < n)
    (hOuter :
      (outerVerifier oSpec F n M params).soundness init impl
        (inputRelation F n M).language langMid e₁)
    (hSumcheck :
      (sumcheckVerifier oSpec F n M params).soundness init impl
        langMid outputRelation.language e₂)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    (himplVB : ∀ (t : oSpec.Domain) (s s' : σ),
      evalDist ((impl t).run' s) = evalDist ((impl t).run' s')) :
    (logupVerifier oSpec F n M params).soundness init impl
      (inputRelation F n M).language outputRelation.language
      (e₁ + e₂) :=
  OracleVerifier.append_soundness.{0, 0}
    (outerVerifier oSpec F n M params) (sumcheckVerifier oSpec F n M params)
    hOuter hSumcheck
    (OracleVerifier.oracleAppendSoundnessResidual_of_plain.{0, 0}
      (init := init) (impl := impl)
      (outerVerifier oSpec F n M params) (sumcheckVerifier oSpec F n M params)
      hOuter hSumcheck
      (_root_.Verifier.append_soundness_msg
        (outerVerifier oSpec F n M params).toVerifier
        (sumcheckVerifier oSpec F n M params).toVerifier
        hOuter hSumcheck
        (logupSumcheck_length_pos n hn)
        (logup_seam_dir F n M params hn)
        (logupSumcheckPSpec_first_dir F n M params hn)
        himplSP himplNF himplVB))

end AnyMid

end Logup

#print axioms Logup.logup_soundness_msgSeam_anyMid
