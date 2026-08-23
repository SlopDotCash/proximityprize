/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Security.SumcheckComposedRejection
import ArkLib.ProofSystem.Logup.Security.SumcheckLensProjSound
import ArkLib.ProofSystem.Logup.Sumcheck.SumcheckLiftCoherent
import ArkLib.ProofSystem.Logup.Security.RbrToSoundBridge
import ArkLib.ProofSystem.Logup.Security.MarginalBridgeProof

/-!
# The LogUp embedded sum-check soundness residual, discharged pointwise (issue #13, pieces E+F)

* `sumcheckVerifier_run_failure` (E): the LogUp-lifted sum-check verifier rejects outright
  (`run = failure`) on any after-outer statement outside `midLanguage`. Chain: the proven
  LogUp-lens coherence commute exposes the lifted run as the inner composed run on the lens
  projection; the projection is outside the inner round-`0` language by the proven
  `SumcheckLensProjSound_holds`; the inner composed verifier rejects by
  `composedSumcheck_run_failure`; and the `OptionT` bind short-circuits.

* `midStateFunction` + `sumcheckVerifier_rbrSoundness_zero` + `sumcheckSoundnessResidual_pointwise`
  (F): the transcript-independent state function `stmt ∈ midLanguage` is a genuine
  `StateFunction` for the lifted verifier (its `toFun_full` is (E)); its flips are impossible, so
  round-by-round soundness holds with error `0`; the proven `marginalBridge_holds` +
  `rbrSoundness_imp_soundness_of_marginal` convert this to plain soundness `0 ≤ ε` — discharging
  `SumcheckSoundnessResidual` outright (no rbr-append keystone, no per-round induction).

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

/-- **(E) The LogUp-lifted sum-check verifier rejects bad mid-claims outright.** -/
theorem sumcheckVerifier_run_failure (hn : 0 < n)
    (stmt : StmtAfterOuter F n M params × (∀ i, OStmtAfterOuter F n M params i))
    (hBad : stmt ∉ midLanguage F n M params)
    (tr : (logupSumcheckPSpec F n M params).FullTranscript) :
    ((sumcheckVerifier oSpec F n M params).toVerifier).run stmt tr =
      (failure : OptionT (OracleComp oSpec) _) := by
  -- The lens projection is outside the inner round-`0` language (proven projection soundness),
  -- hence outside the round-`0` relation (Unit witness).
  have hProjLang := SumcheckLensProjSound_holds oSpec F n M params
    (Fact.out : (-1 : F) ≠ 1) stmt hBad
  have hProjRel : (((logupSumcheckOracleLens.{0} oSpec F n M params).toLens.proj stmt), ())
      ∉ Sumcheck.Spec.relationRound F n (logupSumcheckDegree M params)
        (signDomain F (Fact.out : (-1 : F) ≠ 1)) (0 : Fin (n + 1)) := fun hMem =>
    hProjLang (by
      rw [logupSumcheckInputLanguage, Set.mem_language_iff]
      exact ⟨(), hMem⟩)
  -- Commute `toVerifier` through the LogUp lift (proven coherence).
  haveI := logupSumcheck_liftContextCoherent oSpec F n M params
  have hcomm := OracleVerifier.liftContext_toVerifier_comm
    (stmtLens := logupSumcheckOracleLens.{0} oSpec F n M params)
    (V := (logupConcreteSumcheckOracleReduction oSpec F n M params
      (Fact.out : (-1 : F) ≠ 1)).verifier)
  show (((logupConcreteSumcheckOracleReduction oSpec F n M params
      (Fact.out : (-1 : F) ≠ 1)).verifier.liftContext
      (logupSumcheckOracleLens.{0} oSpec F n M params)).toVerifier).run stmt tr = _
  rw [hcomm]
  -- Expose `n = n' + 1` to apply the composed rejection.
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  -- The lifted run is the inner composed run on the projection, post-composed with the lift;
  -- the inner run fails, and the `OptionT` bind short-circuits.
  show (((logupConcreteSumcheckOracleReduction oSpec F (n' + 1) M params
      (Fact.out : (-1 : F) ≠ 1)).verifier.toVerifier).run
      ((logupSumcheckOracleLens.{0} oSpec F (n' + 1) M params).toLens.proj stmt) tr) >>= _ = _
  have hInnerFail : (((logupConcreteSumcheckOracleReduction oSpec F (n' + 1) M params
      (Fact.out : (-1 : F) ≠ 1)).verifier.toVerifier).run
      ((logupSumcheckOracleLens.{0} oSpec F (n' + 1) M params).toLens.proj stmt) tr)
      = (failure : OptionT (OracleComp oSpec) _) := by
    exact Sumcheck.Spec.composedSumcheck_run_failure oSpec F (logupSumcheckDegree M params)
      (signDomain F (Fact.out : (-1 : F) ≠ 1))
      ((logupSumcheckOracleLens.{0} oSpec F (n' + 1) M params).toLens.proj stmt).1
      ((logupSumcheckOracleLens.{0} oSpec F (n' + 1) M params).toLens.proj stmt).2
      hProjRel tr
  rw [hInnerFail]
  apply OptionT.ext
  simp [OptionT.run_bind]

/-- **(F-i) The transcript-independent mid-language state function for the lifted verifier.**
Its `toFun_full` is exactly the pointwise rejection (E). -/
def midStateFunction (hn : 0 < n) :
    ((sumcheckVerifier oSpec F n M params).toVerifier).StateFunction init impl
      (midLanguage F n M params) outputRelation.language where
  toFun := fun _ stmt _ => stmt ∈ midLanguage F n M params
  toFun_empty := fun _ => Iff.rfl
  toFun_next := fun _ _ _ _ h _ => h
  toFun_full := fun stmt tr hNeg => by
    have hrun := sumcheckVerifier_run_failure oSpec F n M params hn stmt hNeg tr
    rw [probEvent_eq_zero_iff]
    rintro x hx -
    rw [OptionT.mem_support_iff] at hx
    simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hx
    obtain ⟨s, _, hx⟩ := hx
    have key : (simulateQ impl
        (((sumcheckVerifier oSpec F n M params).toVerifier).run stmt tr)).run' s
        = (pure none : ProbComp (Option _)) := by
      rw [hrun]
      change (simulateQ impl (pure none : OracleComp oSpec (Option _))).run' s = _
      rw [simulateQ_pure]
      change Prod.fst <$> (pure (none : Option _) : StateT σ ProbComp _).run s = _
      rw [StateT.run_pure]
      simp [map_pure]
    rw [key] at hx
    simp only [support_pure, Set.mem_singleton_iff] at hx
    exact absurd hx (by simp)

/-- **(F-ii) Round-by-round soundness of the lifted sum-check verifier with error `0`.** -/
theorem sumcheckVerifier_rbrSoundness_zero (hn : 0 < n) :
    ((sumcheckVerifier oSpec F n M params).toVerifier).rbrSoundness init impl
      (midLanguage F n M params) outputRelation.language (fun _ => 0) := by
  refine ⟨midStateFunction oSpec F n M params hn, ?_⟩
  intro stmtIn _ WitIn WitOut witIn prover i
  refine le_of_eq (probEvent_eq_zero ?_)
  rintro ⟨tr, chal⟩ - ⟨hneg, hpos⟩
  exact hneg hpos

/-- **(F-iii) `SumcheckSoundnessResidual` discharged pointwise** — the LogUp embedded sum-check
phase is sound from `midLanguage` into `outputRelation.language` with any error
`sumcheckSoundnessError`, via the error-`0` round-by-round soundness + the proven
`marginalBridge_holds` (no rbr-append keystone, no per-round induction). -/
theorem sumcheckSoundnessResidual_pointwise (hn : 0 < n)
    (sumcheckSoundnessError : ℝ≥0)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    (himplVB : ∀ (t : oSpec.Domain) (s s' : σ),
      evalDist ((impl t).run' s) = evalDist ((impl t).run' s')) :
    SumcheckSoundnessResidual oSpec F n M params init impl sumcheckSoundnessError := by
  have h := Verifier.rbrSoundness_imp_soundness_of_marginal init impl
    (sumcheckVerifier_rbrSoundness_zero oSpec F n M params hn)
    (Verifier.marginalBridge_holds himplSP himplNF himplVB)
  -- `soundness` with error `∑ 0 = 0` weakens to any error.
  intro WitIn WitOut witIn prover stmtIn hStmtIn
  refine le_trans (h WitIn WitOut witIn prover stmtIn hStmtIn) ?_
  simp

end

end Logup

/- Axiom audit. -/
#print axioms Logup.sumcheckVerifier_run_failure
#print axioms Logup.sumcheckVerifier_rbrSoundness_zero
#print axioms Logup.sumcheckSoundnessResidual_pointwise
