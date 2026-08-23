/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Security.OuterVerifierSupport
import ArkLib.ProofSystem.Logup.Security.MarginalBridgeProof
import ArkLib.ProofSystem.Logup.Security.OuterCompleteness
import ArkLib.ProofSystem.Logup.Security.OuterSoundnessReal
import ArkLib.ProofSystem.Logup.Security.LogupProtocol2Status

/-!
# LogUp outer phase: RBR soundness and the `hOuter` discharge at the sharp language (issue #13)

This file closes the **outer half** of the LogUp Protocol 2 soundness obligation — the `hOuter`
hypothesis consumed by `issue13_soundness_msgSeam_sharp_wiredRoundAppend` — by the round-by-round
route, so that **no run-unfolding of `Reduction.run` is needed at all**:

* `outerSharpState` / `outerSharpStateFunction` — the RBR state function for the compiled outer
  verifier at the sharp protocol language: the state is "the recorded round-1 challenge lies in
  the sharp claim language `midSoundnessLanguageSharp` of the input oracles". Its `toFun_full`
  is the proven verifier-collapse pinning (`outer_toVerifier_accept_pins_challenge`); its
  prover-round monotonicity is the transcript-entry preservation under `Transcript.concat`
  (definitional, `Fin.snoc` below the appended position).

* `outerVerifier_rbrSoundness_sharp` — round-by-round soundness with per-round error
  `outerRbrError`: the round-1 flip is exactly the sharp Schwartz–Zippel event (the freshly
  drawn uniform challenge lands in the vanishing locus of the support-cleared check polynomial,
  bounded by `(M·2ⁿ − 1)/|F|` via the proven `outerSoundness_sharp`); the round-3 batching
  challenge cannot flip the state (the state reads only the round-1 entry).

* `outerVerifier_soundness_sharp` — **the `hOuter` discharge**: composing the RBR soundness with
  the proven generic marginal bridge (`Verifier.marginalBridge_holds`, which packages the whole
  run/`simulateQ` plumbing once and for all) yields the protocol-level outer soundness
  `(outerVerifier).soundness init impl (inputRelation).language
  (midSoundnessProtocolLanguageSharp) (outerSoundnessError)` for every state-preserving,
  non-failing, value-blind shared-oracle implementation, over any field with `2ⁿ < |F|`.

Together with the already-landed sumcheck pointwise route this removes the last *outer-phase*
semantic residual of issue #13's soundness side. No `sorry`/`admit`/`axiom`; the audit at the
bottom confirms axiom-cleanliness.
-/

open scoped NNReal ENNReal
open OracleComp OracleSpec ProtocolSpec

namespace Logup

section OuterRbr

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)]
  [SampleableType F]
variable (n M : ℕ) (params : ProtocolParams M)
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

local instance instInhabitedFieldOuterRbr : Inhabited F := ⟨0⟩

/-- The round-by-round state predicate for the outer phase at the sharp language: the input is
good, or the transcript has reached round 2 and its recorded round-1 challenge lies in the
sharp claim language of the input oracles. -/
def outerSharpState (m : Fin 5) (stmt : StmtIn F n M × (∀ i, OStmtIn F n M i))
    (tr : (outerPSpec F n params).Transcript m) : Prop :=
  stmt ∈ (inputRelation F n M).language ∨
    ∃ h : 1 < m.val, (show F from tr ⟨1, h⟩) ∈ midSoundnessLanguageSharp stmt.2

/-- **The outer sharp state function.** -/
noncomputable def outerSharpStateFunction :
    ((outerVerifier oSpec F n M params).toVerifier).StateFunction init impl
      (inputRelation F n M).language
      (midSoundnessProtocolLanguageSharp F n M params) where
  toFun := outerSharpState F n M params
  toFun_empty := fun stmt => by
    unfold outerSharpState
    constructor
    · exact fun h => Or.inl h
    · rintro (h | ⟨h, -⟩)
      · exact h
      · exact absurd h (by omega)
  toFun_next := fun m hdir stmt tr hno msg => by
    fin_cases m
    · -- round 0 (message): no entry exists on either side
      unfold outerSharpState at hno ⊢
      rintro (h | ⟨h, -⟩)
      · exact hno (Or.inl h)
      · exact absurd h (by norm_num)
    · -- round 1 is a challenge round: direction contradiction
      exact absurd hdir (by simp [outerPSpec] at hdir ⊢; exact fun h => by cases hdir)
    · -- round 2 (message): entry 1 preserved by concat
      unfold outerSharpState at hno ⊢
      rintro (h | ⟨h, hmem⟩)
      · exact hno (Or.inl h)
      · refine hno (Or.inr ⟨by norm_num, ?_⟩)
        exact hmem
    · -- round 3 is a challenge round: direction contradiction
      exact absurd hdir (by simp [outerPSpec] at hdir ⊢; exact fun h => by cases hdir)
  toFun_full := fun stmt tr hno => by
    classical
    refine probEvent_eq_zero ?_
    intro x hx hmem
    rw [OptionT.mem_support_iff] at hx
    simp only [OptionT.run_mk, mem_support_bind_iff] at hx
    obtain ⟨s, -, hx⟩ := hx
    have hx' := _root_.support_simulateQ_run'_subset impl _ s hx
    have hpin := outer_toVerifier_accept_pins_challenge stmt.1 stmt.2 tr x hx' hmem
    unfold outerSharpState at hno
    push Not at hno
    exact hno.2 (by norm_num) hpin

end OuterRbr

section OuterRbrBound

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)]
  [SampleableType F]
variable (n M : ℕ) (params : ProtocolParams M)
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

local instance instInhabitedFieldOuterRbrB : Inhabited F := ⟨0⟩

/-- The per-round RBR soundness error for the outer phase: the sharp Schwartz–Zippel budget at
the round-1 challenge, zero at the round-3 batching challenge. -/
noncomputable def outerRbrError : (outerPSpec F n params).ChallengeIdx → ℝ≥0 :=
  fun i => if i.1.val = 1 then ((M * 2 ^ n - 1 : ℕ) : ℝ≥0) / (Fintype.card F : ℝ≥0) else 0

/-- **Outer RBR soundness at the sharp language.** -/
theorem outerVerifier_rbrSoundness_sharp :
    ((outerVerifier oSpec F n M params).toVerifier).rbrSoundness init impl
      (inputRelation F n M).language
      (midSoundnessProtocolLanguageSharp F n M params)
      (outerRbrError F n M params) := by
  classical
  refine ⟨outerSharpStateFunction oSpec F n M params init impl, ?_⟩
  intro stmtIn hStmtIn WitIn WitOut witIn prover i
  -- the two challenge rounds
  rcases i with ⟨⟨iv, hiv⟩, hdir⟩
  interval_cases iv
  · -- round 0 is a message round: direction contradiction
    exact absurd hdir (by exact fun h => by cases h)
  · -- round 1: the sharp Schwartz–Zippel flip
    have herr : outerRbrError F n M params ⟨⟨1, hiv⟩, hdir⟩
        = ((M * 2 ^ n - 1 : ℕ) : ℝ≥0) / (Fintype.card F : ℝ≥0) := by
      unfold outerRbrError; norm_num
    rw [herr]
    -- the bad-lookup hypothesis in relation form
    have hBad : ¬ (((stmtIn.1, stmtIn.2), ()) ∈ inputRelation F n M) := by
      intro h
      exact hStmtIn ((Set.mem_language_iff _ _).mpr ⟨(), h⟩)
    -- peel the init draw
    refine le_trans (probEvent_bind_le_of_forall_support init _ _ _ (fun s _ => ?_)) le_rfl
    -- distribute the simulation over the prefix bind
    rw [simulateQ_bind, StateT.run'_bind_lib]
    -- peel the prover prefix
    refine probEvent_bind_le_of_forall_support _ _ _ _ (fun rk _ => ?_)
    obtain ⟨⟨t, pst⟩, s'⟩ := rk
    -- the challenge draw in `liftM` form, then the uniform average over the drawn challenge
    rw [liftComp_eq_liftM]
    rw [ChallengeCoherence.probEvent_run'_simulateQ_addLift_getChallenge_bind impl s'
      ⟨⟨1, hiv⟩, hdir⟩ (fun c => pure (t, c)) _]
    -- bound the average by the uniform sharp-language mass, then Schwartz–Zippel
    haveI hfinC : Fintype ((outerPSpec F n params).Challenge ⟨⟨1, hiv⟩, hdir⟩) :=
      (inferInstance : Fintype F)
    haveI hsampC : SampleableType ((outerPSpec F n params).Challenge ⟨⟨1, hiv⟩, hdir⟩) :=
      (inferInstance : SampleableType F)
    refine le_trans (tsum_uniform_challenge_mem_le_prob_uniform
      (midSoundnessLanguageSharp stmtIn.2)
      (C := (outerPSpec F n params).Challenge ⟨⟨1, hiv⟩, hdir⟩) rfl _
      (fun c => (show F from c) ∈ midSoundnessLanguageSharp stmtIn.2)
      (fun c => Iff.rfl) ?hg ?hgle) ?_
    case hg =>
      intro c hc
      rw [mul_eq_zero]
      right
      rw [simulateQ_pure]
      refine probEvent_eq_zero ?_
      rintro x hx ⟨hno, hyes⟩
      simp only [StateT.run'_eq, StateT.run_pure, map_pure, support_pure,
        Set.mem_singleton_iff] at hx
      subst hx
      simp only [outerSharpStateFunction] at hyes
      unfold outerSharpState at hyes
      rcases hyes with h | ⟨h, hmem⟩
      · exact hStmtIn h
      · exact hc hmem
    case hgle =>
      intro c
      refine le_trans (mul_le_mul' (le_of_eq ?_) probEvent_le_one) (by rw [mul_one])
      rw [probOutput_uniformSample]
      congr 1
      exact congrArg Nat.cast (Fintype.card_congr (Equiv.cast (rfl : _ = F)))
    · -- the uniform mass of the sharp language is the Schwartz–Zippel budget
      rw [ENNReal.coe_div (by exact_mod_cast Fintype.card_ne_zero)]
      exact outerSoundness_sharp stmtIn.1 stmtIn.2 hBad
  · -- round 2 is a message round: direction contradiction
    exact absurd hdir (by exact fun h => by cases h)
  · -- round 3: the batch challenge cannot flip the state
    have hzero : outerRbrError F n M params ⟨⟨3, hiv⟩, hdir⟩ = 0 := by
      unfold outerRbrError; norm_num
    rw [hzero]
    refine le_of_eq (probEvent_eq_zero ?_)
    rintro ⟨tr, c⟩ - ⟨hno, hyes⟩
    refine hno ?_
    simp only [outerSharpStateFunction] at hyes ⊢
    unfold outerSharpState at hyes ⊢
    rcases hyes with h | ⟨h, hmem⟩
    · exact Or.inl h
    · exact Or.inr ⟨by norm_num, hmem⟩

end OuterRbrBound


section OuterSoundnessCapstone

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)]
  [SampleableType F]
variable (n M : ℕ) (params : ProtocolParams M)
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

local instance instInhabitedFieldOuterCap : Inhabited F := ⟨0⟩

/-- The total outer RBR error is the sharp Schwartz–Zippel budget (the round-3 term is zero). -/
theorem sum_outerRbrError :
    ∑ i : (outerPSpec F n params).ChallengeIdx, outerRbrError F n M params i
      = ((M * 2 ^ n - 1 : ℕ) : ℝ≥0) / (Fintype.card F : ℝ≥0) := by
  classical
  have hsub : ∑ i ∈ Finset.univ.filter
        (fun i : Fin 4 => (outerPSpec F n params).dir i = Direction.V_to_P),
        (if i.val = 1 then ((M * 2 ^ n - 1 : ℕ) : ℝ≥0) / (Fintype.card F : ℝ≥0) else 0)
      = ∑ i : (outerPSpec F n params).ChallengeIdx, outerRbrError F n M params i := by
    refine Finset.sum_subtype _ (fun x => ?_) _
    simp [ProtocolSpec.ChallengeIdx]
  have hfilter : Finset.univ.filter
      (fun i : Fin 4 => (outerPSpec F n params).dir i = Direction.V_to_P)
      = ({⟨1, by norm_num⟩, ⟨3, by norm_num⟩} : Finset (Fin 4)) := by
    ext i
    fin_cases i
    · exact iff_of_false (fun h => nomatch (Finset.mem_filter.mp h).2) (by decide)
    · exact iff_of_true (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩) (by decide)
    · exact iff_of_false (fun h => nomatch (Finset.mem_filter.mp h).2) (by decide)
    · exact iff_of_true (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩) (by decide)
  rw [← hsub, hfilter, Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num

set_option maxHeartbeats 4000000 in
/-- **`hOuter` discharged: protocol-level outer soundness at the sharp language.**

The outer LogUp verifier is sound from the input language into the sharp protocol-level
intermediate language with the paper-shaped error `outerSoundnessError`, for any
state-preserving, non-failing, value-blind shared-oracle implementation. -/
theorem outerVerifier_soundness_sharp (hcard : 2 ^ n < Fintype.card F)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    (himplVB : ∀ (t : oSpec.Domain) (s s' : σ),
      evalDist ((impl t).run' s) = evalDist ((impl t).run' s')) :
    (outerVerifier oSpec F n M params).soundness init impl
      (inputRelation F n M).language
      (midSoundnessProtocolLanguageSharp F n M params)
      (outerSoundnessError F n M params) := by
  have hRbr := outerVerifier_rbrSoundness_sharp oSpec F n M params init impl
  have hbr : Verifier.MarginalBridge init impl
      (inputRelation F n M).language
      (midSoundnessProtocolLanguageSharp F n M params)
      ((outerVerifier oSpec F n M params).toVerifier)
      (outerRbrError F n M params) :=
    Verifier.marginalBridge_holds himplSP himplNF himplVB
  have h := Verifier.rbrSoundness_imp_soundness_of_marginal init impl hRbr hbr
  have hle : (∑ i : (outerPSpec F n params).ChallengeIdx, outerRbrError F n M params i)
      ≤ outerSoundnessError F n M params := by
    rw [sum_outerRbrError]
    exact sharp_error_le_outerSoundnessError (params := params) hcard
  exact Verifier.soundness.mono_error init impl h hle

end OuterSoundnessCapstone


section WiredCorollary

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)]
  [SampleableType F]
variable (n M : ℕ) (params : ProtocolParams M)
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

local instance instInhabitedFieldOuterWired : Inhabited F := ⟨0⟩

/-- **Issue #13 soundness with the outer half fully discharged.** The sharp-language LogUp
soundness front door with `hOuter` replaced by the proven `outerVerifier_soundness_sharp`:
the remaining hypotheses are the embedded-sumcheck projection/RBR data, the append-RBR
keystone, the error equation, and the honest-implementation side conditions. -/
theorem issue13_soundness_sharp_outerDischarged [oSpec.Fintype]
    (sumcheckSoundnessError : ℝ≥0)
    (lang : (i : Fin (n + 1)) →
      Set (Sumcheck.Spec.StatementRound F n i ×
        (∀ j, Sumcheck.Spec.OracleStatement F n (logupSumcheckDegree M params) j)))
    (rbrSoundnessError :
      ∀ _ : Fin n,
        (Sumcheck.Spec.SingleRound.pSpec F (logupSumcheckDegree M params)).ChallengeIdx → ℝ≥0)
    (hn : 0 < n) (hcard : 2 ^ n < Fintype.card F)
    (hLast : lang (Fin.last n) = Set.univ)
    (hError : sumcheckSoundnessError =
      ∑ i : (logupSumcheckPSpec F n M params).ChallengeIdx,
        (fun combinedIdx =>
          letI ij := ProtocolSpec.seqComposeChallengeIdxToSigma combinedIdx
          rbrSoundnessError ij.1 ij.2) i)
    (hProj :
      SumcheckLensProjSoundFor oSpec F n M params
        (midSoundnessProtocolLanguageSharp F n M params) (lang 0))
    (hRound : ∀ i : Fin n,
      (Sumcheck.Spec.SingleRound.oracleVerifier F n (logupSumcheckDegree M params)
          (signDomain F (Fact.out : (-1 : F) ≠ 1)) oSpec i).rbrSoundness init impl
        (lang i.castSucc) (lang i.succ) (rbrSoundnessError i))
    (hAppend : ∀ {S₁ S₂ S₃ : Type} {k₁ k₂ : ℕ}
        {p₁ : ProtocolSpec k₁} {p₂ : ProtocolSpec k₂}
        [∀ j, SampleableType (p₁.Challenge j)] [∀ j, SampleableType (p₂.Challenge j)]
        (V₁ : Verifier oSpec S₁ S₂ p₁) (V₂ : Verifier oSpec S₂ S₃ p₂)
        {l₁ : Set S₁} {l₂ : Set S₂} {l₃ : Set S₃}
        {e₁ : p₁.ChallengeIdx → ℝ≥0} {e₂ : p₂.ChallengeIdx → ℝ≥0},
        V₁.rbrSoundness init impl l₁ l₂ e₁ → V₂.rbrSoundness init impl l₂ l₃ e₂ →
        (V₁.append V₂).rbrSoundness init impl l₁ l₃
          (Sum.elim e₁ e₂ ∘ ChallengeIdx.sumEquiv.symm))
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    (himplVB : ∀ (t : oSpec.Domain) (s s' : σ),
      evalDist ((impl t).run' s) = evalDist ((impl t).run' s')) :
    (logupVerifier oSpec F n M params).soundness init impl
      (inputRelation F n M).language outputRelation.language
      (logupSoundnessError F n M params sumcheckSoundnessError) :=
  issue13_soundness_msgSeam_sharp_wiredRoundAppend oSpec F n M params init impl
    sumcheckSoundnessError lang rbrSoundnessError hn
    (outerVerifier_soundness_sharp oSpec F n M params init impl hcard himplSP himplNF himplVB)
    hLast hError hProj hRound hAppend himplSP himplNF himplVB

end WiredCorollary

end Logup

/-! ### Axiom audit (issue #13 outer RBR discharge) -/

#print axioms Logup.outerSharpStateFunction
#print axioms Logup.outerVerifier_rbrSoundness_sharp
#print axioms Logup.sum_outerRbrError
#print axioms Logup.outerVerifier_soundness_sharp
#print axioms Logup.issue13_soundness_sharp_outerDischarged
