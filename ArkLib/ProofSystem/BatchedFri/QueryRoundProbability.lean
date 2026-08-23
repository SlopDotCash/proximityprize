/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.BatchedFri.Security
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AffineLines.Main
import ArkLib.OracleReduction.Completeness
import ArkLib.ToMathlib.FriQueryRoundProb

/-!
# Batched FRI query-round probability adapters

This module connects the Mathlib-only probability-space query-round theorem from
`ArkLib.ToMathlib.FriQueryRoundProb` to the Batched FRI Claim 8.2 frontier in
`ArkLib.ProofSystem.BatchedFri.Security`.

The remaining hard Claim 8.2/8.3 pieces stay explicit: the correlated-agreement bridge,
virtual-oracle soundness preservation, sequential composition, and total-error consumption are not
proved here.
-/

namespace Fri

namespace Spec.QueryRound

open Domain
open scoped ProbabilityTheory

variable {𝔽 : Type} [NonBinaryField 𝔽] [DecidableEq 𝔽]
variable {n l : ℕ} {ω : SmoothCosetFftDomain n 𝔽}

/-- The concrete query-round challenge oracle samples the verifier's whole length-`l` query tuple
from the independent-uniform PMF on `Fin l → (ω.subdomain 0).toFinset`.

This is the protocol-level distribution bridge consumed by the probability adapters below: the
standalone PMF theorem is not merely about an abstract product space, but about the challenge type
of `Fri.Spec.QueryRound.pSpec` under the default `challengeQueryImpl`. -/
theorem getChallenge_probOutput_uniform_eq_Pr
    [SampleableType (Fin l → (ω.subdomain 0).toFinset)]
    [Nonempty (Fin l → (ω.subdomain 0).toFinset)]
    [Inhabited (Fin l → (ω.subdomain 0).toFinset)]
    (q : Fin l → (ω.subdomain 0).toFinset) :
    Pr[= q |
      simulateQ (ProtocolSpec.challengeQueryImpl (pSpec := pSpec (ω := ω) l))
        ((pSpec (ω := ω) l).getChallenge ⟨0, by simp⟩)]
      = Pr_{ let y ← PMF.uniformOfFintype (Fin l → (ω.subdomain 0).toFinset) }[y = q] := by
  unfold ProtocolSpec.getChallenge
  erw [simulateQ_query]
  simp only [ProtocolSpec.challengeQueryImpl, OracleQuery.cont_query, OracleQuery.input_query]
  change Pr[= q | id <$> ($ᵗ (Fin l → (ω.subdomain 0).toFinset))]
      = Pr_{ let y ← PMF.uniformOfFintype (Fin l → (ω.subdomain 0).toFinset) }[y = q]
  simp only [id_map]
  rw [OracleReduction.probOutput_uniformOfFintype_eq_Pr
    (L := Fin l → (ω.subdomain 0).toFinset) (x := q)]

end Spec.QueryRound

section ProbabilityAdapter

open scoped ENNReal NNReal BigOperators
open OracleComp OracleSpec ProtocolSpec ReedSolomon Domain
open NNReal Finset Function ProbabilityTheory

namespace QueryRound

variable {ι : Type} [Fintype ι] [Nonempty ι]

/-- Probability-space query-round acceptance frontier: under independent uniform queries, all
queries land in the good set with probability at most `(1 - δ) ^ t` when the good-set density is
at most `1 - δ`. -/
def probabilityAcceptanceBound (G : Finset ι) (δ : ℝ≥0∞) (t : ℕ) : Prop :=
  (G.card : ℝ≥0∞) / Fintype.card ι ≤ 1 - δ →
    (PMF.uniformOfFintype (Fin t → ι)).toOuterMeasure
        {q : Fin t → ι | ∀ j, q j ∈ G}
      ≤ (1 - δ) ^ t

/-- The probability-space query-round acceptance frontier is discharged by the Mathlib-only
query-round probability theorem. -/
theorem probabilityAcceptanceBound_holds (G : Finset ι) (δ : ℝ≥0∞) (t : ℕ) :
    probabilityAcceptanceBound G δ t := by
  intro h_density
  exact ArkLib.Fri.QueryRoundProb.prob_allQueriesIn_le G δ t h_density

/-- Probability-space query-round detection frontier: under independent uniform queries, at least
one query lands outside the good set with probability at least `1 - (1 - δ) ^ t`. -/
def probabilityDetectionBound (G : Finset ι) (δ : ℝ≥0∞) (t : ℕ) : Prop :=
  (G.card : ℝ≥0∞) / Fintype.card ι ≤ 1 - δ →
    1 - (1 - δ) ^ t
      ≤ (PMF.uniformOfFintype (Fin t → ι)).toOuterMeasure
          {q : Fin t → ι | ¬ (∀ j, q j ∈ G)}

/-- The probability-space query-round detection frontier is discharged by the Mathlib-only
complementary detection theorem. -/
theorem probabilityDetectionBound_holds (G : Finset ι) (δ : ℝ≥0∞) (t : ℕ) :
    probabilityDetectionBound G δ t := by
  intro h_density
  exact ArkLib.Fri.QueryRoundProb.prob_someQueryOut_ge G δ t h_density

end QueryRound

variable {𝔽 : Type} [NonBinaryField 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] [Nontrivial 𝔽]
variable {n : ℕ} {k : ℕ}
variable {s : Fin (k + 1) → ℕ+} {d : ℕ+}
variable {ω : SmoothCosetFftDomain n 𝔽}

/-- Instantiate the Claim 8.2 frontier with the proved probability-space query-round bound. -/
def FriQuerySoundnessParts.of_queryRoundProbabilityBound
    {t : ℕ}
    {α : ℝ≥0}
    (f : Fin t.succ → (ω.subdomain 0 → 𝔽))
    (h_agreement :
      correlated_agreement_density
        (Fₛ f)
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (2 ^ n))
      ≤ α)
    {m : ℕ}
    (m_ge_3 : m ≥ 3)
    {ι : Type} [Fintype ι] [Nonempty ι]
    (G : Finset ι) (δ : ℝ≥0∞) (queries : ℕ)
    (lensReduction agreementBridge : Prop)
    (pieces_imply_claim :
      QueryRound.probabilityAcceptanceBound G δ queries →
      lensReduction →
      agreementBridge →
      fri_query_soundness (n := n) (ω := ω) (f := f)
        (h_agreement := h_agreement) (m_ge_3 := m_ge_3)) :
    FriQuerySoundnessParts (n := n) (ω := ω) (f := f)
      (h_agreement := h_agreement) (m_ge_3 := m_ge_3) where
  query_round_acceptance_bound := QueryRound.probabilityAcceptanceBound G δ queries
  batching_oracle_lens_reduction := lensReduction
  correlated_agreement_to_jointAgreement := agreementBridge
  pieces_imply_claim := pieces_imply_claim

/-- Reassemble Claim 8.2 after discharging the query-round frontier with the probability-space
query-round theorem. -/
theorem fri_query_soundness_of_queryRoundProbabilityBound
    {t : ℕ}
    {α : ℝ≥0}
    (f : Fin t.succ → (ω.subdomain 0 → 𝔽))
    (h_agreement :
      correlated_agreement_density
        (Fₛ f)
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (2 ^ n))
      ≤ α)
    {m : ℕ}
    (m_ge_3 : m ≥ 3)
    {ι : Type} [Fintype ι] [Nonempty ι]
    (G : Finset ι) (δ : ℝ≥0∞) (queries : ℕ)
    {lensReduction agreementBridge : Prop}
    (pieces_imply_claim :
      QueryRound.probabilityAcceptanceBound G δ queries →
      lensReduction →
      agreementBridge →
      fri_query_soundness (n := n) (ω := ω) (f := f)
        (h_agreement := h_agreement) (m_ge_3 := m_ge_3))
    (h_lens : lensReduction)
    (h_agreementBridge : agreementBridge) :
    fri_query_soundness (n := n) (ω := ω) (f := f)
      (h_agreement := h_agreement) (m_ge_3 := m_ge_3) := by
  let parts :=
    FriQuerySoundnessParts.of_queryRoundProbabilityBound
      (n := n) (ω := ω) (f := f) (h_agreement := h_agreement)
      (m_ge_3 := m_ge_3) G δ queries lensReduction agreementBridge pieces_imply_claim
  exact fri_query_soundness_of_parts (n := n) (ω := ω) f h_agreement m_ge_3 parts
    (QueryRound.probabilityAcceptanceBound_holds G δ queries) h_lens h_agreementBridge

/-- Instantiate the Claim 8.2 frontier with the proved probability-space query-round bound and
the structural Batched FRI oracle-lens package. -/
def FriQuerySoundnessParts.of_queryRoundProbabilityBoundAndBatchedFRIOracleLens
    {t : ℕ}
    {α : ℝ≥0}
    (f : Fin t.succ → (ω.subdomain 0 → 𝔽))
    (h_agreement :
      correlated_agreement_density
        (Fₛ f)
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (2 ^ n))
      ≤ α)
    {m : ℕ}
    (m_ge_3 : m ≥ 3)
    {ι : Type} [Fintype ι] [Nonempty ι]
    (G : Finset ι) (δ : ℝ≥0∞) (queries l : ℕ)
    (domain_size_cond : (2 ^ (∑ i, (s i : ℕ))) * d ≤ 2 ^ n)
    (agreementBridge : Prop)
    (pieces_imply_claim :
      QueryRound.probabilityAcceptanceBound G δ queries →
      batchedFRIOracleLensReduction
        (n := n) (s := s) (d := d) (ω := ω)
        (domain_size_cond := domain_size_cond) l t →
      agreementBridge →
      fri_query_soundness (n := n) (ω := ω) (f := f)
        (h_agreement := h_agreement) (m_ge_3 := m_ge_3)) :
    FriQuerySoundnessParts (n := n) (ω := ω) (f := f)
      (h_agreement := h_agreement) (m_ge_3 := m_ge_3) where
  query_round_acceptance_bound := QueryRound.probabilityAcceptanceBound G δ queries
  batching_oracle_lens_reduction :=
    batchedFRIOracleLensReduction
      (n := n) (s := s) (d := d) (ω := ω)
      (domain_size_cond := domain_size_cond) l t
  correlated_agreement_to_jointAgreement := agreementBridge
  pieces_imply_claim := pieces_imply_claim

/-- Reassemble Claim 8.2 after discharging the probability-space query-round bound and the
structural Batched FRI oracle-lens package. -/
theorem fri_query_soundness_of_queryRoundProbabilityBoundAndBatchedFRIOracleLens
    {t : ℕ}
    {α : ℝ≥0}
    (f : Fin t.succ → (ω.subdomain 0 → 𝔽))
    (h_agreement :
      correlated_agreement_density
        (Fₛ f)
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (2 ^ n))
      ≤ α)
    {m : ℕ}
    (m_ge_3 : m ≥ 3)
    {ι : Type} [Fintype ι] [Nonempty ι]
    (G : Finset ι) (δ : ℝ≥0∞) (queries l : ℕ)
    (domain_size_cond : (2 ^ (∑ i, (s i : ℕ))) * d ≤ 2 ^ n)
    {agreementBridge : Prop}
    (pieces_imply_claim :
      QueryRound.probabilityAcceptanceBound G δ queries →
      batchedFRIOracleLensReduction
        (n := n) (s := s) (d := d) (ω := ω)
        (domain_size_cond := domain_size_cond) l t →
      agreementBridge →
      fri_query_soundness (n := n) (ω := ω) (f := f)
        (h_agreement := h_agreement) (m_ge_3 := m_ge_3))
    (h_agreementBridge : agreementBridge) :
    fri_query_soundness (n := n) (ω := ω) (f := f)
      (h_agreement := h_agreement) (m_ge_3 := m_ge_3) := by
  let parts :=
    FriQuerySoundnessParts.of_queryRoundProbabilityBoundAndBatchedFRIOracleLens
      (n := n) (s := s) (d := d) (ω := ω)
      (f := f) (h_agreement := h_agreement) (m_ge_3 := m_ge_3)
      G δ queries l domain_size_cond agreementBridge pieces_imply_claim
  exact fri_query_soundness_of_parts (n := n) (ω := ω) f h_agreement m_ge_3 parts
    (QueryRound.probabilityAcceptanceBound_holds G δ queries)
    (batchedFRIOracleLensReduction_holds
      (n := n) (s := s) (d := d) (ω := ω)
      (domain_size_cond := domain_size_cond) l t)
    h_agreementBridge

omit [Nontrivial 𝔽] in
/-- Reassemble Claim 8.2 from the probability-space query-round theorem, the structural Batched
FRI oracle lens, and a concrete `Code.jointProximity` witness.

This removes the arbitrary `agreementBridge : Prop` from this front door: the remaining
coding-theoretic obligation is exactly the proximity predicate equivalent to the
`Code.jointAgreement` conclusion of `fri_query_soundness`. -/
theorem fri_query_soundness_of_queryRoundProbabilityBoundAndBatchedFRIOracleLensAndJointProximity
    {t : ℕ}
    {α : ℝ≥0}
    (f : Fin t.succ → (ω.subdomain 0 → 𝔽))
    (h_agreement :
      correlated_agreement_density
        (Fₛ f)
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (2 ^ n))
      ≤ α)
    {m : ℕ}
    (m_ge_3 : m ≥ 3)
    {ι : Type} [Fintype ι] [Nonempty ι]
    (G : Finset ι) (δ : ℝ≥0∞) (queries l : ℕ)
    (domain_size_cond : (2 ^ (∑ i, (s i : ℕ))) * d ≤ 2 ^ n)
    (h_proximity :
      Code.jointProximity
        (C := (ReedSolomon.code
          (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (2 ^ n)).carrier)
        (u := f) (δ := 1 - α)) :
    fri_query_soundness (n := n) (ω := ω) (f := f)
      (h_agreement := h_agreement) (m_ge_3 := m_ge_3) := by
  exact
    fri_query_soundness_of_queryRoundProbabilityBoundAndBatchedFRIOracleLens
      (n := n) (s := s) (d := d) (ω := ω)
      f h_agreement m_ge_3 G δ queries l domain_size_cond
      (agreementBridge :=
        Code.jointProximity
          (C := (ReedSolomon.code
            (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (2 ^ n)).carrier)
          (u := f) (δ := 1 - α))
      (fun _h_query _h_lens h_joint =>
        fri_query_soundness_of_jointProximity
          (n := n) (ω := ω) f h_agreement m_ge_3 h_joint)
      h_proximity

/-- Probability-route Claim 8.2 front door from the affine-line correlated-agreement predicate.

This is the query-level probability analogue of the density-route affine-line CA wrapper. -/
theorem fri_query_soundness_of_queryRoundProbabilityBoundAndBatchedFRIOracleLensAndAffineLineCA
    {α : ℝ≥0}
    (f : Fin 2 → (ω.subdomain 0 → 𝔽))
    (h_agreement :
      correlated_agreement_density
        (Fₛ f)
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (2 ^ n))
      ≤ α)
    {m : ℕ}
    (m_ge_3 : m ≥ 3)
    {ι : Type} [Fintype ι] [Nonempty ι]
    (G : Finset ι) (δ : ℝ≥0∞) (queries l : ℕ)
    (domain_size_cond : (2 ^ (∑ i, (s i : ℕ))) * d ≤ 2 ^ n)
    {ε : ℝ≥0}
    (h_ca :
      ProximityGap.δ_ε_correlatedAgreementAffineLines
        (F := 𝔽) (A := 𝔽) (ι := ω.subdomain 0)
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (2 ^ n)).carrier
        (1 - α) ε)
    (h_prob :
      Pr_{let z ← $ᵖ 𝔽}[
        δᵣ(f 0 + z • f 1,
          (ReedSolomon.code
            (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (2 ^ n)).carrier)
          ≤ 1 - α] > ε) :
    fri_query_soundness (n := n) (ω := ω) (f := f)
      (h_agreement := h_agreement) (m_ge_3 := m_ge_3) := by
  exact
    fri_query_soundness_of_queryRoundProbabilityBoundAndBatchedFRIOracleLensAndJointProximity
      (n := n) (s := s) (d := d) (ω := ω) (t := 1)
      (f := f) h_agreement m_ge_3 G δ queries l domain_size_cond
      (ProximityGap.jointProximity_of_δ_ε_correlatedAgreementAffineLines
        (F := 𝔽) (A := 𝔽) (ι := ω.subdomain 0)
        (C :=
          (ReedSolomon.code
            (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (2 ^ n)).carrier)
        (δ := 1 - α) (ε := ε) (u := f) h_ca h_prob)

/-- Probability-route Claim 8.2 affine-line front door specialized to the BCIKS20
Reed-Solomon affine-line correlated-agreement theorem on the Batched FRI subdomain.

Compared with `...AndAffineLineCA`, callers no longer supply the packaged
`δ_ε_correlatedAgreementAffineLines` predicate.  The remaining coding-theoretic hypotheses are
the BCIKS20 affine-line theorem inputs: the strict coefficient-polynomial residual, the closed
boundary residual, the square-root-radius side condition, and the affine-line probability trigger.
-/
theorem fri_query_soundness_of_queryRoundProbabilityBoundAndBatchedFRIOracleLensAndRSAffineLine
    {α : ℝ≥0}
    (f : Fin 2 → (ω.subdomain 0 → 𝔽))
    (h_agreement :
      correlated_agreement_density
        (Fₛ f)
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (2 ^ n))
      ≤ α)
    {m : ℕ}
    (m_ge_3 : m ≥ 3)
    {ι : Type} [Fintype ι] [Nonempty ι]
    (G : Finset ι) (δ : ℝ≥0∞) (queries l : ℕ)
    (domain_size_cond : (2 ^ (∑ i, (s i : ℕ))) * d ≤ 2 ^ n)
    (hStrictCoeff :
      ProximityGap.StrictCoeffPolysResidual
        (F := 𝔽) (ι := ω.subdomain 0) (k := 1) (deg := 2 ^ n)
        (domain := (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽)) (δ := 1 - α))
    (hBoundaryCard :
      ProximityGap.BoundaryCardResidual
        (F := 𝔽) (ι := ω.subdomain 0) (k := 1) (deg := 2 ^ n)
        (domain := (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽)) (δ := 1 - α))
    (hδ :
      1 - α ≤
        1 - ReedSolomon.sqrtRate
          (2 ^ n) (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽))
    (h_prob :
      Pr_{let z ← $ᵖ 𝔽}[
        δᵣ(f 0 + z • f 1,
          (ReedSolomon.code
            (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (2 ^ n)).carrier)
          ≤ 1 - α] >
        ProximityGap.errorBound
          (1 - α) (2 ^ n) (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽)) :
    fri_query_soundness (n := n) (ω := ω) (f := f)
      (h_agreement := h_agreement) (m_ge_3 := m_ge_3) := by
  classical
  let rsDomain : ω.subdomain 0 ↪ 𝔽 := ⟨fun x => x, by simp⟩
  haveI : NeZero (2 ^ n) := ⟨pow_ne_zero n (by norm_num)⟩
  have hStrictCoeff' :
      ProximityGap.StrictCoeffPolysResidual
        (F := 𝔽) (ι := ω.subdomain 0) (k := 1) (deg := 2 ^ n)
        (domain := rsDomain) (δ := 1 - α) := by
    simpa [rsDomain] using hStrictCoeff
  have hBoundaryCard' :
      ProximityGap.BoundaryCardResidual
        (F := 𝔽) (ι := ω.subdomain 0) (k := 1) (deg := 2 ^ n)
        (domain := rsDomain) (δ := 1 - α) := by
    simpa [rsDomain] using hBoundaryCard
  have hδ' :
      1 - α ≤ 1 - ReedSolomon.sqrtRate (2 ^ n) rsDomain := by
    simpa [rsDomain] using hδ
  have hprob' :
      Pr_{let z ← $ᵖ 𝔽}[
        δᵣ(f 0 + z • f 1,
          (ReedSolomon.code rsDomain (2 ^ n)).carrier)
          ≤ 1 - α] >
        ProximityGap.errorBound (1 - α) (2 ^ n) rsDomain := by
    simpa [rsDomain] using h_prob
  exact
    fri_query_soundness_of_queryRoundProbabilityBoundAndBatchedFRIOracleLensAndAffineLineCA
      (n := n) (s := s) (d := d) (ω := ω)
      (f := f) h_agreement m_ge_3 G δ queries l domain_size_cond
      (ε := ProximityGap.errorBound (1 - α) (2 ^ n) rsDomain)
      (ProximityGap.RS_correlatedAgreement_affineLines
        (ι := ω.subdomain 0) (F := 𝔽) (deg := 2 ^ n)
        (domain := rsDomain) (δ := 1 - α)
        hStrictCoeff' hBoundaryCard' hδ')
      hprob'

omit [Nontrivial 𝔽] in
/-- Probability-route Claim 8.2 front door from the affine-spaces correlated-agreement predicate.

The query-round probability theorem and Batched FRI lens are discharged; the remaining
coding-theoretic inputs are the affine-spaces CA predicate and its probability trigger. -/
theorem fri_query_soundness_of_queryRoundProbabilityBoundAndBatchedFRIOracleLensAndAffineSpacesCA
    {t : ℕ}
    {α : ℝ≥0}
    (f : Fin t.succ → (ω.subdomain 0 → 𝔽))
    (h_agreement :
      correlated_agreement_density
        (Fₛ f)
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (2 ^ n))
      ≤ α)
    {m : ℕ}
    (m_ge_3 : m ≥ 3)
    {ι : Type} [Fintype ι] [Nonempty ι]
    (G : Finset ι) (δ : ℝ≥0∞) (queries l : ℕ)
    (domain_size_cond : (2 ^ (∑ i, (s i : ℕ))) * d ≤ 2 ^ n)
    {ε : ℝ≥0}
    (h_ca :
      ProximityGap.δ_ε_correlatedAgreementAffineSpaces
        (F := 𝔽) (A := 𝔽) (ι := ω.subdomain 0) (k := t)
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (2 ^ n)).carrier
        (1 - α) ε)
    (h_prob :
      Pr_{let y ← $ᵖ ↥(Affine.affineSubspaceAtOrigin (F := 𝔽) (f 0) (Fin.tail f))}[
        δᵣ(y.1,
          (ReedSolomon.code
            (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (2 ^ n)).carrier)
          ≤ 1 - α] > ε) :
    fri_query_soundness (n := n) (ω := ω) (f := f)
      (h_agreement := h_agreement) (m_ge_3 := m_ge_3) := by
  exact
    fri_query_soundness_of_queryRoundProbabilityBoundAndBatchedFRIOracleLensAndJointProximity
      (n := n) (s := s) (d := d) (ω := ω)
      (f := f) h_agreement m_ge_3 G δ queries l domain_size_cond
      (ProximityGap.jointProximity_of_δ_ε_correlatedAgreementAffineSpaces
        (F := 𝔽) (A := 𝔽) (ι := ω.subdomain 0) (k := t)
        (C :=
          (ReedSolomon.code
            (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (2 ^ n)).carrier)
        (δ := 1 - α) (ε := ε) (u := f) h_ca h_prob)

/-- Probability-route Claim 8.2 front door from the polynomial-curve correlated-agreement
predicate. -/
theorem fri_query_soundness_of_queryRoundProbabilityBoundAndBatchedFRIOracleLensAndCurveCA
    {t : ℕ}
    {α : ℝ≥0}
    (f : Fin t.succ → (ω.subdomain 0 → 𝔽))
    (h_agreement :
      correlated_agreement_density
        (Fₛ f)
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (2 ^ n))
      ≤ α)
    {m : ℕ}
    (m_ge_3 : m ≥ 3)
    {ι : Type} [Fintype ι] [Nonempty ι]
    (G : Finset ι) (δ : ℝ≥0∞) (queries l : ℕ)
    (domain_size_cond : (2 ^ (∑ i, (s i : ℕ))) * d ≤ 2 ^ n)
    {ε : ℝ≥0}
    (h_ca :
      ProximityGap.δ_ε_correlatedAgreementCurves
        (F := 𝔽) (A := 𝔽) (ι := ω.subdomain 0) (k := t)
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (2 ^ n)).carrier
        (1 - α) ε)
    (h_prob :
      Pr_{let r ← $ᵖ 𝔽}[
        δᵣ(∑ i : Fin (t + 1), (r ^ (i : ℕ)) • f i,
          (ReedSolomon.code
            (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (2 ^ n)).carrier)
          ≤ 1 - α] > t * ε) :
    fri_query_soundness (n := n) (ω := ω) (f := f)
      (h_agreement := h_agreement) (m_ge_3 := m_ge_3) := by
  exact
    fri_query_soundness_of_queryRoundProbabilityBoundAndBatchedFRIOracleLensAndJointProximity
      (n := n) (s := s) (d := d) (ω := ω)
      (f := f) h_agreement m_ge_3 G δ queries l domain_size_cond
      (ProximityGap.jointProximity_of_δ_ε_correlatedAgreementCurves
        (F := 𝔽) (A := 𝔽) (ι := ω.subdomain 0) (k := t)
        (C :=
          (ReedSolomon.code
            (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (2 ^ n)).carrier)
        (δ := 1 - α) (ε := ε) (u := f) h_ca h_prob)

/-- Probability-route Claim 8.2 polynomial-curve front door specialized to the BCIKS20
Reed-Solomon curve correlated-agreement theorem on the Batched FRI subdomain.

Callers provide the BCIKS20 curve theorem inputs and the curve probability trigger directly,
rather than a pre-packaged `δ_ε_correlatedAgreementCurves` predicate. -/
theorem fri_query_soundness_of_queryRoundProbabilityBoundAndBatchedFRIOracleLensAndRSCurve
    {t : ℕ}
    {α : ℝ≥0}
    (f : Fin t.succ → (ω.subdomain 0 → 𝔽))
    (h_agreement :
      correlated_agreement_density
        (Fₛ f)
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (2 ^ n))
      ≤ α)
    {m : ℕ}
    (m_ge_3 : m ≥ 3)
    {ι : Type} [Fintype ι] [Nonempty ι]
    (G : Finset ι) (δ : ℝ≥0∞) (queries l : ℕ)
    (domain_size_cond : (2 ^ (∑ i, (s i : ℕ))) * d ≤ 2 ^ n)
    (hStrictCoeff :
      ProximityGap.StrictCoeffPolysResidual
        (F := 𝔽) (ι := ω.subdomain 0) (k := t) (deg := 2 ^ n)
        (domain := (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽)) (δ := 1 - α))
    (hBoundary :
      ProximityGap.BoundaryProbabilityResidual
        (F := 𝔽) (ι := ω.subdomain 0) (k := t) (deg := 2 ^ n)
        (domain := (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽)) (δ := 1 - α))
    (hδ :
      1 - α ≤
        1 - ReedSolomon.sqrtRate
          (2 ^ n) (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽))
    (h_prob :
      Pr_{let r ← $ᵖ 𝔽}[
        δᵣ(∑ i : Fin (t + 1), (r ^ (i : ℕ)) • f i,
          (ReedSolomon.code
            (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (2 ^ n)).carrier)
          ≤ 1 - α] >
        t *
          ProximityGap.errorBound
            (1 - α) (2 ^ n) (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽)) :
    fri_query_soundness (n := n) (ω := ω) (f := f)
      (h_agreement := h_agreement) (m_ge_3 := m_ge_3) := by
  classical
  let rsDomain : ω.subdomain 0 ↪ 𝔽 := ⟨fun x => x, by simp⟩
  haveI : NeZero (2 ^ n) := ⟨pow_ne_zero n (by norm_num)⟩
  have hStrictCoeff' :
      ProximityGap.StrictCoeffPolysResidual
        (F := 𝔽) (ι := ω.subdomain 0) (k := t) (deg := 2 ^ n)
        (domain := rsDomain) (δ := 1 - α) := by
    simpa [rsDomain] using hStrictCoeff
  have hBoundary' :
      ProximityGap.BoundaryProbabilityResidual
        (F := 𝔽) (ι := ω.subdomain 0) (k := t) (deg := 2 ^ n)
        (domain := rsDomain) (δ := 1 - α) := by
    simpa [rsDomain] using hBoundary
  have hδ' :
      1 - α ≤ 1 - ReedSolomon.sqrtRate (2 ^ n) rsDomain := by
    simpa [rsDomain] using hδ
  have hprob' :
      Pr_{let r ← $ᵖ 𝔽}[
        δᵣ(∑ i : Fin (t + 1), (r ^ (i : ℕ)) • f i,
          (ReedSolomon.code rsDomain (2 ^ n)).carrier)
          ≤ 1 - α] >
        t * ProximityGap.errorBound (1 - α) (2 ^ n) rsDomain := by
    simpa [rsDomain] using h_prob
  exact
    fri_query_soundness_of_queryRoundProbabilityBoundAndBatchedFRIOracleLensAndCurveCA
      (n := n) (s := s) (d := d) (ω := ω)
      (f := f) h_agreement m_ge_3 G δ queries l domain_size_cond
      (ε := ProximityGap.errorBound (1 - α) (2 ^ n) rsDomain)
      (ProximityGap.correlatedAgreement_affine_curves
        (ι := ω.subdomain 0) (F := 𝔽) (k := t) (deg := 2 ^ n)
        (domain := rsDomain) (δ := 1 - α)
        hStrictCoeff' hBoundary' hδ')
      hprob'

/-! ### Axiom audit (issue #14 probability adapter) -/

#print axioms Fri.QueryRound.probabilityAcceptanceBound
#print axioms Fri.QueryRound.probabilityAcceptanceBound_holds
#print axioms Fri.QueryRound.probabilityDetectionBound
#print axioms Fri.QueryRound.probabilityDetectionBound_holds
#print axioms Fri.FriQuerySoundnessParts.of_queryRoundProbabilityBound
#print axioms Fri.fri_query_soundness_of_queryRoundProbabilityBound
#print axioms Fri.FriQuerySoundnessParts.of_queryRoundProbabilityBoundAndBatchedFRIOracleLens
#print axioms Fri.fri_query_soundness_of_queryRoundProbabilityBoundAndBatchedFRIOracleLens
set_option linter.style.longLine false in
#print axioms Fri.fri_query_soundness_of_queryRoundProbabilityBoundAndBatchedFRIOracleLensAndJointProximity
set_option linter.style.longLine false in
#print axioms Fri.fri_query_soundness_of_queryRoundProbabilityBoundAndBatchedFRIOracleLensAndAffineLineCA
set_option linter.style.longLine false in
#print axioms Fri.fri_query_soundness_of_queryRoundProbabilityBoundAndBatchedFRIOracleLensAndRSAffineLine
set_option linter.style.longLine false in
#print axioms Fri.fri_query_soundness_of_queryRoundProbabilityBoundAndBatchedFRIOracleLensAndAffineSpacesCA
set_option linter.style.longLine false in
#print axioms Fri.fri_query_soundness_of_queryRoundProbabilityBoundAndBatchedFRIOracleLensAndCurveCA
set_option linter.style.longLine false in
#print axioms Fri.fri_query_soundness_of_queryRoundProbabilityBoundAndBatchedFRIOracleLensAndRSCurve

end ProbabilityAdapter
end Fri
