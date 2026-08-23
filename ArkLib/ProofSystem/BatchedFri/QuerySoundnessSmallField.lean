/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.BatchedFri.Security
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Curves.CorrelatedAgreementSmallField

/-!
# Batched FRI query soundness from unconditional CA instances (issue #303)

The Claim 8.2 / Claim 8.3 density-route front doors in `BatchedFri/Security.lean`
(`fri_query_soundness_of_…AndRSAffineLine`, `…AndRSCurve`, and the Claim 8.3 query-lift twins)
still carry the BCIKS20 named residuals (`StrictCoeffPolysResidual`, `BoundaryCardResidual`,
`BoundaryProbabilityResidual`) as hypotheses.  This file routes the **unconditional** BCIKS20
correlated-agreement instances of `CorrelatedAgreementSmallField.lean` (issue #304: the
vacuous/small-field regime, with *no* residual hypotheses) through those front doors, producing
Claim 8.2 and Claim 8.3 conclusions whose only remaining protocol-side input is the probability
trigger on the actual batch — the residual hypotheses are *proved*, not assumed.

Honest scope: as in `CorrelatedAgreementSmallField.lean`, the unconditional instances hold in the
threshold-vacuous regime (`q ≤ k·n` resp. `q ≤ k·deg²·10⁷`); the deployed large-field band remains
the open #304 content shared with STIR.  Within this regime the theorems below are the full
batched-to-base FRI query-soundness lift with the correlated-agreement bridge discharged.
-/

namespace Fri
section Fri

open OracleComp OracleSpec ProtocolSpec ReedSolomon Domain
open NNReal Finset Function ProbabilityTheory

variable {𝔽 : Type} [NonBinaryField 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] [Nontrivial 𝔽]
variable (n : ℕ) {k : ℕ}
variable (s : Fin (k + 1) → ℕ+) (d : ℕ+)
variable {ω : SmoothCosetFftDomain n 𝔽}

section Soundness

variable (domain_size_cond : (2 ^ (∑ i, (s i : ℕ))) * d ≤ 2 ^ n)

include s d domain_size_cond in
/-- **Claim 8.2 (`fri_query_soundness`) discharged in the small-field regime, affine-line case.**

The correlated-agreement predicate is supplied by the *unconditional* BCIKS20 affine-line
instance `RS_correlatedAgreement_affineLines_of_card_le` (no residual hypotheses; valid for
`q ≤ |ω.subdomain 0|`), so the only remaining inputs are the strict-radius side condition `hδ`,
the field-size bound `hq`, and the affine-line probability trigger `h_prob` on the actual
two-row batch. -/
theorem fri_query_soundness_of_card_le_affineLine
    {α : ℝ≥0}
    (f : Fin 2 → (ω.subdomain 0 → 𝔽))
    (h_agreement :
      correlated_agreement_density
        (Fₛ f)
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (2 ^ n))
      ≤ α)
    {m : ℕ}
    (m_ge_3 : m ≥ 3)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : Finset ι) (δ : ℝ≥0) (queries l : ℕ)
    (hδ :
      (1 - α : ℝ≥0) <
        1 - ReedSolomon.sqrtRate (2 ^ n) (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽))
    (hq : (Fintype.card 𝔽 : ℝ≥0) ≤ (Fintype.card (ω.subdomain 0) : ℝ≥0))
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
  haveI : NeZero (2 ^ n) := ⟨pow_ne_zero n (by norm_num)⟩
  exact
    fri_query_soundness_of_queryRoundDensityBoundAndBatchedFRIOracleLensAndAffineLineCA
      (n := n) (s := s) (d := d) (ω := ω)
      (f := f) h_agreement m_ge_3 G δ queries l domain_size_cond
      (ε := ProximityGap.errorBound
        (1 - α) (2 ^ n) (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽))
      (ProximityGap.RS_correlatedAgreement_affineLines_of_card_le
        (ι := ω.subdomain 0) (F := 𝔽) (deg := 2 ^ n)
        (domain := (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽)) (δ := 1 - α)
        hδ hq)
      h_prob

include s d domain_size_cond in
/-- **Claim 8.2 (`fri_query_soundness`) discharged in the small-field regime, curve case.**

The correlated-agreement predicate is supplied by the *unconditional* BCIKS20 affine-curves
instance `correlatedAgreement_affine_curves_of_card_le` (no residual hypotheses; valid for
`q ≤ t·|ω.subdomain 0|`), covering arbitrary batch size `t + 1`. -/
theorem fri_query_soundness_of_card_le_curve
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
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : Finset ι) (δ : ℝ≥0) (queries l : ℕ)
    (hδ :
      (1 - α : ℝ≥0) <
        1 - ReedSolomon.sqrtRate (2 ^ n) (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽))
    (hq : (Fintype.card 𝔽 : ℝ≥0) ≤ (t : ℝ≥0) * (Fintype.card (ω.subdomain 0) : ℝ≥0))
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
  haveI : NeZero (2 ^ n) := ⟨pow_ne_zero n (by norm_num)⟩
  exact
    fri_query_soundness_of_queryRoundDensityBoundAndBatchedFRIOracleLensAndCurveCA
      (n := n) (s := s) (d := d) (ω := ω)
      (f := f) h_agreement m_ge_3 G δ queries l domain_size_cond
      (ε := ProximityGap.errorBound
        (1 - α) (2 ^ n) (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽))
      (ProximityGap.correlatedAgreement_affine_curves_of_card_le
        (ι := ω.subdomain 0) (F := 𝔽) (k := t) (deg := 2 ^ n)
        (domain := (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽)) (δ := 1 - α)
        hδ hq)
      h_prob

/-- **Claim 8.3 query-lift (`friSoundnessQueryLift`) discharged in the small-field regime
(base-FRI lift, curve case).**

The full-domain joint-agreement conclusion of Claim 8.3 at the FRI radius
`δ = 1 - √ρ·(1 + 1/(2m))`, with the correlated-agreement bridge supplied by the unconditional
small-field curves instance and lifted from `ω.subdomain 0` to the base FRI domain `ω` through
`fri_query_soundness_lift_subdomainZero_to_domain`. -/
theorem friSoundnessQueryLift_of_card_le_curve
    {t m : ℕ}
    (f : Fin t.succ → (ω → 𝔽))
    (m_ge_3 : m ≥ 3)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : Finset ι) (δ_query : ℝ≥0) (queries l : ℕ)
    (domain_size_cond : (2 ^ (∑ i, (s i : ℕ))) * d ≤ 2 ^ n)
    (h_agreement :
      correlated_agreement_density
        (Fₛ (fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x)))
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (2 ^ n))
      ≤
      (let ρ_sqrt :=
        ReedSolomon.sqrtRate
          (2 ^ n)
          (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
       ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0)))))
    (hδ :
      (1 -
        (let ρ_sqrt :=
          ReedSolomon.sqrtRate
            (2 ^ n)
            (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
         ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0)))) : ℝ≥0) <
        1 - ReedSolomon.sqrtRate (2 ^ n) (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽))
    (hq : (Fintype.card 𝔽 : ℝ≥0) ≤ (t : ℝ≥0) * (Fintype.card (ω.subdomain 0) : ℝ≥0))
    (h_prob :
      let C :=
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (2 ^ n)).carrier
      let u : Code.WordStack 𝔽 (Fin t.succ) (ω.subdomain 0) :=
        fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x)
      let δ_fri : ℝ≥0 :=
        1 -
          (let ρ_sqrt :=
            ReedSolomon.sqrtRate
              (2 ^ n)
              (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
           ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0))))
      Pr_{
        let r ← $ᵖ 𝔽
      }[δᵣ(∑ i : Fin (t + 1), (r ^ (i : ℕ)) • u i, C) ≤ δ_fri] >
        t *
          ProximityGap.errorBound δ_fri (2 ^ n)
            (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽)) :
    friSoundnessQueryLift (n := n) (ω := ω) f m_ge_3 := by
  classical
  haveI : NeZero (2 ^ n) := ⟨pow_ne_zero n (by norm_num)⟩
  exact
    friSoundnessQueryLift_of_queryRoundDensityBoundAndBatchedFRIOracleLensAndCurveCA
      (n := n) (s := s) (d := d) (ω := ω)
      f m_ge_3 G δ_query queries l domain_size_cond h_agreement
      (ε_ca := ProximityGap.errorBound
        (1 -
          (let ρ_sqrt :=
            ReedSolomon.sqrtRate
              (2 ^ n)
              (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
           ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0)))))
        (2 ^ n) (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽))
      (ProximityGap.correlatedAgreement_affine_curves_of_card_le
        (ι := ω.subdomain 0) (F := 𝔽) (k := t) (deg := 2 ^ n)
        (domain := (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽))
        hδ hq)
      h_prob

open ENNReal in
/-- **Claim 8.3 residual (`fri_soundness`) discharged in the small-field regime (curve case).**

The end-to-end Claim 8.3 conditional statement for Batched FRI with the correlated-agreement
bridge supplied by the unconditional small-field curves instance.  Remaining inputs: the FRI
radius side condition `hδ`, the field-size bound `hq`, the density bound `h_agreement` on the
reindexed batch, and the curve probability trigger `h_prob`. -/
theorem fri_soundness_of_card_le_curve
    {t l m : ℕ}
    (f : Fin t.succ → (ω → 𝔽))
    (m_ge_3 : m ≥ 3)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : Finset ι) (δ_query : ℝ≥0) (queries : ℕ)
    (h_agreement :
      correlated_agreement_density
        (Fₛ (fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x)))
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (2 ^ n))
      ≤
      (let ρ_sqrt :=
        ReedSolomon.sqrtRate
          (2 ^ n)
          (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
       ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0)))))
    (hδ :
      (1 -
        (let ρ_sqrt :=
          ReedSolomon.sqrtRate
            (2 ^ n)
            (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
         ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0)))) : ℝ≥0) <
        1 - ReedSolomon.sqrtRate (2 ^ n) (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽))
    (hq : (Fintype.card 𝔽 : ℝ≥0) ≤ (t : ℝ≥0) * (Fintype.card (ω.subdomain 0) : ℝ≥0))
    (h_prob :
      let C :=
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (2 ^ n)).carrier
      let u : Code.WordStack 𝔽 (Fin t.succ) (ω.subdomain 0) :=
        fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x)
      let δ_fri : ℝ≥0 :=
        1 -
          (let ρ_sqrt :=
            ReedSolomon.sqrtRate
              (2 ^ n)
              (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
           ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0))))
      Pr_{
        let r ← $ᵖ 𝔽
      }[δᵣ(∑ i : Fin (t + 1), (r ^ (i : ℕ)) • u i, C) ≤ δ_fri] >
        t *
          ProximityGap.errorBound δ_fri (2 ^ n)
            (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽)) :
    fri_soundness (n := n) (s := s) (d := d) (ω := ω) (l := l)
      (domain_size_cond := domain_size_cond) f m_ge_3 := by
  exact
    fri_soundness_of_queryLift
      (n := n) (s := s) (d := d) (ω := ω) (domain_size_cond := domain_size_cond)
      f m_ge_3
      (friSoundnessQueryLift_of_card_le_curve
        (n := n) (s := s) (d := d) (ω := ω)
        f m_ge_3 G δ_query queries l domain_size_cond h_agreement hδ hq h_prob)

end Soundness

end Fri
end Fri

/-! ### Axiom audit (issue #303 small-field query-soundness discharge) -/

#print axioms Fri.fri_query_soundness_of_card_le_affineLine
#print axioms Fri.fri_query_soundness_of_card_le_curve
#print axioms Fri.friSoundnessQueryLift_of_card_le_curve
#print axioms Fri.fri_soundness_of_card_le_curve
