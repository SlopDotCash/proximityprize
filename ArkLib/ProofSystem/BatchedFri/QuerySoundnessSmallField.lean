/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Extensions.ProofSystem.BatchedFri.Security
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Curves.CorrelatedAgreementSmallField

/-!
# Batched FRI query soundness from unconditional CA instances (issue #303)

The Claim 8.2 / Claim 8.3 density-route front doors in `BatchedFri/Security.lean`
(`fri_query_soundness_of_…AndRSAffineLine`, `…AndRSCurve`, and the Claim 8.3 query-lift twins)
still carry the BCIKS20 named residuals (`StrictCoeffPolysResidual`, `BoundaryCardResidual`,
`BoundaryProbabilityResidual`) as hypotheses.  This file routes the **unconditional** small-field
BCIKS20 correlated-agreement instances of `CorrelatedAgreementSmallField.lean` (issue #304) through
those front doors, so that their residual hypotheses are *proved*, not assumed.

**Honest scope: every theorem below is vacuous** — its premises are jointly unsatisfiable — so none
of them is a usable Claim 8.2 / 8.3 instance:

* the affine-line front door asks for `q ≤ |ω.subdomain 0|`, which never holds because the FFT
  domain consists of distinct nonzero field elements (`not_card_field_le_card_subdomainZero`);
* the curve front doors work in the regime `q ≤ t · |ω.subdomain 0|` with a strict radius
  `δ < 1 - √ρ`, where BCIKS20's error bound satisfies `1 ≤ t · errorBound`, so their probability
  trigger `Pr[…] > t · errorBound` can never hold (`not_prob_gt_mul_errorBound_of_card_le`).

This is the threshold-vacuous regime of `CorrelatedAgreementSmallField.lean`; the deployed
large-field band (`q > t · n`) remains the open #304 content shared with STIR.

AUDIT REPAIR (2026-10-28, L70): the codes here used to have degree `2 ^ n` on the `2 ^ n`-point
domain (full rate, `√ρ = 1`), so every strict radius premise `δ < 1 - √ρ = 0` was additionally
unsatisfiable and the conclusions were tautologies; they now use the batched FRI input degree
`friDegree s d`.  The earlier summary of these theorems as "the full batched-to-base FRI
query-soundness lift with the correlated-agreement bridge discharged" was inaccurate.
-/

namespace Fri
section Fri

open OracleComp OracleSpec ProtocolSpec ReedSolomon Domain
open NNReal Finset Function ProbabilityTheory

variable {𝔽 : Type} [NonBinaryField 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] [Nontrivial 𝔽]
private noncomputable local instance : SampleableType 𝔽 := SampleableType.ofFintype 𝔽
variable (n : ℕ) {k : ℕ}
variable (s : Fin (k + 1) → ℕ+) (d : ℕ+)
variable {ω : SmoothCosetFftDomain n 𝔽}

section Soundness

variable (domain_size_cond : (2 ^ (∑ i, (s i : ℕ))) * d ≤ 2 ^ n)

omit [Nontrivial 𝔽] in
/-- **The affine-line small-field hypothesis never holds.**  `q ≤ |ω.subdomain 0|` is impossible:
the FFT domain consists of distinct nonzero field elements (`card_subdomainZero_lt_card_field`).
Hence `fri_query_soundness_of_card_le_affineLine` is vacuous. -/
theorem not_card_field_le_card_subdomainZero :
    ¬ ((Fintype.card 𝔽 : ℝ≥0) ≤ (Fintype.card (ω.subdomain 0) : ℝ≥0)) := by
  intro h
  have hlt := card_subdomainZero_lt_card_field n (ω := ω)
  have h' : Fintype.card 𝔽 ≤ Fintype.card (ω.subdomain 0) := by exact_mod_cast h
  omega

/-- **The curve small-field front doors are vacuous.**  In the regime of the unconditional
small-field CA instance (`q ≤ t · |ω.subdomain 0|` and a strict radius `δ < 1 - √ρ`), BCIKS20's
error bound satisfies `|ω.subdomain 0| / q ≤ errorBound` (`DivergenceOfSets.errorBound_ge_const`),
so `1 ≤ t · errorBound` and the curve probability trigger `Pr[…] > t · errorBound` required by
`fri_query_soundness_of_card_le_curve` and its Claim 8.3 twins can never hold. -/
theorem not_prob_gt_mul_errorBound_of_card_le {t : ℕ} {δ : ℝ≥0}
    (u : Fin t.succ → (ω.subdomain 0 → 𝔽))
    (hδ : δ < 1 - ReedSolomon.sqrtRate (friDegree s d) (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽))
    (hq : (Fintype.card 𝔽 : ℝ≥0) ≤ (t : ℝ≥0) * (Fintype.card (ω.subdomain 0) : ℝ≥0)) :
    ¬ (Pr_{let r ← $ᵖ 𝔽}[
        δᵣ(∑ i : Fin (t + 1), (r ^ (i : ℕ)) • u i,
          (ReedSolomon.code
            (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d)).carrier)
          ≤ δ] >
        t * ProximityGap.errorBound δ (friDegree s d)
          (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽)) := by
  intro hprob
  have hconst :
      (Fintype.card (ω.subdomain 0) : ℝ≥0) / (Fintype.card 𝔽 : ℝ≥0) ≤
        ProximityGap.errorBound δ (friDegree s d) (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) :=
    DivergenceOfSets.errorBound_ge_const (deg := friDegree s d)
      (domain := (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽)) (NeZero.pos _) hδ
  have hqpos : (0 : ℝ≥0) < (Fintype.card 𝔽 : ℝ≥0) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card 𝔽)
  have hone : (1 : ℝ≥0) ≤ (t : ℝ≥0) *
      ((Fintype.card (ω.subdomain 0) : ℝ≥0) / (Fintype.card 𝔽 : ℝ≥0)) := by
    rw [mul_div_assoc', le_div_iff₀ hqpos, one_mul]
    exact hq
  have hstep : (1 : ℝ≥0) ≤ (t : ℝ≥0) *
      ProximityGap.errorBound δ (friDegree s d) (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) :=
    le_trans hone (mul_le_mul_of_nonneg_left hconst (by positivity))
  have h1 : (1 : ENNReal) ≤ (t : ENNReal) *
      (ProximityGap.errorBound δ (friDegree s d) (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) :
        ENNReal) := by
    exact_mod_cast hstep
  exact absurd (lt_of_le_of_lt h1 hprob) (not_lt.mpr (PMF.coe_le_one _ _))

include s d domain_size_cond in
/-- **Claim 8.2 (`fri_query_soundness`) from the small-field affine-line CA instance — vacuous.**

The correlated-agreement predicate is supplied by the *unconditional* BCIKS20 affine-line
instance `RS_correlatedAgreement_affineLines_of_card_le` (no residual hypotheses; valid for
`q ≤ |ω.subdomain 0|`), so the only remaining inputs are the strict-radius side condition `hδ`,
the field-size bound `hq`, and the affine-line probability trigger `h_prob` on the actual
two-row batch.  The field-size bound `hq` can never hold (`not_card_field_le_card_subdomainZero`),
so this theorem has no instances. -/
theorem fri_query_soundness_of_card_le_affineLine
    {α : ℝ≥0}
    (f : Fin 2 → (ω.subdomain 0 → 𝔽))
    (h_agreement :
      correlated_agreement_density
        (Fₛ f)
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d))
      ≤ α)
    {m : ℕ}
    (m_ge_3 : m ≥ 3)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : Finset ι) (δ : ℝ≥0) (queries l : ℕ)
    (hδ :
      (1 - α : ℝ≥0) <
        1 - ReedSolomon.sqrtRate (friDegree s d) (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽))
    (hq : (Fintype.card 𝔽 : ℝ≥0) ≤ (Fintype.card (ω.subdomain 0) : ℝ≥0))
    (h_prob :
      Pr_{let z ← $ᵖ 𝔽}[
        δᵣ(f 0 + z • f 1,
          (ReedSolomon.code
            (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d)).carrier)
          ≤ 1 - α] >
        ProximityGap.errorBound
          (1 - α) (friDegree s d) (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽)) :
    fri_query_soundness (n := n) (ω := ω) (f := f)
      (h_agreement := h_agreement) (m_ge_3 := m_ge_3) := by
  classical
  haveI : NeZero (friDegree s d) := inferInstance
  exact
    fri_query_soundness_of_queryRoundDensityBoundAndCanonicalBatchingSeamAndAffineLineCA
      (n := n) (s := s) (d := d) (ω := ω)
      (f := f) h_agreement m_ge_3 G δ queries l domain_size_cond
      (ε := ProximityGap.errorBound
        (1 - α) (friDegree s d) (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽))
      (ProximityGap.RS_correlatedAgreement_affineLines_of_card_le
        (ι := ω.subdomain 0) (F := 𝔽) (deg := friDegree s d)
        (domain := (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽)) (δ := 1 - α)
        hδ hq)
      h_prob

include s d domain_size_cond in
/-- **Claim 8.2 (`fri_query_soundness`) from the small-field curve CA instance — vacuous.**

The correlated-agreement predicate is supplied by the *unconditional* BCIKS20 affine-curves
instance `correlatedAgreement_affine_curves_of_card_le` (no residual hypotheses; valid for
`q ≤ t·|ω.subdomain 0|`), covering arbitrary batch size `t + 1`.  Together, `hδ` and `hq` make the
probability trigger `h_prob` impossible (`not_prob_gt_mul_errorBound_of_card_le`), so this theorem
has no instances. -/
theorem fri_query_soundness_of_card_le_curve
    {t : ℕ}
    {α : ℝ≥0}
    (f : Fin t.succ → (ω.subdomain 0 → 𝔽))
    (h_agreement :
      correlated_agreement_density
        (Fₛ f)
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d))
      ≤ α)
    {m : ℕ}
    (m_ge_3 : m ≥ 3)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : Finset ι) (δ : ℝ≥0) (queries l : ℕ)
    (hδ :
      (1 - α : ℝ≥0) <
        1 - ReedSolomon.sqrtRate (friDegree s d) (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽))
    (hq : (Fintype.card 𝔽 : ℝ≥0) ≤ (t : ℝ≥0) * (Fintype.card (ω.subdomain 0) : ℝ≥0))
    (h_prob :
      Pr_{let r ← $ᵖ 𝔽}[
        δᵣ(∑ i : Fin (t + 1), (r ^ (i : ℕ)) • f i,
          (ReedSolomon.code
            (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d)).carrier)
          ≤ 1 - α] >
        t *
          ProximityGap.errorBound
            (1 - α) (friDegree s d) (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽)) :
    fri_query_soundness (n := n) (ω := ω) (f := f)
      (h_agreement := h_agreement) (m_ge_3 := m_ge_3) := by
  classical
  haveI : NeZero (friDegree s d) := inferInstance
  exact
    fri_query_soundness_of_queryRoundDensityBoundAndCanonicalBatchingSeamAndCurveCA
      (n := n) (s := s) (d := d) (ω := ω)
      (f := f) h_agreement m_ge_3 G δ queries l domain_size_cond
      (ε := ProximityGap.errorBound
        (1 - α) (friDegree s d) (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽))
      (ProximityGap.correlatedAgreement_affine_curves_of_card_le
        (ι := ω.subdomain 0) (F := 𝔽) (k := t) (deg := friDegree s d)
        (domain := (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽)) (δ := 1 - α)
        hδ hq)
      h_prob

/-- **Claim 8.3 query-lift (`friSoundnessQueryLift`) from the small-field curve CA instance
(base-FRI lift) — vacuous.**

The full-domain joint-agreement conclusion of Claim 8.3 at the FRI radius
`δ = 1 - √ρ·(1 + 1/(2m))`, with the correlated-agreement bridge supplied by the unconditional
small-field curves instance and lifted from `ω.subdomain 0` to the base FRI domain `ω` through
`fri_query_soundness_lift_subdomainZero_to_domain`.  As for `fri_query_soundness_of_card_le_curve`,
`hδ` and `hq` make `h_prob` impossible (`not_prob_gt_mul_errorBound_of_card_le`), so this theorem
has no instances. -/
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
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d))
      ≤
      (let ρ_sqrt :=
        ReedSolomon.sqrtRate
          (friDegree s d)
          (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
       ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0)))))
    (hδ :
      (1 -
        (let ρ_sqrt :=
          ReedSolomon.sqrtRate
            (friDegree s d)
            (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
         ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0)))) : ℝ≥0) <
        1 - ReedSolomon.sqrtRate (friDegree s d) (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽))
    (hq : (Fintype.card 𝔽 : ℝ≥0) ≤ (t : ℝ≥0) * (Fintype.card (ω.subdomain 0) : ℝ≥0))
    (h_prob :
      let C :=
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d)).carrier
      let u : Code.WordStack 𝔽 (Fin t.succ) (ω.subdomain 0) :=
        fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x)
      let δ_fri : ℝ≥0 :=
        1 -
          (let ρ_sqrt :=
            ReedSolomon.sqrtRate
              (friDegree s d)
              (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
           ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0))))
      Pr_{
        let r ← $ᵖ 𝔽
      }[δᵣ(∑ i : Fin (t + 1), (r ^ (i : ℕ)) • u i, C) ≤ δ_fri] >
        t *
          ProximityGap.errorBound δ_fri (friDegree s d)
            (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽)) :
    friSoundnessQueryLift (n := n) (s := s) (d := d) (ω := ω) f m_ge_3 := by
  classical
  haveI : NeZero (friDegree s d) := inferInstance
  exact
    friSoundnessQueryLift_of_queryRoundDensityBoundAndCanonicalBatchingSeamAndCurveCA
      (n := n) (s := s) (d := d) (ω := ω)
      f m_ge_3 G δ_query queries l domain_size_cond h_agreement
      (ε_ca := ProximityGap.errorBound
        (1 -
          (let ρ_sqrt :=
            ReedSolomon.sqrtRate
              (friDegree s d)
              (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
           ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0)))))
        (friDegree s d) (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽))
      (ProximityGap.correlatedAgreement_affine_curves_of_card_le
        (ι := ω.subdomain 0) (F := 𝔽) (k := t) (deg := friDegree s d)
        (domain := (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽))
        hδ hq)
      h_prob

open ENNReal in
/-- **Claim 8.3 residual (`fri_soundness_canonicalIndependent`) from the small-field curve CA
instance — vacuous.**

The end-to-end Claim 8.3 conditional statement for Batched FRI with the correlated-agreement
bridge supplied by the unconditional small-field curves instance.  Remaining inputs: the FRI
radius side condition `hδ`, the field-size bound `hq`, the density bound `h_agreement` on the
reindexed batch, and the curve probability trigger `h_prob`; the last cannot hold together with
`hδ` and `hq` (`not_prob_gt_mul_errorBound_of_card_le`), so this theorem has no instances. -/
theorem fri_soundness_canonicalIndependent_of_card_le_curve
    {t l m : ℕ}
    (f : Fin t.succ → (ω → 𝔽))
    (m_ge_3 : m ≥ 3)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : Finset ι) (δ_query : ℝ≥0) (queries : ℕ)
    (h_agreement :
      correlated_agreement_density
        (Fₛ (fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x)))
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d))
      ≤
      (let ρ_sqrt :=
        ReedSolomon.sqrtRate
          (friDegree s d)
          (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
       ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0)))))
    (hδ :
      (1 -
        (let ρ_sqrt :=
          ReedSolomon.sqrtRate
            (friDegree s d)
            (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
         ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0)))) : ℝ≥0) <
        1 - ReedSolomon.sqrtRate (friDegree s d) (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽))
    (hq : (Fintype.card 𝔽 : ℝ≥0) ≤ (t : ℝ≥0) * (Fintype.card (ω.subdomain 0) : ℝ≥0))
    (h_prob :
      let C :=
        (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (friDegree s d)).carrier
      let u : Code.WordStack 𝔽 (Fin t.succ) (ω.subdomain 0) :=
        fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x)
      let δ_fri : ℝ≥0 :=
        1 -
          (let ρ_sqrt :=
            ReedSolomon.sqrtRate
              (friDegree s d)
              (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
           ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0))))
      Pr_{
        let r ← $ᵖ 𝔽
      }[δᵣ(∑ i : Fin (t + 1), (r ^ (i : ℕ)) • u i, C) ≤ δ_fri] >
        t *
          ProximityGap.errorBound δ_fri (friDegree s d)
            (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽)) :
    fri_soundness_canonicalIndependent (n := n) (s := s) (d := d) (ω := ω) (l := l)
      (domain_size_cond := domain_size_cond) f m_ge_3 := by
  exact
    fri_soundness_canonicalIndependent_of_queryLift
      (n := n) (s := s) (d := d) (ω := ω) (domain_size_cond := domain_size_cond)
      f m_ge_3
      (friSoundnessQueryLift_of_card_le_curve
        (n := n) (s := s) (d := d) (ω := ω)
        f m_ge_3 G δ_query queries l domain_size_cond h_agreement hδ hq h_prob)

end Soundness

end Fri
end Fri

/-! ### Axiom audit (issue #303 small-field query-soundness discharge) -/

#print axioms Fri.not_card_field_le_card_subdomainZero
#print axioms Fri.not_prob_gt_mul_errorBound_of_card_le
#print axioms Fri.fri_query_soundness_of_card_le_affineLine
#print axioms Fri.fri_query_soundness_of_card_le_curve
#print axioms Fri.friSoundnessQueryLift_of_card_le_curve
#print axioms Fri.fri_soundness_canonicalIndependent_of_card_le_curve
