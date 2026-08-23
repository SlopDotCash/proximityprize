/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.BatchedFri.QueryRoundSoundness

/-!
# Batched FRI soundness adapters from RS affine-line query routes

`QueryRoundSoundness.lean` and `Security.lean` expose parallel probability-route and density-route
Reed-Solomon affine-line wrappers. This companion module records that their input packages carry
the same fixed-radius BCIKS20 data and provides cross-route full-domain wrappers without growing
the near-cap query-round and security files.
-/

namespace Fri
section RSAffineLineSoundnessAdapter

open scoped ENNReal NNReal BigOperators
open OracleComp OracleSpec ProtocolSpec ReedSolomon Domain
open NNReal Finset Function ProbabilityTheory

variable {𝔽 : Type} [NonBinaryField 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] [Nontrivial 𝔽]
variable {n : ℕ} {k : ℕ}
variable {s : Fin (k + 1) → ℕ+} {d : ℕ+}
variable {ω : SmoothCosetFftDomain n 𝔽}

/-- Probability-route RS affine-line inputs can feed density-route wrappers because the two input
packages carry the same fixed-radius BCIKS20 data. -/
theorem friRSAffineLineDensityInputs_of_probabilityInputs
    (f : Fin 2 → (ω → 𝔽)) (m : ℕ)
    (h : friRSAffineLineProbabilityInputs (n := n) (ω := ω) f m) :
    friRSAffineLineDensityInputs (n := n) (ω := ω) f m := by
  simpa [friRSAffineLineProbabilityInputs, friRSAffineLineDensityInputs] using h

/-- Density-route RS affine-line inputs can feed probability-route wrappers because the two input
packages carry the same fixed-radius BCIKS20 data. -/
theorem friRSAffineLineProbabilityInputs_of_densityInputs
    (f : Fin 2 → (ω → 𝔽)) (m : ℕ)
    (h : friRSAffineLineDensityInputs (n := n) (ω := ω) f m) :
    friRSAffineLineProbabilityInputs (n := n) (ω := ω) f m := by
  simpa [friRSAffineLineProbabilityInputs, friRSAffineLineDensityInputs] using h

/-- The probability-route and density-route RS affine-line input packages are equivalent. -/
theorem friRSAffineLineProbabilityInputs_iff_densityInputs
    (f : Fin 2 → (ω → 𝔽)) (m : ℕ) :
    friRSAffineLineProbabilityInputs (n := n) (ω := ω) f m ↔
      friRSAffineLineDensityInputs (n := n) (ω := ω) f m := by
  constructor
  · exact friRSAffineLineDensityInputs_of_probabilityInputs (n := n) (ω := ω) f m
  · exact friRSAffineLineProbabilityInputs_of_densityInputs (n := n) (ω := ω) f m

/-- Project the strict coefficient-polynomial residual from probability-route RS affine-line
inputs. -/
theorem friRSAffineLineProbabilityInputs.strictCoeff
    (f : Fin 2 → (ω → 𝔽)) (m : ℕ)
    (h : friRSAffineLineProbabilityInputs (n := n) (ω := ω) f m) :
    let rsDomain : ω.subdomain 0 ↪ 𝔽 := ⟨fun x => x, by simp⟩
    let α_fri : ℝ≥0 :=
      let ρ_sqrt :=
        ReedSolomon.sqrtRate
          (2 ^ n)
          (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
      ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0)))
    let δ_fri : ℝ≥0 := 1 - α_fri
    ProximityGap.StrictCoeffPolysResidual
      (F := 𝔽) (ι := ω.subdomain 0) (k := 1) (deg := 2 ^ n)
      (domain := rsDomain) (δ := δ_fri) := by
  dsimp
  dsimp [friRSAffineLineProbabilityInputs] at h
  exact h.1

/-- Project the boundary-cardinality residual from probability-route RS affine-line inputs. -/
theorem friRSAffineLineProbabilityInputs.boundaryCard
    (f : Fin 2 → (ω → 𝔽)) (m : ℕ)
    (h : friRSAffineLineProbabilityInputs (n := n) (ω := ω) f m) :
    let rsDomain : ω.subdomain 0 ↪ 𝔽 := ⟨fun x => x, by simp⟩
    let α_fri : ℝ≥0 :=
      let ρ_sqrt :=
        ReedSolomon.sqrtRate
          (2 ^ n)
          (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
      ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0)))
    let δ_fri : ℝ≥0 := 1 - α_fri
    ProximityGap.BoundaryCardResidual
      (F := 𝔽) (ι := ω.subdomain 0) (k := 1) (deg := 2 ^ n)
      (domain := rsDomain) (δ := δ_fri) := by
  dsimp
  dsimp [friRSAffineLineProbabilityInputs] at h
  exact h.2.1

/-- Project the square-root-radius side condition from probability-route RS affine-line inputs. -/
theorem friRSAffineLineProbabilityInputs.sqrtRadius
    (f : Fin 2 → (ω → 𝔽)) (m : ℕ)
    (h : friRSAffineLineProbabilityInputs (n := n) (ω := ω) f m) :
    let rsDomain : ω.subdomain 0 ↪ 𝔽 := ⟨fun x => x, by simp⟩
    let α_fri : ℝ≥0 :=
      let ρ_sqrt :=
        ReedSolomon.sqrtRate
          (2 ^ n)
          (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
      ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0)))
    let δ_fri : ℝ≥0 := 1 - α_fri
    δ_fri ≤ 1 - ReedSolomon.sqrtRate (2 ^ n) rsDomain := by
  dsimp
  dsimp [friRSAffineLineProbabilityInputs] at h
  exact h.2.2.1

/-- Project the affine-line probability trigger from probability-route RS affine-line inputs. -/
theorem friRSAffineLineProbabilityInputs.lineProbability
    (f : Fin 2 → (ω → 𝔽)) (m : ℕ)
    (h : friRSAffineLineProbabilityInputs (n := n) (ω := ω) f m) :
    let rsDomain : ω.subdomain 0 ↪ 𝔽 := ⟨fun x => x, by simp⟩
    let u : Code.WordStack 𝔽 (Fin 2) (ω.subdomain 0) :=
      fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x)
    let α_fri : ℝ≥0 :=
      let ρ_sqrt :=
        ReedSolomon.sqrtRate
          (2 ^ n)
          (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
      ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0)))
    let δ_fri : ℝ≥0 := 1 - α_fri
    Pr_{let z ← $ᵖ 𝔽}[
      δᵣ(u 0 + z • u 1, (ReedSolomon.code rsDomain (2 ^ n)).carrier) ≤ δ_fri] >
      ProximityGap.errorBound δ_fri (2 ^ n) rsDomain := by
  dsimp
  dsimp [friRSAffineLineProbabilityInputs] at h
  exact h.2.2.2

/-- Project the strict coefficient-polynomial residual from density-route RS affine-line inputs. -/
theorem friRSAffineLineDensityInputs.strictCoeff
    (f : Fin 2 → (ω → 𝔽)) (m : ℕ)
    (h : friRSAffineLineDensityInputs (n := n) (ω := ω) f m) :
    let rsDomain : ω.subdomain 0 ↪ 𝔽 := ⟨fun x => x, by simp⟩
    let α_fri : ℝ≥0 :=
      let ρ_sqrt :=
        ReedSolomon.sqrtRate
          (2 ^ n)
          (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
      ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0)))
    let δ_fri : ℝ≥0 := 1 - α_fri
    ProximityGap.StrictCoeffPolysResidual
      (F := 𝔽) (ι := ω.subdomain 0) (k := 1) (deg := 2 ^ n)
      (domain := rsDomain) (δ := δ_fri) := by
  exact friRSAffineLineProbabilityInputs.strictCoeff (n := n) (ω := ω) f m
    (friRSAffineLineProbabilityInputs_of_densityInputs (n := n) (ω := ω) f m h)

/-- Project the boundary-cardinality residual from density-route RS affine-line inputs. -/
theorem friRSAffineLineDensityInputs.boundaryCard
    (f : Fin 2 → (ω → 𝔽)) (m : ℕ)
    (h : friRSAffineLineDensityInputs (n := n) (ω := ω) f m) :
    let rsDomain : ω.subdomain 0 ↪ 𝔽 := ⟨fun x => x, by simp⟩
    let α_fri : ℝ≥0 :=
      let ρ_sqrt :=
        ReedSolomon.sqrtRate
          (2 ^ n)
          (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
      ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0)))
    let δ_fri : ℝ≥0 := 1 - α_fri
    ProximityGap.BoundaryCardResidual
      (F := 𝔽) (ι := ω.subdomain 0) (k := 1) (deg := 2 ^ n)
      (domain := rsDomain) (δ := δ_fri) := by
  exact friRSAffineLineProbabilityInputs.boundaryCard (n := n) (ω := ω) f m
    (friRSAffineLineProbabilityInputs_of_densityInputs (n := n) (ω := ω) f m h)

/-- Project the square-root-radius side condition from density-route RS affine-line inputs. -/
theorem friRSAffineLineDensityInputs.sqrtRadius
    (f : Fin 2 → (ω → 𝔽)) (m : ℕ)
    (h : friRSAffineLineDensityInputs (n := n) (ω := ω) f m) :
    let rsDomain : ω.subdomain 0 ↪ 𝔽 := ⟨fun x => x, by simp⟩
    let α_fri : ℝ≥0 :=
      let ρ_sqrt :=
        ReedSolomon.sqrtRate
          (2 ^ n)
          (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
      ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0)))
    let δ_fri : ℝ≥0 := 1 - α_fri
    δ_fri ≤ 1 - ReedSolomon.sqrtRate (2 ^ n) rsDomain := by
  exact friRSAffineLineProbabilityInputs.sqrtRadius (n := n) (ω := ω) f m
    (friRSAffineLineProbabilityInputs_of_densityInputs (n := n) (ω := ω) f m h)

/-- Project the affine-line probability trigger from density-route RS affine-line inputs. -/
theorem friRSAffineLineDensityInputs.lineProbability
    (f : Fin 2 → (ω → 𝔽)) (m : ℕ)
    (h : friRSAffineLineDensityInputs (n := n) (ω := ω) f m) :
    let rsDomain : ω.subdomain 0 ↪ 𝔽 := ⟨fun x => x, by simp⟩
    let u : Code.WordStack 𝔽 (Fin 2) (ω.subdomain 0) :=
      fun i x => f i ((subdomainZeroEquiv (n := n) (ω := ω)) x)
    let α_fri : ℝ≥0 :=
      let ρ_sqrt :=
        ReedSolomon.sqrtRate
          (2 ^ n)
          (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
      ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0)))
    let δ_fri : ℝ≥0 := 1 - α_fri
    Pr_{let z ← $ᵖ 𝔽}[
      δᵣ(u 0 + z • u 1, (ReedSolomon.code rsDomain (2 ^ n)).carrier) ≤ δ_fri] >
      ProximityGap.errorBound δ_fri (2 ^ n) rsDomain := by
  exact friRSAffineLineProbabilityInputs.lineProbability (n := n) (ω := ω) f m
    (friRSAffineLineProbabilityInputs_of_densityInputs (n := n) (ω := ω) f m h)

/-- Probability-route RS affine-line inputs can feed the density-route full-domain query lift. -/
theorem friSoundnessQueryLift_densityRSAffineLine_of_probabilityInputs
    {m : ℕ}
    (f : Fin 2 → (ω → 𝔽))
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
    (h_rs : friRSAffineLineProbabilityInputs (n := n) (ω := ω) f m) :
    friSoundnessQueryLift (n := n) (ω := ω) f m_ge_3 :=
  friSoundnessQueryLift_of_queryRoundDensityBoundAndBatchedFRIOracleLensAndRSAffineLine
    (n := n) (s := s) (d := d) (ω := ω)
    f m_ge_3 G δ_query queries l domain_size_cond h_agreement
    (friRSAffineLineDensityInputs_of_probabilityInputs (n := n) (ω := ω) f m h_rs)

/-- Density-route RS affine-line inputs can feed the probability-route full-domain query lift. -/
theorem friSoundnessQueryLift_probabilityRSAffineLine_of_densityInputs
    {m : ℕ}
    (f : Fin 2 → (ω → 𝔽))
    (m_ge_3 : m ≥ 3)
    {ι : Type} [Fintype ι] [Nonempty ι]
    (G : Finset ι) (δ_query : ℝ≥0∞) (queries l : ℕ)
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
    (h_rs : friRSAffineLineDensityInputs (n := n) (ω := ω) f m) :
    friSoundnessQueryLift (n := n) (ω := ω) f m_ge_3 :=
  friSoundnessQueryLift_of_queryRoundProbabilityBoundAndBatchedFRIOracleLensAndRSAffineLine
    (n := n) (s := s) (d := d) (ω := ω)
    f m_ge_3 G δ_query queries l domain_size_cond h_agreement
    (friRSAffineLineProbabilityInputs_of_densityInputs (n := n) (ω := ω) f m h_rs)

open ENNReal in
/-- Probability-route RS affine-line inputs can feed the density-route full-domain Claim 8.3
residual wrapper. -/
theorem fri_soundness_densityRSAffineLine_of_probabilityInputs
    {l m : ℕ}
    (f : Fin 2 → (ω → 𝔽))
    (m_ge_3 : m ≥ 3)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : Finset ι) (δ_query : ℝ≥0) (queries : ℕ)
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
    (h_rs : friRSAffineLineProbabilityInputs (n := n) (ω := ω) f m) :
    fri_soundness (n := n) (s := s) (d := d) (ω := ω) (l := l)
      (domain_size_cond := domain_size_cond) f m_ge_3 := by
  exact
    fri_soundness_of_queryLift
      (n := n) (s := s) (d := d) (ω := ω) (domain_size_cond := domain_size_cond)
      f m_ge_3
      (friSoundnessQueryLift_densityRSAffineLine_of_probabilityInputs
        (n := n) (s := s) (d := d) (ω := ω)
        f m_ge_3 G δ_query queries l domain_size_cond h_agreement h_rs)

open ENNReal in
/-- Density-route RS affine-line inputs can feed the probability-route full-domain Claim 8.3
residual wrapper. -/
theorem fri_soundness_probabilityRSAffineLine_of_densityInputs
    {l m : ℕ}
    (f : Fin 2 → (ω → 𝔽))
    (m_ge_3 : m ≥ 3)
    {ι : Type} [Fintype ι] [Nonempty ι]
    (G : Finset ι) (δ_query : ℝ≥0∞) (queries : ℕ)
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
    (h_rs : friRSAffineLineDensityInputs (n := n) (ω := ω) f m) :
    fri_soundness (n := n) (s := s) (d := d) (ω := ω) (l := l)
      (domain_size_cond := domain_size_cond) f m_ge_3 := by
  exact
    fri_soundness_of_queryLift
      (n := n) (s := s) (d := d) (ω := ω) (domain_size_cond := domain_size_cond)
      f m_ge_3
      (friSoundnessQueryLift_probabilityRSAffineLine_of_densityInputs
        (n := n) (s := s) (d := d) (ω := ω)
        f m_ge_3 G δ_query queries l domain_size_cond h_agreement h_rs)

/-- Raw full-domain Claim 8.2 conclusion from probability-route RS affine-line inputs routed
through the density query-round theorem. -/
theorem fri_jointAgreement_densityRSAffineLine_of_probabilityInputs
    {m : ℕ}
    (f : Fin 2 → (ω → 𝔽))
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
    (h_rs : friRSAffineLineProbabilityInputs (n := n) (ω := ω) f m) :
    Code.jointAgreement
      (F := 𝔽)
      (κ := Fin 2)
      (ι := ω)
      (C := (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω ↪ 𝔽) (2 ^ n)).carrier)
      (δ :=
        let ρ_sqrt :=
          ReedSolomon.sqrtRate
            (2 ^ n)
            (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
        let α : ℝ≥0 := (ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0))))
        1 - α)
      (W := f) := by
  change friSoundnessQueryLift (n := n) (ω := ω) f m_ge_3
  exact
    friSoundnessQueryLift_densityRSAffineLine_of_probabilityInputs
      (n := n) (s := s) (d := d) (ω := ω)
      f m_ge_3 G δ_query queries l domain_size_cond h_agreement h_rs

/-- Raw full-domain Claim 8.2 conclusion from density-route RS affine-line inputs routed through
the probability query-round theorem. -/
theorem fri_jointAgreement_probabilityRSAffineLine_of_densityInputs
    {m : ℕ}
    (f : Fin 2 → (ω → 𝔽))
    (m_ge_3 : m ≥ 3)
    {ι : Type} [Fintype ι] [Nonempty ι]
    (G : Finset ι) (δ_query : ℝ≥0∞) (queries l : ℕ)
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
    (h_rs : friRSAffineLineDensityInputs (n := n) (ω := ω) f m) :
    Code.jointAgreement
      (F := 𝔽)
      (κ := Fin 2)
      (ι := ω)
      (C := (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω ↪ 𝔽) (2 ^ n)).carrier)
      (δ :=
        let ρ_sqrt :=
          ReedSolomon.sqrtRate
            (2 ^ n)
            (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
        let α : ℝ≥0 := (ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0))))
        1 - α)
      (W := f) := by
  change friSoundnessQueryLift (n := n) (ω := ω) f m_ge_3
  exact
    friSoundnessQueryLift_probabilityRSAffineLine_of_densityInputs
      (n := n) (s := s) (d := d) (ω := ω)
      f m_ge_3 G δ_query queries l domain_size_cond h_agreement h_rs

set_option linter.style.longLine false in
#print axioms Fri.friRSAffineLineDensityInputs_of_probabilityInputs
set_option linter.style.longLine false in
#print axioms Fri.friRSAffineLineProbabilityInputs_of_densityInputs
set_option linter.style.longLine false in
#print axioms Fri.friRSAffineLineProbabilityInputs_iff_densityInputs
set_option linter.style.longLine false in
#print axioms Fri.friRSAffineLineProbabilityInputs.strictCoeff
set_option linter.style.longLine false in
#print axioms Fri.friRSAffineLineProbabilityInputs.boundaryCard
set_option linter.style.longLine false in
#print axioms Fri.friRSAffineLineProbabilityInputs.sqrtRadius
set_option linter.style.longLine false in
#print axioms Fri.friRSAffineLineProbabilityInputs.lineProbability
set_option linter.style.longLine false in
#print axioms Fri.friRSAffineLineDensityInputs.strictCoeff
set_option linter.style.longLine false in
#print axioms Fri.friRSAffineLineDensityInputs.boundaryCard
set_option linter.style.longLine false in
#print axioms Fri.friRSAffineLineDensityInputs.sqrtRadius
set_option linter.style.longLine false in
#print axioms Fri.friRSAffineLineDensityInputs.lineProbability
set_option linter.style.longLine false in
#print axioms Fri.friSoundnessQueryLift_densityRSAffineLine_of_probabilityInputs
set_option linter.style.longLine false in
#print axioms Fri.friSoundnessQueryLift_probabilityRSAffineLine_of_densityInputs
set_option linter.style.longLine false in
#print axioms Fri.fri_soundness_densityRSAffineLine_of_probabilityInputs
set_option linter.style.longLine false in
#print axioms Fri.fri_soundness_probabilityRSAffineLine_of_densityInputs
set_option linter.style.longLine false in
#print axioms Fri.fri_jointAgreement_densityRSAffineLine_of_probabilityInputs
set_option linter.style.longLine false in
#print axioms Fri.fri_jointAgreement_probabilityRSAffineLine_of_densityInputs

end RSAffineLineSoundnessAdapter
end Fri
