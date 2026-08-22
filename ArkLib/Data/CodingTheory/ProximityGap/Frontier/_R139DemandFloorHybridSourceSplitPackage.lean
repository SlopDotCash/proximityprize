/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R138DemandFloorHybridTailSourceSplit

/-!
# Packaged source-split hybrid certificates

R137/R138 expose source-split finite-prefix and tail interfaces.  This file bundles those inputs
into one certificate object so concrete producers can hand off a single package: a cutoff `R`, a
KKH26-certified finite rung set, a ladder-certified finite rung set, a cover of `[6,R]`, and a
source-split tail theorem.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R139DemandFloorHybridSourceSplitPackage

open ArkLib.ProximityGap.Frontier.R109DemandFloorGeneralBudgetBridge
open ArkLib.ProximityGap.Frontier.R115DemandFloorTailReduction
open ArkLib.ProximityGap.Frontier.R120DemandFloorNaturalCertificatePackage
open ArkLib.ProximityGap.Frontier.R121DemandFloorTailTheoremInterface
open ArkLib.ProximityGap.Frontier.R132DemandFloorHybridMajorants
open ArkLib.ProximityGap.Frontier.R133DemandFloorHybridCutoff
open ArkLib.ProximityGap.Frontier.R136DemandFloorHybridBoundedPrefix
open ArkLib.ProximityGap.Frontier.R137DemandFloorHybridSourceSplit
open ArkLib.ProximityGap.Frontier.R138DemandFloorHybridTailSourceSplit

/-- A bundled source-split certificate for the hybrid demand tail. -/
structure SourceSplitHybridCertificate (Bad : ℕ → ℕ → ℕ) : Type where
  R : ℕ
  kkhRungs : Finset ℕ
  ladderRungs : Finset ℕ
  cover : Finset.Icc 6 R ⊆ kkhRungs ∪ ladderRungs
  kkhFinite : HasKKH26CensusDominatorsOn Bad kkhRungs
  ladderFinite : HasLadderMajorantsOn Bad ladderRungs
  tail : HasSourceSplitMajorantsAbove Bad R

/-- A source-split package gives the active finite-prefix certificate at its cutoff. -/
theorem active_prefix_of_source_split_certificate
    (Bad : ℕ → ℕ → ℕ)
    (C : SourceSplitHybridCertificate Bad) :
    HasHybridMajorantsActivePrefix Bad C.R :=
  hybrid_active_prefix_of_source_split_cover Bad C.R C.kkhRungs C.ladderRungs
    C.cover C.kkhFinite C.ladderFinite

/-- A source-split package gives the hybrid tail certificate at its cutoff. -/
theorem hybrid_above_of_source_split_certificate
    (Bad : ℕ → ℕ → ℕ)
    (C : SourceSplitHybridCertificate Bad) :
    HasHybridMajorantsAbove Bad C.R :=
  hybrid_above_of_source_split_above Bad C.R C.tail

/-- A source-split package gives uniform hybrid majorants. -/
theorem hybrid_majorants_of_source_split_certificate
    (Bad : ℕ → ℕ → ℕ)
    (C : SourceSplitHybridCertificate Bad) :
    HasHybridMajorants Bad :=
  hybrid_majorants_of_active_prefix_and_tail Bad C.R
    (active_prefix_of_source_split_certificate Bad C)
    (hybrid_above_of_source_split_certificate Bad C)

/-- Closed prefix plus a source-split package gives the natural demand certificate at `g`. -/
theorem natural_demand_certificate_of_prefix_and_source_split_certificate
    (Bad : ℕ → ℕ → ℕ)
    (C : SourceSplitHybridCertificate Bad)
    (g : ℕ) (hg : 3 ≤ g)
    (hprefix : AgreesWithClosedDemandPrefix Bad g) :
    HasNaturalDemandCertificate Bad g :=
  natural_demand_certificate_of_prefix_and_hybrid_majorants Bad
    (hybrid_majorants_of_source_split_certificate Bad C) g hg hprefix

/-- Uniform closed prefixes plus a source-split package give the natural demand theorem. -/
theorem natural_demand_theorem_of_prefixes_and_source_split_certificate
    (Bad : ℕ → ℕ → ℕ)
    (C : SourceSplitHybridCertificate Bad)
    (hprefix : ∀ g : ℕ, 3 ≤ g → AgreesWithClosedDemandPrefix Bad g) :
    NaturalDemandCertificateTheorem Bad :=
  natural_demand_theorem_of_prefixes_and_hybrid_majorants Bad
    (hybrid_majorants_of_source_split_certificate Bad C) hprefix

/-- Uniform closed prefixes plus a source-split package give the divisibility-form budget. -/
theorem demand_floor_of_dvd_four_prefixes_and_source_split_certificate
    (Bad : ℕ → ℕ → ℕ)
    (C : SourceSplitHybridCertificate Bad)
    (hprefix : ∀ g : ℕ, 3 ≤ g → AgreesWithClosedDemandPrefix Bad g)
    (r n : ℕ)
    (hn : 4 ∣ n)
    (hg : 3 ≤ n / 4)
    (hr : 3 ≤ r)
    (hrg : r ≤ n / 4) :
    Bad r n ≤ deepBandBudgetR r n := by
  exact demand_floor_of_dvd_four_prefixes_and_hybrid_majorants Bad
    (hybrid_majorants_of_source_split_certificate Bad C)
    hprefix r n hn hg hr hrg

/-- Uniform closed prefixes plus a source-split package give the positive-rung
divisibility-form budget. -/
theorem demand_floor_positive_of_dvd_four_prefixes_and_source_split_certificate
    (Bad : ℕ → ℕ → ℕ)
    (C : SourceSplitHybridCertificate Bad)
    (hprefix : ∀ g : ℕ, 3 ≤ g → AgreesWithClosedDemandPrefix Bad g)
    (r n : ℕ)
    (hn : 4 ∣ n)
    (hg : 3 ≤ n / 4)
    (hr0 : r ≠ 0)
    (hr1 : r ≠ 1)
    (hr2 : r ≠ 2)
    (hrg : r ≤ n / 4) :
    Bad r n ≤ deepBandBudgetR r n := by
  exact demand_floor_positive_of_dvd_four_prefixes_and_hybrid_majorants Bad
    (hybrid_majorants_of_source_split_certificate Bad C)
    hprefix r n hn hg hr0 hr1 hr2 hrg

/-- A budget overrun refutes any source-split certificate with closed prefixes. -/
theorem not_source_split_certificate_and_prefixes_of_dvd_four_budget_lt_bad
    (Bad : ℕ → ℕ → ℕ)
    (r n : ℕ)
    (hn : 4 ∣ n)
    (hg : 3 ≤ n / 4)
    (hr : 3 ≤ r)
    (hrg : r ≤ n / 4)
    (hgt : deepBandBudgetR r n < Bad r n) :
    ¬ (∃ _ : SourceSplitHybridCertificate Bad,
      ∀ g : ℕ, 3 ≤ g → AgreesWithClosedDemandPrefix Bad g) := by
  rintro ⟨C, hprefix⟩
  exact (Nat.not_le.mpr hgt)
    (demand_floor_of_dvd_four_prefixes_and_source_split_certificate
      Bad C hprefix r n hn hg hr hrg)

/-- Positive-rung obstruction for any source-split certificate with closed prefixes. -/
theorem not_source_split_certificate_and_prefixes_of_dvd_four_budget_lt_bad_positive
    (Bad : ℕ → ℕ → ℕ)
    (r n : ℕ)
    (hn : 4 ∣ n)
    (hg : 3 ≤ n / 4)
    (hr0 : r ≠ 0)
    (hr1 : r ≠ 1)
    (hr2 : r ≠ 2)
    (hrg : r ≤ n / 4)
    (hgt : deepBandBudgetR r n < Bad r n) :
    ¬ (∃ _ : SourceSplitHybridCertificate Bad,
      ∀ g : ℕ, 3 ≤ g → AgreesWithClosedDemandPrefix Bad g) := by
  rintro ⟨C, hprefix⟩
  exact (Nat.not_le.mpr hgt)
    (demand_floor_positive_of_dvd_four_prefixes_and_source_split_certificate
      Bad C hprefix r n hn hg hr0 hr1 hr2 hrg)

end ArkLib.ProximityGap.Frontier.R139DemandFloorHybridSourceSplitPackage

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R139DemandFloorHybridSourceSplitPackage.SourceSplitHybridCertificate
#print axioms
  ArkLib.ProximityGap.Frontier.R139DemandFloorHybridSourceSplitPackage.active_prefix_of_source_split_certificate
#print axioms
  ArkLib.ProximityGap.Frontier.R139DemandFloorHybridSourceSplitPackage.hybrid_above_of_source_split_certificate
#print axioms
  ArkLib.ProximityGap.Frontier.R139DemandFloorHybridSourceSplitPackage.hybrid_majorants_of_source_split_certificate
#print axioms
  ArkLib.ProximityGap.Frontier.R139DemandFloorHybridSourceSplitPackage.natural_demand_certificate_of_prefix_and_source_split_certificate
#print axioms
  ArkLib.ProximityGap.Frontier.R139DemandFloorHybridSourceSplitPackage.natural_demand_theorem_of_prefixes_and_source_split_certificate
#print axioms
  ArkLib.ProximityGap.Frontier.R139DemandFloorHybridSourceSplitPackage.demand_floor_of_dvd_four_prefixes_and_source_split_certificate
#print axioms
  ArkLib.ProximityGap.Frontier.R139DemandFloorHybridSourceSplitPackage.demand_floor_positive_of_dvd_four_prefixes_and_source_split_certificate
#print axioms
  ArkLib.ProximityGap.Frontier.R139DemandFloorHybridSourceSplitPackage.not_source_split_certificate_and_prefixes_of_dvd_four_budget_lt_bad
#print axioms
  ArkLib.ProximityGap.Frontier.R139DemandFloorHybridSourceSplitPackage.not_source_split_certificate_and_prefixes_of_dvd_four_budget_lt_bad_positive
