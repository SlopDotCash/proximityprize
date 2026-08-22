/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R132DemandFloorHybridMajorants

/-!
# Cutoff split for hybrid demand-tail majorants

R132 packages the target `HasHybridMajorants Bad`: every active deep rung has either a KKH26
exact-census dominator or a ladder-list majorant.  This file records the standard finite/tail
split for proving that target.  A future finite search or exact-census lane can discharge
`r ≤ R`, while an asymptotic argument handles `R < r`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R133DemandFloorHybridCutoff

open ArkLib.ProximityGap.Frontier.R109DemandFloorGeneralBudgetBridge
open ArkLib.ProximityGap.Frontier.R115DemandFloorTailReduction
open ArkLib.ProximityGap.Frontier.R120DemandFloorNaturalCertificatePackage
open ArkLib.ProximityGap.Frontier.R121DemandFloorTailTheoremInterface
open ArkLib.ProximityGap.Frontier.R132DemandFloorHybridMajorants

/-- Hybrid majorants on the finite side `r ≤ R`. -/
def HasHybridMajorantsBelow (Bad : ℕ → ℕ → ℕ) (R : ℕ) : Prop :=
  ∀ g r : ℕ, 3 ≤ g → 6 ≤ r → r ≤ g → r ≤ R → HasHybridMajorantAt Bad g r

/-- Hybrid majorants on the tail side `R < r`. -/
def HasHybridMajorantsAbove (Bad : ℕ → ℕ → ℕ) (R : ℕ) : Prop :=
  ∀ g r : ℕ, 3 ≤ g → 6 ≤ r → r ≤ g → R < r → HasHybridMajorantAt Bad g r

/-- A cutoff package for proving `HasHybridMajorants`: finite side plus tail side. -/
structure HasHybridMajorantsCutoff (Bad : ℕ → ℕ → ℕ) (R : ℕ) : Prop where
  below : HasHybridMajorantsBelow Bad R
  above : HasHybridMajorantsAbove Bad R

/-- Finite/tail cutoff packages imply the uniform hybrid-majorant target. -/
theorem hybrid_majorants_of_cutoff
    (Bad : ℕ → ℕ → ℕ) (R : ℕ)
    (hcut : HasHybridMajorantsCutoff Bad R) :
    HasHybridMajorants Bad := by
  intro g r hg hr hrg
  by_cases hrR : r ≤ R
  · exact hcut.below g r hg hr hrg hrR
  · exact hcut.above g r hg hr hrg (Nat.lt_of_not_ge hrR)

/-- Closed prefix plus cutoff hybrid majorants give the natural demand certificate at `g`. -/
theorem natural_demand_certificate_of_prefix_and_hybrid_cutoff
    (Bad : ℕ → ℕ → ℕ) (R : ℕ)
    (hcut : HasHybridMajorantsCutoff Bad R)
    (g : ℕ) (hg : 3 ≤ g)
    (hprefix : AgreesWithClosedDemandPrefix Bad g) :
    HasNaturalDemandCertificate Bad g :=
  natural_demand_certificate_of_prefix_and_hybrid_majorants
    Bad (hybrid_majorants_of_cutoff Bad R hcut) g hg hprefix

/-- Uniform closed prefixes plus cutoff hybrid majorants give the natural demand theorem. -/
theorem natural_demand_theorem_of_prefixes_and_hybrid_cutoff
    (Bad : ℕ → ℕ → ℕ) (R : ℕ)
    (hcut : HasHybridMajorantsCutoff Bad R)
    (hprefix : ∀ g : ℕ, 3 ≤ g → AgreesWithClosedDemandPrefix Bad g) :
    NaturalDemandCertificateTheorem Bad :=
  natural_demand_theorem_of_prefixes_and_hybrid_majorants
    Bad (hybrid_majorants_of_cutoff Bad R hcut) hprefix

/-- Cutoff packages give the divisibility-form demand budget, through R132's hybrid consumer. -/
theorem demand_floor_of_dvd_four_prefixes_and_hybrid_cutoff
    (Bad : ℕ → ℕ → ℕ) (R : ℕ)
    (hcut : HasHybridMajorantsCutoff Bad R)
    (hprefix : ∀ g : ℕ, 3 ≤ g → AgreesWithClosedDemandPrefix Bad g)
    (r n : ℕ)
    (hn : 4 ∣ n)
    (hg : 3 ≤ n / 4)
    (hr : 3 ≤ r)
    (hrg : r ≤ n / 4) :
    Bad r n ≤ deepBandBudgetR r n := by
  exact demand_floor_of_dvd_four_prefixes_and_hybrid_majorants Bad
    (hybrid_majorants_of_cutoff Bad R hcut) hprefix r n hn hg hr hrg

/-- Positive-rung divisibility-form demand budget from cutoff hybrid majorants. -/
theorem demand_floor_positive_of_dvd_four_prefixes_and_hybrid_cutoff
    (Bad : ℕ → ℕ → ℕ) (R : ℕ)
    (hcut : HasHybridMajorantsCutoff Bad R)
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
    (hybrid_majorants_of_cutoff Bad R hcut) hprefix r n hn hg hr0 hr1 hr2 hrg

/-- A single divisible-by-four budget overrun refutes every cutoff proof of the hybrid route. -/
theorem not_hybrid_cutoff_and_prefixes_of_dvd_four_budget_lt_bad
    (Bad : ℕ → ℕ → ℕ) (R : ℕ)
    (r n : ℕ)
    (hn : 4 ∣ n)
    (hg : 3 ≤ n / 4)
    (hr : 3 ≤ r)
    (hrg : r ≤ n / 4)
    (hgt : deepBandBudgetR r n < Bad r n) :
    ¬ (HasHybridMajorantsCutoff Bad R ∧
      ∀ g : ℕ, 3 ≤ g → AgreesWithClosedDemandPrefix Bad g) := by
  rintro ⟨hcut, hprefix⟩
  exact (Nat.not_le.mpr hgt)
    (demand_floor_of_dvd_four_prefixes_and_hybrid_cutoff
      Bad R hcut hprefix r n hn hg hr hrg)

/-- Positive-rung version of the cutoff obstruction. -/
theorem not_hybrid_cutoff_and_prefixes_of_dvd_four_budget_lt_bad_positive
    (Bad : ℕ → ℕ → ℕ) (R : ℕ)
    (r n : ℕ)
    (hn : 4 ∣ n)
    (hg : 3 ≤ n / 4)
    (hr0 : r ≠ 0)
    (hr1 : r ≠ 1)
    (hr2 : r ≠ 2)
    (hrg : r ≤ n / 4)
    (hgt : deepBandBudgetR r n < Bad r n) :
    ¬ (HasHybridMajorantsCutoff Bad R ∧
      ∀ g : ℕ, 3 ≤ g → AgreesWithClosedDemandPrefix Bad g) := by
  rintro ⟨hcut, hprefix⟩
  exact (Nat.not_le.mpr hgt)
    (demand_floor_positive_of_dvd_four_prefixes_and_hybrid_cutoff
      Bad R hcut hprefix r n hn hg hr0 hr1 hr2 hrg)

end ArkLib.ProximityGap.Frontier.R133DemandFloorHybridCutoff

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R133DemandFloorHybridCutoff.HasHybridMajorantsBelow
#print axioms
  ArkLib.ProximityGap.Frontier.R133DemandFloorHybridCutoff.HasHybridMajorantsAbove
#print axioms
  ArkLib.ProximityGap.Frontier.R133DemandFloorHybridCutoff.HasHybridMajorantsCutoff
#print axioms
  ArkLib.ProximityGap.Frontier.R133DemandFloorHybridCutoff.hybrid_majorants_of_cutoff
#print axioms
  ArkLib.ProximityGap.Frontier.R133DemandFloorHybridCutoff.natural_demand_certificate_of_prefix_and_hybrid_cutoff
#print axioms
  ArkLib.ProximityGap.Frontier.R133DemandFloorHybridCutoff.natural_demand_theorem_of_prefixes_and_hybrid_cutoff
#print axioms
  ArkLib.ProximityGap.Frontier.R133DemandFloorHybridCutoff.demand_floor_of_dvd_four_prefixes_and_hybrid_cutoff
#print axioms
  ArkLib.ProximityGap.Frontier.R133DemandFloorHybridCutoff.demand_floor_positive_of_dvd_four_prefixes_and_hybrid_cutoff
#print axioms
  ArkLib.ProximityGap.Frontier.R133DemandFloorHybridCutoff.not_hybrid_cutoff_and_prefixes_of_dvd_four_budget_lt_bad
#print axioms
  ArkLib.ProximityGap.Frontier.R133DemandFloorHybridCutoff.not_hybrid_cutoff_and_prefixes_of_dvd_four_budget_lt_bad_positive
