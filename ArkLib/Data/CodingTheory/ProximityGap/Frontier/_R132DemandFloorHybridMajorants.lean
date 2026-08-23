/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R130DemandFloorKKH26PrizeInterface
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R131DemandFloorLadderPrizeInterface

/-!
# Hybrid demand-tail majorants

The demand tail should not have to use the same extremal model at every rung.  R129/R130 expose a
KKH26 exact-census route, while R128/R131 expose a ladder-list majorant route.  This file packages
the mixed route: at each active deep rung, either certificate is enough.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R132DemandFloorHybridMajorants

open ArkLib.ProximityGap.Frontier.R109DemandFloorGeneralBudgetBridge
open ArkLib.ProximityGap.Frontier.R115DemandFloorTailReduction
open ArkLib.ProximityGap.Frontier.R119DemandFloorNaturalTailCertificates
open ArkLib.ProximityGap.Frontier.R120DemandFloorNaturalCertificatePackage
open ArkLib.ProximityGap.Frontier.R121DemandFloorTailTheoremInterface
open ArkLib.ProximityGap.Frontier.R123DemandFloorDivFourInterface
open ArkLib.ProximityGap.Frontier.R125DemandFloorMaximalOrbitProducer
open ArkLib.ProximityGap.Frontier.R128DemandFloorLadderMajorantPackage
open ArkLib.ProximityGap.Frontier.R129DemandFloorKKH26CensusPackage

/-- At one active tail rung, either the KKH26 exact census or a production ladder-list majorant
dominates the bad-count family. -/
def HasHybridMajorantAt (Bad : ℕ → ℕ → ℕ) (g r : ℕ) : Prop :=
  KKH26CensusDominatesAt Bad g r ∨ HasLadderMajorantAt Bad g r

/-- Uniform hybrid route over all active deep rungs. -/
def HasHybridMajorants (Bad : ℕ → ℕ → ℕ) : Prop :=
  ∀ g r : ℕ, 3 ≤ g → 6 ≤ r → r ≤ g → HasHybridMajorantAt Bad g r

/-- A uniform KKH26 census route is a uniform hybrid route. -/
theorem hybrid_majorants_of_kkh26_census_dominators
    (Bad : ℕ → ℕ → ℕ)
    (hdom : HasKKH26CensusDominators Bad) :
    HasHybridMajorants Bad := by
  intro g r hg hr hrg
  exact Or.inl (hdom g r hg hr hrg)

/-- A uniform ladder-list route is a uniform hybrid route. -/
theorem hybrid_majorants_of_ladder_majorants
    (Bad : ℕ → ℕ → ℕ)
    (hmajor : HasLadderMajorants Bad) :
    HasHybridMajorants Bad := by
  intro g r hg hr hrg
  exact Or.inr (hmajor g r hg hr hrg)

/-- A single hybrid majorant gives the R125 maximal-binomial allowance at its rung. -/
theorem maximal_allowance_of_hybrid_majorant_at
    (Bad : ℕ → ℕ → ℕ) (g r : ℕ)
    (hr : 6 ≤ r)
    (W : HasHybridMajorantAt Bad g r) :
    Bad r (4 * g) ≤ (4 * g) * maximalTailOP g r + 1 := by
  rcases W with hkkh | hladder
  · exact maximal_allowance_of_kkh26_census_dominator_at Bad g r hr hkkh
  · exact maximal_allowance_of_ladder_majorant_at Bad g r hladder

/-- Uniform hybrid majorants imply the R125 maximal tail count bound. -/
theorem maximal_tail_count_bound_of_hybrid_majorants
    (Bad : ℕ → ℕ → ℕ)
    (hhyb : HasHybridMajorants Bad) :
    MaximalTailCountBound Bad := by
  intro g r hg hr hrg
  exact maximal_allowance_of_hybrid_majorant_at Bad g r hr (hhyb g r hg hr hrg)

/-- Uniform hybrid majorants produce natural-range deep-tail orbit certificates. -/
theorem deep_tail_orbit_certificates_le_of_hybrid_majorants
    (Bad : ℕ → ℕ → ℕ)
    (hhyb : HasHybridMajorants Bad)
    (g : ℕ) (hg : 3 ≤ g) :
    HasDeepTailOrbitCertificatesLe Bad g := by
  intro r hr hrg
  refine ⟨maximalTailOP g r, le_rfl, ?_⟩
  exact maximal_allowance_of_hybrid_majorant_at Bad g r hr (hhyb g r hg hr hrg)

/-- Closed prefix plus uniform hybrid majorants give the natural demand certificate at `g`. -/
theorem natural_demand_certificate_of_prefix_and_hybrid_majorants
    (Bad : ℕ → ℕ → ℕ)
    (hhyb : HasHybridMajorants Bad)
    (g : ℕ) (hg : 3 ≤ g)
    (hprefix : AgreesWithClosedDemandPrefix Bad g) :
    HasNaturalDemandCertificate Bad g :=
  ⟨hprefix, deep_tail_orbit_certificates_le_of_hybrid_majorants Bad hhyb g hg⟩

/-- Uniform closed prefixes plus uniform hybrid majorants give the natural demand theorem. -/
theorem natural_demand_theorem_of_prefixes_and_hybrid_majorants
    (Bad : ℕ → ℕ → ℕ)
    (hhyb : HasHybridMajorants Bad)
    (hprefix : ∀ g : ℕ, 3 ≤ g → AgreesWithClosedDemandPrefix Bad g) :
    NaturalDemandCertificateTheorem Bad := by
  intro g hg
  exact natural_demand_certificate_of_prefix_and_hybrid_majorants
    Bad hhyb g hg (hprefix g hg)

/-- Divisibility-form demand budget from closed prefixes plus hybrid majorants. -/
theorem demand_floor_of_dvd_four_prefixes_and_hybrid_majorants
    (Bad : ℕ → ℕ → ℕ)
    (hhyb : HasHybridMajorants Bad)
    (hprefix : ∀ g : ℕ, 3 ≤ g → AgreesWithClosedDemandPrefix Bad g)
    (r n : ℕ)
    (hn : 4 ∣ n)
    (hg : 3 ≤ n / 4)
    (hr : 3 ≤ r)
    (hrg : r ≤ n / 4) :
    Bad r n ≤ deepBandBudgetR r n := by
  exact demand_floor_of_dvd_four_natural_demand_theorem Bad
    (natural_demand_theorem_of_prefixes_and_hybrid_majorants Bad hhyb hprefix)
    r n hn hg hr hrg

/-- Positive-rung divisibility-form demand budget from hybrid majorants. -/
theorem demand_floor_positive_of_dvd_four_prefixes_and_hybrid_majorants
    (Bad : ℕ → ℕ → ℕ)
    (hhyb : HasHybridMajorants Bad)
    (hprefix : ∀ g : ℕ, 3 ≤ g → AgreesWithClosedDemandPrefix Bad g)
    (r n : ℕ)
    (hn : 4 ∣ n)
    (hg : 3 ≤ n / 4)
    (hr0 : r ≠ 0)
    (hr1 : r ≠ 1)
    (hr2 : r ≠ 2)
    (hrg : r ≤ n / 4) :
    Bad r n ≤ deepBandBudgetR r n := by
  exact demand_floor_positive_of_dvd_four_natural_demand_theorem Bad
    (natural_demand_theorem_of_prefixes_and_hybrid_majorants Bad hhyb hprefix)
    r n hn hg hr0 hr1 hr2 hrg

/-- A single divisible-by-four budget overrun refutes the combined hybrid route. -/
theorem not_prefixes_and_hybrid_majorants_of_dvd_four_budget_lt_bad
    (Bad : ℕ → ℕ → ℕ)
    (r n : ℕ)
    (hn : 4 ∣ n)
    (hg : 3 ≤ n / 4)
    (hr : 3 ≤ r)
    (hrg : r ≤ n / 4)
    (hgt : deepBandBudgetR r n < Bad r n) :
    ¬ (HasHybridMajorants Bad ∧
      ∀ g : ℕ, 3 ≤ g → AgreesWithClosedDemandPrefix Bad g) := by
  rintro ⟨hhyb, hprefix⟩
  exact (Nat.not_le.mpr hgt)
    (demand_floor_of_dvd_four_prefixes_and_hybrid_majorants
      Bad hhyb hprefix r n hn hg hr hrg)

/-- Positive-rung version of the hybrid-route obstruction. -/
theorem not_prefixes_and_hybrid_majorants_of_dvd_four_budget_lt_bad_positive
    (Bad : ℕ → ℕ → ℕ)
    (r n : ℕ)
    (hn : 4 ∣ n)
    (hg : 3 ≤ n / 4)
    (hr0 : r ≠ 0)
    (hr1 : r ≠ 1)
    (hr2 : r ≠ 2)
    (hrg : r ≤ n / 4)
    (hgt : deepBandBudgetR r n < Bad r n) :
    ¬ (HasHybridMajorants Bad ∧
      ∀ g : ℕ, 3 ≤ g → AgreesWithClosedDemandPrefix Bad g) := by
  rintro ⟨hhyb, hprefix⟩
  exact (Nat.not_le.mpr hgt)
    (demand_floor_positive_of_dvd_four_prefixes_and_hybrid_majorants
      Bad hhyb hprefix r n hn hg hr0 hr1 hr2 hrg)

end ArkLib.ProximityGap.Frontier.R132DemandFloorHybridMajorants

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R132DemandFloorHybridMajorants.HasHybridMajorantAt
#print axioms
  ArkLib.ProximityGap.Frontier.R132DemandFloorHybridMajorants.HasHybridMajorants
#print axioms
  ArkLib.ProximityGap.Frontier.R132DemandFloorHybridMajorants.hybrid_majorants_of_kkh26_census_dominators
#print axioms
  ArkLib.ProximityGap.Frontier.R132DemandFloorHybridMajorants.hybrid_majorants_of_ladder_majorants
#print axioms
  ArkLib.ProximityGap.Frontier.R132DemandFloorHybridMajorants.maximal_allowance_of_hybrid_majorant_at
#print axioms
  ArkLib.ProximityGap.Frontier.R132DemandFloorHybridMajorants.maximal_tail_count_bound_of_hybrid_majorants
#print axioms
  ArkLib.ProximityGap.Frontier.R132DemandFloorHybridMajorants.deep_tail_orbit_certificates_le_of_hybrid_majorants
#print axioms
  ArkLib.ProximityGap.Frontier.R132DemandFloorHybridMajorants.natural_demand_certificate_of_prefix_and_hybrid_majorants
#print axioms
  ArkLib.ProximityGap.Frontier.R132DemandFloorHybridMajorants.natural_demand_theorem_of_prefixes_and_hybrid_majorants
#print axioms
  ArkLib.ProximityGap.Frontier.R132DemandFloorHybridMajorants.demand_floor_of_dvd_four_prefixes_and_hybrid_majorants
#print axioms
  ArkLib.ProximityGap.Frontier.R132DemandFloorHybridMajorants.demand_floor_positive_of_dvd_four_prefixes_and_hybrid_majorants
#print axioms
  ArkLib.ProximityGap.Frontier.R132DemandFloorHybridMajorants.not_prefixes_and_hybrid_majorants_of_dvd_four_budget_lt_bad
#print axioms
  ArkLib.ProximityGap.Frontier.R132DemandFloorHybridMajorants.not_prefixes_and_hybrid_majorants_of_dvd_four_budget_lt_bad_positive
