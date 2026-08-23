/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R135DemandFloorHybridFiniteCertificates

/-!
# Bounded-prefix hybrid certificates

R135 lets finite search output certificates on a fixed interval.  In the demand-floor range the
only active rungs at block coordinate `g` are `r ≤ g`, so a concrete low-rung producer naturally
certifies the bounded prefix `6 ≤ r ≤ min R g`.  This file packages that active-prefix form and
connects it to the R133/R134 cutoff interface.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R136DemandFloorHybridBoundedPrefix

open ArkLib.ProximityGap.Frontier.R109DemandFloorGeneralBudgetBridge
open ArkLib.ProximityGap.Frontier.R115DemandFloorTailReduction
open ArkLib.ProximityGap.Frontier.R120DemandFloorNaturalCertificatePackage
open ArkLib.ProximityGap.Frontier.R121DemandFloorTailTheoremInterface
open ArkLib.ProximityGap.Frontier.R132DemandFloorHybridMajorants
open ArkLib.ProximityGap.Frontier.R133DemandFloorHybridCutoff
open ArkLib.ProximityGap.Frontier.R134DemandFloorHybridWindows
open ArkLib.ProximityGap.Frontier.R135DemandFloorHybridFiniteCertificates

/-- Active bounded-prefix certificates: for each `g`, certify only the rungs in
`[6, min R g]`. -/
def HasHybridMajorantsActivePrefix (Bad : ℕ → ℕ → ℕ) (R : ℕ) : Prop :=
  ∀ g r : ℕ, 3 ≤ g → 6 ≤ r → r ≤ R → r ≤ g → HasHybridMajorantAt Bad g r

/-- A window certificate on `[6,R]` gives the active bounded-prefix form. -/
theorem hybrid_active_prefix_of_initial_window
    (Bad : ℕ → ℕ → ℕ) (R : ℕ)
    (hwin : HasHybridMajorantsWindow Bad 6 R) :
    HasHybridMajorantsActivePrefix Bad R := by
  intro g r hg hr hrR hrg
  exact hwin g r hg hr hrg hr hrR

/-- A finite certificate on `Icc 6 R` gives the active bounded-prefix form. -/
theorem hybrid_active_prefix_of_hybrid_on_Icc
    (Bad : ℕ → ℕ → ℕ) (R : ℕ)
    (hon : HasHybridMajorantsOn Bad (Finset.Icc 6 R)) :
    HasHybridMajorantsActivePrefix Bad R := by
  exact hybrid_active_prefix_of_initial_window Bad R
    (hybrid_window_of_hybrid_on_Icc Bad 6 R hon)

/-- The active-prefix form supplies the finite side of the cutoff package. -/
theorem hybrid_below_of_active_prefix
    (Bad : ℕ → ℕ → ℕ) (R : ℕ)
    (hprefix : HasHybridMajorantsActivePrefix Bad R) :
    HasHybridMajorantsBelow Bad R := by
  intro g r hg hr hrg hrR
  exact hprefix g r hg hr hrR hrg

/-- Active bounded-prefix certificates plus a tail theorem give the R133 cutoff package. -/
theorem hybrid_cutoff_of_active_prefix_and_tail
    (Bad : ℕ → ℕ → ℕ) (R : ℕ)
    (hactive : HasHybridMajorantsActivePrefix Bad R)
    (htail : HasHybridMajorantsAbove Bad R) :
    HasHybridMajorantsCutoff Bad R :=
  ⟨hybrid_below_of_active_prefix Bad R hactive, htail⟩

/-- Active bounded-prefix certificates plus a tail theorem give uniform hybrid majorants. -/
theorem hybrid_majorants_of_active_prefix_and_tail
    (Bad : ℕ → ℕ → ℕ) (R : ℕ)
    (hactive : HasHybridMajorantsActivePrefix Bad R)
    (htail : HasHybridMajorantsAbove Bad R) :
    HasHybridMajorants Bad :=
  hybrid_majorants_of_cutoff Bad R
    (hybrid_cutoff_of_active_prefix_and_tail Bad R hactive htail)

/-- Active bounded-prefix certificates plus a tail theorem give the natural demand certificate
at one `g`. -/
theorem natural_demand_certificate_of_prefix_and_hybrid_active_prefix_tail
    (Bad : ℕ → ℕ → ℕ) (R : ℕ)
    (hactive : HasHybridMajorantsActivePrefix Bad R)
    (htail : HasHybridMajorantsAbove Bad R)
    (g : ℕ) (hg : 3 ≤ g)
    (hprefix : AgreesWithClosedDemandPrefix Bad g) :
    HasNaturalDemandCertificate Bad g :=
  natural_demand_certificate_of_prefix_and_hybrid_cutoff Bad R
    (hybrid_cutoff_of_active_prefix_and_tail Bad R hactive htail) g hg hprefix

/-- Active bounded-prefix certificates plus a tail theorem give the uniform natural demand theorem. -/
theorem natural_demand_theorem_of_prefixes_and_hybrid_active_prefix_tail
    (Bad : ℕ → ℕ → ℕ) (R : ℕ)
    (hactive : HasHybridMajorantsActivePrefix Bad R)
    (htail : HasHybridMajorantsAbove Bad R)
    (hprefix : ∀ g : ℕ, 3 ≤ g → AgreesWithClosedDemandPrefix Bad g) :
    NaturalDemandCertificateTheorem Bad :=
  natural_demand_theorem_of_prefixes_and_hybrid_cutoff Bad R
    (hybrid_cutoff_of_active_prefix_and_tail Bad R hactive htail) hprefix

/-- Active bounded-prefix certificates plus a tail theorem give the divisibility-form budget. -/
theorem demand_floor_of_dvd_four_prefixes_and_hybrid_active_prefix_tail
    (Bad : ℕ → ℕ → ℕ) (R : ℕ)
    (hactive : HasHybridMajorantsActivePrefix Bad R)
    (htail : HasHybridMajorantsAbove Bad R)
    (hprefix : ∀ g : ℕ, 3 ≤ g → AgreesWithClosedDemandPrefix Bad g)
    (r n : ℕ)
    (hn : 4 ∣ n)
    (hg : 3 ≤ n / 4)
    (hr : 3 ≤ r)
    (hrg : r ≤ n / 4) :
    Bad r n ≤ deepBandBudgetR r n := by
  exact demand_floor_of_dvd_four_prefixes_and_hybrid_cutoff Bad R
    (hybrid_cutoff_of_active_prefix_and_tail Bad R hactive htail)
    hprefix r n hn hg hr hrg

/-- Active bounded-prefix certificates plus a tail theorem give the positive-rung
divisibility-form budget. -/
theorem demand_floor_positive_of_dvd_four_prefixes_and_hybrid_active_prefix_tail
    (Bad : ℕ → ℕ → ℕ) (R : ℕ)
    (hactive : HasHybridMajorantsActivePrefix Bad R)
    (htail : HasHybridMajorantsAbove Bad R)
    (hprefix : ∀ g : ℕ, 3 ≤ g → AgreesWithClosedDemandPrefix Bad g)
    (r n : ℕ)
    (hn : 4 ∣ n)
    (hg : 3 ≤ n / 4)
    (hr0 : r ≠ 0)
    (hr1 : r ≠ 1)
    (hr2 : r ≠ 2)
    (hrg : r ≤ n / 4) :
    Bad r n ≤ deepBandBudgetR r n := by
  exact demand_floor_positive_of_dvd_four_prefixes_and_hybrid_cutoff Bad R
    (hybrid_cutoff_of_active_prefix_and_tail Bad R hactive htail)
    hprefix r n hn hg hr0 hr1 hr2 hrg

/-- A budget overrun refutes any active-prefix plus tail proof. -/
theorem not_hybrid_active_prefix_tail_and_prefixes_of_dvd_four_budget_lt_bad
    (Bad : ℕ → ℕ → ℕ) (R : ℕ)
    (r n : ℕ)
    (hn : 4 ∣ n)
    (hg : 3 ≤ n / 4)
    (hr : 3 ≤ r)
    (hrg : r ≤ n / 4)
    (hgt : deepBandBudgetR r n < Bad r n) :
    ¬ (HasHybridMajorantsActivePrefix Bad R ∧ HasHybridMajorantsAbove Bad R ∧
      ∀ g : ℕ, 3 ≤ g → AgreesWithClosedDemandPrefix Bad g) := by
  rintro ⟨hactive, htail, hprefix⟩
  exact (Nat.not_le.mpr hgt)
    (demand_floor_of_dvd_four_prefixes_and_hybrid_active_prefix_tail
      Bad R hactive htail hprefix r n hn hg hr hrg)

/-- Positive-rung version of the active-prefix plus tail obstruction. -/
theorem not_hybrid_active_prefix_tail_and_prefixes_of_dvd_four_budget_lt_bad_positive
    (Bad : ℕ → ℕ → ℕ) (R : ℕ)
    (r n : ℕ)
    (hn : 4 ∣ n)
    (hg : 3 ≤ n / 4)
    (hr0 : r ≠ 0)
    (hr1 : r ≠ 1)
    (hr2 : r ≠ 2)
    (hrg : r ≤ n / 4)
    (hgt : deepBandBudgetR r n < Bad r n) :
    ¬ (HasHybridMajorantsActivePrefix Bad R ∧ HasHybridMajorantsAbove Bad R ∧
      ∀ g : ℕ, 3 ≤ g → AgreesWithClosedDemandPrefix Bad g) := by
  rintro ⟨hactive, htail, hprefix⟩
  exact (Nat.not_le.mpr hgt)
    (demand_floor_positive_of_dvd_four_prefixes_and_hybrid_active_prefix_tail
      Bad R hactive htail hprefix r n hn hg hr0 hr1 hr2 hrg)

end ArkLib.ProximityGap.Frontier.R136DemandFloorHybridBoundedPrefix

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R136DemandFloorHybridBoundedPrefix.HasHybridMajorantsActivePrefix
#print axioms
  ArkLib.ProximityGap.Frontier.R136DemandFloorHybridBoundedPrefix.hybrid_active_prefix_of_initial_window
#print axioms
  ArkLib.ProximityGap.Frontier.R136DemandFloorHybridBoundedPrefix.hybrid_active_prefix_of_hybrid_on_Icc
#print axioms
  ArkLib.ProximityGap.Frontier.R136DemandFloorHybridBoundedPrefix.hybrid_below_of_active_prefix
#print axioms
  ArkLib.ProximityGap.Frontier.R136DemandFloorHybridBoundedPrefix.hybrid_cutoff_of_active_prefix_and_tail
#print axioms
  ArkLib.ProximityGap.Frontier.R136DemandFloorHybridBoundedPrefix.hybrid_majorants_of_active_prefix_and_tail
#print axioms
  ArkLib.ProximityGap.Frontier.R136DemandFloorHybridBoundedPrefix.natural_demand_certificate_of_prefix_and_hybrid_active_prefix_tail
#print axioms
  ArkLib.ProximityGap.Frontier.R136DemandFloorHybridBoundedPrefix.natural_demand_theorem_of_prefixes_and_hybrid_active_prefix_tail
#print axioms
  ArkLib.ProximityGap.Frontier.R136DemandFloorHybridBoundedPrefix.demand_floor_of_dvd_four_prefixes_and_hybrid_active_prefix_tail
#print axioms
  ArkLib.ProximityGap.Frontier.R136DemandFloorHybridBoundedPrefix.demand_floor_positive_of_dvd_four_prefixes_and_hybrid_active_prefix_tail
#print axioms
  ArkLib.ProximityGap.Frontier.R136DemandFloorHybridBoundedPrefix.not_hybrid_active_prefix_tail_and_prefixes_of_dvd_four_budget_lt_bad
#print axioms
  ArkLib.ProximityGap.Frontier.R136DemandFloorHybridBoundedPrefix.not_hybrid_active_prefix_tail_and_prefixes_of_dvd_four_budget_lt_bad_positive
