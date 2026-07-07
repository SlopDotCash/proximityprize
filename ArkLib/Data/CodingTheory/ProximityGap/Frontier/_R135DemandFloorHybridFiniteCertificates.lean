/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R134DemandFloorHybridWindows

/-!
# Finite hybrid-majorant certificates

R134 packages finite low-rung work as an interval `[6, R]`.  Exhaustive or semi-exhaustive
producers often emit one certificate per rung, or one finite set of certified rungs.  This file
adds the small adapter layer from singleton/finite certificates to the window interface.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R135DemandFloorHybridFiniteCertificates

open ArkLib.ProximityGap.Frontier.R109DemandFloorGeneralBudgetBridge
open ArkLib.ProximityGap.Frontier.R115DemandFloorTailReduction
open ArkLib.ProximityGap.Frontier.R120DemandFloorNaturalCertificatePackage
open ArkLib.ProximityGap.Frontier.R121DemandFloorTailTheoremInterface
open ArkLib.ProximityGap.Frontier.R132DemandFloorHybridMajorants
open ArkLib.ProximityGap.Frontier.R133DemandFloorHybridCutoff
open ArkLib.ProximityGap.Frontier.R134DemandFloorHybridWindows

/-- A certificate for one deep rung `r0`, uniform in the ambient block length `g`. -/
def HasHybridMajorantRung (Bad : ℕ → ℕ → ℕ) (r0 : ℕ) : Prop :=
  ∀ g : ℕ, 3 ≤ g → 6 ≤ r0 → r0 ≤ g → HasHybridMajorantAt Bad g r0

/-- A certificate for every rung in a finite set. -/
def HasHybridMajorantsOn (Bad : ℕ → ℕ → ℕ) (rs : Finset ℕ) : Prop :=
  ∀ r : ℕ, r ∈ rs → HasHybridMajorantRung Bad r

/-- A window certificate restricts to a singleton rung. -/
theorem hybrid_rung_of_window
    (Bad : ℕ → ℕ → ℕ) (lo hi r0 : ℕ)
    (hwin : HasHybridMajorantsWindow Bad lo hi)
    (hlo : lo ≤ r0) (hhi : r0 ≤ hi) :
    HasHybridMajorantRung Bad r0 := by
  intro g hg hr hrg
  exact hwin g r0 hg hr hrg hlo hhi

/-- A singleton rung certificate is the same data as a finite-set certificate on `{r0}`. -/
theorem hybrid_on_singleton_of_rung
    (Bad : ℕ → ℕ → ℕ) (r0 : ℕ)
    (hrung : HasHybridMajorantRung Bad r0) :
    HasHybridMajorantsOn Bad ({r0} : Finset ℕ) := by
  intro r hr
  have h : r = r0 := by simpa using hr
  simpa [h] using hrung

/-- Finite-set certificates restrict along subset inclusion. -/
theorem hybrid_on_mono
    (Bad : ℕ → ℕ → ℕ) (rs ts : Finset ℕ)
    (hsub : rs ⊆ ts)
    (hts : HasHybridMajorantsOn Bad ts) :
    HasHybridMajorantsOn Bad rs := by
  intro r hr
  exact hts r (hsub hr)

/-- Finite-set certificates glue across finite-set union. -/
theorem hybrid_on_union
    (Bad : ℕ → ℕ → ℕ) (rs ts : Finset ℕ)
    (hrs : HasHybridMajorantsOn Bad rs)
    (hts : HasHybridMajorantsOn Bad ts) :
    HasHybridMajorantsOn Bad (rs ∪ ts) := by
  intro r hr
  rcases Finset.mem_union.mp hr with hr | hr
  · exact hrs r hr
  · exact hts r hr

/-- A finite certificate on the interval finset `Icc lo hi` gives the R134 window certificate. -/
theorem hybrid_window_of_hybrid_on_Icc
    (Bad : ℕ → ℕ → ℕ) (lo hi : ℕ)
    (hon : HasHybridMajorantsOn Bad (Finset.Icc lo hi)) :
    HasHybridMajorantsWindow Bad lo hi := by
  intro g r hg hr hrg hlo hhi
  exact hon r (Finset.mem_Icc.mpr ⟨hlo, hhi⟩) g hg hr hrg

/-- Per-rung certificates for every `r ∈ [lo, hi]` give a window certificate. -/
theorem hybrid_window_of_forall_rung
    (Bad : ℕ → ℕ → ℕ) (lo hi : ℕ)
    (hrungs : ∀ r : ℕ, lo ≤ r → r ≤ hi → HasHybridMajorantRung Bad r) :
    HasHybridMajorantsWindow Bad lo hi := by
  intro g r hg hr hrg hlo hhi
  exact hrungs r hlo hhi g hg hr hrg

/-- Initial finite rung certificates plus a tail theorem give the natural demand certificate
at one `g`. -/
theorem natural_demand_certificate_of_prefix_and_hybrid_finite_tail
    (Bad : ℕ → ℕ → ℕ) (R : ℕ)
    (hon : HasHybridMajorantsOn Bad (Finset.Icc 6 R))
    (htail : HasHybridMajorantsAbove Bad R)
    (g : ℕ) (hg : 3 ≤ g)
    (hprefix : AgreesWithClosedDemandPrefix Bad g) :
    HasNaturalDemandCertificate Bad g :=
  natural_demand_certificate_of_prefix_and_hybrid_window_tail Bad R
    (hybrid_window_of_hybrid_on_Icc Bad 6 R hon) htail g hg hprefix

/-- Initial finite rung certificates plus a tail theorem give the uniform natural demand theorem. -/
theorem natural_demand_theorem_of_prefixes_and_hybrid_finite_tail
    (Bad : ℕ → ℕ → ℕ) (R : ℕ)
    (hon : HasHybridMajorantsOn Bad (Finset.Icc 6 R))
    (htail : HasHybridMajorantsAbove Bad R)
    (hprefix : ∀ g : ℕ, 3 ≤ g → AgreesWithClosedDemandPrefix Bad g) :
    NaturalDemandCertificateTheorem Bad :=
  natural_demand_theorem_of_prefixes_and_hybrid_window_tail Bad R
    (hybrid_window_of_hybrid_on_Icc Bad 6 R hon) htail hprefix

/-- Initial finite rung certificates plus a tail theorem give the divisibility-form demand budget. -/
theorem demand_floor_of_dvd_four_prefixes_and_hybrid_finite_tail
    (Bad : ℕ → ℕ → ℕ) (R : ℕ)
    (hon : HasHybridMajorantsOn Bad (Finset.Icc 6 R))
    (htail : HasHybridMajorantsAbove Bad R)
    (hprefix : ∀ g : ℕ, 3 ≤ g → AgreesWithClosedDemandPrefix Bad g)
    (r n : ℕ)
    (hn : 4 ∣ n)
    (hg : 3 ≤ n / 4)
    (hr : 3 ≤ r)
    (hrg : r ≤ n / 4) :
    Bad r n ≤ deepBandBudgetR r n := by
  exact demand_floor_of_dvd_four_prefixes_and_hybrid_window_tail Bad R
    (hybrid_window_of_hybrid_on_Icc Bad 6 R hon) htail hprefix r n hn hg hr hrg

/-- A budget overrun refutes any finite initial certificate plus tail proof. -/
theorem not_hybrid_finite_tail_and_prefixes_of_dvd_four_budget_lt_bad
    (Bad : ℕ → ℕ → ℕ) (R : ℕ)
    (r n : ℕ)
    (hn : 4 ∣ n)
    (hg : 3 ≤ n / 4)
    (hr : 3 ≤ r)
    (hrg : r ≤ n / 4)
    (hgt : deepBandBudgetR r n < Bad r n) :
    ¬ (HasHybridMajorantsOn Bad (Finset.Icc 6 R) ∧ HasHybridMajorantsAbove Bad R ∧
      ∀ g : ℕ, 3 ≤ g → AgreesWithClosedDemandPrefix Bad g) := by
  rintro ⟨hon, htail, hprefix⟩
  exact (Nat.not_le.mpr hgt)
    (demand_floor_of_dvd_four_prefixes_and_hybrid_finite_tail
      Bad R hon htail hprefix r n hn hg hr hrg)

end ArkLib.ProximityGap.Frontier.R135DemandFloorHybridFiniteCertificates

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R135DemandFloorHybridFiniteCertificates.HasHybridMajorantRung
#print axioms
  ArkLib.ProximityGap.Frontier.R135DemandFloorHybridFiniteCertificates.HasHybridMajorantsOn
#print axioms
  ArkLib.ProximityGap.Frontier.R135DemandFloorHybridFiniteCertificates.hybrid_rung_of_window
#print axioms
  ArkLib.ProximityGap.Frontier.R135DemandFloorHybridFiniteCertificates.hybrid_on_singleton_of_rung
#print axioms
  ArkLib.ProximityGap.Frontier.R135DemandFloorHybridFiniteCertificates.hybrid_on_mono
#print axioms
  ArkLib.ProximityGap.Frontier.R135DemandFloorHybridFiniteCertificates.hybrid_on_union
#print axioms
  ArkLib.ProximityGap.Frontier.R135DemandFloorHybridFiniteCertificates.hybrid_window_of_hybrid_on_Icc
#print axioms
  ArkLib.ProximityGap.Frontier.R135DemandFloorHybridFiniteCertificates.hybrid_window_of_forall_rung
#print axioms
  ArkLib.ProximityGap.Frontier.R135DemandFloorHybridFiniteCertificates.natural_demand_certificate_of_prefix_and_hybrid_finite_tail
#print axioms
  ArkLib.ProximityGap.Frontier.R135DemandFloorHybridFiniteCertificates.natural_demand_theorem_of_prefixes_and_hybrid_finite_tail
#print axioms
  ArkLib.ProximityGap.Frontier.R135DemandFloorHybridFiniteCertificates.demand_floor_of_dvd_four_prefixes_and_hybrid_finite_tail
#print axioms
  ArkLib.ProximityGap.Frontier.R135DemandFloorHybridFiniteCertificates.not_hybrid_finite_tail_and_prefixes_of_dvd_four_budget_lt_bad
