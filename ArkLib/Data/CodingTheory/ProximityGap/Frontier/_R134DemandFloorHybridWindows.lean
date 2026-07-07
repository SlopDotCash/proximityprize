/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R133DemandFloorHybridCutoff

/-!
# Windowed hybrid majorants

R133 splits the hybrid-majorant target into a finite side and a tail side.  This file adds a
windowed finite-side interface: proof-producing searches can certify intervals of rungs, adjacent
windows can be glued, and an initial `[6, R]` window supplies the finite side of the cutoff package.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R134DemandFloorHybridWindows

open ArkLib.ProximityGap.Frontier.R109DemandFloorGeneralBudgetBridge
open ArkLib.ProximityGap.Frontier.R115DemandFloorTailReduction
open ArkLib.ProximityGap.Frontier.R120DemandFloorNaturalCertificatePackage
open ArkLib.ProximityGap.Frontier.R121DemandFloorTailTheoremInterface
open ArkLib.ProximityGap.Frontier.R132DemandFloorHybridMajorants
open ArkLib.ProximityGap.Frontier.R133DemandFloorHybridCutoff

/-- Hybrid majorants on a closed rung window `lo ≤ r ≤ hi`. -/
def HasHybridMajorantsWindow (Bad : ℕ → ℕ → ℕ) (lo hi : ℕ) : Prop :=
  ∀ g r : ℕ, 3 ≤ g → 6 ≤ r → r ≤ g → lo ≤ r → r ≤ hi →
    HasHybridMajorantAt Bad g r

/-- A uniform hybrid-majorant proof restricts to any finite window. -/
theorem hybrid_window_of_hybrid_majorants
    (Bad : ℕ → ℕ → ℕ) (lo hi : ℕ)
    (hhyb : HasHybridMajorants Bad) :
    HasHybridMajorantsWindow Bad lo hi := by
  intro g r hg hr hrg _hlo _hhi
  exact hhyb g r hg hr hrg

/-- Adjacent certified windows glue into one larger window. -/
theorem hybrid_window_union_adjacent
    (Bad : ℕ → ℕ → ℕ) (lo mid hi : ℕ)
    (hleft : HasHybridMajorantsWindow Bad lo mid)
    (hright : HasHybridMajorantsWindow Bad (mid + 1) hi) :
    HasHybridMajorantsWindow Bad lo hi := by
  intro g r hg hr hrg hlo hhi
  by_cases hle : r ≤ mid
  · exact hleft g r hg hr hrg hlo hle
  · have hge : mid + 1 ≤ r := by omega
    exact hright g r hg hr hrg hge hhi

/-- The initial `[6, R]` window is exactly the finite side required by R133. -/
theorem hybrid_below_of_initial_window
    (Bad : ℕ → ℕ → ℕ) (R : ℕ)
    (hwin : HasHybridMajorantsWindow Bad 6 R) :
    HasHybridMajorantsBelow Bad R := by
  intro g r hg hr hrg hrR
  exact hwin g r hg hr hrg hr hrR

/-- An initial window plus a tail theorem gives the R133 cutoff package. -/
theorem hybrid_cutoff_of_initial_window_and_tail
    (Bad : ℕ → ℕ → ℕ) (R : ℕ)
    (hwin : HasHybridMajorantsWindow Bad 6 R)
    (htail : HasHybridMajorantsAbove Bad R) :
    HasHybridMajorantsCutoff Bad R :=
  ⟨hybrid_below_of_initial_window Bad R hwin, htail⟩

/-- Initial-window plus tail packages imply the uniform hybrid-majorant target. -/
theorem hybrid_majorants_of_initial_window_and_tail
    (Bad : ℕ → ℕ → ℕ) (R : ℕ)
    (hwin : HasHybridMajorantsWindow Bad 6 R)
    (htail : HasHybridMajorantsAbove Bad R) :
    HasHybridMajorants Bad :=
  hybrid_majorants_of_cutoff Bad R
    (hybrid_cutoff_of_initial_window_and_tail Bad R hwin htail)

/-- Initial-window plus tail packages give the natural demand certificate at one `g`. -/
theorem natural_demand_certificate_of_prefix_and_hybrid_window_tail
    (Bad : ℕ → ℕ → ℕ) (R : ℕ)
    (hwin : HasHybridMajorantsWindow Bad 6 R)
    (htail : HasHybridMajorantsAbove Bad R)
    (g : ℕ) (hg : 3 ≤ g)
    (hprefix : AgreesWithClosedDemandPrefix Bad g) :
    HasNaturalDemandCertificate Bad g :=
  natural_demand_certificate_of_prefix_and_hybrid_cutoff Bad R
    (hybrid_cutoff_of_initial_window_and_tail Bad R hwin htail) g hg hprefix

/-- Initial-window plus tail packages give the uniform natural demand theorem. -/
theorem natural_demand_theorem_of_prefixes_and_hybrid_window_tail
    (Bad : ℕ → ℕ → ℕ) (R : ℕ)
    (hwin : HasHybridMajorantsWindow Bad 6 R)
    (htail : HasHybridMajorantsAbove Bad R)
    (hprefix : ∀ g : ℕ, 3 ≤ g → AgreesWithClosedDemandPrefix Bad g) :
    NaturalDemandCertificateTheorem Bad :=
  natural_demand_theorem_of_prefixes_and_hybrid_cutoff Bad R
    (hybrid_cutoff_of_initial_window_and_tail Bad R hwin htail) hprefix

/-- Initial-window plus tail packages give the divisibility-form demand budget. -/
theorem demand_floor_of_dvd_four_prefixes_and_hybrid_window_tail
    (Bad : ℕ → ℕ → ℕ) (R : ℕ)
    (hwin : HasHybridMajorantsWindow Bad 6 R)
    (htail : HasHybridMajorantsAbove Bad R)
    (hprefix : ∀ g : ℕ, 3 ≤ g → AgreesWithClosedDemandPrefix Bad g)
    (r n : ℕ)
    (hn : 4 ∣ n)
    (hg : 3 ≤ n / 4)
    (hr : 3 ≤ r)
    (hrg : r ≤ n / 4) :
    Bad r n ≤ deepBandBudgetR r n := by
  exact demand_floor_of_dvd_four_prefixes_and_hybrid_cutoff Bad R
    (hybrid_cutoff_of_initial_window_and_tail Bad R hwin htail)
    hprefix r n hn hg hr hrg

/-- A single divisible-by-four budget overrun refutes any initial-window plus tail proof. -/
theorem not_hybrid_window_tail_and_prefixes_of_dvd_four_budget_lt_bad
    (Bad : ℕ → ℕ → ℕ) (R : ℕ)
    (r n : ℕ)
    (hn : 4 ∣ n)
    (hg : 3 ≤ n / 4)
    (hr : 3 ≤ r)
    (hrg : r ≤ n / 4)
    (hgt : deepBandBudgetR r n < Bad r n) :
    ¬ (HasHybridMajorantsWindow Bad 6 R ∧ HasHybridMajorantsAbove Bad R ∧
      ∀ g : ℕ, 3 ≤ g → AgreesWithClosedDemandPrefix Bad g) := by
  rintro ⟨hwin, htail, hprefix⟩
  exact (Nat.not_le.mpr hgt)
    (demand_floor_of_dvd_four_prefixes_and_hybrid_window_tail
      Bad R hwin htail hprefix r n hn hg hr hrg)

end ArkLib.ProximityGap.Frontier.R134DemandFloorHybridWindows

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R134DemandFloorHybridWindows.HasHybridMajorantsWindow
#print axioms
  ArkLib.ProximityGap.Frontier.R134DemandFloorHybridWindows.hybrid_window_of_hybrid_majorants
#print axioms
  ArkLib.ProximityGap.Frontier.R134DemandFloorHybridWindows.hybrid_window_union_adjacent
#print axioms
  ArkLib.ProximityGap.Frontier.R134DemandFloorHybridWindows.hybrid_below_of_initial_window
#print axioms
  ArkLib.ProximityGap.Frontier.R134DemandFloorHybridWindows.hybrid_cutoff_of_initial_window_and_tail
#print axioms
  ArkLib.ProximityGap.Frontier.R134DemandFloorHybridWindows.hybrid_majorants_of_initial_window_and_tail
#print axioms
  ArkLib.ProximityGap.Frontier.R134DemandFloorHybridWindows.natural_demand_certificate_of_prefix_and_hybrid_window_tail
#print axioms
  ArkLib.ProximityGap.Frontier.R134DemandFloorHybridWindows.natural_demand_theorem_of_prefixes_and_hybrid_window_tail
#print axioms
  ArkLib.ProximityGap.Frontier.R134DemandFloorHybridWindows.demand_floor_of_dvd_four_prefixes_and_hybrid_window_tail
#print axioms
  ArkLib.ProximityGap.Frontier.R134DemandFloorHybridWindows.not_hybrid_window_tail_and_prefixes_of_dvd_four_budget_lt_bad
