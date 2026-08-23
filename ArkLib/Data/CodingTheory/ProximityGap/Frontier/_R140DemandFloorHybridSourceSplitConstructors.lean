/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R139DemandFloorHybridSourceSplitPackage

/-!
# Constructors for packaged source-split hybrid certificates

R139 defines the bundled certificate object.  This file adds convenience constructors for the
common producer shapes: all finite rungs certified by KKH26, all finite rungs certified by the
ladder route, and tails certified by a single source.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R140DemandFloorHybridSourceSplitConstructors

open ArkLib.ProximityGap.Frontier.R109DemandFloorGeneralBudgetBridge
open ArkLib.ProximityGap.Frontier.R115DemandFloorTailReduction
open ArkLib.ProximityGap.Frontier.R137DemandFloorHybridSourceSplit
open ArkLib.ProximityGap.Frontier.R138DemandFloorHybridTailSourceSplit
open ArkLib.ProximityGap.Frontier.R139DemandFloorHybridSourceSplitPackage

/-- Empty finite sets carry vacuous KKH26 finite certificates. -/
theorem kkh26_on_empty (Bad : ℕ → ℕ → ℕ) :
    HasKKH26CensusDominatorsOn Bad ∅ := by
  intro r hr
  simp at hr

/-- Empty finite sets carry vacuous ladder finite certificates. -/
theorem ladder_on_empty (Bad : ℕ → ℕ → ℕ) :
    HasLadderMajorantsOn Bad ∅ := by
  intro r hr
  simp at hr

/-- KKH26-only finite prefix plus source-split tail gives a bundled certificate. -/
def source_split_certificate_of_kkh26_finite
    (Bad : ℕ → ℕ → ℕ) (R : ℕ)
    (hkkhFin : HasKKH26CensusDominatorsOn Bad (Finset.Icc 6 R))
    (htail : HasSourceSplitMajorantsAbove Bad R) :
    SourceSplitHybridCertificate Bad where
  R := R
  kkhRungs := Finset.Icc 6 R
  ladderRungs := ∅
  cover := by
    intro r hr
    exact Finset.mem_union_left _ hr
  kkhFinite := hkkhFin
  ladderFinite := ladder_on_empty Bad
  tail := htail

/-- Ladder-only finite prefix plus source-split tail gives a bundled certificate. -/
def source_split_certificate_of_ladder_finite
    (Bad : ℕ → ℕ → ℕ) (R : ℕ)
    (hladderFin : HasLadderMajorantsOn Bad (Finset.Icc 6 R))
    (htail : HasSourceSplitMajorantsAbove Bad R) :
    SourceSplitHybridCertificate Bad where
  R := R
  kkhRungs := ∅
  ladderRungs := Finset.Icc 6 R
  cover := by
    intro r hr
    exact Finset.mem_union_right _ hr
  kkhFinite := kkh26_on_empty Bad
  ladderFinite := hladderFin
  tail := htail

/-- KKH26-only finite prefix and KKH26-only tail gives a bundled certificate. -/
def source_split_certificate_of_kkh26_finite_kkh26_tail
    (Bad : ℕ → ℕ → ℕ) (R : ℕ)
    (hkkhFin : HasKKH26CensusDominatorsOn Bad (Finset.Icc 6 R))
    (hkkhTail : HasKKH26CensusDominatorsAbove Bad R) :
    SourceSplitHybridCertificate Bad :=
  source_split_certificate_of_kkh26_finite Bad R hkkhFin
    (fun g r hg h6 hrg hR => Or.inl (hkkhTail g r hg h6 hrg hR))

/-- Ladder-only finite prefix and ladder-only tail gives a bundled certificate. -/
def source_split_certificate_of_ladder_finite_ladder_tail
    (Bad : ℕ → ℕ → ℕ) (R : ℕ)
    (hladderFin : HasLadderMajorantsOn Bad (Finset.Icc 6 R))
    (hladderTail : HasLadderMajorantsAbove Bad R) :
    SourceSplitHybridCertificate Bad :=
  source_split_certificate_of_ladder_finite Bad R hladderFin
    (fun g r hg h6 hrg hR => Or.inr (hladderTail g r hg h6 hrg hR))

/-- KKH26-only finite prefix and KKH26-only tail give the divisibility-form demand budget. -/
theorem demand_floor_of_dvd_four_prefixes_and_kkh26_finite_kkh26_tail
    (Bad : ℕ → ℕ → ℕ) (R : ℕ)
    (hkkhFin : HasKKH26CensusDominatorsOn Bad (Finset.Icc 6 R))
    (hkkhTail : HasKKH26CensusDominatorsAbove Bad R)
    (hprefix : ∀ g : ℕ, 3 ≤ g → AgreesWithClosedDemandPrefix Bad g)
    (r n : ℕ)
    (hn : 4 ∣ n)
    (hg : 3 ≤ n / 4)
    (hr : 3 ≤ r)
    (hrg : r ≤ n / 4) :
    Bad r n ≤ deepBandBudgetR r n := by
  exact demand_floor_of_dvd_four_prefixes_and_source_split_certificate Bad
    (source_split_certificate_of_kkh26_finite_kkh26_tail Bad R hkkhFin hkkhTail)
    hprefix r n hn hg hr hrg

/-- KKH26-only finite prefix and KKH26-only tail give the positive-rung
divisibility-form demand budget. -/
theorem demand_floor_positive_of_dvd_four_prefixes_and_kkh26_finite_kkh26_tail
    (Bad : ℕ → ℕ → ℕ) (R : ℕ)
    (hkkhFin : HasKKH26CensusDominatorsOn Bad (Finset.Icc 6 R))
    (hkkhTail : HasKKH26CensusDominatorsAbove Bad R)
    (hprefix : ∀ g : ℕ, 3 ≤ g → AgreesWithClosedDemandPrefix Bad g)
    (r n : ℕ)
    (hn : 4 ∣ n)
    (hg : 3 ≤ n / 4)
    (hr0 : r ≠ 0)
    (hr1 : r ≠ 1)
    (hr2 : r ≠ 2)
    (hrg : r ≤ n / 4) :
    Bad r n ≤ deepBandBudgetR r n := by
  exact demand_floor_positive_of_dvd_four_prefixes_and_source_split_certificate Bad
    (source_split_certificate_of_kkh26_finite_kkh26_tail Bad R hkkhFin hkkhTail)
    hprefix r n hn hg hr0 hr1 hr2 hrg

/-- Ladder-only finite prefix and ladder-only tail give the divisibility-form demand budget. -/
theorem demand_floor_of_dvd_four_prefixes_and_ladder_finite_ladder_tail
    (Bad : ℕ → ℕ → ℕ) (R : ℕ)
    (hladderFin : HasLadderMajorantsOn Bad (Finset.Icc 6 R))
    (hladderTail : HasLadderMajorantsAbove Bad R)
    (hprefix : ∀ g : ℕ, 3 ≤ g → AgreesWithClosedDemandPrefix Bad g)
    (r n : ℕ)
    (hn : 4 ∣ n)
    (hg : 3 ≤ n / 4)
    (hr : 3 ≤ r)
    (hrg : r ≤ n / 4) :
    Bad r n ≤ deepBandBudgetR r n := by
  exact demand_floor_of_dvd_four_prefixes_and_source_split_certificate Bad
    (source_split_certificate_of_ladder_finite_ladder_tail Bad R hladderFin hladderTail)
    hprefix r n hn hg hr hrg

/-- Ladder-only finite prefix and ladder-only tail give the positive-rung divisibility-form
demand budget. -/
theorem demand_floor_positive_of_dvd_four_prefixes_and_ladder_finite_ladder_tail
    (Bad : ℕ → ℕ → ℕ) (R : ℕ)
    (hladderFin : HasLadderMajorantsOn Bad (Finset.Icc 6 R))
    (hladderTail : HasLadderMajorantsAbove Bad R)
    (hprefix : ∀ g : ℕ, 3 ≤ g → AgreesWithClosedDemandPrefix Bad g)
    (r n : ℕ)
    (hn : 4 ∣ n)
    (hg : 3 ≤ n / 4)
    (hr0 : r ≠ 0)
    (hr1 : r ≠ 1)
    (hr2 : r ≠ 2)
    (hrg : r ≤ n / 4) :
    Bad r n ≤ deepBandBudgetR r n := by
  exact demand_floor_positive_of_dvd_four_prefixes_and_source_split_certificate Bad
    (source_split_certificate_of_ladder_finite_ladder_tail Bad R hladderFin hladderTail)
    hprefix r n hn hg hr0 hr1 hr2 hrg

end ArkLib.ProximityGap.Frontier.R140DemandFloorHybridSourceSplitConstructors

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R140DemandFloorHybridSourceSplitConstructors.kkh26_on_empty
#print axioms
  ArkLib.ProximityGap.Frontier.R140DemandFloorHybridSourceSplitConstructors.ladder_on_empty
#print axioms
  ArkLib.ProximityGap.Frontier.R140DemandFloorHybridSourceSplitConstructors.source_split_certificate_of_kkh26_finite
#print axioms
  ArkLib.ProximityGap.Frontier.R140DemandFloorHybridSourceSplitConstructors.source_split_certificate_of_ladder_finite
#print axioms
  ArkLib.ProximityGap.Frontier.R140DemandFloorHybridSourceSplitConstructors.source_split_certificate_of_kkh26_finite_kkh26_tail
#print axioms
  ArkLib.ProximityGap.Frontier.R140DemandFloorHybridSourceSplitConstructors.source_split_certificate_of_ladder_finite_ladder_tail
#print axioms
  ArkLib.ProximityGap.Frontier.R140DemandFloorHybridSourceSplitConstructors.demand_floor_of_dvd_four_prefixes_and_kkh26_finite_kkh26_tail
#print axioms
  ArkLib.ProximityGap.Frontier.R140DemandFloorHybridSourceSplitConstructors.demand_floor_positive_of_dvd_four_prefixes_and_kkh26_finite_kkh26_tail
#print axioms
  ArkLib.ProximityGap.Frontier.R140DemandFloorHybridSourceSplitConstructors.demand_floor_of_dvd_four_prefixes_and_ladder_finite_ladder_tail
#print axioms
  ArkLib.ProximityGap.Frontier.R140DemandFloorHybridSourceSplitConstructors.demand_floor_positive_of_dvd_four_prefixes_and_ladder_finite_ladder_tail
