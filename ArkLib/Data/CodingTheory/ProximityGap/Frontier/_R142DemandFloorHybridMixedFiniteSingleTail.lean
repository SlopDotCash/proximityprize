/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R141DemandFloorHybridConstructorObstructions

/-!
# Mixed finite source certificates with a single-source tail

R140 handles all-KKH26 and all-ladder constructor packages.  This file adds the intermediate
shape expected from practical searches: the finite window `[6,R]` may be covered by separate KKH26
and ladder-certified rung sets, while the tail is certified by one source.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R142DemandFloorHybridMixedFiniteSingleTail

open ArkLib.ProximityGap.Frontier.R109DemandFloorGeneralBudgetBridge
open ArkLib.ProximityGap.Frontier.R115DemandFloorTailReduction
open ArkLib.ProximityGap.Frontier.R137DemandFloorHybridSourceSplit
open ArkLib.ProximityGap.Frontier.R138DemandFloorHybridTailSourceSplit
open ArkLib.ProximityGap.Frontier.R139DemandFloorHybridSourceSplitPackage

/-- Mixed finite source cover plus a KKH26-only tail gives a bundled source-split certificate. -/
def source_split_certificate_of_mixed_finite_kkh26_tail
    (Bad : ℕ → ℕ → ℕ) (R : ℕ) (rs ts : Finset ℕ)
    (hcover : Finset.Icc 6 R ⊆ rs ∪ ts)
    (hkkhFin : HasKKH26CensusDominatorsOn Bad rs)
    (hladderFin : HasLadderMajorantsOn Bad ts)
    (hkkhTail : HasKKH26CensusDominatorsAbove Bad R) :
    SourceSplitHybridCertificate Bad where
  R := R
  kkhRungs := rs
  ladderRungs := ts
  cover := hcover
  kkhFinite := hkkhFin
  ladderFinite := hladderFin
  tail := fun g r hg h6 hrg hR => Or.inl (hkkhTail g r hg h6 hrg hR)

/-- Mixed finite source cover plus a ladder-only tail gives a bundled source-split certificate. -/
def source_split_certificate_of_mixed_finite_ladder_tail
    (Bad : ℕ → ℕ → ℕ) (R : ℕ) (rs ts : Finset ℕ)
    (hcover : Finset.Icc 6 R ⊆ rs ∪ ts)
    (hkkhFin : HasKKH26CensusDominatorsOn Bad rs)
    (hladderFin : HasLadderMajorantsOn Bad ts)
    (hladderTail : HasLadderMajorantsAbove Bad R) :
    SourceSplitHybridCertificate Bad where
  R := R
  kkhRungs := rs
  ladderRungs := ts
  cover := hcover
  kkhFinite := hkkhFin
  ladderFinite := hladderFin
  tail := fun g r hg h6 hrg hR => Or.inr (hladderTail g r hg h6 hrg hR)

/-- Mixed finite source cover plus a KKH26-only tail gives the divisibility-form budget. -/
theorem demand_floor_of_dvd_four_prefixes_and_mixed_finite_kkh26_tail
    (Bad : ℕ → ℕ → ℕ) (R : ℕ) (rs ts : Finset ℕ)
    (hcover : Finset.Icc 6 R ⊆ rs ∪ ts)
    (hkkhFin : HasKKH26CensusDominatorsOn Bad rs)
    (hladderFin : HasLadderMajorantsOn Bad ts)
    (hkkhTail : HasKKH26CensusDominatorsAbove Bad R)
    (hprefix : ∀ g : ℕ, 3 ≤ g → AgreesWithClosedDemandPrefix Bad g)
    (r n : ℕ)
    (hn : 4 ∣ n)
    (hg : 3 ≤ n / 4)
    (hr : 3 ≤ r)
    (hrg : r ≤ n / 4) :
    Bad r n ≤ deepBandBudgetR r n := by
  exact demand_floor_of_dvd_four_prefixes_and_source_split_certificate Bad
    (source_split_certificate_of_mixed_finite_kkh26_tail
      Bad R rs ts hcover hkkhFin hladderFin hkkhTail)
    hprefix r n hn hg hr hrg

/-- Mixed finite source cover plus a KKH26-only tail gives the positive-rung
divisibility-form budget. -/
theorem demand_floor_positive_of_dvd_four_prefixes_and_mixed_finite_kkh26_tail
    (Bad : ℕ → ℕ → ℕ) (R : ℕ) (rs ts : Finset ℕ)
    (hcover : Finset.Icc 6 R ⊆ rs ∪ ts)
    (hkkhFin : HasKKH26CensusDominatorsOn Bad rs)
    (hladderFin : HasLadderMajorantsOn Bad ts)
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
    (source_split_certificate_of_mixed_finite_kkh26_tail
      Bad R rs ts hcover hkkhFin hladderFin hkkhTail)
    hprefix r n hn hg hr0 hr1 hr2 hrg

/-- Mixed finite source cover plus a ladder-only tail gives the divisibility-form budget. -/
theorem demand_floor_of_dvd_four_prefixes_and_mixed_finite_ladder_tail
    (Bad : ℕ → ℕ → ℕ) (R : ℕ) (rs ts : Finset ℕ)
    (hcover : Finset.Icc 6 R ⊆ rs ∪ ts)
    (hkkhFin : HasKKH26CensusDominatorsOn Bad rs)
    (hladderFin : HasLadderMajorantsOn Bad ts)
    (hladderTail : HasLadderMajorantsAbove Bad R)
    (hprefix : ∀ g : ℕ, 3 ≤ g → AgreesWithClosedDemandPrefix Bad g)
    (r n : ℕ)
    (hn : 4 ∣ n)
    (hg : 3 ≤ n / 4)
    (hr : 3 ≤ r)
    (hrg : r ≤ n / 4) :
    Bad r n ≤ deepBandBudgetR r n := by
  exact demand_floor_of_dvd_four_prefixes_and_source_split_certificate Bad
    (source_split_certificate_of_mixed_finite_ladder_tail
      Bad R rs ts hcover hkkhFin hladderFin hladderTail)
    hprefix r n hn hg hr hrg

/-- Mixed finite source cover plus a ladder-only tail gives the positive-rung
divisibility-form budget. -/
theorem demand_floor_positive_of_dvd_four_prefixes_and_mixed_finite_ladder_tail
    (Bad : ℕ → ℕ → ℕ) (R : ℕ) (rs ts : Finset ℕ)
    (hcover : Finset.Icc 6 R ⊆ rs ∪ ts)
    (hkkhFin : HasKKH26CensusDominatorsOn Bad rs)
    (hladderFin : HasLadderMajorantsOn Bad ts)
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
    (source_split_certificate_of_mixed_finite_ladder_tail
      Bad R rs ts hcover hkkhFin hladderFin hladderTail)
    hprefix r n hn hg hr0 hr1 hr2 hrg

/-- A budget overrun refutes mixed finite source cover plus KKH26-only tail. -/
theorem not_mixed_finite_kkh26_tail_and_prefixes_of_dvd_four_budget_lt_bad
    (Bad : ℕ → ℕ → ℕ) (R : ℕ) (rs ts : Finset ℕ)
    (r n : ℕ)
    (hn : 4 ∣ n)
    (hg : 3 ≤ n / 4)
    (hr : 3 ≤ r)
    (hrg : r ≤ n / 4)
    (hgt : deepBandBudgetR r n < Bad r n) :
    ¬ (Finset.Icc 6 R ⊆ rs ∪ ts ∧
      HasKKH26CensusDominatorsOn Bad rs ∧
      HasLadderMajorantsOn Bad ts ∧
      HasKKH26CensusDominatorsAbove Bad R ∧
      ∀ g : ℕ, 3 ≤ g → AgreesWithClosedDemandPrefix Bad g) := by
  rintro ⟨hcover, hkkhFin, hladderFin, hkkhTail, hprefix⟩
  exact (Nat.not_le.mpr hgt)
    (demand_floor_of_dvd_four_prefixes_and_mixed_finite_kkh26_tail
      Bad R rs ts hcover hkkhFin hladderFin hkkhTail hprefix r n hn hg hr hrg)

/-- Positive-rung obstruction for mixed finite source cover plus KKH26-only tail. -/
theorem not_mixed_finite_kkh26_tail_and_prefixes_of_dvd_four_budget_lt_bad_positive
    (Bad : ℕ → ℕ → ℕ) (R : ℕ) (rs ts : Finset ℕ)
    (r n : ℕ)
    (hn : 4 ∣ n)
    (hg : 3 ≤ n / 4)
    (hr0 : r ≠ 0)
    (hr1 : r ≠ 1)
    (hr2 : r ≠ 2)
    (hrg : r ≤ n / 4)
    (hgt : deepBandBudgetR r n < Bad r n) :
    ¬ (Finset.Icc 6 R ⊆ rs ∪ ts ∧
      HasKKH26CensusDominatorsOn Bad rs ∧
      HasLadderMajorantsOn Bad ts ∧
      HasKKH26CensusDominatorsAbove Bad R ∧
      ∀ g : ℕ, 3 ≤ g → AgreesWithClosedDemandPrefix Bad g) := by
  rintro ⟨hcover, hkkhFin, hladderFin, hkkhTail, hprefix⟩
  exact (Nat.not_le.mpr hgt)
    (demand_floor_positive_of_dvd_four_prefixes_and_mixed_finite_kkh26_tail
      Bad R rs ts hcover hkkhFin hladderFin hkkhTail hprefix r n hn hg hr0 hr1 hr2 hrg)

/-- A budget overrun refutes mixed finite source cover plus ladder-only tail. -/
theorem not_mixed_finite_ladder_tail_and_prefixes_of_dvd_four_budget_lt_bad
    (Bad : ℕ → ℕ → ℕ) (R : ℕ) (rs ts : Finset ℕ)
    (r n : ℕ)
    (hn : 4 ∣ n)
    (hg : 3 ≤ n / 4)
    (hr : 3 ≤ r)
    (hrg : r ≤ n / 4)
    (hgt : deepBandBudgetR r n < Bad r n) :
    ¬ (Finset.Icc 6 R ⊆ rs ∪ ts ∧
      HasKKH26CensusDominatorsOn Bad rs ∧
      HasLadderMajorantsOn Bad ts ∧
      HasLadderMajorantsAbove Bad R ∧
      ∀ g : ℕ, 3 ≤ g → AgreesWithClosedDemandPrefix Bad g) := by
  rintro ⟨hcover, hkkhFin, hladderFin, hladderTail, hprefix⟩
  exact (Nat.not_le.mpr hgt)
    (demand_floor_of_dvd_four_prefixes_and_mixed_finite_ladder_tail
      Bad R rs ts hcover hkkhFin hladderFin hladderTail hprefix r n hn hg hr hrg)

/-- Positive-rung obstruction for mixed finite source cover plus ladder-only tail. -/
theorem not_mixed_finite_ladder_tail_and_prefixes_of_dvd_four_budget_lt_bad_positive
    (Bad : ℕ → ℕ → ℕ) (R : ℕ) (rs ts : Finset ℕ)
    (r n : ℕ)
    (hn : 4 ∣ n)
    (hg : 3 ≤ n / 4)
    (hr0 : r ≠ 0)
    (hr1 : r ≠ 1)
    (hr2 : r ≠ 2)
    (hrg : r ≤ n / 4)
    (hgt : deepBandBudgetR r n < Bad r n) :
    ¬ (Finset.Icc 6 R ⊆ rs ∪ ts ∧
      HasKKH26CensusDominatorsOn Bad rs ∧
      HasLadderMajorantsOn Bad ts ∧
      HasLadderMajorantsAbove Bad R ∧
      ∀ g : ℕ, 3 ≤ g → AgreesWithClosedDemandPrefix Bad g) := by
  rintro ⟨hcover, hkkhFin, hladderFin, hladderTail, hprefix⟩
  exact (Nat.not_le.mpr hgt)
    (demand_floor_positive_of_dvd_four_prefixes_and_mixed_finite_ladder_tail
      Bad R rs ts hcover hkkhFin hladderFin hladderTail hprefix r n hn hg hr0 hr1 hr2 hrg)

end ArkLib.ProximityGap.Frontier.R142DemandFloorHybridMixedFiniteSingleTail

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R142DemandFloorHybridMixedFiniteSingleTail.source_split_certificate_of_mixed_finite_kkh26_tail
#print axioms
  ArkLib.ProximityGap.Frontier.R142DemandFloorHybridMixedFiniteSingleTail.source_split_certificate_of_mixed_finite_ladder_tail
#print axioms
  ArkLib.ProximityGap.Frontier.R142DemandFloorHybridMixedFiniteSingleTail.demand_floor_of_dvd_four_prefixes_and_mixed_finite_kkh26_tail
#print axioms
  ArkLib.ProximityGap.Frontier.R142DemandFloorHybridMixedFiniteSingleTail.demand_floor_positive_of_dvd_four_prefixes_and_mixed_finite_kkh26_tail
#print axioms
  ArkLib.ProximityGap.Frontier.R142DemandFloorHybridMixedFiniteSingleTail.demand_floor_of_dvd_four_prefixes_and_mixed_finite_ladder_tail
#print axioms
  ArkLib.ProximityGap.Frontier.R142DemandFloorHybridMixedFiniteSingleTail.demand_floor_positive_of_dvd_four_prefixes_and_mixed_finite_ladder_tail
#print axioms
  ArkLib.ProximityGap.Frontier.R142DemandFloorHybridMixedFiniteSingleTail.not_mixed_finite_kkh26_tail_and_prefixes_of_dvd_four_budget_lt_bad
#print axioms
  ArkLib.ProximityGap.Frontier.R142DemandFloorHybridMixedFiniteSingleTail.not_mixed_finite_kkh26_tail_and_prefixes_of_dvd_four_budget_lt_bad_positive
#print axioms
  ArkLib.ProximityGap.Frontier.R142DemandFloorHybridMixedFiniteSingleTail.not_mixed_finite_ladder_tail_and_prefixes_of_dvd_four_budget_lt_bad
#print axioms
  ArkLib.ProximityGap.Frontier.R142DemandFloorHybridMixedFiniteSingleTail.not_mixed_finite_ladder_tail_and_prefixes_of_dvd_four_budget_lt_bad_positive
