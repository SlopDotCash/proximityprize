/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R142DemandFloorHybridMixedFiniteSingleTail

/-!
# Mixed finite certificates with monotone tail cutoffs

R142 consumes mixed finite certificates on `[6,R]` and a single-source tail above exactly `R`.
In practice an asymptotic tail certificate may be proved above a smaller cutoff `Rt`; if `Rt ≤ R`,
the same tail certificate applies above `R`.  This file packages that monotonicity at the
constructor/consumer level.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R143DemandFloorHybridMixedFiniteMonotoneTail

open ArkLib.ProximityGap.Frontier.R109DemandFloorGeneralBudgetBridge
open ArkLib.ProximityGap.Frontier.R115DemandFloorTailReduction
open ArkLib.ProximityGap.Frontier.R137DemandFloorHybridSourceSplit
open ArkLib.ProximityGap.Frontier.R138DemandFloorHybridTailSourceSplit
open ArkLib.ProximityGap.Frontier.R139DemandFloorHybridSourceSplitPackage
open ArkLib.ProximityGap.Frontier.R142DemandFloorHybridMixedFiniteSingleTail

/-- Mixed finite source cover plus a KKH26 tail above a smaller cutoff `Rt ≤ R` gives a bundled
source-split certificate at cutoff `R`. -/
def source_split_certificate_of_mixed_finite_kkh26_tail_mono
    (Bad : ℕ → ℕ → ℕ) (R Rt : ℕ) (rs ts : Finset ℕ)
    (hRt : Rt ≤ R)
    (hcover : Finset.Icc 6 R ⊆ rs ∪ ts)
    (hkkhFin : HasKKH26CensusDominatorsOn Bad rs)
    (hladderFin : HasLadderMajorantsOn Bad ts)
    (hkkhTail : HasKKH26CensusDominatorsAbove Bad Rt) :
    SourceSplitHybridCertificate Bad :=
  source_split_certificate_of_mixed_finite_kkh26_tail Bad R rs ts
    hcover hkkhFin hladderFin
    (fun g r hg h6 hrg hR => hkkhTail g r hg h6 hrg (lt_of_le_of_lt hRt hR))

/-- Mixed finite source cover plus a ladder tail above a smaller cutoff `Rt ≤ R` gives a bundled
source-split certificate at cutoff `R`. -/
def source_split_certificate_of_mixed_finite_ladder_tail_mono
    (Bad : ℕ → ℕ → ℕ) (R Rt : ℕ) (rs ts : Finset ℕ)
    (hRt : Rt ≤ R)
    (hcover : Finset.Icc 6 R ⊆ rs ∪ ts)
    (hkkhFin : HasKKH26CensusDominatorsOn Bad rs)
    (hladderFin : HasLadderMajorantsOn Bad ts)
    (hladderTail : HasLadderMajorantsAbove Bad Rt) :
    SourceSplitHybridCertificate Bad :=
  source_split_certificate_of_mixed_finite_ladder_tail Bad R rs ts
    hcover hkkhFin hladderFin
    (fun g r hg h6 hrg hR => hladderTail g r hg h6 hrg (lt_of_le_of_lt hRt hR))

/-- Mixed finite source cover plus a monotone KKH26 tail gives the divisibility-form budget. -/
theorem demand_floor_of_dvd_four_prefixes_and_mixed_finite_kkh26_tail_mono
    (Bad : ℕ → ℕ → ℕ) (R Rt : ℕ) (rs ts : Finset ℕ)
    (hRt : Rt ≤ R)
    (hcover : Finset.Icc 6 R ⊆ rs ∪ ts)
    (hkkhFin : HasKKH26CensusDominatorsOn Bad rs)
    (hladderFin : HasLadderMajorantsOn Bad ts)
    (hkkhTail : HasKKH26CensusDominatorsAbove Bad Rt)
    (hprefix : ∀ g : ℕ, 3 ≤ g → AgreesWithClosedDemandPrefix Bad g)
    (r n : ℕ)
    (hn : 4 ∣ n)
    (hg : 3 ≤ n / 4)
    (hr : 3 ≤ r)
    (hrg : r ≤ n / 4) :
    Bad r n ≤ deepBandBudgetR r n := by
  exact demand_floor_of_dvd_four_prefixes_and_source_split_certificate Bad
    (source_split_certificate_of_mixed_finite_kkh26_tail_mono
      Bad R Rt rs ts hRt hcover hkkhFin hladderFin hkkhTail)
    hprefix r n hn hg hr hrg

/-- Mixed finite source cover plus a monotone KKH26 tail gives the positive-rung
divisibility-form budget. -/
theorem demand_floor_positive_of_dvd_four_prefixes_and_mixed_finite_kkh26_tail_mono
    (Bad : ℕ → ℕ → ℕ) (R Rt : ℕ) (rs ts : Finset ℕ)
    (hRt : Rt ≤ R)
    (hcover : Finset.Icc 6 R ⊆ rs ∪ ts)
    (hkkhFin : HasKKH26CensusDominatorsOn Bad rs)
    (hladderFin : HasLadderMajorantsOn Bad ts)
    (hkkhTail : HasKKH26CensusDominatorsAbove Bad Rt)
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
    (source_split_certificate_of_mixed_finite_kkh26_tail_mono
      Bad R Rt rs ts hRt hcover hkkhFin hladderFin hkkhTail)
    hprefix r n hn hg hr0 hr1 hr2 hrg

/-- Mixed finite source cover plus a monotone ladder tail gives the divisibility-form budget. -/
theorem demand_floor_of_dvd_four_prefixes_and_mixed_finite_ladder_tail_mono
    (Bad : ℕ → ℕ → ℕ) (R Rt : ℕ) (rs ts : Finset ℕ)
    (hRt : Rt ≤ R)
    (hcover : Finset.Icc 6 R ⊆ rs ∪ ts)
    (hkkhFin : HasKKH26CensusDominatorsOn Bad rs)
    (hladderFin : HasLadderMajorantsOn Bad ts)
    (hladderTail : HasLadderMajorantsAbove Bad Rt)
    (hprefix : ∀ g : ℕ, 3 ≤ g → AgreesWithClosedDemandPrefix Bad g)
    (r n : ℕ)
    (hn : 4 ∣ n)
    (hg : 3 ≤ n / 4)
    (hr : 3 ≤ r)
    (hrg : r ≤ n / 4) :
    Bad r n ≤ deepBandBudgetR r n := by
  exact demand_floor_of_dvd_four_prefixes_and_source_split_certificate Bad
    (source_split_certificate_of_mixed_finite_ladder_tail_mono
      Bad R Rt rs ts hRt hcover hkkhFin hladderFin hladderTail)
    hprefix r n hn hg hr hrg

/-- Mixed finite source cover plus a monotone ladder tail gives the positive-rung
divisibility-form budget. -/
theorem demand_floor_positive_of_dvd_four_prefixes_and_mixed_finite_ladder_tail_mono
    (Bad : ℕ → ℕ → ℕ) (R Rt : ℕ) (rs ts : Finset ℕ)
    (hRt : Rt ≤ R)
    (hcover : Finset.Icc 6 R ⊆ rs ∪ ts)
    (hkkhFin : HasKKH26CensusDominatorsOn Bad rs)
    (hladderFin : HasLadderMajorantsOn Bad ts)
    (hladderTail : HasLadderMajorantsAbove Bad Rt)
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
    (source_split_certificate_of_mixed_finite_ladder_tail_mono
      Bad R Rt rs ts hRt hcover hkkhFin hladderFin hladderTail)
    hprefix r n hn hg hr0 hr1 hr2 hrg

/-- A budget overrun refutes mixed finite source cover plus a monotone KKH26 tail. -/
theorem not_mixed_finite_kkh26_tail_mono_and_prefixes_of_dvd_four_budget_lt_bad
    (Bad : ℕ → ℕ → ℕ) (R Rt : ℕ) (rs ts : Finset ℕ)
    (r n : ℕ)
    (hn : 4 ∣ n)
    (hg : 3 ≤ n / 4)
    (hr : 3 ≤ r)
    (hrg : r ≤ n / 4)
    (hgt : deepBandBudgetR r n < Bad r n) :
    ¬ (Rt ≤ R ∧
      Finset.Icc 6 R ⊆ rs ∪ ts ∧
      HasKKH26CensusDominatorsOn Bad rs ∧
      HasLadderMajorantsOn Bad ts ∧
      HasKKH26CensusDominatorsAbove Bad Rt ∧
      ∀ g : ℕ, 3 ≤ g → AgreesWithClosedDemandPrefix Bad g) := by
  rintro ⟨hRt, hcover, hkkhFin, hladderFin, hkkhTail, hprefix⟩
  exact (Nat.not_le.mpr hgt)
    (demand_floor_of_dvd_four_prefixes_and_mixed_finite_kkh26_tail_mono
      Bad R Rt rs ts hRt hcover hkkhFin hladderFin hkkhTail hprefix r n hn hg hr hrg)

/-- Positive-rung obstruction for mixed finite source cover plus a monotone KKH26 tail. -/
theorem not_mixed_finite_kkh26_tail_mono_and_prefixes_of_dvd_four_budget_lt_bad_positive
    (Bad : ℕ → ℕ → ℕ) (R Rt : ℕ) (rs ts : Finset ℕ)
    (r n : ℕ)
    (hn : 4 ∣ n)
    (hg : 3 ≤ n / 4)
    (hr0 : r ≠ 0)
    (hr1 : r ≠ 1)
    (hr2 : r ≠ 2)
    (hrg : r ≤ n / 4)
    (hgt : deepBandBudgetR r n < Bad r n) :
    ¬ (Rt ≤ R ∧
      Finset.Icc 6 R ⊆ rs ∪ ts ∧
      HasKKH26CensusDominatorsOn Bad rs ∧
      HasLadderMajorantsOn Bad ts ∧
      HasKKH26CensusDominatorsAbove Bad Rt ∧
      ∀ g : ℕ, 3 ≤ g → AgreesWithClosedDemandPrefix Bad g) := by
  rintro ⟨hRt, hcover, hkkhFin, hladderFin, hkkhTail, hprefix⟩
  exact (Nat.not_le.mpr hgt)
    (demand_floor_positive_of_dvd_four_prefixes_and_mixed_finite_kkh26_tail_mono
      Bad R Rt rs ts hRt hcover hkkhFin hladderFin hkkhTail hprefix
      r n hn hg hr0 hr1 hr2 hrg)

/-- A budget overrun refutes mixed finite source cover plus a monotone ladder tail. -/
theorem not_mixed_finite_ladder_tail_mono_and_prefixes_of_dvd_four_budget_lt_bad
    (Bad : ℕ → ℕ → ℕ) (R Rt : ℕ) (rs ts : Finset ℕ)
    (r n : ℕ)
    (hn : 4 ∣ n)
    (hg : 3 ≤ n / 4)
    (hr : 3 ≤ r)
    (hrg : r ≤ n / 4)
    (hgt : deepBandBudgetR r n < Bad r n) :
    ¬ (Rt ≤ R ∧
      Finset.Icc 6 R ⊆ rs ∪ ts ∧
      HasKKH26CensusDominatorsOn Bad rs ∧
      HasLadderMajorantsOn Bad ts ∧
      HasLadderMajorantsAbove Bad Rt ∧
      ∀ g : ℕ, 3 ≤ g → AgreesWithClosedDemandPrefix Bad g) := by
  rintro ⟨hRt, hcover, hkkhFin, hladderFin, hladderTail, hprefix⟩
  exact (Nat.not_le.mpr hgt)
    (demand_floor_of_dvd_four_prefixes_and_mixed_finite_ladder_tail_mono
      Bad R Rt rs ts hRt hcover hkkhFin hladderFin hladderTail hprefix r n hn hg hr hrg)

/-- Positive-rung obstruction for mixed finite source cover plus a monotone ladder tail. -/
theorem not_mixed_finite_ladder_tail_mono_and_prefixes_of_dvd_four_budget_lt_bad_positive
    (Bad : ℕ → ℕ → ℕ) (R Rt : ℕ) (rs ts : Finset ℕ)
    (r n : ℕ)
    (hn : 4 ∣ n)
    (hg : 3 ≤ n / 4)
    (hr0 : r ≠ 0)
    (hr1 : r ≠ 1)
    (hr2 : r ≠ 2)
    (hrg : r ≤ n / 4)
    (hgt : deepBandBudgetR r n < Bad r n) :
    ¬ (Rt ≤ R ∧
      Finset.Icc 6 R ⊆ rs ∪ ts ∧
      HasKKH26CensusDominatorsOn Bad rs ∧
      HasLadderMajorantsOn Bad ts ∧
      HasLadderMajorantsAbove Bad Rt ∧
      ∀ g : ℕ, 3 ≤ g → AgreesWithClosedDemandPrefix Bad g) := by
  rintro ⟨hRt, hcover, hkkhFin, hladderFin, hladderTail, hprefix⟩
  exact (Nat.not_le.mpr hgt)
    (demand_floor_positive_of_dvd_four_prefixes_and_mixed_finite_ladder_tail_mono
      Bad R Rt rs ts hRt hcover hkkhFin hladderFin hladderTail hprefix
      r n hn hg hr0 hr1 hr2 hrg)

end ArkLib.ProximityGap.Frontier.R143DemandFloorHybridMixedFiniteMonotoneTail

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R143DemandFloorHybridMixedFiniteMonotoneTail.source_split_certificate_of_mixed_finite_kkh26_tail_mono
#print axioms
  ArkLib.ProximityGap.Frontier.R143DemandFloorHybridMixedFiniteMonotoneTail.source_split_certificate_of_mixed_finite_ladder_tail_mono
#print axioms
  ArkLib.ProximityGap.Frontier.R143DemandFloorHybridMixedFiniteMonotoneTail.demand_floor_of_dvd_four_prefixes_and_mixed_finite_kkh26_tail_mono
#print axioms
  ArkLib.ProximityGap.Frontier.R143DemandFloorHybridMixedFiniteMonotoneTail.demand_floor_positive_of_dvd_four_prefixes_and_mixed_finite_kkh26_tail_mono
#print axioms
  ArkLib.ProximityGap.Frontier.R143DemandFloorHybridMixedFiniteMonotoneTail.demand_floor_of_dvd_four_prefixes_and_mixed_finite_ladder_tail_mono
#print axioms
  ArkLib.ProximityGap.Frontier.R143DemandFloorHybridMixedFiniteMonotoneTail.demand_floor_positive_of_dvd_four_prefixes_and_mixed_finite_ladder_tail_mono
#print axioms
  ArkLib.ProximityGap.Frontier.R143DemandFloorHybridMixedFiniteMonotoneTail.not_mixed_finite_kkh26_tail_mono_and_prefixes_of_dvd_four_budget_lt_bad
#print axioms
  ArkLib.ProximityGap.Frontier.R143DemandFloorHybridMixedFiniteMonotoneTail.not_mixed_finite_kkh26_tail_mono_and_prefixes_of_dvd_four_budget_lt_bad_positive
#print axioms
  ArkLib.ProximityGap.Frontier.R143DemandFloorHybridMixedFiniteMonotoneTail.not_mixed_finite_ladder_tail_mono_and_prefixes_of_dvd_four_budget_lt_bad
#print axioms
  ArkLib.ProximityGap.Frontier.R143DemandFloorHybridMixedFiniteMonotoneTail.not_mixed_finite_ladder_tail_mono_and_prefixes_of_dvd_four_budget_lt_bad_positive
