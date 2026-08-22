/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R136DemandFloorHybridBoundedPrefix

/-!
# Source-split hybrid finite certificates

The hybrid target is a disjunction: at each rung, either the KKH26 exact census dominates or a
ladder-list majorant dominates.  Proof-producing searches often certify those two sources
separately on different finite sets of rungs.  This file glues source-split certificates into the
finite and active-prefix hybrid interfaces from R135/R136.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R137DemandFloorHybridSourceSplit

open ArkLib.ProximityGap.Frontier.R109DemandFloorGeneralBudgetBridge
open ArkLib.ProximityGap.Frontier.R115DemandFloorTailReduction
open ArkLib.ProximityGap.Frontier.R120DemandFloorNaturalCertificatePackage
open ArkLib.ProximityGap.Frontier.R121DemandFloorTailTheoremInterface
open ArkLib.ProximityGap.Frontier.R128DemandFloorLadderMajorantPackage
open ArkLib.ProximityGap.Frontier.R129DemandFloorKKH26CensusPackage
open ArkLib.ProximityGap.Frontier.R132DemandFloorHybridMajorants
open ArkLib.ProximityGap.Frontier.R133DemandFloorHybridCutoff
open ArkLib.ProximityGap.Frontier.R135DemandFloorHybridFiniteCertificates
open ArkLib.ProximityGap.Frontier.R136DemandFloorHybridBoundedPrefix

/-- KKH26 census certificates for every rung in a finite set. -/
def HasKKH26CensusDominatorsOn (Bad : ℕ → ℕ → ℕ) (rs : Finset ℕ) : Prop :=
  ∀ r : ℕ, r ∈ rs → ∀ g : ℕ, 3 ≤ g → 6 ≤ r → r ≤ g → KKH26CensusDominatesAt Bad g r

/-- Ladder-list majorant certificates for every rung in a finite set. -/
def HasLadderMajorantsOn (Bad : ℕ → ℕ → ℕ) (rs : Finset ℕ) : Prop :=
  ∀ r : ℕ, r ∈ rs → ∀ g : ℕ, 3 ≤ g → 6 ≤ r → r ≤ g → HasLadderMajorantAt Bad g r

/-- KKH26 finite-set certificates are hybrid finite-set certificates. -/
theorem hybrid_on_of_kkh26_on
    (Bad : ℕ → ℕ → ℕ) (rs : Finset ℕ)
    (hkkh : HasKKH26CensusDominatorsOn Bad rs) :
    HasHybridMajorantsOn Bad rs := by
  intro r hr g hg h6 hrg
  exact Or.inl (hkkh r hr g hg h6 hrg)

/-- Ladder finite-set certificates are hybrid finite-set certificates. -/
theorem hybrid_on_of_ladder_on
    (Bad : ℕ → ℕ → ℕ) (rs : Finset ℕ)
    (hladder : HasLadderMajorantsOn Bad rs) :
    HasHybridMajorantsOn Bad rs := by
  intro r hr g hg h6 hrg
  exact Or.inr (hladder r hr g hg h6 hrg)

/-- Source-split certificates on two finite sets glue into a hybrid certificate on their union. -/
theorem hybrid_on_union_of_kkh26_on_and_ladder_on
    (Bad : ℕ → ℕ → ℕ) (rs ts : Finset ℕ)
    (hkkh : HasKKH26CensusDominatorsOn Bad rs)
    (hladder : HasLadderMajorantsOn Bad ts) :
    HasHybridMajorantsOn Bad (rs ∪ ts) :=
  hybrid_on_union Bad rs ts
    (hybrid_on_of_kkh26_on Bad rs hkkh)
    (hybrid_on_of_ladder_on Bad ts hladder)

/-- A source-split cover of `Icc 6 R` gives active bounded-prefix hybrid certificates. -/
theorem hybrid_active_prefix_of_source_split_cover
    (Bad : ℕ → ℕ → ℕ) (R : ℕ) (rs ts : Finset ℕ)
    (hcover : Finset.Icc 6 R ⊆ rs ∪ ts)
    (hkkh : HasKKH26CensusDominatorsOn Bad rs)
    (hladder : HasLadderMajorantsOn Bad ts) :
    HasHybridMajorantsActivePrefix Bad R := by
  exact hybrid_active_prefix_of_hybrid_on_Icc Bad R
    (hybrid_on_mono Bad (Finset.Icc 6 R) (rs ∪ ts) hcover
      (hybrid_on_union_of_kkh26_on_and_ladder_on Bad rs ts hkkh hladder))

/-- Source-split finite certificates plus a tail theorem give the natural demand certificate
at one `g`. -/
theorem natural_demand_certificate_of_prefix_and_source_split_tail
    (Bad : ℕ → ℕ → ℕ) (R : ℕ) (rs ts : Finset ℕ)
    (hcover : Finset.Icc 6 R ⊆ rs ∪ ts)
    (hkkh : HasKKH26CensusDominatorsOn Bad rs)
    (hladder : HasLadderMajorantsOn Bad ts)
    (htail : HasHybridMajorantsAbove Bad R)
    (g : ℕ) (hg : 3 ≤ g)
    (hprefix : AgreesWithClosedDemandPrefix Bad g) :
    HasNaturalDemandCertificate Bad g :=
  natural_demand_certificate_of_prefix_and_hybrid_active_prefix_tail Bad R
    (hybrid_active_prefix_of_source_split_cover Bad R rs ts hcover hkkh hladder)
    htail g hg hprefix

/-- Source-split finite certificates plus a tail theorem give the uniform natural demand theorem. -/
theorem natural_demand_theorem_of_prefixes_and_source_split_tail
    (Bad : ℕ → ℕ → ℕ) (R : ℕ) (rs ts : Finset ℕ)
    (hcover : Finset.Icc 6 R ⊆ rs ∪ ts)
    (hkkh : HasKKH26CensusDominatorsOn Bad rs)
    (hladder : HasLadderMajorantsOn Bad ts)
    (htail : HasHybridMajorantsAbove Bad R)
    (hprefix : ∀ g : ℕ, 3 ≤ g → AgreesWithClosedDemandPrefix Bad g) :
    NaturalDemandCertificateTheorem Bad :=
  natural_demand_theorem_of_prefixes_and_hybrid_active_prefix_tail Bad R
    (hybrid_active_prefix_of_source_split_cover Bad R rs ts hcover hkkh hladder)
    htail hprefix

/-- Source-split finite certificates plus a tail theorem give the divisibility-form budget. -/
theorem demand_floor_of_dvd_four_prefixes_and_source_split_tail
    (Bad : ℕ → ℕ → ℕ) (R : ℕ) (rs ts : Finset ℕ)
    (hcover : Finset.Icc 6 R ⊆ rs ∪ ts)
    (hkkh : HasKKH26CensusDominatorsOn Bad rs)
    (hladder : HasLadderMajorantsOn Bad ts)
    (htail : HasHybridMajorantsAbove Bad R)
    (hprefix : ∀ g : ℕ, 3 ≤ g → AgreesWithClosedDemandPrefix Bad g)
    (r n : ℕ)
    (hn : 4 ∣ n)
    (hg : 3 ≤ n / 4)
    (hr : 3 ≤ r)
    (hrg : r ≤ n / 4) :
    Bad r n ≤ deepBandBudgetR r n := by
  exact demand_floor_of_dvd_four_prefixes_and_hybrid_active_prefix_tail Bad R
    (hybrid_active_prefix_of_source_split_cover Bad R rs ts hcover hkkh hladder)
    htail hprefix r n hn hg hr hrg

/-- Source-split finite certificates plus a tail theorem give the positive-rung
divisibility-form budget. -/
theorem demand_floor_positive_of_dvd_four_prefixes_and_source_split_tail
    (Bad : ℕ → ℕ → ℕ) (R : ℕ) (rs ts : Finset ℕ)
    (hcover : Finset.Icc 6 R ⊆ rs ∪ ts)
    (hkkh : HasKKH26CensusDominatorsOn Bad rs)
    (hladder : HasLadderMajorantsOn Bad ts)
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
    (hybrid_cutoff_of_active_prefix_and_tail Bad R
      (hybrid_active_prefix_of_source_split_cover Bad R rs ts hcover hkkh hladder) htail)
    hprefix r n hn hg hr0 hr1 hr2 hrg

/-- A budget overrun refutes any source-split finite certificate plus tail proof. -/
theorem not_source_split_tail_and_prefixes_of_dvd_four_budget_lt_bad
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
      HasHybridMajorantsAbove Bad R ∧
      ∀ g : ℕ, 3 ≤ g → AgreesWithClosedDemandPrefix Bad g) := by
  rintro ⟨hcover, hkkh, hladder, htail, hprefix⟩
  exact (Nat.not_le.mpr hgt)
    (demand_floor_of_dvd_four_prefixes_and_source_split_tail
      Bad R rs ts hcover hkkh hladder htail hprefix r n hn hg hr hrg)

/-- Positive-rung obstruction for source-split finite certificates plus a tail theorem. -/
theorem not_source_split_tail_and_prefixes_of_dvd_four_budget_lt_bad_positive
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
      HasHybridMajorantsAbove Bad R ∧
      ∀ g : ℕ, 3 ≤ g → AgreesWithClosedDemandPrefix Bad g) := by
  rintro ⟨hcover, hkkh, hladder, htail, hprefix⟩
  exact (Nat.not_le.mpr hgt)
    (demand_floor_positive_of_dvd_four_prefixes_and_source_split_tail
      Bad R rs ts hcover hkkh hladder htail hprefix r n hn hg hr0 hr1 hr2 hrg)

end ArkLib.ProximityGap.Frontier.R137DemandFloorHybridSourceSplit

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R137DemandFloorHybridSourceSplit.HasKKH26CensusDominatorsOn
#print axioms
  ArkLib.ProximityGap.Frontier.R137DemandFloorHybridSourceSplit.HasLadderMajorantsOn
#print axioms
  ArkLib.ProximityGap.Frontier.R137DemandFloorHybridSourceSplit.hybrid_on_of_kkh26_on
#print axioms
  ArkLib.ProximityGap.Frontier.R137DemandFloorHybridSourceSplit.hybrid_on_of_ladder_on
#print axioms
  ArkLib.ProximityGap.Frontier.R137DemandFloorHybridSourceSplit.hybrid_on_union_of_kkh26_on_and_ladder_on
#print axioms
  ArkLib.ProximityGap.Frontier.R137DemandFloorHybridSourceSplit.hybrid_active_prefix_of_source_split_cover
#print axioms
  ArkLib.ProximityGap.Frontier.R137DemandFloorHybridSourceSplit.natural_demand_certificate_of_prefix_and_source_split_tail
#print axioms
  ArkLib.ProximityGap.Frontier.R137DemandFloorHybridSourceSplit.natural_demand_theorem_of_prefixes_and_source_split_tail
#print axioms
  ArkLib.ProximityGap.Frontier.R137DemandFloorHybridSourceSplit.demand_floor_of_dvd_four_prefixes_and_source_split_tail
#print axioms
  ArkLib.ProximityGap.Frontier.R137DemandFloorHybridSourceSplit.demand_floor_positive_of_dvd_four_prefixes_and_source_split_tail
#print axioms
  ArkLib.ProximityGap.Frontier.R137DemandFloorHybridSourceSplit.not_source_split_tail_and_prefixes_of_dvd_four_budget_lt_bad
#print axioms
  ArkLib.ProximityGap.Frontier.R137DemandFloorHybridSourceSplit.not_source_split_tail_and_prefixes_of_dvd_four_budget_lt_bad_positive
