/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R137DemandFloorHybridSourceSplit

/-!
# Source-split hybrid tail certificates

R137 glues source-split finite prefixes into the hybrid demand interface.  This file does the
same for the tail side: an asymptotic argument may prove the KKH26 census route on some tail, the
ladder-list route on some tail, or a pointwise source split between them.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R138DemandFloorHybridTailSourceSplit

open ArkLib.ProximityGap.Frontier.R109DemandFloorGeneralBudgetBridge
open ArkLib.ProximityGap.Frontier.R115DemandFloorTailReduction
open ArkLib.ProximityGap.Frontier.R120DemandFloorNaturalCertificatePackage
open ArkLib.ProximityGap.Frontier.R121DemandFloorTailTheoremInterface
open ArkLib.ProximityGap.Frontier.R128DemandFloorLadderMajorantPackage
open ArkLib.ProximityGap.Frontier.R129DemandFloorKKH26CensusPackage
open ArkLib.ProximityGap.Frontier.R132DemandFloorHybridMajorants
open ArkLib.ProximityGap.Frontier.R133DemandFloorHybridCutoff
open ArkLib.ProximityGap.Frontier.R136DemandFloorHybridBoundedPrefix
open ArkLib.ProximityGap.Frontier.R137DemandFloorHybridSourceSplit

/-- KKH26 census domination on the tail side `R < r`. -/
def HasKKH26CensusDominatorsAbove (Bad : ℕ → ℕ → ℕ) (R : ℕ) : Prop :=
  ∀ g r : ℕ, 3 ≤ g → 6 ≤ r → r ≤ g → R < r → KKH26CensusDominatesAt Bad g r

/-- Ladder-list majorants on the tail side `R < r`. -/
def HasLadderMajorantsAbove (Bad : ℕ → ℕ → ℕ) (R : ℕ) : Prop :=
  ∀ g r : ℕ, 3 ≤ g → 6 ≤ r → r ≤ g → R < r → HasLadderMajorantAt Bad g r

/-- A pointwise source split on the tail side. -/
def HasSourceSplitMajorantsAbove (Bad : ℕ → ℕ → ℕ) (R : ℕ) : Prop :=
  ∀ g r : ℕ, 3 ≤ g → 6 ≤ r → r ≤ g → R < r →
    KKH26CensusDominatesAt Bad g r ∨ HasLadderMajorantAt Bad g r

/-- KKH26-only tail certificates are hybrid tail certificates. -/
theorem hybrid_above_of_kkh26_above
    (Bad : ℕ → ℕ → ℕ) (R : ℕ)
    (hkkh : HasKKH26CensusDominatorsAbove Bad R) :
    HasHybridMajorantsAbove Bad R := by
  intro g r hg h6 hrg hR
  exact Or.inl (hkkh g r hg h6 hrg hR)

/-- Ladder-only tail certificates are hybrid tail certificates. -/
theorem hybrid_above_of_ladder_above
    (Bad : ℕ → ℕ → ℕ) (R : ℕ)
    (hladder : HasLadderMajorantsAbove Bad R) :
    HasHybridMajorantsAbove Bad R := by
  intro g r hg h6 hrg hR
  exact Or.inr (hladder g r hg h6 hrg hR)

/-- Pointwise source-split tail certificates are hybrid tail certificates. -/
theorem hybrid_above_of_source_split_above
    (Bad : ℕ → ℕ → ℕ) (R : ℕ)
    (hsplit : HasSourceSplitMajorantsAbove Bad R) :
    HasHybridMajorantsAbove Bad R := by
  intro g r hg h6 hrg hR
  exact hsplit g r hg h6 hrg hR

/-- KKH26 tail certificates are monotone in the cutoff: proving them above `Rk` also proves
hybrid majorants above any larger cutoff `R`. -/
theorem hybrid_above_of_kkh26_above_mono
    (Bad : ℕ → ℕ → ℕ) (R Rk : ℕ)
    (hk : Rk ≤ R)
    (hkkh : HasKKH26CensusDominatorsAbove Bad Rk) :
    HasHybridMajorantsAbove Bad R := by
  intro g r hg h6 hrg hR
  exact Or.inl (hkkh g r hg h6 hrg (lt_of_le_of_lt hk hR))

/-- Ladder tail certificates are monotone in the cutoff: proving them above `Rl` also proves
hybrid majorants above any larger cutoff `R`. -/
theorem hybrid_above_of_ladder_above_mono
    (Bad : ℕ → ℕ → ℕ) (R Rl : ℕ)
    (hl : Rl ≤ R)
    (hladder : HasLadderMajorantsAbove Bad Rl) :
    HasHybridMajorantsAbove Bad R := by
  intro g r hg h6 hrg hR
  exact Or.inr (hladder g r hg h6 hrg (lt_of_le_of_lt hl hR))

/-- Source-split finite prefixes plus a source-split tail give the natural demand certificate
at one `g`. -/
theorem natural_demand_certificate_of_prefix_and_source_split_finite_source_split_tail
    (Bad : ℕ → ℕ → ℕ) (R : ℕ) (rs ts : Finset ℕ)
    (hcover : Finset.Icc 6 R ⊆ rs ∪ ts)
    (hkkhFin : HasKKH26CensusDominatorsOn Bad rs)
    (hladderFin : HasLadderMajorantsOn Bad ts)
    (htail : HasSourceSplitMajorantsAbove Bad R)
    (g : ℕ) (hg : 3 ≤ g)
    (hprefix : AgreesWithClosedDemandPrefix Bad g) :
    HasNaturalDemandCertificate Bad g :=
  natural_demand_certificate_of_prefix_and_source_split_tail Bad R rs ts
    hcover hkkhFin hladderFin (hybrid_above_of_source_split_above Bad R htail)
    g hg hprefix

/-- Source-split finite prefixes plus a source-split tail give the uniform natural demand theorem. -/
theorem natural_demand_theorem_of_prefixes_and_source_split_finite_source_split_tail
    (Bad : ℕ → ℕ → ℕ) (R : ℕ) (rs ts : Finset ℕ)
    (hcover : Finset.Icc 6 R ⊆ rs ∪ ts)
    (hkkhFin : HasKKH26CensusDominatorsOn Bad rs)
    (hladderFin : HasLadderMajorantsOn Bad ts)
    (htail : HasSourceSplitMajorantsAbove Bad R)
    (hprefix : ∀ g : ℕ, 3 ≤ g → AgreesWithClosedDemandPrefix Bad g) :
    NaturalDemandCertificateTheorem Bad :=
  natural_demand_theorem_of_prefixes_and_source_split_tail Bad R rs ts
    hcover hkkhFin hladderFin (hybrid_above_of_source_split_above Bad R htail)
    hprefix

/-- Source-split finite prefixes plus a source-split tail give the divisibility-form budget. -/
theorem demand_floor_of_dvd_four_prefixes_and_source_split_finite_source_split_tail
    (Bad : ℕ → ℕ → ℕ) (R : ℕ) (rs ts : Finset ℕ)
    (hcover : Finset.Icc 6 R ⊆ rs ∪ ts)
    (hkkhFin : HasKKH26CensusDominatorsOn Bad rs)
    (hladderFin : HasLadderMajorantsOn Bad ts)
    (htail : HasSourceSplitMajorantsAbove Bad R)
    (hprefix : ∀ g : ℕ, 3 ≤ g → AgreesWithClosedDemandPrefix Bad g)
    (r n : ℕ)
    (hn : 4 ∣ n)
    (hg : 3 ≤ n / 4)
    (hr : 3 ≤ r)
    (hrg : r ≤ n / 4) :
    Bad r n ≤ deepBandBudgetR r n := by
  exact demand_floor_of_dvd_four_prefixes_and_source_split_tail Bad R rs ts
    hcover hkkhFin hladderFin (hybrid_above_of_source_split_above Bad R htail)
    hprefix r n hn hg hr hrg

/-- A budget overrun refutes any source-split finite prefix plus source-split tail proof. -/
theorem not_source_split_finite_source_split_tail_and_prefixes_of_dvd_four_budget_lt_bad
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
      HasSourceSplitMajorantsAbove Bad R ∧
      ∀ g : ℕ, 3 ≤ g → AgreesWithClosedDemandPrefix Bad g) := by
  rintro ⟨hcover, hkkhFin, hladderFin, htail, hprefix⟩
  exact (Nat.not_le.mpr hgt)
    (demand_floor_of_dvd_four_prefixes_and_source_split_finite_source_split_tail
      Bad R rs ts hcover hkkhFin hladderFin htail hprefix r n hn hg hr hrg)

end ArkLib.ProximityGap.Frontier.R138DemandFloorHybridTailSourceSplit

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R138DemandFloorHybridTailSourceSplit.HasKKH26CensusDominatorsAbove
#print axioms
  ArkLib.ProximityGap.Frontier.R138DemandFloorHybridTailSourceSplit.HasLadderMajorantsAbove
#print axioms
  ArkLib.ProximityGap.Frontier.R138DemandFloorHybridTailSourceSplit.HasSourceSplitMajorantsAbove
#print axioms
  ArkLib.ProximityGap.Frontier.R138DemandFloorHybridTailSourceSplit.hybrid_above_of_kkh26_above
#print axioms
  ArkLib.ProximityGap.Frontier.R138DemandFloorHybridTailSourceSplit.hybrid_above_of_ladder_above
#print axioms
  ArkLib.ProximityGap.Frontier.R138DemandFloorHybridTailSourceSplit.hybrid_above_of_source_split_above
#print axioms
  ArkLib.ProximityGap.Frontier.R138DemandFloorHybridTailSourceSplit.hybrid_above_of_kkh26_above_mono
#print axioms
  ArkLib.ProximityGap.Frontier.R138DemandFloorHybridTailSourceSplit.hybrid_above_of_ladder_above_mono
#print axioms
  ArkLib.ProximityGap.Frontier.R138DemandFloorHybridTailSourceSplit.natural_demand_certificate_of_prefix_and_source_split_finite_source_split_tail
#print axioms
  ArkLib.ProximityGap.Frontier.R138DemandFloorHybridTailSourceSplit.natural_demand_theorem_of_prefixes_and_source_split_finite_source_split_tail
#print axioms
  ArkLib.ProximityGap.Frontier.R138DemandFloorHybridTailSourceSplit.demand_floor_of_dvd_four_prefixes_and_source_split_finite_source_split_tail
#print axioms
  ArkLib.ProximityGap.Frontier.R138DemandFloorHybridTailSourceSplit.not_source_split_finite_source_split_tail_and_prefixes_of_dvd_four_budget_lt_bad
