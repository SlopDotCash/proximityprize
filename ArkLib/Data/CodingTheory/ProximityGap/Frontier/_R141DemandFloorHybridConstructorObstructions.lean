/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R140DemandFloorHybridSourceSplitConstructors

/-!
# Obstructions for packaged source-specific constructor routes

R140 gives direct positive consumers for the all-KKH26 and all-ladder constructor packages.  This
file records their matching budget-overrun obstructions, so failed demand bounds immediately rule
out those source-specific certificate shapes.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R141DemandFloorHybridConstructorObstructions

open ArkLib.ProximityGap.Frontier.R109DemandFloorGeneralBudgetBridge
open ArkLib.ProximityGap.Frontier.R115DemandFloorTailReduction
open ArkLib.ProximityGap.Frontier.R137DemandFloorHybridSourceSplit
open ArkLib.ProximityGap.Frontier.R138DemandFloorHybridTailSourceSplit
open ArkLib.ProximityGap.Frontier.R140DemandFloorHybridSourceSplitConstructors

/-- A single budget overrun refutes the all-KKH26 finite-prefix plus all-KKH26 tail route. -/
theorem not_kkh26_finite_kkh26_tail_and_prefixes_of_dvd_four_budget_lt_bad
    (Bad : ℕ → ℕ → ℕ) (R : ℕ)
    (r n : ℕ)
    (hn : 4 ∣ n)
    (hg : 3 ≤ n / 4)
    (hr : 3 ≤ r)
    (hrg : r ≤ n / 4)
    (hgt : deepBandBudgetR r n < Bad r n) :
    ¬ (HasKKH26CensusDominatorsOn Bad (Finset.Icc 6 R) ∧
      HasKKH26CensusDominatorsAbove Bad R ∧
      ∀ g : ℕ, 3 ≤ g → AgreesWithClosedDemandPrefix Bad g) := by
  rintro ⟨hkkhFin, hkkhTail, hprefix⟩
  exact (Nat.not_le.mpr hgt)
    (demand_floor_of_dvd_four_prefixes_and_kkh26_finite_kkh26_tail
      Bad R hkkhFin hkkhTail hprefix r n hn hg hr hrg)

/-- A single budget overrun refutes the all-ladder finite-prefix plus all-ladder tail route. -/
theorem not_ladder_finite_ladder_tail_and_prefixes_of_dvd_four_budget_lt_bad
    (Bad : ℕ → ℕ → ℕ) (R : ℕ)
    (r n : ℕ)
    (hn : 4 ∣ n)
    (hg : 3 ≤ n / 4)
    (hr : 3 ≤ r)
    (hrg : r ≤ n / 4)
    (hgt : deepBandBudgetR r n < Bad r n) :
    ¬ (HasLadderMajorantsOn Bad (Finset.Icc 6 R) ∧
      HasLadderMajorantsAbove Bad R ∧
      ∀ g : ℕ, 3 ≤ g → AgreesWithClosedDemandPrefix Bad g) := by
  rintro ⟨hladderFin, hladderTail, hprefix⟩
  exact (Nat.not_le.mpr hgt)
    (demand_floor_of_dvd_four_prefixes_and_ladder_finite_ladder_tail
      Bad R hladderFin hladderTail hprefix r n hn hg hr hrg)

end ArkLib.ProximityGap.Frontier.R141DemandFloorHybridConstructorObstructions

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R141DemandFloorHybridConstructorObstructions.not_kkh26_finite_kkh26_tail_and_prefixes_of_dvd_four_budget_lt_bad
#print axioms
  ArkLib.ProximityGap.Frontier.R141DemandFloorHybridConstructorObstructions.not_ladder_finite_ladder_tail_and_prefixes_of_dvd_four_budget_lt_bad
