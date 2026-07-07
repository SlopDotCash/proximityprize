/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R125DemandFloorMaximalOrbitProducer

/-!
# Obstructions to the maximal binomial demand-tail producer

R125 shows that the demand tail follows from the maximal-binomial count bound

`Bad r (4g) ≤ (4g) * C(2g,r-1) + 1`.

This file records the matching contrapositives: if a candidate bad-count family exceeds that
maximal allowance at one active deep rung, then the maximal producer route is impossible.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R126DemandFloorMaximalProducerObstructions

open ArkLib.ProximityGap.Frontier.R109DemandFloorGeneralBudgetBridge
open ArkLib.ProximityGap.Frontier.R115DemandFloorTailReduction
open ArkLib.ProximityGap.Frontier.R121DemandFloorTailTheoremInterface
open ArkLib.ProximityGap.Frontier.R125DemandFloorMaximalOrbitProducer

/-- A single overrun of the maximal-binomial allowance refutes `MaximalTailCountBound`. -/
theorem not_maximal_tail_count_bound_of_allowance_lt_bad
    (Bad : ℕ → ℕ → ℕ)
    (g r : ℕ)
    (hg : 3 ≤ g)
    (hr : 6 ≤ r)
    (hrg : r ≤ g)
    (hgt : (4 * g) * maximalTailOP g r + 1 < Bad r (4 * g)) :
    ¬ MaximalTailCountBound Bad := by
  intro hmax
  exact (Nat.not_le.mpr hgt) (hmax g r hg hr hrg)

/-- If the maximal-binomial allowance is below `Bad`, the R125 budget route cannot be used. -/
theorem not_maximal_route_of_allowance_lt_bad
    (Bad : ℕ → ℕ → ℕ)
    (g r : ℕ)
    (hg : 3 ≤ g)
    (hr : 6 ≤ r)
    (hrg : r ≤ g)
    (hgt : (4 * g) * maximalTailOP g r + 1 < Bad r (4 * g)) :
    ¬ ∃ _hmax : MaximalTailCountBound Bad,
      Bad r (4 * g) ≤ deepBandBudgetR r (4 * g) := by
  rintro ⟨hmax, _hbudget⟩
  exact not_maximal_tail_count_bound_of_allowance_lt_bad Bad g r hg hr hrg hgt hmax

/-- If the maximal-binomial allowance is below `Bad`, then no R125 maximal-tail proof can
produce the packaged natural demand theorem. -/
theorem not_maximal_natural_demand_route_of_allowance_lt_bad
    (Bad : ℕ → ℕ → ℕ)
    (g r : ℕ)
    (hg : 3 ≤ g)
    (hr : 6 ≤ r)
    (hrg : r ≤ g)
    (hgt : (4 * g) * maximalTailOP g r + 1 < Bad r (4 * g)) :
    ¬ ∃ (_ : ∀ g : ℕ, 3 ≤ g → AgreesWithClosedDemandPrefix Bad g)
        (_ : MaximalTailCountBound Bad),
      NaturalDemandCertificateTheorem Bad := by
  rintro ⟨_hprefix, hmax, _hnatural⟩
  exact not_maximal_tail_count_bound_of_allowance_lt_bad Bad g r hg hr hrg hgt hmax

/-- Divisibility-form obstruction for the maximal-binomial route. -/
theorem not_maximal_route_of_dvd_four_allowance_lt_bad
    (Bad : ℕ → ℕ → ℕ)
    (r n : ℕ)
    (hn : 4 ∣ n)
    (hg : 3 ≤ n / 4)
    (hr : 6 ≤ r)
    (hrg : r ≤ n / 4)
    (hgt : n * maximalTailOP (n / 4) r + 1 < Bad r n) :
    ¬ MaximalTailCountBound Bad := by
  have hn' : n = 4 * (n / 4) :=
    ArkLib.ProximityGap.Frontier.R123DemandFloorDivFourInterface.eq_four_mul_div_four_of_dvd n hn
  have hgt' : (4 * (n / 4)) * maximalTailOP (n / 4) r + 1 <
      Bad r (4 * (n / 4)) := by
    simpa only [← hn'] using hgt
  exact not_maximal_tail_count_bound_of_allowance_lt_bad
    Bad (n / 4) r hg hr hrg hgt'

/-- Divisibility-form obstruction for the R125 maximal-tail proof of the packaged natural demand
theorem. -/
theorem not_maximal_natural_demand_route_of_dvd_four_allowance_lt_bad
    (Bad : ℕ → ℕ → ℕ)
    (r n : ℕ)
    (hn : 4 ∣ n)
    (hg : 3 ≤ n / 4)
    (hr : 6 ≤ r)
    (hrg : r ≤ n / 4)
    (hgt : n * maximalTailOP (n / 4) r + 1 < Bad r n) :
    ¬ ∃ (_ : ∀ g : ℕ, 3 ≤ g → AgreesWithClosedDemandPrefix Bad g)
        (_ : MaximalTailCountBound Bad),
      NaturalDemandCertificateTheorem Bad := by
  rintro ⟨_hprefix, hmax, _hnatural⟩
  exact not_maximal_route_of_dvd_four_allowance_lt_bad Bad r n hn hg hr hrg hgt hmax

end ArkLib.ProximityGap.Frontier.R126DemandFloorMaximalProducerObstructions

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R126DemandFloorMaximalProducerObstructions.not_maximal_tail_count_bound_of_allowance_lt_bad
#print axioms
  ArkLib.ProximityGap.Frontier.R126DemandFloorMaximalProducerObstructions.not_maximal_route_of_allowance_lt_bad
#print axioms
  ArkLib.ProximityGap.Frontier.R126DemandFloorMaximalProducerObstructions.not_maximal_route_of_dvd_four_allowance_lt_bad
#print axioms
  ArkLib.ProximityGap.Frontier.R126DemandFloorMaximalProducerObstructions.not_maximal_natural_demand_route_of_allowance_lt_bad
#print axioms
  ArkLib.ProximityGap.Frontier.R126DemandFloorMaximalProducerObstructions.not_maximal_natural_demand_route_of_dvd_four_allowance_lt_bad
