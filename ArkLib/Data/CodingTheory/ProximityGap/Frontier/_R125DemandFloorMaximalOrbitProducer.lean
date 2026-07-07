/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R124DemandFloorExplicitProducerNInterface

/-!
# Maximal binomial orbit producer

R122 reduces the demand tail to an explicit orbit-count function `OP g r`.  The largest admissible
choice is the binomial cap itself, `OP g r = C(2g, r-1)`.  With that canonical choice, the only
remaining tail obligation is the honest-orbit count inequality

`Bad r (4g) ≤ (4g) * C(2g, r-1) + 1`.

This file records that reduction in a reusable form.  Later combinatorial work can prove the
single displayed inequality and immediately obtain the explicit producer.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R125DemandFloorMaximalOrbitProducer

open ArkLib.ProximityGap.Frontier.R115DemandFloorTailReduction
open ArkLib.ProximityGap.Frontier.R121DemandFloorTailTheoremInterface
open ArkLib.ProximityGap.Frontier.R122DemandFloorExplicitOrbitProducer
open ArkLib.ProximityGap.Frontier.R124DemandFloorExplicitProducerNInterface

/-- The maximal admissible orbit-count witness at `(g,r)`. -/
def maximalTailOP (g r : ℕ) : ℕ := (2 * g).choose (r - 1)

/-- The single count inequality needed by the maximal binomial producer. -/
def MaximalTailCountBound (Bad : ℕ → ℕ → ℕ) : Prop :=
  ∀ g r : ℕ, 3 ≤ g → 6 ≤ r → r ≤ g →
    Bad r (4 * g) ≤ (4 * g) * maximalTailOP g r + 1

/-- A maximal count bound gives an explicit natural tail orbit producer. -/
theorem explicit_orbit_producer_of_maximal_tail_count_bound
    (Bad : ℕ → ℕ → ℕ)
    (hmax : MaximalTailCountBound Bad) :
    ExplicitNaturalTailOrbitProducer Bad maximalTailOP := by
  intro g r hg hr hrg
  exact ⟨le_rfl, hmax g r hg hr hrg⟩

/-- A maximal count bound plus checked prefix agreement gives the packaged natural demand
certificate theorem. -/
theorem natural_demand_theorem_of_maximal_tail_count_bound
    (Bad : ℕ → ℕ → ℕ)
    (hprefix : ∀ g : ℕ, 3 ≤ g → AgreesWithClosedDemandPrefix Bad g)
    (hmax : MaximalTailCountBound Bad) :
    NaturalDemandCertificateTheorem Bad :=
  natural_demand_theorem_of_explicit_orbit_producer Bad maximalTailOP hprefix
    (explicit_orbit_producer_of_maximal_tail_count_bound Bad hmax)

/-- Direct active-budget consumer for the maximal binomial producer. -/
theorem demand_floor_active_of_maximal_tail_count_bound
    (Bad : ℕ → ℕ → ℕ)
    (hprefix : ∀ g : ℕ, 3 ≤ g → AgreesWithClosedDemandPrefix Bad g)
    (hmax : MaximalTailCountBound Bad)
    (g r : ℕ)
    (hg : 3 ≤ g)
    (hr : 3 ≤ r)
    (hrg : r ≤ g) :
    Bad r (4 * g) ≤
      ArkLib.ProximityGap.Frontier.R109DemandFloorGeneralBudgetBridge.deepBandBudgetR r (4 * g) := by
  exact demand_floor_active_of_explicit_orbit_producer Bad maximalTailOP hprefix
    (explicit_orbit_producer_of_maximal_tail_count_bound Bad hmax) g r hg hr hrg

/-- Divisibility-form `(r,n)` consumer for the maximal binomial producer. -/
theorem demand_floor_of_dvd_four_maximal_tail_count_bound
    (Bad : ℕ → ℕ → ℕ)
    (hprefix : ∀ g : ℕ, 3 ≤ g → AgreesWithClosedDemandPrefix Bad g)
    (hmax : MaximalTailCountBound Bad)
    (r n : ℕ)
    (hn : 4 ∣ n)
    (hg : 3 ≤ n / 4)
    (hr : 3 ≤ r)
    (hrg : r ≤ n / 4) :
    Bad r n ≤ ArkLib.ProximityGap.Frontier.R109DemandFloorGeneralBudgetBridge.deepBandBudgetR r n := by
  exact demand_floor_of_dvd_four_explicit_orbit_producer Bad maximalTailOP hprefix
    (explicit_orbit_producer_of_maximal_tail_count_bound Bad hmax) r n hn hg hr hrg

end ArkLib.ProximityGap.Frontier.R125DemandFloorMaximalOrbitProducer

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R125DemandFloorMaximalOrbitProducer.maximalTailOP
#print axioms
  ArkLib.ProximityGap.Frontier.R125DemandFloorMaximalOrbitProducer.MaximalTailCountBound
#print axioms
  ArkLib.ProximityGap.Frontier.R125DemandFloorMaximalOrbitProducer.explicit_orbit_producer_of_maximal_tail_count_bound
#print axioms
  ArkLib.ProximityGap.Frontier.R125DemandFloorMaximalOrbitProducer.natural_demand_theorem_of_maximal_tail_count_bound
#print axioms
  ArkLib.ProximityGap.Frontier.R125DemandFloorMaximalOrbitProducer.demand_floor_active_of_maximal_tail_count_bound
#print axioms
  ArkLib.ProximityGap.Frontier.R125DemandFloorMaximalOrbitProducer.demand_floor_of_dvd_four_maximal_tail_count_bound
