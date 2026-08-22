/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R384CenteredGeneratorAverage

/-!
# R385: off-diagonal cross-generator covariance misses unique-root endpoints

The natural continuation of R384 is to bound pairs of distinct primitive generators by imposing
two finite-field equations.  This file audits that proposal before any algebraic-geometry input is
spent.  For an endpoint incident to `Z` generators, the number of ordered distinct generator pairs
is exactly `Z^2-Z`.  It therefore vanishes identically on the `Z=1` stratum, although that stratum's
centered coefficient is `q-card(T)` and can be nonzero (indeed large).

Thus an off-diagonal two-generator estimate cannot control the single-generator relations seen in
the exact R383 census.  It needs a separate first-incidence input, which is the original wall.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R385CrossGeneratorCovarianceBlindSpot

open ArkLib.ProximityGap.Frontier.R383GeneratorAveragingDoubleCount
open ArkLib.ProximityGap.Frontier.R384CenteredGeneratorAverage

variable {A D : Type*} [DecidableEq A] [DecidableEq D]

/-- Number of ordered pairs of distinct generators at which one endpoint vanishes. -/
def offDiagEndpointIncidence
    (T : Finset A) (rel : A → D → Prop) [DecidableRel rel] (d : D) : ℕ :=
  ((T.filter fun a => rel a d).offDiag).card

/-- The cross-generator pair count is the second factorial moment `Z*(Z-1)`. -/
theorem offDiagEndpointIncidence_eq
    (T : Finset A) (rel : A → D → Prop) [DecidableRel rel] (d : D) :
    offDiagEndpointIncidence T rel d =
      endpointIncidence T rel d * endpointIncidence T rel d - endpointIncidence T rel d := by
  unfold offDiagEndpointIncidence endpointIncidence
  rw [Finset.offDiag_card]

/-- Every endpoint with at most one primitive-generator root is invisible to off-diagonal
cross-generator covariance. -/
theorem offDiagEndpointIncidence_eq_zero_of_le_one
    (T : Finset A) (rel : A → D → Prop) [DecidableRel rel] (d : D)
    (h : endpointIncidence T rel d ≤ 1) :
    offDiagEndpointIncidence T rel d = 0 := by
  rw [offDiagEndpointIncidence_eq]
  have hcases : endpointIncidence T rel d = 0 ∨ endpointIncidence T rel d = 1 := by omega
  rcases hcases with hzero | hone
  · simp [hzero]
  · simp [hone]

/-- **Blind-spot counterexample.** A unique-root endpoint has zero off-diagonal pair incidence but
centered coefficient `q-card(T)`, which is nonzero whenever `q` differs from the generator count. -/
theorem uniqueRoot_invisible_but_centered_nonzero
    (q : ℝ) (T : Finset A) (rel : A → D → Prop) [DecidableRel rel] (d : D)
    (hZ : endpointIncidence T rel d = 1) (hq : q ≠ T.card) :
    offDiagEndpointIncidence T rel d = 0 ∧
      centeredEndpointIncidence q T rel d ≠ 0 := by
  constructor
  · apply offDiagEndpointIncidence_eq_zero_of_le_one
    omega
  · unfold centeredEndpointIncidence
    simpa [hZ] using (sub_ne_zero.mpr hq)

end ArkLib.ProximityGap.Frontier.R385CrossGeneratorCovarianceBlindSpot

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R385CrossGeneratorCovarianceBlindSpot.uniqueRoot_invisible_but_centered_nonzero
