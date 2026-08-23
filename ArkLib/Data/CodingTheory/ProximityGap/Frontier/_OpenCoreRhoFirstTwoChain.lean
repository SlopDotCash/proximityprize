/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._OpenCoreRhoMonotone
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._OpenCoreRhoStepOneExplicit
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._OpenCoreRhoStepTwoExplicit

/-!
# Door IV: chaining the first two explicit `ρ` targets (#444)

`_OpenCoreRhoStepOneExplicit.lean` pins the first monotonicity rung to the single char-p target
`S_2 ≤ 3n(n−1)(p−n)`. `_OpenCoreRhoStepTwoExplicit.lean` pins the second rung to the normalized
next-energy target
`S_3 ≤ S_2·(15n³−45n²+40n)/(3n(n−1))`.

This file packages the exact two-rung consumer: if those two finite targets are proved elsewhere,
then the explicit normalized quantities satisfy
```
    ρ_3 ≤ ρ_2 ≤ ρ_1,
```
where `ρ_1 = (p n − n²)/((p−1)n)`, `ρ_2 = S_2/((p−1)·3n(n−1))`, and
`ρ_3 = S_3/((p−1)·(15n³−45n²+40n))`.

SCOPE: consumer/reduction only. It proves neither finite target, does not prove the probe-verified
`E_3` closed form, and makes no CORE/cancellation/completion/moment-saving/capacity claim.
-/

namespace ProximityGap.Frontier.OpenCoreRhoFirstTwo

open ProximityGap.Frontier.OpenCoreRho
open ProximityGap.Frontier.OpenCoreRhoStepOne
open ProximityGap.Frontier.OpenCoreRhoStepTwo

/-- The first two explicit finite targets imply the first two normalized `ρ` inequalities,
`ρ_3 ≤ ρ_2` and `ρ_2 ≤ ρ_1`. This is the exact consumer surface for extending the proven base
`ρ(1) < 1` through two additional rungs, once the two char-p energy targets are discharged. -/
theorem first_two_rho_steps_of_targets (S2 S3 p n : ℝ)
    (hp1 : 0 < p - 1) (hn : 1 < n)
    (hS2 : S2 ≤ 3 * n * (n - 1) * (p - n))
    (hS3 : S3 ≤ S2 * (15 * n ^ 3 - 45 * n ^ 2 + 40 * n) / (3 * n * (n - 1))) :
    (S3 / ((p - 1) * (15 * n ^ 3 - 45 * n ^ 2 + 40 * n))
        ≤ S2 / ((p - 1) * (3 * n * (n - 1)))) ∧
      (S2 / ((p - 1) * (3 * n * (n - 1)))
        ≤ (p * n - n ^ 2) / ((p - 1) * n)) := by
  constructor
  · exact (rho_step_two_target S2 S3 p n hp1 hn).2 hS3
  · exact (rho_step_one_target S2 p n hp1 hn).2 hS2

/-- Chained form of `first_two_rho_steps_of_targets`: the two finite targets imply the direct
comparison `ρ_3 ≤ ρ_1`. This theorem is transitive bookkeeping only; all analytic content remains in
`hS2` and `hS3`. -/
theorem rho_three_le_rho_one_of_first_two_targets (S2 S3 p n : ℝ)
    (hp1 : 0 < p - 1) (hn : 1 < n)
    (hS2 : S2 ≤ 3 * n * (n - 1) * (p - n))
    (hS3 : S3 ≤ S2 * (15 * n ^ 3 - 45 * n ^ 2 + 40 * n) / (3 * n * (n - 1))) :
    S3 / ((p - 1) * (15 * n ^ 3 - 45 * n ^ 2 + 40 * n))
      ≤ (p * n - n ^ 2) / ((p - 1) * n) := by
  rcases first_two_rho_steps_of_targets S2 S3 p n hp1 hn hS2 hS3 with ⟨h32, h21⟩
  exact le_trans h32 h21

/-- The first two explicit finite targets plus the proven Parseval base `ρ_1 < 1` put both
normalized finite rungs below `1`. This is the exact two-rung consumer surface: all hard
analytic content remains in the two target inequalities `hS2` and `hS3`; this theorem only
chains them to the already-proven base case. -/
theorem first_two_rho_lt_one_of_targets (S2 S3 p n : ℝ)
    (hp : n < p) (hn : 1 < n)
    (hS2 : S2 ≤ 3 * n * (n - 1) * (p - n))
    (hS3 : S3 ≤ S2 * (15 * n ^ 3 - 45 * n ^ 2 + 40 * n) / (3 * n * (n - 1))) :
    (S2 / ((p - 1) * (3 * n * (n - 1))) < 1) ∧
      (S3 / ((p - 1) * (15 * n ^ 3 - 45 * n ^ 2 + 40 * n)) < 1) := by
  have hp1 : 0 < p - 1 := by linarith
  have hbase : (p * n - n ^ 2) / ((p - 1) * n) < 1 :=
    rho_base_lt_one n p hn hp
  rcases first_two_rho_steps_of_targets S2 S3 p n hp1 hn hS2 hS3 with ⟨h32, h21⟩
  constructor
  · exact lt_of_le_of_lt h21 hbase
  · exact lt_of_le_of_lt (le_trans h32 h21) hbase

/-- Finite-prefix consumer form through the first two explicit rungs. For any named sequence `ρ`
whose first three values are the Parseval base and the two normalized explicit rungs, the two finite
target inequalities imply the open-core bound `ρ r < 1` for every `1 ≤ r ≤ 3`. This is only a
three-point packaging of the two target reductions plus the proven base. -/
theorem rho_prefix_three_lt_one_of_targets (ρ : ℕ → ℝ) (S2 S3 p n : ℝ)
    (hp : n < p) (hn : 1 < n)
    (hρ1 : ρ 1 = (p * n - n ^ 2) / ((p - 1) * n))
    (hρ2 : ρ 2 = S2 / ((p - 1) * (3 * n * (n - 1))))
    (hρ3 : ρ 3 = S3 / ((p - 1) * (15 * n ^ 3 - 45 * n ^ 2 + 40 * n)))
    (hS2 : S2 ≤ 3 * n * (n - 1) * (p - n))
    (hS3 : S3 ≤ S2 * (15 * n ^ 3 - 45 * n ^ 2 + 40 * n) / (3 * n * (n - 1))) :
    ∀ r : ℕ, 1 ≤ r → r ≤ 3 → ρ r < 1 := by
  intro r hr1 hr3
  have hbase : (p * n - n ^ 2) / ((p - 1) * n) < 1 :=
    rho_base_lt_one n p hn hp
  have hlt := first_two_rho_lt_one_of_targets S2 S3 p n hp hn hS2 hS3
  interval_cases r
  · simpa [hρ1] using hbase
  · simpa [hρ2] using hlt.1
  · simpa [hρ3] using hlt.2

end ProximityGap.Frontier.OpenCoreRhoFirstTwo

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ProximityGap.Frontier.OpenCoreRhoFirstTwo.first_two_rho_steps_of_targets
#print axioms ProximityGap.Frontier.OpenCoreRhoFirstTwo.rho_three_le_rho_one_of_first_two_targets
#print axioms ProximityGap.Frontier.OpenCoreRhoFirstTwo.first_two_rho_lt_one_of_targets
#print axioms ProximityGap.Frontier.OpenCoreRhoFirstTwo.rho_prefix_three_lt_one_of_targets
