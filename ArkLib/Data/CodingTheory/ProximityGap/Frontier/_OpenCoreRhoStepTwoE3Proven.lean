/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.CharZeroEnergyThreeExact
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._OpenCoreRhoStepTwoExplicit

/-!
# Door IV: thread the KERNEL-PROVEN `E₃` value into the second `ρ` rung (#444)

`_OpenCoreRhoStepTwoExplicit.lean` states the second antitone rung `ρ(3) ≤ ρ(2)` with the third
char-0 energy `E₃(ℂ) = 15n³ − 45n² + 40n`, but it carries an HONESTY NOTE saying that closed form
is *only probe-verified* (exact at `n = 4,8,16,32`), "NOT yet kernel-proven... the combinatorial
proof is left open."

That note is now **stale**: `CharZeroEnergyThreeExact.B6_eq_E3` already proves, axiom-clean (rel.
to the two elementary named inputs Lam–Leung-at-depth-≤3 and the add-one-class `BalancedCount`
recursion), that the depth-3 zero-sum count `B 6 m` — i.e. `E₃(μ_n)` for `n = 2m` — equals exactly
`15(2m)³ − 45(2m)² + 40(2m)`. So `E₃` is no longer a bare probe hypothesis: it is the value of a
recursion-solved integer count.

## What this file does (pure assembly of two PROVEN in-tree pieces; frontier-movement, not re-map)

It connects the two previously-disconnected files. Concretely:

* `B6_eq_E3_real` — casts `CharZeroEnergyThreeExact.B6_eq_E3` to `ℝ`: for any `BalancedCount B`
  witness and `n := 2m`, `(B 6 m : ℝ) = 15·n³ − 45·n² + 40·n`. This is the bridge: the StepTwo
  E₃ polynomial is the real image of the kernel-proven integer zero-sum count.

* `rho_step_two_target_E3_proven` — the SECOND antitone rung restated with `E₃` supplied by the
  recursion-proven count `(B 6 m : ℝ)` instead of the bare polynomial literal: for `n = 2m > 1`,
  `p − 1 > 0`, and a `BalancedCount B` witness, the explicit step
  `ρ(3) ≤ ρ(2)` holds **iff** the single normalized char-p target
  `S_3 ≤ S_2·(B 6 m)/(3n(n−1))` holds, with the `E₃` coefficient `(B 6 m : ℝ)` now PROVEN equal to
  `15n³−45n²+40n` (no longer assumed). This removes the StepTwo "left open" honesty caveat on the
  `E₃` *value*: the only open content of rung 2 is the char-p `S_3` bound itself, exactly as before.

## Honest scope

This does NOT prove the `S_3` target (the genuine open analytic content of rung 2), does NOT prove
the full antitone chain, and makes NO CORE / cancellation / completion / moment-saving / capacity
claim. The prize CORE stays OPEN. What changes: the `E₃` coefficient in the rung is now the
value of an axiom-clean recursion solution, so the rung no longer rests on an unverified closed-form
guess. The two elementary inputs (`BalancedCount` + Lam–Leung-depth-≤3) are still carried as named
hypotheses exactly as in `CharZeroEnergyThreeExact`, NOT silently discharged.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`. Issue #444.
-/

namespace ProximityGap.Frontier.OpenCoreRhoStepTwoE3Proven

open ArkLib.ProximityGap.Frontier.CharZeroEnergyThree (BalancedCount B6_eq_E3)

variable {B : ℕ → ℕ → ℤ}

/-- **Bridge: the kernel-proven depth-3 zero-sum count, cast to `ℝ`, is the StepTwo `E₃`.**
`CharZeroEnergyThreeExact.B6_eq_E3` proves `B 6 m = 15(2m)³ − 45(2m)² + 40(2m)` over `ℤ` from
the `BalancedCount` recursion. Casting to `ℝ` and writing `n = 2m`, the real image of the count
is exactly the `E₃(ℂ) = 15n³ − 45n² + 40n` literal used (probe-only) in StepTwoExplicit. -/
theorem B6_eq_E3_real (h : BalancedCount B) (m : ℕ) :
    (B 6 m : ℝ)
      = 15 * (2 * (m : ℝ)) ^ 3 - 45 * (2 * (m : ℝ)) ^ 2 + 40 * (2 * (m : ℝ)) := by
  have hint := B6_eq_E3 h m
  have := congrArg (fun z : ℤ => (z : ℝ)) hint
  push_cast at this
  simpa using this

/-- **The second `ρ` rung with `E₃` supplied by the recursion-proven count.**

For `n = 2m`, `n > 1`, `p − 1 > 0`, and a `BalancedCount B` witness, the explicit antitone step
`ρ(3) ≤ ρ(2)` (written with the `E₃` coefficient as the kernel-proven count `(B 6 m : ℝ)`) is
equivalent to the single normalized char-p target
`S_3 ≤ S_2·(B 6 m)/(3n(n−1))`.

This is `_OpenCoreRhoStepTwoExplicit.rho_step_two_target` with its bare `E₃`-polynomial literal
replaced everywhere by `(B 6 m : ℝ)`, which `B6_eq_E3_real` proves equals that literal. The
analytic content (the `S_3` bound) is unchanged; what is removed is the StepTwo probe-only caveat on
the `E₃` value. -/
theorem rho_step_two_target_E3_proven
    (h : BalancedCount B) (m : ℕ) (S2 S3 p : ℝ)
    (hp1 : 0 < p - 1) (hm : 1 < (2 * (m : ℝ))) :
    (S3 / ((p - 1) * (B 6 m : ℝ))
        ≤ S2 / ((p - 1) * (3 * (2 * (m : ℝ)) * ((2 * (m : ℝ)) - 1))))
      ↔ S3 ≤
          S2 * (B 6 m : ℝ) / (3 * (2 * (m : ℝ)) * ((2 * (m : ℝ)) - 1)) := by
  rw [B6_eq_E3_real h m]
  exact ProximityGap.Frontier.OpenCoreRhoStepTwo.rho_step_two_target
    S2 S3 p (2 * (m : ℝ)) hp1 hm

end ProximityGap.Frontier.OpenCoreRhoStepTwoE3Proven

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ProximityGap.Frontier.OpenCoreRhoStepTwoE3Proven.B6_eq_E3_real
#print axioms ProximityGap.Frontier.OpenCoreRhoStepTwoE3Proven.rho_step_two_target_E3_proven
