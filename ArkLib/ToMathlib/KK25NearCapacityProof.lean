/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArkLib.Data.CodingTheory.ProximityGap.CapacityBounds

/-!
# A named `Θ(1/log n)` slack residual for the BCHKS25+KK25 near-capacity lower bound

`CodingTheory.rs_epsCA_lower_capacity_bchks25_kk25` (ABF26 Theorem 4.16 [BCHKS25, KK25])
existentially binds the proximity `slack` as a bare `ℝ≥0` knob, with a comment that it is of
order `Θ(1/log n)`.  This file makes that asymptotic shape an explicit, *named* residual instead
of an unconstrained parameter, without claiming the underlying bad-code construction is proved.

Main definitions:

* `CodingTheory.SlackThetaInvLog c₁ c₂ n slack`: the two-sided explicit-constant bracket
  `c₁ / Real.log n ≤ slack ≤ c₂ / Real.log n`, the formal `Θ(1/log n)` predicate.
* `CodingTheory.RSLowerCapacityWitnessΘ`: the `RSLowerCapacityWitness` payload augmented with a
  `SlackThetaInvLog` certificate on its `slack` field (with `n = |L|`).

Main results:

* `CodingTheory.RSLowerCapacityWitnessΘ.toWitness`: forgetful map back to the bare witness.
* `CodingTheory.rs_epsCA_lower_capacity_bchks25_kk25_of_witnessΘ`: a `Θ`-shaped witness still
  re-derives the external T4.16 front door.
* Basic structural lemmas about `SlackThetaInvLog` (positivity, monotonicity in the constants,
  and a packaging constructor from a single `slack = c / log n`).

All surfaces here are checked: each `#print axioms` line reports
`[propext, Classical.choice, Quot.sound]`.
-/

open scoped NNReal

namespace CodingTheory

/-- **Named `Θ(1/log n)` slack residual.**  For an explicit positive constant pair `0 < c₁ ≤ c₂`
and a code length `n`, this asserts the (real) slack lies in the two-sided bracket
`c₁ / Real.log n ≤ slack ≤ c₂ / Real.log n`.  This is the concrete in-Lean encoding of the
ABF26 T4.16 "`slack` of order `Θ(1/log n)`" claim, replacing the bare existential knob with a
named residual carrying explicit constants. -/
def SlackThetaInvLog (c₁ c₂ : ℝ) (n : ℕ) (slack : ℝ) : Prop :=
  0 < c₁ ∧ c₁ ≤ c₂ ∧ c₁ / Real.log n ≤ slack ∧ slack ≤ c₂ / Real.log n

namespace SlackThetaInvLog

variable {c₁ c₂ : ℝ} {n : ℕ} {slack : ℝ}

/-- The lower constant of a `Θ(1/log n)` slack certificate is positive. -/
theorem c₁_pos (h : SlackThetaInvLog c₁ c₂ n slack) : 0 < c₁ := h.1

/-- The constants of a `Θ(1/log n)` slack certificate are ordered. -/
theorem c₁_le_c₂ (h : SlackThetaInvLog c₁ c₂ n slack) : c₁ ≤ c₂ := h.2.1

/-- The lower bracket of a `Θ(1/log n)` slack certificate. -/
theorem lower (h : SlackThetaInvLog c₁ c₂ n slack) : c₁ / Real.log n ≤ slack := h.2.2.1

/-- The upper bracket of a `Θ(1/log n)` slack certificate. -/
theorem upper (h : SlackThetaInvLog c₁ c₂ n slack) : slack ≤ c₂ / Real.log n := h.2.2.2

/-- When `n ≥ 2` (so `Real.log n > 0`) the slack of a `Θ(1/log n)` certificate is positive. -/
theorem slack_pos (h : SlackThetaInvLog c₁ c₂ n slack) (hn : 2 ≤ n) : 0 < slack := by
  have hlogpos : 0 < Real.log n := by
    have : (1 : ℝ) < n := by exact_mod_cast lt_of_lt_of_le one_lt_two hn
    exact Real.log_pos this
  have hdivpos : 0 < c₁ / Real.log n := div_pos h.c₁_pos hlogpos
  exact lt_of_lt_of_le hdivpos h.lower

/-- A `Θ(1/log n)` certificate widens to any larger constant bracket. -/
theorem mono {c₁' c₂' : ℝ} (h : SlackThetaInvLog c₁ c₂ n slack)
    (hn : 2 ≤ n) (h1 : 0 < c₁') (h1' : c₁' ≤ c₁) (h2 : c₂ ≤ c₂') :
    SlackThetaInvLog c₁' c₂' n slack := by
  have hlogpos : 0 < Real.log n := by
    have : (1 : ℝ) < n := by exact_mod_cast lt_of_lt_of_le one_lt_two hn
    exact Real.log_pos this
  refine ⟨h1, le_trans h1' (le_trans h.c₁_le_c₂ h2), ?_, ?_⟩
  · exact le_trans (div_le_div_of_nonneg_right h1' hlogpos.le) h.lower
  · exact le_trans h.upper (div_le_div_of_nonneg_right h2 hlogpos.le)

/-- An exact `slack = c / Real.log n` (with `0 < c`) is a `Θ(1/log n)` certificate with constants
`c₁ = c₂ = c`. -/
theorem of_eq {c : ℝ} (hc : 0 < c) (heq : slack = c / Real.log n) :
    SlackThetaInvLog c c n slack := by
  refine ⟨hc, le_rfl, ?_, ?_⟩ <;> rw [heq]

end SlackThetaInvLog

/-- **`Θ`-shaped near-capacity witness package.**  A `RSLowerCapacityWitness` whose `slack` field
additionally carries an explicit-constant `Θ(1/log n)` certificate, with `n = |L| = |ιC|`.  This
turns the bare existential slack knob of `rs_epsCA_lower_capacity_bchks25_kk25` into a named
residual carrying explicit constants `0 < c₁ ≤ c₂`. -/
structure RSLowerCapacityWitnessΘ
    (c ρ : ℝ≥0)
    (ιC : Type) [Fintype ιC] [Nonempty ιC] [DecidableEq ιC]
    (FC : Type) [Field FC] [Fintype FC] [DecidableEq FC]
    extends RSLowerCapacityWitness c ρ ιC FC where
  /-- Lower asymptotic constant of the slack. -/
  slackC₁ : ℝ
  /-- Upper asymptotic constant of the slack. -/
  slackC₂ : ℝ
  /-- The named `Θ(1/log n)` certificate on `slack`, with `n = |ιC|`. -/
  slackTheta : SlackThetaInvLog slackC₁ slackC₂ (Fintype.card ιC) ((toRSLowerCapacityWitness.slack : ℝ))

namespace RSLowerCapacityWitnessΘ

variable {c ρ : ℝ≥0}
    {ιC : Type} [Fintype ιC] [Nonempty ιC] [DecidableEq ιC]
    {FC : Type} [Field FC] [Fintype FC] [DecidableEq FC]

/-- Forget the `Θ(1/log n)` certificate, recovering the bare near-capacity witness. -/
def toWitness (W : RSLowerCapacityWitnessΘ c ρ ιC FC) : RSLowerCapacityWitness c ρ ιC FC :=
  W.toRSLowerCapacityWitness

/-- The `Θ`-certificate's lower constant is positive. -/
theorem slackC₁_pos (W : RSLowerCapacityWitnessΘ c ρ ιC FC) : 0 < W.slackC₁ :=
  W.slackTheta.c₁_pos

/-- The slack of a `Θ`-shaped witness is positive whenever the code length is at least `2`. -/
theorem slack_pos (W : RSLowerCapacityWitnessΘ c ρ ιC FC) (hn : 2 ≤ Fintype.card ιC) :
    (0 : ℝ) < (W.toRSLowerCapacityWitness.slack : ℝ) :=
  W.slackTheta.slack_pos hn

end RSLowerCapacityWitnessΘ

/-- A `Θ`-shaped near-capacity witness still reassembles the external T4.16 front door,
`rs_epsCA_lower_capacity_bchks25_kk25`. -/
theorem rs_epsCA_lower_capacity_bchks25_kk25_of_witnessΘ
    (c : ℝ≥0) (hc : 0 < c) (ρ : ℝ≥0) (hρ_pos : 0 < ρ)
    (hρ_lt : ρ < (1 / 2 : ℝ≥0))
    {ιC : Type} [Fintype ιC] [Nonempty ιC] [DecidableEq ιC]
    {FC : Type} [Field FC] [Fintype FC] [DecidableEq FC]
    (W : RSLowerCapacityWitnessΘ c ρ ιC FC) :
    rs_epsCA_lower_capacity_bchks25_kk25 c hc ρ hρ_pos hρ_lt :=
  rs_epsCA_lower_capacity_bchks25_kk25_of_witness c hc ρ hρ_pos hρ_lt W.toWitness

#print axioms CodingTheory.SlackThetaInvLog
#print axioms CodingTheory.SlackThetaInvLog.slack_pos
#print axioms CodingTheory.SlackThetaInvLog.mono
#print axioms CodingTheory.SlackThetaInvLog.of_eq
#print axioms CodingTheory.RSLowerCapacityWitnessΘ.toWitness
#print axioms CodingTheory.RSLowerCapacityWitnessΘ.slack_pos
#print axioms CodingTheory.rs_epsCA_lower_capacity_bchks25_kk25_of_witnessΘ

end CodingTheory
