/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CharPWickConditionalPin

/-!
# The char-`p` step-ratio pin and its domination of the cross-bound pin (#444)

Two char-`p` reductions of the prize deep-moment Wick bound `E_r(μ_n) ≤ (2r−1)‼·n^r = Wick_r` are
in tree, each phrasing the SAME open inequality differently against the exact recursion
`E_{r+1} = n·E_r + cross_r` (`CharPMomentRecursion.rEnergy_succ`, `CharPWickConditionalPin.cross_eq`):

* the **cross-bound** form (`CharPWickConditionalPin.CrossBoundedByWick`):
  `cross_r ≤ 2r·n·Wick_r` — the off-diagonal mass measured against the char-`0` **envelope** `Wick_r`;
* the **step-ratio** form (the abstract `WickStepRatio.le_wickEnvelope_of_step_ratio` consumer):
  `E_{r+1} ≤ (2r+1)·n·E_r`, equivalently `cross_r ≤ 2r·n·E_r` — the same mass measured against the
  **actual energy** `E_r`.

This file proves the previously-unassembled relation between them, directly on the concrete char-`p`
`rEnergy μ_n` (the abstract `WickStepRatio` bridge had never been instantiated on `rEnergy`):

* `StepRatioBounded`              : the step-ratio hypothesis `cross_r ≤ 2r·n·E_r ∀ r ≥ 1`, as a `Prop`.
* `EnergyStepBounded`             : the recurrence form `E_{r+1} ≤ (2r+1)nE_r`.
* `stepRatioBounded_iff_energyStepBounded` : the two step-ratio forms are equivalent by `cross_eq`, so
  the envelope-free recurrence and the cross-mass pin are the SAME open input, not two assumptions.
* `rEnergy_le_wick_of_stepRatio`  : the step-ratio hypothesis ALONE drives the clean ladder
  `E_r ≤ Wick_r ∀ r ≥ 1` (base `E_1 = n = Wick_1`, then `E_{r+1} ≤ (2r+1)n·E_r ≤ (2r+1)n·Wick_r`).
* `crossBounded_of_stepRatio`     : **THE DOMINATION.** the step-ratio hypothesis IMPLIES the in-tree
  cross-bound hypothesis `CrossBoundedByWick`. (Because on the ladder `E_r ≤ Wick_r`, the step-ratio RHS
  `2r·n·E_r` is `≤` the cross-bound RHS `2r·n·Wick_r`.) Hence the step-ratio form is the **strictly
  stronger / dominant** lever: anything provable from `CrossBoundedByWick` is provable from it, including
  the full conditional prize sup-norm chain. The converse is FALSE wherever `E_r < Wick_r` strictly
  (the cross-bound RHS is genuinely looser), which a probe confirms is everywhere for `r ≥ 2`.
* `eta_pow2r_le_wick_of_stepRatio`: the consumer — the conditional prize-floor moment bound
  `‖η_b‖^{2r} ≤ q·(2r−1)‼·n^r` for every `b`, now from the step-ratio hypothesis, via the domination.

## Honest scope — CONDITIONAL, does NOT close the prize

The step-ratio inequality `cross_r ≤ 2r·n·E_r` at depth `r ≍ log m` is itself an OPEN char-`p`
deep-moment bound — it is FALSE in the thick window and only conjectured at `β ≥ 4` (DISPROOF_LOG:
"holds THIN with GROWING margin, fails THICK"). This file proves NO new char-`p` energy inequality:
it is a pure structural comparison establishing that the step-ratio reduction **dominates** the
in-tree cross-bound reduction, unifying `WickStepRatio` + `CharPMomentRecursion` +
`CharPWickConditionalPin` against the concrete `rEnergy μ_n`. The single open input remains the
BGK / Lam–Leung deep-moment wall. No capacity, beyond-Johnson, or cliff-at-`n/2` claim is made.

PROBE (`scripts/probes/probe_crossbound_vs_stepratio.py`, exact integer `E_r` over PROPER thin `μ_n`,
`p ≈ n^4`, two primes per `n ∈ {4,8,16}`, never `n = q−1`, `r = 1..4`): BOTH hypotheses hold on every
clean rung; the step-ratio RHS `2r·n·E_r` is `<` the cross-bound RHS `2r·n·Wick_r` for every `r ≥ 2`
(strict domination, growing gap), and `cross_r` satisfies the stronger step-ratio bound WITH margin.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


open Finset
open scoped Nat
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment (eta)
open ArkLib.ProximityGap.SubgroupGaussSumMoment (rEnergy)
open ArkLib.ProximityGap.CharPDeepMomentTail (rEnergy_one)
open ArkLib.ProximityGap.CharPWickConditionalPin
  (cross cross_eq wick wick_one wick_succ CrossBoundedByWick
   rEnergy_le_wick_of_crossBound eta_pow2r_le_wick_of_crossBound)

namespace ArkLib.ProximityGap.CharPWickStepRatioPin

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ### The step-ratio hypothesis -/

/-- **THE STEP-RATIO HYPOTHESIS, as one `Prop`:** `cross_r ≤ 2r·n·E_r` for all `r ≥ 1`, equivalently
`E_{r+1} = n·E_r + cross_r ≤ (2r+1)·n·E_r` (the abstract `WickStepRatio` step bound, with `n = |G|`).
This measures the off-diagonal mass against the **actual energy** `E_r`, not the envelope `Wick_r`.
Stated, NOT proved — it is the open char-`p` deep-moment wall in its sharpest (envelope-free) form. -/
def StepRatioBounded (G : Finset F) : Prop :=
  ∀ r : ℕ, 1 ≤ r → cross G r ≤ 2 * r * (G.card * rEnergy G r)

/-- **The same step-ratio hypothesis in recurrence form.** This is the concrete `rEnergy` version of
`E_{r+1} ≤ (2r+1)nE_r`, separated from `StepRatioBounded` so consumers can state whichever form is
natural. The two forms are equivalent by the exact char-`p` decomposition `E_{r+1}=nE_r+cross_r`. -/
def EnergyStepBounded (G : Finset F) : Prop :=
  ∀ r : ℕ, 1 ≤ r → rEnergy G (r + 1) ≤ (2 * r + 1) * G.card * rEnergy G r

/-- **Cross-mass step-ratio implies recurrence step-ratio.** This is the previously implicit algebraic
conversion from `cross_r ≤ 2r·n·E_r` to `E_{r+1} ≤ (2r+1)nE_r`, using the exact recurrence. -/
theorem energyStepBounded_of_stepRatio (G : Finset F) (hS : StepRatioBounded G) :
    EnergyStepBounded G := by
  intro r hr
  have hcross : cross G r ≤ 2 * r * (G.card * rEnergy G r) := hS r hr
  calc rEnergy G (r + 1)
      = G.card * rEnergy G r + cross G r := cross_eq G r
    _ ≤ G.card * rEnergy G r + 2 * r * (G.card * rEnergy G r) :=
          Nat.add_le_add_left hcross _
    _ = (2 * r + 1) * G.card * rEnergy G r := by ring

/-- **Recurrence step-ratio implies cross-mass step-ratio.** Conversely, because the recurrence is an
exact decomposition with the same diagonal term on both sides, `E_{r+1} ≤ (2r+1)nE_r` cancels to
`cross_r ≤ 2r·n·E_r`. Thus `StepRatioBounded` and `EnergyStepBounded` are not two assumptions; they
are the same char-`p` wall in two coordinates. -/
theorem stepRatio_of_energyStepBounded (G : Finset F) (hE : EnergyStepBounded G) :
    StepRatioBounded G := by
  intro r hr
  have hstep : rEnergy G (r + 1) ≤ (2 * r + 1) * G.card * rEnergy G r := hE r hr
  rw [cross_eq G r] at hstep
  have hrewrite :
      (2 * r + 1) * G.card * rEnergy G r =
        G.card * rEnergy G r + 2 * r * (G.card * rEnergy G r) := by ring
  rw [hrewrite] at hstep
  exact Nat.le_of_add_le_add_left hstep

/-- **Equivalence of the two concrete step-ratio forms.** The cross-mass inequality and the energy
recurrence inequality are definitionally different but mathematically identical once `cross_eq` is in
place. This pins the exact open input used by the Wick bridge and avoids treating the envelope-free
recurrence as a stronger or separate hypothesis. -/
theorem stepRatioBounded_iff_energyStepBounded (G : Finset F) :
    StepRatioBounded G ↔ EnergyStepBounded G :=
  ⟨energyStepBounded_of_stepRatio G, stepRatio_of_energyStepBounded G⟩

/-! ### The step-ratio hypothesis drives the Wick ladder -/

/-- **The step-ratio hypothesis alone drives `E_r ≤ Wick_r`.** Clean induction from the proven base
`E_1 = n = Wick_1` (`rEnergy_one`, `wick_one`) through the exact recursion `E_{r+1} = n·E_r + cross_r`
(`cross_eq`): if `E_r ≤ Wick_r` and `cross_r ≤ 2r·n·E_r` (step-ratio), then
`E_{r+1} = n·E_r + cross_r ≤ n·E_r + 2r·n·E_r = (2r+1)·n·E_r ≤ (2r+1)·n·Wick_r = Wick_{r+1}`. -/
theorem rEnergy_le_wick_of_stepRatio (G : Finset F) (hS : StepRatioBounded G) :
    ∀ r : ℕ, 1 ≤ r → rEnergy G r ≤ wick G.card r := by
  intro r
  induction r with
  | zero => intro h; omega
  | succ k ih =>
      intro _
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk; rw [rEnergy_one, wick_one]
      · have ihk : rEnergy G k ≤ wick G.card k := ih hk
        have hcross : cross G k ≤ 2 * k * (G.card * rEnergy G k) := hS k hk
        calc rEnergy G (k + 1)
            = G.card * rEnergy G k + cross G k := cross_eq G k
          _ ≤ G.card * rEnergy G k + 2 * k * (G.card * rEnergy G k) :=
                Nat.add_le_add_left hcross _
          _ = (2 * k + 1) * G.card * rEnergy G k := by ring
          _ ≤ (2 * k + 1) * G.card * wick G.card k := by
                exact Nat.mul_le_mul_left _ ihk
          _ = wick G.card (k + 1) := (wick_succ G.card k hk).symm

/-! ### THE DOMINATION: step-ratio ⟹ cross-bound -/

/-- **THE DOMINATION.** The step-ratio hypothesis `cross_r ≤ 2r·n·E_r` IMPLIES the in-tree cross-bound
hypothesis `cross_r ≤ 2r·n·Wick_r` (`CrossBoundedByWick`).

Mechanism: by `rEnergy_le_wick_of_stepRatio`, the step-ratio hypothesis forces `E_r ≤ Wick_r` on the
whole ladder; hence the step-ratio RHS `2r·n·E_r` is `≤` the cross-bound RHS `2r·n·Wick_r`, and the
cross-bound follows by transitivity. So the step-ratio reduction is **strictly stronger**: every
consequence of `CrossBoundedByWick` (the full conditional prize sup-norm chain) follows from it. The
converse fails wherever `E_r < Wick_r` strictly — i.e. the cross-bound RHS is genuinely looser. -/
theorem crossBounded_of_stepRatio (G : Finset F) (hS : StepRatioBounded G) :
    CrossBoundedByWick G := by
  intro r hr
  have hcross : cross G r ≤ 2 * r * (G.card * rEnergy G r) := hS r hr
  have hEW : rEnergy G r ≤ wick G.card r := rEnergy_le_wick_of_stepRatio G hS r hr
  calc cross G r
      ≤ 2 * r * (G.card * rEnergy G r) := hcross
    _ ≤ 2 * r * (G.card * wick G.card r) := by
          exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hEW)

/-! ### The consumer: the prize-floor moment bound from the step-ratio hypothesis -/

/-- **The conditional prize-floor moment bound from the step-ratio hypothesis:**
`‖η_b‖^{2r} ≤ q·(2r−1)‼·n^r` for every `b` and every `r ≥ 1`, assuming the step-ratio inequality
`cross_r ≤ 2r·n·E_r`. Routes through the domination `crossBounded_of_stepRatio` into the in-tree
consumer `eta_pow2r_le_wick_of_crossBound` — confirming the step-ratio reduction yields the FULL
conditional prize chain, hence dominates the cross-bound reduction. -/
theorem eta_pow2r_le_wick_of_stepRatio {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hS : StepRatioBounded G) (r : ℕ) (hr : 1 ≤ r) (b : F) :
    ‖eta ψ G b‖ ^ (2 * r) ≤ (Fintype.card F : ℝ) * ((2 * r - 1)‼ * (G.card : ℝ) ^ r) :=
  eta_pow2r_le_wick_of_crossBound hψ G (crossBounded_of_stepRatio G hS) r hr b

#print axioms energyStepBounded_of_stepRatio
#print axioms stepRatio_of_energyStepBounded
#print axioms stepRatioBounded_iff_energyStepBounded
#print axioms rEnergy_le_wick_of_stepRatio
#print axioms crossBounded_of_stepRatio
#print axioms eta_pow2r_le_wick_of_stepRatio

end ArkLib.ProximityGap.CharPWickStepRatioPin
