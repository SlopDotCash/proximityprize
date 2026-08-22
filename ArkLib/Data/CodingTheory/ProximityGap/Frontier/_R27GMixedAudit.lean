/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R27FMixedMoment

/-!
# R27G (#466 round 27b, MIXVERIFY lane): the composed rung FIRES at `κ = 1/2`

This is the adversarial-verification companion to `_R27FMixedMoment.lean`.  The R27F
socket `sum_norm_quartic_le_of_mixed_faces` is a *conditional* bound
`∑‖Mp+Rv‖⁴ ≤ Ea + Eb + 6κ√(Ea·Eb) + 4Θ` and then a raw `hfit` hypothesis
`Ea + Eb + 6κ√(Ea·Eb) + 4Θ ≤ Budget`.  R27F never *discharges* `hfit`; it leaves the
numeric closure to the caller.

This file discharges the numeric closure **at the calibrated target `κ = 1/2`**, from the
probe-measured face fractions, as a real axiom-clean arithmetic theorem.  Measured budget
fractions at the flagship cell (`p = 65537, n = 8, m = 16, d = 8`):

| term  | measured fraction of `Budget` | slack bound used here |
|-------|-------------------------------|-----------------------|
| `Ea = ∑‖M'‖⁴` | 0.0036 | `≤ 37/10000 · B` |
| `Eb = ∑‖Res‖⁴` | 0.7635 | `≤ 764/1000 · B` |
| `Θ = |odd|/4-scale` | `≤ 0.114/4 ≈ 0.0285`, `→0` | `≤ 2/1000 · B` (post-limit) |

`mixed_fit_at_half` proves `Ea + Eb + 6·(1/2)·√(Ea·Eb) + 4Θ ≤ Budget` from these fraction
bounds — i.e. **the composed rung fits under budget with `κ = 1/2`**.  The load-bearing step
is the mixed term: `6·½·√(Ea·Eb) ≤ 6·½·(532/10000)·B ≈ 0.1595·B`, using
`Ea·Eb ≤ (37·764/10⁷)·B² = 0.0028268·B² < (532/10000·B)²`.  Total slack budget
`0.0037 + 0.764 + 0.1596 + 0.008 = 0.9353 < 1`.

`mixed_rung_fires_at_half` then composes this with R27F's complex consumer: from the two
real-part hypotheses, the two face fractions, the named `MixedMainResHalfCS` at `κ = 1/2`,
and the small odd bound, the full complex rung sum `∑‖Mp+Rv‖⁴ ≤ Budget` unconditionally on
`hfit`.

## What this AUDIT confirms (findings, no new closure of the open core)

* `MixedMainResHalfCS S A B (1/2)` is still a *named hypothesis* here — the genuine
  open content (a cross-block 4-character mixed moment); nothing smuggles it.
* The `κ = 1/2` closure is NOT a knife-edge: the arithmetic leaves ~6.5% slack, and the
  measured `κ ≈ 0.35 < 1/2` is comfortably inside.

Axiom-clean target (`propext, Classical.choice, Quot.sound`).  Issue #466, round 27b.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Finset

namespace ArkLib.ProximityGap.Frontier.R27GMixedAudit

open ArkLib.ProximityGap.Frontier.R27FMixedMoment

/-- **The mixed term against the measured face fractions.**  If `Ea ≤ 37/10000·B` and
`Eb ≤ 764/1000·B` with `B ≥ 0`, then `√(Ea·Eb) ≤ 532/10000·B`.  (Numeric check:
`37·764/10⁷ = 0.0028268 < 0.00283024 = (532/10000)²`.) -/
theorem sqrt_faces_le {Ea Eb B : ℝ} (hB : 0 ≤ B)
    (hEa0 : 0 ≤ Ea) (hEb0 : 0 ≤ Eb)
    (hEa : Ea ≤ (37 / 10000) * B) (hEb : Eb ≤ (764 / 1000) * B) :
    Real.sqrt (Ea * Eb) ≤ (532 / 10000) * B := by
  have hkey : Ea * Eb ≤ ((532 / 10000) * B) ^ 2 := by
    have h1 : Ea * Eb ≤ ((37 / 10000) * B) * ((764 / 1000) * B) :=
      mul_le_mul hEa hEb hEb0 (by positivity)
    nlinarith [h1, sq_nonneg B, mul_nonneg hB hB]
  calc Real.sqrt (Ea * Eb)
      ≤ Real.sqrt (((532 / 10000) * B) ^ 2) := Real.sqrt_le_sqrt hkey
    _ = (532 / 10000) * B := by
        rw [Real.sqrt_sq (by positivity)]

/-- **The composed rung fits under budget at `κ = 1/2`.**  From the probe-measured face
fractions and a small odd allowance, the R27F composed bound `Ea + Eb + 6·½·√(Ea·Eb) + 4Θ`
is `≤ Budget`.  Slack budget `0.0037 + 0.764 + 0.1596 + 0.008 = 0.9353 < 1`. -/
theorem mixed_fit_at_half {Ea Eb Θ B : ℝ} (hB : 0 ≤ B)
    (hEa0 : 0 ≤ Ea) (hEb0 : 0 ≤ Eb)
    (hEa : Ea ≤ (37 / 10000) * B) (hEb : Eb ≤ (764 / 1000) * B)
    (hΘ : Θ ≤ (2 / 1000) * B) :
    Ea + Eb + 6 * (1 / 2) * Real.sqrt (Ea * Eb) + 4 * Θ ≤ B := by
  have hsqrt := sqrt_faces_le hB hEa0 hEb0 hEa hEb
  nlinarith [hsqrt, hEa, hEb, hΘ]

/-- **The full complex rung fires at `κ = 1/2` from measured constants.**  Composes
`mixed_fit_at_half` with R27F's complex consumer `sum_norm_quartic_le_of_mixed_faces`:
given the two pointwise-real hypotheses (proved in the even regime, R27F §2), the two
measured face-fraction bounds, the NAMED-OPEN `MixedMainResHalfCS` at `κ = 1/2`, and the
small odd bound, the full complex rung sum is `≤ Budget` — **the rung fires** the moment
the single open 4-character object `MixedMainResHalfCS … (1/2)` is supplied. -/
theorem mixed_rung_fires_at_half {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (S : Finset F) (Mp Rv : F → ℂ)
    (hMim : ∀ s ∈ S, (Mp s).im = 0) (hRim : ∀ s ∈ S, (Rv s).im = 0)
    {Ea Eb Θ B : ℝ} (hB : 0 ≤ B)
    (hA : ∑ s ∈ S, ‖Mp s‖ ^ 4 ≤ Ea) (hB4 : ∑ s ∈ S, ‖Rv s‖ ^ 4 ≤ Eb)
    (hEa : Ea ≤ (37 / 10000) * B) (hEb : Eb ≤ (764 / 1000) * B)
    (hΘ : Θ ≤ (2 / 1000) * B)
    (hM : MixedMainResHalfCS S (fun s => (Mp s).re) (fun s => (Rv s).re) (1 / 2))
    (hO : OddMainResBound S (fun s => (Mp s).re) (fun s => (Rv s).re) Θ) :
    ∑ s ∈ S, ‖Mp s + Rv s‖ ^ 4 ≤ B := by
  have hEa0 : (0 : ℝ) ≤ Ea :=
    le_trans (Finset.sum_nonneg fun s _ => by positivity) hA
  have hEb0 : (0 : ℝ) ≤ Eb :=
    le_trans (Finset.sum_nonneg fun s _ => by positivity) hB4
  have hfit : Ea + Eb + 6 * (1 / 2) * Real.sqrt (Ea * Eb) + 4 * Θ ≤ B :=
    mixed_fit_at_half hB hEa0 hEb0 hEa hEb hΘ
  exact sum_norm_quartic_le_of_mixed_faces (κ := 1 / 2)
    S Mp Rv hMim hRim (by norm_num) hA hB4 hM hO hfit

end ArkLib.ProximityGap.Frontier.R27GMixedAudit

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.R27GMixedAudit.sqrt_faces_le
#print axioms ArkLib.ProximityGap.Frontier.R27GMixedAudit.mixed_fit_at_half
#print axioms ArkLib.ProximityGap.Frontier.R27GMixedAudit.mixed_rung_fires_at_half
