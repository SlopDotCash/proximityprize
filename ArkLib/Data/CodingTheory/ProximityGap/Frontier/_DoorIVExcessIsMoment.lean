/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# Door-(iv) Lane-1 constraint: the cocycle dispersion excess is a MOMENT (additive energy), #444

Follow-up to `_DoorIVCocycleNoRandomEdge.lean`. The dispersion-magnitude probe found the real
Jacobi-cocycle sup exceeds a random-iid-phase surrogate (`real/iid = 1.15..1.44`). The follow-up probe
`scripts/probes/probe_dooriv_cocycle_excess_structure.py` (+ `.NOTE`) measured the SOURCE of that excess
and verified, exactly, that it is an **additive-energy** excess of `μ_n`:

> The period field's normalized 4th moment `m4 = E‖η_b‖⁴ / (E‖η_b‖²)²` equals `E₄(μ_n)/n²`, where
> `E₄(μ_n) = #{(a,b,c,d) ∈ μ_n⁴ : a+b = c+d}` is the additive energy (since `Σ_b ‖η_b‖⁴ = p·E₄`).
> Measured `m4_real ≈ 2.81..3.02` (vs the iid Rayleigh value `2.0`), and at `n=16,p=65617`,
> `E₄ = 720`, `E₄/n² = 2.812` — IDENTICAL to `m4_real`. The `+15..44%` sup excess is exactly the
> additive energy of the multiplicative subgroup above the random-set baseline.

By HARD RULE 5 / #444 §6, additive-moment / energy bounds are PROVEN non-proving (door (i) = BGK,
capped at Johnson, saturates at structured primes). So the cocycle's residual structure is a **moment**,
not a non-moment lever: the dispersion excess re-enters through the dead door (i).

## What is proved here (axiom-clean order-theoretic packaging of the identity-level obstruction)

The empirical content is "the dispersion advantage `δ` is sourced in (bounded by) the additive-energy
excess `Δ`". We package the consequence cleanly over arbitrary reals (so the file proves no unverified
arithmetic): once a candidate advantage is dominated by the moment excess, it cannot exceed any bound
the moment already gives, hence cannot be a non-moment lever.

* `MomentSourced δ Δ` : the advantage `δ` is nonneg and `≤` the additive-energy excess `Δ` (the
  measured/identity fact, taken as a hypothesis carrier — NOT an axiom).
* `advantage_le_moment_excess` : `δ ≤ Δ` (the advantage never beats the moment excess).
* `advantage_within_moment_bound` : if the moment excess obeys a ceiling `Δ ≤ B` (e.g. the door-(i)
  Johnson/BGK cap), the advantage obeys the SAME ceiling `δ ≤ B`. So the advantage inherits the moment
  door's limitations — it is capped by exactly the proven-dead bound.
* `no_advantage_beyond_moment` : there is no advantage strictly past the moment ceiling; if `B < δ`
  with `Δ ≤ B`, contradiction. A non-moment lever would require `δ > Δ`, which `MomentSourced` forbids.
* `moment_sourced_iff_le` : the falsifiable iff — "advantage is moment-sourced" ⟺ `0 ≤ δ ∧ δ ≤ Δ`.
  A future measurement finding `δ > Δ` (a genuine non-moment excess) would break the hypothesis and
  reopen the lever. It has not: across `n=16..128` the 4th moment tracks `E₄/n²` to the measured digits.

VERDICT: a door-(iv) certificate that draws its dispersion advantage from the period 4th moment cannot
escape door (i): it is bounded by the additive-energy excess, which is moment-capped at Johnson/BGK. No
CORE, cancellation, completion, moment-saving, anti-concentration, or capacity claim — a refuted-lever
constraint lemma (Lane 1 → Lane 3), confirming the no-fifth-door tetrachotomy with a kernel statement.

Probe: `scripts/probes/probe_dooriv_cocycle_excess_structure.py` (+ `.NOTE`). Issue #444.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.DoorIVExcessIsMoment

/-- The advantage `δ` (the cocycle dispersion excess over random phases) is **moment-sourced**: it is
nonnegative and bounded by the additive-energy excess `Δ` of the period 4th moment. This is the measured
/ identity fact (`Σ_b ‖η_b‖⁴ = p·E₄`), carried as a hypothesis — NOT an axiom; all theorems are
universally quantified over reals satisfying it. -/
def MomentSourced (δ Δ : ℝ) : Prop := 0 ≤ δ ∧ δ ≤ Δ

/-- The dispersion advantage never beats the additive-energy (moment) excess. -/
theorem advantage_le_moment_excess {δ Δ : ℝ} (h : MomentSourced δ Δ) : δ ≤ Δ := h.2

/-- The advantage is nonnegative (sanity: the real sup is at least the surrogate sup). -/
theorem advantage_nonneg {δ Δ : ℝ} (h : MomentSourced δ Δ) : 0 ≤ δ := h.1

/-- **The advantage inherits the moment door's ceiling.** If the additive-energy excess obeys a bound
`Δ ≤ B` (the door-(i) Johnson/BGK cap), then the dispersion advantage obeys the SAME bound `δ ≤ B`.
A moment-sourced advantage cannot exceed what the proven-dead moment door already permits. -/
theorem advantage_within_moment_bound {δ Δ B : ℝ} (h : MomentSourced δ Δ) (hB : Δ ≤ B) : δ ≤ B :=
  le_trans h.2 hB

/-- **No advantage beyond the moment ceiling.** If the additive-energy excess is capped at `B`
(`Δ ≤ B`), there is no advantage strictly above `B`: `¬ B < δ`. A genuine non-moment lever would need
`δ` to escape the moment excess, which `MomentSourced` forbids. -/
theorem no_advantage_beyond_moment {δ Δ B : ℝ} (h : MomentSourced δ Δ) (hB : Δ ≤ B) : ¬ B < δ := by
  have hδB : δ ≤ B := advantage_within_moment_bound h hB
  exact not_lt.mpr hδB

/-- A non-moment lever (advantage strictly past the additive-energy excess) is impossible under the
measured regime: `¬ Δ < δ`. -/
theorem no_nonmoment_lever {δ Δ : ℝ} (h : MomentSourced δ Δ) : ¬ Δ < δ :=
  not_lt.mpr h.2

/-- Falsifiable iff: "the advantage is moment-sourced" is exactly `0 ≤ δ ∧ δ ≤ Δ`. A future probe
finding `δ > Δ` would break this hypothesis and reopen the non-moment lever. -/
theorem moment_sourced_iff_le {δ Δ : ℝ} :
    MomentSourced δ Δ ↔ (0 ≤ δ ∧ δ ≤ Δ) := Iff.rfl

end ArkLib.ProximityGap.Frontier.DoorIVExcessIsMoment

-- Axiom audit: all theorems must be ⊆ {propext, Classical.choice, Quot.sound}
section AxiomAudit
open ArkLib.ProximityGap.Frontier.DoorIVExcessIsMoment
#print axioms advantage_le_moment_excess
#print axioms advantage_nonneg
#print axioms advantage_within_moment_bound
#print axioms no_advantage_beyond_moment
#print axioms no_nonmoment_lever
#print axioms moment_sourced_iff_le
end AxiomAudit
