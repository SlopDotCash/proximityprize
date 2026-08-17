/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.WorstPeriodMomentRatioLower

/-!
# Floor lower bound ⟸ energy-ratio growth: the wired reduction (#444)

Companion to `Frontier/FloorResonanceLowerBound.lean` (the abstract resonance engine). This file
WIRES the engine to the concrete worst Gauss period through the in-tree, axiom-clean reverse-Markov
bound `WorstPeriodMomentRatioLower.exists_period_sq_ge_moment_ratio`:

> `∃ b ≠ 0,  q·E_r − |G|^{2r}  ≤  ‖η_b‖²·(q·E_{r−1} − |G|^{2(r−1)})`.

We name the ONE open input as a `Prop` and prove that it implies the floor lower bound
`M(n)² ≥ T` (with `T = c·n·log m` at the optimizing depth `r ≈ log m`):

* **`EnergyRatioGrowth ψ G r T`** (the named obligation): at moment depth `r`, the consecutive
  energy ratio is at least `T`, in cross-multiplied positive form
  `q·E_r − |G|^{2r} ≥ T·(q·E_{r−1} − |G|^{2(r−1)})` with `q·E_{r−1} − |G|^{2(r−1)} > 0`.
* **`worst_period_sq_ge_of_energyRatioGrowth`** (PROVEN): `EnergyRatioGrowth ψ G r T` ⟹
  `∃ b ≠ 0, T ≤ ‖η_b‖²`. The floor lower bound, modulo the named energy-ratio growth.

**Honest verdict (reduces-to-wall).** The floor `M(n) ≥ c√(n log m)` is numerically real
(`scripts/probes/probe_floor_resonance.py`: `M²/n ~ (1.1–1.95)·log m`, non-decaying band), and the
resonance method supplies the engine + this reverse-Markov lower bound with NO new open input *per
depth*. But reaching the target `T = c·n·log m` forces depth `r ≈ log m`
(`probe_floor_resonance_construction.py`: the depth `r⋆` to reach `0.9·max` grows like `log m`), so
`EnergyRatioGrowth` at `r ≈ log m` is a LOWER bound on `E_{log m}(μ_n)/E_{log m −1}(μ_n)` — the same
Bourgain–Shkredov additive-energy quantity (wall W4) that gates the UPPER bound. The structure-blind
(GCD / Bondarenko–Seip) resonator provably certifies only the mean
(`FloorResonanceLowerBound.structureBlind_resonator_le_mean`; probe `probe_floor_resonance_gcd.py`
measures `≈ n`), so it gives NO shortcut. The floor lower bound and the moment-method upper bound
are DUAL on `E_{log m}` — the resonance method does not breach the wall, it re-derives it from
below.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`; no `sorry`).
-/

set_option linter.style.longLine false


namespace ArkLib.ProximityGap.FloorResonanceBridge

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The single open input: energy-ratio growth at depth `r`.** The consecutive additive-energy
ratio at moment depth `r` is at least the target `T`, in cross-multiplied positive form. At the
optimizing depth `r ≈ log m` and `T ≈ c·n·log m` this is a LOWER bound on `E_{log m}(μ_n)` — the
open Bourgain–Shkredov additive-energy quantity (wall W4). Stated as a `Prop` so the reduction
below is an honest implication, never a hidden closure. -/
def EnergyRatioGrowth (ψ : AddChar F ℂ) (G : Finset F) (r : ℕ) (T : ℝ) : Prop :=
  0 < (Fintype.card F : ℝ) * rEnergy G (r - 1) - (G.card : ℝ) ^ (2 * (r - 1)) ∧
    T * ((Fintype.card F : ℝ) * rEnergy G (r - 1) - (G.card : ℝ) ^ (2 * (r - 1)))
      ≤ (Fintype.card F : ℝ) * rEnergy G r - (G.card : ℝ) ^ (2 * r)

/-- **Floor lower bound ⟸ energy-ratio growth (the wired reduction).** If the named energy-ratio
growth holds at depth `r`, then some nontrivial frequency has `‖η_b‖² ≥ T`. This is the resonance
floor lower bound, with the ONLY open input the energy-ratio growth (= the wall at `r ≈ log m`).
Proven by chaining the in-tree reverse-Markov bound `exists_period_sq_ge_moment_ratio` with the
positivity of the `(r−1)`-th moment defect: from
`q·E_r − n^{2r} ≤ ‖η_b‖²·(q·E_{r−1} − n^{2(r−1)})` and
`T·(q·E_{r−1} − n^{2(r−1)}) ≤ q·E_r − n^{2r}` with `q·E_{r−1} − n^{2(r−1)} > 0`, cancel the positive
factor to get `T ≤ ‖η_b‖²`. -/
theorem worst_period_sq_ge_of_energyRatioGrowth {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (r : ℕ) (hr : 1 ≤ r) (T : ℝ) (hgrow : EnergyRatioGrowth ψ G r T) :
    ∃ b : F, b ≠ 0 ∧ T ≤ ‖eta ψ G b‖ ^ 2 := by
  obtain ⟨hposdef, hTle⟩ := hgrow
  obtain ⟨b, hb, hbound⟩ := exists_period_sq_ge_moment_ratio hψ G r hr
  refine ⟨b, hb, ?_⟩
  -- hbound : q·E_r − n^{2r} ≤ ‖η_b‖²·(q·E_{r−1} − n^{2(r−1)})
  -- hTle   : T·(q·E_{r−1} − n^{2(r−1)}) ≤ q·E_r − n^{2r}
  -- so T·D ≤ ‖η_b‖²·D with D > 0 ⟹ T ≤ ‖η_b‖².
  set D : ℝ := (Fintype.card F : ℝ) * rEnergy G (r - 1) - (G.card : ℝ) ^ (2 * (r - 1)) with hD
  have hchain : T * D ≤ ‖eta ψ G b‖ ^ 2 * D := le_trans hTle hbound
  exact le_of_mul_le_mul_right hchain hposdef

/-- **The reduction, in contrapositive (no floor ⟹ no energy growth).** If NO nontrivial period
reaches `T` (i.e. the floor `M² ≥ T` fails), then the energy-ratio growth fails at every depth `r`.
This is the precise sense in which the floor lower bound IS the energy wall: they stand or fall
together. -/
theorem energyRatioGrowth_fails_of_no_floor {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (r : ℕ) (hr : 1 ≤ r) (T : ℝ)
    (hnofloor : ∀ b : F, b ≠ 0 → ‖eta ψ G b‖ ^ 2 < T) :
    ¬ EnergyRatioGrowth ψ G r T := by
  intro hgrow
  obtain ⟨b, hb, hge⟩ := worst_period_sq_ge_of_energyRatioGrowth hψ G r hr T hgrow
  exact (not_lt.mpr hge) (hnofloor b hb)

end ArkLib.ProximityGap.FloorResonanceBridge

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.FloorResonanceBridge.worst_period_sq_ge_of_energyRatioGrowth
#print axioms
  ArkLib.ProximityGap.FloorResonanceBridge.energyRatioGrowth_fails_of_no_floor
