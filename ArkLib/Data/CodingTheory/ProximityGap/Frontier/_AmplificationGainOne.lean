/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Amplification-gain-one: the QUE / Iwaniec–Sarnak route is dead on flat spectra (#407, #444)

**NEGATIVE / guardrail brick (an honest no-go, NOT a closure).** This file documents *why* the
QUE / Iwaniec–Sarnak Hecke-amplification route to the proximity prize is structurally vacuous for
the Gauss-period family `η`: a **flat spectrum** makes the amplification gain identically `1`, so
the method can only ever certify the Parseval / RMS (`L²`) value and **never** the `L^∞` prize
factor. The prize's `√(log)` `L^∞` excess is untouched — it remains the open BGK core (faces 3↔4
of the §3.5 open-core map). This came out of an exotic-math sweep (workflow), as a *documented
negative result*.

## The method, and the no-go

The Iwaniec–Sarnak amplification trick bounds a sup `|f|` by inserting an "amplifier" `a` and
controlling the amplifier-weighted spectral energy

  `∑_χ ‖f̂(χ)‖² ‖â(χ)‖²`,

choosing `a` so that the diagonal `χ` (the one whose eigenvalue you want to detect) is enlarged
relative to the rest. The trick gains exactly when the spectrum of `f` is **uneven** — there is a
distinguished large coefficient to amplify against the small ones.

**The death.** Suppose `f` has a *flat* spectrum: all nonzero Fourier / character coefficients have
**equal modulus** `‖f̂(χ)‖ = c` on a support `S`. Then for **every** amplifier `a`,

  `∑_{χ ∈ S} ‖f̂(χ)‖² ‖â(χ)‖² = c² · ∑_{χ ∈ S} ‖â(χ)‖²`.

The amplifier-weighted energy factors as `c²` times the *restricted amplifier energy* — it depends
on `a` **only through its norm on `S`**, never through its *shape*. So no choice of amplifier can
tilt the weighted energy: the amplification **gain** (amplified bound ÷ unamplified bound) is the
constant `c²/c² = 1`. Amplification certifies only the Parseval value `c² ‖a‖_S²` and never beats
it. This is the formal death of the amplification method for a flat-spectrum object.

## The prize family `η` has a flat spectrum

The prize Gauss-period family `η_b = ∑_{y ∈ μ_n} ψ(b y)` is *exactly* flat in the relevant sense:
its "Hecke eigenvalues" are the Gauss sums `τ(χ)/m`, and `‖τ(χ)‖ = √q` **EXACT** for every nonzero
multiplicative character `χ` (`Mathlib.NumberTheory.GaussSum`: `gaussSum_mul_gaussSum_eq_card`).
Hence `‖f̂(χ)‖ = √q / m` is **constant** across nonzero characters, i.e. `c = √q / m` here; cf. the
in-tree worst-case anchor `SubgroupGaussSumWorstCase` (`‖η_b‖ ≤ √q` every `b`) and the second-moment
Parseval floor `GaussPeriodParsevalFloor` (`∑_b ‖η_b‖² = q·|G|`, the average sits at `√|G|`). With a
flat spectrum, `amplification_gain_one` below applies verbatim: amplification yields the RMS scale
`√|G|`, never the `L^∞` `√(|G| log(1/ε*))` the prize needs. That `L^∞` excess is the open BGK /
Paley-graph sub-`√q` cancellation, not addressable by amplification.

We keep the abstract flat-spectrum identity as the reusable engine (it needs only `Finset` sums and
`RCLike` / complex norms) and cite the in-tree Gauss-period flat spectrum rather than forcing a
fragile instantiation against the heavy character-sum substrate.

Issues #407, #444 (exotic-math sweep).
-/

namespace ProximityGap.Frontier.AmplificationGainOne

open Finset

variable {ι : Type*} {𝕜 : Type*} [RCLike 𝕜]

/--
**The flat-spectrum amplification identity (the genuine engine).**

If the coefficient vector `fc` has *flat modulus* `c` on a support `S`
(`∀ χ ∈ S, ‖fc χ‖ = c`), then for **every** amplifier `ac` the amplifier-weighted spectral energy
factors:

  `∑_{χ ∈ S} ‖fc χ‖² ‖ac χ‖² = c² · ∑_{χ ∈ S} ‖ac χ‖²`.

The weighted energy depends on `ac` **only through its restricted energy** `∑_{χ ∈ S} ‖ac χ‖²`,
never through the *shape* of `ac`. Hence no choice of amplifier improves the bound — the
amplification gain is identically `1`. This is the formal no-go for the QUE / Iwaniec–Sarnak route
on a flat-spectrum object. -/
theorem flat_spectrum_weighted_energy
    (S : Finset ι) (fc ac : ι → 𝕜) (c : ℝ)
    (hflat : ∀ χ ∈ S, ‖fc χ‖ = c) :
    ∑ χ ∈ S, ‖fc χ‖ ^ 2 * ‖ac χ‖ ^ 2 = c ^ 2 * ∑ χ ∈ S, ‖ac χ‖ ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro χ hχ
  rw [hflat χ hχ]

/--
**Amplification gain is identically one (ratio form).**

For a flat-spectrum object (`‖fc χ‖ = c` on `S`) and *any* amplifier `ac` with **positive**
restricted energy `A = ∑_{χ ∈ S} ‖ac χ‖² > 0`, the per-energy amplifier-weighted spectral energy is
the constant `c²`, independent of the amplifier:

  `(∑_{χ ∈ S} ‖fc χ‖² ‖ac χ‖²) / A = c²`.

So every amplifier returns the same Parseval / RMS value `c²` (per unit amplifier energy) — the
amplification "gain" is `1`. The method cannot certify anything beyond the flat coefficient modulus
`c`; in the prize instantiation `c = √q / m` gives the RMS scale `√|G|`, never the `L^∞` prize. -/
theorem amplification_gain_one
    (S : Finset ι) (fc ac : ι → 𝕜) (c : ℝ)
    (hflat : ∀ χ ∈ S, ‖fc χ‖ = c)
    (hA : (0 : ℝ) < ∑ χ ∈ S, ‖ac χ‖ ^ 2) :
    (∑ χ ∈ S, ‖fc χ‖ ^ 2 * ‖ac χ‖ ^ 2) / (∑ χ ∈ S, ‖ac χ‖ ^ 2) = c ^ 2 := by
  rw [flat_spectrum_weighted_energy S fc ac c hflat]
  exact mul_div_cancel_right₀ (c ^ 2) (ne_of_gt hA)

/--
**Amplifier-independence (the no-go, sharpest form).**

For a flat-spectrum object, *any two* amplifiers `a₁`, `a₂` with **equal restricted energy**
(`∑_{χ ∈ S} ‖a₁ χ‖² = ∑_{χ ∈ S} ‖a₂ χ‖²`) produce the **same** amplifier-weighted spectral energy.

This is the operational content of "gain = 1": you cannot reshape the amplifier within a fixed
energy budget to enlarge the weighted energy — every shape is equivalent to every other. The
Iwaniec–Sarnak choice of amplifier is therefore vacuous on a flat spectrum. -/
theorem weighted_energy_amplifier_indep
    (S : Finset ι) (fc a₁ a₂ : ι → 𝕜) (c : ℝ)
    (hflat : ∀ χ ∈ S, ‖fc χ‖ = c)
    (henergy : ∑ χ ∈ S, ‖a₁ χ‖ ^ 2 = ∑ χ ∈ S, ‖a₂ χ‖ ^ 2) :
    ∑ χ ∈ S, ‖fc χ‖ ^ 2 * ‖a₁ χ‖ ^ 2 = ∑ χ ∈ S, ‖fc χ‖ ^ 2 * ‖a₂ χ‖ ^ 2 := by
  rw [flat_spectrum_weighted_energy S fc a₁ c hflat,
      flat_spectrum_weighted_energy S fc a₂ c hflat, henergy]

/--
**The Parseval ceiling the method cannot pierce.**

For a flat-spectrum object, the amplifier-weighted spectral energy never exceeds `c²` times the
*total* (unrestricted) amplifier energy `∑_{χ ∈ S} ‖ac χ‖²` — it equals it. There is no slack: the
amplification bound is pinned to the Parseval value `c² ‖a‖_S²`, so the certified sup bound is the
RMS value and nothing finer. The `L^∞` excess (the prize `√log` factor) lies strictly above this
ceiling and is invisible to amplification. -/
theorem weighted_energy_le_parseval_ceiling
    (S : Finset ι) (fc ac : ι → 𝕜) (c : ℝ)
    (hflat : ∀ χ ∈ S, ‖fc χ‖ = c) :
    ∑ χ ∈ S, ‖fc χ‖ ^ 2 * ‖ac χ‖ ^ 2 ≤ c ^ 2 * ∑ χ ∈ S, ‖ac χ‖ ^ 2 :=
  le_of_eq (flat_spectrum_weighted_energy S fc ac c hflat)

#print axioms flat_spectrum_weighted_energy
#print axioms amplification_gain_one
#print axioms weighted_energy_amplifier_indep
#print axioms weighted_energy_le_parseval_ceiling

end ProximityGap.Frontier.AmplificationGainOne
