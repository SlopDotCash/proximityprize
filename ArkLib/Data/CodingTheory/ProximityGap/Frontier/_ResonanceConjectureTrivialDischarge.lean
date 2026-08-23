/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ResonanceMomentUnconditionalCeiling

/-!
# General-`r` conditional discharge of the Resonance Conjecture from the trivial ceiling (#407 / #444)

`_ResonanceMomentRTwoBounds` proves the conditional discharge ONLY at `r = 2`
(`resonanceConjecture_two_of_trivCeil_le`): if the trivial ceiling `m·(m−1)²` fits under the
conjecture target `(2 m log m)²`, then `ResonanceConjecture u 2` holds for unit phases.

With the UNCONDITIONAL `∀r` trivial ceiling `T r ≤ m·(m−1)^{2(r−1)}`
(`resonanceMoment_le_unconditional`) now available, that discharge generalizes to EVERY `r`:

> **`m·(m−1)^{2(r−1)} ≤ (2 m log m)^r ⟹ ResonanceConjecture u r`** (unit phases)
> (`resonanceConjecture_of_trivCeil_le`).

i.e. WHEREVER the trivial (triangle/`L¹`) ceiling already sits under the conjecture target, the
Resonance Conjecture is FREE — no `√`-cancellation needed. The open prize content is therefore
EXACTLY the complementary regime where the trivial ceiling OVERSHOOTS the target. This is the
general-`r` form of the door-(i)-style "`L¹`/triangle is insufficient only asymptotically" constraint:
the trivial ceiling overshoots by `~ (m−1)^{2(r−1)} / (2 log m)^r`, which → ∞ for `r ≍ log m`, so the
triangle route reaches the conjecture only off the prize depth; the prize lives precisely where the
off-diagonal `√`-cancellation must beat the trivial bound.

CERTAIN conditional implication (a transitivity through the proven unconditional ceiling), NOT a
bound on the open content. No CORE / cancellation / completion / moment / anti-concentration /
capacity claim. The prize `M(μ_n) ≤ C·√(n·log(p/n))` remains OPEN.

Axiom-clean (`propext, Classical.choice, Quot.sound`). Issue #407 / #444.
-/

namespace ArkLib.ProximityGap.GaussPhaseResonance

open scoped BigOperators Classical
open Finset

variable {m : ℕ} [NeZero m]

/-- **General-`r` conditional Resonance-Conjecture discharge from the trivial ceiling.** For unit
phases, if the unconditional trivial ceiling `m·(m−1)^{2(r−1)}` fits under the conjecture target
`(2 m log m)^r`, then `ResonanceConjecture u r` holds. Transitivity of
`resonanceMoment_le_unconditional` through the fit hypothesis. -/
theorem resonanceConjecture_of_trivCeil_le (u : ZMod m → ℂ) (hu : ∀ l : ZMod m, ‖u l‖ = 1)
    (r : ℕ)
    (hfit : (m : ℝ) * ((m : ℝ) - 1) ^ (2 * (r - 1)) ≤ (2 * (m : ℝ) * Real.log m) ^ r) :
    ResonanceConjecture u r := by
  unfold ResonanceConjecture
  exact le_trans (resonanceMoment_le_unconditional u hu r) hfit

end ArkLib.ProximityGap.GaussPhaseResonance
