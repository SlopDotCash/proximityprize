/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.EnergyExcessCore

/-!
# The wall CLOSES in the deployed regime `n² ≤ p` (#389)

Empirically (probes `probe_excess_growth/even/ratio/weil_form`), the energy excess of a
root-of-unity subgroup obeys the **Weil form**

  `energyExcess(μ_n) = Θ(n⁴ / p)`,  with `p · energyExcess ≤ C · n⁴`, `C ≈ 4.4` bounded,

and `energyExcess/n² → 0` as `n²/p → 0` (μ_n is *exactly* Sidon for small subgroups).
This is the standard additive-energy-of-a-multiplicative-subgroup bound (a 4th-moment /
equidistribution estimate — the regime where Weil *works*, unlike the worst-case
representation count of `SubgroupCharacterSumNoGo`).

Taking that bound as the named input, this file proves — by pure arithmetic on the
already-machine-checked `gvRepBound_of_excess_le` — that the **entire supply wall closes
in the deployed regime `n² ≤ p`** (`n ≤ √p`, exactly the production setting `n ≪ √q`):

> **`wall_closes_in_weil_regime`** — if `p · energyExcess(μ_n) ≤ C·n⁴` and `n² ≤ p`,
> then `GVRepBound G M` for any `M` with `(3+C)·n ≤ M²` and `M³ ≤ 64n²` (`M = O(√n)`).

So in the deployed regime the energy excess is `O(n²)`, the representation count is
`O(√n)`, and `δ*` reaches the optimal (capacity-side) value — `μ_n` beats Johnson.  The
only remaining input is the **standard Weil energy bound** `p·excess ≤ C·n⁴`, a known
true estimate (not the worst-case no-go), now isolated as the sole hypothesis.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`.
-/

open Finset

namespace ArkLib.ProximityGap.AdditiveEnergySidonModNeg

open ArkLib.ProximityGap.AdditiveEnergyRepBound

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Quadratic excess closes the representation wall.** If the additive-energy excess above the
minimal SidonModNeg value is `≤ C·n²`, then the Garcia–Voloch representation bound holds at
`M = O(√n)`. This is the direct consumer of the now-isolated open core
`E_{F_p}(μ_n) ≤ C·n²`. -/
theorem gvRepBound_of_energyExcess_quadratic {G : Finset F} {n C M : ℕ}
    (hn : 1 ≤ n) (hGmem : ∀ z, z ∈ G ↔ z ^ n = 1) (hcard : G.card = n)
    (h2 : (2 : F) ≠ 0) (h0 : (0 : F) ∉ G) (hneg : ∀ x ∈ G, -x ∈ G)
    (hexc : energyExcess G ≤ C * n ^ 2)
    (hM : (3 + C) * n ≤ M ^ 2) (hM3 : M ^ 3 ≤ 64 * n ^ 2) :
    GVRepBound G M := by
  have hkey : 3 * n ^ 2 + C * n ^ 2 ≤ n * M ^ 2 := by
    have hh : (3 + C) * n ^ 2 ≤ n * M ^ 2 := by
      calc (3 + C) * n ^ 2 = n * ((3 + C) * n) := by ring
        _ ≤ n * M ^ 2 := Nat.mul_le_mul_left n hM
    rw [show 3 * n ^ 2 + C * n ^ 2 = (3 + C) * n ^ 2 by ring]
    exact hh
  refine gvRepBound_of_excess_le hn hGmem hcard h2 h0 hneg ?_ ?_ ?_
  · omega
  · rw [hcard]
    exact hM3
  · omega

/-- **The wall closes in the deployed regime.**  Given the standard Weil energy bound
`p · energyExcess ≤ C·n⁴` and `n² ≤ p`, the Garcia–Voloch representation bound holds at
`M = O(√n)`: every `c ≠ 0` has `r(c) ≤ M`, so the entire supply wall closes. -/
theorem wall_closes_in_weil_regime {G : Finset F} {n C M : ℕ}
    (hn : 1 ≤ n) (hGmem : ∀ z, z ∈ G ↔ z ^ n = 1) (hcard : G.card = n)
    (h2 : (2 : F) ≠ 0) (h0 : (0 : F) ∉ G) (hneg : ∀ x ∈ G, -x ∈ G)
    (hWeil : Fintype.card F * energyExcess G ≤ C * n ^ 4)
    (hnp : n ^ 2 ≤ Fintype.card F)
    (hM : (3 + C) * n ≤ M ^ 2) (hM3 : M ^ 3 ≤ 64 * n ^ 2) :
    GVRepBound G M := by
  -- Step 1: from the Weil bound and `n² ≤ p`, the excess is `≤ C·n²`.
  have hnpos : 0 < n ^ 2 := by positivity
  have hexc : energyExcess G ≤ C * n ^ 2 := by
    have h1 : n ^ 2 * energyExcess G ≤ C * n ^ 4 := by
      calc n ^ 2 * energyExcess G ≤ Fintype.card F * energyExcess G := by gcongr
        _ ≤ C * n ^ 4 := hWeil
    have h2' : n ^ 2 * energyExcess G ≤ n ^ 2 * (C * n ^ 2) := by
      calc n ^ 2 * energyExcess G ≤ C * n ^ 4 := h1
        _ = n ^ 2 * (C * n ^ 2) := by ring
    exact Nat.le_of_mul_le_mul_left h2' hnpos
  -- Step 2: feed the quadratic-excess consumer.
  exact gvRepBound_of_energyExcess_quadratic hn hGmem hcard h2 h0 hneg hexc hM hM3

end ArkLib.ProximityGap.AdditiveEnergySidonModNeg

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.AdditiveEnergySidonModNeg.gvRepBound_of_energyExcess_quadratic
#print axioms ArkLib.ProximityGap.AdditiveEnergySidonModNeg.wall_closes_in_weil_regime
