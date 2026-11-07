/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.EnergyExcessCore

/-!
# Conditional representation bound from a Weil-form energy-excess input (#389)

The historical title of this file was "the wall CLOSES in the deployed regime `n² ≤ p`".
That overclaims: what is proved is a **conditional** Garcia–Voloch representation bound
`GVRepBound G M`, from an energy-excess hypothesis that is *not* proved anywhere in-tree.

## The research input (a hypothesis, not a known theorem)

Finite probes (`probe_excess_growth/even/ratio/weil_form`) motivated the **Weil-form**
estimate

  `p · energyExcess(μ_n) ≤ C · n⁴`   (`C ≈ 4.4` in the probed range),

which in the regime `n² ≤ p` is equivalent to `energyExcess(μ_n) = O(n²)`, i.e. additive
energy `E(μ_n) = O(n²)`. This file takes it as the explicit hypothesis `hWeil`; it is a
**probe-motivated conditional research input**. We cite no theorem in the literature that
proves it in this regime, and it should not be called "standard" or "known true": general
proven bounds on the additive energy of multiplicative subgroups (Heath-Brown–Konyagin type
`E(H) ≪ |H|^{5/2}` for `|H| ≤ p^{2/3}`, and later refinements) are much weaker than
`E = O(n²)`.

The finite data are also **not** a uniform `Θ(n⁴/p)` law: in the strong Sidon regime
(`p > 2^n`, see `SmallSubgroupSidon`) `μ_n` is exactly Sidon-modulo-negation and
`energyExcess(μ_n) = 0` (`SidonEnergyIff.energyExcess_eq_zero_iff_sidonModNeg`), so no
matching `Ω(n⁴/p)` lower bound holds there. Only the upper-bound form is used here.

## What is formalized (axiom-clean, no `sorry`)

Pure arithmetic on the machine-checked `gvRepBound_of_excess_le`:

* `gvRepBound_of_energyExcess_quadratic` — if `energyExcess G ≤ C·n²`, then `GVRepBound G M`
  for every `M` with `(3+C)·n ≤ M²` and `M³ ≤ 64n²`.
* `wall_closes_in_weil_regime` (historical name) — if `p · energyExcess(μ_n) ≤ C·n⁴` and
  `n² ≤ p`, then the same conclusion `GVRepBound G M` under the same two extra `M`
  hypotheses (`(3+C)·n ≤ M²`, `M³ ≤ 64n²`, so `M = Θ(√n)` and `n` large enough relative to
  `C`). These `M` hypotheses are part of the statement and are not discharged here.

## What is NOT proved here

* the input estimate `p · energyExcess ≤ C·n⁴` itself;
* any received-word **list-size** bound, any universal incidence/supply census, or any
  bound on `ε_mca` — `GVRepBound` bounds additive representation counts `r(t)` of `μ_n`,
  and no bridge from it to the MCA/list objects is supplied in this file;
* any statement about `δ*`, capacity, or beating Johnson. The earlier claims that "the
  entire supply wall closes" and "`δ*` reaches the optimal (capacity-side) value" relied on
  such further bridges, which are absent (see `Research/ProximityPrize/LegacyWorkbench.lean`:
  supply is not incidence).

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`.
-/

open Finset

namespace ArkLib.ProximityGap.AdditiveEnergySidonModNeg

open ArkLib.ProximityGap.AdditiveEnergyRepBound

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Quadratic excess closes the representation wall.** If the additive-energy excess above the
minimal SidonModNeg value is `≤ C·n²`, then the Garcia–Voloch representation bound holds at
`M = O(√n)`, subject to the two explicit `M` hypotheses. This is the direct consumer of the open
(unproved) quadratic-excess input `energyExcess(μ_n) ≤ C·n²`, i.e. `E_{F_p}(μ_n) = O(n²)`. -/
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

/-- **Conditional representation bound in the regime `n² ≤ p`** (historical name
`wall_closes_in_weil_regime`).  Given the probe-motivated, *unproved* Weil-form input
`p · energyExcess ≤ C·n⁴` (hypothesis `hWeil`), `n² ≤ p`, and the explicit `M` hypotheses
`(3+C)·n ≤ M²`, `M³ ≤ 64n²`, the Garcia–Voloch representation bound holds at `M`: every
`c ≠ 0` has `r(c) ≤ M`. This is only a representation-count bound; it does not by itself give
a list-size, census, `ε_mca`, `δ*` or capacity statement. -/
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
