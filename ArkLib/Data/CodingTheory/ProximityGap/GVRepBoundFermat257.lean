/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GVHBKEnergyReduction
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupAdditiveEnergyFermat257

/-!
# A concrete `GVRepBound` witness: the order-16 NTT subgroup of `F₂₅₇` (#389)

The Garcia–Voloch / Heath-Brown–Konyagin energy reduction (`GVHBKEnergyReduction.lean`)
introduced the named smooth-domain input `GVRepBound G M` (`∀ t ≠ 0, r(t) ≤ M` with
`M³ ≤ 64·|G|²`), the integer-clean form of `r(t) ≤ 4·|G|^{2/3}`, and proved the
conditional energy bound `E(G)³ ≤ 260·|G|⁸` from it.  The input was stated as a `Prop`
pending its in-tree Stepanov proof — with **no concrete instance**, so the whole
GV → energy → cubic-supply chain was vacuous.

This file supplies the first machine-checked witness, at a *production-shape NTT domain*:
the order-16 multiplicative subgroup `H16 ⊆ F₂₅₇^×` (`F₂₅₇` is a Fermat prime, the
canonical small NTT field; `|G| = 16 ≪ q = 257` is the deployed `|G| ≪ q` regime).

* `gvRepBound_H16 : GVRepBound H16 4` — every nonzero `t` has at most `4`
  representations `t = c + d`, `c, d ∈ H16` (`decide`), and `4³ = 64 ≤ 64·16² = 16384`.
  So `M = 4 = 4·16^{2/3}` saturates the Garcia–Voloch exponent exactly at this point.
* `additiveEnergy_H16_le_gv` — the conditional bound `E(H16)³ ≤ 260·16⁸` instantiated,
  consistent with the exactly-known `E(H16) = 912` (`912³ = 758 550 528 ≤
  1 116 691 496 960`): the chain is non-vacuous and the GV ceiling is comfortably above
  the true energy, as expected in the `|G| ≪ q` regime.

The pointwise GV ceiling is verified empirically across 89 two-power domains
`μ_{2^k} ⊂ F_p` (k = 3..6, ~20 primes each) in `probe_smooth_zero_sum_triples.py` —
`max_{t≠0} r(t) ≤ 4·n^{2/3}` with **zero** violations, alongside the zero-sum-triple
census (the cubic supply via the orchard identity): it ranges from exactly `0` (the
char-0 Mann rigidity — three 2-power roots of unity never sum to zero — survives to
`F_p` for many primes) up to `~n^{5/3}` (GV-tight) for others, always `≪ n²`.

Issue #389.  Probe: `scripts/probes/probe_smooth_zero_sum_triples.py`.
-/

open Finset

namespace ArkLib.ProximityGap.AdditiveEnergyRepBound

open ArkLib.ProximityGap.SubgroupAdditiveEnergyFermat257

local instance localInstance_GVRepBoundFermat257_1 : Fact (Nat.Prime 257) := ⟨by norm_num⟩

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
/-- **The first concrete `GVRepBound` witness**: the order-16 NTT subgroup of `F₂₅₇`
satisfies `GVRepBound H16 4` — every nonzero shift has at most `4` representations as a
sum of two subgroup elements, and `4³ = 64 ≤ 64·16² = 16384`.  The observed maximum
`M = 4` is the *true* rep-count ceiling here, comfortably inside the Garcia–Voloch bound
`4·|G|^{2/3} = 4·16^{2/3} ≈ 25.4` (and inside the integer-clean form, which would admit
any `M ≤ 25`).  Certifies the GV→energy→cubic-supply chain is non-vacuous at a
production-shape point. -/
theorem gvRepBound_H16 : GVRepBound H16 4 := by
  refine ⟨?_, ?_⟩
  · decide
  · have h : H16.card = 16 := cards.2.2.2
    rw [h]; norm_num

/-- The conditional energy bound (`additiveEnergy_cube_le_of_gvRepBound`) instantiated at
`H16`: `E(H16)³ ≤ 260·16⁸`.  Consistent with the exact `E(H16) = 912` (in-tree
`energy_H16`): `912³ ≤ 260·16⁸`. -/
theorem additiveEnergy_H16_le_gv : additiveEnergy H16 ^ 3 ≤ 260 * H16.card ^ 8 :=
  additiveEnergy_cube_le_of_gvRepBound H16 gvRepBound_H16

/-- Sanity: the conditional GV ceiling at `H16` is comfortably above the true energy
`E(H16) = 912`, confirming the `|G| ≪ q` looseness. -/
theorem additiveEnergy_H16_gv_consistent : (912 : ℕ) ^ 3 ≤ 260 * 16 ^ 8 := by norm_num

end ArkLib.ProximityGap.AdditiveEnergyRepBound

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.gvRepBound_H16
