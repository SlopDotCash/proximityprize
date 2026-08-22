/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.AdditiveEnergyRepBound

/-!
# Round 11 (Issue #232, ABF26) — the EXACT additive energy of a concrete smooth `F_q` subgroup.

`RootsOfUnityAdditiveEnergy` proved the char-0 minimum `E(S) ≤ 3|S|²` (roots of unity, maximal
anti-concentration). `AdditiveEnergyRepBound` reduced the finite-field side to the representation
bound `repCount ≤ 2`, and `SubgroupRepCountFiniteFieldCounterexample` showed that bound **fails** over
`F_q` (the shift `t = 1` has `3` representations in the order-8 subgroup of `F₁₇`). This file closes
the concrete loop by computing the **exact** additive energy of that same explicit subgroup:

> `additiveEnergy_F17_eighthRoots_eq`:  `E(G) = 264`  for `G = {1,2,4,8,9,13,15,16} ⊆ F₁₇` (the
> order-8 multiplicative subgroup = 8-th roots of unity), by `decide`.

The value sits **strictly between** the char-0 minimum and the trivial maximum:

> `char0_minimum_lt`:  `3·|G|² = 192 < 264 = E(G)`  (the finite-field energy EXCEEDS the char-0
>   minimum — a quantitative witness that the roots-of-unity anti-concentration is **lost** over `F_q`,
>   matching the `repCount = 3 > 2` counterexample), and
> `lt_trivial_maximum`: `E(G) = 264 < 512 = |G|³`  (it is still far from the maximal-concentration
>   degenerate value).

So for this explicit prize-faithful smooth instance the additive energy is a concrete number in the
open band `(3|G|², |G|³)`; the prize regime's question is exactly *where in that band* the energy of
the `2^k`-subgroup lands as `|G|, q → ∞` (the open Weil/sum-product input). `sorry`-free, axiom-clean.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #232.
-/

open ArkLib.ProximityGap.AdditiveEnergyRepBound

namespace ArkLib.ProximityGap.SubgroupAdditiveEnergyF17

/-- `17` is prime, so `ZMod 17` is a `Field` (required by `additiveEnergy`'s `[Field F]`). -/
local instance localInstance_SubgroupAdditiveEnergyF17_1 : Fact (Nat.Prime 17) := ⟨by norm_num⟩

/-- The order-8 multiplicative subgroup of `F₁₇` (the 8-th roots of unity), the same explicit smooth
instance used in `SubgroupRepCountFiniteFieldCounterexample`. -/
def G : Finset (ZMod 17) := {1, 2, 4, 8, 9, 13, 15, 16}

theorem G_card : G.card = 8 := by decide

theorem G_eighth_roots : ∀ x ∈ G, x ^ 8 = 1 := by decide

/-- **The exact additive energy of the order-8 subgroup of `F₁₇` is `264`.** Computed by `decide`
over `additiveEnergy G = ∑_{a,b∈G} #{y∈G : (a+b)−y ∈ G}`. -/
theorem additiveEnergy_F17_eighthRoots_eq : additiveEnergy G = 264 := by decide

/-- **The finite-field energy exceeds the char-0 minimum `3|G|²`.** `192 < 264`: a quantitative
witness that the roots-of-unity minimal-additive-energy (anti-concentration) property is lost over
`F_q`, consistent with `repCount = 3 > 2` (`SubgroupRepCountFiniteFieldCounterexample`). -/
theorem char0_minimum_lt : 3 * G.card ^ 2 < additiveEnergy G := by decide

/-- **The energy is still strictly below the trivial maximum `|G|³`.** `264 < 512`: the subgroup is
far from the maximal-concentration degenerate regime; its energy lies in the open band `(3|G|²,|G|³)`,
exactly the band whose asymptotics for the `2^k`-subgroup is the open prize quantity. -/
theorem lt_trivial_maximum : additiveEnergy G < G.card ^ 3 := by decide

end ArkLib.ProximityGap.SubgroupAdditiveEnergyF17

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.SubgroupAdditiveEnergyF17.additiveEnergy_F17_eighthRoots_eq
#print axioms ArkLib.ProximityGap.SubgroupAdditiveEnergyF17.char0_minimum_lt
