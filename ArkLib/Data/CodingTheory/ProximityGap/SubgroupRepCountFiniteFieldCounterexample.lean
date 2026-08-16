/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum

set_option linter.style.longLine false

/-!
# Round 9 (Issue #232, ABF26) — the char-0 minimal-energy bound DOES NOT transfer to `F_q` (verified).

`RootsOfUnityAdditiveEnergy` proved that in **characteristic 0** the roots of unity have minimal
additive energy, via the unit-circle fact that a nonzero `t` has at most `2` representations
`#{c : c, c+t both roots of unity} ≤ 2`. `AdditiveEnergyRepBound` then showed `repCount ≤ 2 ⟹ E ≤ 3|G|²`
over any field. The natural hope was to prove `repCount ≤ 2` for the `2^k`-subgroup over `F_q`.

**This file refutes that hope with an explicit verified counterexample.** Over `F₁₇` (`17 ≡ 1 mod 16`,
so the `8`-th roots of unity exist), the `8`-th roots are
`G = {1,2,4,8,9,13,15,16} = {±1,±2,±4,±8}`, and the nonzero shift `t = 1` has **three** representations:

> `repCount_F17_eighthRoots_eq_three`:  `#{c ∈ G : c + 1 ∈ G} = 3`,  witnessed by `c ∈ {1, 8, 15}`
> (the consecutive pairs `(1,2), (8,9), (15,16)` are all inside `G`).

So `repCount ≤ 2` is **false** over `F_q`: the char-0 minimal-additive-energy property of roots of unity
does **not** transfer to finite fields. The additive coincidences (here, three consecutive pairs inside
the subgroup) are a genuine `F_q` phenomenon with no characteristic-0 analogue — exactly the reason the
deep-interior δ* question is hard over `F_q`, and a sharp correction to the naive "smooth domains have
minimal additive energy" intuition: **they do in char 0, but not over `F_q`.** The honest open problem is
therefore the *true* (larger-than-`3|G|²`) sum-product additive-energy bound for `2^k`-subgroups over
`F_q`, not the char-0 value. All `sorry`-free and axiom-clean (the finite `F₁₇` facts are closed by
the kernel `decide`, not `native_decide`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #232.
-/

open Finset

namespace ArkLib.ProximityGap.SubgroupRepCountFiniteFieldCounterexample

/-- The `8`-th roots of unity in `F₁₇` (the multiplicative subgroup `⟨2⟩` of order `8`):
`{1, 2, 4, 8, 9, 13, 15, 16} = {±1, ±2, ±4, ±8}`. -/
def G : Finset (ZMod 17) := {1, 2, 4, 8, 9, 13, 15, 16}

/-- Every element of `G` is an `8`-th root of unity (`x^8 = 1`). -/
theorem G_eighth_roots : ∀ x ∈ G, x ^ 8 = 1 := by decide

/-- `G` has `8` elements (it is the full subgroup of `8`-th roots of unity, since `8 ∣ 16 = |F₁₇ˣ|`). -/
theorem G_card : G.card = 8 := by decide

/-- **The char-0 bound `repCount ≤ 2` FAILS over `F₁₇`.** The nonzero shift `t = 1` has *three*
representations `c, c+1 ∈ G`, namely `c ∈ {1, 8, 15}`. So the `8`-th roots of unity over `F₁₇` do **not**
have the char-0 "at most two representations" property. -/
theorem repCount_F17_eighthRoots_eq_three :
    (G.filter (fun c => c + 1 ∈ G)).card = 3 := by decide

/-- The three explicit witnesses: `(1,2), (8,9), (15,16)` are consecutive pairs inside `G`. -/
theorem repCount_witnesses :
    (1 : ZMod 17) ∈ G ∧ (1 + 1 : ZMod 17) ∈ G ∧
    (8 : ZMod 17) ∈ G ∧ (8 + 1 : ZMod 17) ∈ G ∧
    (15 : ZMod 17) ∈ G ∧ (15 + 1 : ZMod 17) ∈ G := by decide

/-- **Consequence: `repCount ≤ 2` is not provable over `F_q`** — there is an explicit subgroup (the
`8`-th roots of unity in `F₁₇`) and a nonzero `t` with `repCount = 3 > 2`. Hence the char-0
minimal-additive-energy argument (`RootsOfUnityAdditiveEnergy.unitCircle_reps_le_two`) genuinely does
**not** transfer to finite fields; the true `F_q` additive energy is the open sum-product quantity. -/
theorem char0_repBound_fails_over_finite_field :
    ∃ (t : ZMod 17), t ≠ 0 ∧ 2 < (G.filter (fun c => c + t ∈ G)).card :=
  ⟨1, by decide, by rw [repCount_F17_eighthRoots_eq_three]; norm_num⟩

end ArkLib.ProximityGap.SubgroupRepCountFiniteFieldCounterexample

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.SubgroupRepCountFiniteFieldCounterexample.repCount_F17_eighthRoots_eq_three
#print axioms ArkLib.ProximityGap.SubgroupRepCountFiniteFieldCounterexample.char0_repBound_fails_over_finite_field
