/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CubicOrchardIdentity
import Mathlib.Tactic.NormNum.Prime

/-!
# The deep-band cubic-supply dichotomy: `3 ∣ n` ⟹ nonzero (#389)

`CubicSupplyZeroF73.lean` shows `x³` on `μ_8 ⊂ F₇₃` has **0** explainable `3`-cores — the
char-`0` Mann rigidity (`ThreeRootsSumZeroCharZero`: no three `n`-th roots of unity sum to
zero **when `3 ∤ n`**) lifting to `F_p`.  This file lands the **complementary half**, making
the `3 ∤ n` hypothesis sharp: when `3 ∣ n`, the cube roots of unity lie in `μ_n` and
`1 + ω + ω² = 0` *forces* a zero-sum triple, so the deep-band supply is **nonzero**.

> **`cubicSupply_mu6_F7_eq_two`** — `x³` on `μ_6 = F₇^× ⊂ F₇` has exactly `2` explainable
> `3`-cores: the cube-root triple `{1,2,4}` (`1+2+4 = 0`) and `{3,5,6}` (`3+5+6 = 0`).  Via
> the cubic orchard identity, the zero-sum-triple count is `2`.

Together with `cubicSupply_mu8_F73_eq_zero` this is the exact deep-band dichotomy:

  `3 ∤ n  ⟹  cubic supply 0` (Mann rigidity, e.g. `μ_8`);
  `3 ∣ n  ⟹  cubic supply ≥ 1` (cube-root triple, e.g. `μ_6`).

So the deepest pre-capacity (sub-Johnson) supply of the tower-shaped word `x³` is governed
by a single arithmetic condition on `n` — the precise boundary of the char-`0` rigidity that
makes `μ_{2^k}` (`3 ∤ 2^k`) a good deep-band word and `3 ∣ n` domains bad.  Issue #389.
-/

open Finset

namespace ProximityGap.PairRank

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership Code

local instance localInstance_CubicSupplyDichotomy_1 : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- `μ_6 = F₇^× ⊂ F₇` (the full multiplicative group, cyclic of order 6). -/
def dom6vals : Fin 6 → ZMod 7 := ![1, 2, 3, 4, 5, 6]

/-- The evaluation domain `μ_6 ⊂ F₇` as an embedding (injective by `decide`). -/
def dom6 : Fin 6 ↪ ZMod 7 := ⟨dom6vals, by decide⟩

set_option maxHeartbeats 1000000 in
/-- The zero-sum-triple count of `μ_6 ⊂ F₇` is `2`: `{1,2,4}` (the cube roots, `1+2+4 = 0`)
and `{3,5,6}` (`3+5+6 = 0`).  Since `3 ∣ 6`, the cube roots of unity are present. -/
theorem mu6_F7_zeroSum_triples_eq_two :
    (((Finset.univ : Finset (Fin 6)).powersetCard 3).filter
        (fun T => ∑ i ∈ T, dom6 i = 0)).card = 2 := by
  decide

open Classical in
/-- **The complementary deep-band supply, NONZERO**: `x³` on `μ_6 ⊂ F₇` has exactly `2`
explainable `3`-cores (vs `0` for `μ_8 ⊂ F₇₃`).  When `3 ∣ n`, the cube-root triple
`1 + ω + ω² = 0` makes the deep-band supply nonzero — the sharp boundary of the rigidity. -/
theorem cubicSupply_mu6_F7_eq_two :
    ((Finset.univ : Finset (Fin 6 → ZMod 7)).filter (fun c =>
        c ∈ (rsCode dom6 2 : Submodule (ZMod 7) (Fin 6 → ZMod 7))
          ∧ 3 ≤ (agreeSet c (fun i => (dom6 i) ^ 3)).card)).card = 2 := by
  rw [cubic_list_eq_zeroSum dom6]
  exact mu6_F7_zeroSum_triples_eq_two

end ProximityGap.PairRank

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.PairRank.mu6_F7_zeroSum_triples_eq_two
#print axioms ProximityGap.PairRank.cubicSupply_mu6_F7_eq_two
