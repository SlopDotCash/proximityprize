/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumFourthMoment
import Mathlib.Combinatorics.Additive.Energy

/-!
# Bridge: the local `addEnergy` equals Mathlib's `Finset.addEnergy` (#357)

`SubgroupGaussSumFourthMoment.addEnergy G = ∑_{y₁,y₂,y₃,y₄∈G} [y₁+y₂ = y₃+y₄]` is the local additive
energy used by the anti-concentration ladder and the homogeneity reduction. Mathlib's
`Finset.addEnergy G G` counts the same quadruples `(a₁,a₂,b₁,b₂)∈G⁴` with `a₁+b₁ = a₂+b₂`. This file
proves they are equal:

  `addEnergy_eq_mathlib` : `addEnergy G = Finset.addEnergy G G`.

This opens the entire Mathlib additive-combinatorics energy API (`le_addEnergy`, monotonicity, the
Cauchy–Schwarz `card_sq_le_card_mul_addEnergy`, etc.) to the HBK/Stepanov formalization, and lets
the local `addEnergy_ge_sq` / `addEnergy_le_cube` / `addEnergy_eq_card_mul_normalizedCount`
interoperate with the library.

**Honest scope:** a definitional bridge; it does not bound the energy (the open sum-product input).
Does not pin `δ*`.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset

namespace ArkLib.ProximityGap.SubgroupGaussSumFourthMoment

variable {F : Type*} [Field F] [DecidableEq F]

/-- **The local additive energy equals Mathlib's `Finset.addEnergy`.** Both count quadruples in
`G⁴` with a matching additive equation; the variable groupings differ by a transposition of the two
middle coordinates, resolved by `Finset.sum_comm`. -/
theorem addEnergy_eq_mathlib (G : Finset F) :
    addEnergy G = Finset.addEnergy G G := by
  classical
  rw [Finset.addEnergy, Finset.card_filter, Finset.sum_product, addEnergy]
  -- LHS: ∑_{y₁}∑_{y₂}∑_{y₃}∑_{y₄} [y₁+y₂ = y₃+y₄]
  -- RHS: ∑_{p∈G×ˢG} ∑_{q∈G×ˢG} [p.1+q.1 = p.2+q.2]
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl (fun y₁ _ => ?_)
  -- ∑_{y₂}∑_{y₃}∑_{y₄}[y₁+y₂=y₃+y₄]  vs  ∑_{a₂∈G} ∑_{q∈G×ˢG} [y₁+q.1 = a₂+q.2]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun y₂ _ => ?_)
  rw [Finset.sum_product]

end ArkLib.ProximityGap.SubgroupGaussSumFourthMoment

/-! ## Axiom audit — kernel-clean. -/
#print axioms ArkLib.ProximityGap.SubgroupGaussSumFourthMoment.addEnergy_eq_mathlib
