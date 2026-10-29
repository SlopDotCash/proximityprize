/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.Data.Lattices.CyclotomicRing.NormBounds.Basic

/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ProximityPrize.Extensions.Data.Lattices.CyclotomicRing.Rq
import ProximityPrize.Extensions.Data.Lattices.Vectors
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.ValMinAbs

/-!
# Centered Norms And Norm-Growth Bounds on `Rq Φ` (Common Layer)

The centered `ℓ₁` / squared-`ℓ₂` norms of a cyclotomic-ring element `a : Rq Φ` over
`ZMod q` (sums of `ZMod.valMinAbs` representatives of its coefficients), their vector
lifts, the bound expressions, and the genuinely-proven norm-growth fact:

* `sub_l2NormSq_le` — `‖v - w‖₂² ≤ 4·b` whenever `‖v‖₂², ‖w‖₂² ≤ b`,

which lets the Module-SIS shortness predicate be instantiated concretely (see
`Ajtai.Simple.Security`). The foundational fact is the minimality of the centered
representative (`valMinAbs_natAbs_le`).

There are two more complicated norm-lemmas in sibling files:
* `NormBounds.MicciancioYoung` — the product bound `scalarVecMul_mul_l2NormSq_le`;
* `NormBounds.LyubashevskySeiler` — short-element invertibility `isUnit_of_l1Norm_le`.

## References

* [Nguyen, N. K., and Seiler, G., *Greyhound: Fast Polynomial Commitments from Lattices*][NS24]
* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
    Polynomial Commitments over Extension Fields*][NOZ26]
-/

open scoped BigOperators

namespace ArkLib.Lattices.CyclotomicModulus

variable {q : ℕ} [NeZero q]

/-! ## Minimality and triangle inequality for the centered representative -/

variable [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
  (Φ : CyclotomicModulus (ZMod q)) [IsCyclotomic Φ]

/-! ## The centered norms -/

end ArkLib.Lattices.CyclotomicModulus
