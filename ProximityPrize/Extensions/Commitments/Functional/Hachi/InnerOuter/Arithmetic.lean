/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.Commitments.Functional.Hachi.InnerOuter.Arithmetic

/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Data.Lattices.CyclotomicRing.PowTwo
import ArkLib.Data.Lattices.CyclotomicRing.NormBounds

/-!
# The Inner-Outer Commitment/Hachi Ring `Z_q[X] / (X^{2^α} + 1)`

This file fixes the cyclotomic ring over which the **inner-outer Ajtai commitment** operates.
That commitment — the Greyhound [NS24] / Hachi [NOZ26] construction — works specifically over
the power-of-two cyclotomic ring `R_q := Z_q[X] / (X^{2^α} + 1)`.

The ring itself now lives in `Data/Lattices` as `primePowTwoModulus` / `PrimePowTwoRing` (see
`ArkLib/Data/Lattices/CyclotomicRing/PowTwo.lean`), since it is pure cyclotomic ring theory and
is shared with the extension-field algebra of Hachi [NOZ26, §3]. This file just re-exports it
under the commitment-facing names `hachiModulus` / `HachiRing` and installs the scoped notation,
so the inner-outer correctness/security files are unaffected.

The weak-binding *security* of the scheme genuinely needs this ring: its two deep analytic
inputs — Lyubashevsky–Seiler short-element invertibility (`isUnit_of_l1Norm_le`) and the
Micciancio/Young product norm bound (`scalarVecMul_mul_l2NormSq_le`) — hold only over
`X^{2^α} + 1`. Because `hachiModulus` is *reducibly* equal to `powTwoCyclotomic α`, those
`powTwoCyclotomic`-stated lemmas apply to `HachiRing q α` directly.

## Main definitions

* `hachiModulus q α` — the inner-outer commitment modulus `X^{2^α} + 1` over `ZMod q`
  (a re-export of `primePowTwoModulus`).
* `HachiRing q α` — the inner-outer commitment ring `Z_q[X] / (X^{2^α} + 1)`
  (a re-export of `PrimePowTwoRing`).

## Notation

* `𝓡⟦q, α⟧` (scoped, in `ArkLib.Lattices.Ajtai.InnerOuter`) — the ring `HachiRing q α`.
* `𝓜(q, α)` (scoped, in `ArkLib.Lattices.Ajtai.InnerOuter`) — the modulus `hachiModulus q α`.

## References

* [Lyubashevsky, V., and Seiler, G., *Short, Invertible Elements in Partially Splitting
    Cyclotomic Rings*][LS18]
* [Nguyen, N. K., and Seiler, G., *Greyhound: Fast Polynomial Commitments from Lattices*][NS24]
* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
    Polynomial Commitments over Extension Fields*][NOZ26]
-/

open ArkLib.Lattices ArkLib.Lattices.CyclotomicModulus CompPoly CompPoly.CPolynomial

namespace ArkLib.Lattices.Ajtai.InnerOuter

variable (q : ℕ) [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)] (α : ℕ)

end ArkLib.Lattices.Ajtai.InnerOuter
