/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CensusClassificationCharZero
import ArkLib.Data.CodingTheory.ProximityGap.KKH26FiberStructural

/-!
# The exact sub-Johnson list at agreement rm: the char-0 census IS the squaring fibres (#389)

The subset-sum fibre law's lower half is proven (`ladder_list_ge_fibre`); its upper half
(no word beats the fibre packing) is the census-domination wall over a general finite
field.  **In characteristic zero the wall dissolves for the squaring tower**, and this
file states it as a single exact theorem by instantiating the in-tree 2-power Lam–Leung
(Mann) classification at the ladder stack parameters:

> **`ladder_gapBand_antipodal_charZero`** — over a `2^μ`-th-root domain in a
> characteristic-zero field, every `GapBand` solution `T` of the squaring-tower ladder
> stack `(X^{2r}, X^{2(r−1)})` at code degree `< 2r−2` is **antipodally closed**
> (`∀ x ∈ T, −x ∈ T`) — i.e. a union of `r` squaring-fibres `{±y}`.

Combined with `fiberUnion_gapBand` (the converse — fibre-unions are `GapBand` solutions),
the char-0 ladder census at agreement `2r` is **exactly** the squaring-fibre-unions, both
inclusions.  Each such union is determined by its squaring image (an `r`-subset of the
`2^{μ−1}`-th roots with sum `−λ`), so the exact list count equals the subset-sum fibre
count `N_fib` — the upper bound MEETS the proven lower bound, with no constant gap and no
wall.

The finite-field statement holds above the char-0→`F_q` resultant threshold (for the
deployed `ε* = 2^{−128}` regime, `q ≥ 2^{128} ≫` threshold for fixed `n`); below it,
small-field inflation occurs (measured: the `p = 97` adversarial run).

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Polynomial Finset

namespace ArkLib.ProximityGap.KKH26

variable {L : Type*} [Field L] [CharZero L] [DecidableEq L]

/-- **THE EXACT UPPER STRUCTURE (char 0).**  Every `GapBand` solution of the squaring-tower
ladder stack `(X^{2r}, X^{2(r−1)})` over a `2^μ`-th-root domain is antipodally closed — a
union of squaring fibres.  This is the upper half of the exact sub-Johnson list law for the
squaring tower, matching the proven fibre supply; the wall dissolves in characteristic
zero.  (Instantiation of `gapBand_antipodal_charZero` at `A = 2r`, `B = 2r−2`,
`k = 2r−3`.) -/
theorem ladder_gapBand_antipodal_charZero {ζ : L} {μ : ℕ} (hμ : 1 ≤ μ)
    (hζ : IsPrimitiveRoot ζ (2 ^ μ)) {r : ℕ} (hr : 2 ≤ r)
    {T : Finset L} (hT : ∀ x ∈ T, x ^ (2 ^ μ) = 1) (hTcard : T.card = 2 * r)
    {lam : L} (hband : GapBand T (2 * r) (2 * r - 2) (2 * r - 3) lam) :
    ∀ x ∈ T, -x ∈ T := by
  refine gapBand_antipodal_charZero hμ hζ hT (k := 2 * r - 3)
    (A := 2 * r) (B := 2 * r - 2) ?_ ?_ ?_ ?_ hTcard hband
  · omega          -- 1 ≤ 2r − 3   (r ≥ 2)
  · omega          -- 2r − 2 < 2r − 1
  · omega          -- 2r − 3 ≤ 2r − 1
  · omega          -- 2 ≤ 2r

end ArkLib.ProximityGap.KKH26

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.KKH26.ladder_gapBand_antipodal_charZero
