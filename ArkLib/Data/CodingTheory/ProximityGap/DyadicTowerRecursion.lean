/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-!
# The dyadic Gauss-period tower recursion and its parallelogram law (#407)

For `n = 2^μ`, the smooth domain splits `μ_{2^μ} = μ_{2^{μ-1}} ⊔ ω·μ_{2^{μ-1}}` (ω a primitive `2^μ`-th
root). Hence the Gauss period at level μ is the sum of two level-`(μ-1)` periods:

> **`sum_tower_split`** — if `G = H ⊔ ω·H` then `∑_{x∈G} f(x) = ∑_{x∈H} f(x) + ∑_{x∈H} f(ω·x)`.
> Instantiated at `f = ψ(b·•)` this is the exact recursion `η_b^{(μ)} = η_b^{(μ-1)} + η_{bω}^{(μ-1)}`.

Pairing it with the parallelogram law gives the exact second-moment recursion that the dyadic-tower
attacks rest on (and shows why naive triangle-bounding only yields the trivial `2×` per level):

> **`period_parallelogram`** — `‖a+b‖² + ‖a-b‖² = 2(‖a‖² + ‖b‖²)` for the period `η=a+b` and the
> χ-twisted period `η̃=a-b` (a,b the two sub-period halves).

These are char-free identities; the open content is controlling the cross-term/alignment across the
tower (cross-moments provably DOMINATE — no free decorrelation), not these recursions themselves.

Issue #407.
-/

open Finset

namespace ArkLib.ProximityGap.DyadicTowerRecursion

variable {F : Type*} [Field F] [DecidableEq F]

/-- **Tower split.** If `G` decomposes as the disjoint union of `H` and its `ω`-dilate `ω·H`, then any
sum over `G` splits as a sum over `H` plus a sum over `H` of the `ω`-shifted summand. With
`f = b`-additive-character this is the period recursion `η_b^{(μ)} = η_b^{(μ-1)} + η_{bω}^{(μ-1)}`. -/
theorem sum_tower_split {M : Type*} [AddCommMonoid M] {G H : Finset F} {ω : F} (hω : ω ≠ 0)
    (f : F → M) (hsplit : G = H ∪ H.image (fun x => ω * x))
    (hdisj : Disjoint H (H.image (fun x => ω * x))) :
    ∑ x ∈ G, f x = ∑ x ∈ H, f x + ∑ x ∈ H, f (ω * x) := by
  have hinj : ∀ x ∈ H, ∀ y ∈ H, ω * x = ω * y → x = y :=
    fun a _ b _ h => mul_left_cancel₀ hω h
  rw [hsplit, Finset.sum_union hdisj, Finset.sum_image hinj]

/-- **Period parallelogram law.** For the level-μ period `η = a + b` and its χ-twist `η̃ = a − b`
(where `a, b` are the two level-`(μ-1)` sub-period halves), `‖η‖² + ‖η̃‖² = 2(‖a‖² + ‖b‖²)`. The total
second moment is conserved and split between the period and its twist — the exact obstruction to a
naive `√`-cancellation descent. -/
theorem period_parallelogram (a b : ℂ) :
    ‖a + b‖ ^ 2 + ‖a - b‖ ^ 2 = 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  exact parallelogram_law_with_norm ℂ a b

end ArkLib.ProximityGap.DyadicTowerRecursion

#print axioms ArkLib.ProximityGap.DyadicTowerRecursion.sum_tower_split
#print axioms ArkLib.ProximityGap.DyadicTowerRecursion.period_parallelogram
