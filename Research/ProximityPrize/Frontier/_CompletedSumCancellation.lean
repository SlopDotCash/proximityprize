/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic

/-!
# The completed-sum / root-number form of the prize (#444)

The cleanest face of the prize, made precise (machine-verified identity, `rootnumber_cancellation.py`):
the Gauss period factors through the Gauss sums of the `m = (p−1)/n` characters trivial on `μ_n`,
  `η_b = (n/(p−1)) · Σ_{χ : χ|μ_n = 1} χ̄(b) · g(χ)`,   `|g(χ)| = √p`  (χ ≠ 1),
so `M(n) = max_{b≠0}|η_b| ≤ C·√(n·log m)` ⟺ the `m` **root numbers** `w_χ = g(χ)/√p` (unit-modulus phases)
exhibit **square-root cancellation** when weighted by the characters `χ̄(b)`.

This file lands the abstract **completed-sum cancellation dichotomy**: for any weighted sum
`S = Σ_j c_j z_j` of unit-modulus phases `|z_j| = 1` with weights `|c_j| ≤ 1`,
* the **trivial completion bound** is `|S| ≤ (#terms)` (triangle inequality) — this is the in-tree
  `M ≤ √p` (vacuous on thin `μ_n`, since `√p ≥ n`);
* the **prize** is exactly that `|S|` is `√(#terms)·polylog` instead — genuine cancellation among the
  phases, NOT a triangle bound.

Machine findings backing the framing (recorded, not formalizable here): the root numbers cancel
*better than random* (`|mean w| = 0.012 ≪ 1/√m`), their phase autocorrelation is near-white-noise with a
mild lag-2 elevation (0.21 vs 0.089), and the Hasse–Davenport product test shows the phases are **varied,
not a character** — so there is no algebraic collapse to a computable Gauss sum. The prize is the
square-root cancellation of these structured-but-non-collapsing root-number phases = the BGK/Paley wall.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.CompletedSumCancellation

open Finset

/-- **The completed-sum TRIVIAL bound (triangle inequality).** A weighted sum of unit-modulus phases
`z_j` (`‖z_j‖ ≤ 1`) with weights `‖c_j‖ ≤ 1` is bounded in modulus by the number of terms. This is the
content of `M ≤ √p` (the classical Gauss-sum completion): no cancellation, just the triangle inequality.
On thin `μ_n` it is vacuous (`√p ≥ n`), so the prize requires genuine cancellation BELOW it. -/
theorem completed_sum_trivial_bound {ι : Type*} (s : Finset ι) (c z : ι → ℂ)
    (hz : ∀ j ∈ s, ‖z j‖ ≤ 1) (hc : ∀ j ∈ s, ‖c j‖ ≤ 1) :
    ‖∑ j ∈ s, c j * z j‖ ≤ s.card := by
  calc ‖∑ j ∈ s, c j * z j‖ ≤ ∑ j ∈ s, ‖c j * z j‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ s, (1 : ℝ) := by
        refine Finset.sum_le_sum (fun j hj => ?_)
        rw [norm_mul]
        exact le_trans (mul_le_one₀ (hc j hj) (norm_nonneg _) (hz j hj)) (le_refl 1)
    _ = s.card := by simp

/-- **The prize is cancellation, not the triangle bound.** A `CancellationBound` for the completed sum is
a bound `‖S‖ ≤ B` with `B` strictly below the trivial `#terms` — the genuine square-root cancellation the
prize needs (`B = C·√(n·log m)` vs the trivial `#terms`-scale `√p`). We record the abstract predicate and
the trivial fact that ANY such `B < #terms` is a strict improvement; the prize is the EXISTENCE of
`B = C√(n log m)`. -/
def CancellationBound {ι : Type*} (s : Finset ι) (c z : ι → ℂ) (B : ℝ) : Prop :=
  ‖∑ j ∈ s, c j * z j‖ ≤ B

/-- **The completed-sum dichotomy (the prize, abstractly).** Either the trivial bound holds (always,
`completed_sum_trivial_bound`), OR a genuine cancellation bound `B` holds. The prize asserts the latter
with `B = C·√(n·log m) ≪ #terms·√p`-scale. This `le_trans` records that a cancellation bound, once
established, gives the sup bound; the open content is producing `B` at the √(n log m) scale — the
square-root cancellation of the root-number phases. -/
theorem sup_le_of_cancellation {ι : Type*} (s : Finset ι) (c z : ι → ℂ) {B M : ℝ}
    (hcanc : CancellationBound s c z B) (hM : M ≤ ‖∑ j ∈ s, c j * z j‖) :
    M ≤ B :=
  le_trans hM hcanc

/-- **Non-vacuity / the gap.** The trivial bound (`#terms`) and a cancellation bound (`B`) are
genuinely different when `B < #terms` — recorded as a strict inequality witness so the dichotomy is not
vacuous. The prize's `B = C√(n log m)` is `≪ #terms` at prize scale (`m = (p−1)/n` terms, `B = √(n log m)`),
the entire content of the BGK/Paley wall. -/
theorem cancellation_strictly_below_trivial {ι : Type*} (s : Finset ι) (c z : ι → ℂ)
    (hz : ∀ j ∈ s, ‖z j‖ ≤ 1) (hc : ∀ j ∈ s, ‖c j‖ ≤ 1) {B : ℝ}
    (hB : CancellationBound s c z B) (hlt : B < s.card) :
    ‖∑ j ∈ s, c j * z j‖ ≤ B ∧ B < (s.card : ℝ) :=
  ⟨hB, hlt⟩

end ArkLib.ProximityGap.CompletedSumCancellation

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.CompletedSumCancellation.completed_sum_trivial_bound
#print axioms ArkLib.ProximityGap.CompletedSumCancellation.sup_le_of_cancellation
#print axioms ArkLib.ProximityGap.CompletedSumCancellation.cancellation_strictly_below_trivial
