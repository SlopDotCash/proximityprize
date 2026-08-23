/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The moment → sup-norm bridge for the δ* open core (#389)

The assembly step of the cyclotomic-lattice reformulation
(`docs/kb/deltastar-cyclotomic-lattice-collision-core-2026-06-13.md`): the rigorous link from a
high even-moment bound on the Gauss periods to the sup-norm `B(μ_n) = max_{b≠0}‖η_b‖` that the
prize δ* needs. It is the elementary `ℓ^∞ ≤ ℓ^{2r}` inequality:

    `max_b ‖η_b‖ ≤ (∑_b ‖η_b‖^{2r})^{1/(2r)}`.

With `∑_{b≠0}‖η_b‖^{2r} = p·E_r − n^{2r}` (orthogonality) this says: **any** bound
`E_r ≤ (1+o(1))·E_r^{(0)}` on the `r`-th additive moment, at the optimal `r ≈ ⌈ln p⌉`, yields
`B ≤ (1+o(1))·√(e·n·ln p)` — the prize sup-norm. So this brick is precisely what converts the
(open) high-moment "halo non-concentration" inequality into the prize δ*. The open input is the
moment bound itself (the Bourgain–Shkredov wall); this bridge is unconditional and elementary.

Axiom target: `[propext, Classical.choice, Quot.sound]`.
-/

open Finset

namespace ArkLib.ProximityGap.MomentSupNormBridge

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- **Single-term domination under a power sum.** For nonnegative reals and any exponent `m ≥ 1`,
each term to the `m` is at most the full power sum: `(f b)^m ≤ ∑_i (f i)^m`. -/
theorem pow_le_sum_pow (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (m : ℕ) (b : ι) :
    (f b) ^ m ≤ ∑ i, (f i) ^ m :=
  Finset.single_le_sum (f := fun i => (f i) ^ m) (fun i _ => pow_nonneg (hf i) m)
    (Finset.mem_univ b)

/-- **The moment → sup-norm bridge (`ℓ^∞ ≤ ℓ^{2r}`).** For a nonnegative family `f` and `r ≥ 1`,
every term is bounded by the `(2r)`-th root of the `(2r)`-th power sum:

    `f b ≤ (∑_i (f i)^{2r})^{1/(2r)}`.

Instantiated at `f b = ‖η_b‖` this is `max_b‖η_b‖ ≤ (∑_b‖η_b‖^{2r})^{1/(2r)}` — the rigorous
conversion of the additive moment `E_r` into the prize sup-norm `B(μ_n)`. -/
theorem sup_le_moment_root (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) {r : ℕ} (hr : 1 ≤ r) (b : ι) :
    f b ≤ (∑ i, (f i) ^ (2 * r)) ^ ((1 : ℝ) / (2 * r)) := by
  have h2r : 0 < 2 * r := by omega
  have hsum_nonneg : 0 ≤ ∑ i, (f i) ^ (2 * r) :=
    Finset.sum_nonneg (fun i _ => pow_nonneg (hf i) _)
  -- raise the term bound `(f b)^{2r} ≤ ∑` to the power `1/(2r)`
  have hterm : (f b) ^ (2 * r) ≤ ∑ i, (f i) ^ (2 * r) := pow_le_sum_pow f hf (2 * r) b
  have hroot : ((f b) ^ (2 * r) : ℝ) ^ ((1 : ℝ) / (2 * r))
      ≤ (∑ i, (f i) ^ (2 * r)) ^ ((1 : ℝ) / (2 * r)) :=
    Real.rpow_le_rpow (pow_nonneg (hf b) _) hterm (by positivity)
  -- LHS simplifies to `f b`
  have hlhs : ((f b) ^ (2 * r) : ℝ) ^ ((1 : ℝ) / (2 * r)) = f b := by
    rw [one_div, show (2 * (r : ℝ)) = ((2 * r : ℕ) : ℝ) by push_cast; ring]
    exact Real.pow_rpow_inv_natCast (hf b) (by omega)
  rwa [hlhs] at hroot

end ArkLib.ProximityGap.MomentSupNormBridge

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.MomentSupNormBridge.sup_le_moment_root
