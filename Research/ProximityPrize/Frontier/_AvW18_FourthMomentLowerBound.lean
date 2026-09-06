/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-!
# Fourth-moment lower bound on the Paley eigenvalue M (#444)

From the "exact value" analysis (the limiting measure of `η_b/√n` is `N(0,1)`, so the conjectured
value is `M ≈ √(2 n log p)`): the matching lower bound at the `√(n log p)` scale needs the far tail
and is comparably hard to the upper bound. What IS elementary is the `√n`-scale lower bound via the
2nd and 4th moments — recorded here honestly (correctly scoped: this is `Ω(√n)`, NOT `Ω(√(n log p))`).

## The bound
For the periods `a_b = |η_b|²` over `b ≠ 0`, the ratio of the 4th to 2nd period moments lower-bounds
the max: `M² = max_b a_b ≥ (Σ_b a_b²)/(Σ_b a_b) = (Σ_b|η_b|⁴)/(Σ_b|η_b|²)`. With the in-tree exact
moments `Σ_{b≠0}|η_b|² = p·n − n²` (Parseval) and `Σ_{b≠0}|η_b|⁴ = p·E_2 − n⁴`, `E_2(μ_n) = 3n²−3n`,
this gives `M² ≥ (p(3n²−3n)−n⁴)/(pn−n²) → 3n − 3` as `p → ∞`, i.e.

> **`M(μ_n) ≥ √3·√n·(1 − o(1))`** — strictly above the trivial Parseval `√n`.

This confirms `M` exceeds `√n` (the additive energy being `3n²` rather than the Sidon `2n²` forces a
heavier max), but it is `√n`-scale; reaching the conjectured `√(n log p)` is the open far-tail
problem. The `√3` constant is the energy multiplier `E_2/n² = 3`.

## Results (axiom-clean)
* `sum_sq_le_max_mul_sum` — `Σ a_i² ≤ c·Σ a_i` when `0 ≤ a_i ≤ c` (the Cauchy–Schwarz-free max bound).
* `exists_ge_sq_sum_div_sum` — some `a_i ≥ (Σ a²)/(Σ a)`: the 4th/2nd-moment-ratio lower bound on the
  max, the abstract engine of `M² ≥ E_2/n`.

NOT prize closure — the honest `√n`-scale lower bound; the `√(n log p)` matching bound is open.
-/

namespace ArkLib.ProximityGap.Frontier.AvW18

open Finset

/-- **The max bound (proven).** For nonnegative `a : ι → ℝ` over `s` with every `a i ≤ c`,
`Σ_{i∈s} a_i² ≤ c · Σ_{i∈s} a_i` (each `a_i² ≤ c·a_i`). Contrapositive: `max a_i ≥ (Σa²)/(Σa)`. -/
theorem sum_sq_le_max_mul_sum {ι : Type*} (s : Finset ι) (a : ι → ℝ) (c : ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hc : ∀ i ∈ s, a i ≤ c) :
    ∑ i ∈ s, (a i) ^ 2 ≤ c * ∑ i ∈ s, a i := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun i hi => ?_)
  have h0 := ha i hi
  have h1 := hc i hi
  nlinarith [h0, h1]

/-- **The 4th/2nd-moment-ratio lower bound on the max (proven).** If `Σ_{i∈s} a_i > 0` and all
`a_i ≥ 0`, then some `a_i ≥ (Σ a²)/(Σ a)`. (Take `c = max a`; `sum_sq_le_max_mul_sum` gives
`Σa² ≤ (max a)·Σa`, so `max a ≥ Σa²/Σa`, and the max is attained.) Specialized to `a_b = |η_b|²`,
`b ≠ 0`: `M² = max|η_b|² ≥ (Σ|η_b|⁴)/(Σ|η_b|²) = E_2/n·(1−o(1)) = 3n·(1−o(1))`. -/
theorem exists_ge_sq_sum_div_sum {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (hne : s.Nonempty) (ha : ∀ i ∈ s, 0 ≤ a i) (hpos : 0 < ∑ i ∈ s, a i) :
    ∃ i ∈ s, (∑ j ∈ s, (a j) ^ 2) / (∑ j ∈ s, a j) ≤ a i := by
  obtain ⟨i₀, hi₀, hmax⟩ := s.exists_max_image a hne
  refine ⟨i₀, hi₀, ?_⟩
  rw [div_le_iff₀ hpos]
  calc ∑ j ∈ s, (a j) ^ 2 ≤ a i₀ * ∑ j ∈ s, a j :=
        sum_sq_le_max_mul_sum s a (a i₀) ha (fun j hj => hmax j hj)
    _ = a i₀ * ∑ j ∈ s, a j := rfl

end ArkLib.ProximityGap.Frontier.AvW18

/-! ## Axiom audit (expected: only `propext, Classical.choice, Quot.sound`; no `sorryAx`) -/
#print axioms ArkLib.ProximityGap.Frontier.AvW18.sum_sq_le_max_mul_sum
#print axioms ArkLib.ProximityGap.Frontier.AvW18.exists_ge_sq_sum_div_sum
