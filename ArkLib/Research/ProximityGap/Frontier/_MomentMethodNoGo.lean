/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# The moment-method no-go for the proximity-prize floor (#407)

The prize floor needs a worst-case sup-norm bound on incomplete character sums over a
multiplicative subgroup `μ_n ⊊ F_p*`: `B := max_b |∑_{x∈μ_n} e_p(bx)| ≲ √(n·log(q/n))`
(square-root cancellation, the Paley-graph / Ramanujan regime).

Every additive-moment / energy route bounds `B` through the `2r`-th moment identity
`∑_b |Ŝ(b)|^{2r} = p · E_r`, where `E_r = #{(x,y) ∈ μ_n^{2r} : ∑x = ∑y}` is the `r`-fold
additive energy, giving `B ≤ (p · E_r)^{1/2r}`.  This file proves, axiom-clean and
**unconditionally**, that this route can **never** beat the trivial bound `n`:

* `card_sq_le_card_mul_energy` — the Cauchy–Schwarz floor `n^{2r} ≤ p · E_r`
  (`E_r = ∑_s c_s²` with `∑_s c_s = n^r` spread over `≤ p` sums).
* `moment_bound_ge_card` — hence `(p · E_r)^{1/2r} ≥ n`: the moment upper bound on `B` is
  always `≥ n`.

So no additive-moment argument of any order `r` can prove `B < n`, let alone `B ≲ √n`.  This
turns the issue's "the L² hierarchy is exhausted (Johnson ceiling, `n^{1/2}` deficit)" into a
machine-checked theorem: the prize floor genuinely requires an L^∞/phase-cancellation argument,
not any L² mass bound.  (It does **not** prove the floor — that remains the open
square-root-cancellation problem.)

Issue #407.
-/

open Finset

namespace ProximityGap.Frontier.MomentMethodNoGo

/-- **Cauchy–Schwarz energy floor.**  If a count function `c : σ → ℝ≥0`-style (here `ℝ`, with
`0 ≤ c`) has total mass `M = ∑_s c s` supported on a type of cardinality `p`, then the energy
`∑_s (c s)^2 ≥ M^2 / p`, equivalently `M^2 ≤ p · ∑_s (c s)^2`.  Instantiated with
`M = n^r` (the number of `r`-tuples from `μ_n`) and `p = |F_p|`, this is `n^{2r} ≤ p · E_r`. -/
theorem card_sq_le_card_mul_energy {σ : Type*} [Fintype σ] (c : σ → ℝ)
    (M : ℝ) (hM : ∑ s, c s = M) :
    M ^ 2 ≤ (Fintype.card σ : ℝ) * ∑ s, (c s) ^ 2 := by
  have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset σ)) (f := c)
  rw [hM] at h
  simpa [Finset.card_univ] using h

/-- **The moment-method bound can never beat `n`.**  With `E = ∑_s (c s)^2` the `r`-fold
additive energy (`c s` = number of `r`-tuples from a set of size `n` summing to `s`, so
`∑_s c s = n^r`), the moment upper bound `(p · E)^{1/(2r)} ≥ n`.  Stated on the squared form to
stay elementary: `(n : ℝ)^(2*r) ≤ p · E`. -/
theorem energy_ge_card_pow {σ : Type*} [Fintype σ] (c : σ → ℝ) (n r : ℕ)
    (hcount : ∑ s, c s = (n : ℝ) ^ r) :
    (n : ℝ) ^ (2 * r) ≤ (Fintype.card σ : ℝ) * ∑ s, (c s) ^ 2 := by
  have h := card_sq_le_card_mul_energy c ((n : ℝ) ^ r) hcount
  calc (n : ℝ) ^ (2 * r) = ((n : ℝ) ^ r) ^ 2 := by rw [← pow_mul, Nat.mul_comm]
    _ ≤ (Fintype.card σ : ℝ) * ∑ s, (c s) ^ 2 := h

/-- **The moment bound is `≥ n` (the route is dead).**  For `p ≥ 1` and energy
`E = ∑_s (c s)^2` with `∑_s c s = n^r`, the `2r`-th-root moment bound `(p · E)^{1/(2r)} ≥ n`.
Hence the additive-moment method cannot certify `B < n`. -/
theorem moment_bound_ge_card {σ : Type*} [Fintype σ] (c : σ → ℝ) (n r : ℕ) (hr : 0 < r)
    (hcount : ∑ s, c s = (n : ℝ) ^ r) :
    (n : ℝ) ≤ ((Fintype.card σ : ℝ) * ∑ s, (c s) ^ 2) ^ ((((2 * r : ℕ) : ℝ))⁻¹) := by
  have hpow : (n : ℝ) ^ (2 * r) ≤ (Fintype.card σ : ℝ) * ∑ s, (c s) ^ 2 :=
    energy_ge_card_pow c n r hcount
  have hbase : (0 : ℝ) ≤ (n : ℝ) ^ (2 * r) := by positivity
  have hexp : (0 : ℝ) ≤ (((2 * r : ℕ) : ℝ))⁻¹ := by positivity
  have hmono := Real.rpow_le_rpow hbase hpow hexp
  have hlhs : ((n : ℝ) ^ (2 * r)) ^ (((2 * r : ℕ) : ℝ))⁻¹ = (n : ℝ) :=
    Real.pow_rpow_inv_natCast (by positivity) (by omega)
  rwa [hlhs] at hmono

end ProximityGap.Frontier.MomentMethodNoGo

#print axioms ProximityGap.Frontier.MomentMethodNoGo.card_sq_le_card_mul_energy
#print axioms ProximityGap.Frontier.MomentMethodNoGo.moment_bound_ge_card
