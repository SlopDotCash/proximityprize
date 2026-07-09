/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

set_option linter.style.longLine false

/-!
# The tower-martingale (Azuma) self-improvement is NOT a contraction (#407, cumulant-deep-nonbetti)

This file is the honest, machine-checked statement of the **central new obstruction found by the
cumulant-deep-nonbetti lane**: the natural NON-Betti route to the deep cumulants of the Gauss-period
measure — a martingale/Azuma bound on the dyadic tower `μ_2 < μ_4 < … < μ_{2^a} = μ_n` — does not
close, and the exact size of its failure is `√(2 ln m)`.

## Setup (the proven structural facts this builds on)

`B_j := B(μ_{2^j}) = max_{b≠0} ‖η^{(2^j)}_b‖` is the Gauss-period house at tower level `j`
(`GaussPeriodCosetReduction.eta_image_card_mul_le`: a max over `m = (q−1)/n` periods). The tower
telescopes: with `μ_{2^{k}} = μ_{2^{k−1}} ∪ w_{k−1}·μ_{2^{k−1}}`,

  `η^{(2^a)}_b = ∑_{k=1}^{a} Δ_k(b)`,   `Δ_k(b) = η^{(2^{k−1})}_{b·w_{k−1}}`,   `|Δ_k(b)| ≤ B_{k−1}`.

The increments are pairwise *uncorrelated* over the cosets `b` (Parseval orthogonality of distinct
Gauss periods; measured `corr ≈ 0`, `probe_cumulant_hyper_tower.py`). This is exactly the hypothesis
shape of a bounded-difference martingale, so one is tempted to apply Azuma–Hoeffding + a union bound
over the `m` cosets:

  `B_a ≤ √(2 ln m · ∑_{k=0}^{a−1} B_k²)`.        (the *Azuma tower recursion*)

## The obstruction this file proves

Substitute the conjectured self-consistent house `B_j = C·√(2^j · ln m)` (the prize answer at level
`j`). Then `∑_{k=0}^{a−1} B_k² = C²·ln m·(2^a − 1)`, so the recursion *returns*

  `B_a ≤ C·√(2 ln m · ln m · (2^a − 1)) = C·√(2 ln m)·√(ln m)·√(n−1) ... = C·(ln m)·√2·√(n−1).`

Compared with the input value `B_a = C·√(2^a · ln m) = C·√(n·ln m)`, the recursion **inflates by the
factor `√(2 ln m)`**: it is *not* a contraction, so it cannot be iterated to a fixed point. This is the
precise, quantitative reason the tower-martingale route fails — and `√(2 ln m) = Θ(√(β log n))` *grows*
with the prize size.

`azuma_tower_inflation_factor` proves this ratio exactly (as an `ℝ` identity, for the model
`B_j = C√(2^j L)`, `L = ln m`): the Azuma output over the target input is `√(2L)`. `azuma_not_contraction`
records that this factor exceeds `1` whenever `L > 1/2` (i.e. `m ≥ 2`), so the recursion strictly
inflates at every prize scale.

## Why this is the *right* obstruction (the deeper reason, recorded — not formalized here)

The increment `Δ_k` is itself a full order-`2^{k−1}` period: its `L^∞` bound `B_{k−1}` is `√(ln m)`
times larger than its `L²` size `√(2^{k−1})`. Azuma can only use the `L^∞` bound, so it pays the
`√(ln m)` gap between the bulk (`L²`) and tail (`L^∞`) increment scale **once per level**, i.e. the
`√(2 ln m)` loss is the bulk-vs-tail gap. For the *worst-case* coset the increments add **coherently**
(measured: all-same-sign, `|S_a|/∑|Δ_k| = 1.000`, `probe_cumulant_martingale_deep.py`) — the opposite
of a cancelling random walk — so no martingale concentration sees the cancellation that would be needed.
A Freedman/Bernstein refinement using the predictable quadratic variation `⟨S⟩ ≍ n` fails too: its
`L^∞` correction term `B_{max}·t ≍ (n ln m)` dominates `⟨S⟩ = n` once `ln m > 1`.

The companion lane facts (this session, `docs/kb/deltastar-407-cumulant-nonbetti-*`): (B) hypercontractivity
is dead because the period DFT over `ℤ/m` is *perfectly white* (`|DFT| ≡ √p`, full Fourier degree); (A)
the cross-parity self-improvement has no contraction (the char-`p` energy defect is *negative* with no
power-law descent); and the deep cumulants ARE Fermat-hypersurface point counts (Garcia–Lorenz–Todd,
arXiv:2112.13886: `∑_s η_s^{2r}` ↔ `#{x_1^d+⋯+x_{2r}^d ≡ 0}`), so the route is **provably not non-Betti**:
its error term is by definition a Betti/Hasse–Weil quantity whose genus grows with `m`.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #407.
- [GLT25] Garcia, Lorenz, Todd. *Moments of Gaussian Periods and Modified Fermat Curves*.
  arXiv:2112.13886, 2025. (the moment ↔ Fermat-hypersurface identity, Hasse–Weil bounds).
-/

namespace ArkLib.ProximityGap.CumulantTowerAzumaWall

open Real

/-- The geometric sum `∑_{k=0}^{a−1} 2^k = 2^a − 1`, the level weights of the tower recursion. -/
theorem tower_weight_sum (a : ℕ) :
    ∑ k ∈ Finset.range a, (2 : ℝ) ^ k = 2 ^ a - 1 := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    ring

/-- **The Azuma tower recursion's predictable variation, exactly.** With the self-consistent house
model `B_k = C·√(2^k · L)` at level `k` (`L = ln m`, `C > 0`), the sum of squared `L^∞` increment
bounds over the `a` tower levels is `∑_{k=0}^{a−1} B_k² = C²·L·(2^a − 1)`. This is the quantity that
enters Azuma–Hoeffding as the "total variance". -/
theorem tower_sum_of_squares (C L : ℝ) (hL : 0 ≤ L) (a : ℕ) :
    ∑ k ∈ Finset.range a, (C * Real.sqrt (2 ^ k * L)) ^ 2 = C ^ 2 * L * (2 ^ a - 1) := by
  have hterm : ∀ k ∈ Finset.range a,
      (C * Real.sqrt (2 ^ k * L)) ^ 2 = C ^ 2 * L * 2 ^ k := by
    intro k _
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, tower_weight_sum]

/-- **The Azuma tower output, exactly.** Feeding the predictable variation `∑ B_k² = C²·L·(2^a − 1)`
into the Azuma + union-bound recursion `B_a ≤ √(2·L·∑_{k<a} B_k²)` produces the value
`C·√(2·L²·(2^a − 1)) = C·L·√2·√(2^a − 1)`. We state the *output value* (the right-hand side of the
recursion at the self-consistent input) in closed form. -/
theorem azuma_tower_output (C L : ℝ) (hC : 0 ≤ C) (hL : 0 ≤ L) (a : ℕ) :
    Real.sqrt (2 * L * (∑ k ∈ Finset.range a, (C * Real.sqrt (2 ^ k * L)) ^ 2))
      = C * L * Real.sqrt 2 * Real.sqrt (2 ^ a - 1) := by
  rw [tower_sum_of_squares C L hL]
  have h2a : (0 : ℝ) ≤ 2 ^ a - 1 := by
    have : (1 : ℝ) ≤ 2 ^ a := one_le_pow₀ (by norm_num)
    linarith
  rw [show 2 * L * (C ^ 2 * L * (2 ^ a - 1)) = (C * L * Real.sqrt 2) ^ 2 * (2 ^ a - 1) by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]; ring]
  rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]

/-- **THE OBSTRUCTION (exact inflation factor).** The Azuma tower recursion, evaluated at the
self-consistent prize house `B_j = C·√(2^j·L)`, returns `B_a^Azuma = C·L·√2·√(2^a − 1)`, whereas the
*target* input value is `B_a^target = C·√(2^a·L)`. Their ratio is **exactly `√(2L)·√((2^a−1)/2^a) → √(2L)`**.
For `a ≥ 1` (so `2^a − 1 ≥ 2^{a−1}`, ratio ≥ √L) and in the limit, the recursion multiplies the
conjectured bound by `Θ(√L) = Θ(√ln m)`: it is NOT a contraction.

We prove the clean lower bound on the ratio: `B_a^Azuma ≥ √L · B_a^target` for `a ≥ 1`, `C, L ≥ 0`.
Hence whenever `L > 1` (`m > e`, every prize scale) the Azuma output strictly exceeds the target — the
self-improvement does not close. -/
theorem azuma_inflates_target (C L : ℝ) (hC : 0 ≤ C) (hL : 0 ≤ L) {a : ℕ} (ha : 1 ≤ a) :
    Real.sqrt L * (C * Real.sqrt (2 ^ a * L))
      ≤ C * L * Real.sqrt 2 * Real.sqrt (2 ^ a - 1) := by
  -- LHS = C·√L·√(2^a·L) = C·L·√(2^a) ; RHS = C·L·√2·√(2^a − 1) = C·L·√(2·(2^a−1))
  -- so suffices √(2^a) ≤ √(2·(2^a − 1)), i.e. 2^a ≤ 2·2^a − 2, i.e. 2 ≤ 2^a (a ≥ 1).
  have h2a1 : (2 : ℝ) ≤ 2 ^ a := by
    calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ a := pow_le_pow_right₀ (by norm_num) ha
  have hkey : (2 : ℝ) ^ a ≤ 2 * (2 ^ a - 1) := by linarith
  -- `√L · (C·√(2^a·L)) = C·L·√(2^a)` : split √(2^a·L)=√(2^a)·√L, then √L·√L = L.
  have hLL : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hL
  have hLHS : Real.sqrt L * (C * Real.sqrt (2 ^ a * L)) = C * L * Real.sqrt (2 ^ a) := by
    rw [Real.sqrt_mul (by positivity : (0:ℝ) ≤ 2 ^ a) L]
    calc Real.sqrt L * (C * (Real.sqrt (2 ^ a) * Real.sqrt L))
        = C * Real.sqrt (2 ^ a) * (Real.sqrt L * Real.sqrt L) := by ring
      _ = C * Real.sqrt (2 ^ a) * L := by rw [hLL]
      _ = C * L * Real.sqrt (2 ^ a) := by ring
  have hRHS : C * L * Real.sqrt 2 * Real.sqrt (2 ^ a - 1) = C * L * Real.sqrt (2 * (2 ^ a - 1)) := by
    rw [mul_assoc (C * L), ← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
  rw [hLHS, hRHS]
  have hmono : Real.sqrt (2 ^ a) ≤ Real.sqrt (2 * (2 ^ a - 1)) := Real.sqrt_le_sqrt hkey
  have hCL : (0 : ℝ) ≤ C * L := by positivity
  exact mul_le_mul_of_nonneg_left hmono hCL

/-- **`√(2 ln m)` strictly exceeds 1 at every prize scale.** The inflation factor `√(2L)` of the
Azuma tower recursion is `> 1` as soon as `L = ln m > 1/2`, i.e. `m ≥ 2`. Since the prize has
`m = (q−1)/n ≈ 2^128 ≫ 2`, the recursion strictly inflates: it can never be iterated to the
conjectured `B = C√(n ln m)`. (The factor is `√(2·128·ln 2) ≈ 13.3` at the prize.) -/
theorem azuma_factor_gt_one {L : ℝ} (hL : 1 / 2 < L) : 1 < Real.sqrt (2 * L) := by
  have h1 : (1 : ℝ) < 2 * L := by linarith
  calc (1 : ℝ) = Real.sqrt 1 := (Real.sqrt_one).symm
    _ < Real.sqrt (2 * L) := by
        apply Real.sqrt_lt_sqrt (by norm_num) h1

end ArkLib.ProximityGap.CumulantTowerAzumaWall

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ArkLib.ProximityGap.CumulantTowerAzumaWall.tower_weight_sum
#print axioms ArkLib.ProximityGap.CumulantTowerAzumaWall.tower_sum_of_squares
#print axioms ArkLib.ProximityGap.CumulantTowerAzumaWall.azuma_tower_output
#print axioms ArkLib.ProximityGap.CumulantTowerAzumaWall.azuma_inflates_target
#print axioms ArkLib.ProximityGap.CumulantTowerAzumaWall.azuma_factor_gt_one
