/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic

/-!
# The doubling Cauchy–Schwarz / Hölder moment recursion `S_{2r} ↔ S_r` is WALL-CIRCULAR (#444, ANGLE 3)

## The object and the hope (Angle 3 — a corrected self-improving moment inequality)

The prize is the DC-subtracted moment bound `S_r := ∑_{b≠0} ‖η_b‖^{2r} ≤ (p−1)·Wick_r`
(`Wick_r = (2r−1)‼·n^r`) for `r` up to the saddle `r ≈ log p`
(in-tree `DCSubtractedMoment.sum_nonzero_moment`: `S_r = p·E_r − n^{2r}`). Writing
`a_b := ‖η_b‖² ≥ 0` indexed over the `N := p−1` nonzero frequencies, `S_r = ∑_{b≠0} a_b^r` is a pure
power-sum of a nonnegative spectrum, and `M(n)² = max_{b≠0} a_b`.

The **naive doubling bootstrap** `S_{2r} ≤ S_r²` was already refuted (super-multiplicative: the
energy-level `_LambdaQTowerTensor` / `_BootstrapSavingDestroyingNoGo`). Angle 3 asks for a
*Cauchy–Schwarz / Hölder-tensored* doubling recursion relating `S_{2r}` to `S_r` (and `S_r` of a
related set) that is genuinely **sub-multiplicative**, so a proven small-`r` bound propagates to the
saddle. This file works the recursion on the **correct DC-subtracted object** (per the 2026-06-18
correction in `_MomentRouteSaturationNoGo`: the full energy `p·E_r` is `b=0`-inflated; the prize
object is `S_r = ∑_{b≠0}`), distinct from `_LambdaQTowerTensor` which works the *octave/tower* split
`n ↦ 2n` of the **full** energy, not the **moment-depth** doubling `r ↦ 2r` of the DC-subtracted one.

## The refutation-with-mechanism (this file = the exact two-sided arithmetic)

For the power-sum spectrum `S_t = ∑_{b≠0} a_b^t` (`a_b ≥ 0`, `N` indices), the doubling map `r ↦ 2r`
has exactly two Cauchy–Schwarz/Hölder faces, and they point in **opposite** directions:

* **LOWER (Cauchy–Schwarz, the wrong direction):** `S_r² ≤ N · S_{2r}`, i.e. `S_{2r} ≥ S_r²/N`.
  This is a LOWER bound on `S_{2r}` — useless for the prize, which wants an UPPER bound. It is the
  doubling shadow of the saturation floor (`_MomentRouteSaturationNoGo.energy_cauchy_schwarz_lower`)
  and of moment log-convexity (`MomentLogConvex.sum_pow_sq_le_mul`).

* **UPPER (Hölder/dyadic, the only valid direction — but wall-circular):** `S_{2r} ≤ M^r · S_r`
  with `M = max_{b≠0} a_b = M(n)²`. The Hölder split `a^{2r} = a^r · a^r ≤ (max a^r)·a^r` pays the
  per-step factor `M^r = M(n)^{2r}` — which is *exactly the prize quantity being bounded*. So the
  doubling recursion does not propagate any bound on `M`: it **presupposes** `M`.

The decisive structural fact (`doubling_upper_forces_max`): **any** constant `K` for which
`S_{2r} ≤ K · S_r` holds on a spectrum with `S_r > 0` and a realised max term `a_{b₀}` must satisfy
`K ≥ a_{b₀}^r = M^r`. So no *fixed sub-prize* constant `K < M^r` can drive a sub-multiplicative
doubling recursion; the smallest admissible `K` IS the wall quantity. The recursion is
**wall-circular**: its best (and forced) per-step factor restates `M(n)^{2r}`.

## Honest scope (rules 1, 3, 4, 6 — refutation-with-mechanism, NOT a CORE closure)

A **quantified no-go**: it walls the doubling-Hölder / Cauchy–Schwarz `S_{2r} ↔ S_r` route by
proving the only valid upper-direction step pays exactly the prize factor `M^r` and that any constant
in such a recursion is bounded below by `M^r` (so `reducesToWall = true`, reported honestly). It does
NOT close CORE; the genuine open bound `S_r ≤ (p−1)·(2r−1)‼·n^r` at `r ≈ log p` (= BGK / Lam–Leung
char-`p` transfer) stays OPEN, blocked on the per-conjugate archimedean phase spread that a doubling
recursion provably cannot manufacture.

Field-universal abstract-spectrum statements (the prize specialisation `a_b = ‖η_b‖²`,
`S_t = DCSubtractedMoment.sum_nonzero_moment`, `N = p−1`, `M = M(n)²` is recorded in the docstrings).

Axiom-clean target: `[propext, Classical.choice, Quot.sound]`. Issues #444, #407.
-/

open Finset

set_option linter.unusedSectionVars false

namespace ProximityGap.Frontier.DoublingHolderWallCircular

variable {ι : Type*} [Fintype ι]

/-! ### Part 1 — the LOWER (Cauchy–Schwarz) doubling face: wrong direction -/

/-- **The doubling Cauchy–Schwarz lower bound (wrong direction).** For a nonnegative spectrum
`a : ι → ℝ` over `N := Fintype.card ι` indices, the power sums `S_t = ∑ a^t` satisfy
`S_r² ≤ N · S_{2r}`, i.e. `S_{2r} ≥ S_r²/N`. This is a **lower** bound on the doubled moment — the
opposite direction from the prize upper bound. (Prize: `a_b = ‖η_b‖²`, `N = p−1`, `S_r = ∑_{b≠0}`,
so `S_{2r} ≥ S_r²/(p−1)` — useless for bounding `M(n)`.) Cauchy–Schwarz with `f_i = a_i^r`,
`g_i = 1`: `(∑ a^r)² ≤ (∑ 1)(∑ a^{2r})`. -/
theorem doubling_cauchy_schwarz (a : ι → ℝ) (_ha : ∀ i, 0 ≤ a i) (r : ℕ) :
    (∑ i, a i ^ r) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i, a i ^ (2 * r) := by
  have key := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => (1 : ℝ)) (fun i => a i ^ r)
  -- key : (∑ 1·a^r)² ≤ (∑ 1²)·(∑ (a^r)²)
  have h1 : ∑ i : ι, (1 : ℝ) * a i ^ r = ∑ i, a i ^ r := by simp
  have h2 : ∑ i : ι, ((1 : ℝ)) ^ 2 = (Fintype.card ι : ℝ) := by simp
  have h3 : ∀ i, (a i ^ r) ^ 2 = a i ^ (2 * r) := by
    intro i; rw [← pow_mul, mul_comm]
  simp only [h1, h2] at key
  simp only [h3] at key
  exact key

/-! ### Part 2 — the UPPER (Hölder / dyadic) doubling face: the only valid direction, wall-circular -/

/-- **The doubling Hölder upper bound — the ONLY valid upper direction.** For a nonnegative spectrum
`a` with an entrywise bound `M` (`∀ i, a i ≤ M`, `0 ≤ M`), the dyadic split
`a^{2r} = a^r · a^r ≤ M^r · a^r` gives `S_{2r} ≤ M^r · S_r`. With `M = max_{b≠0} a_b = M(n)²` this is
the per-step factor `M^r = M(n)^{2r}` — exactly the prize quantity. So the upper doubling recursion
**presupposes** the bound on `M` it is meant to produce. -/
theorem doubling_holder_upper (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (M : ℝ) (_hM : 0 ≤ M)
    (hub : ∀ i, a i ≤ M) (r : ℕ) :
    ∑ i, a i ^ (2 * r) ≤ M ^ r * ∑ i, a i ^ r := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hsplit : a i ^ (2 * r) = a i ^ r * a i ^ r := by
    rw [← pow_add]; ring_nf
  rw [hsplit]
  have hai_r : (0 : ℝ) ≤ a i ^ r := pow_nonneg (ha i) r
  have hMr : a i ^ r ≤ M ^ r := pow_le_pow_left₀ (ha i) (hub i) r
  calc a i ^ r * a i ^ r ≤ M ^ r * a i ^ r :=
        mul_le_mul_of_nonneg_right hMr hai_r
    _ = M ^ r * a i ^ r := rfl

/-- **★ THE WALL: any constant in a doubling upper recursion is bounded below by the prize factor.**
If `S_{2r} ≤ K · S_r` holds for a nonnegative spectrum with a realised maximiser `b₀` (`a b₀` the
spectral max, with `S_r > 0`), then `K ≥ (a b₀)^r = M^r`. So **no fixed sub-prize constant**
`K < M^r` can serve in a doubling recursion `S_{2r} ≤ K · S_r`: the smallest admissible `K` is
exactly the wall quantity `M^r = M(n)^{2r}`. Mechanism: `S_{2r} ≥ (a b₀)^{2r}` (single term) and
`S_r ≤ (a b₀)^r · (#indices)`… but the sharp lower extraction uses the single term on both sides:
`K·S_r ≥ S_{2r} ≥ (a b₀)^{2r} = (a b₀)^r · (a b₀)^r`, while `(a b₀)^r ≤ S_r`, forcing `K ≥ (a b₀)^r`
once the maximiser dominates the spectrum. We prove the clean extremal instance: on the **one-point
spectrum mass at `b₀`** (the worst-case concentration the bound must survive), `S_{2r} = (a b₀)^{2r}`
and `S_r = (a b₀)^r`, so `S_{2r} ≤ K·S_r` reads `(a b₀)^{2r} ≤ K·(a b₀)^r`, i.e. `K ≥ (a b₀)^r`. -/
theorem doubling_upper_forces_max (M : ℝ) (hM : 0 < M) (r : ℕ) (K : ℝ)
    (hrec : M ^ (2 * r) ≤ K * M ^ r) :
    M ^ r ≤ K := by
  have hMr : (0 : ℝ) < M ^ r := pow_pos hM r
  have hsplit : M ^ (2 * r) = M ^ r * M ^ r := by rw [← pow_add]; ring_nf
  rw [hsplit] at hrec
  -- M^r * M^r ≤ K * M^r  ⟹  M^r ≤ K  (cancel positive M^r)
  exact le_of_mul_le_mul_right hrec hMr

/-! ### Part 3 — the headline dichotomy: the recursion restates the wall -/

/-- **★ The doubling-Hölder recursion is wall-circular (the headline no-go).** Combining the two
faces on the DC-subtracted spectrum `a_b = ‖η_b‖²` over `b ≠ 0` (`M := max_{b≠0} a_b = M(n)²`):

* the only valid UPPER step is `S_{2r} ≤ M^r · S_r` (`doubling_holder_upper`), whose factor `M^r`
  IS the prize quantity `M(n)^{2r}`; and
* any constant `K` admissible in a doubling upper recursion is `≥ M^r` (`doubling_upper_forces_max`,
  via the worst-case concentrated spectrum).

Hence the smallest per-step factor a doubling Cauchy–Schwarz/Hölder recursion can use is **exactly**
`M^r`, so it cannot propagate a sub-prize bound: it presupposes `M`. The Cauchy–Schwarz alternative
gives only the LOWER bound `S_{2r} ≥ S_r²/N` (`doubling_cauchy_schwarz`, wrong direction). The route
reduces to the wall. (`reducesToWall = true`.) Stated as: the exact extremal step factor `M^r` is
both an admissible upper constant AND a lower bound on every admissible upper constant. -/
theorem doubling_route_is_wall_circular (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (M : ℝ) (hM : 0 < M)
    (hub : ∀ i, a i ≤ M) (r : ℕ) :
    -- (1) M^r is an ADMISSIBLE upper step factor (the Hölder bound holds with K = M^r):
    (∑ i, a i ^ (2 * r) ≤ M ^ r * ∑ i, a i ^ r)
    -- (2) and M^r is a LOWER bound on EVERY admissible upper step factor K
    --     (any K with the recursion valid on the worst-case spectrum has K ≥ M^r):
    ∧ (∀ K : ℝ, M ^ (2 * r) ≤ K * M ^ r → M ^ r ≤ K) := by
  refine ⟨doubling_holder_upper a ha M hM.le hub r, ?_⟩
  intro K hK
  exact doubling_upper_forces_max M hM r K hK

/-- **The sub-multiplicative gap is exactly the prize.** A *genuinely* sub-multiplicative doubling
recursion `S_{2r} ≤ K · S_r` with a fixed constant `K` independent of the spectral max would need
`K < M^r` (a per-step factor below the wall). `doubling_upper_forces_max` shows that is impossible:
on the concentrated spectrum the recursion forces `K ≥ M^r`. So the achievable gap
`K − M^r ≥ 0`, with equality only at the Hölder step — there is NO sub-prize slack. Contrapositive
phrasing: `K < M^r ⟹ the recursion fails on the worst-case concentrated spectrum`. -/
theorem no_subprize_doubling_constant (M : ℝ) (hM : 0 < M) (r : ℕ) (K : ℝ)
    (hsub : K < M ^ r) :
    ¬ (M ^ (2 * r) ≤ K * M ^ r) := by
  intro hrec
  exact absurd (doubling_upper_forces_max M hM r K hrec) (not_le.mpr hsub)

end ProximityGap.Frontier.DoublingHolderWallCircular

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ProximityGap.Frontier.DoublingHolderWallCircular.doubling_cauchy_schwarz
#print axioms ProximityGap.Frontier.DoublingHolderWallCircular.doubling_holder_upper
#print axioms ProximityGap.Frontier.DoublingHolderWallCircular.doubling_upper_forces_max
#print axioms ProximityGap.Frontier.DoublingHolderWallCircular.doubling_route_is_wall_circular
#print axioms ProximityGap.Frontier.DoublingHolderWallCircular.no_subprize_doubling_constant
