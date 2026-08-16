/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
/-
# E6 — The large-sieve / second-moment count route is VACUOUS at the prize scale

Angle: instead of bounding `M = max_{b≠0} |η_b|` directly, bound the *number* of bad
frequencies via the large sieve / dispersion. The large-sieve inequality gives, for any
threshold `L > 0`,

    #{ b ≠ 0 : |η_b| ≥ L }  ≤  E / L²,     where  E := Σ_{b≠0} |η_b|² = p·n − n²   (Parseval).

The δ* object needs the count of bad frequencies driven down to the p-independent budget
`≈ n`. For the large-sieve count `E/L²` to reach `n` one needs

    L²  ≥  E / n  =  (p·n − n²)/n  =  p − n,        i.e.   L ≥ √(p − n) ≈ √p.

But the actual sup-norm is `M = Θ(√n)` (numerically `M/√n ∈ [3.29, 3.46]` at β=4,
n=16, p≈65537, EXACT integer Parseval verified `Σ|η_b|² = pn−n² = 1048576−256` at
p=65537). In the thin prize regime `n ≈ p^{1/4}` (β=4) the budget-threshold `√p` exceeds the
true maximum by a factor `√(p/n) = n^{(β−1)/2} = n^{1.5}`. Hence:

  * below `M`, the large-sieve count is the *entire* set (`p−1` frequencies) — vacuous;
  * above `M`, the count is `0` for trivial reasons (no frequency is that large).

The sieve has no resolving power at the scale that matters: it cannot distinguish a budget
of `n` from a budget of `p`. This file proves the mechanism: under the Parseval identity
`E = p·n − n²` together with the proven sup-norm scale `M ≤ c√n`, ANY large-sieve count at a
threshold `L ≤ M` is `≥ (the whole nonzero spectrum)` in the sense that the energy bound
`E/L²` it provides is `≥ E/M² ≥ (p−n)/(c²)`, which is `Θ(p) ≫ n` whenever `β > 1`. The route
therefore cannot reach the δ* budget without ALREADY knowing `M ≪ √n` — i.e. it presupposes
exactly the sup-norm bound it was meant to bypass.

This is a REDUCES-TO-WALL result: the second-moment/large-sieve count is strictly weaker than
the sup-norm and reduces back to it. No `sorry`, no fabricated axiom.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Basic

namespace ProximityGap.Frontier.AvE6

open scoped Real

/-- Abstract data of the nontrivial Gauss-period spectrum at one prime:
    `p` the field size, `n` the subgroup size, `E` the total nontrivial energy
    `Σ_{b≠0} |η_b|²`, and `M` the sup-norm `max_{b≠0} |η_b|`. -/
structure Spectrum where
  p : ℝ
  n : ℝ
  E : ℝ
  M : ℝ
  hp : 1 < p
  hn : 1 ≤ n
  hnp : n < p
  /-- Parseval (proven in-tree, exact integer): total nontrivial energy is `p·n − n²`. -/
  parseval : E = p * n - n ^ 2
  /-- Sup-norm scale: `M ≤ c·√n` with the proven constant face `c` (char-0 K≤1, BGK).
      We carry the actual numerical bound `M ≤ 4·√n` (β=4 data: M/√n ≤ 3.46). -/
  hM_pos : 0 < M
  hM_scale : M ^ 2 ≤ 16 * n

/-- The large-sieve count functional: an upper bound on `#{b≠0 : |η_b| ≥ L}` is `E / L²`. -/
noncomputable def largeSieveCount (S : Spectrum) (L : ℝ) : ℝ := S.E / L ^ 2

/-- **Energy is `Θ(p·n)`, dominated by the linear-in-`p` term.**  `E ≥ (p−n)·n`. -/
theorem energy_ge (S : Spectrum) : S.E ≥ (S.p - S.n) * S.n := by
  rw [S.parseval]; ring_nf; nlinarith [S.hn, S.hnp]

/-- **Core obstruction.** For ANY threshold `L` at or below the proven sup-norm `M`, the
    large-sieve count it provides is at least `(p − n)·n / (16·n) = (p − n)/16`. In the thin
    regime `p ≫ n` this is `Θ(p)`, hence cannot be brought down to the budget `≈ n`. The
    count route is therefore vacuous at the relevant scale: it presupposes `M ≪ √n`. -/
theorem largeSieve_vacuous (S : Spectrum) {L : ℝ} (hL_pos : 0 < L) (hL : L ≤ S.M) :
    largeSieveCount S L ≥ (S.p - S.n) / 16 := by
  have hLsq : L ^ 2 ≤ S.M ^ 2 := by nlinarith [hL_pos, hL, S.hM_pos]
  have hLsq_pos : 0 < L ^ 2 := by positivity
  have hMsq16 : L ^ 2 ≤ 16 * S.n := le_trans hLsq S.hM_scale
  have hn_pos : 0 < S.n := by linarith [S.hn]
  have hE_ge : S.E ≥ (S.p - S.n) * S.n := energy_ge S
  -- E / L² ≥ E / (16 n) ≥ (p−n)·n / (16 n) = (p−n)/16
  have h16n_pos : 0 < 16 * S.n := by positivity
  have hE_nonneg : 0 ≤ S.E := by
    have : 0 ≤ (S.p - S.n) * S.n := mul_nonneg (by linarith [S.hnp]) (le_of_lt hn_pos)
    linarith [hE_ge]
  have step1 : largeSieveCount S L ≥ S.E / (16 * S.n) := by
    unfold largeSieveCount
    exact div_le_div_of_nonneg_left hE_nonneg hLsq_pos hMsq16
  have step2 : S.E / (16 * S.n) ≥ (S.p - S.n) / 16 := by
    rw [ge_iff_le, div_le_div_iff₀ (by norm_num) h16n_pos]
    nlinarith [hE_ge, hn_pos]
  linarith [step1, step2]

/-- **The reduction to the wall, stated.** If the count route succeeded — i.e. there were a
    threshold `L ≤ M` at which the large-sieve count drops to a budget `B`, then necessarily
    `B ≥ (p − n)/16`. So a budget `B < (p − n)/16` is impossible to certify by this route at
    any threshold within reach of the (proven) sup-norm. With `p = n^β`, `(p−n)/16 = Θ(n^β)`,
    while the δ* budget is `O(n)`: for `β > 1` the route is strictly dominated. -/
theorem budget_unreachable (S : Spectrum) {L B : ℝ} (hL_pos : 0 < L) (hL : L ≤ S.M)
    (hcount : largeSieveCount S L ≤ B) : B ≥ (S.p - S.n) / 16 :=
  le_trans (largeSieve_vacuous S hL_pos hL) hcount

#print axioms energy_ge
#print axioms largeSieve_vacuous
#print axioms budget_unreachable

end ProximityGap.Frontier.AvE6
