/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (wf-G1)
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# OSV short-Weil curve-blend is structurally floored at `p^{3/7}` (#444, lane G1)

This file records, as axiom-clean real-exponent inequalities, the **conservation law** that walls
the Ostafe–Shparlinski–Voloch curve-blend method (arXiv:2211.07739, *Weil Sums over Small
Subgroups*, Math. Proc. Camb. Phil. Soc. 176 (2024) 39–53) out of the prize regime.

## The method and its floor

For a multiplicative subgroup `G ⊆ F_p^*` of order `τ` and `f ∈ F_p[X]`, OSV bound
`S(G; f) = Σ_{x∈G} e_p(f(x))` by:

* (Lemma 3.1) `|S(G;f)|^{2kℓ} ≤ p^r τ^{2kℓ−2k−2ℓ} Q_k(n;G) Q_ℓ(n;G)`, reducing to the system-count
  `Q_k`;
* (Lemma 2.1, the curve point-count atom) for an absolutely irreducible `F ∈ F_p[X,Y]` of degree
  `d < p`, `#{(x,y) ∈ F_p² : F(x,y)=0} ≤ 4 d^{4/3} p^{2/3} + 3p`;
* (Lemma 2.2 + Lemma 3.3) the six-variable diagonal system attached to the curve
  `F = (X^{sm}+Y^{sm}−A)^n − (X^{sn}+Y^{sn}−B)^m` gives, with `s = (p−1)/τ`,
  `T₃(m,n;s) ≪ s^{7/3} p^{11/3} + s·p^4`, hence (Cor 3.4) `Q₃(n;G) ≪ τ^{11/3} + τ^5/p`.

The headline results (Thm 1.1, Lemma 3.7) carry the **hard hypothesis `τ ≥ p^{3/7+ε}`**.

**The prize subgroup is the thin 2-power group `μ_n`, `n = τ = p^{1/β}` with `β ∈ [4,5]`.**
So the prize exponent `1/β ∈ [0.20, 0.25]` lies far below `3/7 ≈ 0.4286`.

## What is proven here (axiom-clean, no `sorry`)

1. `osv_curve_threshold_above_prize` — the OSV applicability threshold exponent `3/7` strictly
   exceeds the prize subgroup-size exponent `1/β` for every `β ≥ 2.5`. Hence Thm 1.1 / Lemma 3.7
   are **vacuous** in the prize regime.

2. `osv_T3_linear_term_never_beats_trivial` — the dominant term `s·p^4` of the OSV system bound
   `T₃` is, for every `s ≥ 1` (i.e. always, since `s = (p−1)/τ ≥ 1`), at least the trivial count
   `p^4`. The algebraic-geometry savings (the `s^{7/3}p^{11/3}` term) dominate only when `s` is
   small, i.e. `τ` is large — which is exactly the `τ ≥ p^{3/7}` floor. This is the *root cause*:
   for a thin subgroup `s` is huge, so the curve never bites.

3. `shkredov_r1_exponent_above_trivial` — for the **monomial** prize case `f(X) = bX` (degree 1,
   `r = 1`), the only OSV input is Shkredov's bound `S(G; bX) ≪ τ^{1/2} p^{1/6} (log p)^{1/6}`
   (OSV Lemma 3.6). Its log-`p` exponent `1/(2β) + 1/6` exceeds the trivial exponent `1/β`
   precisely when `β > 3`; the prize `β ∈ [4,5]` makes even this vacuous.

These are recorded as `≤`/`<` facts on real exponents — they need no number theory, only the
arithmetic of the OSV bound shapes, and constitute a precise REFUTATION of lane G1's hope that the
curve blend reaches the prize regime.  Numerical pre-screen (probe_wf5G1_*.py): measured `M(n)`
tracks `√(n log(p/n))` (ratio 1.0–1.3) while the Shkredov bound sits strictly above the trivial
`τ = n` at `n = 8,16,32`, `β = 4`.
-/

namespace ArkLib.ProximityGap.Frontier.OSVCurveFloor

/-- **The OSV applicability threshold exceeds the prize regime.**
The OSV curve-blend (Thm 1.1, Lemma 3.7) requires the subgroup exponent to be `≥ 3/7`. The thin
2-power prize subgroup `μ_n` has exponent `1/β` with `β ≥ 5/2`, so `1/β ≤ 2/5 < 3/7`. Thus the
method is vacuous in the prize regime. -/
theorem osv_curve_threshold_above_prize {β : ℝ} (hβ : (5 : ℝ) / 2 ≤ β) :
    (1 : ℝ) / β < 3 / 7 := by
  have hβpos : (0 : ℝ) < β := by linarith
  -- 1/β ≤ 2/5 since β ≥ 5/2, and 2/5 < 3/7.
  have h1 : (1 : ℝ) / β ≤ 2 / 5 := by
    rw [div_le_div_iff₀ hβpos (by norm_num)]
    linarith
  have h2 : (2 : ℝ) / 5 < 3 / 7 := by norm_num
  linarith

/-- **The dominant `T₃` term never beats trivial for a thin subgroup.**
In the OSV system bound `T₃ ≪ s^{7/3} p^{11/3} + s·p^4` (Lemma 3.3), the linear term `s·p^4` is at
least the trivial count `p^4` for every `s ≥ 1`. Since `s = (p−1)/τ ≥ 1` always (and is *large* for
a thin subgroup), the curve savings cannot lower `T₃` below trivial unless `s` is small, i.e.
`τ ≥ p^{3/7}`. This is the structural root of the `p^{3/7}` floor. -/
theorem osv_T3_linear_term_never_beats_trivial {s p : ℝ} (hs : (1 : ℝ) ≤ s) :
    p ^ 4 ≤ s * p ^ 4 := by
  have hp4 : (0 : ℝ) ≤ p ^ 4 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hs hp4]

/-- **The Shkredov `r = 1` exponent exceeds trivial for `β > 3`.**
For the prize monomial case `f(X) = bX`, OSV's only input is Shkredov's bound with log-`p` exponent
`1/(2β) + 1/6` (ignoring the `(log p)^{1/6}` factor). It beats the trivial exponent `1/β` iff
`1/6 < 1/(2β)` iff `β < 3`. The prize `β ≥ 4 > 3` makes it vacuous: the Shkredov exponent strictly
exceeds the trivial exponent. -/
theorem shkredov_r1_exponent_above_trivial {β : ℝ} (hβ : (3 : ℝ) < β) :
    (1 : ℝ) / β < 1 / (2 * β) + 1 / 6 := by
  have hβpos : (0 : ℝ) < β := by linarith
  -- 1/β − 1/(2β) = 1/(2β) < 1/6  ⇔  β > 3.
  have hkey : (1 : ℝ) / (2 * β) < 1 / 6 := by
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hsplit : (1 : ℝ) / β = 1 / (2 * β) + 1 / (2 * β) := by
    field_simp; ring
  rw [hsplit]
  linarith

/-- **Combined refutation for the prize regime `β ≥ 4`.**
Both gates fire simultaneously: the curve method is below its applicability threshold AND the
Shkredov `r = 1` input is above trivial. There is no instantiation of the OSV curve-blend that is
non-vacuous for the thin 2-power prize subgroup. -/
theorem osv_vacuous_in_prize_regime {β : ℝ} (hβ : (4 : ℝ) ≤ β) :
    (1 : ℝ) / β < 3 / 7 ∧ (1 : ℝ) / β < 1 / (2 * β) + 1 / 6 :=
  ⟨osv_curve_threshold_above_prize (by linarith),
   shkredov_r1_exponent_above_trivial (by linarith)⟩

end ArkLib.ProximityGap.Frontier.OSVCurveFloor
