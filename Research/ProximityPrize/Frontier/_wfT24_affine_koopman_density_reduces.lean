/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# T24 — "Sarnak–Xue DENSITY of the affine Koopman operator caps the non-tempered count" REDUCES TO
        the wall (primary **F1** via the Parseval/Markov level-set duality; terminal **F0**); the earlier
        "sharp form REFUTED" verdict is **WITHDRAWN** (miscalibrated Gaussian test, audit CW-DL08a-02) (#444)

Candidate **T24** (architect `G5-4`). Let `U` be the Koopman operator of the affine `ax+b` action on
`L²(F_p)`, decomposed over the principal series `π_χ` of `G_aff = F_p ⋊ μ_n`, `n = 2^30`, `p = Θ(n^4)`.
The periods are matrix coefficients `⟨U_b ξ, ξ⟩ = η_b`, `η_b = Σ_{x∈μ_n} e_p(bx)`. A frequency `b` is
"`τ`-non-tempered" if `‖η_b‖ > t√n`. The conjecture (affine Sarnak–Xue density):

> `N(s) := #{b ≠ 0 : ‖η_b‖ ≥ n^{1/2+s}} ≤ p^{1−2s+o(1)}`, `0 ≤ s ≤ 1/2`,

with a sharp log-refined form claimed to force `M(n) ≤ √(2 n log(p/n))`.  The candidate wrote the
sharp form as `#{‖η_b‖ ≥ t√n} ≤ m·e^{−(1−o(1))t²}` (`m = (p−1)/n`), but that is mis-normalized:
`η_b/√n` has unit variance (`E|η_b|² = n` up to `O(n²/p)`), so the Gaussian tail is `e^{−t²/2}`, and
only the `e^{−t²/2}` form matches both `E_r ≤ (2r−1)‼ n^r` and the claimed edge `√(2 log m)`.  The
correctly normalized sharp form is `N_t ≤ m·e^{−(1/2−o(1))t²}`.

## Verdict: REDUCES-TO-WALL (F1; terminal F0). No refutation of the sharp form.

Two machine-faithful probes (`scripts/probes/rust/probe_wfT24_affine_koopman_density.rs`,
`probe_wfT24_density_overshoot.rs`, exact `F_p`, `p` prime, `n | p−1`, `m > 1`, `log_n p ≈ 4` (`p ≈ n^4`),
full `p−1` nonzero-frequency sweep) give the following (all EMPIRICAL, `n ∈ {8,16,32}`):

**(M0) The affine Koopman wrapping is COSMETIC — the density count is over the SAME multiset `{η_b}`
as the abelian Cayley graph.** Restricting `U` to the translation subgroup `F_p ⊴ G_aff` decomposes
as the regular representation of the *abelian* `F_p`; its `F_p`-matrix coefficients against the period
vector are the additive characters, picking out exactly `η_b`. Measured `max_b |Im η_b| ≈ 10^{-15}`
at every cell (`μ_n = −μ_n` for `n` even ⟹ `η_b ∈ ℝ`), so `{η_b}` IS the real spectrum of the
abelian adjacency `Cay(F_p, μ_n)`. The "non-abelian principal series" supplies the SAME eigenvalues;
the density count `N(s)` is a count over `b` of the abelian eigenvalues — there is no new input. This
is the C12-EDGE observation (`_wfA11`, `probe_c12_sarnak_xue_edge.py`) carried to the count form, and
it is the trigger of **F5/F11**. (This is a representation-theoretic remark; it is not formalized here.)

**(M1) The best density bound the period spectrum yields IS the Parseval/Markov level-set inequality
(= F1), and the literal `p^{1−2s}` exponent overshoots at small `n`.** For every `r`, the
trace/Parseval identity `Σ_{b≠0} ‖η_b‖^{2r} = p·E_r(μ_n) − n^{2r}` and the Markov level-set inequality
give the count bound `N(s) ≤ (Σ_{b≠0}‖η_b‖^{2r}) / (n^{1/2+s})^{2r}` (the `levelSet_le_moment` lemma
below). Minimizing over `r` is the entire handle the period spectrum offers on `N(s)`; it is fence
**F1** (a moment/energy functional). Measured: the empirical exponent `log_p N(s)` exceeds `1−2s` by up
to `0.29` (n=8), `0.245` (n=16), `0.204` (n=32), decreasing in `n` — consistent with a `p^{1−2s+o(1)}`
law whose `o(1)` is governed by the same `E_r` whose char-`p` control is the open transfer.

**(M2)/(M3) The sharp form is NOT refuted (correction, audit CW-DL08a-02).** An earlier version of
this file tested the measured tail against `m·e^{−t²}` (tail constant `1`) and declared the sharp
form refuted because the measured `c_eff := −log(N_t/m)/t² ≈ 0.65–0.73 < 1` in the bulk (`t ≥ 1.75`).
That test is miscalibrated: the correctly normalized threshold is `1/2`, and `0.65–0.73 > 1/2`.
Likewise the measured normalized edges `t_max = M/√n = 2.58, 3.32, 4.06` (n = 8, 16, 32) exceed
`√(log m) ≈ 2.50, 2.88, 3.22` but sit **below** the prize-shape edge `√(2 log m) ≈ 3.53, 4.08, 4.56`
(`m ≈ n³`).  So the small-`n` data are consistent with the prize-shape bound and give no "BGK excess".
They also do not prove it: three small cells say nothing about `n = 2^30`.

## The exact reduction map (T24 ⟶ F1 ⟶ F0)

The density count is the survival times the population: `N(s) = (p−1)·S(s)`, `S(s) = N(s)/(p−1)`.
Writing `t = n^{s}` (so `‖η_b‖ ≥ t√n`), the ONLY spectral handle is `S(t) ≤ E_r·n^{−r}·t^{−2r}` for
each `r` (Markov on the `2r`-th moment, `E_r = Σ‖η_b‖^{2r}/((p−1)n^r)` the normalized energy). This is
identically the in-tree moment ladder `M^{2r} ≤ Σ_b‖η_b‖^{2r}` viewed at a threshold (the top level
set is the single largest period). Minimizing over `r` at `r ≈ ln q` and demanding `N(s*) < 1` returns
`M ≤ √(2 n ln q)` given `E_r ≤ (2r−1)‼ n^r` at `r ≈ ln q` — the char-`p` energy transfer, char-0
proven (`char0_prize_moment_bound`), char-`p` OPEN for `n = 2^30` (the BGK/Paley wall). So T24's
density form and the in-tree moment/edge forms carry the same open input. This is the SAME funnel as
T11 (min-entropy level-set), T12 (rate function), A01 (S2 equidistribution).  (This reduction is
prose; only the Markov step below is formalized.)

## What this file proves (axiom-clean, elementary real arithmetic + finite sums)

1. `levelSet_le_moment` — the **Markov level-set inequality**: for any threshold `θ ≥ 0`, depth `r`,
   and finite nonnegative family, `(#{b : θ ≤ a b}) · θ^(2r) ≤ Σ_b (a b)^(2r)`.
2. `density_le_normalized_energy` — the same inequality at the threshold `θ = n^{1/2+s}`, written as
   `N · n^{(1+2s)r} ≤ Σ_b (a b)^(2r)`.  This is one-sided (an upper bound on the count by a moment);
   no identity minimized over `r` is proved.
3. `exp_neg_mul_sq_le_exp_neg_mul_sq_iff` — an elementary real lemma: for `t > 0`,
   `e^{−c t²} ≤ e^{−κ t²} ↔ κ ≤ c`.  (It does not mention `E_r`; the link to the energy is prose.)
4. `mul_exp_neg_mul_sq_lt_of_lt` — an elementary real lemma: for `c < κ`, `t > 0`, `m > 0`,
   `m·e^{−κ t²} < m·e^{−c t²}`.  It holds for arbitrary such `c`; it is not a countermodel.
5. `log_lt_mul_sq_of_edge` — an elementary real lemma: if `c·t² = log m`, `c < κ`, `t > 0`, then
   `log m < κ·t²` (a tail constant below `κ` pushes the edge above `√(log m / κ)`).

NO closure is claimed, and no refutation is claimed. T24 is **REDUCES-TO-WALL** (primary **F1**,
terminal **F0**). The honest residual is the one the whole campaign reduces to: the char-`p` transfer
`E_r(μ_n) ≤ (2r−1)‼ n^r` at `r ≈ ln q`, `n = 2^30` — the BGK/Paley short-character-sum wall.

Issue #444.
-/

set_option autoImplicit false
set_option linter.style.longLine false


open Real Finset

namespace ProximityGap.Frontier.AffineKoopmanDensityReduces

/-! ## 1. The Markov/Parseval level-set inequality — the entire spectral handle on the count (F1). -/

/-- **Markov level-set inequality (the density bound IS a moment bound = F1).** For a finite index
set `B`, nonnegative magnitudes `a : B → ℝ` (the `‖η_b‖`), a threshold `θ ≥ 0`, and any natural depth
`r`, the count of indices exceeding the threshold, times `θ^(2r)`, is at most the `2r`-th moment sum:
`(#{b : θ ≤ a b}) · θ^(2r) ≤ Σ_b (a b)^(2r)`. This is the moment handle on the
"non-tempered count" `N` used throughout T24; it is fence **F1** (the count bounded by a moment). -/
theorem levelSet_le_moment {B : Type*} [Fintype B] (a : B → ℝ) (ha : ∀ b, 0 ≤ a b)
    (θ : ℝ) (hθ : 0 ≤ θ) (r : ℕ) :
    ((Finset.univ.filter (fun b => θ ≤ a b)).card : ℝ) * θ ^ (2 * r)
      ≤ ∑ b, (a b) ^ (2 * r) := by
  classical
  set S : Finset B := Finset.univ.filter (fun b => θ ≤ a b) with hS
  -- On S, each term (a b)^(2r) ≥ θ^(2r); sum over S ≥ |S|·θ^(2r); extend to univ (nonneg terms).
  have hcard : (S.card : ℝ) * θ ^ (2 * r) = ∑ _b ∈ S, θ ^ (2 * r) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  rw [hcard]
  have hle_S : ∑ _b ∈ S, θ ^ (2 * r) ≤ ∑ b ∈ S, (a b) ^ (2 * r) := by
    apply Finset.sum_le_sum
    intro b hb
    have hθb : θ ≤ a b := by
      have := (Finset.mem_filter.mp hb).2; simpa using this
    exact pow_le_pow_left₀ hθ hθb (2 * r)
  refine hle_S.trans ?_
  -- ∑_{S} ≤ ∑_{univ}, since each term is nonnegative
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
  intro b _ _
  exact pow_nonneg (ha b) (2 * r)

/-! ## 2. The Markov bound at the prize threshold (one-sided). -/

/-- **The density bound at the prize threshold (one-sided Markov).** Specializing
`levelSet_le_moment` to `θ = n^{1/2+s}` (so `θ^(2r) = n^{(1+2s)r}`) gives
`N(s) · n^{(1+2s)r} ≤ Σ_b ‖η_b‖^{2r}`.  Writing `Σ_b ‖η_b‖^{2r} = (p−1)·n^r·E_r` (Parseval, `E_r` the
normalized energy — prose, not formalized here), this reads `N(s) ≤ (p−1)·E_r·n^{−2 s r}`. -/
theorem density_le_normalized_energy {B : Type*} [Fintype B] (a : B → ℝ) (ha : ∀ b, 0 ≤ a b)
    (n : ℝ) (hn : 1 ≤ n) (s : ℝ) (r : ℕ) :
    ((Finset.univ.filter (fun b => n ^ (1/2 + s) ≤ a b)).card : ℝ) * n ^ ((1 + 2 * s) * r)
      ≤ ∑ b, (a b) ^ (2 * r) := by
  classical
  have hθ : (0 : ℝ) ≤ n ^ (1/2 + s) := Real.rpow_nonneg (by linarith) _
  have hkey := levelSet_le_moment a ha (n ^ (1/2 + s)) hθ r
  -- rewrite (n^{1/2+s})^{2r} = n^{(1+2s) r}
  have hpow : (n ^ (1/2 + s : ℝ)) ^ (2 * r) = n ^ ((1 + 2 * s) * r) := by
    rw [← Real.rpow_natCast (n ^ (1/2 + s : ℝ)) (2 * r), ← Real.rpow_mul (by linarith)]
    congr 1
    push_cast
    ring
  rw [hpow] at hkey
  exact hkey

/-! ## 3. Elementary Gaussian-tail comparisons (real lemmas; the energy link is prose). -/

/-- **Comparing Gaussian tails (elementary).** For `t > 0`, `e^{−c t²} ≤ e^{−κ t²}` iff `κ ≤ c`.
For T24 the relevant normalization is `κ = 1/2` (`η_b/√n` has unit variance); the audited earlier
version used `κ = 1`, which is miscalibrated.  No statement about `E_r` is proved here. -/
theorem exp_neg_mul_sq_le_exp_neg_mul_sq_iff {c κ t : ℝ} (ht : 0 < t) :
    Real.exp (-(c * t ^ 2)) ≤ Real.exp (-(κ * t ^ 2)) ↔ κ ≤ c := by
  rw [Real.exp_le_exp]
  have ht2 : 0 < t ^ 2 := by positivity
  constructor
  · intro h
    have h' : κ * t ^ 2 ≤ c * t ^ 2 := by linarith
    exact le_of_mul_le_mul_right h' ht2
  · intro h
    nlinarith [mul_le_mul_of_nonneg_right h (le_of_lt ht2)]

/-- **A smaller tail constant gives a larger count (elementary).** For `c < κ`, `t > 0`, `m > 0`:
`m·e^{−κ t²} < m·e^{−c t²}`.  This holds for every such `c`; it is not a countermodel to any
density claim.  (The measured `c_eff ≈ 0.65–0.73` is above the correctly normalized `κ = 1/2`.) -/
theorem mul_exp_neg_mul_sq_lt_of_lt {c κ t mm : ℝ} (hcκ : c < κ) (ht : 0 < t) (hm : 0 < mm) :
    mm * Real.exp (-(κ * t ^ 2)) < mm * Real.exp (-(c * t ^ 2)) := by
  apply mul_lt_mul_of_pos_left _ hm
  rw [Real.exp_lt_exp]
  have ht2 : 0 < t ^ 2 := by positivity
  nlinarith [mul_lt_mul_of_pos_right hcκ ht2]

/-- **Edge comparison (elementary).** If the survival is `e^{−c t²}` and the count-vanishing edge
satisfies `c·t_max² = log m`, then `c < κ` gives `log m < κ·t_max²`, i.e. `t_max > √(log m / κ)`. -/
theorem log_lt_mul_sq_of_edge {c κ m tmax : ℝ} (hcκ : c < κ)
    (hedge : c * tmax ^ 2 = Real.log m) (htpos : 0 < tmax) :
    Real.log m < κ * tmax ^ 2 := by
  have ht2 : 0 < tmax ^ 2 := by positivity
  rw [← hedge]
  exact mul_lt_mul_of_pos_right hcκ ht2

end ProximityGap.Frontier.AffineKoopmanDensityReduces

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.AffineKoopmanDensityReduces.levelSet_le_moment
#print axioms ProximityGap.Frontier.AffineKoopmanDensityReduces.density_le_normalized_energy
#print axioms ProximityGap.Frontier.AffineKoopmanDensityReduces.exp_neg_mul_sq_le_exp_neg_mul_sq_iff
#print axioms ProximityGap.Frontier.AffineKoopmanDensityReduces.mul_exp_neg_mul_sq_lt_of_lt
#print axioms ProximityGap.Frontier.AffineKoopmanDensityReduces.log_lt_mul_sq_of_edge
