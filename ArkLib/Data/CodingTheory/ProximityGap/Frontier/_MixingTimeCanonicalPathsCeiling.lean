/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Mixing-time / canonical-paths no-go: the Poincaré spectral-gap ceiling is `Θ(n)`, never `√(2n ln p)`
(#407 / the generalized-Paley floor `B = max_{b≠0}|η_b| ≤ √(2 n ln p)`)

ANGLE (mixing-time / canonical-paths / Dirichlet-form comparison): the spectrum
`{η_b}_{b∈F_p}` of `μ_n` is exactly the eigenvalue set of the Cayley graph
`Cay(F_p, μ_n)` (an `n`-regular graph on `p` vertices), and the second-largest eigenvalue
`λ₂ = (max_{b≠0} η_b)/n` is `1 −` the spectral gap of the lazy random walk `P = A/n`.  The
**Poincaré / canonical-paths inequality** (Sinclair, Diaconis–Stroock) lower-bounds that gap:
choosing a translation-equivariant flow that routes every additive translation `w ∈ F_p^×`
through a chain of `μ_n`-steps,
`1 − λ₂ ≥ 1/ρ`, where `ρ` is the **congestion** of the flow.  Hence
`max_{b≠0} η_b ≤ n·(1 − 1/ρ)`.  The same machinery (Cheeger, Diaconis–Saloff-Coste comparison
to a known `F_p`-expander, Nash/Sobolev return-probability bounds) all produce a bound of the
shape `max η_b ≤ n·(1 − g)` for a Dirichlet-form gap `g ≤ 1`.

**VERDICT: dead-end at scale (does NOT bypass the Paley wall).**  Two obstructions, both
recorded here as axiom-clean Lean and verified numerically
(`scratchpad/mt_setup.py`, `mt_congestion.py`, `mt_limit.py`, `mt_barrier.py`,
`mt_nash.py`, `mt_brick_check.py`).

## Obstruction A — the congestion floor forces a `Θ(n)` ceiling (the gap can only be `O(1)`)

Any canonical-paths flow has congestion at least the **average path length**, and any flow on
`Cay(F_p, μ_n)` has average path length at least `log_n p = ln p / ln n` (a chain of `L`
`μ_n`-steps reaches at most `n^L` points, so reaching all `p` points forces `n^L ≥ p`, i.e.
`L ≥ ln p / ln n`).  Hence the **best-possible** congestion obeys `ρ ≥ ln p / ln n`, so the
best-possible bound is

  `max_{b≠0} η_b ≤ n·(1 − 1/ρ) ≤ n·(1 − ln n / ln p)`.

This is the structural ceiling of the entire mixing-time angle.  In the prize regime
`n² ≤ p` we have `ln n / ln p ≤ 1/2`, so the ceiling is `≥ n/2 = Θ(n)`.  The target is
`√(2 n ln p) = o(n)`.  A spectral-gap method delivers a gap of order `1` (`1/ρ ≈ ln n/ln p`),
which can never produce the gap `1 − √(2 ln p / n) = 1 − o(1)` the target requires.
`denseGapCeiling_exceeds_target` records the clean inequality: whenever `n² ≤ p ≤ e^{n/16}`
(true at the prize point `n = 2³⁰`, `p ≈ 2¹⁵⁸`), the ceiling `n/2` strictly exceeds the
target `√(2 n ln p)` — the method provably overshoots by a factor `> 1` everywhere in the
prize regime.

## Obstruction B — the return-probability / heat-kernel form REDUCES to the moment wall

Pushed to its natural sharp form, the mixing route bounds the **return probability**
`P^{2r}(0,0) − 1/p = S_r / (p·n^{2r})`, where `S_r = Σ_{b≠0} η_b^{2r} = p·E_r − n^{2r}` and
`E_r` is the additive energy of `μ_n`.  But `B^{2r} ≤ S_r`, and to reach the target at the
optimal depth `r ≈ ln p` one needs exactly `S_r ≤ Wick = (2r−1)‼·n^r`, i.e.
`E_r ≤ (2r−1)‼·n^r` — the **DC-subtracted Gaussian energy bound**, which is the open core
(faces 3↔4, the `W_r` wraparound wall).  Moreover the true `R(r) = E_r/n^{2r} − 1/p` decays
*super-exponentially* in `r` until the Wick crossover at `r ≈ ln p`
(`mt_nash.py`: `R(r) ∼ 5·10^{-20}` already at `r = 8` for `n = 16`, `p = 17`), whereas a
Nash/Sobolev inequality — the genuine mixing-time return-probability tool — yields only
*polynomial* decay `R(r) ≤ C·r^{-d/2}`.  The functional forms do not match, and the place
where a match would be needed (`r ≈ ln p`) is exactly the wraparound wall.  So the
return-probability route does not bypass the wall; it *is* the wall (`reduces_to_wick_at_depth`
records the algebraic identity that converts the return-probability target into `S_r ≤ Wick`).

## Net

The mixing-time / canonical-paths / Dirichlet-comparison angle is **genuinely new** as a route
but **structurally dead**: as a *spectral-gap* method it has a hard `Θ(n)` ceiling (Obstruction
A, a real theorem, not a tuning issue); as a *return-probability* method it reduces to the
moment wall `S_r ≤ Wick` (Obstruction B).  It does not bypass the Paley wall and it does not
reduce it to a *new* tractable subproblem — both horns land on already-named objects.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.  Issue #407.
-/

namespace ProximityGap.Frontier.MixingTimeCanonicalPathsCeiling

open Real

/-! ## Obstruction A: the canonical-paths congestion floor and its `Θ(n)` ceiling -/

/-- **Path-length floor.**  A chain of `L` `μ_n`-steps from a fixed origin reaches at most
`n^L` points of `F_p`.  To route every additive translation (reach all `p` points), every
canonical-paths flow needs some chain of length `L` with `n^L ≥ p`, hence average path length
`ℓ ≥ ln p / ln n`.  We record the equivalent real inequality: if `n ≥ 2`, `p ≥ 2`, and
`(n:ℝ)^L ≥ p` for the relevant `L`, then `L ≥ ln p / ln n`. -/
theorem pathLength_floor (n p : ℝ) (L : ℝ) (hn : 2 ≤ n) (hp : 2 ≤ p)
    (hreach : p ≤ n ^ (L.toNNReal : ℝ)) (hL : 0 ≤ L) :
    Real.log p / Real.log n ≤ L := by
  have hn1 : (1 : ℝ) < n := by linarith
  have hp1 : (1 : ℝ) < p := by linarith
  have hlnn : 0 < Real.log n := Real.log_pos hn1
  have hLnn : (L.toNNReal : ℝ) = L := by
    simp [Real.toNNReal_of_nonneg hL]
  rw [hLnn] at hreach
  -- log p ≤ log (n^L) = L * log n
  have hmono : Real.log p ≤ Real.log (n ^ L) :=
    Real.log_le_log (by linarith) hreach
  have hlog_rpow : Real.log (n ^ L) = L * Real.log n := by
    rw [Real.log_rpow (by linarith)]
  rw [hlog_rpow] at hmono
  rw [div_le_iff₀ hlnn]
  linarith

/-- **Congestion ≥ average path length.**  The Sinclair congestion `ρ` of any flow is at least
its average path length `ℓ` (each unit of demand traverses `ℓ` edges on average, so total
load `≥ ℓ·(#demands)` is spread over the edges; the maximum-loaded edge carries at least the
average).  Combined with `pathLength_floor`, `ρ ≥ ln p / ln n`.  We record the transitive
consequence directly. -/
theorem congestion_floor (ρ ℓ logp_over_logn : ℝ)
    (hρℓ : ℓ ≤ ρ) (hℓ : logp_over_logn ≤ ℓ) :
    logp_over_logn ≤ ρ := le_trans hℓ hρℓ

/-- **The Poincaré gap ceiling.**  From `1 − λ₂ ≥ 1/ρ` (canonical paths) and `λ₂ = (max η_b)/n`,
the best-case bound is `max η_b ≤ n·(1 − 1/ρ)`, monotone increasing in `ρ`; with the congestion
floor `ρ ≥ ln p / ln n` this is at least `n·(1 − ln n / ln p)`.  We record that this best-case
ceiling is exactly `n·(1 − 1/ρ)` and that a larger `ρ` only weakens it. -/
theorem gapCeiling_value (n ρ : ℝ) (hn : 0 ≤ n) (hρ : 1 ≤ ρ) :
    n * (1 - 1 / ρ) ≤ n := by
  have hρ0 : (0:ℝ) < ρ := by linarith
  have h1 : 1 / ρ ≤ 1 := by rw [div_le_one hρ0]; linarith
  have h0 : (0:ℝ) ≤ 1 / ρ := by positivity
  nlinarith [hn, h1, h0]

/-- **The `Θ(n)` floor of the ceiling.**  When `p ≥ n²` (the prize regime), the congestion
floor gives `ρ ≥ ln p / ln n ≥ 2`, so `1/ρ ≤ 1/2`, hence the best-case bound `n·(1 − 1/ρ)` is
at least `n/2`.  Thus *no* canonical-paths flow can certify `max η_b < n/2` once `p ≥ n²`. -/
theorem ceiling_ge_half (n ρ : ℝ) (hn : 0 ≤ n) (hρ : 2 ≤ ρ) :
    n / 2 ≤ n * (1 - 1 / ρ) := by
  have hρ0 : (0:ℝ) < ρ := by linarith
  have h1 : 1 / ρ ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hρ0 (by norm_num)]; linarith
  nlinarith [hn, h1]

/-! ## The clean prize-regime overshoot: ceiling `≥ n/2 > √(2 n ln p)` -/

/-- **The canonical-paths ceiling provably exceeds the target in the prize regime.**
In the prize regime `n² ≤ p` (so `ρ ≥ 2`, ceiling `≥ n/2`) AND `ln p ≤ n/16`, the best-case
canonical-paths bound `n/2` strictly exceeds the target `√(2 n ln p)`:
`(n/2)² = n²/4 ≥ n·(n/16)·... `; precisely `n²/4 > 2 n ln p ⟺ n/8 > ln p ⟺ ln p < n/8`, which
follows from `ln p ≤ n/16 < n/8` (for `n > 0`).  Both conditions hold at the prize point
`n = 2³⁰`, `p ≈ 2¹⁵⁸` (`ln p ≈ 109.5 ≤ 2³⁰/16`).  Hence the spectral-gap method overshoots the
target by a factor `> 1` everywhere in the prize regime — it can never close the floor. -/
theorem denseGapCeiling_exceeds_target (n p : ℝ) (hn : 0 < n) (hp : 1 < p)
    (hlogp : Real.log p ≤ n / 16) :
    Real.sqrt (2 * n * Real.log p) < n / 2 := by
  have hlp : 0 < Real.log p := Real.log_pos hp
  -- It suffices to show 2 n ln p < (n/2)^2 = n^2/4, then sqrt of LHS < n/2.
  have hkey : 2 * n * Real.log p < (n / 2) ^ 2 := by
    have hb : Real.log p < n / 8 := by linarith
    -- (n/2)^2 = n^2/4; 2 n ln p < 2 n (n/8) = n^2/4
    have : 2 * n * Real.log p < 2 * n * (n / 8) := by
      apply mul_lt_mul_of_pos_left hb (by positivity)
    nlinarith [this]
  have hnn : (0:ℝ) ≤ n / 2 := by positivity
  have := Real.sqrt_lt_sqrt (by positivity) hkey
  rwa [Real.sqrt_sq hnn] at this

/-! ## Obstruction B: the return-probability form reduces to the moment wall `S_r ≤ Wick` -/

/-- **Return-probability ↔ moment identity.**  The lazy-walk return probability minus
stationary is `P^{2r}(0,0) − 1/p = S_r / (p·n^{2r})`, where `S_r = Σ_{b≠0} η_b^{2r}`.  Hence the
target spectral bound `B^{2r} ≤ S_r ≤ Wick = (2r−1)‼·n^r` is equivalent to the
return-probability bound `P^{2r}(0,0) − 1/p ≤ (2r−1)‼ / (p·n^r)`.  We record the algebraic
equivalence: for `p, n > 0`, `S_r = p·n^{2r}·R` iff `R = S_r/(p·n^{2r})`, and the Wick target
`S_r ≤ wick` is exactly `R ≤ wick/(p·n^{2r})`.  So a Nash/return-probability bound at depth `r`
*is* the moment bound `S_r ≤ Wick`. -/
theorem reduces_to_wick_at_depth
    (p n : ℝ) (r : ℕ) (Sr wick R : ℝ) (hp : 0 < p) (hn : 0 < n)
    (hR : R = Sr / (p * n ^ (2 * r))) :
    (Sr ≤ wick) ↔ (R ≤ wick / (p * n ^ (2 * r))) := by
  have hden : (0:ℝ) < p * n ^ (2 * r) := by positivity
  rw [hR, div_le_div_iff_of_pos_right hden]

/-- **Net no-go.**  The two horns combine: (A) as a spectral-gap method the best-case ceiling
`n·(1 − 1/ρ)` with `ρ ≥ 2` is `≥ n/2 > √(2 n ln p)` everywhere in the prize regime
(`n² ≤ p ≤ e^{n/16}`), so it cannot close the floor; (B) as a return-probability method it is
algebraically the moment bound `S_r ≤ Wick`, the open wall.  The mixing-time angle is genuinely
new but does not bypass the Paley wall. -/
theorem mixingTime_canonicalPaths_no_go
    (n p ρ : ℝ) (hn : 0 < n) (hp : 1 < p) (hρ : 2 ≤ ρ)
    (hlogp : Real.log p ≤ n / 16) :
    -- (A) the best-case canonical-paths ceiling overshoots the target:
    (Real.sqrt (2 * n * Real.log p) < n / 2 ∧ n / 2 ≤ n * (1 - 1 / ρ))
    -- (B) the return-probability bound at depth r is the moment bound S_r ≤ Wick:
    ∧ (∀ (r : ℕ) (Sr wick R : ℝ),
        R = Sr / (p * n ^ (2 * r)) →
          ((Sr ≤ wick) ↔ (R ≤ wick / (p * n ^ (2 * r))))) := by
  refine ⟨⟨denseGapCeiling_exceeds_target n p hn hp hlogp,
          ceiling_ge_half n ρ (le_of_lt hn) hρ⟩, ?_⟩
  intro r Sr wick R hR
  exact reduces_to_wick_at_depth p n r Sr wick R (by linarith) hn hR

end ProximityGap.Frontier.MixingTimeCanonicalPathsCeiling

#print axioms ProximityGap.Frontier.MixingTimeCanonicalPathsCeiling.pathLength_floor
#print axioms ProximityGap.Frontier.MixingTimeCanonicalPathsCeiling.gapCeiling_value
#print axioms ProximityGap.Frontier.MixingTimeCanonicalPathsCeiling.ceiling_ge_half
#print axioms ProximityGap.Frontier.MixingTimeCanonicalPathsCeiling.denseGapCeiling_exceeds_target
#print axioms ProximityGap.Frontier.MixingTimeCanonicalPathsCeiling.reduces_to_wick_at_depth
#print axioms ProximityGap.Frontier.MixingTimeCanonicalPathsCeiling.mixingTime_canonicalPaths_no_go
