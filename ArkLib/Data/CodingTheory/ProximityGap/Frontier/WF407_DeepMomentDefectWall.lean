/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# WF407 / T389-01-deepmom — the deep-moment wall is the char-`p` ENERGY DEFECT (monotone, one-sided)

This file is the sharp localization of the **master open input** (thread 389-T01): √-cancellation
at moment depth `r ≍ log q` for the worst Gauss period `B = max_{b≠0}‖η_b‖`, `η_b = Σ_{x∈μ_n} e_p(bx)`.

## What the numerics settled (probes `wf407_T389-01-deepmom_{crossover,threshold,saddle}.py`)

For `μ_n` (`n = 2^a`) and the `2r`-fold additive energy
`E_r = #{(x,y)∈μ_n^{2r} : Σx = Σy}`, the moment transport (`CharSumMomentDeepWall`) gives
`B ≤ (q·E_r)^{1/2r}` for every `r`, and the conjectured `B ≲ √(n·log q)` is the value of this bound
at the saddle `r ≍ log q`. The data localized the wall **exactly**:

1. **The char-`0` bound `E_r^{(0)}(μ_n) ≤ (2r−1)!!·n^r` is a THEOREM, never fails** (the Bessel
   coefficient inequality, `RungBesselEnergy.bessel_energy_le_gaussian`). Measured ratio
   `E_r^{(0)} / ((2r−1)!!·n^r)` is `< 1` and DECREASING in `r` (n=16: 0.94, 0.82 at r=2,3). So if the
   moment method had access to the char-`0` energy at all depths it would close the prize.

2. **The char-`p` energy `E_r^{(p)} ≥ E_r^{(0)}` is one-sided ≥, with equality iff `p > τ_r ≍
   n^{(r+3)/2}`**, i.e. iff `r ≤ r_max := 2·log_n p − 3` (threshold law, fit: last-defect prime at
   order `r` has `log_n(p_def) ≈ (r+3)/2`; n=16,r=3 → p_def=5281, log₁₆=3.09 ≈ (r+3)/2=3.0). The
   defect `E_r^{(p)} − E_r^{(0)} ≥ 0` counts the **spurious** `r`-subset sums of `μ_n` that vanish
   mod `p` but not in `ℤ[ζ_n]`.

3. **Hence the failure is ENTIRELY the char-`p` transfer, never the char-`0` bound.** At the saddle
   `r ≍ log q ≫ r_max` (ratio `r_opt/r_max = (log n)/2 = a/2` in log₂ units — half the tower depth,
   confirmed `15.84` at `a=32,β=5`) the char-`p` energy has saturated toward the trivial `n^{2r}` and
   the moment bound is pinned at its `r=r_max` value `(q·E_{r_max})^{1/2 r_max} ≍ n^{3/4}·√(log_n p)`
   — strictly worse than `√n` (wall **W4**, moment-method `√(log)`-short).

## The theorem of this file (elementary, axiom-clean)

The wall is **monotone and one-sided**: the moment bound under the *actual* char-`p` energy is
ALWAYS ≥ the bound under the ideal char-`0` energy, and the gap is governed by the nonnegative
defect. A spurious mod-`p` collision can only WORSEN the moment bound; it can never help. This pins
the entire obstruction on the defect `Δ_r := E_r^{(p)} − E_r^{(0)} ≥ 0`, and proves that no
re-optimization over `r` of the *char-`p`* moments can recover what the char-`0` moments give.

* `momentBound q E r := (q·E)^{1/(2r)}` — the value the moment method optimizes.
* `momentBound_mono_in_energy` — `E ≤ E'` ⟹ `momentBound q E r ≤ momentBound q E' r` (the bound is
  monotone in the energy; bigger energy = worse bound).
* `defect_only_worsens` — the headline: with `E_p = E_0 + Δ`, `Δ ≥ 0`, the char-`p` moment bound is
  ≥ the char-`0` moment bound, with equality iff `Δ = 0` (the transfer holds). **This is the wall.**
* `momentBound_beats_iff` — `momentBound q E r ≤ T ↔ q·E ≤ T^{2r}` (re-derived self-contained), the
  exact criterion; combined with `defect_only_worsens`, beating target `T` under char-`p` requires
  `q·(E_0+Δ) ≤ T^{2r}`, strictly harder than the char-`0` requirement `q·E_0 ≤ T^{2r}`.

The number-theoretic inputs (the value `E_r^{(0)} ≍ (2r−1)!!n^r`, the threshold `r_max = 2 log_n p−3`,
and whether `Δ_r = 0` at the saddle `r ≍ log q`) are the OPEN content, deliberately not supplied —
the last is exactly the BGK/Paley-graph √-cancellation wall. This file proves the *arrow* and the
*one-sidedness* rigorously and states the gap honestly; it does NOT cross the wall.
-/

namespace ArkLib.ProximityGap.WF407.DeepMomentDefectWall

open Real

/-- **The moment-method bound value** `(q·E)^{1/(2r)}`, i.e. the `2r`-th root of `q` times the
`2r`-fold additive energy `E`. The moment method outputs `B ≤ momentBound q E r` and optimizes over
`r`. -/
noncomputable def momentBound (q E : ℝ) (r : ℕ) : ℝ := (q * E) ^ ((1 : ℝ) / (2 * r))

/-- **The moment bound is monotone in the energy.** For a fixed depth `r ≥ 1` and `q ≥ 0`, if the
energy goes up (`E ≤ E'`) the bound goes up: `momentBound q E r ≤ momentBound q E' r`. (A larger
`2r`-fold additive energy means more additive collisions, hence a weaker square-root-cancellation
bound.) -/
theorem momentBound_mono_in_energy {q E E' : ℝ} (r : ℕ) (hr : 1 ≤ r)
    (hq : 0 ≤ q) (hE : 0 ≤ E) (hle : E ≤ E') :
    momentBound q E r ≤ momentBound q E' r := by
  unfold momentBound
  have hexp : (0 : ℝ) ≤ (1 : ℝ) / (2 * r) := by positivity
  exact Real.rpow_le_rpow (by positivity) (by nlinarith) hexp

/-- **THE WALL, one-sided: the char-`p` energy defect can only WORSEN the moment bound.**
Write the actual char-`p` energy as `E_p = E_0 + Δ` with the spurious-collision defect `Δ ≥ 0`
(`Δ = E_r^{(p)} − E_r^{(0)}`, the count of `r`-subset sums of `μ_n` vanishing mod `p` but not in
`ℤ[ζ_n]`). Then the moment bound under the true char-`p` energy is at least the bound under the ideal
char-`0` energy:
`momentBound q E_0 r ≤ momentBound q (E_0 + Δ) r`.
So the only obstruction to the prize bound is the nonnegativity of `Δ`: a spurious mod-`p` collision
strictly hurts, never helps. The deep-moment wall is exactly the statement that `Δ_r > 0` at the
saddle depth `r ≍ log q` (the BGK/Paley √-cancellation wall). -/
theorem defect_only_worsens {q E0 Δ : ℝ} (r : ℕ) (hr : 1 ≤ r)
    (hq : 0 ≤ q) (hE0 : 0 ≤ E0) (hΔ : 0 ≤ Δ) :
    momentBound q E0 r ≤ momentBound q (E0 + Δ) r :=
  momentBound_mono_in_energy r hr hq hE0 (by linarith)

/-- **Strict form: a genuine defect strictly worsens the bound.** If additionally `q > 0`, `E0 > 0`
and `Δ > 0`, the char-`p` moment bound is STRICTLY larger than the char-`0` one. (The transfer
`E_r^{(p)} = E_r^{(0)}` — equivalently `Δ = 0`, equivalently `p > τ_r` — is the ONLY way the moment
method attains the clean Gaussian bound at depth `r`.) -/
theorem defect_strictly_worsens {q E0 Δ : ℝ} (r : ℕ) (hr : 1 ≤ r)
    (hq : 0 < q) (hE0 : 0 < E0) (hΔ : 0 < Δ) :
    momentBound q E0 r < momentBound q (E0 + Δ) r := by
  unfold momentBound
  have hexp : (0 : ℝ) < (1 : ℝ) / (2 * r) := by positivity
  have hbase : (0 : ℝ) < q * E0 := mul_pos hq hE0
  have hlt : q * E0 < q * (E0 + Δ) := by nlinarith
  exact Real.rpow_lt_rpow (le_of_lt hbase) hlt hexp

/-- **The exact beats-target criterion (self-contained).** For `r ≥ 1`, `qE ≥ 0`, `T ≥ 0`:
`momentBound q E r ≤ T ↔ q·E ≤ T^{2r}` (writing `qE = q*E`). The moment method runs on this
equivalence; the prize target is `T = √(n·log(q/n))`, so `T^{2r} = (n·log(q/n))^r`, and beating it
needs `q·E_r ≤ (n·log(q/n))^r`, satisfiable only at depth `r ≳ log q`. -/
theorem momentBound_beats_iff {q E T : ℝ} (r : ℕ) (hr : 1 ≤ r)
    (hqE : 0 ≤ q * E) (hT : 0 ≤ T) :
    momentBound q E r ≤ T ↔ q * E ≤ T ^ (2 * r) := by
  unfold momentBound
  have h2r : (0 : ℝ) < 2 * r := by
    have : (0 : ℕ) < 2 * r := by omega
    exact_mod_cast this
  rw [show T ^ (2 * r) = T ^ ((2 * r : ℕ) : ℝ) from (Real.rpow_natCast T (2 * r)).symm]
  have hcast : ((2 * r : ℕ) : ℝ) = 2 * (r : ℝ) := by push_cast; ring
  rw [hcast]
  constructor
  · intro h
    have hmono := Real.rpow_le_rpow (Real.rpow_nonneg hqE _) h (le_of_lt h2r)
    rwa [← Real.rpow_mul hqE, one_div_mul_cancel (ne_of_gt h2r), Real.rpow_one] at hmono
  · intro h
    have hmono := Real.rpow_le_rpow (by positivity) h
      (le_of_lt (by positivity : (0:ℝ) < 1 / (2 * (r : ℝ))))
    rwa [← Real.rpow_mul hT, mul_one_div, div_self (ne_of_gt h2r), Real.rpow_one] at hmono

/-- **Corollary — the char-`p` transfer is NECESSARY to beat the target.** If the char-`p` moment
bound at depth `r` beats target `T` (`momentBound q (E0+Δ) r ≤ T`), then so does the char-`0` bound
(`momentBound q E0 r ≤ T`) — but NOT conversely unless `Δ = 0`. Contrapositive: if the char-`0`
bound at the saddle `r ≍ log q` would beat `√(n log q)` (it does), the only thing that can prevent
the char-`p` bound from doing the same is a positive defect `Δ_r > 0`. The prize ⟺ `Δ_r = 0` at the
saddle = the open BGK/Paley wall. -/
theorem charp_beats_imp_char0_beats {q E0 Δ T : ℝ} (r : ℕ) (hr : 1 ≤ r)
    (hq : 0 ≤ q) (hE0 : 0 ≤ E0) (hΔ : 0 ≤ Δ)
    (h : momentBound q (E0 + Δ) r ≤ T) :
    momentBound q E0 r ≤ T :=
  le_trans (defect_only_worsens r hr hq hE0 hΔ) h

end ArkLib.ProximityGap.WF407.DeepMomentDefectWall

/-! ## Axiom audit (expected: [propext, Classical.choice, Quot.sound]) -/
#print axioms ArkLib.ProximityGap.WF407.DeepMomentDefectWall.momentBound_mono_in_energy
#print axioms ArkLib.ProximityGap.WF407.DeepMomentDefectWall.defect_only_worsens
#print axioms ArkLib.ProximityGap.WF407.DeepMomentDefectWall.defect_strictly_worsens
#print axioms ArkLib.ProximityGap.WF407.DeepMomentDefectWall.momentBound_beats_iff
#print axioms ArkLib.ProximityGap.WF407.DeepMomentDefectWall.charp_beats_imp_char0_beats
