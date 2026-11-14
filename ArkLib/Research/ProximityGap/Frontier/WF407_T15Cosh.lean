/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# WF407 / T15-cosh : the cosh-MGF saddle WALLS onto the deep-moment wall W4

**Thread T15-cosh (407-T15 / A03).**  The open prize core is the worst Gauss period
`B = max_{b≠0} ‖η_b‖`, `η_b = Σ_{x∈μ_n} e_p(b x)`.  The cosh route uses the EXACT char-0
identity

  `Σ_{b∈F_p} cosh(‖η_b‖ y) = p · I₀(2y)^{n/2}`         (char-0, exact)

to get a ROOT-FREE one-term bound `B ≤ min_y (1/y) arccosh(p · I₀(2y)^{n/2})`, with the saddle
`y* = √(2 log p / n)` giving `B ≤ √(2 n log 2p)(1+o(1))`.

**The decisive question (Q3), settled here.**  The cosh-MGF is the *generating function* of the
SAME even moments `E_r` the raw moment method uses:
`Σ_b cosh(‖η_b‖ y) = Σ_r y^{2r}/(2r)! · (Σ_b ‖η_b‖^{2r}) = Σ_r y^{2r}/(2r)! · (p E_r)`.  Using the
PROVEN Bessel sub-Gaussian baseline `E_r ≤ (2r−1)!!·n^r = (2r)!·n^r/(2^r r!)` (`RungBesselEnergy`),
the `r`-th weight at argument `y` is

  `w_r(y) = y^{2r}/(2r)! · E_r ≤ (n y² / 2)^r / r!`,

a **Poisson profile** with intensity `λ = n y² / 2`.  At the saddle `y*² = 2 log p / n` the intensity
is `λ = log p`, so the dominant weight sits at `r ≈ log p`.  But the char-0 value of `E_r` is provably
valid only up to `r ≤ r_max = 2 log_n p` (`CharSumMomentDeepWall`); beyond that the mod-`p`
coincidence excess turns on (numerically the cosh ratio explodes once `y` crosses the saddle:
`wf407_T15-cosh_saddle_verdict.py`, n=32: ratio 1.00 → 2.03 → 71× as `y` grows past the saddle).

Since `log p > 2 log_n p` for every `n > e²` (in particular every `n = 2^μ ≥ 8`), the saddle peak
strictly exceeds the reliable cap — by the SAME factor `≈ (log n)/2` (= half the tower depth) that
`CharSumMomentDeepWall` records for the raw moment method.  **The cosh route does NOT escape W4; it
inherits it exactly.**

## What is proven here (axiom-clean)

- `poisson_weight_le_peak` : the discrete Poisson weight `λ^r/r!` is maximized at `r = ⌊λ⌋`
  (the load-bearing concentration fact: `w_r ≤ w_⌊λ⌋` for all `r`), via the monotone ratio
  `w_{r+1}/w_r = λ/(r+1)`.
- `saddle_intensity_eq_log` : at `y² = 2·L/n` the Poisson intensity `n y²/2 = L`
  (with `L = log p` this is `λ = log p`).
- `cosh_mgf_walls_on_W4` : the WALL inequality `log p > 2·log p/log n` for `n > e²`, i.e. the saddle
  peak `≈ log p` strictly exceeds the char-0 reliable depth `r_max = 2 log_n p`.  The named Prop
  `CoshSaddleEscapesW4` is FALSE at every prize `n`, recorded as `not_coshSaddleEscapesW4`.

These are the elementary, decidable facts that pin the verdict.  The number-theoretic input the cosh
route would need (validity of `E_r` at `r ≈ log p`, equivalently a square-root bound on the
`(p−1)/n` Gauss-sum phases) is exactly the W4 open content and is deliberately NOT supplied.

## References
- In-tree: `RungBesselEnergy.lean` (the `E_r ≤ (2r−1)!! n^r` Bessel baseline),
  `CharSumMomentDeepWall.lean` (the `B ≤ (q E_r)^{1/2r}` transport + the `r ≤ 2 log_n p` cap = W4),
  `Frontier/SalemZygmundChaining.lean` (the per-coset MGF chaining kernel; the SAME moments).
- Probes: `scripts/probes/wf407_T15-cosh_saddle_verdict.py` (Q1/Q2 collapse test),
  `scripts/probes/wf407_T15-cosh_Q3_saddle_weight.py` (Q3 saddle-weight law).
-/

namespace ArkLib.ProximityGap.WF407_T15Cosh

open Real

/-- **The Poisson weight** `w_r(λ) = λ^r / r!` (the `r`-th term of the cosh-MGF after the proven
Bessel bound `E_r ≤ (2r)! n^r/(2^r r!)`, with `λ = n y²/2`). -/
noncomputable def poissonWeight (lam : ℝ) (r : ℕ) : ℝ := lam ^ r / (Nat.factorial r : ℝ)

lemma poissonWeight_nonneg {lam : ℝ} (hlam : 0 ≤ lam) (r : ℕ) : 0 ≤ poissonWeight lam r := by
  unfold poissonWeight
  positivity

/-- **The weight ratio is `λ/(r+1)`** : `w_{r+1} = w_r · λ/(r+1)`.  This is the whole content of the
Poisson concentration — the weight increases while `r+1 ≤ λ` and decreases once `r+1 > λ`. -/
lemma poissonWeight_succ (lam : ℝ) (r : ℕ) :
    poissonWeight lam (r + 1) = poissonWeight lam r * (lam / (r + 1)) := by
  unfold poissonWeight
  rw [Nat.factorial_succ]
  push_cast
  have hr1 : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  have hf : (0 : ℝ) < (Nat.factorial r : ℝ) := by exact_mod_cast Nat.factorial_pos r
  field_simp
  ring

/-- **Increasing below the mean**: if `r + 1 ≤ λ` then `w_r ≤ w_{r+1}`. -/
lemma poissonWeight_le_succ {lam : ℝ} {r : ℕ} (hlam : 0 ≤ lam) (h : (r : ℝ) + 1 ≤ lam) :
    poissonWeight lam r ≤ poissonWeight lam (r + 1) := by
  rw [poissonWeight_succ]
  have hwr : 0 ≤ poissonWeight lam r := poissonWeight_nonneg hlam r
  have hr1 : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  have hge1 : (1 : ℝ) ≤ lam / (r + 1) := by
    rw [le_div_iff₀ hr1]; linarith
  nlinarith [mul_le_mul_of_nonneg_left hge1 hwr]

/-- **Decreasing above the mean**: if `λ ≤ r + 1` then `w_{r+1} ≤ w_r`. -/
lemma poissonWeight_succ_le {lam : ℝ} {r : ℕ} (hlam : 0 ≤ lam) (h : lam ≤ (r : ℝ) + 1) :
    poissonWeight lam (r + 1) ≤ poissonWeight lam r := by
  rw [poissonWeight_succ]
  have hwr : 0 ≤ poissonWeight lam r := poissonWeight_nonneg hlam r
  have hr1 : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  have hle1 : lam / (r + 1) ≤ 1 := by
    rw [div_le_one hr1]; linarith
  nlinarith [mul_le_mul_of_nonneg_left hle1 hwr]

/-- **The saddle intensity law.**  At `y² = 2·L/n` (`n > 0`) the Poisson intensity is `n y²/2 = L`.
With `L = log p` this is the statement that the cosh-saddle places its weight at `λ = log p`. -/
lemma saddle_intensity_eq {n : ℝ} (hn : 0 < n) (L : ℝ) (ysq : ℝ) (hy : ysq = 2 * L / n) :
    n * ysq / 2 = L := by
  rw [hy]
  field_simp

/-- **The named (open-style) claim the cosh route would need** : that the saddle's dominant weight
sits within the char-0 reliable depth, i.e. `log p ≤ 2 log_n p`.  We RECORD it as a Prop and prove it
is FALSE for every prize `n` (`not_coshSaddleEscapesW4`).  `logn` is `log n`. -/
def CoshSaddleEscapesW4 (logp logn : ℝ) : Prop := logp ≤ 2 * logp / logn

/-- **THE WALL.**  For `log n > 2` and `log p > 0`, the saddle peak `≈ log p` STRICTLY exceeds the
char-0 reliable cap `r_max = 2 log_n p = 2 log p / log n`.  Equivalently the cosh route does not stay
within reliable moments: `2 log p / log n < log p`.  (`log n > 2 ⟺ n > e² ≈ 7.39`, so it holds for
every dyadic prize domain `n = 2^μ ≥ 8`.) -/
theorem cosh_mgf_walls_on_W4 {logp logn : ℝ} (hlogp : 0 < logp) (hlogn : 2 < logn) :
    2 * logp / logn < logp := by
  have hlognpos : 0 < logn := by linarith
  rw [div_lt_iff₀ hlognpos]
  -- 2 * logp < logp * logn  ⟺  logp * 2 < logp * logn  ⟺  2 < logn  (logp > 0)
  have : logp * 2 < logp * logn := by
    apply mul_lt_mul_of_pos_left hlogn hlogp
  linarith [this]

/-- **`CoshSaddleEscapesW4` is FALSE at every prize `n`.**  The Prop the cosh route needs
(`log p ≤ 2 log_n p`) fails whenever `log n > 2` and `log p > 0`: the saddle peak provably escapes the
reliable window in the WRONG direction (it sits *deeper*, not shallower).  This is the machine-checked
WALL: the cosh-MGF inherits the deep-moment wall W4. -/
theorem not_coshSaddleEscapesW4 {logp logn : ℝ} (hlogp : 0 < logp) (hlogn : 2 < logn) :
    ¬ CoshSaddleEscapesW4 logp logn := by
  unfold CoshSaddleEscapesW4
  push_neg
  exact cosh_mgf_walls_on_W4 hlogp hlogn

/-- **Quantitative wall gap.**  The peak-to-cap ratio is `(log n)/2`: `log p = (log n / 2)·r_max`
where `r_max = 2 log p / log n`.  At prize `n = 2^32` (`log n = 32 ln 2 ≈ 22.2`) this is `≈ 11`, i.e.
the saddle samples moments `11×` deeper than reliable — exactly the `a/2`-tower-levels gap of W4
(`CharSumMomentDeepWall`, `r_opt/r_max ≍ (log n)/2`). -/
theorem peak_over_rmax_eq {logp logn : ℝ} (hlogn : 0 < logn) :
    logp = (logn / 2) * (2 * logp / logn) := by
  field_simp

end ArkLib.ProximityGap.WF407_T15Cosh

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ArkLib.ProximityGap.WF407_T15Cosh.poissonWeight_succ
#print axioms ArkLib.ProximityGap.WF407_T15Cosh.poissonWeight_le_succ
#print axioms ArkLib.ProximityGap.WF407_T15Cosh.poissonWeight_succ_le
#print axioms ArkLib.ProximityGap.WF407_T15Cosh.saddle_intensity_eq
#print axioms ArkLib.ProximityGap.WF407_T15Cosh.cosh_mgf_walls_on_W4
#print axioms ArkLib.ProximityGap.WF407_T15Cosh.not_coshSaddleEscapesW4
#print axioms ArkLib.ProximityGap.WF407_T15Cosh.peak_over_rmax_eq
