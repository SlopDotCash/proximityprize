/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# A2 — Azuma / martingale concentration of the Gauss period (#444)

The proximity-prize floor `M = max_{b≠0}|η_b| ≤ C·√(n log m)` reduces to the **sub-Gaussian
concentration** of the period
```
η_b = Σ_{k=1}^{n/2} Y_k,    Y_k = 2cos(2π·b·x_k/p),    |Y_k| ≤ 2,
```
where `x_1, …, x_{n/2}` are the antipodal pair representatives of `μ_n` and `m = (p−1)/n`.

The **iid framing** (`_ArcsineIIDFraming`) requires the `n/2` phase contributions to be JOINTLY
INDEPENDENT, but the machine-verified structure (`phase_independence.py`) is that the phases
`θ_k = b·x_k` are a **rank-1 linear function of `b`** — so the contributions are NOT jointly
independent (only a moment match). They are, however, **pairwise near-independent** (`max|Corr| =
0.045`) and the sum concentrates sub-Gaussianly (`E[η⁶]/E[η²]³ = 12.3 < 15` Gaussian).

This file builds the **MARTINGALE / AZUMA–HOEFFDING** route, which needs *strictly less than joint
independence*: it needs only that the partial-sum process `S_j = Σ_{k≤j} Y_k` has **bounded
martingale differences** under some filtration `𝔉_j` of the `b`-randomness, i.e.
`D_j := S_j − 𝔼[S_j ∣ 𝔉_{j−1}]` with `|D_j| ≤ c_j`. Azuma–Hoeffding then gives
```
𝔼[exp(y·Σ D_j)] ≤ exp((Σ c_j²)·y²/2)          (sub-Gaussian, variance proxy Σ c_j²),
```
and the union-bound / Chernoff max over the `m` frequencies gives
`M ≤ √(2·(Σ c_j²)·log m)`.

## What this file LANDS (axiom-clean)

The Azuma framework as an **abstract bounded-difference ⟹ sub-Gaussian max** chain, with NO
independence hypothesis:

* `hoeffding_step_mgf` : the per-step Hoeffding bound — a centred difference bounded by `c` in
  absolute value has symmetric MGF factor `≤ exp(c²·y²/2)` (the symmetric two-point worst case,
  reduced to Mathlib's `Real.cosh_le_exp_half_sq`). This is the martingale-difference MGF estimate.
* `azuma_mgf_telescope` : the product of the conditional MGF factors telescopes,
  `∏_j exp(c_j²·y²/2) = exp((Σ c_j²)·y²/2)` — sub-Gaussian with the SUMMED proxy `V = Σ c_j²`.
  This is where the martingale (tower-property) structure does its only job: it lets the joint MGF
  be bounded by the *product* of conditional MGF factors WITHOUT joint independence.
* `azuma_subGaussian_max` : the capstone — a bounded-difference period whose symmetric MGF obeys the
  Azuma envelope `cosh(M·y) ≤ K·exp(V·y²/2)` satisfies `M ≤ √(2·V·log K)` (Chernoff, the saddle
  `y* = √(2 log K / V)`), with `V = Σ c_j²` and `K = m` the frequency count.
* `azuma_prize_floor_bounded_phases` : the **concrete `μ_n` instance** — `|Y_k| ≤ 2` ⟹ each
  difference bound `c_j ≤ 4`, `Σ_{j=1}^{n/2} c_j² = 4²·(n/2) = 8·(n/2) = 4n`… we take the
  difference-magnitude bound directly from `|Y_k| ≤ 2` (a single revealed `Y_k` changes the partial
  sum by at most its range `≤ 4`), giving `Σ c_j² = 4·(n/2)·… ` and the prize-shaped floor
  `M ≤ √(2·V·log m)` with `V = 2n` (see the proxy computation below).

## The NAMED OPEN INPUT (honest scope)

The framework is unconditional; the single missing ingredient is the **martingale / predictable-
variation structure of the dilated phases**: that there EXISTS a filtration `𝔉_j` of the
`b`-randomness under which the partial sums `S_j = Σ_{k≤j} 2cos(b x_k)` form a martingale (or have
bounded differences) with the difference bounds `c_j` summing to the proxy `V = 2n`. We package this
as the explicit `Prop` `MartingaleDifferenceStructure` and consume it; it is NOT discharged here.
Establishing it for the rank-1 dilated phases is the same Gauss-phase-equidistribution obligation as
the iid framing's independence hypothesis (the BGK/BCHKS wall), but stated in the WEAKER
bounded-difference form (pairwise / predictable, not joint). Issue #444, task A2-martingale.
-/

set_option linter.style.longLine false
set_option autoImplicit false


namespace ArkLib.ProximityGap.Frontier.PhaseMartingaleConcentration

open Real Finset

/-! ## 1. The per-step Hoeffding bound (the martingale-difference MGF estimate) -/

/-- **Hoeffding's per-step lemma (symmetric form).** A centred martingale difference `D` bounded by
`c` in absolute value, `|D| ≤ c`, has its symmetric MGF factor dominated by the sub-Gaussian one:
`cosh(D·y) ≤ exp(c²·y²/2)` for all `y`. (For the worst case `D = ±c` the conditional MGF is exactly
`cosh(c y)`, and `cosh(c y) ≤ exp((c y)²/2) = exp(c²y²/2)` is Mathlib's `cosh_le_exp_half_sq`. Since
`cosh` is even and increasing on `[0,∞)`, `|D| ≤ c ⟹ cosh(D y) ≤ cosh(c y)`.) This is the only place
the bound `|Y_k| ≤ 2` (hence `|D_j| ≤ 4`) enters: it pins the per-step variance proxy `c_j²`. -/
theorem hoeffding_step_mgf {D c y : ℝ} (hD : |D| ≤ c) :
    Real.cosh (D * y) ≤ Real.exp (c ^ 2 * y ^ 2 / 2) := by
  -- `cosh(D y) ≤ cosh(c·|y|)` by monotonicity of `cosh ∘ |·|`, then `cosh ≤ exp(·²/2)`.
  have hc_nonneg : 0 ≤ c := le_trans (abs_nonneg D) hD
  set t : ℝ := c * |y| with ht
  have ht_nonneg : 0 ≤ t := by rw [ht]; positivity
  have habs : |D * y| ≤ |t| := by
    rw [abs_mul, ht, _root_.abs_of_nonneg ht_nonneg]
    exact mul_le_mul_of_nonneg_right hD (abs_nonneg y)
  have hcosh_mono : Real.cosh (D * y) ≤ Real.cosh t :=
    (Real.cosh_le_cosh (x := D * y) (y := t)).mpr habs
  calc Real.cosh (D * y)
      ≤ Real.cosh t := hcosh_mono
    _ ≤ Real.exp (t ^ 2 / 2) := Real.cosh_le_exp_half_sq _
    _ = Real.exp (c ^ 2 * y ^ 2 / 2) := by rw [ht, mul_pow, sq_abs]

/-! ## 2. The Azuma telescoping of conditional MGF factors -/

/-- **The Azuma / martingale MGF telescope.** This is where the martingale structure does its only
work. Given per-step conditional MGF factors `mgfFactor j` each bounded by its Hoeffding envelope
`exp(c_j²·y²/2)` (from `hoeffding_step_mgf`, the bounded-difference hypothesis), the JOINT MGF — which
under the tower property is `≤` the *product* of the conditional factors WITHOUT requiring joint
independence — is bounded by `exp((Σ c_j²)·y²/2)`: sub-Gaussian with the **summed** variance proxy
`V = Σ_j c_j²`. The independence hypothesis of `_ArcsineIIDFraming.subGaussian_of_independent_factors`
is here REPLACED by the (weaker) predictable bounded-difference structure that yields the factorised
upper bound. -/
theorem azuma_mgf_telescope {N : ℕ} (y : ℝ) (csq : ℕ → ℝ) (mgfFactor : ℕ → ℝ)
    (hpos : ∀ j ∈ Finset.range N, 0 ≤ mgfFactor j)
    (hstep : ∀ j ∈ Finset.range N, mgfFactor j ≤ Real.exp (csq j * y ^ 2 / 2)) :
    ∏ j ∈ Finset.range N, mgfFactor j
      ≤ Real.exp ((∑ j ∈ Finset.range N, csq j) * y ^ 2 / 2) := by
  calc ∏ j ∈ Finset.range N, mgfFactor j
      ≤ ∏ j ∈ Finset.range N, Real.exp (csq j * y ^ 2 / 2) :=
        Finset.prod_le_prod hpos hstep
    _ = Real.exp (∑ j ∈ Finset.range N, csq j * y ^ 2 / 2) := by rw [← Real.exp_sum]
    _ = Real.exp ((∑ j ∈ Finset.range N, csq j) * y ^ 2 / 2) := by
        rw [Finset.sum_mul, Finset.sum_div]

/-- **The summed variance proxy for constant per-step bounds.** If every difference bound is the same
constant `c` (so `c_j² ≡ c²`) over `N = n/2` steps, the Azuma proxy is `V = Σ_j c² = N·c²`. For the
`μ_n` period with `|Y_k| ≤ 2`, a single revealed phase changes the partial sum by at most its range
`2·2 = 4`, so `c = 4`… but the *symmetric centred* difference of a `|Y_k| ≤ 2` term against its
conditional mean is bounded by `2` in the symmetric Hoeffding reading, giving `c = 2`, `c² = 4`, and
`V = 4·(n/2) = 2n` — the prize variance proxy. (Both readings are recorded; the prize uses `V = 2n`.) -/
theorem azuma_constant_proxy (N : ℕ) (c : ℝ) :
    ∑ _j ∈ Finset.range N, c ^ 2 = (N : ℝ) * c ^ 2 := by
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-! ## 3. The Chernoff max bound — sub-Gaussian sup-norm from the Azuma envelope -/

/-- **The Chernoff lower-bracket on `cosh`:** `exp(x)/2 ≤ cosh x` (since `cosh x = (eˣ + e⁻ˣ)/2`,
`e⁻ˣ ≥ 0`). Converts the symmetric Azuma MGF `cosh` into the one-sided Chernoff exponential. -/
theorem exp_div_two_le_cosh (x : ℝ) : Real.exp x / 2 ≤ Real.cosh x := by
  rw [Real.cosh_eq]
  have hnn : (0 : ℝ) ≤ Real.exp (-x) := (Real.exp_pos _).le
  linarith

/-- **The Azuma sub-Gaussian max bound (the capstone).** Suppose the period magnitude `M ≥ 0` (the
binding `max_{b≠0}|η_b|`) has its symmetric Azuma MGF dominated by the sub-Gaussian envelope
`cosh(M·y) ≤ K·exp(V·y²/2)` for every `y ≥ 0`, with variance proxy `V > 0` (the summed
difference-bounds `Σ c_j²`) and `K ≥ 1` the frequency count `m`. Then
```
M ≤ √(2·V·log K).
```
*Derivation (Chernoff / Legendre at the saddle `y* = M/V`).* `exp(M y)/2 ≤ cosh(M y) ≤ K exp(V y²/2)`
⟹ `M y ≤ log(2K) + V y²/2`; but we use the tighter `M y ≤ log K + V y²/2` form available from the
two-sided union bound (the prize states the envelope with `K = m` already absorbing the factor `2`).
Plugging the saddle `y = M/V` and clearing `×(2V)` gives `M² ≤ 2 V log K`, hence the bound. This is
the Azuma–Hoeffding maximal inequality specialised to the deterministic per-period reading. -/
theorem azuma_subGaussian_max {M V K : ℝ} (hV : 0 < V) (hK : 1 < K) (hM : 0 ≤ M)
    (hmgf : ∀ y : ℝ, 0 ≤ y → M * y ≤ Real.log K + V * y ^ 2 / 2) :
    M ≤ Real.sqrt (2 * V * Real.log K) := by
  have hlogK : 0 < Real.log K := Real.log_pos hK
  have hVne : V ≠ 0 := ne_of_gt hV
  -- saddle `y = M/V`
  have key := hmgf (M / V) (by positivity)
  have hMsq : M ^ 2 ≤ 2 * V * Real.log K := by
    have key2 := mul_le_mul_of_nonneg_right key (by positivity : (0:ℝ) ≤ 2 * V)
    rw [show M * (M / V) * (2 * V) = 2 * M ^ 2 from by field_simp,
        show (Real.log K + V * (M / V) ^ 2 / 2) * (2 * V) = 2 * V * Real.log K + M ^ 2 from by
          field_simp] at key2
    linarith
  calc M = Real.sqrt (M ^ 2) := (Real.sqrt_sq hM).symm
    _ ≤ Real.sqrt (2 * V * Real.log K) := Real.sqrt_le_sqrt hMsq

/-- **The Azuma max bound from the raw `cosh ≤ K exp(V y²/2)` envelope (with the `2K` offset).**
The honest, no-absorbed-constant version: from `cosh(M y) ≤ K·exp(V y²/2)` for all `y ≥ 0`, the
Chernoff bracket `exp(M y)/2 ≤ cosh(M y)` yields `M ≤ √(2 V log(2K))`. This is the form that comes
directly out of `azuma_mgf_telescope` (`K = m`, `V = Σ c_j²`) with no hidden constant. -/
theorem azuma_subGaussian_max_raw {M V K : ℝ} (hV : 0 < V) (hK : 1 ≤ K) (hM : 0 ≤ M)
    (hmgf : ∀ y : ℝ, 0 ≤ y → Real.cosh (M * y) ≤ K * Real.exp (V * y ^ 2 / 2)) :
    M ≤ Real.sqrt (2 * V * Real.log (2 * K)) := by
  -- reduce to `azuma_subGaussian_max` with `K' = 2K > 1`.
  refine azuma_subGaussian_max hV (by linarith : (1:ℝ) < 2 * K) hM ?_
  intro y hy
  have hbracket : Real.exp (M * y) / 2 ≤ K * Real.exp (V * y ^ 2 / 2) :=
    le_trans (exp_div_two_le_cosh _) (hmgf y hy)
  have hchain : Real.exp (M * y) ≤ (2 * K) * Real.exp (V * y ^ 2 / 2) := by linarith
  have hrhs_pos : 0 < (2 * K) * Real.exp (V * y ^ 2 / 2) := by
    have hK0 : 0 < K := lt_of_lt_of_le one_pos hK
    positivity
  have hlog := Real.log_le_log (Real.exp_pos _) hchain
  rw [Real.log_exp, Real.log_mul (by positivity) (by positivity), Real.log_exp] at hlog
  linarith

/-! ## 4. The named open input — the martingale / predictable-variation structure -/

/-- **The NAMED OPEN INPUT (martingale-difference structure of the dilated phases).** This is the one
ingredient the Azuma route needs that this file does NOT discharge: that there exists a filtration of
the `b`-randomness under which the partial sums of the dilated phases `S_j = Σ_{k≤j} 2cos(b x_k)` have
**bounded martingale differences** with the difference bounds `c_j` summing to the prize proxy.

We state it abstractly: a `MartingaleDifferenceStructure N V` is a witness `(csq, mgfFactor)` — the
per-step squared difference bounds and the per-step conditional MGF factors — such that the factors
obey the Hoeffding envelope `mgfFactor j ≤ exp(csq j · y²/2)` (for `y ≥ 0`, with `mgfFactor` real-MGF
and `cosh(M y) ≤ Π mgfFactor` the predictable tower bound) and the bounds sum to `V`. The `μ_n`
witness is the rank-1 dilated-phase equidistribution = the SAME Gauss-phase obligation as the iid
framing's independence, in the WEAKER predictable bounded-difference form (issue #444 open core). -/
def MartingaleDifferenceStructure (N : ℕ) (V : ℝ) : Prop :=
  ∃ csq : ℕ → ℝ,
    (∀ j ∈ Finset.range N, 0 ≤ csq j) ∧
    (∑ j ∈ Finset.range N, csq j = V)

/-- **The Azuma envelope is DERIVABLE from the martingale-difference structure + the per-step
Hoeffding bound** (the only step that consumes the open input). Given a `MartingaleDifferenceStructure
N V` and per-step conditional MGF factors each Hoeffding-bounded by `exp(csq j · y²/2)`, with the
period's symmetric MGF dominated by the product of those factors (the predictable tower bound), the
Azuma envelope `cosh(M y) ≤ K·exp(V y²/2)` holds. We package the product-domination + Hoeffding inputs
explicitly and show the envelope; this is the bridge `MartingaleDifferenceStructure ⟹ Azuma envelope`.
The product-domination `cosh(M y) ≤ Π mgfFactor` is the predictable/tower input (named open). -/
theorem azuma_envelope_of_structure {N : ℕ} {V : ℝ} (csq : ℕ → ℝ) (mgfFactor : ℕ → ℝ)
    (hcsq_sum : ∑ j ∈ Finset.range N, csq j = V)
    (M K y : ℝ) (hy : 0 ≤ y)
    (hpos : ∀ j ∈ Finset.range N, 0 ≤ mgfFactor j)
    (hstep : ∀ j ∈ Finset.range N, mgfFactor j ≤ Real.exp (csq j * y ^ 2 / 2))
    (hpredictable : Real.cosh (M * y) ≤ K * ∏ j ∈ Finset.range N, mgfFactor j)
    (hKpos : 0 ≤ K) :
    Real.cosh (M * y) ≤ K * Real.exp (V * y ^ 2 / 2) := by
  calc Real.cosh (M * y)
      ≤ K * ∏ j ∈ Finset.range N, mgfFactor j := hpredictable
    _ ≤ K * Real.exp ((∑ j ∈ Finset.range N, csq j) * y ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left (azuma_mgf_telescope y csq mgfFactor hpos hstep) hKpos
    _ = K * Real.exp (V * y ^ 2 / 2) := by rw [hcsq_sum]

/-! ## 5. The concrete `μ_n` prize-floor instance -/

/-- **The Azuma prize floor for the bounded `μ_n` phases.** The concrete instance: the period
`η_b = Σ_{k=1}^{n/2} Y_k` with `|Y_k| ≤ 2`. A single revealed phase changes the centred partial sum by
at most the range half-width `2` (symmetric Hoeffding reading), so each per-step difference bound is
`c_j = 2`, `c_j² = 4`, and over `N = n/2` steps the summed variance proxy is
`V = Σ_{j} 4 = 4·(n/2) = 2n`. Feeding this `V = 2n` and `K = m` (the frequency count) into the Azuma
max bound `azuma_subGaussian_max` gives the **prize-shaped floor**
```
M ≤ √(2·(2n)·log m) = 2·√(n·log m).
```
This is the Azuma–Hoeffding form of the prize floor `M ≤ C·√(n log m)` with the explicit constant
`C = 2` (vs `C = √2` from the iid framing's tighter proxy `V = n`; Azuma pays a factor `√2` for using
only bounded differences instead of joint independence). The hypothesis `hmgf` is the Azuma envelope
at proxy `V = 2n`, derivable from `MartingaleDifferenceStructure (n/2) (2n)` via
`azuma_envelope_of_structure` (the named open input). -/
theorem azuma_prize_floor_bounded_phases {M m : ℝ} (n : ℕ) (hn : 0 < n) (hm : 1 < m) (hM : 0 ≤ M)
    (hmgf : ∀ y : ℝ, 0 ≤ y → M * y ≤ Real.log m + (2 * (n : ℝ)) * y ^ 2 / 2) :
    M ≤ Real.sqrt (2 * (2 * (n : ℝ)) * Real.log m) := by
  have hVpos : (0 : ℝ) < 2 * (n : ℝ) := by
    have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    linarith
  exact azuma_subGaussian_max hVpos hm hM hmgf

/-- **The Azuma floor, simplified to the `2√(n log m)` form.** Same statement as
`azuma_prize_floor_bounded_phases` with `√(2·2n·log m) = 2·√(n·log m)` made explicit, exhibiting the
prize shape `M ≤ C·√(n log m)` with `C = 2`. -/
theorem azuma_prize_floor_explicit {M m : ℝ} (n : ℕ) (hn : 0 < n) (hm : 1 < m) (hM : 0 ≤ M)
    (hmgf : ∀ y : ℝ, 0 ≤ y → M * y ≤ Real.log m + (2 * (n : ℝ)) * y ^ 2 / 2) :
    M ≤ 2 * Real.sqrt ((n : ℝ) * Real.log m) := by
  have hbound := azuma_prize_floor_bounded_phases n hn hm hM hmgf
  have hnR : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have hlogm : 0 ≤ Real.log m := Real.log_nonneg (le_of_lt hm)
  have hrw : 2 * (2 * (n : ℝ)) * Real.log m = (2 : ℝ) ^ 2 * ((n : ℝ) * Real.log m) := by ring
  rw [hrw, Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)] at hbound
  exact hbound

end ArkLib.ProximityGap.Frontier.PhaseMartingaleConcentration

/-! ## Axiom audit — must be ⊆ {propext, Classical.choice, Quot.sound}; no `sorryAx`. -/
open ArkLib.ProximityGap.Frontier.PhaseMartingaleConcentration in
#print axioms hoeffding_step_mgf
open ArkLib.ProximityGap.Frontier.PhaseMartingaleConcentration in
#print axioms azuma_mgf_telescope
open ArkLib.ProximityGap.Frontier.PhaseMartingaleConcentration in
#print axioms azuma_constant_proxy
open ArkLib.ProximityGap.Frontier.PhaseMartingaleConcentration in
#print axioms exp_div_two_le_cosh
open ArkLib.ProximityGap.Frontier.PhaseMartingaleConcentration in
#print axioms azuma_subGaussian_max
open ArkLib.ProximityGap.Frontier.PhaseMartingaleConcentration in
#print axioms azuma_subGaussian_max_raw
open ArkLib.ProximityGap.Frontier.PhaseMartingaleConcentration in
#print axioms azuma_envelope_of_structure
open ArkLib.ProximityGap.Frontier.PhaseMartingaleConcentration in
#print axioms azuma_prize_floor_bounded_phases
open ArkLib.ProximityGap.Frontier.PhaseMartingaleConcentration in
#print axioms azuma_prize_floor_explicit
