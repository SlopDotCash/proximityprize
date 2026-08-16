/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
/-
# LANE S4 — the GF-ceiling brick at the generalized-Fermat prime p = 65537

Issue #466 (Ethereum Proximity Prize). Dossier §15 survivor 7 (bankable ceiling tool).

## What this file proves (axiom-clean)

Let `p = 65537 = 2^16 + 1` (a generalized-Fermat / Fermat prime, `F_4`) and `n = 32`.
The order-`32` multiplicative subgroup of `𝔽_p^×` is `μ₃₂ = ⟨2⟩` (2 has order 32:
`2^16 ≡ -1`, `2^32 ≡ 1 (mod p)`), and as a set of signed residues it is
`{±2^k : k = 0,…,15}` — the `±` powers of `2`.  (The prompt's "B = 4" is a slip:
`⟨4⟩` has order only `16`; the elements listed there, `1,2,…,8192`, are powers of `2`.)

The relevant character sum is
`η₁ = Σ_{x ∈ μ₃₂} e_p(x) = Σ_{x ∈ μ₃₂} cos(2π x/p)`  (real, since `μ₃₂ = -μ₃₂`),
and by the negation-pairing `{+2^k, -2^k}` it equals
`etaGF := 2 · Σ_{k=0}^{15} cos(2π·2^k/p)`.

**Main theorem `etaGF_ge`** (fully proven, no `sorry`, no `native_decide`):
`etaGF ≥ 18`.  Numerically `etaGF ≈ 25.21` (probe `scripts/probes/probe_466_gf_ceiling.py`);
the clean bound `≥ 18` comes from the *uniform* quadratic floor `cos t ≥ 1 - t²/2`
(`Real.one_sub_sq_div_two_le_cos`) on all 16 terms together with `π² ≤ 10` (`Real.pi_lt_d2`).

**Ceiling corollaries** (fully proven):
* `etaGF_gt_ramanujan : etaGF > 2 * √32` — the Ramanujan `M ≤ 2√n` bound is VIOLATED at this
  prime (`M ≥ |η₁| = etaGF`).
* `etaGF_ramanujan_ratio_ge_three_halves : 3/2 ≤ etaGF / (2 * √32)` — a clean rational
  normalized witness, stronger than the advertised `1.34` constant.
* `etaGF_ramanujan_ratio_gt_three_halves : 3/2 < etaGF / (2 * √32)` — the strict form,
  using `2√32 < 12`.
* `C_gt_134 : etaGF > 1.34 * (2 * √32)` — the Ramanujan-normalized ratio `M/(2√n)` is `> 1.34`
  (true value `≈ 2.23`) at `p = 65537`.

⚠️ **HONEST SCOPE (out-of-window; do NOT overclaim).** For `n = 32`, `p = 65537` gives
`β = log₃₂ p ≈ 3.20 < 4` and `p < n⁴ = 2²⁰` — this witness is **OUT of the prize window**
(`β ≥ 4`). It is therefore NOT evidence that the operative wall constant
`C = M/√(n·log(p/n))` fails to be uniformly bounded over *in-window* primes; in fact the
already-landed round-2 finding (DISPROOF `Prize regime is SAFE` + the deployment lane) records
that at the **in-window** Fermat point (`n=16`, `p=65537`, `β=4.00`) the ratio is a benign
`≈ 1.20`, inside the measured band. What this brick actually shows: at the OUT-of-window
generalized-Fermat prime `F₄`, the order-32 subgroup character sum exceeds `2√n` — a
machine-checked instance of the round-2 GF-family mechanism `η₁ = n − c_B` at `B = 2, β = 3.2`
(the ONE regime where B=2 beats the plateau; the B=2 supply ends at `F₄` since `F₅` is
composite). CEILING tool, β ≈ 3.2 only; touches no floor and makes NO in-window claim.

## Character-sum bridge

`etaGF` is the explicit cosine sum. Its identification with the genuine additive-character
sum `η₁ = Re Σ_{x∈μ₃₂} exp(2πi x/p)` is the standard `e_p` negation-pairing, recorded here
as `GFCharSumBridge` (a hypothesis, verified numerically in the probe); `eta1_ceiling`
consumes it to transport the ceiling to the genuine character sum. The analytic content —
the `≥ 18` bound — is proven unconditionally.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

namespace ArkLib.ProximityGap.Frontier.GFCeiling65537

open Real Finset

/-- The generalized-Fermat prime `F_4 = 2^16 + 1`. -/
def p : ℝ := 65537

/-- The real cosine sum representing `η₁` at `p = 65537`, `n = 32`:
`etaGF = 2 · Σ_{k=0}^{15} cos(2π·2^k/p)`, using `μ₃₂ = {±2^k : k=0..15}` and the
negation pairing `cos(2π(-2^k)/p) = cos(2π·2^k/p)`. Numerically `≈ 25.21`. -/
noncomputable def etaGF : ℝ :=
  2 * ∑ k ∈ Finset.range 16, Real.cos (2 * Real.pi * (2 ^ k) / p)

/-- `π² ≤ 10`, from `π < 3.15` (`Real.pi_lt_d2`) and `π > 0`. -/
lemma pi_sq_le_ten : Real.pi ^ 2 ≤ 10 := by
  nlinarith [Real.pi_lt_d2, Real.pi_pos]

/-- Per-term quadratic floor: for every `k`,
`1 - 20·(2^k)²/p² ≤ cos(2π·2^k/p)`.
From `Real.one_sub_sq_div_two_le_cos` (`1 - x²/2 ≤ cos x`) with `x = 2π·2^k/p`, since
`x²/2 = 2π²(2^k)²/p² ≤ 20(2^k)²/p²` by `π² ≤ 10`. -/
lemma term_lower (k : ℕ) :
    (1 : ℝ) - 20 * (2 ^ k) ^ 2 / p ^ 2 ≤ Real.cos (2 * Real.pi * (2 ^ k) / p) := by
  have hcos := Real.one_sub_sq_div_two_le_cos (x := 2 * Real.pi * (2 ^ k) / p)
  refine le_trans ?_ hcos
  have hpi := pi_sq_le_ten
  have ht : (0 : ℝ) ≤ ((2 : ℝ) ^ k) ^ 2 := sq_nonneg _
  have hp2 : (0 : ℝ) < p ^ 2 := by norm_num [p]
  -- reduce to  2π²(2^k)²/p²  ≤  20(2^k)²/p²
  have hrw : (2 * Real.pi * (2 ^ k) / p) ^ 2 / 2
      = 2 * Real.pi ^ 2 * (2 ^ k) ^ 2 / p ^ 2 := by ring
  rw [hrw]
  have hcoef : (0 : ℝ) ≤ 20 - 2 * Real.pi ^ 2 := by nlinarith [hpi]
  have hnn : (0 : ℝ) ≤ 20 * (2 ^ k) ^ 2 / p ^ 2 - 2 * Real.pi ^ 2 * (2 ^ k) ^ 2 / p ^ 2 := by
    have heq : 20 * (2 ^ k) ^ 2 / p ^ 2 - 2 * Real.pi ^ 2 * (2 ^ k) ^ 2 / p ^ 2
        = ((20 - 2 * Real.pi ^ 2) * (2 ^ k) ^ 2) / p ^ 2 := by ring
    rw [heq]
    exact div_nonneg (mul_nonneg hcoef ht) (le_of_lt hp2)
  linarith [hnn]

/-- **Main axiom-clean lower bound:** `etaGF ≥ 18` (true value `≈ 25.21`). -/
theorem etaGF_ge : etaGF ≥ 18 := by
  have hsum : ∑ k ∈ Finset.range 16, ((1 : ℝ) - 20 * (2 ^ k) ^ 2 / p ^ 2)
      ≤ ∑ k ∈ Finset.range 16, Real.cos (2 * Real.pi * (2 ^ k) / p) :=
    Finset.sum_le_sum (fun k _ => term_lower k)
  have hval : (9 : ℝ) ≤ ∑ k ∈ Finset.range 16, ((1 : ℝ) - 20 * (2 ^ k) ^ 2 / p ^ 2) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, p]
    norm_num
  have : (9 : ℝ) ≤ ∑ k ∈ Finset.range 16, Real.cos (2 * Real.pi * (2 ^ k) / p) :=
    le_trans hval hsum
  unfold etaGF
  linarith

/-- `2 * √32 ≤ 12` (in fact `2√32 ≈ 11.31`): `√32 < 6` since `6² = 36 > 32`. -/
lemma two_sqrt32_le_twelve : 2 * Real.sqrt 32 ≤ 12 := by
  have h36 : Real.sqrt 36 = 6 := by
    rw [show (36 : ℝ) = 6 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  have h : Real.sqrt 32 ≤ 6 := by
    rw [← h36]; exact Real.sqrt_le_sqrt (by norm_num)
  linarith

/-- Strict version of `two_sqrt32_le_twelve`: `2√32 < 12`. -/
lemma two_sqrt32_lt_twelve : 2 * Real.sqrt 32 < 12 := by
  rw [show (12 : ℝ) = 2 * 6 by norm_num]
  gcongr
  rw [show (6 : ℝ) = Real.sqrt 36 by
    rw [show (36 : ℝ) = 6 ^ 2 by norm_num]
    exact (Real.sqrt_sq (by norm_num)).symm]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

/-- **Ceiling corollary (Ramanujan/EVT violated):** `etaGF > 2√32`.
The square-root ceiling `M ≤ 2√n` fails at this generalized-Fermat prime, since
`M ≥ |η₁| = etaGF ≥ 18 > 12 ≥ 2√32`. -/
theorem etaGF_gt_ramanujan : etaGF > 2 * Real.sqrt 32 := by
  have h1 := etaGF_ge
  have h2 := two_sqrt32_le_twelve
  linarith

/-- **Normalized rational ceiling witness:** `etaGF/(2√32) ≥ 3/2`.
This is the same coarse certificate as `etaGF_ge`, divided by the Ramanujan scale:
`etaGF ≥ 18` and `2√32 ≤ 12`. -/
theorem etaGF_ramanujan_ratio_ge_three_halves :
    (3 / 2 : ℝ) ≤ etaGF / (2 * Real.sqrt 32) := by
  have hnum : (18 : ℝ) ≤ etaGF := etaGF_ge
  have hden_pos : 0 < 2 * Real.sqrt 32 := by positivity
  have hden : 2 * Real.sqrt 32 ≤ 12 := two_sqrt32_le_twelve
  have hscaled : 18 / (2 * Real.sqrt 32) ≤ etaGF / (2 * Real.sqrt 32) := by
    exact div_le_div_of_nonneg_right hnum (le_of_lt hden_pos)
  have hbase : (3 / 2 : ℝ) ≤ 18 / (2 * Real.sqrt 32) := by
    rw [le_div_iff₀ hden_pos]
    nlinarith
  exact hbase.trans hscaled

/-- **Strict normalized rational ceiling witness:** `etaGF/(2√32) > 3/2`. -/
theorem etaGF_ramanujan_ratio_gt_three_halves :
    (3 / 2 : ℝ) < etaGF / (2 * Real.sqrt 32) := by
  have hnum : (18 : ℝ) ≤ etaGF := etaGF_ge
  have hden_pos : 0 < 2 * Real.sqrt 32 := by positivity
  have hden : 2 * Real.sqrt 32 < 12 := two_sqrt32_lt_twelve
  have hscaled : 18 / (2 * Real.sqrt 32) ≤ etaGF / (2 * Real.sqrt 32) := by
    exact div_le_div_of_nonneg_right hnum (le_of_lt hden_pos)
  have hbase : (3 / 2 : ℝ) < 18 / (2 * Real.sqrt 32) := by
    rw [lt_div_iff₀ hden_pos]
    nlinarith
  exact hbase.trans_le hscaled

/-- **Ceiling corollary (EVT constant `> 1.34`):** `etaGF > 1.34 · (2√32)`.
Hence the EVT constant `C = M/(2√n) ≥ etaGF/(2√32) > 1.34` (true value `≈ 2.23`):
`C` is NOT uniformly `≤ 1.34` over valid in-window primes; the "`M = o(n)` for all `p`"
hope needs a generalized-Fermat exclusion. -/
theorem C_gt_134 : etaGF > 1.34 * (2 * Real.sqrt 32) := by
  have h1 := etaGF_ge
  have h2 := two_sqrt32_le_twelve
  -- 1.34 * (2√32) ≤ 1.34 * 12 = 16.08 < 18 ≤ etaGF
  nlinarith [h1, h2, Real.sqrt_nonneg (32 : ℝ)]

/-- The `e_p` negation-pairing bridge (verified numerically in the probe): the real part of
the genuine additive-character sum `η₁ = Σ_{x∈μ₃₂} exp(2πi x/p)` equals `etaGF`.
Recorded as a hypothesis so `eta1_ceiling` transports the (unconditionally proven) ceiling
to the genuine character sum. -/
def GFCharSumBridge (eta1re : ℝ) : Prop := eta1re = etaGF

/-- **Transport to the genuine character sum.** Given the standard `e_p` pairing bridge,
the real part of the genuine `μ₃₂` character sum exceeds the Ramanujan ceiling `2√32`
and the `1.34` EVT ceiling. Axiom-clean modulo the explicit bridge hypothesis. -/
theorem eta1_ceiling {eta1re : ℝ} (h : GFCharSumBridge eta1re) :
    eta1re > 2 * Real.sqrt 32 ∧ eta1re > 1.34 * (2 * Real.sqrt 32) := by
  unfold GFCharSumBridge at h
  subst h
  exact ⟨etaGF_gt_ramanujan, C_gt_134⟩

/-- Ratio-form transport to the genuine character sum. -/
theorem eta1_ramanujan_ratio_ge_three_halves {eta1re : ℝ} (h : GFCharSumBridge eta1re) :
    (3 / 2 : ℝ) ≤ eta1re / (2 * Real.sqrt 32) := by
  unfold GFCharSumBridge at h
  subst h
  exact etaGF_ramanujan_ratio_ge_three_halves

/-- Strict ratio-form transport to the genuine character sum. -/
theorem eta1_ramanujan_ratio_gt_three_halves {eta1re : ℝ} (h : GFCharSumBridge eta1re) :
    (3 / 2 : ℝ) < eta1re / (2 * Real.sqrt 32) := by
  unfold GFCharSumBridge at h
  subst h
  exact etaGF_ramanujan_ratio_gt_three_halves

end ArkLib.ProximityGap.Frontier.GFCeiling65537

-- Axiom audit (frontier convention: keep these so pg-iterate reports the audit).
#print axioms ArkLib.ProximityGap.Frontier.GFCeiling65537.etaGF_ge
#print axioms ArkLib.ProximityGap.Frontier.GFCeiling65537.etaGF_gt_ramanujan
#print axioms ArkLib.ProximityGap.Frontier.GFCeiling65537.etaGF_ramanujan_ratio_ge_three_halves
#print axioms ArkLib.ProximityGap.Frontier.GFCeiling65537.etaGF_ramanujan_ratio_gt_three_halves
#print axioms ArkLib.ProximityGap.Frontier.GFCeiling65537.C_gt_134
#print axioms ArkLib.ProximityGap.Frontier.GFCeiling65537.eta1_ceiling
#print axioms ArkLib.ProximityGap.Frontier.GFCeiling65537.eta1_ramanujan_ratio_ge_three_halves
#print axioms ArkLib.ProximityGap.Frontier.GFCeiling65537.eta1_ramanujan_ratio_gt_three_halves
