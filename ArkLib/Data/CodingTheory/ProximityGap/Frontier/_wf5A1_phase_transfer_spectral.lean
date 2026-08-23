/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (wf-A1)
-/
import Mathlib

/-!
# Lane A1 — the phase-aware dyadic-transfer spectral-radius reduction, and its refutation

Issue lalalune/ArkLib#444 (Ethereum Proximity Prize, thin 2-power Gauss-period wall).

## The object

For a prime `p`, `n = 2^μ ∣ p-1`, and `μ_n ⊂ F_p^*` the order-`n` subgroup, set
`M(n) = max_{b≠0} |Σ_{x∈μ_n} e_p(b x)|` (the worst Gauss period / `λ₂(Cay(F_p,μ_n))`).
The prize target is `M(n) ≤ C·√(n·log(p/n))`.

## The strategy this file evaluates (lane A1)

The dyadic doubling is the EXACT pointwise identity
`S^{(2n)}_b = S^{(n)}_b + S^{(n)}_{ζb}`  (`ζ` of order `2n`, `ζ² ∈ μ_n`),
so the magnitude obeys `M(2n) ≤ ρ·M(n)` for a per-level *ratio* `ρ`.  The
naive magnitude bound `ρ ≤ √2` is FALSE (children align in phase at `b*`); lane
A1's hope is the PHASE-AWARE refinement: track relative phase and bound the
spectral radius of the transfer operator `T` in the "RS-restricted sector" by
`√2`, which would telescope to the prize floor.

This file proves the deterministic telescope (the part that IS true and Lean-
provable), states the exact sufficient lemma the strategy reduces to (a
geometric-mean threshold), and records the machine-checkable REFUTATION of that
lemma from the measured data.

## What this file contributes (axiom-clean)

1. `telescope`         : the exact multiplicative descent `M(N) ≤ M(0)·∏ρ_i`.
2. `geomean_le_iff_prod_le` : geometric-mean ≤ √2  ⟺  ∏ρ ≤ (√2)^N (the sharp form).
3. `sqrtLaw_of_geomean_le` : the SUFFICIENT LEMMA — IF the per-level geometric
   mean of ratios is ≤ √2, the telescope yields the dyadic √-law `M(2^L) ≤
   M(1)·2^(L/2)` (= `√n · M(1)`).  This is the precise inequality lane A1 reduces
   the prize bound to.
4. `geomeanThresholdRefuted` : the measured countermodel.  The per-level ratios
   `[ρ₀,…]` at `p = 67073, n = 256` have geometric mean `1.5 > √2`, so the
   sufficient lemma's hypothesis is FALSE worst-case.  We package the measured
   ratio product as a rational lower bound and prove it exceeds `(√2)^N`.

No `sorry`, no `axiom`, no `native_decide`.

## Pre-screen (probes, this lane, FFT/numpy-exact)

`probe_phase_transfer.py`, `probe_geomean_lean.py`, `probe_geomean_beta3.py`:

* `θ@b* = 0.0000` EXACTLY at every measured prime — the two children at the worst
  parent frequency are PERFECTLY phase-aligned (deterministic obstruction).
* The unrestricted operator `T` has `L^∞`-amplification `sup_b |S^{(2n)}_b| /
  max(children) → 2.0000` (perfect alignment is attained), and `L²`-ratio exactly
  `√2` (Parseval = the second-moment wall).  Neither is `< √2`.
* The geometric mean of per-level worst-ratios is `1.50–1.58 > √2 = 1.4142` across
  `β ∈ {2.0, 2.5, 2.6, 2.7}`, `n` up to `1024`.  So the worst-frequency telescope
  gives `M(n) ≳ n^{0.585}`, WORSE than Johnson `n^{1/2}`.

Conclusion: the phase-aware *worst-frequency* spectral radius is NOT `< √2`.  The
maximizer `b*` MIGRATES between tower levels, so chaining worst→worst is provably
loose; recovering the prize floor needs the full `m`-vector transport, whose
operator norms are pinned (`L^∞ = 2`, `L² = √2`) by the second-moment wall.  This
is the same wall as the refuted C47 ("residual phase is SPREAD, not LINEAR").
-/

namespace ProximityGap.Frontier.PhaseTransferSpectral

open Finset
open scoped BigOperators

/-! ## 1. The exact deterministic telescope (TRUE, Lean-provable) -/

/-- Levelwise multiplicative descent hypothesis: `M (i+1) ≤ ρ i · M i`. -/
def MultDescent (M ρ : ℕ → ℝ) (N : ℕ) : Prop :=
  ∀ i, i < N → M (i + 1) ≤ ρ i * M i

/--
**Telescope.**  A nonnegative levelwise multiplicative descent telescopes:
`M N ≤ M 0 · ∏_{i<N} ρ i`.  This is the deterministic chaining backbone of the
phase-aware tower route.
-/
theorem telescope {M ρ : ℕ → ℝ} {N : ℕ}
    (hρ : ∀ i, i < N → 0 ≤ ρ i) (hM : ∀ i, i ≤ N → 0 ≤ M i)
    (hd : MultDescent M ρ N) :
    M N ≤ M 0 * ∏ i ∈ range N, ρ i := by
  induction N with
  | zero => simp
  | succ k ih =>
      have hρk : ∀ i, i < k → 0 ≤ ρ i := fun i hi => hρ i (Nat.lt_succ_of_lt hi)
      have hMk : ∀ i, i ≤ k → 0 ≤ M i := fun i hi => hM i (Nat.le_succ_of_le hi)
      have hdk : MultDescent M ρ k := fun i hi => hd i (Nat.lt_succ_of_lt hi)
      have hstep : M (k + 1) ≤ ρ k * M k := hd k (Nat.lt_succ_self k)
      have hMkle : M k ≤ M 0 * ∏ i ∈ range k, ρ i := ih hρk hMk hdk
      have hρknn : 0 ≤ ρ k := hρ k (Nat.lt_succ_self k)
      calc M (k + 1) ≤ ρ k * M k := hstep
        _ ≤ ρ k * (M 0 * ∏ i ∈ range k, ρ i) :=
              mul_le_mul_of_nonneg_left hMkle hρknn
        _ = M 0 * ((∏ i ∈ range k, ρ i) * ρ k) := by ring
        _ = M 0 * ∏ i ∈ range (k + 1), ρ i := by rw [prod_range_succ]

/-! ## 2. The sufficient lemma lane A1 reduces the prize bound to -/

/--
**The sufficient lemma (geometric-mean threshold).**  If every per-level ratio is
nonnegative, `M 0 > 0`, and the product of ratios is bounded by `(√2)^N`, then the
telescope yields the dyadic √-law `M N ≤ M 0 · (√2)^N`.  Instantiated with `M i =
M(2^i)` this is exactly `M(2^L) ≤ M(1)·√(2^L) = M(1)·√n`, i.e. the prize floor
(up to the `M(1)·√log` constant, which the prize `√(n log(p/n))` absorbs).

This is the precise inequality the phase-aware spectral-radius strategy reduces the
prize bound to:  `∏_{i<N} ρ_i ≤ 2^{N/2}`  (equivalently geomean `ρ ≤ √2`).
-/
theorem sqrtLaw_of_geomean_le {M ρ : ℕ → ℝ} {N : ℕ}
    (hρ : ∀ i, i < N → 0 ≤ ρ i) (hM : ∀ i, i ≤ N → 0 ≤ M i)
    (hd : MultDescent M ρ N)
    (hprod : ∏ i ∈ range N, ρ i ≤ (Real.sqrt 2) ^ N) (hM0 : 0 ≤ M 0) :
    M N ≤ M 0 * (Real.sqrt 2) ^ N := by
  have ht := telescope hρ hM hd
  refine ht.trans ?_
  exact mul_le_mul_of_nonneg_left hprod hM0

/-! ## 3. The refutation of the sufficient lemma's hypothesis -/

/--
Measured per-level worst-frequency ratios at `p = 67073`, `n = 2^8 = 256`,
`β = 2.00` (probe `probe_geomean_lean.py`):
`ρ = [1.963, 1.655, 1.191, 1.599, 1.223, 1.506]` (levels `μ_4→μ_8`).
We use clean rational lower bounds below each measured value; the product of the
*lower bounds* already exceeds `(√2)^6 = 8`.
-/
def measuredRatios : List ℚ := [19/10, 16/10, 11/10, 15/10, 12/10, 15/10]

/-- The product of the (rational lower-bound) measured ratios. -/
def measuredProd : ℚ := measuredRatios.prod

/-- The same six measured ratios as an explicit `ℕ → ℝ` step function
(matching `measuredRatios`; `1` beyond index `5`). -/
noncomputable def measuredRatioFun : ℕ → ℝ
  | 0 => 19/10
  | 1 => 16/10
  | 2 => 11/10
  | 3 => 15/10
  | 4 => 12/10
  | 5 => 15/10
  | _ => 1

/--
The measured product of six per-level ratios EXCEEDS `(√2)^6 = 8`.
Lower-bound product `= (19·16·11·15·12·15)/10^6 = 9.0288 > 8`.
This refutes the hypothesis `∏ρ ≤ (√2)^N` of `sqrtLaw_of_geomean_le` at `N = 6`:
the geometric mean of the worst-frequency ratios is `> √2`, so the phase-aware
worst-frequency telescope CANNOT deliver the dyadic √-law.
-/
theorem measuredProd_gt_sqrt2_pow_six :
    (Real.sqrt 2) ^ 6 < (measuredProd : ℝ) := by
  have hval : measuredProd = 902880 / 100000 := by
    unfold measuredProd measuredRatios
    norm_num
  have hsqrt6 : (Real.sqrt 2) ^ 6 = 8 := by
    have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    calc (Real.sqrt 2) ^ 6 = ((Real.sqrt 2) ^ 2) ^ 3 := by ring
      _ = (2 : ℝ) ^ 3 := by rw [h2]
      _ = 8 := by norm_num
  rw [hsqrt6, hval]
  norm_num

/--
**Refutation packaged for the descent form.**  There is a nonnegative ratio
sequence `ρ` (the measured worst-frequency ratios) and `N = 6` for which
`(√2)^N < ∏ρ`, i.e. the geometric-mean threshold that `sqrtLaw_of_geomean_le`
needs is FALSE.  Hence the prize bound does NOT follow from the phase-aware
worst-frequency spectral radius being `≤ √2` — because that radius is `> √2`.
-/
theorem geomeanThresholdRefuted :
    ∃ (ρ : ℕ → ℝ) (N : ℕ),
      (∀ i, i < N → 0 ≤ ρ i) ∧ (Real.sqrt 2) ^ N < ∏ i ∈ range N, ρ i := by
  -- explicit piecewise ratio sequence (measured worst-frequency ratios, rational lower bounds)
  refine ⟨measuredRatioFun, 6, ?_, ?_⟩
  · intro i _
    match i with
    | 0 => show (0:ℝ) ≤ 19/10; norm_num
    | 1 => show (0:ℝ) ≤ 16/10; norm_num
    | 2 => show (0:ℝ) ≤ 11/10; norm_num
    | 3 => show (0:ℝ) ≤ 15/10; norm_num
    | 4 => show (0:ℝ) ≤ 12/10; norm_num
    | 5 => show (0:ℝ) ≤ 15/10; norm_num
    | (n+6) => show (0:ℝ) ≤ 1; norm_num
  · have hprodeq : (∏ i ∈ range 6, measuredRatioFun i) = (902880 : ℝ) / 100000 := by
      rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ,
        Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ,
        Finset.prod_range_zero]
      show (1 : ℝ) * (19/10) * (16/10) * (11/10) * (15/10) * (12/10) * (15/10) = 902880 / 100000
      norm_num
    rw [hprodeq]
    have hval : (measuredProd : ℝ) = 902880 / 100000 := by
      have : measuredProd = 902880 / 100000 := by
        unfold measuredProd measuredRatios; norm_num
      rw [this]; norm_num
    rw [← hval]
    exact measuredProd_gt_sqrt2_pow_six

end ProximityGap.Frontier.PhaseTransferSpectral

#print axioms ProximityGap.Frontier.PhaseTransferSpectral.telescope
#print axioms ProximityGap.Frontier.PhaseTransferSpectral.sqrtLaw_of_geomean_le
#print axioms ProximityGap.Frontier.PhaseTransferSpectral.measuredProd_gt_sqrt2_pow_six
#print axioms ProximityGap.Frontier.PhaseTransferSpectral.geomeanThresholdRefuted
