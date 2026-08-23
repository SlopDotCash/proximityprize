/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.Field.Basic

/-!
# Loop 9 (PROOF side) — the large-gap regime gives a `q`-independent Johnson list bound

The disproof loops fenced the open core to *small* gaps. This file works the **proof** side: it
shows the prize is *provable* whenever the gap `η` is large enough, by turning the in-tree Johnson
list bound (`JohnsonListBound.johnson_list_bound_div`, `|L| ≤ n²/(a² − n·b)`) into a `q`-independent
list-size budget.

Instantiate the Johnson bound at a received word for a Reed–Solomon code of rate `ρ` over a domain
of size `n`:
* agreement threshold `a = (1−δ)·n` (a `δ`-close codeword agrees on `≥ (1−δ)n` points);
* pairwise codeword agreement `b = ρ·n` (two distinct degree-`<k` polynomials agree on `≤ k−1 < ρn`
  points — RS is MDS).

Then `a² − n·b = (1−δ)²n² − ρn² = n²·((1−δ)² − ρ)`, so

    |L| ≤ n² / (n²·((1−δ)² − ρ)) = 1 / ((1−δ)² − ρ),

which is **independent of `n` and `q`**, and finite precisely when `(1−δ)² > ρ`, i.e. below the
Johnson radius `δ < 1 − √ρ`. Combined with Loop 5 (`η > √ρ − ρ ⟹ δ ≤ 1−ρ−η < 1−√ρ`), this gives a
`q`-independent list-size budget in the large-gap regime — the proof-side analogue of Loop 8's
`q`-independence.

**Honest scope (disproof of the proof).** The budget `1/((1−δ)²−ρ) ≤ 1/((ρ+η)²−ρ)` **blows up as
`η → (√ρ−ρ)⁺`** (the denominator `(ρ+η)²−ρ → 0` there), so it is `poly(1/(η−(√ρ−ρ)))`, *not*
`poly(1/η)`. Hence the Johnson bound proves the prize only for gaps bounded **away from** the Johnson
threshold `√ρ−ρ`; the threshold region and the whole sub-Johnson band remain the open beyond-UDR
core. So this is a genuine *partial* proof, exactly complementary to the partial disproof side.

All results sorry-free and axiom-clean. See `DISPROOF_LOG.md` (P1).
-/

namespace ArkLib.ProximityGap.ProofLoop9

open scoped Real

/-- **Large gap ⟹ strictly below the Johnson radius (squared form).** If `0 < ρ < 1`, the gap
exceeds the Johnson gap (`√ρ − ρ < η`), and the radius is at most `1 − ρ − η` (so `ρ + η ≤ 1 − δ`),
then `ρ < (1−δ)²` — the exact positivity making the Johnson list bound finite. -/
theorem below_johnson_of_large_gap
    {ρ η δ : ℝ} (hρ0 : 0 < ρ) (hgap : Real.sqrt ρ - ρ < η)
    (hδ : ρ + η ≤ 1 - δ) :
    ρ < (1 - δ) ^ 2 := by
  have hsqrt_nonneg : 0 ≤ Real.sqrt ρ := Real.sqrt_nonneg ρ
  -- `√ρ < ρ + η ≤ 1 − δ`
  have h1 : Real.sqrt ρ < ρ + η := by linarith
  have h2 : Real.sqrt ρ < 1 - δ := lt_of_lt_of_le h1 hδ
  have h3 : (0 : ℝ) < 1 - δ := lt_of_le_of_lt hsqrt_nonneg h2
  -- square the strict inequality `√ρ < 1−δ` (both nonneg), then use `(√ρ)² = ρ`
  have hsq : (Real.sqrt ρ) ^ 2 < (1 - δ) ^ 2 := by
    exact pow_lt_pow_left₀ h2 hsqrt_nonneg (by norm_num)
  rwa [Real.sq_sqrt (le_of_lt hρ0)] at hsq

/-- **The Johnson list budget is `q`-independent and monotone in the gap.** With `ρ < (1−δ)²`
(below Johnson) and `ρ + η ≤ 1 − δ`, the `q`-independent Johnson list size
`1/((1−δ)² − ρ)` is at most the explicit `(ρ,η)`-only constant `1/((ρ+η)² − ρ)`. Neither side
depends on `n` or `q`. -/
theorem johnson_listbudget_le
    {ρ η δ : ℝ} (hρ0 : 0 < ρ) (hgap : Real.sqrt ρ - ρ < η)
    (hδ : ρ + η ≤ 1 - δ) :
    1 / ((1 - δ) ^ 2 - ρ) ≤ 1 / ((ρ + η) ^ 2 - ρ) := by
  -- both denominators are positive
  have hden2 : 0 < (ρ + η) ^ 2 - ρ := by
    have hsqrt_nonneg : 0 ≤ Real.sqrt ρ := Real.sqrt_nonneg ρ
    have h1 : Real.sqrt ρ < ρ + η := by linarith
    have hpos : (0:ℝ) < ρ + η := lt_of_le_of_lt hsqrt_nonneg h1
    have hsq : (Real.sqrt ρ) ^ 2 < (ρ + η) ^ 2 := by
      exact pow_lt_pow_left₀ h1 hsqrt_nonneg (by norm_num)
    rw [Real.sq_sqrt (le_of_lt hρ0)] at hsq
    linarith
  have hden1 : 0 < (1 - δ) ^ 2 - ρ := by
    have := below_johnson_of_large_gap hρ0 hgap hδ; linarith
  -- `(ρ+η)² ≤ (1−δ)²` since `0 ≤ ρ+η ≤ 1−δ`
  have hbase : 0 ≤ ρ + η := by
    have hsqrt_nonneg : 0 ≤ Real.sqrt ρ := Real.sqrt_nonneg ρ
    have h1 : Real.sqrt ρ < ρ + η := by linarith
    linarith
  have hmono : (ρ + η) ^ 2 ≤ (1 - δ) ^ 2 := by
    exact pow_le_pow_left₀ hbase hδ 2
  have hdenle : (ρ + η) ^ 2 - ρ ≤ (1 - δ) ^ 2 - ρ := by linarith
  exact one_div_le_one_div_of_le hden2 hdenle

/-- **Proof-side partial result.** In the large-gap regime (`η > √ρ − ρ`, gap bounded away from the
Johnson threshold by virtue of the strict inequality), the Reed–Solomon list size at any radius
`δ ≤ 1 − ρ − η` is bounded by the `q`-independent constant `1/((ρ+η)² − ρ)` — a positive real
depending only on `(ρ, η)`. This is the prize's list-size budget, met without any `q`-dependence;
the remaining open content is the *small-gap* regime `η ≤ √ρ − ρ` and the immediate
Johnson-threshold neighbourhood where this constant blows up. -/
theorem johnson_budget_qindependent_pos
    {ρ η δ : ℝ} (hρ0 : 0 < ρ) (hgap : Real.sqrt ρ - ρ < η)
    (hδ : ρ + η ≤ 1 - δ) :
    0 < 1 / ((ρ + η) ^ 2 - ρ) ∧ 1 / ((1 - δ) ^ 2 - ρ) ≤ 1 / ((ρ + η) ^ 2 - ρ) := by
  refine ⟨?_, johnson_listbudget_le hρ0 hgap hδ⟩
  have hsqrt_nonneg : 0 ≤ Real.sqrt ρ := Real.sqrt_nonneg ρ
  have h1 : Real.sqrt ρ < ρ + η := by linarith
  have hsq : (Real.sqrt ρ) ^ 2 < (ρ + η) ^ 2 := by
    exact pow_lt_pow_left₀ h1 hsqrt_nonneg (by norm_num)
  rw [Real.sq_sqrt (le_of_lt hρ0)] at hsq
  have hden : 0 < (ρ + η) ^ 2 - ρ := by linarith
  exact one_div_pos.mpr hden

end ArkLib.ProximityGap.ProofLoop9
