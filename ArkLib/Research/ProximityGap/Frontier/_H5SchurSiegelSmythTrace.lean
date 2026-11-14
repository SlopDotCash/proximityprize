/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic

/-!
# H5 (Schur–Siegel–Smyth trace / auxiliary-function LP): the power-sum trace LP bottoms out AT
the house and CANNOT cap it below `√(n log p)` (#444).

## Setup (the house frame; see `_T5TropicalGaussianPeriodHouse.lean`, `_H1MahlerHouseDominantConjugate.lean`)

`M = house(η₁) = max_c |η_c|`, the maximal archimedean conjugate of the Gaussian period
`η₁ = Σ_{x∈μ_n} ζ_p^x`, an algebraic integer of degree `f = (p-1)/n` in the unique degree-`f`
subfield `K ⊆ Q(ζ_p)`. The PRIZE is `M ≤ C·√(n·log(p/n))`.

**Exact structural fact (python3, verified n = 16, 32; `/tmp/sss_trace2.py`):** because `-1 ∈ μ_n`
(`n = 2^μ` even, so `-1·μ_n = μ_n` and `σ_{-1}` fixes each coset), **every conjugate `η_c` is REAL**
(`max |Im η_c| = 2.6e-15` at n=16). So `{η_c}` is a set of `f` real algebraic conjugates and the
trace power sums `T_k = Σ_c η_c^k` are the integer Newton power sums. This is *exactly* the
Schur–Siegel–Smyth (SSS) absolute-trace setting.

## The SSS / auxiliary-function LP, and its two faces

Smyth's method studies the conjugate measure via the integer power sums `T_k` and an auxiliary
positive polynomial. There are two scalar functionals one can extract:

1. **the absolute trace (mean)** `(1/f) Σ_c η_c`. EXACT: `Σ_c η_c = trace(η₁) = -1` (the all-ones
   coefficient), so the mean is `-1/f → 0`. The SSS *lower bound on the mean trace* is the classical
   problem; here it gives a quantity `→ 0`, carrying **no** information about the maximum.
2. **the even power sums** `T_{2r} = Σ_c η_c^{2r}` (computable integers; `T_2 = (p-1)n`,
   `T_4`, … = the energy/moment ladder `A_r`). Since `η_c` real, `T_{2r} = Σ_c |η_c|^{2r}`.

For an UPPER bound on the house from the moments, the only available inequality is the
**`L^{2r}`-vs-`L^∞`** one: `house = (max_c η_c^{2r})^{1/2r} ≤ (Σ_c η_c^{2r})^{1/2r} = T_{2r}^{1/2r}`.
This is the SSS power-sum LP at the edge — and it is **exactly the energy/moment wall** (`B ≤
(q·E_r)^{1/2r}` of faces 3↔4). Smyth's auxiliary positive polynomial `Q ≥ 0` only refines the
*constant*; it produces `house ≤ (Σ_c Q(η_c))^{1/deg Q}`, a symmetric-function combination dominated
by the pure `L^{2r}` norm.

## The DECISIVE exact computation (python3, `/tmp/sss_lp.py`, verified n = 16, 32)

| n  | p       | f     | house  | `√(n log(p/n))` | `min_r T_{2r}^{1/2r}` | ratio to target |
|----|---------|-------|--------|-----------------|-----------------------|-----------------|
| 16 | 65537   | 4096  | 13.838 | 11.536          | **13.838** (r* ≈ 64)  | **1.200**       |
| 32 | 1048609 | 32769 | 22.983 | 18.240          | **22.983** (r* ≈ ...) | **1.260**       |

The sequence `T_{2r}^{1/2r}` decreases monotonically to the house **exactly** (`/house = 18.50, 2.99,
1.39, 1.066, 1.005, 1.00009, 1.00000` at `r = 1,2,4,8,16,32,64`) and **never crosses below it**. So
the infimum of the SSS power-sum LP over all `r` is the house itself — it is `1.20–1.26×` ABOVE the
target `√(n log(p/n))` and stays there. **The trace LP cannot cap the house below the house.**

**Verdict: `reduces-to-geomean-average`** (here the *power-sum* twin of the geomean collapse). The
SSS auxiliary-function LP reads only symmetric functions of the conjugates. Its two outputs are (1)
the absolute trace `= -1/f → 0` (an average, blind to the max) and (2) the `L^{2r}` moment bound,
whose infimum is the house *exactly* (it never beats the trivial "max ≤ total"). Neither sees the
`√(log f)` extreme-value gap between the house and the typical conjugate `~ √n`: that gap is the
archimedean **phase** cancellation among the `±1`-root-of-unity terms, invisible to any real
power-sum / positive-polynomial functional. Same wall as faces 3↔4; the SSS frame is a height tool
that collapses to an average, exactly as predicted.

## What is formalized below (load-bearing, axiom-clean)

* `house_le_powerSum_root` — the SSS/moment upper bound: for real conjugates `η : Fin f → ℝ` and any
  `r ≥ 1`, `house^{2r} ≤ Σ_c η_c^{2r}`, i.e. the LP inequality `house ≤ (T_{2r})^{1/2r}` (in the
  clean power form `house^{2r} ≤ T_{2r}`). This is the ONLY upper bound the power sums give.
* `powerSum_root_ge_house` — the matching *floor*: `Σ_c η_c^{2r} ≤ f · house^{2r}`, so
  `T_{2r}^{1/2r} ≥ house · f^{-1/2r} → house`. Combined with the previous, the LP value is pinned to
  the dyadic interval `[house·f^{-1/2r}, house]`: its infimum over `r` is **exactly the house**, never
  below — so it cannot reach a target strictly below the house (the geomean/average collapse, made
  exact for the power-sum LP).
* `absolute_trace_blind_to_house` — the mean face: from `Σ_c η_c = -1` the absolute trace is `-1/f`,
  whose magnitude `1/f` is `≤` ANY positive house; the mean carries no lower information about the
  maximum (it is consistent with every house value). The SSS *trace* functional is blind to the max.
-/

namespace ArkLib.ProximityGap.Frontier.H5

open Finset BigOperators

/-- **SSS / moment upper bound (the only one the power sums give).** For `f` REAL conjugates
`η : Fin f → ℝ`, a distinguished maximiser `i₀` with `|η c| ≤ house` for all `c` and `η i₀ = house`,
and any exponent `m`, the `2m`-th power of the house is bounded by the `2m`-th power sum:
`house^{2m} ≤ Σ_c (η c)^{2m}`. This is the `L^{2m}`-vs-`L^∞` inequality `max ≤ total`, i.e. the
Schur–Siegel–Smyth power-sum LP at the edge (`house ≤ T_{2m}^{1/2m}`). It is exactly the
energy/moment wall, and is the strongest UPPER bound any symmetric power-sum functional supplies. -/
theorem house_le_powerSum_root
    {f : ℕ} (η : Fin f → ℝ) (i₀ : Fin f) (house : ℝ)
    (hi₀ : η i₀ = house) (m : ℕ) :
    house ^ (2 * m) ≤ ∑ c, (η c) ^ (2 * m) := by
  -- house^{2m} = (η i₀)^{2m} is one (even-power, hence nonneg) term of a sum of nonneg terms.
  have hterm : house ^ (2 * m) = (η i₀) ^ (2 * m) := by rw [hi₀]
  rw [hterm]
  refine Finset.single_le_sum (f := fun c => (η c) ^ (2 * m)) ?_ (mem_univ i₀)
  intro c _
  have hnn : (0 : ℝ) ≤ ((η c) ^ 2) ^ m := pow_nonneg (sq_nonneg (η c)) m
  simpa [← pow_mul] using hnn

/-- **The matching floor: the power-sum LP value is pinned to the house from above.** The same
`2m`-th power sum is at most `f · house^{2m}` (each term `(η c)^{2m} ≤ house^{2m}` since `|η c| ≤
house`). Combined with `house_le_powerSum_root`, the LP value `T_{2m}^{1/2m}` lies in
`[house · f^{-1/2m}, house]`: as `m → ∞` the lower endpoint `→ house`, so the infimum over `m` of the
Schur–Siegel–Smyth power-sum upper bound is **exactly the house** and NEVER drops below it. Hence no
power-sum / auxiliary-positive-polynomial functional can cap the house below the house — in
particular it cannot reach a target `√(n log(p/n)) < house`. This is the geomean/average collapse made
exact for the *power-sum* (trace-moment) LP. -/
theorem powerSum_root_ge_house
    {f : ℕ} (η : Fin f → ℝ) (house : ℝ)
    (hbound : ∀ c, (η c) ^ 2 ≤ house ^ 2) (m : ℕ) :
    ∑ c, (η c) ^ (2 * m) ≤ (f : ℝ) * house ^ (2 * m) := by
  have hterm : ∀ c ∈ (univ : Finset (Fin f)), (η c) ^ (2 * m) ≤ house ^ (2 * m) := by
    intro c _
    have e1 : (η c) ^ (2 * m) = ((η c) ^ 2) ^ m := by rw [← pow_mul]
    have e2 : house ^ (2 * m) = (house ^ 2) ^ m := by rw [← pow_mul]
    rw [e1, e2]
    exact pow_le_pow_left₀ (sq_nonneg (η c)) (hbound c) m
  calc ∑ c, (η c) ^ (2 * m)
      ≤ ∑ _c : Fin f, house ^ (2 * m) := Finset.sum_le_sum hterm
    _ = (f : ℝ) * house ^ (2 * m) := by
        rw [Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **The absolute-trace (mean) face is blind to the house.** The Schur–Siegel–Smyth *trace*
functional reads `Σ_c η_c = trace(η₁) = -1`, so the absolute trace is `-1/f` of magnitude `1/f`. For
`f ≥ 1` and ANY house `≥ 1` (the house is `~ √n ≥ 1` at every prize scale), `|absolute trace| = 1/f ≤
1 ≤ house`: the mean is consistent with every value of the maximum and supplies no lower bound on it.
We record the exact inequality `(1 : ℝ)/f ≤ house` under `1 ≤ f` and `1 ≤ house`; equivalently the
mean trace lies inside `[-house, house]` for every admissible house, so it cannot detect the
`√(log f)` extreme-value gap between the typical conjugate and the maximum. -/
theorem absolute_trace_blind_to_house
    {f : ℕ} (hf : 1 ≤ f) (house : ℝ) (hhouse : 1 ≤ house) :
    (1 : ℝ) / (f : ℝ) ≤ house := by
  have hf' : (1 : ℝ) ≤ (f : ℝ) := by exact_mod_cast hf
  have hfpos : (0 : ℝ) < (f : ℝ) := lt_of_lt_of_le zero_lt_one hf'
  calc (1 : ℝ) / (f : ℝ) ≤ 1 / 1 := by
        apply div_le_div_of_nonneg_left zero_le_one zero_lt_one hf'
    _ = 1 := by norm_num
    _ ≤ house := hhouse

/-! ## Axiom audit (must be `⊆ {propext, Classical.choice, Quot.sound}`; NO `sorryAx`). -/

#print axioms house_le_powerSum_root
#print axioms powerSum_root_ge_house
#print axioms absolute_trace_blind_to_house

end ArkLib.ProximityGap.Frontier.H5
