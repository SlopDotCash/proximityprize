/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# H2 — The period-polynomial ROOT-BOUND route is REAL-ROOTED and collapses to the energy/moment
ladder (the trace-form is `√2` sharper than Fujiwara but still `Θ(√(nm))`) (#444)

**The angle (lane H2, house/height attack).** The Gaussian periods `η₀,…,η_{f-1}` of the dyadic
subgroup `μ_n` (order `n = 2^μ`, `m = f = (p-1)/n` cosets) are the roots of the degree-`f` period
polynomial `Ψ(T) = ∏_c (T - η_c) ∈ ℤ[T]`. The prize quantity is `M = house(η₁) = max_c |η_c|`.
The mission: do the EXACT coefficients of `Ψ`, fed through a classical max-root bound
(Cauchy / Fujiwara / Lagrange / **trace-form** / Schur–Cohn / **abs-moment**), force
`M ≤ C·√(n·log(p/n))`, or do they collapse to the average/geomean/energy ladder again?

**The exact computational findings (all hard-verified, `n=16,32,64`, see probe).**

* **REAL-ROOTEDNESS (new, the structural lever H2 exploits).** Because `μ_n` is dyadic with
  `2 ∣ n`, it is closed under negation (`-1 ∈ μ_n`), so each period `η_c = Σ_{x∈μ_n} ζ_p^{cx}`
  pairs `x ↔ -x` and is therefore **REAL**. Verified exactly: `max_c |Im η_c| = 0` at all tested
  `(n,p)`. Hence `Ψ(T)` is a **real-rooted** monic integer polynomial of degree `f`.

* **EXACT second power sum (= the energy `E_1`):** `p₂ := Σ_c η_c² = p - n` (verified exactly;
  the classical `n(m-1)+1` identity). With `p₁ = Σ_c η_c = -1`.

* **TRACE-FORM bound (new, sharper than the G3 Fujiwara bound).** For a real-rooted polynomial
  every root is real so `η_c² = |η_c|²`, hence
  `house² = max_c η_c² ≤ Σ_c η_c² = p₂ = p - n`, i.e. `house ≤ √(p - n)`.
  This is `√2`-times tighter than the G3 Fujiwara value `√(2(p-n-1))` (measured ratio
  `Fuj/trace → √2 = 1.4142…` uniformly), yet still `Θ(√(nm))`.

* **The abs-moment ladder IS the Wick-energy ladder.** Real-rootedness gives
  `Σ_c |η_c|^{2r} = Σ_c η_c^{2r} = p_{2r}` (the integer power sum `= q·E_r/n`-style energy).
  Thus `house ≤ p_{2r}^{1/(2r)}` for every `r`, and this sequence is **monotone non-increasing**
  in `r`, converging DOWN to `house` only as `r → ∞`. Its first usable term `r=1` is exactly the
  trace-form `√(p-n) = Θ(√(nm))`; reaching the prize scale `√(n log m)` needs depth `r ≈ log m`,
  which is exactly the open BGK/Paley energy wall.

**The verdict: `reduces-to-geomean-average` (equivalently `reduces-to-wall`).** Every
coefficient-magnitude / power-sum root bound is a function of the energies `p_{2r}` (the
moments), and the *only* one available at bounded char-0 depth is the second moment
`p₂ = p - n = Θ(nm)`; its square root is `Θ(√(nm)) = √(m/log m)·prize`. The house lives below
this — at `√(n log m)` — purely by the SIGN cancellation among the `f` real periods, which the
moment magnitudes are blind to. The height tool collapses to the energy/moment average, the
wrong side of `√n`, EXACTLY as the tropical engine (`_T5`) collapsed to the geomean.

**What is NEW vs G3 (`_wf9G3_periodpoly_coeff_nogo`).** G3 proved the *Fujiwara* bound is loose by
`√(m/log m)` via `|e₂|`. H2 adds: (i) the polynomial is **real-rooted**, so (ii) the **trace-form**
bound `house ≤ √(p-n)` is the genuinely sharper member of the family (`√2` below Fujiwara) and is
the `r=1` term of (iii) the full **abs-moment ladder** `house ≤ p_{2r}^{1/2r}`, monotone to the
house — pinpointing that the *entire* root-bound family reduces to the energy/moment method and the
char-0 floor is the single second moment `p₂ = p - n`.

**Tag: OBSTRUCTION (CHAR-0) / reduces-to-geomean-average.** Axiom-clean; no `sorry`.

Probe: `/tmp/period_poly{2,3,5}.py` (exact integer power sums `p_k = (Z_k·p − n^k)/n` via the
coset-sum DP; real-rootedness `max|Im η|=0`; trace-form vs Fujiwara ratio `→ √2`; abs-moment
ladder `= p_{2r}` monotone to the house).

Issue #444, lane H2.
-/

namespace ArkLib.ProximityGap.Frontier.H2

open scoped Real
open Finset BigOperators

/-! ## 1. The trace-form bound for a real-rooted polynomial (the new sharper member). -/

/-- **Trace-form root bound (real-rooted).** For any finite family of REAL numbers `η : Fin f → ℝ`
(the real period roots), the square of the house (max absolute value) is at most the sum of squares
`Σ_c η_c²` (the second power sum `p₂`). This is `house² ≤ p₂`. It uses real-rootedness
load-bearingly: each `η_c²` is a nonnegative summand, so the max is dominated by the total.

This is the `r = 1` term of the abs-moment ladder and is `√2`-sharper than the Fujiwara bound
`√(2|e₂|) = √(2(p₂−1))`. -/
theorem house_sq_le_p2 {f : ℕ} (η : Fin f → ℝ) (c₀ : Fin f) :
    (η c₀) ^ 2 ≤ ∑ c, (η c) ^ 2 := by
  refine Finset.single_le_sum (f := fun c => (η c) ^ 2) ?_ (Finset.mem_univ c₀)
  intro i _; positivity

/-- **Trace-form bound, value form.** If the second power sum is `p₂ = p - n` then the house is at
most `√(p - n)`. This is the exact value the trace-form delivers; it is `Θ(√(nm))` since
`p - n = nm + 1 - n = n(m-1) + 1`. -/
theorem house_le_sqrt_p2 {f : ℕ} (η : Fin f → ℝ) (c₀ : Fin f)
    (p n : ℝ) (hp2 : ∑ c, (η c) ^ 2 = p - n) (hpn : 0 ≤ p - n) :
    |η c₀| ≤ Real.sqrt (p - n) := by
  have h := house_sq_le_p2 η c₀
  rw [hp2] at h
  -- |η c₀| ≤ √(p-n)  ⟺  |η c₀|² ≤ p-n
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt h

/-! ## 2. The trace-form is √2 sharper than Fujiwara, but both are Θ(√(nm)). -/

/-- **Trace-form is `√2`-sharper than Fujiwara.** With `p₂ = p - n` and `|e₂| = (p - n - 1)/2`,
the Fujiwara value is `2√|e₂| = √(2(p - n - 1))` and the trace-form value is `√(p - n)`. Their
ratio is `√(2(p-n-1)/(p-n)) → √2` as `p → ∞`. We record the clean inequality
`trace-form ≤ Fujiwara` (so the trace-form is the better — but still loose — member) whenever
`p - n ≥ 2` (i.e. `p - n - 1 ≥ p - n - 1` and `2(p-n-1) ≥ p-n ⟺ p-n ≥ 2`). -/
theorem traceForm_le_fujiwara (p n : ℝ) (h : 2 ≤ p - n) :
    Real.sqrt (p - n) ≤ Real.sqrt (2 * (p - n - 1)) := by
  apply Real.sqrt_le_sqrt
  linarith

/-! ## 3. The abs-moment ladder = the energy ladder, monotone to the house, floor at `r=1`. -/

/-- **Abs-moment root bound (real-rooted) = even power-sum bound.** For real roots,
`|η_c|^{2r} = η_c^{2r}`, so the abs-`2r`-moment equals the integer power sum `p_{2r}`, and
`house^{2r} ≤ p_{2r}`, i.e. `house ≤ p_{2r}^{1/(2r)}`. We state the inner inequality
`(η c₀)^{2r} ≤ Σ_c (η c)^{2r}` (every even power is a nonneg summand). This is the full root-bound
family: at `r = 1` it is the trace-form `p₂ = p - n` (the char-0 floor), and only as `r → ∞`
does `p_{2r}^{1/2r}` descend to the house — exactly the energy/moment ladder. -/
theorem house_pow_le_evenPowerSum {f : ℕ} (η : Fin f → ℝ) (c₀ : Fin f) (r : ℕ) :
    (η c₀) ^ (2 * r) ≤ ∑ c, (η c) ^ (2 * r) := by
  refine Finset.single_le_sum (f := fun c => (η c) ^ (2 * r)) ?_ (Finset.mem_univ c₀)
  intro i _
  exact (even_two_mul r).pow_nonneg (η i)

/-- **The energy floor is the second moment (the geomean/wall collapse, value form).** The best
the abs-moment ladder delivers at the only bounded-char-0 depth `r = 1` is `√(p - n) = Θ(√(nm))`,
which exceeds the prize scale `C·√(n·log m)` for every fixed `C` once `m` is large: the ratio is
`√((m-1)/log m) → ∞` (here `p - n = n(m-1) + 1 ≥ n(m-1)`). The full ladder reaches the prize scale
only at depth `r ≈ log m`, the open BGK wall. We formalize the divergence of the `r = 1` floor. -/
theorem energy_floor_diverges (C : ℝ) (hC : 0 < C) :
    ∃ m : ℝ, 2 ≤ m ∧ ∀ n : ℝ, 0 < n →
      Real.sqrt (n * (m - 1)) > C * Real.sqrt (n * Real.log m) := by
  -- Witness m = (2C²+2)², so √m = 2C²+2; log m ≤ 2(√m−1); reduce to √m+1 = 2C²+3 > 2C².
  refine ⟨(2 * C ^ 2 + 2) ^ 2, by nlinarith [sq_nonneg C, sq_nonneg (2 * C ^ 2 + 2)], ?_⟩
  intro n hn
  set m : ℝ := (2 * C ^ 2 + 2) ^ 2 with hmdef
  have hsm : Real.sqrt m = 2 * C ^ 2 + 2 := by rw [hmdef]; exact Real.sqrt_sq (by positivity)
  have hm2 : (2 : ℝ) ≤ m := by rw [hmdef]; nlinarith [sq_nonneg C]
  have hmpos : (0 : ℝ) < m := by linarith
  have hlog : Real.log m ≤ 2 * (Real.sqrt m - 1) := by
    have h1 : Real.log (Real.sqrt m) ≤ Real.sqrt m - 1 :=
      Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hmpos)
    have h2 : Real.log m = 2 * Real.log (Real.sqrt m) := by
      rw [Real.log_sqrt (le_of_lt hmpos)]; ring
    rw [h2]; linarith
  have hlogpos : 0 ≤ Real.log m := Real.log_nonneg (by linarith)
  have hradR_nonneg : 0 ≤ n * Real.log m := mul_nonneg (le_of_lt hn) hlogpos
  -- key radicand comparison: C² · (n log m) < n (m-1)
  have hkey : C ^ 2 * (n * Real.log m) < n * (m - 1) := by
    have hmfact : m - 1 = (Real.sqrt m - 1) * (Real.sqrt m + 1) := by
      have hmm : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt (le_of_lt hmpos)
      nlinarith [hmm]
    have hsm_ge : Real.sqrt m - 1 ≥ 0 := by rw [hsm]; nlinarith [sq_nonneg C]
    have step1 : C ^ 2 * (n * Real.log m) ≤ C ^ 2 * (n * (2 * (Real.sqrt m - 1))) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg C)
      exact mul_le_mul_of_nonneg_left hlog (le_of_lt hn)
    have step2 : C ^ 2 * (n * (2 * (Real.sqrt m - 1))) < n * (m - 1) := by
      rw [hmfact, hsm]
      -- goal: C²·(n·2·(2C²+1)) < n·((2C²+1)·(2C²+3))
      -- ⟺ 2C²·(2C²+1) < (2C²+1)(2C²+3): since 2C²+1>0 ⟺ 2C² < 2C²+3. TRUE.
      have hfacpos : (0:ℝ) < 2 * C ^ 2 + 1 := by positivity
      nlinarith [mul_pos hn hfacpos, mul_pos (mul_pos hn hfacpos) hC, sq_nonneg C, hn]
    linarith
  -- conclude by sqrt monotonicity
  have : C * Real.sqrt (n * Real.log m) = Real.sqrt (C ^ 2 * (n * Real.log m)) := by
    rw [Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq (le_of_lt hC)]
  rw [this]
  exact Real.sqrt_lt_sqrt (mul_nonneg (sq_nonneg C) hradR_nonneg) hkey

/-! ## Axiom audit (must be `⊆ {propext, Classical.choice, Quot.sound}`; NO `sorryAx`). -/

#print axioms house_sq_le_p2
#print axioms house_le_sqrt_p2
#print axioms traceForm_le_fujiwara
#print axioms house_pow_le_evenPowerSum
#print axioms energy_floor_diverges

end ArkLib.ProximityGap.Frontier.H2
