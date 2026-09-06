/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (wf-W1)
-/
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.PSeries

/-!
# wf-W1 — the Wick→Gaussian MGF bridge (the per-`r` ⟹ all-`r`-at-once converter, #444)

**Strategy (MGF / saddle-point).** The cosh-MGF identity `CoshMGFIdentity.lean` (PROVEN) is
`∑_b cosh(‖η_b‖y) = ∑_r (q·E_r/(2r)!) y^{2r}`, and the saddle consumer
`_CoshMGFSaddle.period_le_of_mgfBound` (PROVEN) discharges the prize sup-norm floor
**conditionally** on the single inequality `∑_r (q·E_r/(2r)!) y^{2r} ≤ q·exp(n y²/2)`.

This file lands the **bridge that converts a per-`r` Wick bound into exactly that Gaussian MGF**,
so the whole moment sequence is handled at once (no per-`r` bookkeeping):

> **`mgf_le_exp_of_wick`** : if `0 ≤ a r ≤ K^r·(2r−1)‼·n^r` for every `r` (the Wick hypothesis,
> with `K, n ≥ 0`, `y` real), then `∑'_r a r · y^{2r}/(2r)! ≤ exp(K·n·y²/2)`.

The engine is the double-factorial collapse `(2r−1)‼·2^r·r! = (2r)!`
(`Nat.factorial_eq_mul_doubleFactorial` + `Nat.doubleFactorial_two_mul`), which turns the Wick
term into the *Gaussian* term:
`K^r·(2r−1)‼·n^r·y^{2r}/(2r)! = (K·n·y²/2)^r / r!`, whose `tsum` is `exp(K·n·y²/2)`.

**Honest scope (the W1 lane finding).** Numerics (`scripts/probes/rust/wf7W1_*.rs`) show that the
DC-subtracted char-`p` MGF `Φ_p^{nz}(y) = (1/q)∑_{b≠0}cosh(η_b y)` satisfies the *Gaussian* bound
`Φ_p^{nz}(y) ≤ exp(n y²/2)` **uniformly** (max ratio `≤ 1` for `n = 16..256`, value `0.04–0.19`
at the saddle), whereas the **stronger** `K = 1` form `Φ_p^{nz} ≤ I₀(2y)^{n/2}` (char-0 Bessel)
**FAILS at `n = 128`** (ratio `1.091` at `y = 0.4`): the spurious mod-`p` excess at intermediate
`r` is real, so char-`p` Wick needs `K > 1` — but the Gaussian envelope absorbs it. Hence the
correct hypothesis fed to this bridge is the **`K`-Wick** per-`r` bound `A_r ≤ K^r(2r−1)‼n^r` with
an absolute `K`, NOT `K = 1`. This file proves the bridge axiom-clean; the per-`r` `K`-Wick bound
itself (equivalently `Φ_p^{nz} ≤ exp(Kn y²/2)` directly) is the named open core (the BGK saddle).

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`.  Issue #444 (wf-W1).
-/

open scoped BigOperators
open Finset Nat

namespace ProximityGap.Frontier.WickToGaussianMGF

/-- **Double-factorial collapse.** `(2r−1)‼ · (2^r · r!) = (2r)!`. For `r = 0` both sides are `1`;
for `r = s+1`, `2(s+1) = (2s+1)+1`, so `(2(s+1))! = (2(s+1))‼ · (2s+1)‼`
(`Nat.factorial_eq_mul_doubleFactorial`) and `(2(s+1))‼ = 2^{s+1}·(s+1)!`
(`Nat.doubleFactorial_two_mul`). -/
theorem doubleFactorial_collapse (r : ℕ) :
    (2 * r - 1)‼ * (2 ^ r * r.factorial) = (2 * r).factorial := by
  cases r with
  | zero => simp
  | succ s =>
    have hm : 2 * (s + 1) - 1 = 2 * s + 1 := by omega
    have he : 2 * (s + 1) = (2 * s + 1) + 1 := by ring
    rw [hm, he, Nat.factorial_eq_mul_doubleFactorial (2 * s + 1)]
    have hdf : (2 * s + 1 + 1)‼ = 2 ^ (s + 1) * (s + 1).factorial := by
      have h2 : 2 * s + 1 + 1 = 2 * (s + 1) := by ring
      rw [h2, Nat.doubleFactorial_two_mul]
    rw [hdf]; ring

/-- **The Wick→Gaussian MGF bridge (W1).** If a nonnegative real moment sequence `a` is dominated
per-`r` by the `K`-Wick envelope `a r ≤ K^r·(2r−1)‼·n^r` (`K, n ≥ 0`), then its even-moment MGF is
dominated by the Gaussian: `∑'_r a r · y^{2r}/(2r)! ≤ exp(K·n·y²/2)`, for every real `y`. This is the
"all-`r` at once" converter: the per-`r` Wick bound (one inequality per moment) collapses to the single
Gaussian MGF bound the saddle consumer (`_CoshMGFSaddle.period_le_of_mgfBound`) consumes. -/
theorem mgf_le_exp_of_wick {a : ℕ → ℝ} {K n y : ℝ}
    (hK : 0 ≤ K) (hn : 0 ≤ n)
    (ha0 : ∀ r, 0 ≤ a r)
    (haW : ∀ r, a r ≤ K ^ r * ((2 * r - 1)‼ : ℝ) * n ^ r) :
    (∑' r : ℕ, a r * y ^ (2 * r) / ((2 * r).factorial : ℝ))
      ≤ Real.exp (K * n * y ^ 2 / 2) := by
  set t : ℝ := K * n * y ^ 2 / 2 with ht
  -- RHS as the exp power series over ℝ
  have hexp : Real.exp t = ∑' r : ℕ, t ^ r / (r.factorial : ℝ) := by
    have h1 : Real.exp t = NormedSpace.exp t := by rw [Real.exp_eq_exp_ℝ]
    rw [h1, NormedSpace.exp_eq_tsum_div]
  -- the comparison (exp) series is summable
  have hgsum : Summable (fun r : ℕ => t ^ r / (r.factorial : ℝ)) :=
    Real.summable_pow_div_factorial t
  -- termwise bound: a r y^{2r}/(2r)! ≤ t^r / r!
  have hterm : ∀ r, a r * y ^ (2 * r) / ((2 * r).factorial : ℝ) ≤ t ^ r / (r.factorial : ℝ) := by
    intro r
    have hfac2 : (0 : ℝ) < ((2 * r).factorial : ℝ) := by exact_mod_cast (2 * r).factorial_pos
    have hfacr : (0 : ℝ) < (r.factorial : ℝ) := by exact_mod_cast r.factorial_pos
    have hy2r : (0 : ℝ) ≤ y ^ (2 * r) := by rw [pow_mul]; positivity
    have hnum : a r * y ^ (2 * r) ≤ (K ^ r * ((2 * r - 1)‼ : ℝ) * n ^ r) * y ^ (2 * r) :=
      mul_le_mul_of_nonneg_right (haW r) hy2r
    -- collapse identity cast to ℝ
    have hcollapse :
        (((2 * r - 1)‼ : ℕ) : ℝ) * ((2 : ℝ) ^ r * (r.factorial : ℝ)) = ((2 * r).factorial : ℝ) := by
      have h := doubleFactorial_collapse r
      exact_mod_cast h
    -- the Wick term equals the Gaussian term
    have hkey : (K ^ r * ((2 * r - 1)‼ : ℝ) * n ^ r) * y ^ (2 * r) / ((2 * r).factorial : ℝ)
        = t ^ r / (r.factorial : ℝ) := by
      rw [ht, ← hcollapse]
      have hyr : y ^ (2 * r) = (y ^ 2) ^ r := by rw [← pow_mul, Nat.mul_comm]
      have h2r : (2 : ℝ) ^ r ≠ 0 := by positivity
      have hdf : (((2 * r - 1)‼ : ℕ) : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.doubleFactorial_pos (2 * r - 1)).ne'
      rw [hyr, div_pow, mul_pow, mul_pow,
        div_eq_div_iff (by positivity) (ne_of_gt hfacr)]
      field_simp
    calc a r * y ^ (2 * r) / ((2 * r).factorial : ℝ)
        ≤ (K ^ r * ((2 * r - 1)‼ : ℝ) * n ^ r) * y ^ (2 * r) / ((2 * r).factorial : ℝ) :=
          (div_le_div_iff_of_pos_right hfac2).mpr hnum
      _ = t ^ r / (r.factorial : ℝ) := hkey
  -- the LHS series is summable (nonneg, termwise ≤ summable)
  have hasum : Summable (fun r : ℕ => a r * y ^ (2 * r) / ((2 * r).factorial : ℝ)) := by
    refine Summable.of_nonneg_of_le (fun r => ?_) (fun r => hterm r) hgsum
    have hy2r : (0 : ℝ) ≤ y ^ (2 * r) := by rw [pow_mul]; positivity
    have hfac2 : (0 : ℝ) ≤ ((2 * r).factorial : ℝ) := by positivity
    have := ha0 r
    positivity
  calc (∑' r : ℕ, a r * y ^ (2 * r) / ((2 * r).factorial : ℝ))
      ≤ ∑' r : ℕ, t ^ r / (r.factorial : ℝ) := hasum.tsum_le_tsum hterm hgsum
    _ = Real.exp t := hexp.symm

end ProximityGap.Frontier.WickToGaussianMGF

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.WickToGaussianMGF.doubleFactorial_collapse
#print axioms ProximityGap.Frontier.WickToGaussianMGF.mgf_le_exp_of_wick
