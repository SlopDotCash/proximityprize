/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# The char-0 MGF Bessel bound: the entire char-0 face of the prize, in one inequality (#444)

The char-0 additive energy of the 2-power subgroup `μ_n` packages into a **modified-Bessel generating
function**: with `E_r(ℂ) = (2r)!·[z^r] f(z)^{n/2}`, `f(z) = Σ_k z^k/(k!)²`,
```
Σ_r  E_r(ℂ)/(2r)! · y^{2r}  =  f(y²)^{n/2}  =  I₀(2y)^{n/2},        I₀(2y) = Σ_k y^{2k}/(k!)².
```
So the char-0 cosh-MGF is `Ψ₀(y) = q·I₀(2y)^{n/2}`. The sub-Gaussian prize bound
`Ψ(y) ≤ q·exp(n y²/2)` (at the saddle `y* = √(2 ln q / n)` this gives `Ψ(y*) ≤ q²`, hence
`B = max_{b≠0}‖η_b‖ ≤ √(2n ln q)`, the prize) holds in char 0 because of the **trivial coefficient
inequality** `1/(k!)² ≤ 1/k!` (i.e. `(k!)² ≥ k!`):
```
I₀(2y) = Σ_k y^{2k}/(k!)²  ≤  Σ_k y^{2k}/k!  =  exp(y²),   so   I₀(2y)^{n/2} ≤ exp(n y²/2).
```

This file proves exactly that, axiom-clean:
- `besselI0Two_le_exp_sq` : `Σ_k y^{2k}/(k!)² ≤ exp(y²)` for `y ≥ 0` (the heart — termwise `(k!)² ≥ k!`);
- `besselI0Two_pow_le_exp` : `(Σ_k y^{2k}/(k!)²)^m ≤ exp(m·y²)` — the **char-0 MGF sub-Gaussian bound**
  (`m = n/2`), the char-0 face of the prize.

Coefficient-by-coefficient this *is* the char-0 Gaussian/Lam–Leung energy bound `E_r(ℂ) ≤ (2r−1)‼·n^r`
**for all `r`** (cf. `_CharZeroEnergyClosedForm`, which proved it only `r ≤ 6` by `nlinarith`); the Bessel
form gives the clean uniform-in-`r` proof.

**HONESTY.** This is the *char-0* MGF. The prize needs the *char-p* MGF `Ψ_p(y) = Σ_{b≠0} cosh(η_b y)`; the
open core is exactly the char-p excess `Ψ_p − Ψ₀ > 0` (= `Spur_r` = the onset-threshold `W_r`), which at the
prize-binding depth is the collision-saturated, p-dependent BGK/BCHKS-1.12 wall. This file proves the char-0
face is clean; it does **not** cross the wall. Issue #444.
-/

namespace ProximityGap.Frontier.CharZeroMGFBessel

open scoped Nat

/-- The modified Bessel value `I₀(2y) = Σ_k y^{2k}/(k!)²` (the char-0 energy MGF base). -/
noncomputable def besselI0Two (y : ℝ) : ℝ := ∑' k : ℕ, y ^ (2 * k) / (k.factorial : ℝ) ^ 2

/-- `exp(y²) = Σ_k y^{2k}/k!` (the exponential series, reindexed through `(y²)^k = y^{2k}`). -/
theorem exp_sq_eq_tsum (y : ℝ) :
    Real.exp (y ^ 2) = ∑' k : ℕ, y ^ (2 * k) / (k.factorial : ℝ) := by
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  refine tsum_congr (fun k => ?_)
  rw [← pow_mul, mul_comm 2 k]

/-- Summability of the exponential series `Σ_k y^{2k}/k!`. -/
theorem summable_exp_terms (y : ℝ) :
    Summable (fun k : ℕ => y ^ (2 * k) / (k.factorial : ℝ)) := by
  have := Real.summable_pow_div_factorial (y ^ 2)
  refine this.congr (fun k => ?_)
  rw [← pow_mul, mul_comm 2 k]

/-- The termwise bound: `y^{2k}/(k!)² ≤ y^{2k}/k!` for `y ≥ 0` (since `(k!)² ≥ k! ≥ 1`). -/
theorem bessel_term_le_exp_term (y : ℝ) (hy : 0 ≤ y) (k : ℕ) :
    y ^ (2 * k) / (k.factorial : ℝ) ^ 2 ≤ y ^ (2 * k) / (k.factorial : ℝ) := by
  have hk1 : (1 : ℝ) ≤ (k.factorial : ℝ) := by exact_mod_cast k.factorial_pos
  have hkpos : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast k.factorial_pos
  have hle : (k.factorial : ℝ) ≤ (k.factorial : ℝ) ^ 2 := by nlinarith [hk1, hkpos]
  exact div_le_div_of_nonneg_left (by positivity) hkpos hle

/-- Summability of the Bessel series `Σ_k y^{2k}/(k!)²` (comparison with the exp series). -/
theorem summable_bessel_terms (y : ℝ) (hy : 0 ≤ y) :
    Summable (fun k : ℕ => y ^ (2 * k) / (k.factorial : ℝ) ^ 2) := by
  refine Summable.of_nonneg_of_le (fun k => by positivity)
    (fun k => bessel_term_le_exp_term y hy k) (summable_exp_terms y)

/-- **The Bessel inequality (heart of the char-0 prize face):** `I₀(2y) ≤ exp(y²)` for `y ≥ 0`. -/
theorem besselI0Two_le_exp_sq (y : ℝ) (hy : 0 ≤ y) :
    besselI0Two y ≤ Real.exp (y ^ 2) := by
  rw [besselI0Two, exp_sq_eq_tsum]
  exact Summable.tsum_le_tsum (fun k => bessel_term_le_exp_term y hy k)
    (summable_bessel_terms y hy) (summable_exp_terms y)

/-- `0 ≤ I₀(2y)`. -/
theorem besselI0Two_nonneg (y : ℝ) (hy : 0 ≤ y) : 0 ≤ besselI0Two y :=
  tsum_nonneg (fun k => by positivity)

/-- **The char-0 MGF sub-Gaussian bound (the char-0 face of the prize).** For `m = n/2`,
`I₀(2y)^m ≤ exp(m·y²)`. Since the char-0 cosh-MGF is `Ψ₀(y) = q·I₀(2y)^{n/2}`, this is
`Ψ₀(y) ≤ q·exp(n y²/2)`, which at the saddle `y* = √(2 ln q / n)` gives `Ψ₀(y*) ≤ q²` — the char-0
per-frequency bound `B ≤ √(2n ln q)`. The char-p excess is the open core. -/
theorem besselI0Two_pow_le_exp (y : ℝ) (hy : 0 ≤ y) (m : ℕ) :
    besselI0Two y ^ m ≤ Real.exp ((m : ℝ) * y ^ 2) := by
  calc besselI0Two y ^ m
      ≤ Real.exp (y ^ 2) ^ m :=
        pow_le_pow_left₀ (besselI0Two_nonneg y hy) (besselI0Two_le_exp_sq y hy) m
    _ = Real.exp ((m : ℝ) * y ^ 2) := by
        rw [← Real.exp_nat_mul]

end ProximityGap.Frontier.CharZeroMGFBessel

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.CharZeroMGFBessel.besselI0Two_le_exp_sq
#print axioms ProximityGap.Frontier.CharZeroMGFBessel.besselI0Two_pow_le_exp
