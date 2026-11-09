/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# The assembly: prize floor from the SINGLE no-wraparound residual (#444)

This file consolidates the prove-assault: it chains the **maximal proven prefix** of the δ* program into
one end-to-end conditional theorem, reducing the prize to the **single tightest named residual** — that the
char-`p` additive energy has **no `r`-fold wraparound** at the saddle depth `r* ≈ log p`.

## The chain (every step but one is proven)

For the worst nonzero period `M = max_{b≠0}|η_b|`, with `q` the field size and `n = |μ_n|`:

1. **[moment identity, PROVEN in-tree]** `M^{2r} ≤ Σ_{b≠0}‖η_b‖^{2r} = q·E_r − n^{2r}` — the worst term is `≤`
   the mean-zero `2r`-th moment (`DCSubtractedMoment.sum_nonzero_moment` + `Finset.single_le_sum`). Carried
   here as the hypothesis `hMoment` (a theorem, not an assumption, for the concrete `η`/`E_r`).
2. **[no wraparound, THE OPEN RESIDUAL]** `E_r = E_r^{char0}` — the char-`p` energy equals its
   characteristic-`0` value; no `r`-fold additive relation `Σx_i ≡ Σy_i (mod p)` wraps around. The *single*
   open input; equivalent to the onset threshold `r_0(n) > r*` (the `r`-fold sumset of `μ_n` has diameter
   `< p`). Provided concretely by `_NoExcessOnsetThreshold` / `_TwiseIndependenceFramework`. Carried as
   `hNoWrap : E = E0`.
3. **[char-0 bound, PROVEN (Lam–Leung)]** `E_r^{char0} ≤ (2r−1)‼·n^r ≤ (2r·n)^r` — antipodal matchings of
   distinct `2`-power roots. Carried as `hChar0 : E0 ≤ (2r·n)^r` (Mathlib lacks Lam–Leung, so named).
4. **[saddle, PROVEN — inlined below]** `M^{2r} ≤ q·(2r·n)^r` with `q ≤ exp r` (`r ≈ log q`) gives
   `M ≤ √e·√(2r·n) = √(2e·r·n)`, the **prize floor** `M ≤ √(2e·n·log p)` at `r ≈ log p`.

So **the entire prize reduces to step 2 alone** — the no-wraparound residual at `r ≈ log p`. Steps 1, 3, 4
are proven (1, 4 in Lean; 3 in the literature). This file proves `1∧2∧3∧4 ⟹ prize floor` axiom-clean.

## Honest status

This is **not** a proof of the prize: `hNoWrap` at the saddle depth over `F_p` is the open core (equivalent
to BGK — whether short `±1` relations of `2^μ`-th roots vanish mod the prize prime). What this file
contributes is the **tightest consolidation**: prize = (three proven pillars) + (ONE named combinatorial
residual), machine-checked end to end. (Saddle steps `moment_saddle_value` / `saddle_floor` are inlined
copies of the in-tree `MomentSaddleValue` lemmas so this file is self-contained.) Issue #444.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.ProveAssembly

open scoped BigOperators

/-! ## The saddle (self-contained copies of the in-tree `MomentSaddleValue` lemmas) -/

/-- **Moment ⟹ sup value.** `M^{2r} ≤ p·B^r` (`B ≥ 0`) gives `M ≤ p^{1/2r}·√B` (take the `2r`-th root). -/
theorem moment_saddle_value {M p B : ℝ} {r : ℕ} (hr : 0 < r)
    (hM : 0 ≤ M) (hp : 0 ≤ p) (hB : 0 ≤ B)
    (hbound : M ^ (2 * r) ≤ p * B ^ r) :
    M ≤ p ^ (((2 * r : ℕ) : ℝ)⁻¹) * Real.sqrt B := by
  have hr2 : (2 * r : ℕ) ≠ 0 := by positivity
  have hMpow : (0 : ℝ) ≤ M ^ (2 * r) := by positivity
  have step1 : M ≤ (p * B ^ r) ^ (((2 * r : ℕ) : ℝ)⁻¹) := by
    calc M = (M ^ (2 * r)) ^ (((2 * r : ℕ) : ℝ)⁻¹) := (Real.pow_rpow_inv_natCast hM hr2).symm
      _ ≤ (p * B ^ r) ^ (((2 * r : ℕ) : ℝ)⁻¹) := Real.rpow_le_rpow hMpow hbound (by positivity)
  have hsqrt : (B ^ r) ^ (((2 * r : ℕ) : ℝ)⁻¹) = Real.sqrt B := by
    rw [← Real.rpow_natCast B r, ← Real.rpow_mul hB, Real.sqrt_eq_rpow]
    congr 1
    push_cast
    rw [mul_inv_eq_iff_eq_mul₀ (by positivity)]
    ring
  have step2 : (p * B ^ r) ^ (((2 * r : ℕ) : ℝ)⁻¹) = p ^ (((2 * r : ℕ) : ℝ)⁻¹) * Real.sqrt B := by
    rw [Real.mul_rpow hp (by positivity), hsqrt]
  rw [step2] at step1; exact step1

/-- **Saddle floor.** `M^{2r} ≤ q·(2r·n)^r` with `q ≤ exp r` gives `M ≤ √e·√(2r·n)` (the prize floor at
`r ≈ log q`), via `q^{1/2r} ≤ (exp r)^{1/2r} = exp(1/2) = √e`. -/
theorem saddle_floor {M q n : ℝ} {r : ℕ} (hr : 0 < r) (hM : 0 ≤ M) (hq : 0 ≤ q) (hn : 0 ≤ n)
    (hWick : M ^ (2 * r) ≤ q * (2 * r * n) ^ r) (hdepth : q ≤ Real.exp r) :
    M ≤ Real.sqrt (Real.exp 1) * Real.sqrt (2 * r * n) := by
  have hsaddle := moment_saddle_value hr hM hq (by positivity : (0:ℝ) ≤ 2 * r * n) hWick
  refine le_trans hsaddle ?_
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  have hrinv : (0 : ℝ) ≤ (((2 * r : ℕ) : ℝ))⁻¹ := by positivity
  calc q ^ (((2 * r : ℕ) : ℝ))⁻¹
      ≤ (Real.exp (r : ℝ)) ^ (((2 * r : ℕ) : ℝ))⁻¹ := Real.rpow_le_rpow hq hdepth hrinv
    _ = Real.sqrt (Real.exp 1) := by
        rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, Real.sqrt_eq_rpow,
            Real.rpow_def_of_pos (Real.exp_pos 1), Real.log_exp]
        congr 1
        have hrne : (r : ℝ) ≠ 0 := by positivity
        push_cast
        field_simp

/-! ## The assembly -/

/-- **★ The assembly: prize floor from the single no-wraparound residual.** Chaining the four pillars
(moment identity `hMoment`, the OPEN no-wraparound residual `hNoWrap : E = E0`, the proven char-0 bound
`hChar0` in envelope form, and the saddle), the worst nonzero period obeys the prize floor
`M ≤ √e·√(2r·n)`. At `r ≈ log p` this is `M ≤ √(2e·n·log p)`. The ONLY open input is `hNoWrap`. -/
theorem prize_floor_of_noWraparound
    {M q n E E0 : ℝ} {r : ℕ} (hr : 0 < r) (hM : 0 ≤ M) (hq : 0 ≤ q) (hn : 0 ≤ n)
    (hMoment : M ^ (2 * r) ≤ q * E - n ^ (2 * r))
    (hNoWrap : E = E0)
    (hChar0 : E0 ≤ (2 * r * n) ^ r)
    (hdepth : q ≤ Real.exp r) :
    M ≤ Real.sqrt (Real.exp 1) * Real.sqrt (2 * r * n) := by
  have hWick : M ^ (2 * r) ≤ q * (2 * r * n) ^ r := by
    have h1 : M ^ (2 * r) ≤ q * E := by
      have : (0 : ℝ) ≤ n ^ (2 * r) := pow_nonneg hn (2 * r)
      linarith
    have h2 : E ≤ (2 * r * n) ^ r := by rw [hNoWrap]; exact hChar0
    calc M ^ (2 * r) ≤ q * E := h1
      _ ≤ q * (2 * r * n) ^ r := mul_le_mul_of_nonneg_left h2 hq
  exact saddle_floor hr hM hq hn hWick hdepth

/-- **The residual is the whole gap (contrapositive).** If the prize floor *fails* at the saddle depth
(with the proven pillars in place), the no-wraparound residual must fail — there IS an `r`-fold wraparound
`E ≠ E0`. A prize counterexample would exhibit a genuine additive wraparound among the `2`-power roots: the
only escape. -/
theorem wraparound_of_prize_fails
    {M q n E E0 : ℝ} {r : ℕ} (hr : 0 < r) (hM : 0 ≤ M) (hq : 0 ≤ q) (hn : 0 ≤ n)
    (hMoment : M ^ (2 * r) ≤ q * E - n ^ (2 * r))
    (hChar0 : E0 ≤ (2 * r * n) ^ r)
    (hdepth : q ≤ Real.exp r)
    (hfail : ¬ (M ≤ Real.sqrt (Real.exp 1) * Real.sqrt (2 * r * n))) :
    E ≠ E0 := fun hEq => hfail (prize_floor_of_noWraparound hr hM hq hn hMoment hEq hChar0 hdepth)

end ArkLib.ProximityGap.Frontier.ProveAssembly

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.ProveAssembly.moment_saddle_value
#print axioms ArkLib.ProximityGap.Frontier.ProveAssembly.saddle_floor
#print axioms ArkLib.ProximityGap.Frontier.ProveAssembly.prize_floor_of_noWraparound
#print axioms ArkLib.ProximityGap.Frontier.ProveAssembly.wraparound_of_prize_fails
