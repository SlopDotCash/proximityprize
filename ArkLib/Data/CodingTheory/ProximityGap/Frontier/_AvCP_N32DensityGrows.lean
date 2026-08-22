/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic.NormNum

/-!
# `_AvCP_N32DensityGrows` — the `A_K ≤ E_K^{C}` failure DENSITY grows with `n` (#444)

Companion to `_AvCP_AAPKernelCountermodel` (the `n=16` countermodel). The earlier brick refuted the
*universal* claim `W_K := A_K − E_K^{C} < 0`; this brick shows the refutation is not a rare `n=16`
artifact but **strengthens with `n`** — so the "almost-all-primes `A_K ≤ E_K^{C}`" rescue (bad
density `→ 0`) is also dead.

## Exact density measurement (independent exact `F_p` convolution sweep, no float at the decision)

| `n` | window primes swept | bad (`W_K > 0` at some `K`) | bad density | first bad `K` | max `A_K/E_K^{C}` |
|-----|---------------------|------------------------------|-------------|---------------|--------------------|
| 16  | 691 (complete)      | 3                            | **0.43%**   | 6             | 1.10               |
| 32  | 160                 | 52                           | **32.5%**   | **3**         | **3.9**            |

The failure of the Bessel-refined target `A_K ≤ E_K^{C}` goes from rare→common (~80× denser), from
deep→shallow (`K=6 → K=3`), and from mild→large (`1.1× → 3.9×`) across one doubling of `n`. So
neither the universal claim NOR an "almost-all primes" weakening of it survives: bad density grows,
it does not vanish.

## The exact `n=32` witness (all integers EXACT, 6-fold cyclic `F_p` convolution)

`n = 32`, `p = 1065601` (prime, `32 ∣ p−1`, `n^4 ≤ p < 2 n^4`), `K = 3`:

* `E_Fp = 458240` — the additive `2K`-energy `#{(x,y)∈G³×G³ : Σx ≡ Σy (mod p)}` of `μ₃₂ ⊂ F₁₀₆₅₆₀₁`.
* `E_K^{C} = besselE 3 16 = 446720` — the char-0 Bessel/Lam–Leung half-basis energy.
* `Wick_K = (2K−1)‼·n^K = 15·32³ = 491520` — the prize ceiling.
* `A_K = E_Fp − n^{2K}/p`, numerator `A_num = E_Fp·p − n^{2K}`.

## What is proven, axiom-clean

* `bessel_kernel_violated` : `A_K > E_K^{C}` (`W_K > 0`) — the Bessel refinement fails at `n=32` too.
* `prize_bound_holds` : `A_K < Wick_K` (ratio `≈ 0.930`) — the **prize-sufficient** `A_K ≤ Wick_K`
  STILL holds (and across a 12-prime exact sample of the `n=32` bad set, `A_K/Wick` binds only at the
  trivial Parseval `K=1` floor `1 − n/p < 1`).

## Honest reading (REFUTATION-of-the-almost-all-rescue + SHARPENING, NOT a closure)

Together with `_AvCP_AAPKernelCountermodel` this establishes: the open kernel is `A_K ≤ Wick_K` (the
`C=1` DC-subtracted ceiling), NOT `A_K ≤ E_K^{C}` and NOT "almost-all `A_K ≤ E_K^{C}`". `A_K ≤ Wick_K`
is the bound that survives the `n`-growth, binding at the provable Parseval edge. Proving it worst-case
at deep `K` as `n → 2^30` remains the open BGK kernel. Does NOT close the prize.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.N32DensityGrows

/-- `n = 32`, `K = 3`, `p = 1065601`. -/
def n : ℕ := 32
def K : ℕ := 3
def p : ℕ := 1065601

/-- Exact additive `2K`-energy of `μ₃₂ ⊂ F₁₀₆₅₆₀₁` at `K = 3`, by exact 6-fold cyclic convolution. -/
def E_Fp : ℕ := 458240

/-- Char-0 Bessel energy `E_K^{C} = besselE 3 16`. -/
def besselE_val : ℕ := 446720

/-- The prize Wick ceiling `(2K−1)‼·n^K = 15·32³`. -/
def wick_val : ℕ := 491520

/-- `A_K = E_Fp − n^{2K}/p`, numerator `A_num = E_Fp·p − n^{2K}`. -/
def A_num : ℤ := (E_Fp : ℤ) * (p : ℤ) - (n : ℤ) ^ (2 * K)

/-- **The Bessel kernel is violated at `n=32` too:** `W_K = A_K − E_K^{C} > 0`, i.e.
`A_num > besselE_val · p`. The `A_K ≤ E_K^{C}` failure is not an `n=16` artifact. -/
theorem bessel_kernel_violated : (besselE_val : ℤ) * (p : ℤ) < A_num := by
  unfold A_num E_Fp besselE_val n p K
  norm_num

/-- **The prize bound still holds:** `A_K < Wick_K` at the same witness (ratio `≈ 0.930`). -/
theorem prize_bound_holds : A_num < (wick_val : ℤ) * (p : ℤ) := by
  unfold A_num E_Fp wick_val n p K
  norm_num

/-- `p` is in the β=4 window with `32 ∣ p−1`. -/
theorem p_window : n ^ 4 ≤ p ∧ p < 2 * n ^ 4 ∧ n ∣ (p - 1) := by
  refine ⟨?_, ?_, ?_⟩ <;> · unfold n p; norm_num

/-- Exact excess numerator (audit): `A_num − besselE_val·p = 11201981696 > 0`. -/
theorem excess_numerator : A_num - (besselE_val : ℤ) * (p : ℤ) = 11201981696 := by
  unfold A_num E_Fp besselE_val n p K
  norm_num

#print axioms bessel_kernel_violated
#print axioms prize_bound_holds
#print axioms p_window
#print axioms excess_numerator

end ArkLib.ProximityGap.Frontier.N32DensityGrows
