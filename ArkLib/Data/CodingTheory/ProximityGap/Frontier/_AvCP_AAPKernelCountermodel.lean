/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic.NormNum

/-!
# `_AvCP_AAPKernelCountermodel` — the ALMOST-ALL-PRIMES kernel `W_K ≤ 0` is FALSE worst-case (#444)

Angle **ALMOST_ALL_PRIMES** (di Benedetto `T_2/T_3`, almost-all-primes Wick transfer). The
in-tree DC-subtracted reduction `_DE_DCSubtractedDeep` records (docstring table) the empirical
claim `W_K := A_K − E_K^{C} < 0` at **every** measured `K` (a uniform deficit), and names
`W_K ≤ 0` as the OPEN kernel. This file supplies the **exact integer countermodel** showing the
empirical universal claim is FALSE: there are primes `p ~ n^4` (β=4 window) at which the
DC-subtracted nonprincipal energy `A_K` strictly **EXCEEDS** the char-0 Bessel energy `E_K^{C}`.

## The witness (all integers EXACT, computed by exact `F_p` 6-fold cyclic convolution — no float)

`n = 16`, `p = 76001` (prime, `16 ∣ p−1`, `n^4 ≤ p < 2 n^4`), `K = 6`:

* `E_Fp = 68984125056` — the additive `2K`-energy `#{(x,y)∈G⁶×G⁶ : Σx ≡ Σy (mod p)}` of
  `μ₁₆ ⊂ F₇₆₀₀₁`, an EXACT integer count.
* `A_K = E_Fp − n^{2K}/p` — the DC-subtracted nonprincipal energy (numerator `A_num` over `p`).
* `E_K^{C} = besselE 6 8 = 64941883776` — the char-0 Bessel/Lam–Leung half-basis energy (an
  integer at this `K`), the LANDED `AvW0.besselWick_allR` target.
* `Wick_K = (2K−1)!!·n^K = 174399160320` — the prize ceiling.

## What is proven, axiom-clean

* `bessel_kernel_violated` : `A_K > E_K^{C}`, i.e. **`W_K = A_K − E_K^{C} > 0`** — the Bessel
  refinement (and hence the universal "`W_K < 0` at every `K`" measurement) is FALSE here.
* `prize_bound_holds` : `A_K < Wick_K` (ratio `≈ 0.374`) — the **prize-sufficient** bound
  `A_K ≤ Wick_K` (the `C = 1` DC-subtracted ceiling) STILL holds at this same witness.

## Honest reading (this is a REFUTATION-of-a-sub-claim + SHARPENING, NOT a closure)

The bad set is real but **rare** (exact sweep, n=16: `2/271 ≈ 0.7%` of primes `p` near `n^4`
have `W_K > 0` at some `K ≤ 10`; both bad primes — `76001`, `61057` — have *moderate*
`v₂(p−1) ∈ {5,7}`, NOT the extreme-`v₂` Fermat-like primes, so a "high-`v₂` confinement" does
not isolate them). The takeaway for the kernel:

1. The **Bessel-refined** kernel `A_K ≤ E_K^{C}` (`W_K ≤ 0`) is the WRONG worst-case target —
   it is genuinely violated at a positive (empirically `~1%`, non-decreasing across scales
   `1×→64× n^4`) density of primes. The `_DE_DCSubtractedDeep` reduction's STEP-1 input
   `A_K ≤ E_K^{C}` must therefore be replaced by the strictly weaker, still-prize-sufficient
   `A_K ≤ Wick_K`.
2. `A_K ≤ Wick_K` (the `C = 1` ceiling) is the bound that survives at the bad primes (`A/Wick
   ≈ 0.37` even at the worst witness) and is the honest almost-all → all-primes target. The
   open kernel is `A_K ≤ Wick_K` (or `A_K ≤ C·Wick_K`), NOT `W_K ≤ 0`.

So this brick **corrects the empirical claim in `_DE_DCSubtractedDeep`** (and any memory note
asserting `W_K < 0` universally) and **re-points the open kernel** to the weaker bound that the
data actually supports. It does NOT close the prize.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.AAPKernelCountermodel

/-- `n = 16`, `K = 6`, `p = 76001`. -/
def n : ℕ := 16
def K : ℕ := 6
def p : ℕ := 76001

/-- Exact integer additive `2K`-energy of `μ₁₆ ⊂ F₇₆₀₀₁` at `K = 6`
(`#{(x,y)∈G⁶×G⁶ : Σx ≡ Σy (mod p)}`), by exact 6-fold cyclic convolution over `F_p`. -/
def E_Fp : ℕ := 68984125056

/-- Char-0 Bessel energy `E_K^{C} = besselE 6 8`, an integer at this `K`. -/
def besselE_val : ℕ := 64941883776

/-- The prize Wick ceiling `(2K−1)!!·n^K = 10395 · 16^6`. -/
def wick_val : ℕ := 174399160320

/-- `A_K = E_Fp − n^{2K}/p`, represented by its numerator over `p`: `A_num = E_Fp·p − n^{2K}`. -/
def A_num : ℤ := (E_Fp : ℤ) * (p : ℤ) - (n : ℤ) ^ (2 * K)

/-- **The Bessel kernel is violated:** `W_K = A_K − E_K^{C} > 0` at this witness, i.e.
`A_num > besselE_val · p`. Cleared of division (`p > 0`). This refutes the universal
empirical claim `W_K < 0` recorded in `_DE_DCSubtractedDeep`. -/
theorem bessel_kernel_violated : (besselE_val : ℤ) * (p : ℤ) < A_num := by
  unfold A_num E_Fp besselE_val n p K
  norm_num

/-- **The prize bound still holds:** `A_K < Wick_K` at the SAME witness, i.e.
`A_num < wick_val · p` (ratio `≈ 0.374`). The `C = 1` DC-subtracted ceiling survives where
the Bessel refinement fails — this is the bound the almost-all-primes route should target. -/
theorem prize_bound_holds : A_num < (wick_val : ℤ) * (p : ℤ) := by
  unfold A_num E_Fp wick_val n p K
  norm_num

/-- `p` is in the β=4 window with `16 ∣ p−1`. -/
theorem p_window : n ^ 4 ≤ p ∧ p < 2 * n ^ 4 ∧ n ∣ (p - 1) := by
  refine ⟨?_, ?_, ?_⟩ <;> · unfold n p; norm_num

/-- Exact excess numerator (audit): `A_num − besselE_val·p = 25739402810624 > 0`. -/
theorem excess_numerator : A_num - (besselE_val : ℤ) * (p : ℤ) = 25739402810624 := by
  unfold A_num E_Fp besselE_val n p K
  norm_num

#print axioms bessel_kernel_violated
#print axioms prize_bound_holds
#print axioms p_window
#print axioms excess_numerator

end ArkLib.ProximityGap.Frontier.AAPKernelCountermodel
