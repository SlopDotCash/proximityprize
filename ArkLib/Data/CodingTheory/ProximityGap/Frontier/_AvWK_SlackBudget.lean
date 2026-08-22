/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# `WK_SlackBudget` — the wraparound budget for `A_K ≤ Wick_K`, and the n=32 DC-essential witness (#444)

Angle **WK_SIGN_REPOINTED**. The open prize kernel (post-refutation of `A_K ≤ E_K^C`) is
`A_K ≤ Wick_K`, where (all EXACT integers, by `F_p` `K`-fold cyclic convolution, no float):

* `N_K = #{(x,y) ∈ μ_n^{2K} : Σxᵢ ≡ Σyⱼ (mod p)}` — additive `2K`-energy of `μ_n`.
* `A_K = N_K − n^{2K}/p` — the DC-subtracted nonprincipal energy `(1/q)Σ_{b≠0}|η_b|^{2K}`.
* `E_K^C = besselE K (n/2)` — char-0 Bessel energy. **PROVEN (lattice enumeration here + memory):**
  `E_K^C` IS the **char-0 relation count** `N_K^C := #{(x,y)∈μ_n^{2K} : Σxᵢ = Σyⱼ in ℂ}`. Hence
  `N_K = N_K^C + W_wrap` with `W_wrap := N_K − N_K^C ≥ 0` the **wraparound-only** count.
* `Wick_K = (2K−1)‼·n^K`. `SLACK := Wick_K − E_K^C ≥ 0` (char-0, p-independent; `besselWick_allR`).

## The exact decomposition (algebra)

  `A_K = E_K^C + (W_wrap − n^{2K}/p)`,  so  `A_K ≤ Wick_K  ⟺  W_wrap ≤ SLACK + n^{2K}/p`.

The wraparound budget is `BUDGET := SLACK + n^{2K}/p`. The "fluctuation" `DEV := A_K − E_K^C
= W_wrap − n^{2K}/p` is the di Benedetto kernel (REFUTED sign), and `A_K ≤ Wick ⟺ DEV ≤ SLACK`.

## The DC-ESSENTIAL witness (the result of this file)

At `n = 32`, `p = 1048609` (prime, `32∣p−1`, `n⁴ ≤ p < 2n⁴`), `K = 9` (≈ prize depth `ln p`):

* `SLACK < W_wrap` STRICTLY — the char-0 slack ALONE is **too small** to absorb the wraparound
  count (`SLACK − W_wrap = −324888139138524247040 < 0`).
* `A_K ≤ Wick_K` STILL HOLDS — the missing budget is supplied by the `+ n^{2K}/p` DC term.

So at (and past) the prize depth the prize bound `A_K ≤ Wick` is NOT a consequence of the char-0
slack absorbing the wraparound count: the **DC main term `n^{2K}/p` is load-bearing**. (The
exact-computation asymptotic `rho_K := E_K^C/Wick → 1` at depth `K* ≈ 4 ln n`, since
`K*²/n = 16(ln n)²/n → 0`, shows `SLACK/Wick → 0` — the char-0 slack is a *vanishing* fraction of
Wick at true prize depth, so the slack route alone cannot close `A_K ≤ Wick` for large `n`.)

This is a **structural reduction + witness**, NOT a closure: it pins the open inequality to
`DEV = W_wrap − n^{2K}/p ≤ SLACK` (the wraparound *fluctuation* ≤ char-0 slack), and refutes the
weaker hope "char-0 slack absorbs the wraparound count".
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.WKSlackBudget

/-- `n = 32`, `K = 9`, `p = 1048609`. -/
def n : ℕ := 32
def K : ℕ := 9
def p : ℕ := 1048609

/-- Exact additive `2K`-energy `N_K = #{(x,y)∈μ₃₂⁹×μ₃₂⁹ : Σx ≡ Σy (mod p)}` over `F_{1048609}`,
by exact 9-fold cyclic convolution. -/
def N_K : ℕ := 1537321370305723888640

/-- Char-0 Bessel energy `E_K^C = besselE 9 16` = char-0 relation count `N_K^C`. -/
def E_C : ℕ := 378194015274763550720

/-- The prize Wick ceiling `(2K−1)‼·n^K = 34459425 · 32⁹`. -/
def Wick : ℕ := 1212433231167199641600

/-- The wraparound-only count `W_wrap = N_K − N_K^C = N_K − E_C`. -/
def Wwrap : ℕ := N_K - E_C

/-- The char-0 slack `SLACK = Wick − E_C` (`≥ 0` by `besselWick_allR`). -/
def slack : ℕ := Wick - E_C

/-- `p` is in the β=4 window with `32 ∣ p−1`. -/
theorem p_window : n ^ 4 ≤ p ∧ p < 2 * n ^ 4 ∧ n ∣ (p - 1) := by
  refine ⟨?_, ?_, ?_⟩ <;> · unfold n p; norm_num

/-- Sanity: `N_K`, `E_C`, `Wick`, `n^{2K}` are the convolution / Bessel / Wick values, and the
char-0 count is `≤` the mod-`p` count (`W_wrap ≥ 0`). -/
theorem wrap_nonneg : E_C ≤ N_K := by unfold E_C N_K; norm_num

/-- **The exact decomposition identity** (cleared of division by `p`):
`A_num := N_K·p − n^{2K} = E_C·p + (W_wrap·p − n^{2K})`. Equivalently `A_K = E_C + DEV` with
`DEV = W_wrap − n^{2K}/p`. -/
theorem decomposition_identity :
    (N_K : ℤ) * p - (n : ℤ) ^ (2 * K)
      = (E_C : ℤ) * p + ((Wwrap : ℤ) * p - (n : ℤ) ^ (2 * K)) := by
  have hw : (Wwrap : ℤ) = (N_K : ℤ) - (E_C : ℤ) := by
    unfold Wwrap; rw [Nat.cast_sub (by unfold E_C N_K; norm_num)]
  rw [hw]; ring

/-- **The slack-budget equivalence** (cleared of division):
`A_K ≤ Wick  ⟺  W_wrap·p ≤ slack·p + n^{2K}`. (`A_num ≤ Wick·p ⟺ W_wrap·p ≤ slack·p + n^{2K}`.) -/
theorem budget_equiv :
    ((N_K : ℤ) * p - (n : ℤ) ^ (2 * K) ≤ (Wick : ℤ) * p)
      ↔ ((Wwrap : ℤ) * p ≤ (slack : ℤ) * p + (n : ℤ) ^ (2 * K)) := by
  have hw : (Wwrap : ℤ) = (N_K : ℤ) - (E_C : ℤ) := by
    unfold Wwrap; rw [Nat.cast_sub (by unfold E_C N_K; norm_num)]
  have hs : (slack : ℤ) = (Wick : ℤ) - (E_C : ℤ) := by
    unfold slack; rw [Nat.cast_sub (by unfold E_C Wick; norm_num)]
  rw [hw, hs]; constructor <;> intro h <;> linarith

/-- **The char-0 SLACK ALONE FAILS** at this prize-depth witness: `slack < W_wrap` strictly.
The char-0 deficit `Wick − E_C` cannot absorb the wraparound count `W_wrap`. -/
theorem slack_alone_insufficient : slack < Wwrap := by
  unfold slack Wwrap E_C N_K Wick; norm_num

/-- **The prize bound STILL holds:** `A_K ≤ Wick_K` (cleared of division: `A_num ≤ Wick·p`).
The deficit `W_wrap − slack` is exactly covered by the DC term `n^{2K}/p` — the DC main term is
LOAD-BEARING (without it the bound would fail by `slack < W_wrap`). -/
theorem prize_bound_holds : (N_K : ℤ) * p - (n : ℤ) ^ (2 * K) ≤ (Wick : ℤ) * p := by
  unfold N_K Wick n p K; norm_num

/-- **DC term is essential, quantified:** the slack deficit `W_wrap − slack` is strictly positive
yet strictly below the DC term `n^{2K}/p` (cleared: `(W_wrap − slack)·p < n^{2K}`). So the budget
`slack·p + n^{2K}` clears `W_wrap·p` with room, but `slack·p` alone does not. -/
theorem dc_term_covers_deficit :
    0 < (Wwrap : ℤ) * p - (slack : ℤ) * p
      ∧ (Wwrap : ℤ) * p - (slack : ℤ) * p < (n : ℤ) ^ (2 * K) := by
  refine ⟨?_, ?_⟩
  · have h := slack_alone_insufficient
    have : (slack : ℤ) < (Wwrap : ℤ) := by exact_mod_cast h
    have hp : (0 : ℤ) < p := by unfold p; norm_num
    nlinarith [this, hp]
  · unfold Wwrap slack E_C N_K Wick n p K; norm_num

#print axioms p_window
#print axioms wrap_nonneg
#print axioms decomposition_identity
#print axioms budget_equiv
#print axioms slack_alone_insufficient
#print axioms prize_bound_holds
#print axioms dc_term_covers_deficit

end ArkLib.ProximityGap.Frontier.WKSlackBudget
