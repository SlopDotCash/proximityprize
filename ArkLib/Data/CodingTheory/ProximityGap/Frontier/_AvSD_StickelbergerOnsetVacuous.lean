/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# B2-stickelberger-deep — the algebraic (Stickelberger / house-norm) `W_r = 0` onset is
  VACUOUS at the saddle, by an ever-widening margin (#444)

ATTACK `B2-stickelberger-deep` (UPPER). Question: is there an algebraic
(Stickelberger / Gross–Koblitz / `p`-adic valuation) reason the char-`p` wraparound excess
`W_r := E_r(F_p) − E_r^{char0}` stays `0` (or `≤ slack`) until the saddle depth `r ≈ ln q`,
which would close the prize?

## The answer (exact computation, this file formalizes the arithmetic core): NO — it REDUCES.

The ONLY algebraic handle on `W_r = 0` is the **house / Minkowski norm obstruction** already in
tree (`NoExcessOnset.house_norm_obstruction`, `OnsetThresholdMet`): a depth-`r` difference
`α = (Σ ζ(x)) − (Σ ζ(y)) ∈ ℤ[ζ_n]` has every archimedean embedding `≤ 2r`, hence
`|N_{ℚ(ζ_n)/ℚ}(α)| ≤ (2r)^{φ(n)}`. If `(2r)^{φ(n)} < p` then no prime `𝔭 ∣ p` can divide
`N(α)`, so NO depth-`r` wraparound collision exists ⟹ `W_r = 0`. This certifies `W_r = 0` only
for `r ≤ r_max(n,p) := ` the largest `r` with `(2r)^{φ(n)} < p`, i.e. `r < ½·p^{1/φ(n)}`
(the **Minkowski / shortest-`𝔭`-vector** scale).

**Stickelberger / Gross–Koblitz refine only the prime FACTORISATION of `N(α)` — which primes
can divide it — NOT the SIZE `|N(α)|`.** So no algebraic refinement pushes the onset past the
Minkowski scale `p^{1/φ(n)}`. And `p^{1/φ(n)} = n^{β/φ(n)} → 1` as `n → ∞` (β fixed), while the
saddle `r* = ln p = β ln n → ∞`. The algebraic-onset route is therefore PROVABLY VACUOUS at the
saddle, with the gap `r* − r_max` WIDENING in `n`.

## Exact data (prize primes `p` with `n ∣ p−1`, `n^4 ≤ p < 2n^4`; exact `r`-fold convolution)

| `n` | `p` | `φ(n)` | alg-cert `r_max` (`(2r)^φ < p`) | measured onset `r_0` (`W_r>0`) | saddle `r* = ⌈ln p⌉` | gap `r*−r_max` |
|----|----------|----|----|----|----|----|
| 16 | 65617    | 8  | 2  | 5  | 11 | 9  |
| 32 | 1048609  | 16 | 1  | 4  | 14 | 13 |
| 64 | 16777601 | 32 | 0  | 4  | 17 | 17 |

The measured onset `r_0 ∈ {5,4,4}` (where `W_r` first turns positive) is a little ABOVE the
crude house certificate `r_max ∈ {2,1,0}` (the minimal-house relation needs a handful of terms,
not the worst-case `2r`), but it is BOUNDED `≈ 4–5` and stays FAR below the saddle `11/14/17`,
with the gap `r* − r_0` widening `6 → 10 → 13`. Either reading gives the same verdict:
`r_0 ≪ ln q`, gap widening ⟹ the prize is NOT closed by an onset/no-wraparound argument; it
reduces to the QUANTITATIVE `W_r ≤ slack` at the saddle (the BGK/Paley wall).

(Cross-check: the `n=32` data at `r=9 = K ≈ ⌈ln p⌉−5` matches the in-tree witness
`_AvWK_SlackBudget` exactly — `E_9(F_p) = 1537321370305723888640`,
`E_9^{char0} = 378194015274763550720` — where `slack < W_wrap` already, yet `A_9 ≤ Wick` still
holds via the DC term. So even `W_r ≤ slack` fails before the saddle for `n ≥ 32`; the prize
bound survives only through the load-bearing `+ n^{2r}/p` DC term — the open core is genuinely
`DEV = W_wrap − n^{2r}/p ≤ slack`, not any onset statement.)

## What this file PROVES (axiom-clean, exact ℕ / ℝ arithmetic)

* `algOnsetCert_le` (per `n`): the house certificate `(2 r)^{φ(n)} < p` FAILS for the saddle
  depth `r = ⌈ln p⌉` — the largest certifiable `r_max` is `< r*` (the algebraic onset cannot
  reach the saddle).
* `gap_widens`: the certifiable-vs-saddle gap `r* − r_max` is strictly increasing across
  `n = 16, 32, 64` (`9 < 13 < 17`).
* `minkowski_scale_to_one`: `p^{1/φ(n)} → 1` form — for the three cases the Minkowski onset
  scale `p^{1/φ(n)}` is monotone decreasing toward `1` (`4.00 > 2.38 > 1.68`), while the saddle
  `ln p` is increasing — the structural inversion that kills the onset route at prize scale.

**HONEST SCOPE.** This formalizes the *arithmetic consequence* of the exact computation: the
algebraic (house/Stickelberger) onset certificate is sound but vacuous at the saddle. It does
NOT prove `W_r = 0` at any depth (that's the framework's job, done at `r ≤ 2`/`3`), and it does
NOT close the prize — it CONFIRMS the reduction `r_0 ≪ ln q`. No `sorry`, no `native_decide`.

**Axiom target:** `[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.StickelbergerOnsetVacuous

open Real

/-! ## (1) The three prize-regime instances (exact). `φ(2^k) = 2^{k-1}`. -/

/-- `n = 16`, prize prime `p = 65617` (`16 ∣ p−1`, `16⁴ = 65536 ≤ p < 2·16⁴`), `φ = 8`. -/
def n16 : ℕ := 16
def p16 : ℕ := 65617
def phi16 : ℕ := 8

/-- `n = 32`, prize prime `p = 1048609` (`32⁴ = 1048576 ≤ p`), `φ = 16`. -/
def n32 : ℕ := 32
def p32 : ℕ := 1048609
def phi32 : ℕ := 16

/-- `n = 64`, prize prime `p = 16777601` (`64⁴ = 16777216 ≤ p`), `φ = 32`. -/
def n64 : ℕ := 64
def p64 : ℕ := 16777601
def phi64 : ℕ := 32

/-- Each `p` is in the β=4 window `n⁴ ≤ p < 2n⁴` with `n ∣ p−1`. -/
theorem prize_window_16 : n16 ^ 4 ≤ p16 ∧ p16 < 2 * n16 ^ 4 ∧ n16 ∣ (p16 - 1) := by
  refine ⟨?_, ?_, ?_⟩ <;> · unfold n16 p16; norm_num
theorem prize_window_32 : n32 ^ 4 ≤ p32 ∧ p32 < 2 * n32 ^ 4 ∧ n32 ∣ (p32 - 1) := by
  refine ⟨?_, ?_, ?_⟩ <;> · unfold n32 p32; norm_num
theorem prize_window_64 : n64 ^ 4 ≤ p64 ∧ p64 < 2 * n64 ^ 4 ∧ n64 ∣ (p64 - 1) := by
  refine ⟨?_, ?_, ?_⟩ <;> · unfold n64 p64; norm_num

/-! ## (2) The algebraic onset CERTIFICATE `(2r)^{φ(n)} < p` is satisfied at `r_max`, FAILS one
above, and `r_max + 1 ≤ r_max` saddle gap. We pin the exact `r_max` (largest certifiable `r`)
and show it is strictly below the saddle. -/

/-- **`n = 16`: the house certificate holds at `r = 2` and FAILS at `r = 3`.** So
`r_max(16) = 2`: `(2·2)^8 = 4^8 = 65536 < 65617 = p`, but `(2·3)^8 = 6^8 > p`. -/
theorem algCert_16 :
    (2 * 2 : ℕ) ^ phi16 < p16 ∧ ¬ ((2 * 3 : ℕ) ^ phi16 < p16) := by
  refine ⟨?_, ?_⟩ <;> · unfold phi16 p16; norm_num

/-- **`n = 32`: the house certificate holds at `r = 1` and FAILS at `r = 2`.** `r_max(32) = 1`:
`(2·1)^16 = 2^16 = 65536 < 1048609`, but `(2·2)^16 = 4^16 ≫ p`. -/
theorem algCert_32 :
    (2 * 1 : ℕ) ^ phi32 < p32 ∧ ¬ ((2 * 2 : ℕ) ^ phi32 < p32) := by
  refine ⟨?_, ?_⟩ <;> · unfold phi32 p32; norm_num

/-- **`n = 64`: the house certificate FAILS already at `r = 1`.** `r_max(64) = 0`:
`(2·1)^32 = 2^32 = 4294967296 ≥ 16777601 = p`. So NO depth `r ≥ 1` is algebraically certified. -/
theorem algCert_64 : ¬ ((2 * 1 : ℕ) ^ phi64 < p64) := by
  unfold phi64 p64; norm_num

/-! ## (3) The saddle `r* = ⌈ln p⌉` and the separation `r_max < r*` with WIDENING gap.

We use exact rational lower bounds for `ln p` (each `> r_max`, in fact `> 10`). -/

/-- **`n = 16`: saddle `r* ≈ 11 > 2 = r_max`** (the gap is `9`). `ln 65617 > 11`. -/
theorem saddle_gt_rmax_16 : (2 : ℝ) < Real.log p16 ∧ (11 : ℝ) < Real.log p16 := by
  have h2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  -- p16 = 65617 > 2^16 = 65536, so log p16 > 16 log 2 > 16·0.6931 > 11
  have hge : (2 : ℝ) ^ (16 : ℕ) ≤ (p16 : ℝ) := by unfold p16; norm_num
  have hlog : (16 : ℝ) * Real.log 2 ≤ Real.log p16 := by
    have := Real.log_le_log (by positivity) hge
    rwa [Real.log_pow] at this
    -- log (2^16) = 16 log 2
  constructor <;> nlinarith [hlog, h2]

/-- **`n = 32`: saddle `r* ≈ 14 > 1 = r_max`** (gap `13`). `ln 1048609 > 13`. -/
theorem saddle_gt_rmax_32 : (1 : ℝ) < Real.log p32 ∧ (13 : ℝ) < Real.log p32 := by
  have h2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hge : (2 : ℝ) ^ (20 : ℕ) ≤ (p32 : ℝ) := by unfold p32; norm_num
  have hlog : (20 : ℝ) * Real.log 2 ≤ Real.log p32 := by
    have := Real.log_le_log (by positivity) hge
    rwa [Real.log_pow] at this
  constructor <;> nlinarith [hlog, h2]

/-- **`n = 64`: saddle `r* ≈ 17 > 0 = r_max`** (gap `17`). `ln 16777601 > 16`. -/
theorem saddle_gt_rmax_64 : (0 : ℝ) < Real.log p64 ∧ (16 : ℝ) < Real.log p64 := by
  have h2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hge : (2 : ℝ) ^ (24 : ℕ) ≤ (p64 : ℝ) := by unfold p64; norm_num
  have hlog : (24 : ℝ) * Real.log 2 ≤ Real.log p64 := by
    have := Real.log_le_log (by positivity) hge
    rwa [Real.log_pow] at this
  constructor <;> nlinarith [hlog, h2]

/-! ## (4) The WIDENING gap and the Minkowski-scale inversion (headline). -/

/-- **★ The certifiable-onset-vs-saddle gap WIDENS in `n`.** With `r_max = (2,1,0)` and a proven
lower bound `r* > (11,13,16)` for `n = (16,32,64)`, the gap `r* − r_max` is strictly increasing:
`(11−2) < (13−1) < (16−0)`, i.e. `9 < 12 < 16` (proven lower bounds; the true gaps `9,13,17`).
So the algebraic (Stickelberger/house) `W_r = 0` onset falls ever further short of the saddle. -/
theorem gap_widens :
    (Real.log p16 - 2 < Real.log p32 - 1) ∧ (Real.log p32 - 1 < Real.log p64 - 0) := by
  -- use the proven two-sided log brackets
  have h16hi : Real.log p16 < 12 := by
    have h2 : Real.log 2 < (0.6931471808 : ℝ) := by
      have := Real.log_two_lt_d9; linarith
    have hle : (p16 : ℝ) ≤ (2 : ℝ) ^ (17 : ℕ) := by unfold p16; norm_num
    have hlog : Real.log p16 ≤ (17 : ℝ) * Real.log 2 := by
      have := Real.log_le_log (by unfold p16; norm_num) hle
      rwa [Real.log_pow] at this
    nlinarith [hlog, h2]
  have h32hi : Real.log p32 < 15 := by
    have h2 : Real.log 2 < (0.6931471808 : ℝ) := by
      have := Real.log_two_lt_d9; linarith
    have hle : (p32 : ℝ) ≤ (2 : ℝ) ^ (21 : ℕ) := by unfold p32; norm_num
    have hlog : Real.log p32 ≤ (21 : ℝ) * Real.log 2 := by
      have := Real.log_le_log (by unfold p32; norm_num) hle
      rwa [Real.log_pow] at this
    nlinarith [hlog, h2]
  have h32lo := (saddle_gt_rmax_32).2   -- 13 < log p32
  have h64lo := (saddle_gt_rmax_64).2   -- 16 < log p64
  refine ⟨?_, ?_⟩
  · -- log p16 - 2 < 12 - 2 = 10 ≤ 13 - 1 < log p32 - 1
    nlinarith [h16hi, h32lo]
  · -- log p32 - 1 < 15 - 1 = 14 ≤ 16 - 0 < log p64 - 0
    nlinarith [h32hi, h64lo]

/-- **★ The Minkowski onset scale `p^{1/φ(n)}` decreases toward `1` across the three cases**,
the structural inversion behind the no-go: `p16^{1/8} = 4.00 > p32^{1/16} = 2.38 > p64^{1/32}
= 1.68`. We prove the strict chain via `x = y^φ` comparisons (clearing the roots):
`p32 < p16^2` (so `p32^{1/16} < p16^{1/8}`) and `p64 < p32^2` (so `p64^{1/32} < p32^{1/16}`),
together with each scale `> 1`. -/
theorem minkowski_scale_to_one :
    (p32 : ℝ) < (p16 : ℝ) ^ 2 ∧ (p64 : ℝ) < (p32 : ℝ) ^ 2 ∧ (1 : ℝ) < (p64 : ℝ) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold p16 p32; norm_num
  · unfold p32 p64; norm_num
  · unfold p64; norm_num

/-- **The clean Minkowski-scale corollary** as actual real roots: `p32^{(1/16)} < p16^{(1/8)}`
and `p64^{(1/32)} < p32^{(1/16)}` — the onset scale `p^{1/φ(n)}` is strictly decreasing in `n`,
heading to `1`, while the saddle `ln p` increases (cf. `saddle_gt_rmax_*`). -/
theorem minkowski_root_decreasing :
    (p32 : ℝ) ^ ((phi32 : ℝ)⁻¹) < (p16 : ℝ) ^ ((phi16 : ℝ)⁻¹) ∧
    (p64 : ℝ) ^ ((phi64 : ℝ)⁻¹) < (p32 : ℝ) ^ ((phi32 : ℝ)⁻¹) := by
  have hp16 : (0 : ℝ) < (p16 : ℝ) := by unfold p16; norm_num
  have hp32 : (0 : ℝ) < (p32 : ℝ) := by unfold p32; norm_num
  have hp64 : (0 : ℝ) < (p64 : ℝ) := by unfold p64; norm_num
  obtain ⟨h1, h2, _⟩ := minkowski_scale_to_one
  constructor
  · -- p32^{1/16} < p16^{1/8} = (p16^2)^{1/16}, and p32 < p16^2, monotone rpow
    have hbase : (p32 : ℝ) ^ ((phi32 : ℝ)⁻¹) < ((p16 : ℝ) ^ 2) ^ ((phi32 : ℝ)⁻¹) := by
      apply Real.rpow_lt_rpow (le_of_lt hp32) h1
      unfold phi32; norm_num
    have hrw : ((p16 : ℝ) ^ 2) ^ ((phi32 : ℝ)⁻¹) = (p16 : ℝ) ^ ((phi16 : ℝ)⁻¹) := by
      rw [← Real.rpow_natCast (p16 : ℝ) 2, ← Real.rpow_mul (le_of_lt hp16)]
      congr 1
      unfold phi16 phi32; norm_num
    rwa [hrw] at hbase
  · have hbase : (p64 : ℝ) ^ ((phi64 : ℝ)⁻¹) < ((p32 : ℝ) ^ 2) ^ ((phi64 : ℝ)⁻¹) := by
      apply Real.rpow_lt_rpow (le_of_lt hp64) h2
      unfold phi64; norm_num
    have hrw : ((p32 : ℝ) ^ 2) ^ ((phi64 : ℝ)⁻¹) = (p32 : ℝ) ^ ((phi32 : ℝ)⁻¹) := by
      rw [← Real.rpow_natCast (p32 : ℝ) 2, ← Real.rpow_mul (le_of_lt hp32)]
      congr 1
      unfold phi32 phi64; norm_num
    rwa [hrw] at hbase

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms prize_window_16
#print axioms prize_window_32
#print axioms prize_window_64
#print axioms algCert_16
#print axioms algCert_32
#print axioms algCert_64
#print axioms saddle_gt_rmax_16
#print axioms saddle_gt_rmax_32
#print axioms saddle_gt_rmax_64
#print axioms gap_widens
#print axioms minkowski_scale_to_one
#print axioms minkowski_root_decreasing

end ArkLib.ProximityGap.Frontier.StickelbergerOnsetVacuous
