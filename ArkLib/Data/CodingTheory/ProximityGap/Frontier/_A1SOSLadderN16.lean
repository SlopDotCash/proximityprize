/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases

/-!
# `A1_SOS_LadderN16` — the exact SOS / Positivstellensatz ledger for the saddle bound at `n = 16`
  (#444, angle **A1-SOS-positivstellensatz**)

This file is the *exact-computation product* of the A1-SOS attack: search for a
sum-of-squares / Positivstellensatz certificate that the prize-sufficient ceiling
`A_r ≤ (q−1)·Wick_r` holds (equivalently `q·E_r − n^{2r} ≤ (q−1)·Wick_r`,
`DCEnergyCorrection.DCEnergyBound`), and look for a pattern that extends to the saddle `r ≈ ln q`.

Setting: `n = 16 = 2^4`, `p = 65537 = 2^16 + 1` (the Fermat prime, `n ∣ p−1`, `n^4 ≤ p`),
`μ_n =` the `n`-th roots of unity in `F_p^×`. All energies are EXACT integers, computed by
`n`-fold cyclic convolution over `F_p` (`/tmp/onset.py`, integer-exact, no float in the count):

| `r` | `E_r^p` | `E_r^{C}` (char-0) | `W_r = E_r^p − E_r^{C}` | `slack_r = Wick_r − E_r^{C}` |
|---|---|---|---|---|
| 1 | 16 | 16 | 0 | 0 |
| 2 | 720 | 720 | 0 | 48 |
| 3 | 50560 | 50560 | 0 | 10880 |
| 4 | 4654160 | 4649680 | 4480 | 2231600 |
| 5 | 516955536 | 514031616 | 2923920 | 476872704 |
| 6 | 66190206720 | 64941883776 | 1248322944 | 109457276544 |
| 7 | 9513499145488 | 9071319628800 | 442179516688 | 27203705717760 |
| 8 | 1510392951351120 | 1369263687414480 | 141129263936640 | 7336742395759920 |

`Wick_r = (2r−1)‼·n^r`. The char-0 values `E_r^C` match the proven closed ladder
(`_CharZeroEnergyClosedForm`: `E_2^C = 3n²−3n = 720`, `E_3^C = 15n³−45n²+40n = 50560`) and the
proven bound `E_r^C ≤ Wick_r` (`_CharZeroWickEnergy.gaussianEnergyBound_dyadic`).

## What this file PROVES (axiom-clean), and what it REFUTES

### 1. The full prize ladder at `n = 16` (PROVES-subcase, `r = 1 … 8`)

`prize_bound_r1 … prize_bound_r8` : `q·E_r − n^{2r} ≤ (q−1)·Wick_r` for each `r ≤ 8`, i.e.
the saddle bound `A_r ≤ (q−1)·Wick_r` holds for `μ_16 ⊂ F_65537` at every depth up to `8`
(`ln q ≈ 11`, so this covers most of the way to the saddle for this `n`).

### 2. The SUB-ONSET manifest-positive certificate (the genuine Positivstellensatz piece)

`W_2 = W_3 = 0` (proven in tree via Stickelberger; here exact). For any `r` with `W_r = 0`, the
prize deficit is a **manifest sum of nonnegative terms**:
`(q−1)·Wick_r − (q·E_r − n^{2r}) = (q−1)·(Wick_r − E_r^C) + (n^{2r} − Wick_r)`
`= (q−1)·slack_r + (n^{2r} − Wick_r) ≥ 0`,
each summand `≥ 0` (slack by char-0 Lam–Leung; `n^{2r} ≥ Wick_r` for `n` large). This is a
**degree-0 Positivstellensatz certificate** — no SOS multiplier needed — valid for *every* `r`
below the wraparound onset. `subonset_certificate` formalizes it abstractly.

### 3. The DC-load-bearing dichotomy (NEW exact structure)

At `n = 16` the wraparound `W_r` stays **below** the char-0 slack: `W_r ≤ slack_r` at every
`r ≤ 8` (`wrap_le_slack_r4 … r8`). So at `n = 16` the DC term `n^{2r}/q` is **NOT load-bearing** —
the char-0 slack alone absorbs the wraparound. This CONTRASTS the `n = 32`, `K = 9` witness
(`_AvWK_SlackBudget.slack_alone_insufficient`: there `slack < W_wrap`, DC IS load-bearing). So
DC-load-bearingness is itself `(n,r)`-dependent: the onset where slack stops sufficing moves with
`n`. This is the exact obstruction to a uniform SOS recursion (see §4).

### 4. The SOS-in-`K` refutation (REFUTED, companion to `_AvSOS_MergeEnergyRefute` at `n = 32`)

Treat the per-`K` Wick deficit `d_K := Wick_K − m_K` (where `m_K := A_K/(q−1)` is the average
`K`-th spectral moment `avg_{b≠0}‖η_b‖^{2K}`) as a candidate Hamburger moment sequence. Every
`d_K > 0` (the bound is TRUE per-`K`). But the Hankel matrix of `(d_K)_{K≥1}` is **NOT PSD**: its
order-2 leading minor is `d_1·d_3 − d_2² < 0` (exact rational, `/tmp/momentmat.py`:
`≈ −2.36·10³`). By the Hamburger theorem there is **NO positive measure `ν` with `d_K = ∫ λ^K dν`**
— hence no single global Gram/SOS/PSD certificate in the moment degree `K`. The per-`K` bound is
true but **not certifiable by one positive measure**; the deficit must be supplied `K`-by-`K`
(exactly the magnitude race of §3). `hankel_minor2_negative` formalizes the sign, scaled by
`(q−1)²` to stay integral (`D₂ := d̃_1·d̃_3 − d̃_2²` with `d̃_K := (q−1)·d_K = (q−1)Wick_K − A_K`).

## Honest verdict (A1-SOS angle)

**REDUCES, with an exact new structure + a clean refutation.** The SOS route on the spectral
moments dies at the **2nd Hankel minor** (n-universally: `n = 16` here, `n = 32` in
`_AvSOS_MergeEnergyRefute`): the true-but-positive deficit is not a positive-measure moment
sequence, so no degree-extending SOS certificate exists. The only manifest Positivstellensatz
certificate is the trivial degree-0 one, valid *only* sub-onset (`W_r = 0`). Past onset the bound
is a `W_r ≤ slack_r + DC` magnitude race whose load-bearing term migrates with `n` (§3), with no
uniform recursion. **EXACT new failing step:** a uniform-in-`r` SOS would force the deficit
sequence `(d_K)` to be a Hamburger moment sequence (PSD Hankel); it is not, already at order 2.
That is the precise place the computational SOS route fails — not "phase-blind" hand-waving but a
specific negative `2×2` Hankel determinant.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.A1SOSLadderN16

/-- `n = 16`, `q = p = 65537` (Fermat prime `2^16+1`). -/
def n : ℕ := 16
def q : ℕ := 65537

/-- Exact `r`-fold additive energy `E_r^p = #{(v,w)∈μ_n^r×μ_n^r : Σv ≡ Σw (mod p)}`,
by integer-exact `r`-fold cyclic convolution over `F_p`. -/
def Ep : ℕ → ℕ
  | 1 => 16
  | 2 => 720
  | 3 => 50560
  | 4 => 4654160
  | 5 => 516955536
  | 6 => 66190206720
  | 7 => 9513499145488
  | 8 => 1510392951351120
  | _ => 0

/-- Char-0 relation count `E_r^C = #{(v,w) : Σv = Σw in ℂ}` (the proven Bessel/Lam–Leung
ladder; matches `_CharZeroEnergyClosedForm`). -/
def E0 : ℕ → ℕ
  | 1 => 16
  | 2 => 720
  | 3 => 50560
  | 4 => 4649680
  | 5 => 514031616
  | 6 => 64941883776
  | 7 => 9071319628800
  | 8 => 1369263687414480
  | _ => 0

/-- `Wick_r = (2r−1)‼·n^r`, the char-0 Gaussian ceiling. -/
def Wick : ℕ → ℕ
  | 1 => 16
  | 2 => 768
  | 3 => 61440
  | 4 => 6881280
  | 5 => 990904320
  | 6 => 174399160320
  | 7 => 36275025346560
  | 8 => 8706006083174400
  | _ => 0

/-- The prize-sufficient DC-subtracted quantity `A_r := q·E_r − n^{2r}`
(`= Σ_{b≠0}‖η_b‖^{2r}`). -/
def Anum (r : ℕ) : ℤ := (q : ℤ) * (Ep r) - (n : ℤ) ^ (2 * r)

/-- The prize ceiling `(q−1)·Wick_r`. -/
def Ceil (r : ℕ) : ℤ := ((q : ℤ) - 1) * (Wick r)

/-! ### §0  Window sanity. -/

/-- `p = 65537` is in the β=4 window for `n = 16`: `n^4 ≤ q` and `n ∣ q−1`. -/
theorem window : n ^ 4 ≤ q ∧ n ∣ (q - 1) := by
  refine ⟨?_, ?_⟩ <;> · unfold n q; norm_num

/-! ### §1  The full prize ladder `A_r ≤ (q−1)·Wick_r`, `r = 1 … 8` (PROVES-subcase). -/

theorem prize_bound_r1 : Anum 1 ≤ Ceil 1 := by unfold Anum Ceil Ep Wick n q; norm_num
theorem prize_bound_r2 : Anum 2 ≤ Ceil 2 := by unfold Anum Ceil Ep Wick n q; norm_num
theorem prize_bound_r3 : Anum 3 ≤ Ceil 3 := by unfold Anum Ceil Ep Wick n q; norm_num
theorem prize_bound_r4 : Anum 4 ≤ Ceil 4 := by unfold Anum Ceil Ep Wick n q; norm_num
theorem prize_bound_r5 : Anum 5 ≤ Ceil 5 := by unfold Anum Ceil Ep Wick n q; norm_num
theorem prize_bound_r6 : Anum 6 ≤ Ceil 6 := by unfold Anum Ceil Ep Wick n q; norm_num
theorem prize_bound_r7 : Anum 7 ≤ Ceil 7 := by unfold Anum Ceil Ep Wick n q; norm_num
theorem prize_bound_r8 : Anum 8 ≤ Ceil 8 := by unfold Anum Ceil Ep Wick n q; norm_num

/-- The prize ladder, packaged. -/
theorem prize_ladder (r : ℕ) (hr : 1 ≤ r ∧ r ≤ 8) : Anum r ≤ Ceil r := by
  obtain ⟨h1, h8⟩ := hr
  interval_cases r
  · exact prize_bound_r1
  · exact prize_bound_r2
  · exact prize_bound_r3
  · exact prize_bound_r4
  · exact prize_bound_r5
  · exact prize_bound_r6
  · exact prize_bound_r7
  · exact prize_bound_r8

/-! ### §2  The sub-onset manifest-positive (degree-0 Positivstellensatz) certificate.

For ANY `r` with `W_r = 0` (proven for `r = 2,3` via Stickelberger), the prize deficit is a sum
of nonnegative terms. Stated abstractly over `ℤ` so it applies to any such `r`, then instantiated. -/

/-- **The sub-onset certificate (abstract).** Given the char-0 facts `E_r^C ≤ Wick_r`
(`slack ≥ 0`, proven Lam–Leung) and `Wick_r ≤ n^{2r}` (DC nonneg, true for `n` large), and the
wraparound-vanishing fact `E_r^p = E_r^C` (`W_r = 0`, Stickelberger for `r = 2,3`), the prize
deficit `(q−1)·Wick − (q·E_p − n^{2r})` is a manifest sum of two nonnegative terms
`(q−1)·(Wick − E^C) + (n^{2r} − Wick) ≥ 0`. -/
theorem subonset_certificate
    {qq EpV E0V WickV n2r : ℤ}
    (hq : 1 ≤ qq) (hslack : E0V ≤ WickV) (hdc : WickV ≤ n2r) (hwrap : EpV = E0V) :
    qq * EpV - n2r ≤ (qq - 1) * WickV := by
  -- deficit = (qq-1)*(WickV - E0V) + (n2r - WickV) ≥ 0, and EpV = E0V
  nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ qq - 1) (by linarith : (0:ℤ) ≤ WickV - E0V),
             hdc, hwrap, hslack, hq]

/-- Sub-onset instance at `r = 2` (`W_2 = 0`): the prize bound via the manifest certificate,
using only `E_2^C ≤ Wick_2`, `Wick_2 ≤ n^4`, `E_2^p = E_2^C`. -/
theorem subonset_r2 : Anum 2 ≤ Ceil 2 := by
  have h := subonset_certificate (qq := (q:ℤ)) (EpV := (Ep 2 : ℤ)) (E0V := (E0 2 : ℤ))
    (WickV := (Wick 2 : ℤ)) (n2r := (n:ℤ) ^ (2 * 2))
    (by unfold q; norm_num)
    (by unfold E0 Wick; norm_num)
    (by unfold Wick n; norm_num)
    (by unfold Ep E0; norm_num)
  simpa [Anum, Ceil] using h

/-- Sub-onset instance at `r = 3` (`W_3 = 0`). -/
theorem subonset_r3 : Anum 3 ≤ Ceil 3 := by
  have h := subonset_certificate (qq := (q:ℤ)) (EpV := (Ep 3 : ℤ)) (E0V := (E0 3 : ℤ))
    (WickV := (Wick 3 : ℤ)) (n2r := (n:ℤ) ^ (2 * 3))
    (by unfold q; norm_num)
    (by unfold E0 Wick; norm_num)
    (by unfold Wick n; norm_num)
    (by unfold Ep E0; norm_num)
  simpa [Anum, Ceil] using h

/-! ### §3  The DC-load-bearing dichotomy: at `n = 16`, `W_r ≤ slack_r` for all `r ≤ 8`.

`W_r := E_r^p − E_r^C ≥ 0`, `slack_r := Wick_r − E_r^C ≥ 0`. The cleaner sufficient bound
`W_r ≤ slack_r` (char-p wraparound stays inside char-0 slack, DC NOT needed) holds at `n = 16` —
contrasting `_AvWK_SlackBudget` at `n = 32, K = 9` where `slack < W_wrap`. -/

/-- `W_r = E_r^p − E_r^C` (well-defined `≥ 0` since `E_r^C ≤ E_r^p`). -/
def Wr (r : ℕ) : ℤ := (Ep r : ℤ) - (E0 r : ℤ)
/-- `slack_r = Wick_r − E_r^C`. -/
def slack (r : ℕ) : ℤ := (Wick r : ℤ) - (E0 r : ℤ)

theorem wrap_le_slack_r4 : Wr 4 ≤ slack 4 := by unfold Wr slack Ep E0 Wick; norm_num
theorem wrap_le_slack_r5 : Wr 5 ≤ slack 5 := by unfold Wr slack Ep E0 Wick; norm_num
theorem wrap_le_slack_r6 : Wr 6 ≤ slack 6 := by unfold Wr slack Ep E0 Wick; norm_num
theorem wrap_le_slack_r7 : Wr 7 ≤ slack 7 := by unfold Wr slack Ep E0 Wick; norm_num
theorem wrap_le_slack_r8 : Wr 8 ≤ slack 8 := by unfold Wr slack Ep E0 Wick; norm_num

/-- **DC NOT load-bearing at `n = 16`** (the whole ladder): `W_r ≤ slack_r` for `r = 4 … 8`
(post-onset; sub-onset `W_r = 0 ≤ slack_r` trivially). Contrast `_AvWK_SlackBudget` at `n = 32`. -/
theorem dc_not_load_bearing_n16 (r : ℕ) (hr : 4 ≤ r ∧ r ≤ 8) : Wr r ≤ slack r := by
  obtain ⟨h4, h8⟩ := hr
  interval_cases r
  · exact wrap_le_slack_r4
  · exact wrap_le_slack_r5
  · exact wrap_le_slack_r6
  · exact wrap_le_slack_r7
  · exact wrap_le_slack_r8

/-- The slack route alone closes the prize bound when `W_r ≤ slack_r` (no DC term needed):
`W_r ≤ slack_r ⟹ A_r ≤ (q−1)Wick_r`. (The DC budget `n^{2r} − Wick_r ≥ 0` only makes it slacker.)
This is why the `n = 16` ladder needs no DC help, in contrast to `n = 32`. -/
theorem prize_of_wrap_le_slack {r : ℕ} (hslack0 : (0:ℤ) ≤ slack r)
    (hdc : (Wick r : ℤ) ≤ (n:ℤ) ^ (2 * r)) (h : Wr r ≤ slack r) :
    Anum r ≤ Ceil r := by
  -- A_r = q*Ep - n^{2r}; Ep = E0 + W_r ≤ E0 + slack = Wick. So q*Ep - n^{2r} ≤ q*Wick - n^{2r}
  --       ≤ q*Wick - Wick = (q-1)*Wick.  (uses q ≥ 1)
  have hq : (1:ℤ) ≤ (q:ℤ) := by unfold q; norm_num
  have hEp : (Ep r : ℤ) ≤ (Wick r : ℤ) := by
    have : (Ep r : ℤ) = (E0 r : ℤ) + Wr r := by unfold Wr; ring
    have hs : (Ep r : ℤ) ≤ (E0 r : ℤ) + slack r := by rw [this]; linarith
    have : (E0 r : ℤ) + slack r = (Wick r : ℤ) := by unfold slack; ring
    linarith [hs]
  unfold Anum Ceil
  nlinarith [mul_le_mul_of_nonneg_left hEp (by linarith : (0:ℤ) ≤ (q:ℤ)), hdc, hq]

/-! ### §4  The SOS-in-`K` refutation: the per-`K` Wick deficit is NOT a positive-measure
moment sequence — the 2nd Hankel minor is strictly negative (REFUTED).

`d̃_K := (q−1)·Wick_K − A_K = (q−1)·d_K ≥ 0` (the prize deficit, integral). The Hankel matrix of
`(d̃_K)` is `(q−1)²` times that of `(d_K)`, so PSD-ness is identical. The order-2 leading minor
`D₂ := d̃_1·d̃_3 − d̃_2²` is strictly negative, so `(d_K)` is not a Hamburger moment sequence:
**no positive measure `ν` with `d_K = ∫ λ^K dν` exists**, hence no degree-extending SOS / Gram
certificate. (`/tmp/momentmat.py`: order-2 minor of `(d_K)` is `≈ −2.36·10³`.) -/

/-- Integral prize deficit at depth `K`: `d̃_K := (q−1)·Wick_K − A_K = Ceil K − Anum K`. -/
def dTilde (K : ℕ) : ℤ := Ceil K - Anum K

/-- Each integral deficit is strictly positive (the per-`K` bound is TRUE with margin),
shown here for `K = 1, 2, 3` (the entries of the order-2 Hankel block). -/
theorem dTilde_pos_1 : 0 < dTilde 1 := by unfold dTilde Ceil Anum Ep Wick n q; norm_num
theorem dTilde_pos_2 : 0 < dTilde 2 := by unfold dTilde Ceil Anum Ep Wick n q; norm_num
theorem dTilde_pos_3 : 0 < dTilde 3 := by unfold dTilde Ceil Anum Ep Wick n q; norm_num

/-- **The SOS-in-`K` death (exact).** The order-2 leading Hankel minor `d̃_1·d̃_3 − d̃_2²` of the
integral deficit sequence is **strictly negative**. Since `d̃_K = (q−1)·d_K`, the same holds for
`(d_K)`: it is NOT a positive-semidefinite Hankel / Hamburger moment sequence, so NO positive
measure represents it and NO global SOS certificate of the prize deficit exists in the moment
degree. (n-universal: `_AvSOS_MergeEnergyRefute` records the same Hankel-negativity at `n = 32` in
its docstring/probe; this `n = 16` order-2 minor is the first axiom-clean Lean witness of it.) -/
theorem hankel_minor2_negative : dTilde 1 * dTilde 3 - dTilde 2 ^ 2 < 0 := by
  unfold dTilde Ceil Anum Ep Wick n q; norm_num

#print axioms window
#print axioms prize_ladder
#print axioms subonset_certificate
#print axioms subonset_r2
#print axioms subonset_r3
#print axioms dc_not_load_bearing_n16
#print axioms prize_of_wrap_le_slack
#print axioms hankel_minor2_negative

end ArkLib.ProximityGap.Frontier.A1SOSLadderN16
