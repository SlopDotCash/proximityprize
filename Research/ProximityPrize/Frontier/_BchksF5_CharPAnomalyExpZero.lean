/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# Bchks F5 — the char-`p` energy anomaly is EXPONENT-0 (#444)

One of the three named residuals of the explicit `δ*` lower bound (`_BchksF6`). The char-`p`
additive-energy anomaly
  `W_r := E_r(F_p) − E_r^{char0}(μ_n)`
is the extra mod-`p` coincidences ("wraparound") beyond the genuine `ℂ`-coincidences. ABF26 §4:
the leading-order `δ*` is char-FREE-pinned; the anomaly is **exponent-0** — it changes only the
sub-leading term, never the leading `(2r−1)‼·n^r` energy coefficient.

**The proof (this file).** GIVEN the below-Wick property `E_r(F_p) ≤ Wick_r := (2r−1)‼·n^r` (the
char-`p` Wick bound — itself the open deep-`r` input, the W1/DC-Wick wall), the anomaly is squeezed:
  `0 ≤ W_r = E_r(F_p) − E_r^{char0} ≤ Wick_r − E_r^{char0}`.
Because the char-0 closed form has the SAME leading coefficient as Wick (`E_r^{char0} =
(2r−1)‼·n^r − C(r,2)(2r−1)‼·n^{r−1} + …`), the gap `Wick_r − E_r^{char0}` is `O(n^{r−1})` — one power
below the leading. So `W_r` does NOT move the leading-order energy, hence not the leading `δ*`.

We prove this EXACTLY for `r = 4,5,6,7` using the in-tree exact closed forms (the leading `n^r`
coefficient cancels, leaving a degree-`(r−1)` bound), and state the exponent-0 conclusion. All
char-free; no `sorry`. The genuine open input is the below-Wick hypothesis `hWick`, named explicitly.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.BchksF5

/-- Char-0 additive-energy closed forms (μ_n), the in-tree ladder E_2..E_7 (here r=4..7). -/
def E0 : ℕ → ℕ → ℤ
  | 4, n => 105*(n:ℤ)^4 - 630*n^3 + 1435*n^2 - 1155*n
  | 5, n => 945*(n:ℤ)^5 - 9450*n^4 + 39375*n^3 - 77175*n^2 + 57456*n
  | 6, n => 10395*(n:ℤ)^6 - 155925*n^5 + 1022175*n^4 - 3534300*n^3 + 6246471*n^2 - 4370520*n
  | 7, n => 135135*(n:ℤ)^7 - 2837835*n^6 + 26801775*n^5 - 141891750*n^4 + 433726293*n^3
              - 708996288*n^2 + 471556800*n
  | _, _ => 0

/-- The Wick value `(2r−1)‼·n^r`. -/
def Wick : ℕ → ℕ → ℤ
  | 4, n => 105*(n:ℤ)^4
  | 5, n => 945*(n:ℤ)^5
  | 6, n => 10395*(n:ℤ)^6
  | 7, n => 135135*(n:ℤ)^7
  | _, _ => 0

/-- **The Wick−char0 gap has the leading coefficient cancelled** — it is a degree-`(r−1)` polynomial
(r=4). The `n^4` term vanishes (`105 − 105 = 0`); the gap is `630n^3 − 1435n^2 + 1155n`, degree 3. -/
theorem gap_four (n : ℕ) : Wick 4 n - E0 4 n = 630*(n:ℤ)^3 - 1435*n^2 + 1155*n := by
  simp only [Wick, E0]; ring

theorem gap_five (n : ℕ) :
    Wick 5 n - E0 5 n = 9450*(n:ℤ)^4 - 39375*n^3 + 77175*n^2 - 57456*n := by
  simp only [Wick, E0]; ring

theorem gap_six (n : ℕ) :
    Wick 6 n - E0 6 n = 155925*(n:ℤ)^5 - 1022175*n^4 + 3534300*n^3 - 6246471*n^2 + 4370520*n := by
  simp only [Wick, E0]; ring

theorem gap_seven (n : ℕ) :
    Wick 7 n - E0 7 n = 2837835*(n:ℤ)^6 - 26801775*n^5 + 141891750*n^4 - 433726293*n^3
      + 708996288*n^2 - 471556800*n := by
  simp only [Wick, E0]; ring

/-- **The anomaly is bounded by the (degree-`r−1`) gap, GIVEN the below-Wick property.**
`W_r = E_r(F_p) − E_r^{char0} ≤ Wick_r − E_r^{char0}` whenever `E_r(F_p) ≤ Wick_r`. Stated for any
`r`; the gap's leading coefficient is 0 (the four `gap_*` lemmas), so the bound is `O(n^{r−1})`. -/
theorem anomaly_le_gap (r n : ℕ) (Efp : ℤ) (hWick : Efp ≤ Wick r n) :
    Efp - E0 r n ≤ Wick r n - E0 r n := by linarith

/-- **Exponent-0, r=4 concrete (clean gap form, no n≥1 needed):** GIVEN below-Wick, the anomaly
`W_4 ≤ 630n³ − 1435n² + 1155n`, a polynomial of degree `3 = r−1` whose leading (`n⁴`) coefficient is
0 (`gap_four`). So the anomaly NEVER reaches the leading energy order `n⁴`; the leading coefficient
`105 = (2·4−1)‼` is char-FREE / unchanged. This is the exponent-0 statement. -/
theorem anomaly_exp_zero_four (n : ℕ) (Efp : ℤ) (hWick : Efp ≤ Wick 4 n) :
    Efp - E0 4 n ≤ 630*(n:ℤ)^3 - 1435*(n:ℤ)^2 + 1155*(n:ℤ) := by
  have h := anomaly_le_gap 4 n Efp hWick; rwa [gap_four] at h

/-- **The exponent-0 statement as a `Prop`.** The anomaly is bounded by a polynomial of degree
`r−1` (one below the leading `n^r`) — i.e. the gap `Wick_r − E_r^{char0}`, whose leading coefficient
is 0 (the `gap_*` lemmas). So it is strictly sub-leading: it cannot move the leading-order energy,
hence not the leading `δ*`. Holds GIVEN the below-Wick char-`p` input (the open deep-`r` wall). -/
def AnomalyExponentZeroAt (r : ℕ) : Prop :=
  ∀ (n : ℕ) (Efp : ℤ), Efp ≤ Wick r n → Efp - E0 r n ≤ Wick r n - E0 r n

/-- r=5 instance (the gap `Wick_5 − E_5^{char0}` is degree 4 = r−1, `gap_five`). -/
theorem anomalyExponentZero_five : AnomalyExponentZeroAt 5 := fun n Efp hWick =>
  anomaly_le_gap 5 n Efp hWick

/-- r=6,7 instances. -/
theorem anomalyExponentZero_six : AnomalyExponentZeroAt 6 := fun n Efp hWick =>
  anomaly_le_gap 6 n Efp hWick
theorem anomalyExponentZero_seven : AnomalyExponentZeroAt 7 := fun n Efp hWick =>
  anomaly_le_gap 7 n Efp hWick

end ArkLib.ProximityGap.BchksF5

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.BchksF5.gap_four
#print axioms ArkLib.ProximityGap.BchksF5.anomaly_le_gap
#print axioms ArkLib.ProximityGap.BchksF5.anomaly_exp_zero_four
#print axioms ArkLib.ProximityGap.BchksF5.anomalyExponentZero_five
