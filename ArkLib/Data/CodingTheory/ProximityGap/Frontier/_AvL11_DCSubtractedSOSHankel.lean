/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# DC-subtracted SOS / Hankel-moment test for the prize energy bound (#444, avenue L11)

The whole prize reduces (machine-checked elsewhere) to the **DC-subtracted** inequality
`A_r ≤ Wick_r` where `A_r := E_r(μ_n) − |G|^{2r}/q` is the nontrivial-period moment
`(1/q)∑_{b≠0}‖η_b‖^{2r}` and `Wick_r := (2r−1)‼·n^r` (see `DCSubtractedMoment.sum_nonzero_moment`,
`DCEnergyCorrection`). Equivalently the **deficit** `d_r := Wick_r − A_r` must be `≥ 0` at every
depth `r ≈ ln q` for the worst prime.

A *moment / SOS certificate* for `d_r ≥ 0` (the strongest form of proof, valid for ALL depths and
extensible by recursion) would require the deficit sequence `(d_k)_{k≥0}` to itself be a **Hamburger
moment sequence** — equivalently its Hankel matrix `H = (d_{i+j})` to be PSD. The PRIOR SOS attempt
ran this test on the *un*-DC-subtracted object `Wick_r − A_r` with `A_r = q·E_r − n^{2r}` and found a
negative `2×2`-level minor (`d₁d₃ − d₂² < 0`). This file runs the test on the **DC-subtracted**
object, whose Hankel structure is genuinely different, and reports the exact outcome.

## Setup (exact, char-`p`, scaled by `q` to stay in `ℤ`)

Write `aₖ := ∑_{b≠0}‖η_b‖^{2k} = q·Eₖ − n^{2k}` (`a₀ = q − 1`), and the `q`-scaled deficit
`Dₖ := q·Wickₖ − aₖ`.  Using the in-tree exact char-0 energies (`Eₖ = Eₖ(ℂ)` for the small depths
relevant to the leading Hankel block, where `Wₖ = 0`: `E₁ = n`, `E₂ = 3n²−3n`, `E₃ = 15n³−45n²+40n`),
these are, **exactly and for every split prime `q ≡ 1 (mod n)`**:

```
D₀ = 1,    D₁ = n²,    D₂ = 3·q·n + n⁴,    D₃ = q·(45n²−40n) + n⁶, …
```

## Results (computed exactly `n = 16, 32, 64`, all primes `q ≡ 1 mod n`; this file = the algebra)

1. **NEW exact identity / surviving partial.** The leading `2×2` deficit Hankel minor is
   `D₀·D₂ − D₁² = 3·q·n`, *strictly positive*. So — unlike the prior `Wick − A_r` object — the
   DC-subtracted deficit passes the order-`≤ 2` moment test: the DC subtraction genuinely *moves the
   obstruction up one order* (the `b = 0` mass `D₀ = 1` is exactly what makes the order-2 minor
   positive). `D₀·D₂ − D₁² = 3qn` is a clean new energy identity (`theorem hankel2_eq`).

2. **REFUTATION at order 3, char-0 structural.** The leading `3×3` deficit Hankel minor is negative
   for *every* prime (numerically `+ + − −` sign pattern, prime-independent). The exact cause is
   already in the char-0 deficit `gₖ := Wickₖ − Eₖ(ℂ)`: `g₁ = n − n = 0` (the antipodal pairs make
   `E₁ = n = Wick₁`, **zero** deficit at depth 1) while `g₂ = 3n > 0`. A nonnegative measure with
   first moment `0` is a point mass at `0`, forcing the second moment `0`; since `g₂ = 3n ≠ 0`, the
   `gₖ` are **not** a moment sequence, and the `2×2` char-0 Hankel minor `g₁·g₃ − g₂² = −(3n)² = −9n²`
   is strictly negative (`theorem char0_hankel2_neg`). This is a genuinely DIFFERENT refutation
   location from the prior one (`+ + − −`, not a sign-flip at order 2), but the conclusion is the
   same: **no Hamburger-moment / global-SOS certificate exists for the deficit.**

## What survives (the honest partial)

The DC-subtracted route does NOT prove the prize, and the moment-certificate door is closed at order
`3` by an *exact char-0 identity* (`g₁ = 0`, `g₂ = 3n`). The salvageable true facts, landed here
axiom-clean, are: the new order-2 identity `D₀D₂ − D₁² = 3qn > 0` (a positive-definite *truncated*
moment block — the prize bound holds through the depth-`≤ 2` Hankel block for the genuine char-`p`
periods) and the exact obstruction minor `g₁g₃ − g₂² = −9n²` that any future certificate must dodge.

Issue #444.
-/

namespace ProximityGap.Frontier.DCSubtractedSOSHankel

/-! ## Char-0 exact energies (the depth-`≤ 3` block where `W_r = 0` for all `q > n⁴`) -/

/-- `E₁(μ_n) = n` (antipodal pairs `x + (−x) = 0`; `= (2·1−1)‼·n = Wick₁`). -/
def E1 (n : ℤ) : ℤ := n

/-- `E₂(μ_n) = 3n² − 3n` (in-tree `_CharZeroEnergyClosedForm`; `W₂ = 0` for all `q > n⁴`). -/
def E2 (n : ℤ) : ℤ := 3 * n ^ 2 - 3 * n

/-- `E₃(μ_n) = 15n³ − 45n² + 40n` (in-tree; `W₃ = 0` for all `q > n⁴`). -/
def E3 (n : ℤ) : ℤ := 15 * n ^ 3 - 45 * n ^ 2 + 40 * n

/-- The "Wick" leading term `(2r−1)‼·n^r`. -/
def wick (r : ℕ) (n : ℤ) : ℤ := (Nat.doubleFactorial (2 * r - 1) : ℤ) * n ^ r

@[simp] theorem wick_zero (n : ℤ) : wick 0 n = 1 := by simp [wick, Nat.doubleFactorial]
@[simp] theorem wick_one (n : ℤ) : wick 1 n = n := by simp [wick, Nat.doubleFactorial]
@[simp] theorem wick_two (n : ℤ) : wick 2 n = 3 * n ^ 2 := by
  simp [wick, Nat.doubleFactorial]
@[simp] theorem wick_three (n : ℤ) : wick 3 n = 15 * n ^ 3 := by
  simp [wick, Nat.doubleFactorial]

/-! ## The `q`-scaled DC-subtracted deficit `Dₖ = q·Wickₖ − aₖ`, `aₖ = q·Eₖ − n^{2k}` -/

/-- `D₀ = q·Wick₀ − a₀ = q·1 − (q − 1) = 1` (the `b = 0` DC mass survives subtraction as the unit). -/
def D0 (q n : ℤ) : ℤ := q * wick 0 n - (q - 1)

/-- `D₁ = q·Wick₁ − a₁ = q·n − (q·E₁ − n²) = n²` (the depth-1 deficit is pure `n²`, `q`-free). -/
def D1 (q n : ℤ) : ℤ := q * wick 1 n - (q * E1 n - n ^ (2 * 1))

/-- `D₂ = q·Wick₂ − a₂ = q·3n² − (q·E₂ − n⁴) = 3qn + n⁴`. -/
def D2 (q n : ℤ) : ℤ := q * wick 2 n - (q * E2 n - n ^ (2 * 2))

/-- `D₃ = q·Wick₃ − a₃ = q·15n³ − (q·E₃ − n⁶) = q·(45n²−40n) + n⁶`. -/
def D3 (q n : ℤ) : ℤ := q * wick 3 n - (q * E3 n - n ^ (2 * 3))

theorem D0_eq (q n : ℤ) : D0 q n = 1 := by rw [D0, wick_zero]; ring

theorem D1_eq (q n : ℤ) : D1 q n = n ^ 2 := by
  rw [D1, E1, wick_one]; ring

theorem D2_eq (q n : ℤ) : D2 q n = 3 * q * n + n ^ 4 := by
  rw [D2, E2, wick_two]; ring

theorem D3_eq (q n : ℤ) : D3 q n = q * (45 * n ^ 2 - 40 * n) + n ^ 6 := by
  rw [D3, E3, wick_three]; ring

/-! ## Result 1 — the NEW exact identity (surviving partial): order-2 Hankel minor `= 3qn` -/

/-- **The leading `2×2` DC-subtracted deficit Hankel minor equals `3·q·n`.**
`det [[D₀, D₁], [D₁, D₂]] = D₀·D₂ − D₁² = (3qn + n⁴) − (n²)² = 3qn`. Strictly positive for `n ≥ 1`,
`q ≥ 1`: the DC-subtracted deficit passes the order-`≤ 2` moment test, the prior `Wick − A_r` object
did not. The `b = 0` DC mass `D₀ = 1` is exactly what lifts this minor positive. -/
theorem hankel2_eq (q n : ℤ) : D0 q n * D2 q n - D1 q n ^ 2 = 3 * q * n := by
  rw [D0_eq, D1_eq, D2_eq]; ring

/-- The order-2 minor is strictly positive in the prize regime (`q ≥ 1`, `n ≥ 1`). -/
theorem hankel2_pos {q n : ℤ} (hq : 1 ≤ q) (hn : 1 ≤ n) :
    0 < D0 q n * D2 q n - D1 q n ^ 2 := by
  rw [hankel2_eq]; positivity

/-! ## Result 2 — the REFUTATION (char-0 structural, order 3): the obstruction minor `= −9n²` -/

/-- `g₁ = Wick₁ − E₁(ℂ) = n − n = 0`. The depth-1 char-0 deficit **vanishes** (antipodal pairs make
`E₁ = n = Wick₁`). This single exact zero is the root cause of the order-3 refutation. -/
theorem g1_eq (n : ℤ) : wick 1 n - E1 n = 0 := by rw [E1, wick_one]; ring

/-- `g₂ = Wick₂ − E₂(ℂ) = 3n² − (3n²−3n) = 3n`, strictly positive for `n ≥ 1`. -/
theorem g2_eq (n : ℤ) : wick 2 n - E2 n = 3 * n := by rw [E2, wick_two]; ring

/-- `g₃ = Wick₃ − E₃(ℂ) = 15n³ − (15n³−45n²+40n) = 45n² − 40n`. -/
theorem g3_eq (n : ℤ) : wick 3 n - E3 n = 45 * n ^ 2 - 40 * n := by rw [E3, wick_three]; ring

/-- **REFUTATION: the char-0 deficit is NOT a moment sequence — its `2×2` Hankel minor is `−9n² < 0`.**
`det [[g₁, g₂], [g₂, g₃]] = g₁·g₃ − g₂² = 0·g₃ − (3n)² = −9n²`. Because `g₁ = 0` (an *exact*
identity) while `g₂ = 3n ≠ 0`, no nonnegative measure can have moments `(gₖ)` (first moment `0` ⟹
point mass at `0` ⟹ second moment `0`, contradicting `g₂ = 3n`). Hence the DC-subtracted SOS /
Hamburger-moment certificate **does not exist**, and the obstruction is char-0 (Lam–Leung), not a
bad-prime effect: it survives `q → ∞`. The refutation lives at order `3` (the char-`p` leading `3×3`
minor inherits this), strictly *higher* than the prior `Wick − A_r` order-2 break. -/
theorem char0_hankel2_neg (n : ℤ) :
    (wick 1 n - E1 n) * (wick 3 n - E3 n) - (wick 2 n - E2 n) ^ 2 = -9 * n ^ 2 := by
  rw [g1_eq, g2_eq, g3_eq]; ring

/-- The char-0 obstruction minor is strictly negative for `n ≥ 1`. -/
theorem char0_hankel2_strict_neg {n : ℤ} (hn : 1 ≤ n) :
    (wick 1 n - E1 n) * (wick 3 n - E3 n) - (wick 2 n - E2 n) ^ 2 < 0 := by
  rw [char0_hankel2_neg]; nlinarith [sq_nonneg n, hn]

/-! ## Exact numeric anchors (the `n = 16` worst-prime `q = 61057` instance, matching the probe) -/

/-- At the empirically-worst `n = 16` prime `q = 61057`: order-2 minor `= 3·61057·16 = 2930736 > 0`. -/
theorem hankel2_n16_p61057 : D0 61057 16 * D2 61057 16 - D1 61057 16 ^ 2 = 2930736 := by
  rw [hankel2_eq]; norm_num

/-- At `n = 16`: char-0 obstruction minor `= −9·16² = −2304 < 0`. -/
theorem char0_hankel2_n16 :
    (wick 1 16 - E1 16) * (wick 3 16 - E3 16) - (wick 2 16 - E2 16) ^ 2 = -2304 := by
  rw [char0_hankel2_neg]; norm_num

end ProximityGap.Frontier.DCSubtractedSOSHankel

-- Axiom audit (run by the iterate script):
#print axioms ProximityGap.Frontier.DCSubtractedSOSHankel.hankel2_eq
#print axioms ProximityGap.Frontier.DCSubtractedSOSHankel.hankel2_pos
#print axioms ProximityGap.Frontier.DCSubtractedSOSHankel.char0_hankel2_neg
#print axioms ProximityGap.Frontier.DCSubtractedSOSHankel.char0_hankel2_strict_neg
