/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# The char-0 additive energy `E_9(μ_n)`: exact closed form (#444, avenue L2)

Companion to `_CharZeroEnergyClosedForm.lean` (`E_2 … E_6`), `_AvL2_E7ClosedForm.lean` (`E_7`) and
`_AvL2_E8ClosedForm.lean` (`E_8`). This file extends the char-0 additive-energy closed-form ladder
to **`r = 9`** (leading double-factorial coefficient `(2·9−1)‼ = 17‼ = 34459425`), the next rung of
the `E_r` ladder that §6.1 of #444 flags as the only in-tree forward motion on the char-0 face
("extending the E_r ladder (E₈+)").

## The object

For the `2`-power multiplicative subgroup `μ_n` (`n = 2^μ`, the `n`-th roots of unity in `ℂ`), the
`r`-fold char-0 additive energy is `E_r(ℂ) = #{(x,y) : Σ_i x_i = Σ_i y_i over ℂ}`. Via the antipodal
bridge `ζ^a ↦ ±e_{a mod n/2}` it equals the additive energy of the cross-polytope
`S = {±e_j : j < n/2} ⊂ ℤ^{n/2}`, which collapses to
`E_r(ℂ) = (2r)! · [z^r] f(z)^{n/2}`, `f(z) = Σ_{k≥0} z^k/(k!)²`.

## The closed form (`r = 9`, computed + verified this session)

```
E_9(ℂ) = 34459425 n⁹ − 1240539300 n⁸ + 20744573850 n⁷ − 206963306550 n⁶ + 1327347186165 n⁵
         − 5524263935190 n⁴ + 14357763632355 n³ − 20957471507115 n² + 12885585512800 n
```

leading coeff `(2·9−1)‼ = 17‼ = 34459425` (the real-Gaussian / Lam–Leung "Wick" value), second
coeff `−C(9,2)·34459425 = −36·34459425 = −1240539300` (matching the `E_r` second-coefficient law
`−C(r,2)(2r−1)‼`).

**Exact-verification (`scripts/probes/probe_e9_closedform.py`, this session):**
- the GF value `(18)! · [z^9] f(z)^{n/2}` matches the brute-force cross-polytope additive-energy
  count at `n = 2, 4` (`E_9(2) = 48620 = C(18,9)`, `E_9(4) = 2363904400`);
- the degree-9 fit through `n = 2,…,20` reproduces the GF value at the *extra* points
  `n = 22, …, 42` (over-determined check, no curve-fitting artifact);
- leading coeff `= 17‼ = 34459425`, second coeff `= −C(9,2)·17‼ = −1240539300`.

## What this file proves (axiom-clean)

Taking the closed-form polynomial as the definition of `E_9(ℂ)` (the energy ⇔ polynomial bridge is
the cited antipodal/cyclotomic identity, exact-verified above), we prove, all
`⊆ {propext, Classical.choice, Quot.sound}`:

- the **small-case exact values** `E_9(2) = 48620`, `E_9(4) = 2363904400` (`by decide`);
- the **exact deficit** `D_9 := wick 9 n − E_9(ℂ)`, with leading coefficient `C(9,2)·17‼ =
  1240539300`;
- the **char-0 Gaussian energy bound** `E_9(ℂ) ≤ (2·9−1)‼·n⁹ = 34459425 n⁹` for `n ≥ 2` (the
  *provable half* of `GaussianEnergyBound` at `r = 9`; the char-`p` transfer at depth `r ≈ ln q`
  is the part refuted at the prize, so this char-0 bound is the boundary of what is true);
- the **deficit is strictly positive** for `n ≥ 2` (the cushion shrinks `~36/n` but never vanishes).
  Continuing the trend recorded at `r = 8`, the SOS basis drifts further from `n−2`: the deficit
  cofactor `g(n) := D_9/n` is a degree-7 form with a single real root at `n ≈ 1.982 < 2`, so it is
  positive on `[2,∞)`; the all-nonneg SOS certificate is taken in `u = 2n − 7` (`128·g(n)` has
  all-nonnegative `u`-coefficients), valid for `n ≥ 4` (`u ≥ 1`); `n = 2, 3` are `by decide`.

Issue #444.
-/

namespace ProximityGap.Frontier.E9ClosedForm

/-- `E_9(ℂ)(n)`: the char-0 additive energy of `μ_n` at depth `r = 9`, the exact degree-9 closed
form (leading coeff `(2·9−1)‼ = 34459425`, second coeff `−C(9,2)·34459425`). -/
def E9 (n : ℤ) : ℤ :=
  34459425 * n ^ 9 - 1240539300 * n ^ 8 + 20744573850 * n ^ 7 - 206963306550 * n ^ 6
    + 1327347186165 * n ^ 5 - 5524263935190 * n ^ 4 + 14357763632355 * n ^ 3
    - 20957471507115 * n ^ 2 + 12885585512800 * n

/-- The "Wick" leading term `(2r−1)‼·n^r`. -/
def wick (r : ℕ) (n : ℤ) : ℤ := (Nat.doubleFactorial (2 * r - 1) : ℤ) * n ^ r

@[simp] theorem wick_nine (n : ℤ) : wick 9 n = 34459425 * n ^ 9 := by
  simp [wick, Nat.doubleFactorial]

/-! ## Small-case exact values (the anchors pinning the degree-9 fit) -/

/-- `E_9(2) = 48620 = C(18,9)` (the all-coincident base; brute-force cross-polytope match). -/
theorem E9_two : E9 2 = 48620 := by decide

/-- `E_9(4) = 2363904400` (brute-force cross-polytope energy match). -/
theorem E9_four : E9 4 = 2363904400 := by decide

/-! ## The exact char-0 deficit `D_9 = wick 9 n − E_9(ℂ)` (leading coefficient `C(9,2)·17‼`) -/

/-- The exact deficit `wick 9 n − E_9(ℂ)`. Leading coefficient `C(9,2)·(2·9−1)‼ = 36·34459425 =
1240539300`. -/
theorem deficit_nine (n : ℤ) :
    wick 9 n - E9 n =
      1240539300 * n ^ 8 - 20744573850 * n ^ 7 + 206963306550 * n ^ 6 - 1327347186165 * n ^ 5
        + 5524263935190 * n ^ 4 - 14357763632355 * n ^ 3 + 20957471507115 * n ^ 2
        - 12885585512800 * n := by
  simp only [wick_nine, E9]; ring

/-- `128·(wick 9 n − E_9) = n · (Σ_k c_k · u^k)` with `u = 2n − 7` and all `c_k ≥ 0`.  Hence for
`n ≥ 4` (`u = 2n−7 ≥ 1 > 0`) the deficit is strictly positive. -/
theorem deficit_nine_factored_u (n : ℤ) :
    128 * (wick 9 n - E9 n) =
      n * (102304530207880 + 109272934287660 * (2 * n - 7) + 57933199896000 * (2 * n - 7) ^ 2
        + 16343700953580 * (2 * n - 7) ^ 3 + 2754236164680 * (2 * n - 7) ^ 4
        + 361823962500 * (2 * n - 7) ^ 5 + 19297278000 * (2 * n - 7) ^ 6
        + 1240539300 * (2 * n - 7) ^ 7) := by
  rw [deficit_nine]; ring

/-- `0 ≤ 128·(wick 9 n − E9 n)` for `n ≥ 4`, from the all-nonneg `u = 2n−7` certificate. -/
theorem deficit_nine_scaled_nonneg (n : ℤ) (hn : 4 ≤ n) :
    0 ≤ 128 * (wick 9 n - E9 n) := by
  have hu0 : (0 : ℤ) ≤ 2 * n - 7 := by linarith
  have hn0 : (0 : ℤ) ≤ n := by linarith
  rw [deficit_nine_factored_u]
  have h0 : (0:ℤ) ≤ n * 102304530207880 := by positivity
  have h1 : (0:ℤ) ≤ n * (109272934287660 * (2 * n - 7)) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) hu0)
  have h2 : (0:ℤ) ≤ n * (57933199896000 * (2 * n - 7) ^ 2) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 2))
  have h3 : (0:ℤ) ≤ n * (16343700953580 * (2 * n - 7) ^ 3) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 3))
  have h4 : (0:ℤ) ≤ n * (2754236164680 * (2 * n - 7) ^ 4) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 4))
  have h5 : (0:ℤ) ≤ n * (361823962500 * (2 * n - 7) ^ 5) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 5))
  have h6 : (0:ℤ) ≤ n * (19297278000 * (2 * n - 7) ^ 6) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 6))
  have h7 : (0:ℤ) ≤ n * (1240539300 * (2 * n - 7) ^ 7) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 7))
  nlinarith [h0, h1, h2, h3, h4, h5, h6, h7]

/-! ## The char-0 Gaussian energy bound: `E_9(ℂ) ≤ (2·9−1)‼·n⁹ = 34459425 n⁹` for `n ≥ 2` -/

/-- `E_9(2) ≤ wick 9 2` and `E_9(3) ≤ wick 9 3` (the deficits at the base are positive). -/
theorem E9_le_wick_base_two : E9 2 ≤ wick 9 2 := by rw [E9_two, wick_nine]; norm_num

theorem E9_le_wick_base_three : E9 3 ≤ wick 9 3 := by decide

theorem E9_le_wick (n : ℤ) (hn : 2 ≤ n) : E9 n ≤ wick 9 n := by
  rcases lt_or_ge n 4 with hlt | hge
  · -- n ∈ {2, 3}
    interval_cases n
    · exact E9_le_wick_base_two
    · exact E9_le_wick_base_three
  · have hpos := deficit_nine_scaled_nonneg n hge
    linarith

/-! ## The deficit is strictly positive (the cushion shrinks but never vanishes in char 0) -/

theorem deficit_nine_pos (n : ℤ) (hn : 2 ≤ n) : 0 < wick 9 n - E9 n := by
  rcases lt_or_ge n 4 with hlt | hge
  · interval_cases n
    · rw [deficit_nine]; norm_num
    · rw [deficit_nine]; norm_num
  · have hu0 : (0 : ℤ) ≤ 2 * n - 7 := by linarith
    have hn0 : (0 : ℤ) ≤ n := by linarith
    have hcert := deficit_nine_factored_u n
    have hstrict : (0:ℤ) < n * 102304530207880 := by positivity
    have h1 : (0:ℤ) ≤ n * (109272934287660 * (2 * n - 7)) :=
      mul_nonneg hn0 (mul_nonneg (by norm_num) hu0)
    have h2 : (0:ℤ) ≤ n * (57933199896000 * (2 * n - 7) ^ 2) :=
      mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 2))
    have h3 : (0:ℤ) ≤ n * (16343700953580 * (2 * n - 7) ^ 3) :=
      mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 3))
    have h4 : (0:ℤ) ≤ n * (2754236164680 * (2 * n - 7) ^ 4) :=
      mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 4))
    have h5 : (0:ℤ) ≤ n * (361823962500 * (2 * n - 7) ^ 5) :=
      mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 5))
    have h6 : (0:ℤ) ≤ n * (19297278000 * (2 * n - 7) ^ 6) :=
      mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 6))
    have h7 : (0:ℤ) ≤ n * (1240539300 * (2 * n - 7) ^ 7) :=
      mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 7))
    nlinarith [hcert, hstrict, h1, h2, h3, h4, h5, h6, h7]

/-- The deficit-to-Wick ratio cushion leading numerator `1240539300 = 36·34459425 =
C(9,2)·(2·9−1)‼` (the `(wick − E_9)/wick → C(9,2)/n = 36/n` asymptotics). -/
theorem deficit_nine_leading : (1240539300 : ℤ) = 36 * 34459425 := by norm_num

end ProximityGap.Frontier.E9ClosedForm

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.E9ClosedForm.E9_two
#print axioms ProximityGap.Frontier.E9ClosedForm.deficit_nine
#print axioms ProximityGap.Frontier.E9ClosedForm.E9_le_wick
#print axioms ProximityGap.Frontier.E9ClosedForm.deficit_nine_pos
