/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# The char-0 additive energy `E_7(μ_n)`: exact closed form (#444, avenue L2)

Companion to `_CharZeroEnergyClosedForm.lean` (which lands `E_2 … E_6`). This file extends the
char-0 additive-energy closed-form ladder to **`r = 7`** (leading double-factorial coefficient
`(2·7−1)‼ = 13‼ = 135135`).

## The object

For the `2`-power multiplicative subgroup `μ_n` (`n = 2^μ`, the `n`-th roots of unity in `ℂ`), the
`r`-fold char-0 additive energy is
`E_r(ℂ) = #{(x,y) ∈ μ_n^r × μ_n^r : Σ_i x_i = Σ_i y_i  over ℂ}`.

Because the only `ℚ`-linear relation among `2^μ`-th roots of unity is the antipodal
`ζ^{a+n/2} = −ζ^a`, the map `ζ^a ↦ ±e_{a mod n/2}` sends `μ_n` bijectively onto the cross-polytope
vertices `S = {±e_j : j < n/2} ⊂ ℤ^{n/2}`, and `Σ x_i = Σ y_i` over `ℂ ⟺` the same identity in
`ℤ^{n/2}`. Hence `E_r(ℂ)` is the additive energy of `S`, which by the constant-term identity
`energy(S) = CT[(Σ_{j<m}(t_j + t_j^{-1}))^{2r}]` (`m = n/2`) collapses to
`E_r(ℂ) = (2r)! · [z^r] f(z)^{n/2}`, `f(z) = Σ_{k≥0} z^k/(k!)²`.

## The closed form (`r = 7`, computed + verified this session)

Expanding `(2·7)! · [z^7] f(z)^{n/2}` gives the **degree-7 polynomial in `n`**

```
E_7(ℂ) = 135135 n⁷ − 2837835 n⁶ + 26801775 n⁵ − 141891750 n⁴
         + 433726293 n³ − 708996288 n² + 471556800 n
```

with leading coefficient `(2·7−1)‼ = 135135` (the real-Gaussian / Lam–Leung "Wick" value) and
second coefficient `−C(7,2)·135135 = −2837835` (one coincident coordinate pair).

**Exact-verification (`scripts`, this session):**
- the generating-function value `(14)! · [z^7] f(z)^{n/2}` matches the brute-force cross-polytope
  additive-energy count at `n = 2, 4, 6, 8` (e.g. `E_7(2) = 3432 = C(14,7)`, `E_7(8) = 16993726464`);
- the degree-7 fit through `n = 2,…,16` reproduces the exact values at the *extra* points
  `n = 18, 20, 22` (over-determined check, no curve-fitting artifact);
- leading coeff `= 13‼ = 135135`, second coeff `= −C(7,2)·13‼ = −2837835`, both as predicted by the
  `E_r` second-coefficient law `−C(r,2)(2r−1)‼`.

## What this file proves (axiom-clean)

Taking the closed-form polynomial as the definition of `E_7(ℂ)` (the energy ⇔ polynomial identity
is the cited antipodal/cyclotomic bridge, exact-verified above; its full `Polynomial.cyclotomic`
formalization is a separate brick), we prove, all `⊆ {propext, Classical.choice, Quot.sound}`:

- the **small-case exact values** `E_7(2) = 3432`, `E_7(4) = 11778624`, `E_7(6) = 936369720`,
  `E_7(8) = 16993726464` (the anchors that pin the degree-7 fit — `by decide`/`by norm_num`);
- the **exact deficit** `D_7 := wick 7 n − E_7(ℂ) = 2837835 n⁶ − 26801775 n⁵ + 141891750 n⁴
  − 433726293 n³ + 708996288 n² − 471556800 n`, with leading coefficient `C(7,2)·13‼`;
- the **char-0 Gaussian energy bound** `E_7(ℂ) ≤ (2·7−1)‼·n⁷ = 135135 n⁷` for `n ≥ 2` (the
  *provable half* of `GaussianEnergyBound` at `r = 7`; the char-`p` transfer at depth `r ≈ ln q`
  is the part refuted at the prize, so this char-0 bound is the boundary of what is true);
- the **deficit is strictly positive** for `n ≥ 2` (the cushion shrinks but never vanishes in
  char 0); the deficit factors as `n · g(n)` with `g((n−2)+2)` having *all nonnegative*
  coefficients, the SOS certificate driving the `nlinarith` proof.

Issue #444.
-/

namespace ProximityGap.Frontier.E7ClosedForm

/-- `E_7(ℂ)(n)`: the char-0 additive energy of `μ_n` at depth `r = 7`, the exact degree-7 closed
form `135135 n⁷ − 2837835 n⁶ + 26801775 n⁵ − 141891750 n⁴ + 433726293 n³ − 708996288 n² +
471556800 n` (leading coeff `(2·7−1)‼ = 135135`, second coeff `−C(7,2)·135135`). -/
def E7 (n : ℤ) : ℤ :=
  135135 * n ^ 7 - 2837835 * n ^ 6 + 26801775 * n ^ 5 - 141891750 * n ^ 4
    + 433726293 * n ^ 3 - 708996288 * n ^ 2 + 471556800 * n

/-- The "Wick" leading term `(2r−1)‼·n^r` (`(2r-1)‼ = doubleFactorial (2r-1)`). -/
def wick (r : ℕ) (n : ℤ) : ℤ := (Nat.doubleFactorial (2 * r - 1) : ℤ) * n ^ r

@[simp] theorem wick_seven (n : ℤ) : wick 7 n = 135135 * n ^ 7 := by
  simp [wick, Nat.doubleFactorial]

/-! ## Small-case exact values (the anchors pinning the degree-7 fit) -/

/-- `E_7(2) = 3432 = C(14,7)` (the all-coincident base; brute-force cross-polytope energy match). -/
theorem E7_two : E7 2 = 3432 := by decide

/-- `E_7(4) = 11778624` (brute-force cross-polytope energy match). -/
theorem E7_four : E7 4 = 11778624 := by decide

/-- `E_7(6) = 936369720` (brute-force cross-polytope energy match). -/
theorem E7_six : E7 6 = 936369720 := by decide

/-- `E_7(8) = 16993726464` (brute-force cross-polytope energy match). -/
theorem E7_eight : E7 8 = 16993726464 := by decide

/-! ## The exact char-0 deficit `D_7 = wick 7 n − E_7(ℂ)` (leading coefficient `C(7,2)·13‼`) -/

/-- The exact deficit `wick 7 n − E_7(ℂ) = 2837835 n⁶ − 26801775 n⁵ + 141891750 n⁴ −
433726293 n³ + 708996288 n² − 471556800 n`. Leading coefficient `C(7,2)·(2·7−1)‼ = 21·135135 =
2837835`. -/
theorem deficit_seven (n : ℤ) :
    wick 7 n - E7 n =
      2837835 * n ^ 6 - 26801775 * n ^ 5 + 141891750 * n ^ 4 - 433726293 * n ^ 3
        + 708996288 * n ^ 2 - 471556800 * n := by
  simp only [wick_seven, E7]; ring

/-- The deficit factors as `n · g(n)` with `g` written in the shifted variable `(n−2)` having all
**nonnegative** coefficients — the SOS certificate that makes positivity manifest for `n ≥ 2`:
`D_7(n) = n·(8646924 + 46162116(n−2) + 1408407(n−2)² + 40990950(n−2)³ + 1576575(n−2)⁴
+ 2837835(n−2)⁵)`. -/
theorem deficit_seven_factored (n : ℤ) :
    wick 7 n - E7 n =
      n * (8646924 + 46162116 * (n - 2) + 1408407 * (n - 2) ^ 2 + 40990950 * (n - 2) ^ 3
        + 1576575 * (n - 2) ^ 4 + 2837835 * (n - 2) ^ 5) := by
  rw [deficit_seven]; ring

/-! ## The char-0 Gaussian energy bound: `E_7(ℂ) ≤ (2·7−1)‼·n⁷ = 135135 n⁷` for `n ≥ 2`

This is the *provable half* of `GaussianEnergyBound` at `r = 7`. (The char-`p` analogue at depth
`r ≈ ln q` is the part this session's exact computation **refutes** at the prize, so this char-0
bound is precisely the boundary of what is true.) -/

theorem E7_le_wick (n : ℤ) (hn : 2 ≤ n) : E7 n ≤ wick 7 n := by
  have h := deficit_seven_factored n
  have hn0 : (0 : ℤ) ≤ n := by linarith
  have ht : (0 : ℤ) ≤ n - 2 := by linarith
  -- each `n·(n-2)^k ≥ 0`, so the nonneg-combination factorization gives `wick - E7 ≥ 0`.
  nlinarith [h, hn0,
    mul_nonneg hn0 ht,
    mul_nonneg hn0 (pow_nonneg ht 2),
    mul_nonneg hn0 (pow_nonneg ht 3),
    mul_nonneg hn0 (pow_nonneg ht 4),
    mul_nonneg hn0 (pow_nonneg ht 5)]

/-! ## The deficit is strictly positive (the cushion shrinks but never vanishes in char 0) -/

theorem deficit_seven_pos (n : ℤ) (hn : 2 ≤ n) : 0 < wick 7 n - E7 n := by
  have h := deficit_seven_factored n
  have hn0 : (0 : ℤ) < n := by linarith
  have ht : (0 : ℤ) ≤ n - 2 := by linarith
  nlinarith [h, hn0,
    mul_pos hn0 (by norm_num : (0:ℤ) < 8646924),
    mul_nonneg (le_of_lt hn0) ht,
    mul_nonneg (le_of_lt hn0) (pow_nonneg ht 2),
    mul_nonneg (le_of_lt hn0) (pow_nonneg ht 3),
    mul_nonneg (le_of_lt hn0) (pow_nonneg ht 4),
    mul_nonneg (le_of_lt hn0) (pow_nonneg ht 5)]

/-- The deficit-to-Wick ratio cushion: `wick 7 n − E_7(ℂ) = C(7,2)·13‼·n⁶ + (lower order)`, so
`(wick − E_7)/wick → C(7,2)/n = 21/n` as `n → ∞` — the collapse of this cushion at the moment-optimal
depth `r ≈ ln q ≪ n/2` is what refutes the energy/moment route at the prize. The leading
coefficient `2837835 = 21·135135 = C(7,2)·(2·7−1)‼` is recorded here as the exact ratio numerator. -/
theorem deficit_seven_leading : (2837835 : ℤ) = 21 * 135135 := by norm_num

end ProximityGap.Frontier.E7ClosedForm

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.E7ClosedForm.E7_two
#print axioms ProximityGap.Frontier.E7ClosedForm.E7_eight
#print axioms ProximityGap.Frontier.E7ClosedForm.deficit_seven
#print axioms ProximityGap.Frontier.E7ClosedForm.E7_le_wick
#print axioms ProximityGap.Frontier.E7ClosedForm.deficit_seven_pos
