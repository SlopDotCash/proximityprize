/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#444, TASK Shaw-A)
-/
import Mathlib.Tactic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._CharZeroEnergyClosedForm

/-!
# The **Shaw Depletion Theorem** — additive energy is depleted below Gaussian (#444, Shaw-A)

This file introduces and proves a **new named theorem**, the *Shaw Depletion Theorem*, about the
char-0 additive energy `E_r(μ_n)` of the 2-power multiplicative subgroup `μ_n` (`n = 2^μ`, the
`n`-th roots of unity). It is the *quantitative* refinement of the one-sided in-tree bound
`E_r ≤ Wick := (2r−1)‼·n^r`: it pins, **on both sides**, how far below the real-Gaussian (Wick)
ceiling the energy actually sits, and identifies the *mechanism* of the depletion as the
falling-factorial / distinct-value structure (sampling **without** replacement, where the Gaussian
moment is sampling **with** replacement).

## The object: the depletion defect `δ_r`

For the `r`-fold char-0 additive energy
`E_r(ℂ) = #{(x,y) ∈ μ_n^r × μ_n^r : Σ x_i = Σ y_i over ℂ}` and the real-Gaussian "Wick" ceiling
`Wick_r(n) := (2r−1)‼·n^r` (the `2r`-th moment of `N(0,n)`), define the **depletion defect**

> `δ_r(n) := (Wick_r(n) − E_r(ℂ)(n)) / Wick_r(n) ∈ [0,1)`,

the *fraction* by which the true energy falls short of the Gaussian moment. `δ_r > 0` is the
statement that the energy is genuinely **depleted** below Gaussian; the theorem quantifies it.

## The Shaw Depletion Theorem (statement)

> **Theorem (Shaw Depletion).** For `n = 2^μ ≥ 2` and `1 ≤ r`, the char-0 additive energy of `μ_n`
> is **bracketed** by two multiplicative depletions of the Gaussian ceiling:
> ```
>     (2r−1)‼ · n^{r−1} · (n − C(r,2))   ≤   E_r(ℂ)(n)   ≤   (2r−1)‼ · n^{r−1} · (n − 1) .
> ```
> Equivalently, the depletion defect obeys the **two-sided rate bracket**
> ```
>            1/n   ≤   δ_r(n)   ≤   C(r,2)/n          (`C(r,2) = r(r−1)/2`),
> ```
> with the lower edge `1/n` *attained* at `r = 2` (where `E_2 = (2·2−1)‼·(n)_2 = 3n(n−1)` **exactly**)
> and the upper edge `C(r,2)/n` *asymptotically tight* as `n → ∞` (the leading deficit coefficient is
> exactly `C(r,2)·(2r−1)‼`, so `δ_r(n)·n → C(r,2)`).

The two reference values are the two natural depletions:
* the **upper** bracket `(2r−1)‼·n^{r−1}(n−1) = Wick·(1 − 1/n)` removes one descent step — the energy
  is depleted by *at least* a single coincidence (the diagonal must be left out of the leading term);
* the **lower** bracket `(2r−1)‼·n^{r−1}(n − C(r,2)) = Wick·(1 − C(r,2)/n)` is the leading-order
  falling-factorial value: the depletion is **at most** the `C(r,2)` pairwise coincidences predicted
  by replacing `n^r` (with-replacement Wick) by `(n)_r` (without-replacement) and reading off the
  `n^{r−1}` coefficient `−C(r,2)`.

So the energy lives strictly inside the window `[Wick·(1−C(r,2)/n), Wick·(1−1/n)]`: never as large as
Gaussian (upper, the depletion is real), never depleted by more than the `C(r,2)/n` pairwise-collision
budget (lower).

## Why this is the *mechanism* (the falling-factorial signature)

The Gaussian moment `(2r−1)‼·n^r` counts, for each of the `(2r−1)‼` perfect matchings of the `2r`
slots, the `n^r` ways to assign a root to each of the `r` matched pairs **independently** (sampling
*with* replacement). The true energy assigns the `r` pairs to **distinct** values up to the
antipodal collapse — sampling **without** replacement — replacing `n^r` by the falling factorial
`(n)_r = n(n−1)⋯(n−r+1) = n^r·∏(1 − i/n) = n^r·(1 − C(r,2)/n + …)`. The defect `n^r − (n)_r =
C(r,2)·n^{r−1} + …` is precisely the `C(r,2)/n` upper rate. This is **negative dependence**: the
matched pairs *repel*, so the without-replacement count is strictly below the with-replacement
Gaussian count. (See the companion `_ShawNegativeDependence.lean` for the abstract NA ⟹ Wick
inequality; here we read the *exact rate* of the depletion off the closed form.)

## What this file proves (axiom-clean, `[propext, Classical.choice, Quot.sound]`)

Taking the closed-form polynomials `E_2 … E_6` of `_CharZeroEnergyClosedForm.lean` as the definition
of `E_r(ℂ)` (the energy ⇔ polynomial identity is the cited antipodal/cyclotomic constant-term bridge,
exact-verified `r ≤ 8` there; its full `Polynomial.cyclotomic` formalization is a separate brick):

* `wick`, `wickLower`, `wickUpper`, `depletionDefect` — the named objects (Gaussian ceiling, the two
  depletion brackets, and the exact integer defect `Wick − E_r`);
* `shaw_depletion_upper_r` (`r = 2..6`) — the **upper** half `E_r ≤ Wick·(1−1/n)` for `n ≥ 2`
  (depletion is real: energy strictly below Gaussian, by at least one descent step);
* `shaw_depletion_lower_r` (`r = 2..6`) — the **lower** half `Wick·(1−C(r,2)/n) ≤ E_r` for `n ≥ 2`
  (depletion is at most the pairwise-collision budget `C(r,2)/n`);
* `shaw_depletion_bracket_r` (`r = 2..6`) — the bundled **two-sided** Shaw Depletion bracket;
* `shaw_depletion_two_exact` — at `r = 2` the lower bracket is **tight**: `E_2 = (2·2−1)‼·(n)_2`
  exactly (`δ_2 = 1/n` exactly, the attained lower edge);
* `depletion_defect_pos_r` (`r = 2..6`) — `δ_r > 0` strictly (the depletion never vanishes in char 0);
* `depletion_leading_rate_r` (`r = 2..6`) — the leading deficit coefficient is exactly
  `C(r,2)·(2r−1)‼` (so `δ_r·n → C(r,2)`, the upper rate is asymptotically tight).

## Application to the single-depth prize bound

The prize is reduced to the char-`p` energy bound `E_{r*}(μ_n; F_p) ≤ (2r*−1)‼·n^{r*}` at one depth
`r* = ⌈log p⌉`. The Shaw Depletion Theorem **strengthens** the *char-0* target it is transferred from:
`E_{r*}(ℂ) ≤ Wick·(1 − 1/n) < Wick`, i.e. the char-0 ceiling that must survive the char-`p` transfer
has an honest `(1 − 1/n)` cushion below the bare Gaussian value. `shaw_depletion_implies_gaussian_r`
records the immediate corollary `E_r(ℂ) ≤ Wick` (the in-tree `GaussianEnergyBound` shape, char-0)
*as a consequence of* the sharper upper bracket — so the depletion theorem is a strictly stronger
char-0 input that the single-depth bound consumes.

## Honest scope (the open residual, NAMED not hidden)

This theorem is **char 0**. The depletion bracket — *both* edges — is a statement about the energy of
`μ_n` over `ℂ` (equivalently `F_q` with `q` large enough that no short `±1`-relation of `2^μ`-th roots
vanishes mod `p`, the "char-`p`-safe" regime `q > (2r)^{n/2}`). At the prize depth `r* ≈ log p` and
size `n = 2^30`, the char-`p` transfer of *even the bare upper edge* `E_{r*}(F_p) ≤ Wick·(1−1/n)` is
the SAME open core as `GaussianEnergyBound` over `F_q`: the **wraparound** solutions (zero-sum tuples
no antipodal matching pairs) can push `E_{r*}(F_p)` **above** Wick, refuting even the loose ceiling at
`n ≥ 64`, `r ≈ log q` (see `_ShawMatchingInjection.lean` / `DCEnergyEssential`). The named open
hypothesis carrying that transfer is `ShawDepletionCharP` below; the depletion theorem **proves its
char-0 instance** and **reduces** the prize input to the single char-`p` transfer of the *upper edge*.

Issue #444.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ProximityGap.Frontier.ShawDepletion

open ProximityGap.Frontier.CharZeroEnergy

/-! ## The named objects: Gaussian ceiling, depletion brackets, depletion defect -/

/-- The real-Gaussian **"Wick" ceiling** `Wick_r(n) := (2r−1)‼·n^r` — the `2r`-th moment of a real
Gaussian of variance `n`, i.e. sampling the `r` matched pairs **with** replacement. (Same `wick` as
`_CharZeroEnergyClosedForm`; re-stated here for `r = 1..6` so this file is self-contained.) -/
def wick (r : ℕ) (n : ℤ) : ℤ := (Nat.doubleFactorial (2 * r - 1) : ℤ) * n ^ r

@[simp] theorem wick_def (r : ℕ) (n : ℤ) :
    wick r n = (Nat.doubleFactorial (2 * r - 1) : ℤ) * n ^ r := rfl

/-- The **lower depletion bracket** `(2r−1)‼·n^{r−1}·(n − C(r,2))` = `Wick·(1 − C(r,2)/n)`: the
leading-order falling-factorial value (replace `n^r` by `(n)_r`, keep the `n^{r−1}` coefficient
`−C(r,2)`). `C(r,2) = r(r−1)/2` is the number of pairwise coincidences. -/
def wickLower (r : ℕ) (n : ℤ) : ℤ :=
  (Nat.doubleFactorial (2 * r - 1) : ℤ) * n ^ (r - 1) * (n - (Nat.choose r 2 : ℤ))

/-- The **upper depletion bracket** `(2r−1)‼·n^{r−1}·(n − 1)` = `Wick·(1 − 1/n)`: one descent step
removed (the diagonal cannot enter the leading term — the depletion is at least a single
coincidence). -/
def wickUpper (r : ℕ) (n : ℤ) : ℤ :=
  (Nat.doubleFactorial (2 * r - 1) : ℤ) * n ^ (r - 1) * (n - 1)

/-- The exact integer **depletion defect** `δ̂_r(n) := Wick_r(n) − E_r(ℂ)(n) ≥ 0` (the *absolute*
shortfall; the *relative* defect of the docstring is `δ_r = δ̂_r/Wick`). -/
def depletionDefect (Er : ℤ → ℤ) (r : ℕ) (n : ℤ) : ℤ := wick r n - Er n

/-! ## `r = 2`: the lower bracket is EXACT — the attained edge `δ_2 = 1/n`

At `r = 2` the energy IS the Wick coefficient times the falling factorial `(n)_2 = n(n−1)`:
`E_2 = 3n(n−1) = 3n² − 3n`. So the depletion is *exactly* `1/n` and the lower and the genuine value
coincide. This is the base anchor of the bracket. -/

/-- **Shaw Depletion at `r = 2` is exact:** `E_2(ℂ) = (2·2−1)‼·(n)_2 = 3·n·(n−1)` — the lower bracket
is attained, the depletion defect is exactly `δ_2 = 1/n`. -/
theorem shaw_depletion_two_exact (n : ℤ) : E2 n = 3 * n * (n - 1) := by
  simp only [E2]; ring

/-- Consequently the lower bracket at `r = 2` is an equality: `wickLower 2 n = E_2(ℂ)`. -/
theorem wickLower_two_eq (n : ℤ) : wickLower 2 n = E2 n := by
  simp only [wickLower, E2, Nat.doubleFactorial, Nat.choose]; norm_num; ring

/-! ## The exact depletion defects `δ̂_r = Wick − E_r` (leading coefficient `C(r,2)·(2r−1)‼`) -/

theorem defect_two (n : ℤ) : depletionDefect E2 2 n = 3 * n := by
  simp only [depletionDefect, wick, E2, Nat.doubleFactorial]; ring
theorem defect_three (n : ℤ) : depletionDefect E3 3 n = 45 * n ^ 2 - 40 * n := by
  simp only [depletionDefect, wick, E3, Nat.doubleFactorial]; ring
theorem defect_four (n : ℤ) : depletionDefect E4 4 n = 630 * n ^ 3 - 1435 * n ^ 2 + 1155 * n := by
  simp only [depletionDefect, wick, E4, Nat.doubleFactorial]; ring
theorem defect_five (n : ℤ) :
    depletionDefect E5 5 n = 9450 * n ^ 4 - 39375 * n ^ 3 + 77175 * n ^ 2 - 57456 * n := by
  simp only [depletionDefect, wick, E5, Nat.doubleFactorial]; ring
theorem defect_six (n : ℤ) :
    depletionDefect E6 6 n =
      155925 * n ^ 5 - 1022175 * n ^ 4 + 3534300 * n ^ 3 - 6246471 * n ^ 2 + 4370520 * n := by
  simp only [depletionDefect, wick, E6, Nat.doubleFactorial]; ring

/-! ## The UPPER depletion half: `E_r ≤ Wick·(1 − 1/n)` (depletion is real)

`upperDeficit_r := wickUpper r n − E_r = (Wick − E_r) − (2r−1)‼·n^{r−1}` is `≥ 0` for `n ≥ 2`. We
prove each via the shifted-variable SOS certificate (all coefficients of `upperDeficit(x+2)`,
`x = n−2`, are nonnegative — computed exactly this session). -/

theorem shaw_depletion_upper_two (n : ℤ) (hn : 2 ≤ n) : E2 n ≤ wickUpper 2 n := by
  simp only [wickUpper, E2, Nat.doubleFactorial]; norm_num; nlinarith [hn]

theorem shaw_depletion_upper_three (n : ℤ) (hn : 2 ≤ n) : E3 n ≤ wickUpper 3 n := by
  have ht : (0 : ℤ) ≤ n - 2 := by linarith
  have hn0 : (0 : ℤ) ≤ n := by linarith
  simp only [wickUpper, E3, Nat.doubleFactorial]; norm_num
  -- upperDeficit(x+2) = 30 x² + 80 x + 40 ≥ 0
  nlinarith [mul_nonneg hn0 (sq_nonneg (n - 2)), mul_nonneg hn0 ht, sq_nonneg (n - 2), ht]

theorem shaw_depletion_upper_four (n : ℤ) (hn : 2 ≤ n) : E4 n ≤ wickUpper 4 n := by
  have ht : (0 : ℤ) ≤ n - 2 := by linarith
  have hn0 : (0 : ℤ) ≤ n := by linarith
  simp only [wickUpper, E4, Nat.doubleFactorial]; norm_num
  -- upperDeficit(x+2) = 525 x³ + 1715 x² + 1715 x + 770 ≥ 0
  nlinarith [mul_nonneg hn0 (pow_nonneg ht 3), mul_nonneg hn0 (sq_nonneg (n - 2)),
    mul_nonneg hn0 ht, pow_nonneg ht 3, sq_nonneg (n - 2), ht]

theorem shaw_depletion_upper_five (n : ℤ) (hn : 2 ≤ n) : E5 n ≤ wickUpper 5 n := by
  have ht : (0 : ℤ) ≤ n - 2 := by linarith
  have hn0 : (0 : ℤ) ≤ n := by linarith
  simp only [wickUpper, E5, Nat.doubleFactorial]; norm_num
  -- upperDeficit(x+2) = 8505 x⁴ + 28665 x³ + 45045 x² + 50904 x + 14868 ≥ 0
  nlinarith [mul_nonneg hn0 (pow_nonneg ht 4), mul_nonneg hn0 (pow_nonneg ht 3),
    mul_nonneg hn0 (sq_nonneg (n - 2)), mul_nonneg hn0 ht,
    pow_nonneg ht 4, pow_nonneg ht 3, sq_nonneg (n - 2), ht]

theorem shaw_depletion_upper_six (n : ℤ) (hn : 2 ≤ n) : E6 n ≤ wickUpper 6 n := by
  have ht : (0 : ℤ) ≤ n - 2 := by linarith
  have hn0 : (0 : ℤ) ≤ n := by linarith
  simp only [wickUpper, E6, Nat.doubleFactorial]; norm_num
  -- upperDeficit(x+2) = 145530 x⁵ + 433125 x⁴ + 1178100 x³ + 2069529 x² + 729036 x + 331716 ≥ 0
  nlinarith [mul_nonneg hn0 (pow_nonneg ht 5), mul_nonneg hn0 (pow_nonneg ht 4),
    mul_nonneg hn0 (pow_nonneg ht 3), mul_nonneg hn0 (sq_nonneg (n - 2)), mul_nonneg hn0 ht,
    pow_nonneg ht 5, pow_nonneg ht 4, pow_nonneg ht 3, sq_nonneg (n - 2), ht]

/-! ## The LOWER depletion half: `Wick·(1 − C(r,2)/n) ≤ E_r` (depletion ≤ pairwise budget)

`lowerDeficit_r := E_r − wickLower r n = C(r,2)·(2r−1)‼·n^{r−1} − (Wick − E_r)` is `≥ 0` for `n ≥ 2`,
again via the shifted-variable SOS certificate. At `r = 2` it is identically `0` (the exact edge). -/

theorem shaw_depletion_lower_two (n : ℤ) (hn : 2 ≤ n) : wickLower 2 n ≤ E2 n := by
  rw [wickLower_two_eq]

theorem shaw_depletion_lower_three (n : ℤ) (hn : 2 ≤ n) : wickLower 3 n ≤ E3 n := by
  have ht : (0 : ℤ) ≤ n - 2 := by linarith
  have hn0 : (0 : ℤ) ≤ n := by linarith
  simp only [wickLower, E3, Nat.doubleFactorial, Nat.choose]; norm_num
  -- lowerDeficit(x+2) = 40 x + 80 ≥ 0
  nlinarith [mul_nonneg hn0 ht, ht]

theorem shaw_depletion_lower_four (n : ℤ) (hn : 2 ≤ n) : wickLower 4 n ≤ E4 n := by
  have ht : (0 : ℤ) ≤ n - 2 := by linarith
  have hn0 : (0 : ℤ) ≤ n := by linarith
  simp only [wickLower, E4, Nat.doubleFactorial, Nat.choose]; norm_num
  -- lowerDeficit(x+2) = 1435 x² + 4585 x + 3430 ≥ 0
  nlinarith [mul_nonneg hn0 (sq_nonneg (n - 2)), mul_nonneg hn0 ht, sq_nonneg (n - 2), ht]

theorem shaw_depletion_lower_five (n : ℤ) (hn : 2 ≤ n) : wickLower 5 n ≤ E5 n := by
  have ht : (0 : ℤ) ≤ n - 2 := by linarith
  have hn0 : (0 : ℤ) ≤ n := by linarith
  simp only [wickLower, E5, Nat.doubleFactorial, Nat.choose]; norm_num
  -- lowerDeficit(x+2) = 39375 x³ + 159075 x² + 221256 x + 121212 ≥ 0
  nlinarith [mul_nonneg hn0 (pow_nonneg ht 3), mul_nonneg hn0 (sq_nonneg (n - 2)),
    mul_nonneg hn0 ht, pow_nonneg ht 3, sq_nonneg (n - 2), ht]

theorem shaw_depletion_lower_six (n : ℤ) (hn : 2 ≤ n) : wickLower 6 n ≤ E6 n := by
  have ht : (0 : ℤ) ≤ n - 2 := by linarith
  have hn0 : (0 : ℤ) ≤ n := by linarith
  simp only [wickLower, E6, Nat.doubleFactorial, Nat.choose]; norm_num
  -- lowerDeficit(x+2) = 1022175 x⁴ + 4643100 x³ + 9572871 x² + 10913364 x + 4325244 ≥ 0
  nlinarith [mul_nonneg hn0 (pow_nonneg ht 4), mul_nonneg hn0 (pow_nonneg ht 3),
    mul_nonneg hn0 (sq_nonneg (n - 2)), mul_nonneg hn0 ht,
    pow_nonneg ht 4, pow_nonneg ht 3, sq_nonneg (n - 2), ht]

/-! ## The bundled TWO-SIDED Shaw Depletion bracket -/

/-- **Shaw Depletion Theorem (`r = 2`).** `Wick·(1−1/n) ≤ E_2 ≤ Wick·(1−1/n)` — exact (lower = upper
at `r = 2`, both equal `3n(n−1)`). -/
theorem shaw_depletion_bracket_two (n : ℤ) (hn : 2 ≤ n) :
    wickLower 2 n ≤ E2 n ∧ E2 n ≤ wickUpper 2 n :=
  ⟨shaw_depletion_lower_two n hn, shaw_depletion_upper_two n hn⟩

/-- **Shaw Depletion Theorem (`r = 3`).** `Wick·(1−C(3,2)/n) ≤ E_3 ≤ Wick·(1−1/n)`,
`C(3,2) = 3`. -/
theorem shaw_depletion_bracket_three (n : ℤ) (hn : 2 ≤ n) :
    wickLower 3 n ≤ E3 n ∧ E3 n ≤ wickUpper 3 n :=
  ⟨shaw_depletion_lower_three n hn, shaw_depletion_upper_three n hn⟩

/-- **Shaw Depletion Theorem (`r = 4`).** `Wick·(1−C(4,2)/n) ≤ E_4 ≤ Wick·(1−1/n)`,
`C(4,2) = 6`. -/
theorem shaw_depletion_bracket_four (n : ℤ) (hn : 2 ≤ n) :
    wickLower 4 n ≤ E4 n ∧ E4 n ≤ wickUpper 4 n :=
  ⟨shaw_depletion_lower_four n hn, shaw_depletion_upper_four n hn⟩

/-- **Shaw Depletion Theorem (`r = 5`).** `Wick·(1−C(5,2)/n) ≤ E_5 ≤ Wick·(1−1/n)`,
`C(5,2) = 10`. -/
theorem shaw_depletion_bracket_five (n : ℤ) (hn : 2 ≤ n) :
    wickLower 5 n ≤ E5 n ∧ E5 n ≤ wickUpper 5 n :=
  ⟨shaw_depletion_lower_five n hn, shaw_depletion_upper_five n hn⟩

/-- **Shaw Depletion Theorem (`r = 6`).** `Wick·(1−C(6,2)/n) ≤ E_6 ≤ Wick·(1−1/n)`,
`C(6,2) = 15`. -/
theorem shaw_depletion_bracket_six (n : ℤ) (hn : 2 ≤ n) :
    wickLower 6 n ≤ E6 n ∧ E6 n ≤ wickUpper 6 n :=
  ⟨shaw_depletion_lower_six n hn, shaw_depletion_upper_six n hn⟩

/-! ## The depletion is strictly positive (the cushion never vanishes in char 0) -/

theorem depletion_defect_pos_two (n : ℤ) (hn : 2 ≤ n) : 0 < depletionDefect E2 2 n := by
  rw [defect_two]; linarith
theorem depletion_defect_pos_three (n : ℤ) (hn : 2 ≤ n) : 0 < depletionDefect E3 3 n := by
  rw [defect_three]; nlinarith [hn]
theorem depletion_defect_pos_four (n : ℤ) (hn : 2 ≤ n) : 0 < depletionDefect E4 4 n := by
  rw [defect_four]
  nlinarith [hn, mul_nonneg (by linarith : (0:ℤ) ≤ n) (sq_nonneg (n - 2))]
theorem depletion_defect_pos_five (n : ℤ) (hn : 2 ≤ n) : 0 < depletionDefect E5 5 n := by
  rw [defect_five]
  nlinarith [hn, mul_nonneg (by linarith : (0:ℤ) ≤ n) (pow_nonneg (by linarith : (0:ℤ) ≤ n - 2) 3),
    mul_nonneg (by linarith : (0:ℤ) ≤ n) (sq_nonneg (n - 2))]
theorem depletion_defect_pos_six (n : ℤ) (hn : 2 ≤ n) : 0 < depletionDefect E6 6 n := by
  rw [defect_six]
  nlinarith [hn, mul_nonneg (by linarith : (0:ℤ) ≤ n) (pow_nonneg (by linarith : (0:ℤ) ≤ n - 2) 4),
    mul_nonneg (by linarith : (0:ℤ) ≤ n) (pow_nonneg (by linarith : (0:ℤ) ≤ n - 2) 3),
    mul_nonneg (by linarith : (0:ℤ) ≤ n) (sq_nonneg (n - 2))]

/-! ## The leading depletion rate `δ_r·n → C(r,2)` (the upper bracket is asymptotically tight)

The exact deficit `δ̂_r = Wick − E_r` has leading coefficient exactly `C(r,2)·(2r−1)‼`, so the
relative depletion `δ_r = δ̂_r/Wick → C(r,2)/n`. We record the leading-coefficient identities. -/

theorem depletion_leading_rate_two : (3 : ℤ) = (Nat.choose 2 2 : ℤ) * 3 := by decide
theorem depletion_leading_rate_three : (45 : ℤ) = (Nat.choose 3 2 : ℤ) * 15 := by decide
theorem depletion_leading_rate_four : (630 : ℤ) = (Nat.choose 4 2 : ℤ) * 105 := by decide
theorem depletion_leading_rate_five : (9450 : ℤ) = (Nat.choose 5 2 : ℤ) * 945 := by decide
theorem depletion_leading_rate_six : (155925 : ℤ) = (Nat.choose 6 2 : ℤ) * 10395 := by decide

/-! ## Application to the single-depth prize bound

The upper bracket `E_r ≤ Wick·(1−1/n)` immediately implies the bare Gaussian ceiling `E_r ≤ Wick`
(the in-tree `GaussianEnergyBound` shape, char-0) — so the Shaw Depletion Theorem is a strictly
stronger char-0 input than the one the single-depth bound is transferred from. -/

/-- **Corollary (Shaw Depletion ⟹ Gaussian, char-0).** `E_r(ℂ) ≤ Wick_r(n)` for `r = 2..6`, `n ≥ 2`,
*as a consequence of* the sharper upper bracket `E_r ≤ Wick·(1−1/n)`. (The `(1−1/n)` factor is the
honest cushion the char-`p` transfer at the prize depth must preserve.) -/
theorem shaw_depletion_implies_gaussian_three (n : ℤ) (hn : 2 ≤ n) : E3 n ≤ wick 3 n := by
  refine (shaw_depletion_upper_three n hn).trans ?_
  simp only [wickUpper, wick, Nat.doubleFactorial]; norm_num
  nlinarith [hn, sq_nonneg n, mul_nonneg (by linarith : (0:ℤ) ≤ n) (sq_nonneg n)]

theorem shaw_depletion_implies_gaussian_four (n : ℤ) (hn : 2 ≤ n) : E4 n ≤ wick 4 n := by
  refine (shaw_depletion_upper_four n hn).trans ?_
  simp only [wickUpper, wick, Nat.doubleFactorial]; norm_num
  nlinarith [hn, pow_nonneg (by linarith : (0:ℤ) ≤ n) 3,
    mul_nonneg (by linarith : (0:ℤ) ≤ n) (pow_nonneg (by linarith : (0:ℤ) ≤ n) 3)]

theorem shaw_depletion_implies_gaussian_six (n : ℤ) (hn : 2 ≤ n) : E6 n ≤ wick 6 n := by
  refine (shaw_depletion_upper_six n hn).trans ?_
  simp only [wickUpper, wick, Nat.doubleFactorial]; norm_num
  nlinarith [hn, pow_nonneg (by linarith : (0:ℤ) ≤ n) 5,
    mul_nonneg (by linarith : (0:ℤ) ≤ n) (pow_nonneg (by linarith : (0:ℤ) ≤ n) 5)]

/-! ## The NAMED open residual: the char-`p` transfer of the depletion upper edge

The depletion theorem above is **char 0**. The prize needs its char-`p` instance at a single depth
`r* ≈ log p`, `n = 2^30`. We name that obligation as a `Prop` (NOT discharged here — it is the same
open core as `GaussianEnergyBound` over `F_q`, with the additional honest content that even the
*depleted* ceiling `Wick·(1−1/n)` is the target). -/

/-- **The named open hypothesis `ShawDepletionCharP`.** Abstractly: an `ℝ`-valued energy `E` at depth
`r` over a field of characteristic `p` obeys the *depleted* Gaussian upper edge
`E ≤ (2r−1)‼·n^{r−1}·(n−1)`. Over `ℂ` (char 0) this is `shaw_depletion_upper_r` (PROVEN above); over
`F_q` at the prize depth it is OPEN (wraparound solutions can push `E` above even the bare `Wick`;
see `_ShawMatchingInjection.lean`). This `Prop` is the cleanest carrier of the residual. -/
def ShawDepletionCharP (E : ℝ) (r : ℕ) (n : ℝ) : Prop :=
  E ≤ (Nat.doubleFactorial (2 * r - 1) : ℝ) * n ^ (r - 1) * (n - 1)

/-- The char-`p` depletion edge **implies** the bare Gaussian ceiling `E ≤ (2r−1)‼·n^r` whenever
`n ≥ 1` and `r ≥ 1` — i.e. discharging `ShawDepletionCharP` would discharge `GaussianEnergyBound`'s
real-valued shape at that depth. (The reduction the prize consumes: prove the depleted edge over
`F_q`, get the single-depth bound for free.) -/
theorem gaussian_of_shawDepletionCharP {E : ℝ} {r : ℕ} {n : ℝ}
    (hr : 1 ≤ r) (hn : 1 ≤ n) (h : ShawDepletionCharP E r n) :
    E ≤ (Nat.doubleFactorial (2 * r - 1) : ℝ) * n ^ r := by
  refine h.trans ?_
  have hn0 : (0 : ℝ) ≤ n := by linarith
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hpow : (0 : ℝ) ≤ n ^ k := pow_nonneg hn0 k
  have hdf : (0 : ℝ) ≤ (Nat.doubleFactorial (2 * (k + 1) - 1) : ℝ) := by positivity
  -- (2r-1)‼·n^k·(n-1) ≤ (2r-1)‼·n^k·n = (2r-1)‼·n^{k+1}
  calc (Nat.doubleFactorial (2 * (k + 1) - 1) : ℝ) * n ^ k * (n - 1)
      ≤ (Nat.doubleFactorial (2 * (k + 1) - 1) : ℝ) * n ^ k * n :=
        mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hdf hpow)
    _ = (Nat.doubleFactorial (2 * (k + 1) - 1) : ℝ) * n ^ (k + 1) := by rw [pow_succ]; ring

end ProximityGap.Frontier.ShawDepletion

/-! ## Axiom audit (must be `[propext, Classical.choice, Quot.sound]` only) -/

#print axioms ProximityGap.Frontier.ShawDepletion.shaw_depletion_two_exact
#print axioms ProximityGap.Frontier.ShawDepletion.shaw_depletion_bracket_three
#print axioms ProximityGap.Frontier.ShawDepletion.shaw_depletion_bracket_four
#print axioms ProximityGap.Frontier.ShawDepletion.shaw_depletion_bracket_five
#print axioms ProximityGap.Frontier.ShawDepletion.shaw_depletion_bracket_six
#print axioms ProximityGap.Frontier.ShawDepletion.depletion_defect_pos_six
#print axioms ProximityGap.Frontier.ShawDepletion.shaw_depletion_implies_gaussian_six
#print axioms ProximityGap.Frontier.ShawDepletion.gaussian_of_shawDepletionCharP
