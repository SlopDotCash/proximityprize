/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# The char-0 additive energy `E_8(μ_n)`: exact closed form (#444, avenue L2)

Companion to `_CharZeroEnergyClosedForm.lean` (which lands `E_2 … E_6`) and
`_AvL2_E7ClosedForm.lean` (which lands `E_7`). This file extends the char-0 additive-energy
closed-form ladder to **`r = 8`** (leading double-factorial coefficient `(2·8−1)‼ = 15‼ = 2027025`),
the next rung of the `E_r` ladder that §6.1 of #444 flags as the only in-tree forward motion on the
char-0 face ("extending the E_r ladder (E₈+)").

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

## The closed form (`r = 8`, computed + verified this session)

Expanding `(2·8)! · [z^8] f(z)^{n/2}` gives the **degree-8 polynomial in `n`**

```
E_8(ℂ) = 2027025 n⁸ − 56756700 n⁷ + 728377650 n⁶ − 5439183750 n⁵
         + 25055875845 n⁴ − 69934975110 n³ + 107438611995 n² − 68492499075 n
```

with leading coefficient `(2·8−1)‼ = 15‼ = 2027025` (the real-Gaussian / Lam–Leung "Wick" value)
and second coefficient `−C(8,2)·2027025 = −28·2027025 = −56756700` (one coincident coordinate pair),
both matching the `E_r` second-coefficient law `−C(r,2)(2r−1)‼`.

**Exact-verification (`scripts/probes/probe_e8_closedform.py`, this session):**
- the generating-function value `(16)! · [z^8] f(z)^{n/2}` matches the brute-force cross-polytope
  additive-energy count at `n = 2, 4, 6` (e.g. `E_8(2) = 12870 = C(16,8)`,
  `E_8(6) = 27770358330`);
- the degree-8 fit through `n = 2,…,18` reproduces the exact GF values at the *extra* points
  `n = 20, 22, …, 38` (over-determined check, no curve-fitting artifact);
- leading coeff `= 15‼ = 2027025`, second coeff `= −C(8,2)·15‼ = −56756700`, both as predicted by
  the `E_r` second-coefficient law `−C(r,2)(2r−1)‼`.

## What this file proves (axiom-clean)

Taking the closed-form polynomial as the definition of `E_8(ℂ)` (the energy ⇔ polynomial identity
is the cited antipodal/cyclotomic bridge, exact-verified above; its full `Polynomial.cyclotomic`
formalization is a separate brick), we prove, all `⊆ {propext, Classical.choice, Quot.sound}`:

- the **small-case exact values** `E_8(2) = 12870`, `E_8(4) = 165636900`, `E_8(6) = 27770358330`
  (the anchors that pin the degree-8 fit — `by decide`);
- the **exact deficit** `D_8 := wick 8 n − E_8(ℂ) = 56756700 n⁷ − 728377650 n⁶ + 5439183750 n⁵
  − 25055875845 n⁴ + 69934975110 n³ − 107438611995 n² + 68492499075 n`, with leading coefficient
  `C(8,2)·15‼ = 56756700`;
- the **char-0 Gaussian energy bound** `E_8(ℂ) ≤ (2·8−1)‼·n⁸ = 2027025 n⁸` for `n ≥ 2` (the
  *provable half* of `GaussianEnergyBound` at `r = 8`; the char-`p` transfer at depth `r ≈ ln q` is
  the part refuted at the prize, so this char-0 bound is the boundary of what is true);
- the **deficit is strictly positive** for `n ≥ 2` (the cushion shrinks but never vanishes in
  char 0). Unlike `r ≤ 7`, the deficit's cofactor `g(n) := D_8/n` does **not** become
  all-nonneg-coefficient under the shift `n ↦ (n−2)`; the SOS certificate is taken in the shifted
  variable `u = 2n−5` (`g` is a positive-definite degree-6 form with **no real roots**, minimum
  `≈ 1.24·10⁸` at `n ≈ 2.16`), where `64·g(n)` has all-nonnegative `u`-coefficients —
  driving the `nlinarith` proof for `n ≥ 3`; the `n = 2` case is `by decide`.

Issue #444.
-/

namespace ProximityGap.Frontier.E8ClosedForm

/-- `E_8(ℂ)(n)`: the char-0 additive energy of `μ_n` at depth `r = 8`, the exact degree-8 closed
form `2027025 n⁸ − 56756700 n⁷ + 728377650 n⁶ − 5439183750 n⁵ + 25055875845 n⁴ − 69934975110 n³
+ 107438611995 n² − 68492499075 n` (leading coeff `(2·8−1)‼ = 2027025`, second coeff
`−C(8,2)·2027025`). -/
def E8 (n : ℤ) : ℤ :=
  2027025 * n ^ 8 - 56756700 * n ^ 7 + 728377650 * n ^ 6 - 5439183750 * n ^ 5
    + 25055875845 * n ^ 4 - 69934975110 * n ^ 3 + 107438611995 * n ^ 2 - 68492499075 * n

/-- The "Wick" leading term `(2r−1)‼·n^r` (`(2r-1)‼ = doubleFactorial (2r-1)`). -/
def wick (r : ℕ) (n : ℤ) : ℤ := (Nat.doubleFactorial (2 * r - 1) : ℤ) * n ^ r

@[simp] theorem wick_eight (n : ℤ) : wick 8 n = 2027025 * n ^ 8 := by
  simp [wick, Nat.doubleFactorial]

/-! ## Small-case exact values (the anchors pinning the degree-8 fit) -/

/-- `E_8(2) = 12870 = C(16,8)` (the all-coincident base; brute-force cross-polytope match). -/
theorem E8_two : E8 2 = 12870 := by decide

/-- `E_8(4) = 165636900` (brute-force cross-polytope energy match). -/
theorem E8_four : E8 4 = 165636900 := by decide

/-- `E_8(6) = 27770358330` (brute-force cross-polytope energy match). -/
theorem E8_six : E8 6 = 27770358330 := by decide

/-! ## The exact char-0 deficit `D_8 = wick 8 n − E_8(ℂ)` (leading coefficient `C(8,2)·15‼`) -/

/-- The exact deficit `wick 8 n − E_8(ℂ) = 56756700 n⁷ − 728377650 n⁶ + 5439183750 n⁵ −
25055875845 n⁴ + 69934975110 n³ − 107438611995 n² + 68492499075 n`. Leading coefficient
`C(8,2)·(2·8−1)‼ = 28·2027025 = 56756700`. -/
theorem deficit_eight (n : ℤ) :
    wick 8 n - E8 n =
      56756700 * n ^ 7 - 728377650 * n ^ 6 + 5439183750 * n ^ 5 - 25055875845 * n ^ 4
        + 69934975110 * n ^ 3 - 107438611995 * n ^ 2 + 68492499075 * n := by
  simp only [wick_eight, E8]; ring

/-- The deficit factors as `n · g(n)` with `g` a positive-definite degree-6 form.  The SOS witness
is taken in the shifted variable `u = 2n − 5`: `64·g(n) = 43878720600 + 108230239260·u
+ 86914687860·u² + 12390618240·u³ + 6621615000·u⁴ + 245945700·u⁵ + 56756700·u⁶`, all coefficients
nonnegative.  Hence for `n ≥ 3` (`u = 2n−5 ≥ 1 > 0`) the deficit is strictly positive. -/
theorem deficit_eight_factored_u (n : ℤ) :
    64 * (wick 8 n - E8 n) =
      n * (43878720600 + 108230239260 * (2 * n - 5) + 86914687860 * (2 * n - 5) ^ 2
        + 12390618240 * (2 * n - 5) ^ 3 + 6621615000 * (2 * n - 5) ^ 4
        + 245945700 * (2 * n - 5) ^ 5 + 56756700 * (2 * n - 5) ^ 6) := by
  rw [deficit_eight]; ring

/-! ## The char-0 Gaussian energy bound: `E_8(ℂ) ≤ (2·8−1)‼·n⁸ = 2027025 n⁸` for `n ≥ 2`

This is the *provable half* of `GaussianEnergyBound` at `r = 8`. (The char-`p` analogue at depth
`r ≈ ln q` is the part this session's exact computation **refutes** at the prize, so this char-0
bound is precisely the boundary of what is true.) -/

/-- `0 ≤ 64·(wick 8 n − E8 n)` for `n ≥ 3`, from the all-nonneg `u = 2n−5` certificate.  Each
summand `n · cₖ · uᵏ` is a product of nonnegatives (`n ≥ 0`, `cₖ ≥ 0`, `u ≥ 0`). -/
theorem deficit_eight_scaled_nonneg (n : ℤ) (hn : 3 ≤ n) :
    0 ≤ 64 * (wick 8 n - E8 n) := by
  have hu0 : (0 : ℤ) ≤ 2 * n - 5 := by linarith
  have hn0 : (0 : ℤ) ≤ n := by linarith
  rw [deficit_eight_factored_u]
  have h0 : (0:ℤ) ≤ n * 43878720600 := by positivity
  have h1 : (0:ℤ) ≤ n * (108230239260 * (2 * n - 5)) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) hu0)
  have h2 : (0:ℤ) ≤ n * (86914687860 * (2 * n - 5) ^ 2) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 2))
  have h3 : (0:ℤ) ≤ n * (12390618240 * (2 * n - 5) ^ 3) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 3))
  have h4 : (0:ℤ) ≤ n * (6621615000 * (2 * n - 5) ^ 4) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 4))
  have h5 : (0:ℤ) ≤ n * (245945700 * (2 * n - 5) ^ 5) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 5))
  have h6 : (0:ℤ) ≤ n * (56756700 * (2 * n - 5) ^ 6) :=
    mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 6))
  nlinarith [h0, h1, h2, h3, h4, h5, h6]

/-- `E_8(2) ≤ wick 8 2` (the deficit at the base is `518905530 > 0`). -/
theorem E8_le_wick_two : E8 2 ≤ wick 8 2 := by
  rw [E8_two, wick_eight]; norm_num

theorem E8_le_wick (n : ℤ) (hn : 2 ≤ n) : E8 n ≤ wick 8 n := by
  rcases eq_or_lt_of_le hn with h2 | h3
  · -- n = 2: the deficit is `518905530 > 0`
    subst h2; exact E8_le_wick_two
  · -- n ≥ 3: u = 2n - 5 ≥ 1 > 0; the all-nonneg `u`-certificate gives `64·(wick − E8) ≥ 0`.
    have hn3 : (3 : ℤ) ≤ n := by linarith
    have hpos := deficit_eight_scaled_nonneg n hn3
    linarith

/-! ## The deficit is strictly positive (the cushion shrinks but never vanishes in char 0) -/

theorem deficit_eight_pos (n : ℤ) (hn : 2 ≤ n) : 0 < wick 8 n - E8 n := by
  rcases eq_or_lt_of_le hn with h2 | h3
  · subst h2; rw [E8_two, wick_eight]; norm_num
  · have hn3 : (3 : ℤ) ≤ n := by linarith
    have hpos := deficit_eight_scaled_nonneg n hn3
    -- the constant term `n · 43878720600 ≥ 3·43878720600 > 0` keeps it strict
    have hu0 : (0 : ℤ) ≤ 2 * n - 5 := by linarith
    have hn0 : (0 : ℤ) ≤ n := by linarith
    have hcert := deficit_eight_factored_u n
    have hstrict : (0:ℤ) < n * 43878720600 := by positivity
    have h1 : (0:ℤ) ≤ n * (108230239260 * (2 * n - 5)) :=
      mul_nonneg hn0 (mul_nonneg (by norm_num) hu0)
    have h2' : (0:ℤ) ≤ n * (86914687860 * (2 * n - 5) ^ 2) :=
      mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 2))
    have h3' : (0:ℤ) ≤ n * (12390618240 * (2 * n - 5) ^ 3) :=
      mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 3))
    have h4' : (0:ℤ) ≤ n * (6621615000 * (2 * n - 5) ^ 4) :=
      mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 4))
    have h5' : (0:ℤ) ≤ n * (245945700 * (2 * n - 5) ^ 5) :=
      mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 5))
    have h6' : (0:ℤ) ≤ n * (56756700 * (2 * n - 5) ^ 6) :=
      mul_nonneg hn0 (mul_nonneg (by norm_num) (pow_nonneg hu0 6))
    nlinarith [hcert, hstrict, h1, h2', h3', h4', h5', h6']

/-- The deficit-to-Wick ratio cushion: `wick 8 n − E_8(ℂ) = C(8,2)·15‼·n⁷ + (lower order)`, so
`(wick − E_8)/wick → C(8,2)/n = 28/n` as `n → ∞` — the collapse of this cushion at the
moment-optimal depth `r ≈ ln q ≪ n/2` is what refutes the energy/moment route at the prize. The
leading coefficient `56756700 = 28·2027025 = C(8,2)·(2·8−1)‼` is recorded here as the exact ratio
numerator. -/
theorem deficit_eight_leading : (56756700 : ℤ) = 28 * 2027025 := by norm_num

end ProximityGap.Frontier.E8ClosedForm

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.E8ClosedForm.E8_two
#print axioms ProximityGap.Frontier.E8ClosedForm.E8_six
#print axioms ProximityGap.Frontier.E8ClosedForm.deficit_eight
#print axioms ProximityGap.Frontier.E8ClosedForm.E8_le_wick
#print axioms ProximityGap.Frontier.E8ClosedForm.deficit_eight_pos
