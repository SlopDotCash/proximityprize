/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# wf8-B4: the `r = 2` coefficient of the DC-subtracted cosh-MGF overflows its Gaussian value at
some sub-prize (`β ≈ 3`) primes — so the termwise route to `Φ_p^{nz}(y) ≤ exp(n y²/2)` fails there.
(#444, lane wf-B4)

## The target

`W1-MGF`:   `Φ_p^{nz}(y) := (1/q) ∑_{b≠0} cosh(η_b y)  ≤  exp(n y²/2)`   for all `y ≥ 0`,

where `η_b = ∑_{x∈μ_n} e_p(b x)` are the (real, since `μ_n = −μ_n`) Gauss periods of the dyadic
subgroup `μ_n ⊂ F_p^*` (`n = 2^μ`), `q = p`. Lane B4 was asked to **prove** this directly.

## What is established (and what is NOT)

1. **Coefficient dominance is sufficient for `W1-MGF`.** Both sides are even power series with
   nonnegative coefficients:
   `Φ_p^{nz}(y) = ∑_r a_r · y^{2r}/(2r)!`  with  `a_r = (q·E_r − n^{2r})/q`,
   `exp(n y²/2) = ∑_r W_r · y^{2r}/(2r)!`  with  `W_r = (2r−1)‼·n^r`  (the Wick numbers).
   `mgf_of_coeff` (PROVEN) is `(∀ r, a_r ≤ W_r) → ` partial-sum domination.  Coefficient
   dominance is only SUFFICIENT, not necessary: since `a_0 = (q−1)/q < 1 = W_0`, `Φ < exp` for
   small `y` even when some higher coefficient overflows.  So a coefficient overflow does NOT by
   itself show `W1-MGF` is false.

2. **The `r = 2` coefficient overflows when the additive-energy spur is large.** `a_2 ≤ W_2`
   clears (over `q > 0`) to `E_2 ≤ 3n² + n⁴/q`.  Writing `E_2 = 3n²−3n + spur`,
   `coeffTwo_overflow_of_spur` proves the overflow for `n ≥ 2`, `q ≥ n⁴`, `spur ≥ 4n` — a
   CONDITIONAL statement: no prime `q ≥ n⁴` with such a spur is exhibited in this file.

## Numerics (probe `scripts/probes/rust/probe_wf8B4_*.rs`) — SUB-PRIZE primes only

At `n = 32` the probe reports spur primes `p = 32993` (`E_2 = 3744`), `65537`, `37217`, `50177`
(`E_2 = 3360`), with `a_2/W_2 > 1` and probe function ratios `max_y Φ_nz/exp(ny²/2) > 1` near the
saddle.  All four primes are `< 32⁴ = 1048576` (`β ≈ 3`), so they do NOT satisfy the `q ≥ n⁴`
hypothesis of `coeffTwo_overflow_of_spur`.  An independent exact recomputation (audit
2026-10-28) of `E_2(μ_32)` for all primes `p ≡ 1 (mod 32)` in the prize window `[32⁴, 2·32⁴]`
found `E_2 = 2976 = 3n² − 3n`, i.e. spur `0`, throughout.  So nothing here shows `W1-MGF` fails at
prize scale; the function-level violations are probe data at sub-prize primes.

## What this file proves (axiom-clean: `propext, Classical.choice, Quot.sound`)

* `dcCoeff r q Er n := (q·E_r − n^{2r})/q`, `wick2 n := 3 n²` — the `r=2` MGF / Gaussian coefficients.
* `mgf_of_coeff` — coefficient dominance `(∀ r ∈ S, a r ≤ W r)` ⇒ partial-sum MGF domination.
* `coeffTwo_le_iff_cleared` — `dcCoeff 2 q E₂ n ≤ wick2 n ↔ q·E₂ − n⁴ ≤ 3n²·q` (clear `q > 0`).
* `coeffTwo_overflow_of_spur` — conditional: for `n ≥ 2`, `q ≥ n⁴`, spur `≥ 4n`, the `r=2`
  coefficient strictly exceeds Wick.
* `coeffTwo_overflow_n32_p32993` — the exact integer instance (`norm_num`): at `n=32, q=32993,
  E₂=3744` (the probe value; the prime is sub-prize, `q < n⁴`) the `r=2` coefficient overflows.

## References
- `_wf8B1_kurtosis_cap.lean` (B1; note it proves the kurtosis cap `mu_n_kurtosis_cap`, it does not
  establish a prize-scale spur).
- `Frontier/DCSubtractedCoshMGF.lean` (the in-tree DC-subtracted cosh-MGF identity + consumer).
- [ABF26] ePrint 2026/680, §5.0. #444.
- Probes: `scripts/probes/rust/probe_wf8B4_v2.rs`, `probe_wf8B4_spurhunt.rs`,
  `scripts/probes/probe_wf8B4_obstruction.py`.
-/
set_option linter.style.longLine false
set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.WF8B4

/-! ## The two power-series coefficient families -/

/-- The `r`-th coefficient of the **DC-subtracted cosh-MGF** `Φ_p^{nz}(y) = ∑_r a_r y^{2r}/(2r)!`:
`a_r = (q·E_r − n^{2r})/q` (`E_r` the `r`-fold additive energy of `μ_n`; the principal `b=0` term
`n^{2r}` removed). Equals `((q−1)/q)·M(r)` for the non-principal moment `M(r)`. -/
noncomputable def dcCoeff (r : ℕ) (q Er n : ℝ) : ℝ := (q * Er - n ^ (2 * r)) / q

/-- The `r = 2` Gaussian coefficient `W₂ = (2·2−1)‼·n² = 3 n²`. -/
def wick2 (n : ℝ) : ℝ := 3 * n ^ 2

/-! ## (1) The clean TRUE direction: coefficient dominance ⟹ the MGF bound (no shortcut) -/

/-- **`W1-MGF` is implied by the per-`r` W3 moment family.** If every coefficient is at most its Wick
value, `a r ≤ W r`, then every partial sum of the DC-subtracted cosh-MGF is dominated by the Gaussian's:
`∑_{r∈S} a r · y^{2r}/(2r)! ≤ ∑_{r∈S} W r · y^{2r}/(2r)!`. (The full `tsum` bound follows by
`tsum_le_tsum` given summability.  This direction is sufficient only: `W1-MGF` can hold even when
some coefficient overflows.) -/
theorem mgf_of_coeff (S : Finset ℕ) (a W : ℕ → ℝ) (y : ℝ)
    (hcoeff : ∀ r ∈ S, a r ≤ W r)
    (hpos : ∀ r ∈ S, (0 : ℝ) ≤ y ^ (2 * r) / ((2 * r).factorial : ℝ)) :
    (∑ r ∈ S, a r * (y ^ (2 * r) / ((2 * r).factorial : ℝ)))
      ≤ ∑ r ∈ S, W r * (y ^ (2 * r) / ((2 * r).factorial : ℝ)) :=
  Finset.sum_le_sum (fun r hr => mul_le_mul_of_nonneg_right (hcoeff r hr) (hpos r hr))

/-! ## (2) The `r = 2` coefficient bound as a cleared integer inequality -/

/-- **The `r = 2` MGF-coefficient bound, cleared.** Over `q > 0`, `dcCoeff 2 q E₂ n ≤ wick2 n`
(i.e. `(q·E₂ − n⁴)/q ≤ 3 n²`) is equivalent to `q·E₂ − n⁴ ≤ 3 n²·q`. (`n^(2*2) = n⁴`.) -/
theorem coeffTwo_le_iff_cleared (q E₂ n : ℝ) (hq : 0 < q) :
    dcCoeff 2 q E₂ n ≤ wick2 n ↔ q * E₂ - n ^ 4 ≤ 3 * n ^ 2 * q := by
  unfold dcCoeff wick2
  have h4 : n ^ (2 * 2) = n ^ 4 := by norm_num
  rw [h4, div_le_iff₀ hq]

/-! ## (3) THE OBSTRUCTION: the char-`p` spur breaks the `r = 2` coefficient -/

/-- **Conditional `r = 2` overflow.** If `n ≥ 2`, `q ≥ n⁴`, and the char-`p` additive-energy
spur is at least `4n` (no such prime is exhibited here; the probe's spur primes are all `< n⁴`),
then the `r = 2` coefficient of the DC-subtracted cosh-MGF strictly exceed its Gaussian value:
`wick2 n < dcCoeff 2 q ((3n²−3n)+spur) n`.

Indeed `dcCoeff 2 ≤ wick2 ⟺ q·E₂ − n⁴ ≤ 3n²q ⟺ q·spur ≤ 3n³ + n⁴` (substitute `E₂ = 3n²−3n+spur`).
With `4n ≤ spur` and `q ≥ n⁴`, `q·spur ≥ 4nq = 3nq + nq ≥ 3nq + n·n⁴ = 3nq + n⁵ > 3n³ + n⁴` (the last
step uses `n ≥ 2`). So the cap is broken and the coefficient overflows.  Coefficient overflow
blocks the termwise route only; it does not by itself refute `W1-MGF`. -/
theorem coeffTwo_overflow_of_spur {n q spur : ℤ}
    (hn : 2 ≤ n) (hq : n ^ 4 ≤ q) (hspur : 4 * n ≤ spur) :
    wick2 (n : ℝ) < dcCoeff 2 (q : ℝ) (((3 * n ^ 2 - 3 * n) + spur : ℤ) : ℝ) (n : ℝ) := by
  have hnpos : (0 : ℤ) < n := by omega
  have hqpos : (0 : ℤ) < q := by nlinarith [pow_pos hnpos 4, hq]
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqpos
  -- the cleared strict inequality `3n²q < q·E₂ − n⁴` (E₂ = 3n²−3n+spur)
  have key : 3 * (n:ℝ)^2 * (q:ℝ)
      < (q:ℝ) * (((3 * n ^ 2 - 3 * n) + spur : ℤ) : ℝ) - (n:ℝ) ^ 4 := by
    have hspR : (4 * (n:ℝ)) ≤ (spur:ℝ) := by exact_mod_cast hspur
    have hqn4 : (n:ℝ)^4 ≤ (q:ℝ) := by exact_mod_cast hq
    have hnR : (2 : ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    have hcast : (((3 * n ^ 2 - 3 * n) + spur : ℤ) : ℝ)
        = 3 * (n:ℝ)^2 - 3 * (n:ℝ) + (spur:ℝ) := by push_cast; ring
    rw [hcast]
    -- 3n²q < q(3n²−3n+spur) − n⁴ ⇔ q·spur > 3nq + n⁴.
    -- q·spur ≥ 4nq = 3nq + nq ≥ 3nq + n·n⁴ = 3nq + n⁵ > 3nq + n⁴  (n ≥ 2)
    have hnpos' : (0 : ℝ) < (n:ℝ) := by linarith
    have h1 : 4 * (n:ℝ) * (q:ℝ) ≤ (spur:ℝ) * (q:ℝ) :=
      mul_le_mul_of_nonneg_right hspR hqR.le
    have h2 : (n:ℝ) * (n:ℝ)^4 ≤ (n:ℝ) * (q:ℝ) :=
      mul_le_mul_of_nonneg_left hqn4 hnpos'.le
    nlinarith [h1, h2, hqR, hnR, hqn4, pow_pos hnpos' 4, pow_pos hnpos' 5]
  -- transport: ¬(dcCoeff ≤ wick2) ↔ wick2 < dcCoeff
  have hnotle : ¬ (dcCoeff 2 (q:ℝ) (((3*n^2-3*n)+spur:ℤ):ℝ) (n:ℝ) ≤ wick2 (n:ℝ)) := by
    rw [coeffTwo_le_iff_cleared (q:ℝ) _ (n:ℝ) hqR]; linarith [key]
  exact lt_of_not_ge hnotle

/-- **Exact integer instance: `n = 32`, `q = 32993`, `E₂ = 3744`.** The probe-measured char-`p`
second additive energy at this prime is `E₂ = 3744` (char-`0` value `3·32² − 3·32 = 2976`, spur
`768 = 24n`).  The `r = 2` coefficient strictly exceeds the Gaussian's:
`wick2 32 < dcCoeff 2 32993 3744 32`.  Note `32993 < 32⁴`, so this is a sub-prize (`β ≈ 3`) prime,
and coefficient overflow alone does not refute `W1-MGF`.  Closed integers, `norm_num`. -/
theorem coeffTwo_overflow_n32_p32993 :
    wick2 (32 : ℝ) < dcCoeff 2 (32993 : ℝ) (3744 : ℝ) (32 : ℝ) := by
  unfold wick2 dcCoeff
  rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 32993)]
  norm_num

end ArkLib.ProximityGap.Frontier.WF8B4

/-! ## Axiom audit (expected: `propext`, `Classical.choice`, `Quot.sound` only) -/
#print axioms ArkLib.ProximityGap.Frontier.WF8B4.mgf_of_coeff
#print axioms ArkLib.ProximityGap.Frontier.WF8B4.coeffTwo_le_iff_cleared
#print axioms ArkLib.ProximityGap.Frontier.WF8B4.coeffTwo_overflow_of_spur
#print axioms ArkLib.ProximityGap.Frontier.WF8B4.coeffTwo_overflow_n32_p32993
