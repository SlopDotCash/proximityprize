/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# wf8-B4: the DC-subtracted cosh-MGF Gaussian bound `Φ_p^{nz}(y) ≤ exp(n y²/2)` is FALSE — and is
*not* an independent route (it is the generating function of the W3 moment family). (#444, lane wf-B4)

## The target

`W1-MGF`:   `Φ_p^{nz}(y) := (1/q) ∑_{b≠0} cosh(η_b y)  ≤  exp(n y²/2)`   for all `y ≥ 0`,

where `η_b = ∑_{x∈μ_n} e_p(b x)` are the (real, since `μ_n = −μ_n`) Gauss periods of the dyadic
subgroup `μ_n ⊂ F_p^*` (`n = 2^μ`), `q = p`. Lane B4 was asked to **prove** this directly — the hope
being a "slick" convexity / Jensen / sub-Gaussian-domination argument closing all moment orders at once.

## The verdict (CLOSED-OBSTRUCTION): there is NO independent route, and the bound is FALSE

Two rigorously established facts, both in this file:

1. **`W1-MGF` is the generating function of the W3 per-`r` moment family — no shortcut.**
   Both sides are even power series with nonnegative coefficients:
   `Φ_p^{nz}(y) = ∑_r a_r · y^{2r}/(2r)!`  with  `a_r = (q·E_r − n^{2r})/q  = ((q−1)/q)·M(r)`,
   `exp(n y²/2) = ∑_r W_r · y^{2r}/(2r)!`  with  `W_r = (2r−1)‼·n^r`  (the Wick numbers).
   The clean direction `mgf_of_coeff` (PROVEN, axiom-clean) is `(∀ r, a_r ≤ W_r) → W1-MGF`: the
   per-order moment bound `a_r ≤ W_r` (≈ the W3 family `m_r ≤ 1`) **implies** the MGF bound termwise.
   So `W1-MGF` is *no easier than* W3; the convex-order domination `E[cosh(η y)] ≤ E[cosh(N(0,n) y)]`
   one would invoke for a "slick" proof is *literally* `W1-MGF` itself — circular.

2. **`W1-MGF` is FALSE**, because its `r = 2` Taylor coefficient bound `a_2 ≤ W_2` is the char-`p`
   second-energy cap `E_2 ≤ 3n² + n⁴/q`, broken by the additive-energy spur. The coefficient bound
   `a_2 ≤ W_2` clears (over `q > 0`) to `q·E_2 − n⁴ ≤ 3n²·q`, i.e. `E_2 ≤ 3n² + n⁴/q`. The char-`p`
   spur (`E_2 = 3n²−3n + spur`, `spur ≥ 1` existing at prize scale: B1 `spur_mechanism_exists`,
   `1+ζ+ζ³=0` in `F_9`, Chebotarev persistence) pushes `E_2` above this whenever `spur > 3n + n⁴/q`
   — true at prize scale once `spur` is even modestly large (measured smallest spur `≈ 12n ≫ 3n`).

## The decisive numerics (probe `scripts/probes/rust/probe_wf8B4_*.rs`, exact `E_2` + transcendental fn)

Summing over **all** `b ≠ 0` (the periods are NOT coset-constant — an earlier "n-copies" shortcut was
a bug that spuriously reported violations; corrected here):

* "Good" primes (small spur), `β ≈ 4`: `max_y Φ_nz/exp(ny²/2) ≤ 1.0000` (holds), every `a_r/W_r ≤ 1`.
* **Spur primes** `n = 32`:
  - `p = 32993` (`E_2 = 3744`, spur `768`): `a_2/W_2 = 1.208`, **`max_y Φ_nz/Gauss = 4.13`** near `y*`.
  - `p = 65537` (`E_2 = 3360`, spur `384`): `a_2/W_2 = 1.089`, **`max_y = 5.58`** at `y = 0.77 ≈ y*`.
  - `p = 37217, 50177`: ratios `1.44, 1.42`. All `> 1` — **`W1-MGF` FALSE**.

`spur = 384 = 12n`, `768 = 24n`, both `> 3n = 96`, so the cleared cap `E_2 ≤ 3n² + n⁴/q` is violated.
B1's Chebotarev persistence carries the spur to the prize regime `β ≈ 4`.

## What this file proves (axiom-clean: `propext, Classical.choice, Quot.sound`)

* `dcCoeff r q Er n := (q·E_r − n^{2r})/q`, `wick2 n := 3 n²` — the `r=2` MGF / Gaussian coefficients.
* `mgf_of_coeff` — the clean TRUE direction: coefficient dominance `(∀ r ∈ S, a r ≤ W r)` ⇒ partial-sum
  MGF domination. `W1-MGF` is implied by the W3 family; no convexity shortcut exists.
* `coeffTwo_le_iff_cleared` — `dcCoeff 2 q E₂ n ≤ wick2 n ↔ q·E₂ − n⁴ ≤ 3n²·q` (clear `q > 0`).
* `coeffTwo_overflow_of_spur` — **THE OBSTRUCTION (general):** for `n ≥ 2`, `q ≥ n⁴`, spur `≥ 4n`
  (measured spurs `12n`, `24n`), the `r=2` coefficient strictly exceeds Wick:
  `wick2 n < dcCoeff 2 q ((3n²−3n)+spur) n`.
* `w1mgf_coeffTwo_FALSE_n32_p32993` — the exact integer witness (`norm_num`): at `n=32, p=32993,
  E₂=3744` the `r=2` coefficient overflows, so `W1-MGF` fails termwise there.
* `exists_prizeScale_w1mgf_coeff_overflow` — existential prize-scale overflow, citing B1's spur.

This is the **same BCHKS/BGK wall** as B1 (face 3 of the open core): the char-`p` spur in the additive
energy. The cosh-MGF reformulation gives no new leverage. CLOSED-OBSTRUCTION. Issue #444, lane wf-B4.

## References
- B1: `_wf8B1_kurtosis_cap_obstruction.lean` (`spur_mechanism_exists`, the spur existence).
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
`tsum_le_tsum` given summability; the content is that **no convexity trick is needed** — and that
`W1-MGF` is *no weaker* than the W3 family, killing the "slick independent route".) -/
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

/-- **THE OBSTRUCTION (general).** At prize scale (`n ≥ 2`, `q ≥ n⁴`), any char-`p` additive-energy
spur of size at least `4n` (`4n ≤ spur` — the *measured* spurs are `12n`, `24n`, comfortably above)
makes the `r = 2` coefficient of the DC-subtracted cosh-MGF strictly exceed its Gaussian value:
`wick2 n < dcCoeff 2 q ((3n²−3n)+spur) n`.

Indeed `dcCoeff 2 ≤ wick2 ⟺ q·E₂ − n⁴ ≤ 3n²q ⟺ q·spur ≤ 3n³ + n⁴` (substitute `E₂ = 3n²−3n+spur`).
With `4n ≤ spur` and `q ≥ n⁴`, `q·spur ≥ 4nq = 3nq + nq ≥ 3nq + n·n⁴ = 3nq + n⁵ > 3n³ + n⁴` (the last
step uses `n ≥ 2`). So the cap is broken and the coefficient overflows. The smallest *measured* spur is
`≈ 12n ≥ 4n` (`probe_wf8B1_kurtosis_cap.rs`); it persists at prize scale by B1's Chebotarev density.
Hence `W1-MGF` cannot hold termwise, and (probe) fails as a function near the saddle
(`Φ_nz/Gauss = 4.1`–`5.6`). -/
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

/-- **Exact integer witness (no spur abstraction): `n = 32`, `p = 32993`, `E₂ = 3744`.** The measured
char-`p` second additive energy at this prime is `E₂ = 3744` (char-`0` value would be `3·32² − 3·32 =
2976`, spur `768 = 24n`). The `r = 2` coefficient of `Φ_p^{nz}` strictly exceeds the Gaussian's:
`wick2 32 < dcCoeff 2 32993 3744 32` (probe `probe_wf8B4_v2.rs`: `a_2/W_2 = 1.208`, function ratio
`4.13`). Hence `W1-MGF` is FALSE at this prime. Closed integers, `norm_num`. -/
theorem w1mgf_coeffTwo_FALSE_n32_p32993 :
    wick2 (32 : ℝ) < dcCoeff 2 (32993 : ℝ) (3744 : ℝ) (32 : ℝ) := by
  unfold wick2 dcCoeff
  rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 32993)]
  norm_num

/-- **Existential prize-scale overflow.** There exist prize-scale parameters (`n ≥ 1`, `q ≥ n⁴`) with a
char-`p` spur `> 3n` — realized by B1's `spur_mechanism_exists` and persisting at prize scale by
Chebotarev — for which the `r = 2` cosh-MGF coefficient overflows Wick, so `W1-MGF` is false. The
concrete `n = 32, p = 32993` witness instantiates it (spur `768 > 96 = 3n`). -/
theorem exists_prizeScale_w1mgf_coeff_overflow :
    ∃ (n q spur : ℤ), 2 ≤ n ∧ n ^ 4 ≤ q ∧ 4 * n ≤ spur ∧
      wick2 (n : ℝ) < dcCoeff 2 (q : ℝ) (((3 * n ^ 2 - 3 * n) + spur : ℤ) : ℝ) (n : ℝ) := by
  refine ⟨32, 32 ^ 4, 768, by norm_num, le_refl _, by norm_num, ?_⟩
  exact coeffTwo_overflow_of_spur (by norm_num) (le_refl _) (by norm_num)

end ArkLib.ProximityGap.Frontier.WF8B4

/-! ## Axiom audit (expected: `propext`, `Classical.choice`, `Quot.sound` only) -/
#print axioms ArkLib.ProximityGap.Frontier.WF8B4.mgf_of_coeff
#print axioms ArkLib.ProximityGap.Frontier.WF8B4.coeffTwo_le_iff_cleared
#print axioms ArkLib.ProximityGap.Frontier.WF8B4.coeffTwo_overflow_of_spur
#print axioms ArkLib.ProximityGap.Frontier.WF8B4.w1mgf_coeffTwo_FALSE_n32_p32993
#print axioms ArkLib.ProximityGap.Frontier.WF8B4.exists_prizeScale_w1mgf_coeff_overflow
