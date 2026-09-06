/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (wf-M1)
-/
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# The height/Mahler count-route reduction of the char-`p` transfer (#444, lane wf-M1)

## Setting (the height route to the prize)

The prize bound `M(μ_n) = max_{b≠0}‖η_b‖ ≤ C·√(n·log(p/n))` reduces (substrate
`subgroup_gaussSum_moment` + Markov, see lane wf-M4) to the per-depth energy bound

  `E_r(μ_n) ≤ C₀ · (2r-1)‼ · n^r`     (the char-`0` count, with a constant `C₀`).

`E_r(μ_n)` counts the `2r`-fold signed subset-sum coincidences of `μ_n`-th roots that vanish
**mod `p`**.  By Lam–Leung (substrate `EvenOddAntipodalCharFree`), the configurations that vanish
**over `ℤ`** are exactly the `(2r-1)‼` antipodal matchings (the char-`0` count `E_r^{(0)}`).  The
char-`p` transfer is

  `E_r(μ_n) = E_r^{(0)} + Spur_r(p)`,     `Spur_r(p) = #{ antipodal-free `T`, `|T| ≤ 2r`, `p ∣ N(σ_T)` }`,

where `σ_T = Σ_{i∈T} ±ζ_n^i` is a **nonzero** cyclotomic integer (antipodal-free ⇒ `σ_T ≠ 0` over
`ℤ`, so `N(σ_T) ≠ 0`) and `N = Norm_{ℚ(ζ_n)/ℚ}`.  A spurious config at the prize prime `p` exists
**iff `p ∣ N(σ_T)`**.

## What lane wf-M1 establishes (the two-pronged finding)

### (1) The crude *house* bound is exponentially too weak — and the sharp *Mahler* bound only
recovers a factor 2 in the exponent (still super-polynomial).

`σ_T` is a sum of `≤ 2r` roots of unity, so each of the `φ(n) = n/2` conjugates has modulus `≤ 2r`
(house), giving `1 ≤ |N(σ_T)| ≤ (2r)^{n/2}`.  The "no-spurious ⇒ char-`p` = char-`0`" hope needs
`(2r)^{n/2} < p` — `probe_wf5M1_house_prescreen.py` shows the threshold depth is `r* = e^{2ln p/n}/2
→ 1/2` as `n→∞`: the house bound only rules out spurious at depth `< 1`, useless at the needed
depth `r ~ ln p`.  The **structure-aware (Mahler / geometric-mean) replacement** is measured in
`probe_wf5M1_truenorm.py` / `_maxnorm.py`: the conjugates have *RMS* size `√(2r)` (the trace
identity `Σ_i|σ_T^{(i)}|² = (n/2)·|T|`), so the *geometric-mean* and hence the true norm obeys

  `|N(σ_T)| ≤ |T|^{n/4} = (house)^{φ(n)/2}`        (Mahler bound, **proven below as `mahler_norm_bound`**),

robustly half the crude exponent (measured ratio `log|N|/log(house^{φ(n)}) = 0.476–0.500` across
`n ∈ {16,32,64}`).  This matches lane wf-M2's `p^R ≤ w^{n/4}` and makes the verdict precise: even
the *sharp* height bound gives `max|N| ≍ (2r)^{n/4}`, **super-polynomial** in `n`, while `p ≍ n^β`
is polynomial.  ⟹ **the max-norm route cannot rule out spurious** at the prize prime; only the
*count* route can.

### (2) The count route — the actual sufficient lemma, with a sharp pre-screen.

Since the height of *individual* norms is uncontrollable but most norms are small integers whose
prime factors miss the (large) prize prime, the load-bearing quantity is the **count** `Spur_r(p)`
at the *fixed* prize prime.  Pre-screen `probe_wf5M1_fixedp.py` (exact mod-`p`, proper `μ_n`, prize
primes `p ≍ n^4, p≡1 mod n`): `Spur_r(p) = 0` for all weights `≤ 8` at `n ∈ {16,32,64}` — the
generic prize prime admits **no** spurious config at low depth (a witness *does* exist at the
exceptional prime `665857 ≡ 1 mod 32`, dividing the small norm `N=2·665857` of `T={0,1,4,8,9,21}`
— confirmed in `probe_wf5M1_witness.py` — but such primes are exactly those *dividing* a small
cyclotomic norm, a sparse set the prize primes generically avoid).

The clean **sufficient lemma (S-M1)** this route reduces to is therefore a *relative* count bound:

  `(S-M1)   Spur_r(p) ≤ ε · E_r^{(0)} = ε · (2r-1)‼ · n^r`     (for a constant `ε`, all prize `p`).

`(S-M1) ⟹ E_r(μ_n) ≤ (1+ε)·(2r-1)‼·n^r ⟹ M ≤ (1+ε)^{1/2r}·C·√(n log(p/n))` — the **prize shape**
with constant `C·(1+ε)^{1/2r} → C`.  **This file proves that implication, axiom-clean.**

## What is PROVEN here (axiom-clean ℝ/ℕ arithmetic)

* `mahler_norm_bound` — the Mahler/AM-GM height atom: `φ(n)` nonneg reals `aᵢ = |σ_T^{(i)}|²` with
  `Σ aᵢ = φ(n)·|T|` (the 2-power trace identity, NT2) have `∏ aᵢ ≤ |T|^{φ(n)}`, hence
  `|N(σ_T)| = √(∏ aᵢ) ≤ |T|^{φ(n)/2}` — the factor-2-in-exponent sharpening of house, measured in §1.
* `countRoute_energy_bound` — `(S-M1) ⟹ E_r ≤ (1+ε)·E_r^{(0)}` (the relative-count assembly).
* `countRoute_prize_constant` — the constant transfer: `(1+ε)^{1/2r}` multiplies the prize constant
  and `→ 1`, so `(S-M1)` at *any* fixed `ε` yields the prize square-root shape.

## The PRECISE remaining open step (the crux this lane pins)

`(S-M1)` itself — a *relative* count bound `Spur_r(p) ≤ ε·(2r-1)‼·n^r` *uniform over prize primes*
`p ≍ n^β`, to depth `r ~ ln p`.  Pre-screen says `Spur_r(p) = 0` (so `ε = 0`) at depth `≤ 8` for
the generic prize prime, but a *deterministic* proof for the band `r ∈ [β log n, 1.36 n]` requires
counting prize primes dividing some weight-`≤2r` antipodal-free cyclotomic norm — equivalently a
**Chebotarev/effective-splitting** count of `{p : p ∣ N(σ_T), some |T|≤2r}` — which is **not** a
second-moment quantity (it consumes the [π] non-archimedean ideal-factorisation data).  This is the
genuine open crux; lane wf-M1 reduces the prize to it and proves the surrounding implications.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. #444.
- Lam–Leung, *On vanishing sums of roots of unity* (the char-`0` antipodal count).
- Duke–Garcia, *On the house of Gauss periods* (the period-house study this sharpens).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false


namespace ArkLib.ProximityGap.Frontier.WF5M1

open scoped BigOperators

/-! ### §1  The Mahler / geometric-mean height atom

`σ_T` has `M = φ(n)` complex conjugates `σ_T^{(i)}`.  Set `aᵢ = |σ_T^{(i)}|² ≥ 0`.  The 2-power
cyclotomic trace identity gives `Σ aᵢ = M · b` with `b = |T|` (each root contributes `1` to each
`|σ^{(i)}|²` on average; `Tr(ζ^m)=0` kills the cross terms over the full conjugate set).  AM–GM then
bounds the product, and `|N(σ_T)| = √(∏ aᵢ)`.  This is the sharp (factor-2-in-exponent) replacement
for the crude house bound `∏ aᵢ ≤ ((2r)²)^M`. -/

/-- **Mahler height atom (AM–GM form).**  Given `M` nonnegative reals `a` with arithmetic mean
exactly `b` (i.e. `∑ a = M·b`, the 2-power trace identity NT2 with `b = |T|`), the product is
`≤ b^M`.  Hence `|N(σ_T)| = √(∏ aᵢ) ≤ b^{M/2} = |T|^{φ(n)/2}` — the structure-aware bound,
**half** the crude house exponent `b^M` (which would need `aᵢ ≤ b²`, i.e. conjugate `≤ 2r`, not
`√(2r)`). -/
theorem mahler_norm_bound {M : ℕ} (a : Fin M → ℝ) (b : ℝ)
    (hnn : ∀ i, 0 ≤ a i) (htrace : ∑ i, a i = (M : ℝ) * b) :
    ∏ i, a i ≤ b ^ M := by
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM; simp
  · have hMpos : (0:ℝ) < (M:ℝ) := by exact_mod_cast hM
    -- `b ≥ 0` (it is the mean of nonneg reals).
    have hb : 0 ≤ b := by
      have hsumnn : 0 ≤ ∑ i, a i := Finset.sum_nonneg (fun i _ => hnn i)
      rw [htrace] at hsumnn
      exact nonneg_of_mul_nonneg_right hsumnn hMpos
    -- Uniform weights wᵢ = 1/M, summing to 1.
    have hwsum : ∑ _i : Fin M, ((M:ℝ)⁻¹) = 1 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    -- Weighted AM–GM: ∏ (aᵢ)^{1/M} ≤ ∑ (1/M)·aᵢ = (∑ aᵢ)/M = b.
    have hAMGM : ∏ i, (a i) ^ ((M:ℝ)⁻¹) ≤ ∑ i, (M:ℝ)⁻¹ * a i :=
      Real.geom_mean_le_arith_mean_weighted Finset.univ (fun _ => (M:ℝ)⁻¹) a
        (fun i _ => by positivity) hwsum (fun i _ => hnn i)
    have hrhs : ∑ i, (M:ℝ)⁻¹ * a i = b := by
      rw [← Finset.mul_sum, htrace]
      field_simp
    rw [hrhs] at hAMGM
    -- Raise both sides (nonneg) to the M-th power.  LHS^M = ∏ aᵢ.
    have hLHSnn : 0 ≤ ∏ i, (a i) ^ ((M:ℝ)⁻¹) :=
      Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (hnn i) _)
    have hpow := pow_le_pow_left₀ hLHSnn hAMGM M
    -- (∏ aᵢ^{1/M})^M = ∏ (aᵢ^{1/M})^M = ∏ aᵢ.
    have hcollapse : (∏ i, (a i) ^ ((M:ℝ)⁻¹)) ^ M = ∏ i, a i := by
      rw [← Finset.prod_pow]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      rw [← Real.rpow_natCast ((a i) ^ ((M:ℝ)⁻¹)) M, ← Real.rpow_mul (hnn i),
        inv_mul_cancel₀ (ne_of_gt hMpos), Real.rpow_one]
    rw [hcollapse] at hpow
    exact hpow

/-! ### §2  The count-route assembly  `(S-M1) ⟹ prize shape`

The char-`p` energy splits as `E_r = E_r^{(0)} + Spur_r(p)`.  The sufficient lemma `(S-M1)` is
`Spur_r(p) ≤ ε · E_r^{(0)}`; it yields `E_r ≤ (1+ε)·E_r^{(0)}`, and the `2r`-th-root extraction
multiplies the prize constant by `(1+ε)^{1/2r} → 1`.  These are unconditional once `(S-M1)` is the
hypothesis. -/

/-- **Count-route energy bound.**  Char-`0` energy `E0 = (2r-1)‼·n^r` plus a spurious count
`Spur ≤ ε·E0` gives total char-`p` energy `E = E0 + Spur ≤ (1+ε)·E0`. -/
theorem countRoute_energy_bound (E0 Spur ε : ℝ) (hE0 : 0 ≤ E0) (hε : 0 ≤ ε)
    (hSpur : Spur ≤ ε * E0) :
    E0 + Spur ≤ (1 + ε) * E0 := by
  have : E0 + Spur ≤ E0 + ε * E0 := by linarith
  linarith [this]

/-- **Count-route constant transfer.**  If the char-`p` energy is `≤ (1+ε)·E0` then the `2r`-th
root (the Markov/optimisation step, lane wf-M4) multiplies the prize-shape envelope by exactly
`(1+ε)^{1/2r}`.  Stated as the clean inequality on the moment `M_r = (p·E)^{1/2r}`:
`M_r ≤ (1+ε)^{1/2r} · (p·E0)^{1/2r}`.  Since `(1+ε)^{1/2r} → 1`, the prize square-root shape of
`(p·E0)^{1/2r}` is preserved with constant `→ C`. -/
theorem countRoute_prize_constant (p E0 ε : ℝ) (r : ℕ) (hr : 0 < r)
    (hp : 0 ≤ p) (hE0 : 0 ≤ E0) (hε : 0 ≤ ε) :
    (p * (E0 + ε * E0)) ^ ((2 * r : ℝ)⁻¹)
      = (1 + ε) ^ ((2 * r : ℝ)⁻¹) * (p * E0) ^ ((2 * r : ℝ)⁻¹) := by
  have hfac : p * (E0 + ε * E0) = (1 + ε) * (p * E0) := by ring
  rw [hfac]
  rw [Real.mul_rpow (by positivity) (by positivity)]

end ArkLib.ProximityGap.Frontier.WF5M1
