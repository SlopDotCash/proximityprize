/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumMomentLadder

/-!
# The discrete arcsine moment — `∑_{k<N} (ζ^k + ζ^{-k})^{2r} = N · C(2r, r)`  (#466, round 25)

The δ* prize's moment route studies the even moments of the Gauss period
`η_b = ∑_{x∈μ_n} ψ(bx)`. Because the dyadic subgroup is closed under negation, `η_b` is real and
its terms are of the form `2cos θ = ζ^k + ζ^{-k}`. The sub-Wick phenomenon (moments strictly below
the Gaussian/Wick value, so the "floor" is true) is governed by the negative excess kurtosis of the
discrete arcsine law: the `2r`-th moment of the discrete cosine over an `N`-point grid equals the
central binomial `C(2r, r)`.

This file proves that exact underlying arithmetic identity, rigorously and prize-independently:

> **`sum_cos_pow_eq`** : for `ζ` a primitive `N`-th root of unity in `ℂ` and `N > 2r`,
> `∑_{k=0}^{N-1} (ζ^k + (ζ^k)⁻¹)^{2r} = N · (2r).choose r`.

Mechanism: `(ζ^k)⁻¹ = (ζ^{N-1})^k`; the binomial theorem gives `∑_j C(2r,j) (ζ^{m_j})^k` with
`m_j = j + (N-1)(2r-j)`; and `ζ^{m_j} = ζ^j·(ζ^{2r-j})⁻¹ = 1 ↔ j = 2r-j ↔ j = r` (primitive root
injective on exponents `< N`). Summing over `k` kills every `j ≠ r` (geometric sum of a nontrivial
root of unity), leaving `C(2r,r)` at each of the `N` points.
-/

set_option autoImplicit false

open Finset

namespace ArkLib.ProximityGap.Frontier.R25DiscreteArcsineMoment

/-- Geometric sum of a nontrivial `N`-th root of unity vanishes. -/
theorem geom_sum_root_eq_zero {N : ℕ} {w : ℂ} (hwN : w ^ N = 1) (hw : w ≠ 1) :
    ∑ k ∈ range N, w ^ k = 0 := by
  have hkey : (∑ k ∈ range N, w ^ k) * (w - 1) = w ^ N - 1 := geom_sum_mul w N
  rw [hwN, sub_self] at hkey
  rcases mul_eq_zero.mp hkey with h | h
  · exact h
  · exact absurd (sub_eq_zero.mp h) hw

/-- For an `N`-th root of unity (`N ≥ 1`), `(ζ^k)⁻¹ = (ζ^{N-1})^k`. -/
theorem inv_pow_eq {N : ℕ} (hN : 1 ≤ N) {ζ : ℂ} (hζN : ζ ^ N = 1) (k : ℕ) :
    (ζ ^ k)⁻¹ = (ζ ^ (N - 1)) ^ k := by
  have hexp : k + (N - 1) * k = N * k := by
    cases N with
    | zero => omega
    | succ m => simp only [Nat.succ_sub_one]; ring
  have hmul : ζ ^ k * (ζ ^ (N - 1)) ^ k = 1 := by
    rw [← pow_mul, ← pow_add, hexp, pow_mul, hζN, one_pow]
  exact inv_eq_of_mul_eq_one_right hmul

/-- The exponent `m_j = j + (N-1)(2r-j)`. -/
private def mExp (N r j : ℕ) : ℕ := j + (N - 1) * (2 * r - j)

/-- `ζ^{m_j} = ζ^j · (ζ^{2r-j})⁻¹` for an `N`-th root of unity. -/
private theorem zeta_mExp_eq {N r j : ℕ} (hN : 1 ≤ N) {ζ : ℂ} (hζN : ζ ^ N = 1) :
    ζ ^ mExp N r j = ζ ^ j * (ζ ^ (2 * r - j))⁻¹ := by
  have hinv : ζ ^ (N - 1) = ζ⁻¹ := by
    have := inv_pow_eq hN hζN 1
    simpa using this.symm
  unfold mExp
  rw [pow_add, pow_mul, hinv, inv_pow]

/-- `ζ^{m_j} = 1 ↔ j = r`, for `j ≤ 2r < N` and `ζ` primitive. -/
private theorem zeta_mExp_eq_one_iff {N r j : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N)
    (hjle : j ≤ 2 * r) (hr : 2 * r < N) : ζ ^ mExp N r j = 1 ↔ j = r := by
  have hN : 1 ≤ N := by omega
  have hζN : ζ ^ N = 1 := hζ.pow_eq_one
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by omega)
  have hb0 : ζ ^ (2 * r - j) ≠ 0 := pow_ne_zero _ hζ0
  rw [zeta_mExp_eq hN hζN]
  rw [← div_eq_mul_inv, div_eq_one_iff_eq hb0]
  constructor
  · intro h
    have := hζ.pow_inj (show j < N by omega) (show 2 * r - j < N by omega) h
    omega
  · intro h; subst h
    congr 1; omega

/-- **The discrete arcsine moment.** For `ζ` a primitive `N`-th root of unity and `N > 2r`,
`∑_{k<N} (ζ^k + (ζ^k)⁻¹)^{2r} = N · C(2r, r)`. -/
theorem sum_cos_pow_eq {N r : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N) (hr : 2 * r < N) :
    ∑ k ∈ range N, (ζ ^ k + (ζ ^ k)⁻¹) ^ (2 * r) = (N : ℂ) * ((2 * r).choose r) := by
  have hN : 1 ≤ N := by omega
  have hζN : ζ ^ N = 1 := hζ.pow_eq_one
  have hterm : ∀ k, (ζ ^ k + (ζ ^ k)⁻¹) ^ (2 * r)
      = ∑ j ∈ range (2 * r + 1), ((2 * r).choose j : ℂ) * (ζ ^ mExp N r j) ^ k := by
    intro k
    rw [inv_pow_eq hN hζN k, add_pow]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hcombine : (ζ ^ k) ^ j * ((ζ ^ (N - 1)) ^ k) ^ (2 * r - j) = (ζ ^ mExp N r j) ^ k := by
      simp only [← pow_mul, ← pow_add]
      congr 1
      unfold mExp; ring
    rw [hcombine]; ring
  rw [Finset.sum_congr rfl (fun k _ => hterm k), Finset.sum_comm]
  have hinner : ∀ j ∈ range (2 * r + 1),
      ∑ k ∈ range N, ((2 * r).choose j : ℂ) * (ζ ^ mExp N r j) ^ k
        = if j = r then (N : ℂ) * ((2 * r).choose r) else 0 := by
    intro j hj
    have hjle : j ≤ 2 * r := by simpa [Nat.lt_succ_iff] using hj
    rw [← Finset.mul_sum]
    by_cases hjr : j = r
    · rw [if_pos hjr, hjr]
      have h1 : ζ ^ mExp N r r = 1 := (zeta_mExp_eq_one_iff hζ (by omega) hr).mpr rfl
      simp only [h1, one_pow, Finset.sum_const, card_range, nsmul_eq_mul, mul_one]
      ring
    · have hne : ζ ^ mExp N r j ≠ 1 := fun h => hjr ((zeta_mExp_eq_one_iff hζ hjle hr).mp h)
      have hwN : (ζ ^ mExp N r j) ^ N = 1 := by
        rw [← pow_mul, mul_comm, pow_mul, hζN, one_pow]
      rw [geom_sum_root_eq_zero hwN hne, mul_zero, if_neg hjr]
  rw [Finset.sum_congr rfl hinner]
  rw [Finset.sum_eq_single r
    (fun b _ hbr => if_neg hbr)
    (fun h => absurd (Finset.mem_range.mpr (show r < 2 * r + 1 by omega)) h)]
  rw [if_pos rfl]

/-- **The shifted / autocorrelation arcsine moment.** For `ζ` primitive `N`-th, `s ≤ r`, and
`2r + 2s < N`, twisting the `2r`-th cosine power by `(ζ^k)^{2s}` extracts the off-diagonal central
binomial: `∑_{k<N} (ζ^k + (ζ^k)⁻¹)^{2r} · (ζ^k)^{2s} = N · C(2r, r-s)`. This is the building block
for the convolution / additive-energy structure of `η_b`: the `s`-shift Fourier coefficient of the
`2r`-th power is `C(2r, r-s)`. (Recovers `sum_cos_pow_eq` at `s = 0`.) -/
theorem sum_cos_pow_mul_shift_eq {N r s : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N)
    (hsr : s ≤ r) (hN2 : 2 * r + 2 * s < N) :
    ∑ k ∈ range N, (ζ ^ k + (ζ ^ k)⁻¹) ^ (2 * r) * (ζ ^ k) ^ (2 * s)
      = (N : ℂ) * ((2 * r).choose (r - s)) := by
  have hN : 1 ≤ N := by omega
  have hζN : ζ ^ N = 1 := hζ.pow_eq_one
  have hiff : ∀ j, j ≤ 2 * r → (ζ ^ (mExp N r j + 2 * s) = 1 ↔ j = r - s) := by
    intro j hjle
    have hζ0 : ζ ≠ 0 := hζ.ne_zero (by omega)
    have hb0 : ζ ^ (2 * r - j) ≠ 0 := pow_ne_zero _ hζ0
    rw [pow_add, zeta_mExp_eq hN hζN]
    rw [show ζ ^ j * (ζ ^ (2 * r - j))⁻¹ * ζ ^ (2 * s)
          = ζ ^ (j + 2 * s) * (ζ ^ (2 * r - j))⁻¹ by rw [pow_add]; ring]
    rw [← div_eq_mul_inv, div_eq_one_iff_eq hb0]
    constructor
    · intro h
      have := hζ.pow_inj (show j + 2 * s < N by omega) (show 2 * r - j < N by omega) h
      omega
    · intro h; subst h
      congr 1; omega
  have hterm : ∀ k, (ζ ^ k + (ζ ^ k)⁻¹) ^ (2 * r) * (ζ ^ k) ^ (2 * s)
      = ∑ j ∈ range (2 * r + 1), ((2 * r).choose j : ℂ) * (ζ ^ (mExp N r j + 2 * s)) ^ k := by
    intro k
    rw [inv_pow_eq hN hζN k, add_pow, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hcombine : (ζ ^ k) ^ j * ((ζ ^ (N - 1)) ^ k) ^ (2 * r - j) = (ζ ^ mExp N r j) ^ k := by
      simp only [← pow_mul, ← pow_add]; congr 1; unfold mExp; ring
    have hshift : ((ζ : ℂ) ^ (2 * s)) ^ k = (ζ ^ k) ^ (2 * s) := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    rw [pow_add, mul_pow, hcombine, ← hshift]; ring
  rw [Finset.sum_congr rfl (fun k _ => hterm k), Finset.sum_comm]
  have hinner : ∀ j ∈ range (2 * r + 1),
      ∑ k ∈ range N, ((2 * r).choose j : ℂ) * (ζ ^ (mExp N r j + 2 * s)) ^ k
        = if j = r - s then (N : ℂ) * ((2 * r).choose (r - s)) else 0 := by
    intro j hj
    have hjle : j ≤ 2 * r := by simpa [Nat.lt_succ_iff] using hj
    rw [← Finset.mul_sum]
    by_cases hjr : j = r - s
    · rw [if_pos hjr, hjr]
      have h1 : ζ ^ (mExp N r (r - s) + 2 * s) = 1 := (hiff (r - s) (by omega)).mpr rfl
      simp only [h1, one_pow, Finset.sum_const, card_range, nsmul_eq_mul, mul_one]
      ring
    · have hne : ζ ^ (mExp N r j + 2 * s) ≠ 1 := fun h => hjr ((hiff j hjle).mp h)
      have hwN : (ζ ^ (mExp N r j + 2 * s)) ^ N = 1 := by
        rw [← pow_mul, mul_comm, pow_mul, hζN, one_pow]
      rw [geom_sum_root_eq_zero hwN hne, mul_zero, if_neg hjr]
  rw [Finset.sum_congr rfl hinner]
  rw [Finset.sum_eq_single (r - s)
    (fun b _ hbr => if_neg hbr)
    (fun h => absurd (Finset.mem_range.mpr (show r - s < 2 * r + 1 by omega)) h)]
  rw [if_pos rfl]

/-- **Second-moment (r = 1):** `∑_{k<N} (ζ^k + (ζ^k)⁻¹)² = 2N`. The variance scale `σ² = 2` per
term underlying the arcsine law (`C(2,1) = 2`). -/
theorem sum_cos_sq_eq {N : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N) (hr : 2 < N) :
    ∑ k ∈ range N, (ζ ^ k + (ζ ^ k)⁻¹) ^ 2 = 2 * (N : ℂ) := by
  have h := sum_cos_pow_eq (r := 1) hζ (by omega)
  norm_num [Nat.choose] at h
  linear_combination h

/-- **Fourth-moment (r = 2):** `∑_{k<N} (ζ^k + (ζ^k)⁻¹)⁴ = 6N`. Central binomial `C(4,2) = 6`,
the additive-energy-relevant moment. Sub-Wick: `6 < 3·2² = 12` (the Gaussian value for variance
`2`), i.e. the excess kurtosis `κ₄ = 6 − 12 = −6 < 0` that makes the subgroup floor true. -/
theorem sum_cos_pow_four_eq {N : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N) (hr : 4 < N) :
    ∑ k ∈ range N, (ζ ^ k + (ζ ^ k)⁻¹) ^ 4 = 6 * (N : ℂ) := by
  have h := sum_cos_pow_eq (r := 2) hζ (by omega)
  norm_num [Nat.choose] at h
  linear_combination h

/-! ## The exact sub-Wick suppression factor

The discrete cosine's `2r`-th moment is the central binomial `C(2r, r)`; the Gaussian/Wick moment
for the matching variance `σ² = 2` is `(2r-1)‼ · 2^r`. Their exact ratio is `1/r!`: the single
bounded (platykurtic) term is `r!`-fold below Gaussian, which is the arithmetic origin of the
floor being true. -/

/-- **Sub-Wick suppression identity:** `C(2r, r) · r! = 2^r · (2r-1)‼`, i.e. the arcsine moment
`C(2r,r)` equals `(2r-1)‼·2^r / r!` — exactly `1/r!` of the Gaussian 2r-th moment of variance 2. -/
theorem centralBinom_mul_factorial_eq {r : ℕ} :
    (2 * r).choose r * Nat.factorial r = 2 ^ r * Nat.doubleFactorial (2 * r - 1) := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr; rfl
  -- (2r).choose r * r! * r! = (2r)!
  have hchoose : (2 * r).choose r * Nat.factorial r * Nat.factorial r = Nat.factorial (2 * r) := by
    have h := Nat.choose_mul_factorial_mul_factorial (show r ≤ 2 * r by omega)
    rwa [show 2 * r - r = r by omega] at h
  -- (2r)! = (2r)‼ * (2r-1)‼ = (2^r * r!) * (2r-1)‼
  have hsplit : Nat.factorial (2 * r)
      = 2 ^ r * Nat.doubleFactorial (2 * r - 1) * Nat.factorial r := by
    have hfac : Nat.factorial (2 * r)
        = Nat.doubleFactorial (2 * r) * Nat.doubleFactorial (2 * r - 1) := by
      have := Nat.factorial_eq_mul_doubleFactorial (2 * r - 1)
      rwa [show 2 * r - 1 + 1 = 2 * r by omega] at this
    rw [hfac, Nat.doubleFactorial_two_mul]
    ring
  -- cancel one r!
  have hcancel : (2 * r).choose r * Nat.factorial r * Nat.factorial r
      = 2 ^ r * Nat.doubleFactorial (2 * r - 1) * Nat.factorial r := by
    rw [hchoose, hsplit]
  exact Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos r) hcancel

/-- **Sub-Wick inequality (consumer form):** the arcsine `2r`-th moment `C(2r, r)` is at most the
Gaussian/Wick moment `2^r · (2r-1)‼`, with equality only for `r ≤ 1`. This is the exact sense in
which the bounded (platykurtic) cosine terms suppress the even moments below Gaussian — the
arithmetic root of the δ* floor. -/
theorem centralBinom_le_wick {r : ℕ} :
    (2 * r).choose r ≤ 2 ^ r * Nat.doubleFactorial (2 * r - 1) := by
  calc (2 * r).choose r
      ≤ (2 * r).choose r * Nat.factorial r :=
        Nat.le_mul_of_pos_right _ (Nat.factorial_pos r)
    _ = 2 ^ r * Nat.doubleFactorial (2 * r - 1) := centralBinom_mul_factorial_eq

/-! ## The moment → sup reduction (the engine that makes moment bounds useful)

Every use of the moment method for the δ* object rests on one elementary fact: a single term of a
sum of nonnegatives is bounded by the whole sum. Applied to `‖η_b‖^{2r}`, it converts a bound on
the `2r`-th moment `∑_{b∈s} ‖η_b‖^{2r}` into a worst-case bound `max_b ‖η_b‖`. -/

/-- **Moment → sup:** for any `g : ι → ℂ`, `b₀ ∈ s`, `‖g b₀‖^n ≤ ∑_{b∈s} ‖g b‖^n`. Hence a moment
bound `∑_{b∈s} ‖g b‖^{2r} ≤ B` gives `‖g b₀‖ ≤ B^{1/(2r)}` for every `b₀ ∈ s` — the reduction the
whole moment route uses. -/
theorem norm_pow_le_sum_norm_pow {ι : Type*} (g : ι → ℂ) (s : Finset ι) {b₀ : ι}
    (hb₀ : b₀ ∈ s) (n : ℕ) : ‖g b₀‖ ^ n ≤ ∑ b ∈ s, ‖g b‖ ^ n :=
  Finset.single_le_sum (f := fun b => ‖g b‖ ^ n) (fun b _ => by positivity) hb₀

end ArkLib.ProximityGap.Frontier.R25DiscreteArcsineMoment

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.R25DiscreteArcsineMoment.sum_cos_pow_eq
#print axioms ArkLib.ProximityGap.Frontier.R25DiscreteArcsineMoment.sum_cos_pow_mul_shift_eq
#print axioms ArkLib.ProximityGap.Frontier.R25DiscreteArcsineMoment.sum_cos_pow_four_eq
#print axioms ArkLib.ProximityGap.Frontier.R25DiscreteArcsineMoment.centralBinom_mul_factorial_eq
#print axioms ArkLib.ProximityGap.Frontier.R25DiscreteArcsineMoment.norm_pow_le_sum_norm_pow
