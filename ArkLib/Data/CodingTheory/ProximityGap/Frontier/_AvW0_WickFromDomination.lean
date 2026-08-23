/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# Char-0 Wick bound `E_r ≤ (2r−1)‼ · nʳ` from coefficientwise Bessel domination (#444, avenue W0)

This file formalizes **Steps 2–3** of the char-0 Wick proof path for thin `2`-power subgroups
`μ_n` (`n = 2^μ`, `m := n/2`), discharging — **axiom-clean** — the named hypothesis `hOff` of
`_AvGER_RecursionStep` (equivalently the Gaussian recursion `E_{r+1} ≤ (2r+1) n E_r`) **given**
the Bessel identity

  `E_r^{char0}(μ_n) = (2r)! · [x^{2r}] I₀(2x)^{m}`,   `I₀(2x) = Σ_k x^{2k}/(k!)²`,  `m = n/2`.

That identity (Step 1, the antipodal-balance decoupling via the in-tree Lam–Leung `2`-power
theorem) is carried here as the explicit hypothesis `hIdentity` and is verified EXACTLY off-line
(n=8, n=16, to high `r`, against the direct root-of-unity count). The content proved here is:

## Step 2 — coefficientwise domination (`besselCoeff_le_expSqCoeff`, `coeff_pow_mono`)
`[x^{2k}] I₀(2x) = 1/(k!)² ≤ 1/k! = [x^{2k}] e^{x²}` (since `1 ≤ k!`), and coefficientwise
domination of non-negative-coefficient (even) power series is preserved under the Cauchy product
(`coeff_mul_mono`), hence under the `m`-th power: `I₀(2x)^m ⪯ (e^{x²})^m = e^{(n/2)x²}`.

## Step 3 — conclusion (`wick_bound_of_identity`)
`[x^{2r}] e^{(n/2)x²} = (n/2)^r / r!`, so
`E_r ≤ (2r)! · (n/2)^r / r! = (2r)!/(2^r r!) · n^r = (2r−1)‼ · n^r`,  sharp `K = 1`, `r`-uniform.

Everything is over `ℚ` with explicit finite convolutions — no analytic Bessel function, no
probability, no floats. The coefficient of `x^{2k}` is carried directly as the rational `1/(k!)²`
(resp. `1/k!`).

## Honest scope (#444)
This is the **char-0 layer only**. It does NOT close the for-all-`q` prize: the char-`p`
energy-excess `W_r` wall (the wraparound term that breaks the antipodal decoupling at finite `p`)
remains entirely open. Here the identity `hIdentity` is an explicit hypothesis (discharged in the
companion identity task / `_AvGER_BesselEGFDeficit`), and only Steps 2–3 are formalized.
-/

namespace ArkLib.ProximityGap.Frontier.AvW0

open Finset BigOperators

/-! ## Even-index coefficient sequences (coefficient of `x^{2k}` carried at index `k`) -/

/-- Coefficient of `x^{2k}` in `I₀(2x) = Σ_k x^{2k}/(k!)²`: the rational `1/(k!)²`. -/
def besselCoeff (k : ℕ) : ℚ := 1 / ((k.factorial : ℚ) ^ 2)

/-- Coefficient of `x^{2k}` in `e^{x²} = Σ_k x^{2k}/k!`: the rational `1/k!`. -/
def expSqCoeff (k : ℕ) : ℚ := 1 / (k.factorial : ℚ)

/-- Even-index Cauchy product (the coefficient of `x^{2k}` in a product of two even series):
`(a ⋆ b) k = Σ_{i ≤ k} a i · b (k − i)`. -/
def conv (a b : ℕ → ℚ) (k : ℕ) : ℚ := ∑ i ∈ range (k + 1), a i * b (k - i)

/-- The even-index coefficient sequence of the `m`-th power of an even series. -/
def convPow (a : ℕ → ℚ) : ℕ → (ℕ → ℚ)
  | 0 => fun k => if k = 0 then 1 else 0
  | (m + 1) => fun k => conv (convPow a m) a k

/-! ## Step 2a — the per-coefficient domination `1/(k!)² ≤ 1/k!` -/

lemma besselCoeff_nonneg (k : ℕ) : 0 ≤ besselCoeff k := by
  unfold besselCoeff
  positivity

lemma expSqCoeff_nonneg (k : ℕ) : 0 ≤ expSqCoeff k := by
  unfold expSqCoeff
  positivity

/-- **Step 2a.** `[x^{2k}] I₀(2x) = 1/(k!)² ≤ 1/k! = [x^{2k}] e^{x²}`, because `(k!)² ≥ k!`
(equivalently `1 ≤ k!`). -/
lemma besselCoeff_le_expSqCoeff (k : ℕ) : besselCoeff k ≤ expSqCoeff k := by
  unfold besselCoeff expSqCoeff
  have hk1 : (1 : ℚ) ≤ (k.factorial : ℚ) := by
    have : 1 ≤ k.factorial := k.factorial_pos
    exact_mod_cast this
  have hkpos : (0 : ℚ) < (k.factorial : ℚ) := by exact_mod_cast k.factorial_pos
  -- 1/(k!)^2 ≤ 1/k!  since  k! ≤ (k!)^2
  apply one_div_le_one_div_of_le hkpos
  nlinarith [hk1, hkpos]

/-! ## Step 2b — domination preserved under convolution and powers -/

/-- Nonnegativity is preserved by `conv`. -/
lemma conv_nonneg {a b : ℕ → ℚ} (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k) (k : ℕ) :
    0 ≤ conv a b k := by
  unfold conv
  exact Finset.sum_nonneg fun i _ => mul_nonneg (ha i) (hb (k - i))

/-- **Step 2b (one product step).** If `a k ≤ b k` and `c k ≤ d k` coefficientwise with all four
sequences nonnegative, then `conv a c k ≤ conv b d k`. (Cauchy product is monotone in each
nonnegative argument.) -/
lemma conv_mono {a b c d : ℕ → ℚ}
    (hab : ∀ k, a k ≤ b k) (hcd : ∀ k, c k ≤ d k)
    (ha : ∀ k, 0 ≤ a k) (hc : ∀ k, 0 ≤ c k) (_hd : ∀ k, 0 ≤ d k) (k : ℕ) :
    conv a c k ≤ conv b d k := by
  unfold conv
  refine Finset.sum_le_sum ?_
  intro i _
  -- a i * c (k-i) ≤ b i * d (k-i)
  have h1 : a i * c (k - i) ≤ b i * c (k - i) :=
    mul_le_mul_of_nonneg_right (hab i) (hc (k - i))
  have h2 : b i * c (k - i) ≤ b i * d (k - i) :=
    mul_le_mul_of_nonneg_left (hcd (k - i)) (le_trans (ha i) (hab i))
  exact le_trans h1 h2

/-- Nonnegativity of every coefficient of `convPow a m` when `a` is nonnegative. -/
lemma convPow_nonneg {a : ℕ → ℚ} (ha : ∀ k, 0 ≤ a k) (m k : ℕ) : 0 ≤ convPow a m k := by
  induction m generalizing k with
  | zero =>
    unfold convPow
    split <;> norm_num
  | succ m ih =>
    unfold convPow
    exact conv_nonneg ih ha k

/-- **Step 2b (full power).** Coefficientwise domination of nonnegative even series is preserved
under the `m`-th convolution power: if `a k ≤ b k` (both nonnegative) for all `k`, then
`convPow a m k ≤ convPow b m k` for all `k, m`. -/
lemma convPow_mono {a b : ℕ → ℚ}
    (hab : ∀ k, a k ≤ b k) (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k) (m : ℕ) :
    ∀ k, convPow a m k ≤ convPow b m k := by
  induction m with
  | zero =>
    intro k
    unfold convPow
    split <;> norm_num
  | succ m ih =>
    intro k
    unfold convPow
    exact conv_mono ih hab (convPow_nonneg ha m) ha hb k

/-! ## Step 3 — the closed form of `[x^{2r}] e^{(n/2)x²}` and the conclusion

`e^{(n/2)x²} = (e^{x²})^{m}` (m = n/2), and its `x^{2r}` coefficient is `m^r / r!`.  We prove the
closed form `convPow expSqCoeff m r = m^r / r!` by the multinomial/EGF identity. The slick route:
`convPow expSqCoeff m` is the even-coefficient sequence of `(Σ x^{2k}/k!)^m = e^{m x²}`, whose
`x^{2r}` coefficient is `m^r/r!`. We prove it by induction on `m` using the Vandermonde/EGF
convolution `Σ_{i≤r} (m^i/i!)·(1/(r−i)!) = (m+1)^r/r!`. -/

/-- The EGF convolution identity `Σ_{i≤r} (mⁱ/i!)·(1/(r−i)!) = (m+1)ʳ/r!`, i.e. the `x^{2r}`
coefficient of `e^{m x²}·e^{x²} = e^{(m+1)x²}`. Proved from the binomial theorem `(m+1)^r =
Σ_i C(r,i) m^i`. -/
lemma convExpSq_step (m r : ℕ) :
    ∑ i ∈ range (r + 1), ((m : ℚ) ^ i / (i.factorial : ℚ)) * (1 / ((r - i).factorial : ℚ))
      = ((m : ℚ) + 1) ^ r / (r.factorial : ℚ) := by
  have hbin : ((m : ℚ) + 1) ^ r = ∑ i ∈ range (r + 1), (r.choose i : ℚ) * (m : ℚ) ^ i := by
    rw [add_pow]
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [one_pow, mul_one, mul_comm]
  rw [hbin, Finset.sum_div]
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [mem_range] at hi
  have hile : i ≤ r := Nat.lt_succ_iff.mp hi
  have hi' : (i.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
  have hri : ((r - i).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (r-i)
  have hr : (r.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
  -- r.choose i * (i! * (r-i)!) = r!
  have hchoose : (r.choose i : ℚ) * ((i.factorial : ℚ) * ((r - i).factorial : ℚ))
      = (r.factorial : ℚ) := by
    have h0 := Nat.choose_mul_factorial_mul_factorial hile
    have : ((r.choose i * i.factorial * (r - i).factorial : ℕ) : ℚ) = (r.factorial : ℚ) := by
      exact_mod_cast h0
    push_cast at this
    linarith [this]
  -- per term: (m^i/i!)*(1/(r-i)!) = (choose r i * m^i)/r!
  rw [div_mul_div_comm, mul_one]
  rw [div_eq_div_iff (mul_ne_zero hi' hri) hr]
  -- goal (some assoc/comm of): m^i * r! = choose r i * m^i * (i! * (r-i)!)
  linear_combination (m : ℚ) ^ i * hchoose.symm

/-- **Step 3 (closed form).** `[x^{2r}] (e^{x²})^m = m^r / r!`. -/
lemma convPow_expSq (m r : ℕ) :
    convPow expSqCoeff m r = (m : ℚ) ^ r / (r.factorial : ℚ) := by
  induction m generalizing r with
  | zero =>
    unfold convPow
    rcases Nat.eq_zero_or_pos r with hr | hr
    · subst hr; norm_num
    · rw [if_neg (by omega)]
      rw [Nat.cast_zero, zero_pow (by omega : r ≠ 0), zero_div]
  | succ m ih =>
    unfold convPow conv
    -- convPow expSq (m+1) r = Σ_{i≤r} convPow expSq m i * expSqCoeff (r-i)
    -- = Σ_{i≤r} (m^i/i!) * (1/(r-i)!) = (m+1)^r/r!
    rw [Finset.sum_congr rfl (g := fun i => ((m : ℚ) ^ i / (i.factorial : ℚ)) *
          (1 / (((r - i)).factorial : ℚ))) (fun i _ => by rw [ih]; rfl)]
    rw [convExpSq_step m r]
    push_cast
    ring

/-! ## Step 2 (combined) — `[x^{2r}] I₀(2x)^m ≤ [x^{2r}] e^{(n/2)x²} = m^r/r!` -/

/-- **Step 2 conclusion.** The `x^{2r}` coefficient of `I₀(2x)^m` is dominated by that of
`(e^{x²})^m`, which equals `m^r/r!`. -/
lemma convPow_bessel_le (m r : ℕ) :
    convPow besselCoeff m r ≤ (m : ℚ) ^ r / (r.factorial : ℚ) := by
  rw [← convPow_expSq m r]
  exact convPow_mono besselCoeff_le_expSqCoeff besselCoeff_nonneg expSqCoeff_nonneg m r

/-! ## Step 3 — the double-factorial arithmetic and the final Wick bound -/

/-- The arithmetic identity tying the EGF coefficient to the sharp Wick constant:
`(2r)! · (n/2)^r / r! = (2r−1)‼ · n^r`, equivalently (clearing `2^r`)
`(2r)! · n^r = (2r−1)‼ · n^r · 2^r · r! = (2r)! · n^r` via `(2r−1)‼ · 2^r · r! = (2r)!`. We use the
Mathlib identity `(2r)! = (2r−1)‼ · (2 r)‼` and `(2r)‼ = 2^r · r!`. -/
lemma wick_const_eq (n r : ℕ) (hn : Even n) :
    ((2 * r).factorial : ℚ) * ((n / 2 : ℕ) : ℚ) ^ r / (r.factorial : ℚ)
      = ((2 * r - 1).doubleFactorial : ℚ) * (n : ℚ) ^ r := by
  obtain ⟨m, rfl⟩ := hn
  have hm : (m + m) / 2 = m := by omega
  rw [hm]
  -- Reduce to the ℕ identity (2r)! * m^r = (2r-1)‼ * (m+m)^r * r!  ... but cleaner: prove
  -- (2r)! * (m^r) = (2r-1)‼ * (2m)^r * r!  via (2r)! = (2r)‼ * (2r-1)‼, (2r)‼ = 2^r r!.
  rcases Nat.eq_zero_or_pos r with hr0 | hrpos
  · subst hr0; simp
  -- r ≥ 1: 2r = (2r-1)+1
  have hsucc : 2 * r = (2 * r - 1) + 1 := by omega
  -- (2r)! = (2r)‼ * (2r-1)‼
  have hfac : (2 * r).factorial = (2 * r).doubleFactorial * (2 * r - 1).doubleFactorial := by
    conv_lhs => rw [hsucc]
    rw [Nat.factorial_eq_mul_doubleFactorial]
    congr 2
    omega
  -- (2r)‼ = 2^r * r!
  have hdd : (2 * r).doubleFactorial = 2 ^ r * r.factorial := Nat.doubleFactorial_two_mul r
  -- Now in ℚ.
  have hr : (r.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
  rw [div_eq_iff hr]
  -- (2r)! * m^r = (2r-1)‼ * (m+m)^r * r!
  have key : ((2 * r).factorial : ℚ) * (m : ℚ) ^ r
      = ((2 * r - 1).doubleFactorial : ℚ) * ((m + m : ℕ) : ℚ) ^ r * (r.factorial : ℚ) := by
    have hfacQ : ((2 * r).factorial : ℚ)
        = (2 : ℚ) ^ r * (r.factorial : ℚ) * ((2 * r - 1).doubleFactorial : ℚ) := by
      rw [hfac, hdd]; push_cast; ring
    rw [hfacQ]
    have : ((m + m : ℕ) : ℚ) = 2 * (m : ℚ) := by push_cast; ring
    rw [this, mul_pow]
    ring
  rw [key]

/-- **THE CHAR-0 WICK BOUND (Steps 2–3), conditional on the Bessel identity (Step 1).**
Given the identity `E_r = (2r)! · [x^{2r}] I₀(2x)^{m}` (`m = n/2`, the antipodal-balance decoupling),
the sharp `K = 1`, `r`-uniform Wick bound holds:
`E_r ≤ (2r−1)‼ · n^r`.

`Er : ℕ` is the char-0 additive energy `E_r^{char0}(μ_n)`; `hIdentity` is the Bessel identity. -/
theorem wick_bound_of_identity (n r : ℕ) (hn : Even n) (Er : ℕ)
    (hIdentity : (Er : ℚ) = ((2 * r).factorial : ℚ) * convPow besselCoeff (n / 2) r) :
    (Er : ℚ) ≤ ((2 * r - 1).doubleFactorial : ℚ) * (n : ℚ) ^ r := by
  rw [hIdentity]
  rw [← wick_const_eq n r hn]
  rw [mul_div_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [← convPow_expSq (n / 2) r]
  exact convPow_mono besselCoeff_le_expSqCoeff besselCoeff_nonneg expSqCoeff_nonneg (n / 2) r

end ArkLib.ProximityGap.Frontier.AvW0

/-! ## Axiom audit (expected: only `propext, Classical.choice, Quot.sound`; no `sorryAx`) -/
#print axioms ArkLib.ProximityGap.Frontier.AvW0.besselCoeff_le_expSqCoeff
#print axioms ArkLib.ProximityGap.Frontier.AvW0.convPow_mono
#print axioms ArkLib.ProximityGap.Frontier.AvW0.convPow_expSq
#print axioms ArkLib.ProximityGap.Frontier.AvW0.convPow_bessel_le
#print axioms ArkLib.ProximityGap.Frontier.AvW0.wick_const_eq
#print axioms ArkLib.ProximityGap.Frontier.AvW0.wick_bound_of_identity
