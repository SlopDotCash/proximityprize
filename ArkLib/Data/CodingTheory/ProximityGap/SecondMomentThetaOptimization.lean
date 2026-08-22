/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
Round 15, Angle B: theta-optimization of the Chernoff second-moment shape.

The in-tree kernel `rs_sum_jointCoverCount_mgf_le` (CS25RSSecondMomentMGF.lean) gives, for every
θ ∈ [0,1],
    θ^(2r) * S ≤ (1+(q-1)θ²)^n + (q(2θ+(q-2)θ²) + (1+(q-1)θ²))^n / q^(n-k)
where S is the RS ball-intersection (second-moment) sum.  This file supplies the missing
downstream: the θ-optimization of that family of bounds, proved self-contained over ℝ
(only Mathlib imports; the kernel shape is restated abstractly as a hypothesis `hkernel`).

Contents:
* `model_bound_interior` — exact closed form of f(θ) = (a+bθ)^n / θ^(2r) at the interior
  critical point θ* = 2ra/(b(n-2r))  (the calculus optimum of the model shape).
* `model_bound_boundary` — value at the boundary θ = 1.
* `model_bound_min` — the combined choice θ = min(1, θ*) is bounded by the max of the two
  closed forms.
* `model_bound_entropy` — the entropy-form bound at θ = r/n:
  (a+b(r/n))^n / (r/n)^(2r) ≤ aⁿ · exp(br/a) · (n/r)^(2r), via 1+x ≤ exp x.
* `second_moment_opt_bound` — the optimized explicit bound: from the kernel hypothesis
  (the exact shape of the in-tree MGF kernel, with both θ²-terms), choosing θ = r/n,
      S ≤ (n/r)^(2r) · ( exp((q-1)r) + exp((q²+q-1)r) / q^(n-k) ).
* Non-vacuity: a concrete numeric instantiation at q = 17, n = 16, k = 2, r = 4 with a
  concrete witness S = 1 satisfying the kernel hypothesis (so the hypothesis is satisfiable
  and the chain runs end to end), plus a `norm_num` evaluation of the interior closed form.
-/

open Real

namespace ThetaOpt

/-! ### The model function f(θ) = (a + b·θ)^n / θ^(2r) -/

/-- **Interior closed form.** At the calculus critical point
`θ* = 2ra / (b(n-2r))` (valid for `2r < n`), the model function evaluates exactly to
`(a·n/(n-2r))^n · (b(n-2r)/(2ra))^(2r)`. -/
theorem model_bound_interior (a b : ℝ) (n r : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hnr : 2 * r < n) (hr : 0 < r) :
    (a + b * (2 * (r : ℝ) * a / (b * ((n : ℝ) - 2 * (r : ℝ))))) ^ n
        / (2 * (r : ℝ) * a / (b * ((n : ℝ) - 2 * (r : ℝ)))) ^ (2 * r)
      = (a * (n : ℝ) / ((n : ℝ) - 2 * (r : ℝ))) ^ n
        * (b * ((n : ℝ) - 2 * (r : ℝ)) / (2 * (r : ℝ) * a)) ^ (2 * r) := by
  have hm : (0 : ℝ) < (n : ℝ) - 2 * (r : ℝ) := by
    have : ((2 * r : ℕ) : ℝ) < (n : ℝ) := by exact_mod_cast hnr
    push_cast at this
    linarith
  have hr' : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have h1 : a + b * (2 * (r : ℝ) * a / (b * ((n : ℝ) - 2 * (r : ℝ))))
      = a * (n : ℝ) / ((n : ℝ) - 2 * (r : ℝ)) := by
    field_simp
    ring
  have h2 : 2 * (r : ℝ) * a / (b * ((n : ℝ) - 2 * (r : ℝ)))
      = (b * ((n : ℝ) - 2 * (r : ℝ)) / (2 * (r : ℝ) * a))⁻¹ := by
    rw [inv_div]
  rw [h1, h2, inv_pow, div_eq_mul_inv, inv_inv]

/-- **Boundary value.** At θ = 1 the model function is `(a+b)^n`. -/
theorem model_bound_boundary (a b : ℝ) (n r : ℕ) :
    (a + b * 1) ^ n / (1 : ℝ) ^ (2 * r) = (a + b) ^ n := by
  rw [mul_one, one_pow, div_one]

/-- **Combined optimization.** The choice `θ = min 1 (2ra/(b(n-2r)))` yields the explicit
closed-form bound: the max of the boundary value and the interior closed form. -/
theorem model_bound_min (a b : ℝ) (n r : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hnr : 2 * r < n) (hr : 0 < r) :
    (a + b * min 1 (2 * (r : ℝ) * a / (b * ((n : ℝ) - 2 * (r : ℝ))))) ^ n
        / (min 1 (2 * (r : ℝ) * a / (b * ((n : ℝ) - 2 * (r : ℝ))))) ^ (2 * r)
      ≤ max ((a + b) ^ n)
          ((a * (n : ℝ) / ((n : ℝ) - 2 * (r : ℝ))) ^ n
            * (b * ((n : ℝ) - 2 * (r : ℝ)) / (2 * (r : ℝ) * a)) ^ (2 * r)) := by
  rcases le_total (2 * (r : ℝ) * a / (b * ((n : ℝ) - 2 * (r : ℝ)))) 1 with h | h
  · rw [min_eq_right h, model_bound_interior a b n r ha hb hnr hr]
    exact le_max_right _ _
  · rw [min_eq_left h, model_bound_boundary a b n r]
    exact le_max_left _ _

/-- **Entropy-form bound.** At the entropy point `θ = r/n` (for `0 < r ≤ n`),
`(a + b·(r/n))^n / (r/n)^(2r) ≤ aⁿ · exp(br/a) · (n/r)^(2r)`, via `1 + x ≤ exp x`. -/
theorem model_bound_entropy (a b : ℝ) (n r : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hr : 0 < r) (hrn : r ≤ n) :
    (a + b * ((r : ℝ) / (n : ℝ))) ^ n / ((r : ℝ) / (n : ℝ)) ^ (2 * r)
      ≤ a ^ n * Real.exp (b * (r : ℝ) / a) * ((n : ℝ) / (r : ℝ)) ^ (2 * r) := by
  have hn : 0 < n := hr.trans_le hrn
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hr' : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  -- the rescaled variable x = br/(an) ≥ 0
  have hx0 : (0 : ℝ) ≤ b * (r : ℝ) / (a * (n : ℝ)) := by positivity
  -- factor out a
  have key1 : a + b * ((r : ℝ) / (n : ℝ)) = a * (1 + b * (r : ℝ) / (a * (n : ℝ))) := by
    field_simp
  -- rewrite the LHS as a^n * (1+x)^n * (n/r)^(2r)
  have key2 : (a + b * ((r : ℝ) / (n : ℝ))) ^ n / ((r : ℝ) / (n : ℝ)) ^ (2 * r)
      = a ^ n * (1 + b * (r : ℝ) / (a * (n : ℝ))) ^ n * ((n : ℝ) / (r : ℝ)) ^ (2 * r) := by
    rw [key1, mul_pow]
    rw [show (r : ℝ) / (n : ℝ) = ((n : ℝ) / (r : ℝ))⁻¹ by rw [inv_div]]
    rw [inv_pow, div_eq_mul_inv, inv_inv]
  -- (1+x)^n ≤ exp(nx) = exp(br/a)
  have hexp : (1 + b * (r : ℝ) / (a * (n : ℝ))) ^ n ≤ Real.exp (b * (r : ℝ) / a) := by
    have h1x : 1 + b * (r : ℝ) / (a * (n : ℝ))
        ≤ Real.exp (b * (r : ℝ) / (a * (n : ℝ))) := by
      have := Real.add_one_le_exp (b * (r : ℝ) / (a * (n : ℝ)))
      linarith
    calc (1 + b * (r : ℝ) / (a * (n : ℝ))) ^ n
        ≤ (Real.exp (b * (r : ℝ) / (a * (n : ℝ)))) ^ n :=
          pow_le_pow_left₀ (by linarith) h1x n
      _ = Real.exp ((n : ℝ) * (b * (r : ℝ) / (a * (n : ℝ)))) :=
          (Real.exp_nat_mul _ n).symm
      _ = Real.exp (b * (r : ℝ) / a) := by
          congr 1
          field_simp
  rw [key2]
  have hnr0 : (0 : ℝ) ≤ ((n : ℝ) / (r : ℝ)) ^ (2 * r) := by positivity
  have ha0 : (0 : ℝ) ≤ a ^ n := by positivity
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp ha0) hnr0

/-! ### The optimized second-moment bound

The kernel hypothesis `hkernel` restates (abstractly, over ℝ) the exact shape of the in-tree
MGF kernel: for all θ ∈ [0,1],
  θ^(2r) · S ≤ (1+(q-1)θ²)^n + (q(2θ+(q-2)θ²) + (1+(q-1)θ²))^n / q^(n-k).
Choosing θ = r/n and dominating θ² ≤ θ turns it into the explicit closed bound. -/

/-- **Optimized explicit second-moment bound.** Given the Chernoff kernel shape for all
θ ∈ [0,1], the choice θ = r/n yields
`S ≤ (n/r)^(2r) · (exp((q-1)r) + exp((q²+q-1)r)/q^(n-k))`. -/
theorem second_moment_opt_bound (q n k r : ℕ) (S : ℝ)
    (hq : 2 ≤ q) (hr : 0 < r) (hrn : r ≤ n)
    (hkernel : ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      θ ^ (2 * r) * S ≤
        (1 + ((q : ℝ) - 1) * θ ^ 2) ^ n
          + ((q : ℝ) * (2 * θ + ((q : ℝ) - 2) * θ ^ 2) + (1 + ((q : ℝ) - 1) * θ ^ 2)) ^ n
              / (q : ℝ) ^ (n - k)) :
    S ≤ ((n : ℝ) / (r : ℝ)) ^ (2 * r)
        * (Real.exp (((q : ℝ) - 1) * (r : ℝ))
            + Real.exp ((((q : ℝ) ^ 2 + (q : ℝ)) - 1) * (r : ℝ)) / (q : ℝ) ^ (n - k)) := by
  have hn : 0 < n := hr.trans_le hrn
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hr' : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hq' : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hθ0 : (0 : ℝ) < (r : ℝ) / (n : ℝ) := div_pos hr' hn'
  have hθ1 : (r : ℝ) / (n : ℝ) ≤ 1 := by
    rw [div_le_one hn']
    exact_mod_cast hrn
  have hθsq : ((r : ℝ) / (n : ℝ)) ^ 2 ≤ (r : ℝ) / (n : ℝ) := by nlinarith
  have hqpow : (0 : ℝ) < (q : ℝ) ^ (n - k) := pow_pos (by linarith) _
  have hθpow : (0 : ℝ) < ((r : ℝ) / (n : ℝ)) ^ (2 * r) := pow_pos hθ0 _
  -- abbreviate θ
  -- bound the A-term: (1+(q-1)θ²)^n ≤ (1+(q-1)θ)^n
  have hA : (1 + ((q : ℝ) - 1) * ((r : ℝ) / (n : ℝ)) ^ 2) ^ n
      ≤ (1 + ((q : ℝ) - 1) * ((r : ℝ) / (n : ℝ))) ^ n := by
    have h0 : (0 : ℝ) ≤ 1 + ((q : ℝ) - 1) * ((r : ℝ) / (n : ℝ)) ^ 2 := by
      have : (0 : ℝ) ≤ ((q : ℝ) - 1) * ((r : ℝ) / (n : ℝ)) ^ 2 :=
        mul_nonneg (by linarith) (sq_nonneg _)
      linarith
    have h1 : 1 + ((q : ℝ) - 1) * ((r : ℝ) / (n : ℝ)) ^ 2
        ≤ 1 + ((q : ℝ) - 1) * ((r : ℝ) / (n : ℝ)) := by
      have := mul_le_mul_of_nonneg_left hθsq (show (0 : ℝ) ≤ (q : ℝ) - 1 by linarith)
      linarith
    exact pow_le_pow_left₀ h0 h1 n
  -- bound the B-term: B(θ) ≤ 1 + (q²+q-1)θ, hence B(θ)^n ≤ (1+(q²+q-1)θ)^n
  have hB0 : (0 : ℝ) ≤ (q : ℝ) * (2 * ((r : ℝ) / (n : ℝ)) + ((q : ℝ) - 2)
      * ((r : ℝ) / (n : ℝ)) ^ 2) + (1 + ((q : ℝ) - 1) * ((r : ℝ) / (n : ℝ)) ^ 2) := by
    have e0 : (0 : ℝ) ≤ (q : ℝ) * (2 * ((r : ℝ) / (n : ℝ)) + ((q : ℝ) - 2)
        * ((r : ℝ) / (n : ℝ)) ^ 2) :=
      mul_nonneg (by linarith)
        (add_nonneg (by linarith) (mul_nonneg (by linarith) (sq_nonneg _)))
    have e1 : (0 : ℝ) ≤ ((q : ℝ) - 1) * ((r : ℝ) / (n : ℝ)) ^ 2 :=
      mul_nonneg (by linarith) (sq_nonneg _)
    linarith
  have hB : ((q : ℝ) * (2 * ((r : ℝ) / (n : ℝ)) + ((q : ℝ) - 2) * ((r : ℝ) / (n : ℝ)) ^ 2)
        + (1 + ((q : ℝ) - 1) * ((r : ℝ) / (n : ℝ)) ^ 2)) ^ n
      ≤ (1 + (((q : ℝ) ^ 2 + (q : ℝ)) - 1) * ((r : ℝ) / (n : ℝ))) ^ n := by
    have e1 : (0 : ℝ) ≤ (q : ℝ) * ((q : ℝ) - 2)
        * (((r : ℝ) / (n : ℝ)) - ((r : ℝ) / (n : ℝ)) ^ 2) :=
      mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
    have e2 : (0 : ℝ) ≤ ((q : ℝ) - 1) * (((r : ℝ) / (n : ℝ)) - ((r : ℝ) / (n : ℝ)) ^ 2) :=
      mul_nonneg (by linarith) (by linarith)
    have h1 : (q : ℝ) * (2 * ((r : ℝ) / (n : ℝ)) + ((q : ℝ) - 2) * ((r : ℝ) / (n : ℝ)) ^ 2)
          + (1 + ((q : ℝ) - 1) * ((r : ℝ) / (n : ℝ)) ^ 2)
        ≤ 1 + (((q : ℝ) ^ 2 + (q : ℝ)) - 1) * ((r : ℝ) / (n : ℝ)) := by nlinarith [e1, e2]
    exact pow_le_pow_left₀ hB0 h1 n
  -- instantiate the kernel at θ = r/n and divide through
  have hker := hkernel ((r : ℝ) / (n : ℝ)) hθ0.le hθ1
  have hS1 : S ≤ ((1 + ((q : ℝ) - 1) * ((r : ℝ) / (n : ℝ))) ^ n
      + (1 + (((q : ℝ) ^ 2 + (q : ℝ)) - 1) * ((r : ℝ) / (n : ℝ))) ^ n / (q : ℝ) ^ (n - k))
        / ((r : ℝ) / (n : ℝ)) ^ (2 * r) := by
    rw [le_div_iff₀ hθpow]
    have hdivB : ((q : ℝ) * (2 * ((r : ℝ) / (n : ℝ)) + ((q : ℝ) - 2)
          * ((r : ℝ) / (n : ℝ)) ^ 2) + (1 + ((q : ℝ) - 1) * ((r : ℝ) / (n : ℝ)) ^ 2)) ^ n
            / (q : ℝ) ^ (n - k)
        ≤ (1 + (((q : ℝ) ^ 2 + (q : ℝ)) - 1) * ((r : ℝ) / (n : ℝ))) ^ n
            / (q : ℝ) ^ (n - k) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hB (by positivity)
    calc S * ((r : ℝ) / (n : ℝ)) ^ (2 * r)
        = ((r : ℝ) / (n : ℝ)) ^ (2 * r) * S := mul_comm _ _
      _ ≤ (1 + ((q : ℝ) - 1) * ((r : ℝ) / (n : ℝ)) ^ 2) ^ n
            + ((q : ℝ) * (2 * ((r : ℝ) / (n : ℝ)) + ((q : ℝ) - 2) * ((r : ℝ) / (n : ℝ)) ^ 2)
                + (1 + ((q : ℝ) - 1) * ((r : ℝ) / (n : ℝ)) ^ 2)) ^ n
                  / (q : ℝ) ^ (n - k) := hker
      _ ≤ (1 + ((q : ℝ) - 1) * ((r : ℝ) / (n : ℝ))) ^ n
            + (1 + (((q : ℝ) ^ 2 + (q : ℝ)) - 1) * ((r : ℝ) / (n : ℝ))) ^ n
                / (q : ℝ) ^ (n - k) := add_le_add hA hdivB
  -- split the division and apply the entropy-form bound twice (a = 1)
  have hsplit : ((1 + ((q : ℝ) - 1) * ((r : ℝ) / (n : ℝ))) ^ n
      + (1 + (((q : ℝ) ^ 2 + (q : ℝ)) - 1) * ((r : ℝ) / (n : ℝ))) ^ n / (q : ℝ) ^ (n - k))
        / ((r : ℝ) / (n : ℝ)) ^ (2 * r)
      = (1 + ((q : ℝ) - 1) * ((r : ℝ) / (n : ℝ))) ^ n / ((r : ℝ) / (n : ℝ)) ^ (2 * r)
        + ((1 + (((q : ℝ) ^ 2 + (q : ℝ)) - 1) * ((r : ℝ) / (n : ℝ))) ^ n
            / ((r : ℝ) / (n : ℝ)) ^ (2 * r)) / (q : ℝ) ^ (n - k) := by
    rw [add_div, div_right_comm]
  have hb1 : (0 : ℝ) < (q : ℝ) - 1 := by linarith
  have hb2 : (0 : ℝ) < ((q : ℝ) ^ 2 + (q : ℝ)) - 1 := by nlinarith
  have hE1 := model_bound_entropy 1 ((q : ℝ) - 1) n r one_pos hb1 hr hrn
  have hE2 := model_bound_entropy 1 (((q : ℝ) ^ 2 + (q : ℝ)) - 1) n r one_pos hb2 hr hrn
  simp only [one_pow, one_mul, div_one] at hE1 hE2
  have hdivE2 : (1 + (((q : ℝ) ^ 2 + (q : ℝ)) - 1) * ((r : ℝ) / (n : ℝ))) ^ n
        / ((r : ℝ) / (n : ℝ)) ^ (2 * r) / (q : ℝ) ^ (n - k)
      ≤ Real.exp ((((q : ℝ) ^ 2 + (q : ℝ)) - 1) * (r : ℝ)) * ((n : ℝ) / (r : ℝ)) ^ (2 * r)
        / (q : ℝ) ^ (n - k) := by
    rw [div_eq_mul_inv, div_eq_mul_inv
      (Real.exp ((((q : ℝ) ^ 2 + (q : ℝ)) - 1) * (r : ℝ)) * ((n : ℝ) / (r : ℝ)) ^ (2 * r))]
    exact mul_le_mul_of_nonneg_right hE2 (by positivity)
  calc S ≤ ((1 + ((q : ℝ) - 1) * ((r : ℝ) / (n : ℝ))) ^ n
        + (1 + (((q : ℝ) ^ 2 + (q : ℝ)) - 1) * ((r : ℝ) / (n : ℝ))) ^ n / (q : ℝ) ^ (n - k))
          / ((r : ℝ) / (n : ℝ)) ^ (2 * r) := hS1
    _ = (1 + ((q : ℝ) - 1) * ((r : ℝ) / (n : ℝ))) ^ n / ((r : ℝ) / (n : ℝ)) ^ (2 * r)
        + ((1 + (((q : ℝ) ^ 2 + (q : ℝ)) - 1) * ((r : ℝ) / (n : ℝ))) ^ n
            / ((r : ℝ) / (n : ℝ)) ^ (2 * r)) / (q : ℝ) ^ (n - k) := hsplit
    _ ≤ Real.exp (((q : ℝ) - 1) * (r : ℝ)) * ((n : ℝ) / (r : ℝ)) ^ (2 * r)
        + Real.exp ((((q : ℝ) ^ 2 + (q : ℝ)) - 1) * (r : ℝ)) * ((n : ℝ) / (r : ℝ)) ^ (2 * r)
            / (q : ℝ) ^ (n - k) := add_le_add hE1 hdivE2
    _ = ((n : ℝ) / (r : ℝ)) ^ (2 * r)
        * (Real.exp (((q : ℝ) - 1) * (r : ℝ))
            + Real.exp ((((q : ℝ) ^ 2 + (q : ℝ)) - 1) * (r : ℝ)) / (q : ℝ) ^ (n - k)) := by
      ring

/-! ### Non-vacuity: concrete numeric instantiation at q = 17, n = 16, k = 2, r = 4 -/

/-- Numeric check of the interior closed form at a = 1, b = 16, n = 16, r = 4:
θ* = 2·4·1/(16·(16−8)) = 1/16, and f(1/16) = 2¹⁶·16⁸ = 2⁴⁸. -/
example : ((1 : ℝ) + 16 * (2 * (4 : ℝ) * 1 / (16 * ((16 : ℝ) - 2 * 4)))) ^ 16
    / (2 * (4 : ℝ) * 1 / (16 * ((16 : ℝ) - 2 * 4))) ^ (2 * 4)
    = 281474976710656 := by norm_num

/-- Cross-check: the closed-form RHS of `model_bound_interior` at the same parameters
evaluates to the same number 2⁴⁸. -/
example : ((1 : ℝ) * 16 / ((16 : ℝ) - 2 * 4)) ^ 16
    * (16 * ((16 : ℝ) - 2 * 4) / (2 * (4 : ℝ) * 1)) ^ (2 * 4)
    = 281474976710656 := by norm_num

/-- A concrete witness: S = 1 satisfies the kernel hypothesis at q = 17, n = 16, k = 2,
r = 4 (indeed θ⁸ ≤ 1 ≤ (1+16θ²)¹⁶ and the second term is nonnegative).  This shows the
hypothesis of `second_moment_opt_bound` is satisfiable by a concrete construction. -/
theorem numeric_kernel_witness : ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
    θ ^ (2 * 4) * (1 : ℝ) ≤
      (1 + (((17 : ℕ) : ℝ) - 1) * θ ^ 2) ^ 16
        + (((17 : ℕ) : ℝ) * (2 * θ + (((17 : ℕ) : ℝ) - 2) * θ ^ 2)
            + (1 + (((17 : ℕ) : ℝ) - 1) * θ ^ 2)) ^ 16 / ((17 : ℕ) : ℝ) ^ (16 - 2) := by
  intro θ h0 h1
  have h17 : ((17 : ℕ) : ℝ) = 17 := by norm_num
  rw [h17]
  have hle1 : θ ^ (2 * 4) * (1 : ℝ) ≤ 1 := by
    rw [mul_one]
    exact pow_le_one₀ h0 h1
  have hA1 : (1 : ℝ) ≤ (1 + ((17 : ℝ) - 1) * θ ^ 2) ^ 16 := by
    apply one_le_pow₀
    nlinarith [sq_nonneg θ]
  have hB1 : (0 : ℝ) ≤ ((17 : ℝ) * (2 * θ + ((17 : ℝ) - 2) * θ ^ 2)
      + (1 + ((17 : ℝ) - 1) * θ ^ 2)) ^ 16 / (17 : ℝ) ^ (16 - 2) := by
    apply div_nonneg _ (by positivity)
    apply pow_nonneg
    nlinarith [sq_nonneg θ]
  calc θ ^ (2 * 4) * (1 : ℝ) ≤ 1 := hle1
    _ ≤ (1 + ((17 : ℝ) - 1) * θ ^ 2) ^ 16 := hA1
    _ ≤ (1 + ((17 : ℝ) - 1) * θ ^ 2) ^ 16
        + ((17 : ℝ) * (2 * θ + ((17 : ℝ) - 2) * θ ^ 2)
            + (1 + ((17 : ℝ) - 1) * θ ^ 2)) ^ 16 / (17 : ℝ) ^ (16 - 2) :=
      le_add_of_nonneg_right hB1

/-- **Concrete end-to-end instance** at q = 17, n = 16, k = 2, r = 4 with the witness
S = 1: the optimized bound 1 ≤ (16/4)⁸·(exp(16·4) + exp(305·4)/17¹⁴) is derived through
`second_moment_opt_bound` from a fully constructed (non-hypothetical) kernel input. -/
theorem numeric_instance :
    (1 : ℝ) ≤ (((16 : ℕ) : ℝ) / ((4 : ℕ) : ℝ)) ^ (2 * 4)
      * (Real.exp ((((17 : ℕ) : ℝ) - 1) * ((4 : ℕ) : ℝ))
          + Real.exp (((((17 : ℕ) : ℝ) ^ 2 + ((17 : ℕ) : ℝ)) - 1) * ((4 : ℕ) : ℝ))
              / ((17 : ℕ) : ℝ) ^ (16 - 2)) :=
  second_moment_opt_bound 17 16 2 4 1 (by norm_num) (by norm_num) (by norm_num)
    numeric_kernel_witness

/-- Decimal sanity: the instantiated bound's prefactor (16/4)^(2·4) = 65536 and the
exponent arguments are 64 and 1220 — the bound is an honest explicit number. -/
example : (((16 : ℕ) : ℝ) / ((4 : ℕ) : ℝ)) ^ (2 * 4) = 65536 ∧
    ((((17 : ℕ) : ℝ) - 1) * ((4 : ℕ) : ℝ)) = 64 ∧
    (((((17 : ℕ) : ℝ) ^ 2 + ((17 : ℕ) : ℝ)) - 1) * ((4 : ℕ) : ℝ)) = 1220 := by
  norm_num

end ThetaOpt

#print axioms ThetaOpt.model_bound_interior
#print axioms ThetaOpt.model_bound_min
#print axioms ThetaOpt.model_bound_entropy
#print axioms ThetaOpt.second_moment_opt_bound
#print axioms ThetaOpt.numeric_kernel_witness
#print axioms ThetaOpt.numeric_instance
