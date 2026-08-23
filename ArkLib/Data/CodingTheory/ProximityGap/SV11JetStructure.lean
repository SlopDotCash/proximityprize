/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SV11GeneratorFamily
import Mathlib.Algebra.Polynomial.Taylor

/-!
# The order-`M` jet of the SV11 generator at a rep point (#389)

The sharp Garcia–Voloch / Heath-Brown–Konyagin Stepanov bound on `|R ∩ (R+c)|` needs the *order of
vanishing* of the Wronskian of the generators `g_{a,b}(X) = X^a (X−c)^{tb}` at the rep points, which
is governed by the rank of the **jet-evaluation map** `g ↦ (D_0 g(y), D_1 g(y), …, D_{M-1} g(y))`.

This file computes that jet exactly. Via Hasse–Leibniz (`hasseDeriv_mul`) and the two factor jets
(`hasseDeriv_X_pow_eval`, `hasseDeriv_X_sub_C_pow_eval` — the latter from `taylor_coeff` +
`coeff_X_add_C_pow`), at a rep point `(y−c)^t = 1`:

  `(y−c)^i · (D_i g_{a,b})(y) = ∑_{j+k=i} C(a,j)·C(tb,k)·y^{a−j}·(y−c)^j`   (`sv11Gen_hasseDeriv_eval_mul`).

The crucial structural fact this exposes: the `b`-dependence enters **only** through the binomials
`C(tb,k)` with `k ≤ i` — polynomials in `b` of degree `≤ i`. So across the `B` values of `b`, the
order-`M` jet map has `b`-rank `≤ M` (not `B`). This rank deficiency is exactly the "free" high-order
vanishing the Stepanov auxiliary exploits, and the input to the Wronskian degree-reduction giving the
sharp `O(n^{2/3})` exponent. Generalises the order-0 (`sv11Gen_eval_of_pow_eq_one`) and order-1
(`sv11Gen_deriv_eval_mul`) bricks to all orders.

Axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

open Polynomial Finset

namespace ProximityGap.BinomialDet

variable {F : Type*} [Field F]

/-- Hasse derivative of a shifted power, evaluated: `(D_k (X−c)^m)(y) = C(m,k)·(y−c)^{m−k}`. -/
theorem hasseDeriv_X_sub_C_pow_eval (c y : F) (m k : ℕ) :
    (hasseDeriv k ((X - C c) ^ m)).eval y = (m.choose k : F) * (y - c) ^ (m - k) := by
  rw [← Polynomial.taylor_coeff, Polynomial.taylor_apply, pow_comp, sub_comp, X_comp, C_comp,
    show (X + C y) - C c = X + C (y - c) by rw [map_sub]; ring, coeff_X_add_C_pow, mul_comm]

/-- Hasse derivative of `X^a`, evaluated: `(D_j X^a)(y) = C(a,j)·y^{a−j}`. -/
theorem hasseDeriv_X_pow_eval (y : F) (a j : ℕ) :
    (hasseDeriv j ((X : F[X]) ^ a)).eval y = (a.choose j : F) * y ^ (a - j) := by
  rw [X_pow_eq_monomial, hasseDeriv_monomial, mul_one, eval_monomial]

/-- **The general order-`i` jet of the SV11 generator at a rep point (Hasse–Leibniz).** At a rep
point `(y−c)^t = 1`,
`(y−c)^i · (D_i g_{a,b})(y) = ∑_{j+k=i} C(a,j)·C(tb,k)·y^{a−j}·(y−c)^j`.
The `b`-dependence enters only through the binomials `C(tb,k)` (polynomials in `b` of degree `k ≤ i`),
so the order-`M` jet map has `b`-rank `≤ M` — the structure governing the Wronskian's multiplicity at
rep points. Generalises the order-0 (`b`-collapse) and order-1 (`tb`-weighting) bricks. -/
theorem sv11Gen_hasseDeriv_eval_mul (c y : F) {t : ℕ} (a b i : ℕ) (h : (y - c) ^ t = 1) :
    (hasseDeriv i (sv11Gen c t (a, b))).eval y * (y - c) ^ i
      = ∑ p ∈ Finset.antidiagonal i,
          (a.choose p.1 : F) * ((t * b).choose p.2 : F) * y ^ (a - p.1) * (y - c) ^ p.1 := by
  have hpow : (y - c) ^ (t * b) = 1 := by rw [pow_mul, h, one_pow]
  unfold sv11Gen
  rw [hasseDeriv_mul, eval_finset_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mem_antidiagonal] at hp
  rw [eval_mul, hasseDeriv_X_pow_eval, hasseDeriv_X_sub_C_pow_eval]
  rcases Nat.lt_or_ge (t * b) p.2 with hlt | hle
  · rw [Nat.choose_eq_zero_of_lt hlt]; push_cast; ring
  · have hpw : (y - c) ^ (t * b - p.2) * (y - c) ^ i = (y - c) ^ p.1 := by
      rw [← pow_add, show t * b - p.2 + i = t * b + p.1 by omega, pow_add, hpow, one_mul]
    calc (a.choose p.1 : F) * y ^ (a - p.1)
            * ((t * b).choose p.2 * (y - c) ^ (t * b - p.2)) * (y - c) ^ i
        = (a.choose p.1 : F) * ((t * b).choose p.2) * y ^ (a - p.1)
            * ((y - c) ^ (t * b - p.2) * (y - c) ^ i) := by ring
      _ = _ := by rw [hpw]

/-- **The generalized free order-`M` vanishing (the rank-deficiency theorem).** If for every `a` and
every `k < M` the generalized moment `∑_b coef(a,b)·C(tb,k) = 0`, then for every `i < M` the `i`-th
Hasse derivative of `Ψ = ∑ coef·g_{a,b}` vanishes at every rep point `y` (`(y−c)^t = 1`, `y ≠ c`).
Hence `Ψ` vanishes to order `≥ M` at every rep point. This is the exact statement of the
`b`-rank-`≤ M` jet deficiency: order-`M` vanishing at the whole rep set costs only the `M·D` moment
conditions. Generalizes the order-0/1/2 ladder bricks to all orders. -/
theorem sv11_combination_hasseDeriv_eval_zero {D B M : ℕ} (c y : F) (t : ℕ) (coef : ℕ → ℕ → F)
    (h : (y - c) ^ t = 1) (hcy : y ≠ c)
    (hmom : ∀ a, ∀ k, k < M → ∑ b ∈ Finset.range B, coef a b * ((t * b).choose k : F) = 0)
    {i : ℕ} (hi : i < M) :
    (hasseDeriv i (∑ a ∈ Finset.range D, ∑ b ∈ Finset.range B,
        Polynomial.C (coef a b) * sv11Gen c t (a, b))).eval y = 0 := by
  have hne : (y - c) ^ i ≠ 0 := pow_ne_zero i (sub_ne_zero.mpr hcy)
  refine (mul_eq_zero.mp ?_).resolve_right hne
  -- linearity: push hasseDeriv i + eval through the double sum
  have hlin : (hasseDeriv i (∑ a ∈ Finset.range D, ∑ b ∈ Finset.range B,
        Polynomial.C (coef a b) * sv11Gen c t (a, b))).eval y
      = ∑ a ∈ Finset.range D, ∑ b ∈ Finset.range B,
          coef a b * (hasseDeriv i (sv11Gen c t (a, b))).eval y := by
    rw [map_sum, eval_finset_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [map_sum, eval_finset_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [← smul_eq_C_mul, map_smul, smul_eq_C_mul, eval_C_mul]
  rw [hlin, Finset.sum_mul]
  refine Finset.sum_eq_zero (fun a _ => ?_)
  rw [Finset.sum_mul]
  -- per-b: rewrite via the jet formula, then sum_comm + moment
  have hb : ∀ b ∈ Finset.range B,
      coef a b * (hasseDeriv i (sv11Gen c t (a, b))).eval y * (y - c) ^ i
        = ∑ p ∈ Finset.antidiagonal i,
            ((a.choose p.1 : F) * y ^ (a - p.1) * (y - c) ^ p.1)
              * (coef a b * ((t * b).choose p.2 : F)) := by
    intro b _
    rw [mul_assoc, sv11Gen_hasseDeriv_eval_mul c y a b i h, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    ring
  rw [Finset.sum_congr rfl hb, Finset.sum_comm]
  refine Finset.sum_eq_zero (fun p hp => ?_)
  rw [← Finset.mul_sum]
  have hp2 : p.2 < M := lt_of_le_of_lt (by rw [Finset.mem_antidiagonal] at hp; omega) hi
  rw [hmom a p.2 hp2, mul_zero]

/-- **Free order-`M` vanishing for arbitrary `x`-exponents.** The generalized rank-deficiency vanishing
(`sv11_combination_hasseDeriv_eval_zero`) re-parametrized so the `x`-layer uses arbitrary exponents
`m a` rather than `a` itself — exactly the form needed for the sharp `DB²` family (`m a = a'+t·b₀`,
matching `sv11_family_indep`). The moment conditions are unchanged (they range over `b`); the exponent
`m a` is simply carried through the jet formula. -/
theorem sv11_combination_hasseDeriv_eval_zero_exp {D B M : ℕ} (c y : F) (t : ℕ) (m : ℕ → ℕ)
    (coef : ℕ → ℕ → F) (h : (y - c) ^ t = 1) (hcy : y ≠ c)
    (hmom : ∀ a, ∀ k, k < M → ∑ b ∈ Finset.range B, coef a b * ((t * b).choose k : F) = 0)
    {i : ℕ} (hi : i < M) :
    (hasseDeriv i (∑ a ∈ Finset.range D, ∑ b ∈ Finset.range B,
        Polynomial.C (coef a b) * sv11Gen c t (m a, b))).eval y = 0 := by
  have hne : (y - c) ^ i ≠ 0 := pow_ne_zero i (sub_ne_zero.mpr hcy)
  refine (mul_eq_zero.mp ?_).resolve_right hne
  have hlin : (hasseDeriv i (∑ a ∈ Finset.range D, ∑ b ∈ Finset.range B,
        Polynomial.C (coef a b) * sv11Gen c t (m a, b))).eval y
      = ∑ a ∈ Finset.range D, ∑ b ∈ Finset.range B,
          coef a b * (hasseDeriv i (sv11Gen c t (m a, b))).eval y := by
    rw [map_sum, eval_finset_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [map_sum, eval_finset_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [← smul_eq_C_mul, map_smul, smul_eq_C_mul, eval_C_mul]
  rw [hlin, Finset.sum_mul]
  refine Finset.sum_eq_zero (fun a _ => ?_)
  rw [Finset.sum_mul]
  have hb : ∀ b ∈ Finset.range B,
      coef a b * (hasseDeriv i (sv11Gen c t (m a, b))).eval y * (y - c) ^ i
        = ∑ p ∈ Finset.antidiagonal i,
            (((m a).choose p.1 : F) * y ^ (m a - p.1) * (y - c) ^ p.1)
              * (coef a b * ((t * b).choose p.2 : F)) := by
    intro b _
    rw [mul_assoc, sv11Gen_hasseDeriv_eval_mul c y (m a) b i h, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    ring
  rw [Finset.sum_congr rfl hb, Finset.sum_comm]
  refine Finset.sum_eq_zero (fun p hp => ?_)
  rw [← Finset.mul_sum]
  have hp2 : p.2 < M := lt_of_le_of_lt (by rw [Finset.mem_antidiagonal] at hp; omega) hi
  rw [hmom a p.2 hp2, mul_zero]

end ProximityGap.BinomialDet


-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.BinomialDet.hasseDeriv_X_sub_C_pow_eval
#print axioms ProximityGap.BinomialDet.sv11Gen_hasseDeriv_eval_mul
#print axioms ProximityGap.BinomialDet.sv11_combination_hasseDeriv_eval_zero
#print axioms ProximityGap.BinomialDet.sv11_combination_hasseDeriv_eval_zero_exp
