/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Sutherland, Ilia Vlasov
-/
import Mathlib.Algebra.Polynomial.BigOperators

import ArkLib.Data.Polynomial.FoldingPolynomial

/-!
# Generalized polynomial splitting and folding

This file defines n-way splitting and folding operations on polynomials.

## Main definitions

* `Polynomial.splitNth f n i`: Splits polynomial `f` into `n` component polynomials,
  where `splitNth f n i` extracts coefficients at positions `j ≡ i (mod n)`.

* `Polynomial.foldNth n f α`: Recombines the n-way split of `f` using powers of `α`,
  computing `∑ i : Fin n, α^i * splitNth f n i`. This is the core operation in
  FRI-style polynomial commitment schemes.

## Implementation notes

When `n = 2`, this recovers the even/odd splitting: `splitNth f 2 0` gives the even
coefficients and `splitNth f 2 1` gives the odd coefficients (after appropriate
reindexing).

-/

open Polynomial

namespace Polynomial

variable {𝔽 : Type*} [CommSemiring 𝔽] [NoZeroDivisors 𝔽]

/--
Splits a polynomial into `n` component polynomials based on coefficient indices modulo `n`.

For a polynomial `f = ∑ⱼ aⱼ Xʲ` and index `i : Fin n`, returns the polynomial whose
coefficients are extracted from positions `j ≡ i (mod n)`, reindexed by `j / n`.
Formally: `splitNth f n i = ∑_{j ≡ i (mod n)} aⱼ X^(j/n)`.
-/
def splitNth (f : 𝔽[X]) (n : ℕ) [inst : NeZero n] : Fin n → 𝔽[X] :=
  fun i =>
    let sup :=
      Finset.filterMap (fun x => if x % n = i.1 then .some (x / n) else .none)
      f.support
      (by
        intros a a' b
        simp only [Option.mem_def, Option.ite_none_right_eq_some, Option.some.injEq, and_imp]
        intros h g h' g'
        rw [Eq.symm (Nat.div_add_mod' a n), Eq.symm (Nat.div_add_mod' a' n)]
        rw [h, g, h', g'])
    Polynomial.ofFinsupp
      ⟨
        sup,
        fun e => f.coeff (e * n + i.1),
        by
          intros a
          dsimp [sup]
          simp only [Finset.mem_filterMap, mem_support_iff, ne_eq, Option.ite_none_right_eq_some,
            Option.some.injEq]
          apply Iff.intro
          · rintro ⟨a', g⟩
            have : a' = a * n + i.1 := by
              rw [Eq.symm (Nat.div_add_mod' a' n)]
              rw [g.2.1, g.2.2]
            rw [this.symm]
            exact g.1
          · intros h
            exists (a * n + i.1)
            apply And.intro h
            rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt i.2]
            apply And.intro rfl
            have {a b : ℕ} : (a * n + b) / n = a + (b / n) := by
              have := inst.out
              have ne_zero : 0 < n := by omega
              rw [Nat.add_div ne_zero, Nat.mul_mod_left, zero_add, Nat.mul_div_cancel a ne_zero]
              have : ¬ (n ≤ b % n) := by
                simp only [not_le]
                exact Nat.mod_lt b ne_zero
              simp [this]
            simp [this]
      ⟩

omit [NoZeroDivisors 𝔽] in
/-- Coefficients of `splitNth` are the corresponding congruence-class coefficients of `f`. -/
lemma coeff_splitNth (f : 𝔽[X]) (n : ℕ) [NeZero n] (i : Fin n) (e : ℕ) :
    (splitNth f n i).coeff e = f.coeff (e * n + i.1) := by
  unfold splitNth
  simp [coeff_ofFinsupp, Finsupp.coe_mk]

omit [NoZeroDivisors 𝔽] in
/-- `splitNth` is additive in the polynomial being split. -/
lemma splitNth_add (p q : 𝔽[X]) (n : ℕ) [NeZero n] (i : Fin n) :
    splitNth (p + q) n i = splitNth p n i + splitNth q n i := by
  ext e
  simp [coeff_splitNth]

/- Proof of key identity `splitNth` has to satisfy. -/
omit [NoZeroDivisors 𝔽] in
lemma splitNth_def (n : ℕ) (f : 𝔽[X]) [inst : NeZero n] :
    f =
      ∑ i : Fin n,
        (Polynomial.X ^ i.1) *
          Polynomial.eval₂ Polynomial.C (Polynomial.X ^ n) (splitNth f n i) := by
  ext e
  rw [Polynomial.finset_sum_coeff]
  have h₀ {b e : ℕ} {f : 𝔽[X]} : (X ^ b * f).coeff e = if e < b then 0 else f.coeff (e - b) := by
    rw [Polynomial.coeff_X_pow_mul' f b e]
    aesop
  have h₁ {e : ℕ} {f : 𝔽[X]}  :
    (eval₂ C (X ^ n) f).coeff e =
      if e % n = 0
      then f.coeff (e / n)
      else 0 := by
    rw [Polynomial.eval₂_def, Polynomial.coeff_sum, Polynomial.sum_def]
    conv =>
      lhs
      congr
      · skip
      ext n
      rw [←pow_mul, Polynomial.coeff_C_mul_X_pow]
    by_cases h : e % n = 0 <;> simp only [h, ↓reduceIte]
    · rw [Finset.sum_eq_single (e / n)]
      · have : e = n * (e / n) :=
          Nat.eq_mul_of_div_eq_right
            (Nat.dvd_of_mod_eq_zero h) rfl
        rw [if_pos]
        exact this
      · intros b h₀ h₁
        have : ¬ (e = n * b) := by
          intros h'
          apply h₁
          rw [h']
          exact Nat.eq_div_of_mul_eq_right inst.out rfl
        simp [this]
      · intros h'
        split_ifs with h''
        · exact notMem_support_iff.mp h'
        · rfl
    · apply Finset.sum_eq_zero
      intro m _
      have hne : e ≠ n * m := by
        intro hm
        apply h
        rw [hm, Nat.mul_mod_right]
      simp [hne]
  conv =>
    rhs
    congr
    · skip
    · ext b
      rw [h₀, h₁]
  unfold splitNth
  simp only [coeff_ofFinsupp, Finsupp.coe_mk]
  rw [Finset.sum_eq_single ⟨e % n, by refine Nat.mod_lt e (by have := inst.out; omega)⟩]
  · simp only
    have h₁ : ¬ (e < e % n) := by
      by_cases h : e < n
      · rw [Nat.mod_eq_of_lt h]
        simp
      · simp only [not_lt] at h ⊢
        exact Nat.mod_le e n
    have h₂ : (e - e % n) % n = 0 := Nat.sub_mod_eq_zero_of_mod_eq (by simp)
    simp only [h₁, h₂, Eq.symm Nat.div_eq_sub_mod_div, Nat.div_add_mod' e n, ↓reduceIte]
  · rintro ⟨b, h⟩ _
    simp only [ne_eq, Fin.mk.injEq, ite_eq_left_iff, not_lt, ite_eq_right_iff]
    intros h₀ h₁ h₂
    exfalso
    apply h₀
    symm
    calc
      e % n = ((e - b) + b) % n := by rw [Nat.sub_add_cancel h₁]
      _ = (((e - b) % n) + b % n) % n := by rw [Nat.add_mod]
      _ = b := by simp [h₂, Nat.mod_eq_of_lt h]
  · intro h
    simp at h

/- Lemma bounding degree of each `n`-split polynomial. -/
omit [NoZeroDivisors 𝔽] in
lemma splitNth_degree_le {n : ℕ} {f : 𝔽[X]} [inst : NeZero n] :
    ∀ {i}, (splitNth f n i).natDegree ≤ f.natDegree / n := by
    intros i
    unfold splitNth Polynomial.natDegree Polynomial.degree
    simp only [support_ofFinsupp]
    rw [WithBot.unbotD_le_iff (by simp)]
    simp only [Finset.max_le_iff, Finset.mem_filterMap, mem_support_iff, ne_eq,
      Option.ite_none_right_eq_some, Option.some.injEq, WithBot.coe_le_coe, forall_exists_index,
      and_imp]
    intros _ _ h _ h'
    rw [←h']
    refine Nat.div_le_div ?_ (Nat.le_refl n) inst.out
    exact le_natDegree_of_ne_zero h

/-- `foldingPolynomial` in terms of `splitNth`
    when `q = X ^ n`. -/
@[simp]
lemma folding_polynomial_eq_sum_splitNth {𝔽 : Type*} [Field 𝔽]
  {f : Polynomial 𝔽} {n : ℕ}
  [inst : NeZero n] :
  FoldingPolynomial.foldingPolynomial (X ^ n) f =
    ∑ i, C (splitNth f n i) * (X ^ i.val) := by
  symm
  apply FoldingPolynomial.folding_polynomial_is_unique'
  · conv =>
      rhs
      rw [splitNth_def (f := f) (inst := inst)]
    rw [
      Polynomial.map_sum,
      Polynomial.eval_finset_sum]
    simp only [Polynomial.map_mul, map_C, coe_compRingHom, Polynomial.map_pow, map_X,
    eval_mul, eval_C, eval_pow, eval_X]
    simp only [comp]
    conv =>
      lhs
      rhs
      ext x
      rw [mul_comm]
      rfl
  · simp only [Bivariate.degreeX, finset_sum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one,
    mul_zero, natDegree_pow, natDegree_X]
    simp only [Finset.sup_le_iff, mem_support_iff, finset_sum_coeff, coeff_C_mul, coeff_X_pow,
    mul_ite, mul_one, mul_zero, ne_eq]
    intro b hb
    apply natDegree_sum_le_of_forall_le
    rintro ⟨i, hi⟩ _
    by_cases heq: b = i
    · simp only [heq, ↓reduceIte]
      exact splitNth_degree_le
    · simp [heq]
  · simp only [Bivariate.natDegreeY, natDegree_pow, natDegree_X, mul_one]
    apply Nat.lt_of_le_pred (by {
      apply Nat.zero_lt_of_ne_zero
      aesop
    })
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro i _
    apply Nat.le_trans Polynomial.natDegree_mul_le
    rcases i with ⟨i, hi⟩
    simp
    omega

/-- `polyFold` in terms of `splitNth`. -/
@[simp]
lemma polyFold_eq_sum_of_splitNth {𝔽 : Type*} [Field 𝔽]
  {f : 𝔽[X]} {n : ℕ} {r : 𝔽}
  [inst : NeZero n] :
  FoldingPolynomial.polyFold f n r =
    ∑ i, C (r ^ i.val) * splitNth f n i := by
  simp only [FoldingPolynomial.polyFold, folding_polynomial_eq_sum_splitNth, map_pow]
  rw [Polynomial.eval_finset_sum]
  simp only [eval_mul, eval_C, eval_pow, eval_X]
  conv =>
    lhs
    rhs
    ext x
    rw [mul_comm]

omit [NoZeroDivisors 𝔽] in
/--
Lemma bridges the coefficient-level identity `splitNth_def` and
evaluation-level reasoning about `splitNth` and `foldNth`.
-/
lemma splitNth_eval_comp_pow {n : ℕ} [NeZero n] (f : 𝔽[X]) (x : 𝔽) (i : Fin n) :
    (eval₂ C (X ^ n) (splitNth f n i)).eval x = (splitNth f n i).eval (x ^ n) := by
  rw [eval₂_eq_sum]
  unfold Polynomial.eval
  rw [Polynomial.eval₂_sum, eval₂_eq_sum]
  congr
  ext e a
  rw [← eval]
  simp

/-!
# Evaluation-level lemmas for `splitNth` and `foldNth`

This section adds evaluation-level lemmas to complement the existing coefficient-level
definitions in this file.

**Context**: These lemmas arise naturally when verifying Plonky3's FRI folding
operation. The existing file defines `splitNth` with coefficient-level identities
(`splitNth_def`) and degree bounds (`splitNth_degree_le`), but provides no evaluation-level
results.

The lemmas below fill that gap. Together they prove that `foldNth 2 f β` evaluated at `x²`
equals the standard FRI fold of `f(x)` and `f(-x)`.

Addresses: https://github.com/Verified-zkEVM/ArkLib/issues/450
-/

variable {𝔽 : Type*} [Field 𝔽]

/-- Helper lemma: `splitNth` of monomial at even position -/
lemma splitNth_monomial_even (a : 𝔽) (k : ℕ) :
    splitNth (monomial (k + k) a) 2 0 = monomial k a := by
  ext j
  by_cases hdeg : k + k = j * 2
  · have hj : j = k := by omega
    subst hj
    rw [coeff_splitNth, coeff_monomial, coeff_monomial]
    rw [if_pos (by omega), if_pos rfl]
  · have hkj : k ≠ j := by omega
    rw [coeff_splitNth, coeff_monomial, coeff_monomial]
    rw [if_neg (by omega), if_neg hkj]

/-- Helper lemma: the odd split of an even monomial vanishes. -/
lemma splitNth_monomial_even_odd_zero (a : 𝔽) (k : ℕ) :
    splitNth (monomial (k + k) a) 2 1 = 0 := by
  ext j
  by_cases hdeg : k + k = j * 2 + 1
  · omega
  · simp [coeff_splitNth, coeff_monomial, hdeg]

/-- Helper lemma: `splitNth` of monomial at odd position -/
lemma splitNth_monomial_odd (a : 𝔽) (k : ℕ) :
    splitNth (monomial (2 * k + 1) a) 2 1 = monomial k a := by
  ext j
  by_cases hdeg : 2 * k = j * 2
  · have hj : j = k := by omega
    subst hj
    rw [coeff_splitNth, coeff_monomial, coeff_monomial]
    rw [if_pos (by omega), if_pos rfl]
  · have hkj : k ≠ j := by omega
    rw [coeff_splitNth, coeff_monomial, coeff_monomial]
    rw [if_neg (by omega), if_neg hkj]

/-- Helper lemma: the even split of an odd monomial vanishes. -/
lemma splitNth_monomial_odd_even_zero (a : 𝔽) (k : ℕ) :
    splitNth (monomial (2 * k + 1) a) 2 0 = 0 := by
  ext j
  by_cases hdeg : 2 * k + 1 = j * 2
  · omega
  · simp [coeff_splitNth, coeff_monomial, hdeg]

/-- Definition: `foldNth n f β` is the linear combination of the n-way splits.

For a polynomial `f` split into `n` component polynomials
`splitNth f n 0, ..., splitNth f n (n-1)`,
this recombines them using powers of `β`:
`foldNth n f β = ∑ i : Fin n, C (β ^ i) * splitNth f n i`

This is the core operation in FRI-style polynomial commitment schemes. -/
noncomputable def foldNth (n : ℕ) (f : 𝔽[X]) (β : 𝔽) [NeZero n] : 𝔽[X] :=
  ∑ i : Fin n, C (β ^ i.val) * splitNth f n i

lemma foldNth_eq_sum_splitNth {n : ℕ} [NeZero n] (f : 𝔽[X]) (β : 𝔽) :
    foldNth n f β = ∑ i : Fin n, C (β ^ i.val) * splitNth f n i := rfl

/-- The `n`-way fold has degree at most `f.natDegree / n`: each component `splitNth f n i`
has degree `≤ f.natDegree / n` (`splitNth_degree_le`), and scaling by the constant
`C (β ^ i)` and summing over `Fin n` does not increase the degree. -/
lemma foldNth_natDegree_le {n : ℕ} [NeZero n] (f : 𝔽[X]) (β : 𝔽) :
    (foldNth n f β).natDegree ≤ f.natDegree / n := by
  rw [foldNth_eq_sum_splitNth]
  apply natDegree_sum_le_of_forall_le
  intro i _
  calc (C (β ^ i.val) * splitNth f n i).natDegree
      ≤ (C (β ^ i.val)).natDegree + (splitNth f n i).natDegree := natDegree_mul_le
    _ = (splitNth f n i).natDegree := by simp [natDegree_C]
    _ ≤ f.natDegree / n := splitNth_degree_le

/-- Pointwise even/odd evaluation split for `n = 2`:
`f(y) = f₀(y²) + y · f₁(y²)` where `f₀ = splitNth f 2 0` (even part) and
`f₁ = splitNth f 2 1` (odd part). This is the reusable building block underlying the
`+`/`-` identities below. -/
lemma splitNth_two_eval (f : 𝔽[X]) (y : 𝔽) :
    f.eval y =
      (splitNth f 2 0).eval (y ^ 2) + y * (splitNth f 2 1).eval (y ^ 2) := by
  conv_lhs => rw [splitNth_def 2 f]
  rw [eval_finset_sum, Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, eval_mul, eval_X,
    one_mul, splitNth_eval_comp_pow]

/-- Lemma 2: Even evaluation identity

For any polynomial `f` and field element `x`,
`f(x) + f(-x) = 2 * (even part of f)(x²)`

where the "even part" is `splitNth f 2 0` — the sub-polynomial collecting all
coefficients of `f` at even-degree positions. -/
lemma splitNth_two_eval_add (f : 𝔽[X]) (x : 𝔽) :
    f.eval x + f.eval (-x) = 2 * (splitNth f 2 0).eval (x ^ 2) := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [splitNth_add]
    simp only [eval_add, Fin.isValue]
    rw [mul_add, ← hp, ← hq]
    ring
  | monomial n a =>
    rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
    · -- even case: n = 2k
      subst hk
      rw [splitNth_monomial_even]
      simp [eval_monomial]
      ring
    · -- odd case: n = 2k + 1
      subst hk
      rw [splitNth_monomial_odd_even_zero]
      simp [eval_monomial, pow_succ, pow_mul]

/-- Lemma 3: Odd evaluation identity

For any polynomial `f` and field element `x`,
`f(x) - f(-x) = 2 * x * (odd part of f)(x²)`

where the "odd part" is `splitNth f 2 1` — collecting coefficients at odd positions. -/
lemma splitNth_two_eval_sub (f : 𝔽[X]) (x : 𝔽) :
    f.eval x - f.eval (-x) = 2 * x * (splitNth f 2 1).eval (x ^ 2) := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [splitNth_add]
    simp only [eval_add, Fin.isValue]
    rw [mul_add, ← hp, ← hq]
    ring
  | monomial n a =>
    rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
    · -- even case: contributes 0 to the odd part
      subst hk
      rw [splitNth_monomial_even_odd_zero]
      simp [eval_monomial]
    · -- odd case: n = 2k+1
      subst hk
      rw [splitNth_monomial_odd]
      simp [eval_monomial, pow_succ]
      ring

/-- Lemma 4: FRI folding evaluation

The main result: `foldNth 2 f β` evaluated at `x²` equals the standard
FRI fold formula in terms of `f(x)` and `f(-x)`. -/
lemma foldNth_two_eval (f : 𝔽[X]) (x β : 𝔽)
    (hx : x ≠ 0) (h2 : (2 : 𝔽) ≠ 0) :
    (foldNth 2 f β).eval (x ^ 2) =
    (f.eval x + f.eval (-x) +
      β * (f.eval x - f.eval (-x)) * x⁻¹) * (2 : 𝔽)⁻¹ := by
  rw [foldNth_eq_sum_splitNth]
  simp only [Fin.sum_univ_two, eval_add, eval_mul, eval_C]
  norm_num
  rw [splitNth_two_eval_add f x, splitNth_two_eval_sub f x]
  field_simp [hx, h2]

end Polynomial
