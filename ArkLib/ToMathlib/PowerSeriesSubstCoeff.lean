/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-! # Coefficients of power-series substitutions and γ-truncation bookkeeping

This file collects clean, generic lemmas about `PowerSeries.subst` and `PowerSeries.coeff`
needed for the "γ-truncation" bookkeeping in the BCIKS20 Appendix-A list-decoding argument
(brick **L6** of the proximity-prize DAG).

The geometric situation is: `γ = PowerSeries.subst g (PowerSeries.mk α)` where `g` is a power
series with zero constant coefficient (in the application `g = X - x₀` as a power series, more
precisely the relevant shift series has positive *order*, so `g = X * h`).  Claims 5.8'/5.9 consume
two facts about such a `γ`:

* the degree-`< k` part of `γ` depends only on finitely many of the `α`-coefficients
  (`coeff_subst_eq_sum_range`, `coeff_subst_congr_of_coeff_eq`,
  `trunc_subst_eq_trunc_subst_coe_trunc`);
* if `α t = 0` for all `t ≥ k`, then `γ` *is* the substitution of a polynomial of degree `< k`,
  hence a truncation (`subst_eq_subst_coe_trunc_of_coeff_eq_zero`,
  `subst_eq_aeval_trunc_of_coeff_eq_zero`, `subst_mk_eq_aeval_trunc_of_tail_zero`), and the §5.9
  `degreeX P ≤ 1` / linear-in-`Z` reading is then a statement about that polynomial
  (`natDegree_trunc_mk_lt`).

All lemmas here are over an arbitrary base where substitution is legal: the substituted series `g`
satisfies `g.constantCoeff = 0` (equivalently `HasSubst g`, equivalently positive order), which is
exactly the BCIKS20 hypothesis on the shift series.  The substitution lemmas are stated for
`PowerSeries.subst` of a *univariate* target (`g : S⟦X⟧`), which is the form `γ` actually uses.
-/

set_option linter.style.longLine false

namespace ArkLib

open PowerSeries

section CoeffPow

variable {R : Type*} [CommRing R]

/-- A power series with zero constant coefficient has `n`-th coefficient of its `d`-th power equal
to zero whenever `n < d`: `g^d` has order `≥ d`. -/
theorem coeff_pow_eq_zero_of_lt_of_constantCoeff_zero
    {g : R⟦X⟧} (hg : constantCoeff (R := R) g = 0) {n d : ℕ} (hnd : n < d) :
    coeff n (g ^ d) = 0 := by
  apply coeff_of_lt_order
  calc (n : ℕ∞) < (d : ℕ∞) := by exact_mod_cast hnd
    _ ≤ (g ^ d).order := le_order_pow_of_constantCoeff_eq_zero d hg

/-- The `n`-th coefficient of `(X * h) ^ d` for `n < d` vanishes; the `g = X * h` packaging of the
positive-order hypothesis. -/
theorem coeff_X_mul_pow_eq_zero_of_lt
    (h : R⟦X⟧) {n d : ℕ} (hnd : n < d) :
    coeff n ((X * h) ^ d) = 0 :=
  coeff_pow_eq_zero_of_lt_of_constantCoeff_zero (by simp) hnd

end CoeffPow

section SubstCoeff

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]

/-- The coefficient-of-substitution finsum (`PowerSeries.coeff_subst'`), re-exposed in the
`ArkLib` namespace for the γ-bookkeeping. -/
theorem coeff_subst_eq_finsum {g : S⟦X⟧} (hg : HasSubst g) (f : R⟦X⟧) (n : ℕ) :
    coeff n (f.subst g) =
      finsum (fun d : ℕ => coeff d f • PowerSeries.coeff n (g ^ d)) :=
  coeff_subst' hg f n

/-- **Finite-support collapse.**  When the substituted series `g` has zero constant coefficient,
the coefficient of the substitution `coeff n (subst g f)` is a *finite* sum over `d ∈ range (n+1)`,
because the higher powers `g^d` (`d > n`) contribute zero.  This is the precise sense in which the
degree-`n` coefficient of `γ = subst g (mk α)` depends on only the first `n+1` coefficients of `f`
(here `f = mk α`). -/
theorem coeff_subst_eq_sum_range {g : S⟦X⟧} (hg : constantCoeff (R := S) g = 0) (f : R⟦X⟧) (n : ℕ) :
    coeff n (f.subst g) =
      ∑ d ∈ Finset.range (n + 1), coeff d f • PowerSeries.coeff n (g ^ d) := by
  classical
  rw [coeff_subst_eq_finsum (HasSubst.of_constantCoeff_zero' hg) f n]
  refine finsum_eq_sum_of_support_subset _ ?_
  intro d hd
  simp only [Function.mem_support, ne_eq] at hd
  simp only [Finset.coe_range, Set.mem_Iio]
  -- if `d ≥ n + 1`, then `n < d`, so `coeff n (g ^ d) = 0` and the term is zero, contradiction.
  by_contra hle
  exact hd (by rw [coeff_pow_eq_zero_of_lt_of_constantCoeff_zero hg (by omega), smul_zero])

/-- The degree-`n` coefficient of `subst g f` only sees the first `n+1` coefficients of `f`: if two
power series agree on `coeff 0 … coeff n`, their substitutions agree on `coeff n`. -/
theorem coeff_subst_congr_of_coeff_eq {g : S⟦X⟧} (hg : constantCoeff (R := S) g = 0) {f₁ f₂ : R⟦X⟧}
    {n : ℕ} (hf : ∀ d ≤ n, coeff d f₁ = coeff d f₂) :
    coeff n (f₁.subst g) = coeff n (f₂.subst g) := by
  rw [coeff_subst_eq_sum_range hg f₁ n, coeff_subst_eq_sum_range hg f₂ n]
  refine Finset.sum_congr rfl ?_
  intro d hd
  rw [Finset.mem_range] at hd
  rw [hf d (by omega)]

end SubstCoeff

section SubstTrunc

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]

/-- **Truncation commutes with substitution (coefficientwise).**  For `g` with zero constant
coefficient, the degree-`< k` coefficients of `subst g f` equal those of `subst g (trunc k f)`:
the truncated `γ` depends only on the first `k` coefficients of `f = mk α`. -/
theorem coeff_subst_eq_coeff_subst_coe_trunc {g : S⟦X⟧} (hg : constantCoeff (R := S) g = 0) (f : R⟦X⟧)
    {k n : ℕ} (hn : n < k) :
    coeff n (f.subst g) = coeff n (((trunc k f : Polynomial R) : R⟦X⟧).subst g) := by
  refine coeff_subst_congr_of_coeff_eq hg ?_
  intro d hd
  rw [Polynomial.coeff_coe, coeff_trunc, if_pos (by omega)]

/-- **Truncation commutes with substitution.**  For `g` with zero constant coefficient, the
length-`k` truncation of `subst g f` equals the length-`k` truncation of `subst g (trunc k f)`.
Equivalently, the degree-`< k` part of `γ = subst g (mk α)` is computed from the polynomial
`trunc k (mk α)`, i.e. depends only on `α 0, …, α (k-1)`. -/
theorem trunc_subst_eq_trunc_subst_coe_trunc {g : S⟦X⟧} (hg : constantCoeff (R := S) g = 0) (f : R⟦X⟧)
    (k : ℕ) :
    trunc k (f.subst g) = trunc k (((trunc k f : Polynomial R) : R⟦X⟧).subst g) := by
  ext n
  rw [coeff_trunc, coeff_trunc]
  split_ifs with hn
  · exact coeff_subst_eq_coeff_subst_coe_trunc hg f hn
  · rfl

end SubstTrunc

section TailZero

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]

/-- If all coefficients of `f` of degree `≥ k` vanish, then `f` equals the coercion of its own
length-`k` truncation (a polynomial of degree `< k`).  This is the power-series identity behind
"the truncated `γ` is a polynomial of the stated degree". -/
theorem eq_coe_trunc_of_coeff_eq_zero {f : R⟦X⟧} {k : ℕ}
    (hf : ∀ t, k ≤ t → coeff t f = 0) :
    f = ((trunc k f : Polynomial R) : R⟦X⟧) := by
  ext n
  rw [Polynomial.coeff_coe, coeff_trunc]
  split_ifs with hn
  · rfl
  · exact (hf n (by omega))

/-- **Tail-vanishing ⟹ substitution of a polynomial.**  If `α t = 0` for all `t ≥ k`, then
`γ = subst g f` equals `subst g (trunc k f)`, i.e. the substitution of an explicit polynomial of
degree `< k`.  This is the power-series side of Claim 5.8' (the truncation) packaged so
Claim 5.9 can read `degreeX P ≤ 1` off the polynomial `trunc k f`. -/
theorem subst_eq_subst_coe_trunc_of_coeff_eq_zero {g : S⟦X⟧} {f : R⟦X⟧} {k : ℕ}
    (hf : ∀ t, k ≤ t → coeff t f = 0) :
    f.subst g = ((trunc k f : Polynomial R) : R⟦X⟧).subst g := by
  conv_lhs => rw [eq_coe_trunc_of_coeff_eq_zero hf]

/-- The substitution of a polynomial `p` into `g` is the polynomial-`aeval` of `g`, so
`subst g (trunc k f)` is literally `Polynomial.aeval g (trunc k f)`.  Combined with
`subst_eq_subst_coe_trunc_of_coeff_eq_zero`, this exhibits `γ` (under tail-vanishing) as a finite
algebraic expression in `g` with polynomial coefficients drawn from `α 0, …, α (k-1)`. -/
theorem subst_coe_trunc_eq_aeval {g : S⟦X⟧} (hg : HasSubst g) (f : R⟦X⟧) (k : ℕ) :
    ((trunc k f : Polynomial R) : R⟦X⟧).subst g = Polynomial.aeval g (trunc k f) :=
  subst_coe hg (trunc k f)

/-- **Tail-vanishing ⟹ `γ` is `aeval` of the truncation polynomial.**  Composite of the previous
two lemmas, in the single form most useful downstream: if `coeff t f = 0` for `t ≥ k`, then
`subst g f = Polynomial.aeval g (trunc k f)`. -/
theorem subst_eq_aeval_trunc_of_coeff_eq_zero {g : S⟦X⟧} (hg : HasSubst g) {f : R⟦X⟧} {k : ℕ}
    (hf : ∀ t, k ≤ t → coeff t f = 0) :
    f.subst g = Polynomial.aeval g (trunc k f) := by
  rw [subst_eq_subst_coe_trunc_of_coeff_eq_zero hf, subst_coe_trunc_eq_aeval hg]

end TailZero

section MkApplication

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]

/-- The application-shaped restatement of `eq_coe_trunc_of_coeff_eq_zero` for `f = mk α`: if
`α t = 0` for all `t ≥ k`, then `mk α` is the polynomial `trunc k (mk α)`. -/
theorem mk_eq_coe_trunc_of_tail_zero {α : ℕ → R} {k : ℕ} (hα : ∀ t, k ≤ t → α t = 0) :
    (mk α) = ((trunc k (mk α) : Polynomial R) : R⟦X⟧) :=
  eq_coe_trunc_of_coeff_eq_zero (by simpa [coeff_mk] using hα)

/-- The application-shaped restatement of `subst_eq_aeval_trunc_of_coeff_eq_zero` for the actual
`γ = subst g (mk α)`: if `α t = 0` for all `t ≥ k`, then
`γ = Polynomial.aeval g (trunc k (mk α))`, the `aeval` of an explicit degree-`< k` polynomial whose
coefficients are exactly `α 0, …, α (k-1)`.  This is precisely the form Claims 5.8'/5.9 consume
(`degreeX P ≤ 1` is then a statement about `trunc k (mk α)`). -/
theorem subst_mk_eq_aeval_trunc_of_tail_zero {g : S⟦X⟧} (hg : HasSubst g) {α : ℕ → R} {k : ℕ}
    (hα : ∀ t, k ≤ t → α t = 0) :
    (mk α).subst g = Polynomial.aeval g (trunc k (mk α)) :=
  subst_eq_aeval_trunc_of_coeff_eq_zero hg (by simpa [coeff_mk] using hα)

/-- The truncation polynomial of `mk α` has `natDegree < k` (for `k > 0`): the explicit degree
bound on the polynomial extracted above. -/
theorem natDegree_trunc_mk_lt {α : ℕ → R} {k : ℕ} (hk : 0 < k) :
    (trunc k (mk α)).natDegree < k := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  exact natDegree_trunc_lt (mk α) j

/-- The `n`-th polynomial coefficient of `trunc k (mk α)` is `α n` for `n < k`, and `0` otherwise:
the truncation polynomial's coefficients are exactly the first `k` entries of `α`. -/
theorem coeff_trunc_mk (α : ℕ → R) (k n : ℕ) :
    (trunc k (mk α)).coeff n = if n < k then α n else 0 := by
  rw [coeff_trunc, coeff_mk]

/-- **The §5.9 power-series side: the truncated `γ`-numerator is linear.**  If `α t = 0` for all
`t ≥ 2`, then the truncation polynomial `trunc k (mk α)` (for any `k`) is the linear polynomial
`C (α 0) + C (α 1) * X`; in particular its `natDegree ≤ 1`.  This is exactly the "linear in the
coefficient variable / `degreeX P ≤ 1`" bookkeeping that Claim 5.9 reads off the truncation. -/
theorem trunc_mk_eq_linear_of_tail_zero {α : ℕ → R} {k : ℕ} (hk : 2 ≤ k)
    (hα : ∀ t, 2 ≤ t → α t = 0) :
    (trunc k (mk α) : Polynomial R) = Polynomial.C (α 0) + Polynomial.C (α 1) * Polynomial.X := by
  ext n
  rw [coeff_trunc_mk, Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul,
    Polynomial.coeff_X]
  rcases n with _ | _ | n
  · simp [show (0 : ℕ) < k by omega]
  · simp [show (1 : ℕ) < k by omega]
  · rw [hα (n + 1 + 1) (by omega)]
    simp

/-- The truncated `γ`-numerator has `natDegree ≤ 1` once the `α`-tail vanishes from index `2` on:
the explicit degree bound feeding Claim 5.9's `degreeX P ≤ 1`. -/
theorem natDegree_trunc_mk_le_one_of_tail_zero {α : ℕ → R} {k : ℕ} (hk : 2 ≤ k)
    (hα : ∀ t, 2 ≤ t → α t = 0) :
    (trunc k (mk α)).natDegree ≤ 1 := by
  rw [trunc_mk_eq_linear_of_tail_zero hk hα]
  apply le_trans (Polynomial.natDegree_add_le _ _)
  simp only [Polynomial.natDegree_C, max_le_iff, Nat.zero_le, true_and]
  exact le_trans (Polynomial.natDegree_C_mul_le _ _) Polynomial.natDegree_X_le

end MkApplication

end ArkLib

#print axioms ArkLib.coeff_pow_eq_zero_of_lt_of_constantCoeff_zero
#print axioms ArkLib.coeff_subst_eq_sum_range
#print axioms ArkLib.coeff_subst_congr_of_coeff_eq
#print axioms ArkLib.coeff_subst_eq_coeff_subst_coe_trunc
#print axioms ArkLib.trunc_subst_eq_trunc_subst_coe_trunc
#print axioms ArkLib.eq_coe_trunc_of_coeff_eq_zero
#print axioms ArkLib.subst_eq_subst_coe_trunc_of_coeff_eq_zero
#print axioms ArkLib.subst_eq_aeval_trunc_of_coeff_eq_zero
#print axioms ArkLib.subst_mk_eq_aeval_trunc_of_tail_zero
#print axioms ArkLib.mk_eq_coe_trunc_of_tail_zero
#print axioms ArkLib.natDegree_trunc_mk_lt
#print axioms ArkLib.coeff_trunc_mk
#print axioms ArkLib.coeff_X_mul_pow_eq_zero_of_lt
#print axioms ArkLib.trunc_mk_eq_linear_of_tail_zero
#print axioms ArkLib.natDegree_trunc_mk_le_one_of_tail_zero
