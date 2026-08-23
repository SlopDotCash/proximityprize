/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.Algebra.MvPolynomial.Coeff
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Data.Nat.Prime.Factorial
import ArkLib.Data.CodingTheory.ProximityGap.SubsetSumRadiusOne

/-!
# Polynomial Infrastructure for the General Erdős–Heilbronn / Dias da Silva–Hamidoune Bound

This module generalizes the $h = 2$ Erdős–Heilbronn restricted sumset bound (formalized in
`ArkLib.ToMathlib.RestrictedSumset`) to general subset size $h \ge 1$. This generalization
is known as the **Dias da Silva–Hamidoune theorem**.

For a field $\mathbb{F}$ of prime characteristic $p$, a finite subset
$A \subseteq \mathbb{F}$ with $n := |A|$, and $1 \le h \le n$ with $h(n - h) < p$, the set
of $h$-subset sums
$$\Sigma_h(A) := \left\{ \sum_{a \in S} a : S \subseteq A, |S| = h \right\}$$
has cardinality at least $h(n - h) + 1$.

## Algebraic Strategy (Alon–Nathanson–Ruzsa)

We proceed via Alon's Combinatorial Nullstellensatz. Suppose for contradiction that
$|\Sigma_h(A)| \le h(n - h)$. We pad $\Sigma_h(A)$ to a set $C'$ of cardinality exactly
$m := h(n - h)$ and define the $h$-variable polynomial:
$$Q(X_0, \dots, X_{h-1}) := \left(\prod_{0 \le i < j < h} (X_j - X_i)\right)
  \prod_{c \in C'} \left(\left(\sum_{k=0}^{h-1} X_k\right) - c\right)$$
which is the product of the Vandermonde determinant and the padded sumset linear factors.

By construction, $Q$ vanishes identically on $A^h$:
- If two coordinates are equal, the Vandermonde factor vanishes.
- If all coordinates are distinct, the sum of the coordinates is in
  $\Sigma_h(A) \subseteq C'$, so one of the sumset factors vanishes.

The total degree of $Q$ is $\binom{h}{2} + h(n - h)$. We target the monomial
$t = \prod_{i=0}^{h-1} X_i^{n-1-i}$.
The coefficient of $t$ in $Q$ corresponds to its coefficient in the leading homogeneous part:
$$V(X) \cdot \left(\sum_{k=0}^{h-1} X_k\right)^m$$
Expanding this via the determinant representation of the Vandermonde polynomial yields the
alternating sum:
$$\text{coeff}_t = \sum_{\sigma \in \mathfrak{S}_h} \text{sign}(\sigma)
  \cdot \text{multinomial}(t - \text{permExp}(\sigma))$$

This is evaluated in closed form as:
$$\prod_{k=0}^{h-1} (t_k)! \cdot \text{coeff}_t \left[ V(X) \cdot \left(\sum_k X_k\right)^M
  \right] = M! \cdot \det\left(\text{vandermonde}(t_0, \dots, t_{h-1})\right)$$
Under the characteristic bounds, this expression is a $p$-adic unit, proving it is nonzero.
The theorem then
follows from the Combinatorial Nullstellensatz.
-/

namespace MvPolynomial

open scoped BigOperators
open Finsupp

section General

variable {F : Type*} [Field F] {h : ℕ}

/-! ### The Vandermonde polynomial and its permutation expansion -/

/-- The exponent vector of the monomial `∏_i X_{σ i}^{i}` appearing in the determinant expansion
of the Vandermonde polynomial. Its value at `k` is `σ⁻¹ k`. -/
noncomputable def permExp (σ : Equiv.Perm (Fin h)) : Fin h →₀ ℕ :=
  ∑ i : Fin h, Finsupp.single (σ i) (i : ℕ)

@[simp]
lemma permExp_apply (σ : Equiv.Perm (Fin h)) (k : Fin h) :
    permExp σ k = (σ.symm k : ℕ) := by
  rw [permExp, Finsupp.finset_sum_apply]
  rw [Finset.sum_eq_single (σ.symm k)]
  · rw [Equiv.apply_symm_apply, Finsupp.single_eq_same]
  · intro b _ hb
    rw [Finsupp.single_eq_of_ne]
    intro hcontra; apply hb
    rw [← Equiv.symm_apply_apply σ b, hcontra]
  · intro hk; exact absurd (Finset.mem_univ _) hk

/-- The Vandermonde polynomial `∏_{i < j} (X j - X i)`, realised as the determinant of the
Vandermonde matrix with `v i = X i`. -/
noncomputable def vdmX (h : ℕ) : MvPolynomial (Fin h) F :=
  (Matrix.vandermonde (fun i => (X i : MvPolynomial (Fin h) F))).det

/-- **Product form** of the Vandermonde polynomial. -/
lemma vdmX_eq_prod (h : ℕ) :
    vdmX (F := F) h
      = ∏ i : Fin h, ∏ j ∈ Finset.Ioi i, (X j - X i : MvPolynomial (Fin h) F) := by
  rw [vdmX, Matrix.det_vandermonde]

/-- **Permutation (determinant) form** of the Vandermonde polynomial. -/
lemma vdmX_eq_perm_sum (h : ℕ) :
    vdmX (F := F) h
      = ∑ σ : Equiv.Perm (Fin h),
          (Equiv.Perm.sign σ : ℤ) • monomial (permExp σ) (1 : F) := by
  rw [vdmX, Matrix.det_apply]
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  rw [permExp, monomial_sum_one]
  apply Finset.prod_congr rfl
  intro i _
  simp [Matrix.vandermonde_apply, X_pow_eq_monomial]

/-- The Vandermonde polynomial has total degree at most `C(h,2)`. -/
lemma totalDegree_vdmX_le (h : ℕ) :
    (vdmX (F := F) h).totalDegree ≤ h.choose 2 := by
  classical
  rw [vdmX_eq_prod]
  refine (totalDegree_finset_prod _ _).trans ?_
  have hstep : ∀ i : Fin h,
      (∏ j ∈ Finset.Ioi i, (X j - X i : MvPolynomial (Fin h) F)).totalDegree
        ≤ (Finset.Ioi i).card := by
    intro i
    refine (totalDegree_finset_prod _ _).trans ?_
    calc ∑ j ∈ Finset.Ioi i, (X j - X i : MvPolynomial (Fin h) F).totalDegree
        ≤ ∑ _j ∈ Finset.Ioi i, 1 := by
          apply Finset.sum_le_sum
          intro j _
          refine (totalDegree_sub _ _).trans ?_
          apply max_le <;> simp [totalDegree_X]
      _ = (Finset.Ioi i).card := by rw [Finset.sum_const, smul_eq_mul, mul_one]
  calc ∑ i : Fin h, (∏ j ∈ Finset.Ioi i, (X j - X i : MvPolynomial (Fin h) F)).totalDegree
      ≤ ∑ i : Fin h, (Finset.Ioi i).card := Finset.sum_le_sum (fun i _ => hstep i)
    _ = ∑ i : Fin h, (h - 1 - (i : ℕ)) := by
        apply Finset.sum_congr rfl; intro i _; rw [Fin.card_Ioi]
    _ = h.choose 2 := by
        have : ∑ i : Fin h, (h - 1 - (i : ℕ)) = ∑ i ∈ Finset.range h, i := by
          rw [Fin.sum_univ_eq_sum_range (fun i => h - 1 - i)]
          rw [← Finset.sum_range_reflect (fun i => h - 1 - i) h]
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.mem_range] at hi
          omega
        rw [this, Finset.sum_range_id, Nat.choose_two_right]

/-! ### The leading-part coefficient as an alternating multinomial sum -/

/-- **Core coefficient identity.** The coefficient of a monomial `t` in the leading part
`vdmX · (∑_k X k)^M` is the alternating sum, over permutations `σ`, of the multinomial coefficient
of the shifted exponent vector `t − permExp σ`. This is the determinant-of-binomials
(Frobenius / Vandermonde-in-factorials) form of the coefficient. -/
lemma coeff_vdmX_mul_sumPow (h M : ℕ) (t : Fin h →₀ ℕ) :
    coeff t (vdmX (F := F) h * (∑ k : Fin h, X k) ^ M)
      = ∑ σ : Equiv.Perm (Fin h), (Equiv.Perm.sign σ : ℤ) •
          (if permExp σ ≤ t then
            (if (t - permExp σ).sum (fun _ m => m) = M then ((t - permExp σ).multinomial : F)
             else 0)
           else 0) := by
  rw [vdmX_eq_perm_sum, Finset.sum_mul, coeff_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [smul_mul_assoc]
  rw [show coeff t ((Equiv.Perm.sign σ : ℤ) •
          ((monomial (permExp σ) (1 : F)) * (∑ k : Fin h, X k) ^ M))
        = (Equiv.Perm.sign σ : ℤ) •
          coeff t ((monomial (permExp σ) (1 : F)) * (∑ k : Fin h, X k) ^ M)
      from coeff_smul t _ _]
  congr 1
  rw [coeff_monomial_mul']
  by_cases hle : permExp σ ≤ t
  · rw [if_pos hle, if_pos hle, coeff_sum_X_pow_of_fintype, one_mul, Nat.cast_ite, Nat.cast_zero]
  · rw [if_neg hle, if_neg hle]

/-! ### Total degree bounds -/

/-- The sum of variables `∑_k X k` has total degree at most `1`. -/
lemma totalDegree_sumX_le (h : ℕ) :
    (∑ k : Fin h, X k : MvPolynomial (Fin h) F).totalDegree ≤ 1 := by
  refine (totalDegree_finsetSum_le ?_)
  intro i _
  simp [totalDegree_X]

/-- The power `(∑_k X k)^j` has total degree at most `j`. -/
lemma totalDegree_sumX_pow_le (h j : ℕ) :
    ((∑ k : Fin h, X k : MvPolynomial (Fin h) F) ^ j).totalDegree ≤ j := by
  calc ((∑ k : Fin h, X k : MvPolynomial (Fin h) F) ^ j).totalDegree
      ≤ j * (∑ k : Fin h, X k : MvPolynomial (Fin h) F).totalDegree := totalDegree_pow _ _
    _ ≤ j * 1 := by gcongr; exact totalDegree_sumX_le h
    _ = j := by ring

/-- The "diagonal" variable `y = ∑_k X k`. -/
noncomputable def ehY (h : ℕ) : MvPolynomial (Fin h) F := ∑ k : Fin h, X k

/-- **Leading-part difference bound.** The product `∏_{c ∈ s} (y - C c)` differs from `y^{|s|}`
by a polynomial of total degree at most `|s| - 1`. -/
lemma totalDegree_prod_sub_pow_le (s : Finset F) :
    ((∏ c ∈ s, (ehY h - C c)) - ehY h ^ s.card).totalDegree ≤ s.card - 1 := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s has hind =>
    rw [Finset.prod_cons, Finset.card_cons]
    have hdecomp :
        (ehY h - C a) * (∏ c ∈ s, (ehY h - C c)) - ehY h ^ (s.card + 1)
          = (ehY h - C a) * ((∏ c ∈ s, (ehY h - C c)) - ehY h ^ s.card)
            - C a * ehY h ^ s.card := by
      ring
    rw [hdecomp]
    refine (totalDegree_sub _ _).trans ?_
    apply max_le
    · rcases s.eq_empty_or_nonempty with rfl | hne
      · simp
      · refine (totalDegree_mul _ _).trans ?_
        have h1 : (ehY h - C a : MvPolynomial (Fin h) F).totalDegree ≤ 1 := by
          refine (totalDegree_sub _ _).trans ?_
          apply max_le
          · exact totalDegree_sumX_le h
          · simp [totalDegree_C]
        have hscard : 1 ≤ s.card := hne.card_pos
        calc (ehY h - C a : MvPolynomial (Fin h) F).totalDegree
              + ((∏ c ∈ s, (ehY h - C c)) - ehY h ^ s.card).totalDegree
            ≤ 1 + (s.card - 1) := by gcongr
          _ = s.card := by omega
    · refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_C, zero_add]
      exact totalDegree_sumX_pow_le h _

/-! ### The target monomial -/

/-- The target monomial exponent vector `t` with `t i = n - 1 - i`, of total degree `C(h,2) + m`
and with every per-variable degree `< n`. -/
noncomputable def ehTarget (h n : ℕ) : Fin h →₀ ℕ :=
  ∑ i : Fin h, Finsupp.single i (n - 1 - (i : ℕ))

@[simp]
lemma ehTarget_apply (h n : ℕ) (k : Fin h) : ehTarget h n k = n - 1 - (k : ℕ) := by
  rw [ehTarget, Finsupp.finset_sum_apply]
  rw [Finset.sum_eq_single k]
  · rw [Finsupp.single_eq_same]
  · intro b _ hb; rw [Finsupp.single_eq_of_ne (Ne.symm hb)]
  · intro hk; exact absurd (Finset.mem_univ _) hk

/-- The total degree of the target monomial is `C(h,2) + h(n - h)` when `h ≤ n`. -/
lemma ehTarget_degree {h n : ℕ} (hhn : h ≤ n) :
    (ehTarget h n).degree = h.choose 2 + h * (n - h) := by
  classical
  rw [Finsupp.degree_eq_sum]
  have hval : ∑ i : Fin h, (ehTarget h n) i = ∑ i : Fin h, (n - 1 - (i : ℕ)) := by
    apply Finset.sum_congr rfl; intro i _; rw [ehTarget_apply]
  rw [hval]
  -- `∑_{i:Fin h}(n-1-i) = ∑_{i∈range h}(n-1-i)`, a "staircase" sum.
  rw [Fin.sum_univ_eq_sum_range (fun i => n - 1 - i)]
  -- split `n-1-i = (n-h) + (h-1-i)` (valid for `i < h ≤ n`).
  have hsplit : ∑ i ∈ Finset.range h, (n - 1 - i)
      = ∑ i ∈ Finset.range h, ((n - h) + (h - 1 - i)) := by
    apply Finset.sum_congr rfl
    intro i hi; rw [Finset.mem_range] at hi; omega
  rw [hsplit, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]
  -- `∑_{i∈range h}(h-1-i) = ∑_{i∈range h} i = C(h,2)`.
  have hrefl : ∑ i ∈ Finset.range h, (h - 1 - i) = ∑ i ∈ Finset.range h, i := by
    rw [← Finset.sum_range_reflect (fun i => h - 1 - i) h]
    apply Finset.sum_congr rfl
    intro i hi; rw [Finset.mem_range] at hi; omega
  rw [hrefl, Finset.sum_range_id, Nat.choose_two_right]
  ring

/-- Every per-variable degree of the target monomial is `< n` when `1 ≤ n`. -/
lemma ehTarget_lt {h n : ℕ} (hn : 1 ≤ n) (k : Fin h) : ehTarget h n k < n := by
  rw [ehTarget_apply]; omega

/-! ### The Erdős–Heilbronn polynomial -/

/-- **The general Erdős–Heilbronn polynomial** for a padded sumset `C'`. -/
noncomputable def ehQ (h : ℕ) (Cset : Finset F) : MvPolynomial (Fin h) F :=
  vdmX h * ∏ c ∈ Cset, (ehY h - C c)

/-- `ehQ h Cset` differs from the leading part `vdmX h · y^{|Cset|}` by a polynomial of strictly
smaller total degree above the Vandermonde degree. -/
lemma coeff_ehQ_eq_leading {Cset : Finset F} {n : ℕ} (t : Fin h →₀ ℕ)
    (hCcard : Cset.card = h * (n - h))
    (htdeg : (vdmX (F := F) h).totalDegree + h * (n - h) ≤ t.degree) :
    coeff t (ehQ h Cset)
      = coeff t (vdmX (F := F) h * (∑ k : Fin h, X k) ^ (h * (n - h))) := by
  classical
  set m := h * (n - h) with hm
  set P' : MvPolynomial (Fin h) F := ∏ c ∈ Cset, (ehY h - C c) with hP'
  -- The difference `ehQ - vdmX·y^m = vdmX·(P' - y^m)`.
  have hQdiff : ehQ h Cset - (vdmX (F := F) h) * (∑ k : Fin h, X k) ^ m
      = vdmX h * (P' - ehY h ^ m) := by
    rw [ehQ, hP', show (∑ k : Fin h, X k : MvPolynomial (Fin h) F) = ehY h from rfl]
    ring
  -- The difference has coefficient `0` at `t`.
  have hcoeff0 : coeff t
      (ehQ h Cset - (vdmX (F := F) h) * (∑ k : Fin h, X k) ^ m) = 0 := by
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · -- `m = 0`: then `Cset = ∅`, so `P' = 1` and the difference is `0`.
      have hcard0 : Cset.card = 0 := by rw [hCcard, hm0]
      have hCempty : Cset = ∅ := Finset.card_eq_zero.mp hcard0
      have : P' - ehY h ^ m = 0 := by rw [hP', hCempty, hm0]; simp
      rw [hQdiff, this, mul_zero, coeff_zero]
    · -- `m ≥ 1`: a total-degree argument.
      apply coeff_eq_zero_of_totalDegree_lt
      rw [← Finsupp.degree_apply]
      refine lt_of_lt_of_le ?_ htdeg
      rw [hQdiff]
      refine lt_of_le_of_lt (totalDegree_mul _ _) ?_
      have h2 : (P' - ehY h ^ m : MvPolynomial (Fin h) F).totalDegree ≤ m - 1 := by
        rw [hP', ← hCcard]
        exact totalDegree_prod_sub_pow_le Cset
      calc (vdmX (F := F) h).totalDegree + (P' - ehY h ^ m).totalDegree
          ≤ (vdmX (F := F) h).totalDegree + (m - 1) := by gcongr
        _ < (vdmX (F := F) h).totalDegree + m := by omega
  rw [coeff_sub, sub_eq_zero] at hcoeff0
  rw [hcoeff0]

/-- `ehQ h Cset` has total degree at most `deg(vdmX) + |Cset|`. -/
lemma totalDegree_ehQ_le (Cset : Finset F) :
    (ehQ h Cset).totalDegree ≤ (vdmX (F := F) h).totalDegree + Cset.card := by
  rw [ehQ]
  refine (totalDegree_mul _ _).trans ?_
  have h2 : (∏ c ∈ Cset, (ehY h - C c) : MvPolynomial (Fin h) F).totalDegree ≤ Cset.card := by
    refine (totalDegree_finset_prod _ _).trans ?_
    calc ∑ c ∈ Cset, (ehY h - C c : MvPolynomial (Fin h) F).totalDegree
        ≤ ∑ _c ∈ Cset, 1 := by
          apply Finset.sum_le_sum
          intro c _
          refine (totalDegree_sub _ _).trans ?_
          apply max_le
          · exact totalDegree_sumX_le h
          · simp [totalDegree_C]
      _ = Cset.card := by rw [Finset.sum_const, smul_eq_mul, mul_one]
  gcongr

/-- `ehQ h Cset` vanishes at every point `s : Fin h → F` whose coordinates are not all distinct,
or whose coordinate sum lies in `Cset`. -/
lemma eval_ehQ_eq_zero {Cset : Finset F} (s : Fin h → F)
    (hdis : (¬ Function.Injective s) ∨ (∑ k, s k) ∈ Cset) :
    eval s (ehQ h Cset) = 0 := by
  classical
  rw [ehQ, eval_mul]
  rcases hdis with hni | hmem
  · -- a repeated coordinate kills the Vandermonde determinant
    have : eval s (vdmX (F := F) h) = 0 := by
      rw [vdmX, RingHom.map_det (eval s)]
      rw [Function.not_injective_iff] at hni
      obtain ⟨i, j, hij, hne⟩ := hni
      apply Matrix.det_zero_of_row_eq hne
      funext c
      change eval s (Matrix.vandermonde (fun i => (X i : MvPolynomial (Fin h) F)) i c) =
           eval s (Matrix.vandermonde (fun i => (X i : MvPolynomial (Fin h) F)) j c)
      rw [Matrix.vandermonde_apply, Matrix.vandermonde_apply, map_pow, map_pow, eval_X, eval_X, hij]
    rw [this, zero_mul]
  · have : eval s (∏ c ∈ Cset, (ehY h - C c) : MvPolynomial (Fin h) F) = 0 := by
      rw [eval_prod]
      apply Finset.prod_eq_zero hmem
      simp only [ehY, eval_sub, eval_sum, eval_X, eval_C, sub_self]
    rw [this, mul_zero]

/-! ### Closed form for the coefficient and its nonvanishing -/

/-- The sum of the permutation exponent vector is `C(h,2)`. -/
lemma sum_permExp (σ : Equiv.Perm (Fin h)) : ∑ k, permExp σ k = h.choose 2 := by
  have hk : ∑ k, permExp σ k = ∑ k, (σ.symm k : ℕ) := by
    apply Finset.sum_congr rfl; intro k _; rw [permExp_apply]
  rw [hk, Equiv.sum_comp σ.symm (fun i => (i : ℕ))]
  rw [Fin.sum_univ_eq_sum_range (fun i => i), Finset.sum_range_id, Nat.choose_two_right]

/-- **Per-permutation factorial/descending-factorial identity.** For a permutation `σ` with
`permExp σ ≤ t`, the product of factorials times the multinomial coefficient of `t − permExp σ`
equals `M!` times the product of descending factorials `∏_k (t_k)_{(σ⁻¹ k)}`. -/
lemma term_factorial (t : Fin h →₀ ℕ) (M : ℕ) (σ : Equiv.Perm (Fin h))
    (hsum : (∑ k, t k) = M + h.choose 2) (hle : permExp σ ≤ t) :
    (∏ k, (t k).factorial) * (t - permExp σ).multinomial
      = M.factorial * ∏ k, (t k).descFactorial (σ.symm k) := by
  classical
  have hsub : ∀ k, (t - permExp σ) k = t k - (σ.symm k : ℕ) := by
    intro k; rw [Finsupp.coe_tsub, Pi.sub_apply, permExp_apply]
  have hpt : ∀ k, (σ.symm k : ℕ) ≤ t k := by
    intro k; have := hle k; rwa [permExp_apply] at this
  have hsumd : ∑ k, (t - permExp σ) k = M := by
    have hadd : ∑ k, t k = ∑ k, permExp σ k + ∑ k, (t - permExp σ) k := by
      rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro k _
      rw [hsub, permExp_apply]; have := hpt k; omega
    rw [sum_permExp] at hadd; omega
  have hmeq : (t - permExp σ).multinomial = Nat.multinomial Finset.univ (t - permExp σ) :=
    Finsupp.multinomial_eq_of_support_subset (Finset.subset_univ _)
  have hspec : (∏ k, ((t - permExp σ) k).factorial) * (t - permExp σ).multinomial
      = M.factorial := by
    rw [hmeq]
    have hh := Nat.multinomial_spec (Finset.univ) (fun k => (t - permExp σ) k)
    rw [hsumd] at hh; exact hh
  have hfact : ∏ k, (t k).factorial
      = (∏ k, ((t - permExp σ) k).factorial) * ∏ k, (t k).descFactorial (σ.symm k) := by
    rw [← Finset.prod_mul_distrib]; apply Finset.prod_congr rfl
    intro k _; rw [hsub, Nat.factorial_mul_descFactorial (hpt k)]
  calc (∏ k, (t k).factorial) * (t - permExp σ).multinomial
      = ((∏ k, ((t - permExp σ) k).factorial) * ∏ k, (t k).descFactorial (σ.symm k))
          * (t - permExp σ).multinomial := by rw [hfact]
    _ = ((∏ k, ((t - permExp σ) k).factorial) * (t - permExp σ).multinomial)
          * ∏ k, (t k).descFactorial (σ.symm k) := by ring
    _ = M.factorial * ∏ k, (t k).descFactorial (σ.symm k) := by rw [hspec]

/-- **Generalised Vandermonde / descending-factorial determinant.** The determinant of the matrix
of descending factorials `[(t_k)_{(j)}]` equals the Vandermonde determinant `∏_{i<j}(t_j − t_i)`,
because the descending factorials are monic polynomials of degrees `0, …, h−1`. -/
lemma det_descFactorial_eq_vandermonde (t : Fin h → ℕ) :
    (Matrix.of (fun k j : Fin h => (((t k).descFactorial (j : ℕ) : ℕ) : F))).det
      = (Matrix.vandermonde (fun k => ((t k : ℕ) : F))).det := by
  rw [Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde (fun k => ((t k : ℕ) : F))
        (fun j => descPochhammer F j) (fun j => descPochhammer_natDegree F j)
        (fun j => monic_descPochhammer F j)]
  congr 1; ext k j
  rw [Matrix.of_apply, Matrix.of_apply, descPochhammer_eval_eq_descFactorial F (t k) j]

/-- The alternating sum `∑_σ sign σ • ∏_k N(k, σ⁻¹ k)` equals `det N`. -/
lemma sum_sign_prod_inv_eq_det (N : Matrix (Fin h) (Fin h) F) :
    ∑ σ : Equiv.Perm (Fin h), (Equiv.Perm.sign σ : ℤ) • ∏ k, N k (σ.symm k) = N.det := by
  rw [Matrix.det_apply]
  apply Finset.sum_congr rfl; intro σ _; congr 1
  rw [← Equiv.prod_comp σ (fun k => N k (σ.symm k))]
  apply Finset.prod_congr rfl; intro i _; rw [Equiv.symm_apply_apply]

/-- **Closed form for the leading-part coefficient.** For any exponent vector `t` with
`∑_k t_k = M + C(h,2)`,

  `(∏_k (t_k)!) · coeff t [vdmX · (∑ X)^M] = M! · det (vandermonde (fun k => t_k))`,

the right-hand determinant being the integer Vandermonde `∏_{i<j}(t_j − t_i)` cast into `F`. -/
lemma coeff_closed_form (t : Fin h →₀ ℕ) (M : ℕ)
    (hsum : (∑ k, t k) = M + h.choose 2) :
    (∏ k, ((t k).factorial : F)) * coeff t ((vdmX (F := F) h) * (∑ k : Fin h, X k) ^ M)
      = (M.factorial : F) * (Matrix.vandermonde (fun k => ((t k : ℕ) : F))).det := by
  classical
  rw [coeff_vdmX_mul_sumPow, Finset.mul_sum]
  rw [← det_descFactorial_eq_vandermonde (F := F) (fun k => t k)]
  rw [← sum_sign_prod_inv_eq_det, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  have hsumcond : permExp σ ≤ t → (t - permExp σ).sum (fun _ m => m) = M := by
    intro hle
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
    have hadd : ∑ k, t k = ∑ k, permExp σ k + ∑ k, (t - permExp σ) k := by
      rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro k _
      rw [Finsupp.coe_tsub, Pi.sub_apply]; have := hle k; omega
    rw [sum_permExp] at hadd; omega
  by_cases hle : permExp σ ≤ t
  · rw [if_pos hle, if_pos (hsumcond hle), mul_smul_comm, mul_smul_comm]
    congr 1
    have ht := term_factorial t M σ hsum hle
    have hcast : ((∏ k, (t k).factorial : ℕ) : F) * ((t - permExp σ).multinomial : F)
        = ((M.factorial : ℕ) : F) * ((∏ k, (t k).descFactorial (σ.symm k) : ℕ) : F) := by
      rw [← Nat.cast_mul, ← Nat.cast_mul, ht]
    push_cast at hcast
    rw [hcast]
    simp only [Matrix.of_apply]
  · rw [if_neg hle, smul_zero, mul_zero]
    have hex : ∃ k, t k < (σ.symm k : ℕ) := by
      by_contra hc
      push Not at hc
      exact hle (Finsupp.le_def.mpr (fun k => by have := hc k; rw [permExp_apply]; omega))
    obtain ⟨k, hk⟩ := hex
    have hzero :
        ∏ j, (Matrix.of (fun k j : Fin h =>
            (((t k).descFactorial (j : ℕ) : ℕ) : F))) j (σ.symm j) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ k)
      rw [Matrix.of_apply, Nat.descFactorial_eq_zero_iff_lt.mpr hk, Nat.cast_zero]
    rw [hzero, smul_zero, mul_zero]

/-- The cast factorial `(n! : F)` is nonzero when `n < p = ringChar F`. -/
lemma factorial_cast_ne_zero {p : ℕ} (hp : p.Prime) (hchar : ringChar F = p) {N : ℕ}
    (hN : N < p) : ((N.factorial : ℕ) : F) ≠ 0 := by
  haveI : CharP F p := hchar ▸ ringChar.charP F
  rw [Ne, CharP.cast_eq_zero_iff F p]
  intro hdvd
  have := (Nat.Prime.dvd_factorial hp).mp hdvd
  omega

/-- The Vandermonde determinant of the staircase `(n-1-k)` is nonzero in `F` when `h ≤ n ≤ p`. -/
lemma vandermonde_ehTarget_ne_zero {p : ℕ} (_hp : p.Prime) (hchar : ringChar F = p)
    {n : ℕ} (hhn : h ≤ n) (hnp : n ≤ p) :
    (Matrix.vandermonde (fun k : Fin h => (((n - 1 - (k : ℕ)) : ℕ) : F))).det ≠ 0 := by
  haveI : CharP F p := hchar ▸ ringChar.charP F
  rw [Matrix.det_vandermonde_ne_zero_iff]
  intro i j hij
  have hi : (n - 1 - (i : ℕ)) < p := by omega
  have hj : (n - 1 - (j : ℕ)) < p := by omega
  have hnat : (n - 1 - (i : ℕ)) = (n - 1 - (j : ℕ)) :=
    CharP.natCast_injOn_Iio F p (Set.mem_Iio.mpr hi) (Set.mem_Iio.mpr hj) hij
  exact Fin.ext (by omega)

/-- **Nonvanishing of the target coefficient.** Under `h ≤ n ≤ p` and `h(n - h) < p`, the
coefficient of the target monomial `t = ∏_i X_i^{n-1-i}` in the leading part is nonzero in `F`. -/
lemma coeff_ehTarget_ne_zero {p : ℕ} (hp : p.Prime) (hchar : ringChar F = p)
    {n : ℕ} (hhn : h ≤ n) (hnp : n ≤ p) (hm : h * (n - h) < p) :
    coeff (ehTarget h n) ((vdmX (F := F) h) * (∑ k : Fin h, X k) ^ (h * (n - h))) ≠ 0 := by
  classical
  -- the closed-form identity
  have hsum : (∑ k, (ehTarget h n) k) = h * (n - h) + h.choose 2 := by
    have hd : (ehTarget h n).degree = h.choose 2 + h * (n - h) := ehTarget_degree hhn
    rw [Finsupp.degree_eq_sum] at hd
    omega
  have cf := coeff_closed_form (F := F) (ehTarget h n) (h * (n - h)) hsum
  intro hzero
  rw [hzero, mul_zero] at cf
  have hfac : ((h * (n - h)).factorial : F) ≠ 0 := factorial_cast_ne_zero hp hchar hm
  have hdet : (Matrix.vandermonde (fun k : Fin h => (((ehTarget h n) k : ℕ) : F))).det ≠ 0 := by
    have hv := vandermonde_ehTarget_ne_zero (F := F) (h := h) hp hchar hhn hnp
    convert hv using 3
    funext k; rw [ehTarget_apply]
  exact (mul_ne_zero hfac hdet) cf.symm

end General

section Main

/- The `Fintype F` instance is required for cardinality bounds and padding steps. -/
set_option linter.unusedFintypeInType false

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The restricted `h`-sumset `Σ_h(A) = { ∑_{a ∈ S} a : S ⊆ A, |S| = h }`. -/
def restrictedSumset (A : Finset F) (h : ℕ) : Finset F :=
  (A.powersetCard h).image (fun S => ∑ a ∈ S, a)

omit [Fintype F] in
/-- For an injective tuple `s : Fin h → F` with all coordinates in `A`, the coordinate sum is an
`h`-subset sum. -/
lemma sum_mem_restrictedSumset {A : Finset F} {h : ℕ} {s : Fin h → F}
    (hinj : Function.Injective s) (hmem : ∀ k, s k ∈ A) :
    (∑ k, s k) ∈ restrictedSumset A h := by
  classical
  rw [restrictedSumset, Finset.mem_image]
  refine ⟨Finset.univ.image s, ?_, ?_⟩
  · rw [Finset.mem_powersetCard]
    refine ⟨?_, ?_⟩
    · intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨k, -, rfl⟩ := hx
      exact hmem k
    · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  · rw [Finset.sum_image (fun a _ b _ h => hinj h)]

/-- **General Erdős–Heilbronn / Dias da Silva–Hamidoune, modulo the coefficient nonvanishing.**

Let `F` be a finite field of prime characteristic `p`, `A : Finset F` with `n := |A|`, and
`1 ≤ h ≤ n`, `h(n - h) < p`. If the coefficient of the target monomial `t = ∏_i X_i^{n-1-i}` in the
leading part `vdmX · (∑ X)^{h(n-h)}` is nonzero in `F`, then

  `h(n - h) + 1 ≤ |Σ_h(A)|`.

The coefficient is exhibited in closed form by `coeff_vdmX_mul_sumPow`; its nonvanishing is the
classical Frobenius / Vandermonde-in-factorials arithmetic fact (a `± m!·∏(a_i−a_j)/∏ a_i!`
ballot number, nonzero mod `p` in the stated regime). -/
theorem erdos_heilbronn_of_coeff {p : ℕ} (hp : p.Prime) (hchar : ringChar F = p)
    (A : Finset F) (h : ℕ) (h1 : 1 ≤ h) (hhA : h ≤ A.card) (hsmall : h * (A.card - h) < p)
    (hcoeff : coeff (ehTarget h A.card)
        ((vdmX (F := F) h) * (∑ k : Fin h, X k) ^ (h * (A.card - h))) ≠ 0) :
    h * (A.card - h) + 1 ≤ (restrictedSumset A h).card := by
  classical
  set n := A.card with hncard
  set m := h * (n - h) with hm
  by_contra hcon
  push Not at hcon
  have hle : (restrictedSumset A h).card ≤ m := by omega
  -- Pad `Σ_h(A)` to a set `C'` of size exactly `m`.
  have hp_le_card : p ≤ Fintype.card F := by
    haveI : Fact p.Prime := ⟨hp⟩
    have hdvd : p ∣ Fintype.card F := by
      rw [← prime_dvd_char_iff_dvd_card (R := F) p, hchar]
    exact Nat.le_of_dvd Fintype.card_pos hdvd
  have hm_le_card : m ≤ Fintype.card F := le_trans (le_of_lt hsmall) hp_le_card
  obtain ⟨C', hC'sub, -, hC'card⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_univ (restrictedSumset A h)) hle (by rw [Finset.card_univ]; exact hm_le_card)
  set t := ehTarget h n with ht
  set f := ehQ h C' with hf
  -- coeff of `t` in `f` is nonzero (equals coeff in the leading part).
  have hdeg_t : t.degree = h.choose 2 + m := by rw [ht]; exact ehTarget_degree hhA
  have hle_deg : (vdmX (F := F) h).totalDegree + m ≤ t.degree := by
    rw [hdeg_t]
    have := totalDegree_vdmX_le (F := F) h
    omega
  have hcoeff_f : coeff t f ≠ 0 := by
    rw [hf, coeff_ehQ_eq_leading (n := n) t hC'card hle_deg]
    exact hcoeff
  -- total degree of `f` equals `t.degree`.
  have htotalDeg : f.totalDegree = t.degree := by
    refine le_antisymm ?_ ?_
    · rw [hdeg_t, hf]
      refine le_trans (totalDegree_ehQ_le C') ?_
      rw [hC'card]
      have := totalDegree_vdmX_le (F := F) h
      omega
    · have hmem : t ∈ f.support := mem_support_iff.mpr hcoeff_f
      rw [Finsupp.degree_apply]
      exact le_totalDegree (p := f) hmem
  -- degree condition `t i < #(S i) = n`.
  set S : Fin h → Finset F := fun _ => A with hS
  have htS : ∀ i, t i < (S i).card := by
    intro i
    rw [hS, ← hncard, ht]
    exact ehTarget_lt (by omega) i
  -- Apply the Combinatorial Nullstellensatz.
  obtain ⟨s, hsA, hsne⟩ := combinatorial_nullstellensatz_exists_eval_nonzero
    f t hcoeff_f htotalDeg S htS
  -- But `f` vanishes on `A^h`.
  apply hsne
  rw [hf]
  apply eval_ehQ_eq_zero
  by_cases hinj : Function.Injective s
  · refine Or.inr (hC'sub ?_)
    exact sum_mem_restrictedSumset hinj (fun k => hsA k)
  · exact Or.inl hinj

/-- **General Erdős–Heilbronn / Dias da Silva–Hamidoune theorem.**

Let `F` be a finite field whose characteristic `p := ringChar F` is prime, and `A : Finset F` with
`n := |A|`. For `1 ≤ h ≤ n`, `n ≤ p`, and `h(n - h) < p`, the restricted `h`-sumset

  `Σ_h(A) = { ∑_{a ∈ S} a : S ⊆ A, |S| = h }`

satisfies

  `h(n - h) + 1 ≤ |Σ_h(A)|`.

(For `h = 2` this is `erdos_heilbronn_two`; for general `h` it is the Dias da Silva–Hamidoune
theorem. The hypothesis `n ≤ p` is automatic when `F = ZMod p`.) -/
theorem erdos_heilbronn {p : ℕ} (hp : p.Prime) (hchar : ringChar F = p)
    (A : Finset F) (h : ℕ) (h1 : 1 ≤ h) (hhA : h ≤ A.card) (hnp : A.card ≤ p)
    (hsmall : h * (A.card - h) < p) :
    h * (A.card - h) + 1 ≤ (restrictedSumset A h).card :=
  erdos_heilbronn_of_coeff hp hchar A h h1 hhA hsmall
    (coeff_ehTarget_ne_zero hp hchar hhA hnp hsmall)

end Main

end MvPolynomial

/-!
## Reed–Solomon MCA Corollary at General Degree $k$

Combining the general Erdős–Heilbronn / Dias da Silva–Hamidoune bound ($h = k + 1$) with the
unconditional subset-sum lower bound `ProximityGap.epsMCA_one_ge_card_subsetSums` yields a
lower bound for the maximum correlation agreement
$\varepsilon_{\text{mca}}(\text{RS}[\mathbb{F}, \text{domain}, k], 1)$
with explicit additive content.
-/

namespace ProximityGap

open scoped BigOperators ENNReal

/- Suppress unused variable linters for the localized bridge variables. -/
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

section EHGeneral

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The restricted `(k+1)`-sumset of an injective evaluation domain's image is contained in the
`(k+1)`-subset-sum set of the domain. -/
lemma restrictedSumset_subset_subsetSumsKplus1 (domain : ι ↪ F) (k : ℕ) :
    MvPolynomial.restrictedSumset (Finset.image (fun i => domain i) Finset.univ) (k + 1)
      ⊆ subsetSumsKplus1 domain k := by
  classical
  intro γ hγ
  rw [MvPolynomial.restrictedSumset, Finset.mem_image] at hγ
  obtain ⟨S, hS, rfl⟩ := hγ
  rw [Finset.mem_powersetCard] at hS
  obtain ⟨hSsub, hScard⟩ := hS
  -- Each element of `S` is `domain i` for a unique `i`; pull `S` back to a subset `T ⊆ ι`.
  set T : Finset ι := Finset.univ.filter (fun i => domain i ∈ S) with hT
  have hTimage : T.image (fun i => domain i) = S := by
    apply Finset.Subset.antisymm
    · intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      rw [hT, Finset.mem_filter] at hi
      exact hi.2
    · intro x hx
      have := hSsub hx
      rw [Finset.mem_image] at this
      obtain ⟨i, -, rfl⟩ := this
      rw [Finset.mem_image]
      exact ⟨i, by rw [hT, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hx⟩, rfl⟩
  have hTcard : T.card = k + 1 := by
    have : (T.image (fun i => domain i)).card = T.card :=
      Finset.card_image_of_injective _ domain.injective
    rw [hTimage] at this
    omega
  rw [subsetSumsKplus1, Finset.mem_image]
  refine ⟨T, ?_, ?_⟩
  · rw [Finset.mem_powersetCard]; exact ⟨Finset.subset_univ _, hTcard⟩
  · rw [← hTimage, Finset.sum_image (fun a _ b _ hab => domain.injective hab)]

/-- The image of an injective `domain` has cardinality `n := |ι|`. -/
lemma card_image_domain' (domain : ι ↪ F) :
    (Finset.image (fun i => domain i) Finset.univ).card = Fintype.card ι := by
  rw [Finset.card_image_of_injective _ domain.injective, Finset.card_univ]

/-- **Erdős–Heilbronn / Dias da Silva–Hamidoune floor for `ε_mca(RS, 1)` at general `k`.**
For `RS[F, domain, k]` over a finite field `F` of prime characteristic `p`, with `n := |ι|`,
`k + 1 ≤ n ≤ p`, and `(k+1)(n - (k+1)) < p`:

  `ε_mca(RS[F, domain, k], 1) ≥ ((k+1)(n - k - 1) + 1) / q`. -/
theorem epsMCA_one_ge_erdos_heilbronn_general (domain : ι ↪ F) {p : ℕ} (hp : p.Prime)
    (hchar : ringChar F = p) {k : ℕ} (hk : k + 1 ≤ Fintype.card ι) (hnp : Fintype.card ι ≤ p)
    (hsmall : (k + 1) * (Fintype.card ι - (k + 1)) < p) :
    (((k + 1) * (Fintype.card ι - (k + 1)) + 1 : ℕ) : ENNReal) / (Fintype.card F : ENNReal) ≤
      epsMCA (F := F) (A := F) (ReedSolomon.code domain k : Set (ι → F)) 1 := by
  classical
  set n := Fintype.card ι with hn_def
  set A : Finset F := Finset.image (fun i => domain i) Finset.univ with hA
  have hAcard : A.card = n := card_image_domain' domain
  -- the general Erdős–Heilbronn bound at `h = k + 1`
  have hEH : (k + 1) * (n - (k + 1)) + 1
      ≤ (MvPolynomial.restrictedSumset A (k + 1)).card := by
    have := MvPolynomial.erdos_heilbronn (F := F) hp hchar A (k + 1) (by omega)
      (by rw [hAcard]; exact hk) (by rw [hAcard]; exact hnp) (by rw [hAcard]; exact hsmall)
    rwa [hAcard] at this
  have hsubset : (k + 1) * (n - (k + 1)) + 1 ≤ (subsetSumsKplus1 domain k).card :=
    le_trans hEH (Finset.card_le_card (restrictedSumset_subset_subsetSumsKplus1 domain k))
  have hfloor := epsMCA_one_ge_card_subsetSums (F := F) domain (k := k) (by omega)
  refine le_trans ?_ hfloor
  have hnum : (((k + 1) * (n - (k + 1)) + 1 : ℕ) : ENNReal)
      ≤ ((subsetSumsKplus1 domain k).card : ENNReal) := by exact_mod_cast hsubset
  exact ENNReal.div_le_div_right hnum _

end EHGeneral

end ProximityGap
