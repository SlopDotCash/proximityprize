/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib

/-!
# The revealed-variable root-counting step (issue #346, brick 17)

The probabilistic engine of [AGL24] Lemma 3.11: when the certificate argument "reveals"
`X_{i₀} = α_{i₀}` with all other variables already fixed, a polynomial that was nonzero
before the reveal vanishes for at most `degreeOf i₀ p` of the `≥ q − n` admissible values.

* `univariateSlice` — the one-variable slice of a multivariate polynomial at a point
  (every other variable evaluated, `X_{i₀}` kept);
* `eval_univariateSlice` — slicing commutes with evaluation: `slice.eval a = p.eval (α[i₀ ↦ a])`;
* `natDegree_univariateSlice_le` — the slice's degree is at most `degreeOf i₀ p`;
* `card_reveal_zero_le` — **the counting step**: if the slice is nonzero, at most
  `degreeOf i₀ p` reveal values zero the polynomial.
-/

open Finset Polynomial

namespace AGL24

variable {ι F : Type*} [DecidableEq ι] [Field F]

/-- The one-variable slice of `p` at the point `α`, keeping `X_{i₀}`. -/
noncomputable def univariateSlice (p : MvPolynomial ι F) (α : ι → F) (i₀ : ι) :
    Polynomial F :=
  MvPolynomial.aeval (fun i => if i = i₀ then Polynomial.X else Polynomial.C (α i)) p

/-- Slicing commutes with evaluation: evaluating the slice at `a` is evaluating `p` with
`i₀` updated to `a`. -/
theorem eval_univariateSlice (p : MvPolynomial ι F) (α : ι → F) (i₀ : ι) (a : F) :
    (univariateSlice p α i₀).eval a = MvPolynomial.eval (Function.update α i₀ a) p := by
  unfold univariateSlice
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => rw [map_add, map_add, Polynomial.eval_add, hp, hq]
  | mul_X p i hp =>
      rw [map_mul, map_mul, Polynomial.eval_mul, hp, MvPolynomial.aeval_X,
        MvPolynomial.eval_X]
      congr 1
      by_cases hi : i = i₀
      · subst hi
        rw [if_pos rfl, Polynomial.eval_X, Function.update_self]
      · rw [if_neg hi, Polynomial.eval_C, Function.update_of_ne hi]

/-- The slice's degree is bounded by the `i₀`-degree of `p`. -/
theorem natDegree_univariateSlice_le (p : MvPolynomial ι F) (α : ι → F) (i₀ : ι) :
    (univariateSlice p α i₀).natDegree ≤ MvPolynomial.degreeOf i₀ p := by
  classical
  have hsum : univariateSlice p α i₀
      = ∑ m ∈ p.support, (MvPolynomial.aeval
          (fun i => if i = i₀ then Polynomial.X else Polynomial.C (α i)))
          (MvPolynomial.monomial m (MvPolynomial.coeff m p)) := by
    unfold univariateSlice
    conv_lhs => rw [← MvPolynomial.support_sum_monomial_coeff p]
    rw [map_sum]
  rw [hsum]
  refine le_trans (Polynomial.natDegree_sum_le _ _) ?_
  rw [Finset.fold_max_le]
  refine ⟨Nat.zero_le _, fun m hm => ?_⟩
  simp only [Function.comp]
  -- Each monomial's slice is C·X^{m i₀}.
  rw [MvPolynomial.aeval_monomial]
  refine le_trans (Polynomial.natDegree_mul_le) ?_
  rw [show (algebraMap F (Polynomial F)) (MvPolynomial.coeff m p)
      = Polynomial.C (MvPolynomial.coeff m p) from rfl]
  rw [Polynomial.natDegree_C, zero_add]
  -- The finsupp product: split the i₀ factor out.
  have hprod : (m.prod fun i k =>
      (if i = i₀ then Polynomial.X else Polynomial.C (α i)) ^ k).natDegree ≤ m i₀ := by
    rw [Finsupp.prod]
    by_cases hi₀ : i₀ ∈ m.support
    · rw [← Finset.mul_prod_erase _ _ hi₀, if_pos rfl]
      refine le_trans (Polynomial.natDegree_mul_le) ?_
      have hX : (Polynomial.X ^ (m i₀) : Polynomial F).natDegree = m i₀ := by
        rw [Polynomial.natDegree_X_pow]
      rw [hX]
      have hrest : (∏ i ∈ m.support.erase i₀,
          (if i = i₀ then Polynomial.X else Polynomial.C (α i)) ^ (m i)).natDegree = 0 := by
        rw [show ∏ i ∈ m.support.erase i₀,
            (if i = i₀ then Polynomial.X else Polynomial.C (α i)) ^ (m i)
            = ∏ i ∈ m.support.erase i₀, Polynomial.C ((α i) ^ (m i)) from
          Finset.prod_congr rfl fun i hi => by
            rw [if_neg (Finset.ne_of_mem_erase hi), map_pow]]
        rw [← map_prod]
        exact Polynomial.natDegree_C _
      omega
    · -- i₀ not in the support: m i₀ = 0 and the product is constant.
      have hm0 : m i₀ = 0 := Finsupp.notMem_support_iff.mp hi₀
      have hconst : (∏ i ∈ m.support,
          (if i = i₀ then Polynomial.X else Polynomial.C (α i)) ^ (m i)).natDegree = 0 := by
        rw [show ∏ i ∈ m.support,
            (if i = i₀ then Polynomial.X else Polynomial.C (α i)) ^ (m i)
            = ∏ i ∈ m.support, Polynomial.C ((α i) ^ (m i)) from
          Finset.prod_congr rfl fun i hi => by
            rw [if_neg (fun h => hi₀ (by rw [← h]; exact hi)), map_pow]]
        rw [← map_prod]
        exact Polynomial.natDegree_C _
      omega
  refine le_trans hprod ?_
  -- m i₀ ≤ degreeOf i₀ p for m in the support.
  rw [MvPolynomial.degreeOf_eq_sup]
  exact Finset.le_sup (f := fun m => m i₀) hm

open scoped Classical in
/-- **The revealed-variable counting step** ([AGL24] Lemma 3.11's engine): if the slice at
`α` is nonzero, then at most `degreeOf i₀ p` reveal values `a ∈ S` zero the polynomial. -/
theorem card_reveal_zero_le (p : MvPolynomial ι F) (α : ι → F) (i₀ : ι) (S : Finset F)
    (hslice : univariateSlice p α i₀ ≠ 0) :
    (S.filter (fun a => MvPolynomial.eval (Function.update α i₀ a) p = 0)).card
      ≤ MvPolynomial.degreeOf i₀ p := by
  classical
  have hsubset : S.filter (fun a => MvPolynomial.eval (Function.update α i₀ a) p = 0)
      ⊆ (univariateSlice p α i₀).roots.toFinset := by
    intro a ha
    rw [Finset.mem_filter] at ha
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hslice]
    rw [Polynomial.IsRoot, eval_univariateSlice]
    exact ha.2
  calc (S.filter (fun a => MvPolynomial.eval (Function.update α i₀ a) p = 0)).card
      ≤ (univariateSlice p α i₀).roots.toFinset.card := Finset.card_le_card hsubset
  _ ≤ Multiset.card (univariateSlice p α i₀).roots := Multiset.toFinset_card_le _
  _ ≤ (univariateSlice p α i₀).natDegree := by
        have := Polynomial.card_roots' (univariateSlice p α i₀)
        exact this
  _ ≤ MvPolynomial.degreeOf i₀ p := natDegree_univariateSlice_le p α i₀

end AGL24

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms AGL24.eval_univariateSlice
#print axioms AGL24.natDegree_univariateSlice_le
#print axioms AGL24.card_reveal_zero_le
