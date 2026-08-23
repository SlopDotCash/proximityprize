/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Ring.Parity

/-!
# The char-free even/odd antipodal closure (#407)

Closes the **char-`p` deployment crux** of `(∗)_d`: the statement "all *odd* elementary symmetric
functions of `S` vanish ⟹ `S` is antipodal (`S = −S`)" was believed to need a char-free even/odd
*descent induction* (`σ_S = G(z²) + z·H(z²)`, force `H = 0`), the paper's char-uniformity difficulty.
It does not: `H = 0` **is** the hypothesis (the odd part of `σ_S` is exactly the odd symmetric
functions), and antipodality is then immediate from a one-step polynomial-parity argument.

The hypothesis "all odd `e_i(S) = 0`" is exactly "`σ_S(X) := ∏_{x∈S}(X − x)` is invariant under
`X ↦ −X`" (for `|S|` even, which the hypothesis forces since `e_{|S|} = ∏x ≠ 0`).  We take that
invariance as the hypothesis and conclude `S = −S`, **char-free**: no roots of unity, no Lam–Leung,
no Galois/Frobenius — for *any* finite subset of *any* field.

This upgrades the in-tree char-0 `LamLeungMultisetAntipodal.count_antipodal_of_sum_eq_zero`
(`e_1 = 0 ⟹` antipodal, via Lam–Leung) to char-free, using *all* odd `e_i` instead of just `e_1`.
Axiom-clean.  Issue #407.

## Mechanism
`σ_S(−X) = σ_S(X)` (the hypothesis) and `σ_S(−X)` evaluated at `x` is `σ_S(−x)`; so for `x ∈ S`,
`σ_S(−x) = σ_S(x) = 0`, hence `−x` is a root of `σ_S = ∏_{y∈S}(X − y)`, hence `−x ∈ S`.  Thus `S` is
closed under negation, and by cardinality `S.image (−·) = S`.
-/

open Polynomial

namespace ArkLib.ProximityGap.EvenOddAntipodal

variable {F : Type*} [Field F] [DecidableEq F]

/-- A polynomial has no odd-degree part. -/
def OddCoeffZero (P : F[X]) : Prop :=
  ∀ i : ℕ, Odd i → P.coeff i = 0

/-- A polynomial with zero odd coefficients is even as a function. -/
theorem eval_neg_eq_eval_of_oddCoeffZero {P : F[X]}
    (hOddCoeff : OddCoeffZero P) (z : F) :
    P.eval (-z) = P.eval z := by
  classical
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  by_cases hiOdd : Odd i
  · simp [hOddCoeff i hiOdd]
  · have hiEven : Even i := Nat.not_odd_iff_even.mp hiOdd
    rw [hiEven.neg_pow z]

/--
Evaluation-even form of the char-free closure.  This is the direct consumer of the
coefficient-level odd-part statement, independent of polynomial composition syntax.
-/
theorem image_neg_eq_of_prod_eval_even (S : Finset F)
    (h : ∀ z : F,
      (∏ x ∈ S, (X - C x)).eval (-z) = (∏ x ∈ S, (X - C x)).eval z) :
    S.image (fun x => -x) = S := by
  classical
  set P := ∏ x ∈ S, (X - C x) with hPdef
  have hclosed : ∀ x ∈ S, -x ∈ S := by
    intro x hx
    have hx0 : P.eval x = 0 := by
      rw [hPdef, eval_prod]
      exact Finset.prod_eq_zero hx (by simp)
    have hnegroot : P.eval (-x) = 0 := by
      rw [hPdef] at h
      rw [h x, hx0]
    rw [hPdef, eval_prod, Finset.prod_eq_zero_iff] at hnegroot
    obtain ⟨y, hy, hzero⟩ := hnegroot
    simp only [eval_sub, eval_X, eval_C] at hzero
    rw [sub_eq_zero.mp hzero]
    exact hy
  have hsub : S.image (fun x => -x) ⊆ S := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact hclosed x hx
  have hcard : (S.image (fun x => -x)).card = S.card :=
    Finset.card_image_of_injective S neg_injective
  exact Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard.symm)

/--
Coefficient-level version: if `∏_{x∈S}(X-C x)` has zero odd coefficients, then `S = -S`.
The Vieta/symmetric-function layer should prove this hypothesis from odd elementary-symmetric
vanishing; this theorem is the characteristic-free endpoint.
-/
theorem image_neg_eq_of_prod_oddCoeffZero (S : Finset F)
    (hOddCoeff : OddCoeffZero (∏ x ∈ S, (X - C x))) :
    S.image (fun x => -x) = S :=
  image_neg_eq_of_prod_eval_even S (eval_neg_eq_eval_of_oddCoeffZero hOddCoeff)

/-- **The char-free even/odd antipodal closure.**  For a finite set `S` of any field, if the
polynomial `∏_{x∈S}(X − x)` is invariant under `X ↦ −X` — equivalently, all *odd* elementary
symmetric functions of `S` vanish — then `S` is antipodal: `S = −S`.  Char-free; closes the char-`p`
crux of `(∗)_d`. -/
theorem image_neg_eq_of_prod_comp_neg (S : Finset F)
    (h : (∏ x ∈ S, (X - C x)).comp (-X) = ∏ x ∈ S, (X - C x)) :
    S.image (fun x => -x) = S := by
  classical
  set P := ∏ x ∈ S, (X - C x) with hPdef
  -- every `x ∈ S` forces `-x ∈ S`
  have hclosed : ∀ x ∈ S, -x ∈ S := by
    intro x hx
    have hx0 : P.eval x = 0 := by
      rw [hPdef, eval_prod]
      exact Finset.prod_eq_zero hx (by simp)
    have heq : (P.comp (-X)).eval x = P.eval (-x) := by
      rw [eval_comp]; congr 1; simp
    rw [h] at heq                      -- heq : P.eval x = P.eval (-x)
    have hnegroot : P.eval (-x) = 0 := by rw [← heq]; exact hx0
    rw [hPdef, eval_prod, Finset.prod_eq_zero_iff] at hnegroot
    obtain ⟨y, hy, hzero⟩ := hnegroot
    simp only [eval_sub, eval_X, eval_C] at hzero
    rw [sub_eq_zero.mp hzero]
    exact hy
  have hsub : S.image (fun x => -x) ⊆ S := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact hclosed x hx
  have hcard : (S.image (fun x => -x)).card = S.card :=
    Finset.card_image_of_injective S neg_injective
  exact Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard.symm)

end ArkLib.ProximityGap.EvenOddAntipodal

-- Axiom audit: must be `[propext, Classical.choice, Quot.sound]` only.
#print axioms ArkLib.ProximityGap.EvenOddAntipodal.eval_neg_eq_eval_of_oddCoeffZero
#print axioms ArkLib.ProximityGap.EvenOddAntipodal.image_neg_eq_of_prod_eval_even
#print axioms ArkLib.ProximityGap.EvenOddAntipodal.image_neg_eq_of_prod_oddCoeffZero
#print axioms ArkLib.ProximityGap.EvenOddAntipodal.image_neg_eq_of_prod_comp_neg
