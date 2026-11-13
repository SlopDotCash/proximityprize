/-
Copyright (c) 2026 arseniybasedgod. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in
LICENSE-MIT and LICENSE.
Authors: arseniybasedgod
-/
import ArkLib.Research.ProximityGap.Frontier._IsoSparsityMasonStothers
import ArkLib.Data.Polynomial.SplitFold

/-!
# The sharp degree-only isolated-root bound

The named `IsolatedNonCosetCountResidual` bounds roots of `A² - X O²` by `k + 1`
under the degree bounds `natDegree A, natDegree O < k`. Its existing refutation
supplies five roots at `k = 3`. Here the unrestricted degree-only problem is
settled for every `k`: the universal bound is `2 k - 1`, and a rational family
attains it for every positive `k`. Consequently the recorded residual over `ℚ`
holds exactly for `k ≤ 2`.

The witnesses reuse `Polynomial.splitNth`: split the polynomial with roots
`1, ..., 2 k - 1` into its even and odd parts. Its positive roots give isolated
roots at their squares. Its values at the corresponding negative integers are
nonzero, so none of the odd parts vanish at those squares.
At `k = 3`, the halves are the common negatives of the existing rational
witnesses in `_IsolatedNonCosetCountResidualRefuted.lean`; the new result is
the sharp family and classification for all dimensions.

This classifies the recorded degree-only statement. It does not bound the
high-head/low-tail subgroup problem, discharge the Kelley/BGK input, or close
the production Proximity Prize claim tracked historically by issue #164.
-/

set_option autoImplicit false

noncomputable section

open Polynomial

namespace ProximityGap.Frontier.IsoSparsityMasonStothers

/-- The odd degree of `X O²` prevents cancellation with the square `A²`. -/
theorem isoPoly_ne_zero {F : Type*} [Field F] (A O : F[X]) (hO : O ≠ 0) :
    isoPoly A O ≠ 0 := by
  intro h
  have heq : A ^ 2 = X * O ^ 2 := sub_eq_zero.mp h
  have hdeg := congrArg Polynomial.natDegree heq
  rw [natDegree_pow, natDegree_mul X_ne_zero (pow_ne_zero _ hO), natDegree_X,
    natDegree_pow] at hdeg
  omega

/-- Degree bounds on both halves give the universal `2 k - 1` root bound. -/
theorem isolated_roots_card_le {F : Type*} [Field F] (k : ℕ) (A O : F[X])
    (hA : A.natDegree < k) (hO : O.natDegree < k) (s : Finset F)
    (hs : ∀ x ∈ s, (isoPoly A O).IsRoot x ∧ O.eval x ≠ 0) :
    s.card ≤ 2 * k - 1 := by
  classical
  by_cases hempty : s = ∅
  · simp [hempty]
  obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  have hOn : O ≠ 0 := by
    intro hzero
    simpa [hzero] using (hs x hx).2
  have hdegree : (isoPoly A O).natDegree ≤ 2 * k - 1 := by
    apply (natDegree_sub_le (A ^ 2) (X * O ^ 2)).trans
    apply max_le
    · rw [natDegree_pow]
      omega
    · rw [natDegree_mul X_ne_zero (pow_ne_zero _ hOn), natDegree_X, natDegree_pow]
      omega
  apply le_trans ?_ hdegree
  apply Polynomial.card_le_degree_of_subset_roots
  intro y hy
  exact (Polynomial.mem_roots (isoPoly_ne_zero A O hOn)).mpr (hs y hy).1

private def rootPolynomial (k : ℕ) : ℚ[X] :=
  ∏ i ∈ Finset.range (2 * k - 1), (X - C (i + 1 : ℚ))

private def sharpA (k : ℕ) : ℚ[X] := splitNth (rootPolynomial k) 2 0

private def sharpO (k : ℕ) : ℚ[X] := -splitNth (rootPolynomial k) 2 1

private theorem rootPolynomial_degree (k : ℕ) :
    (rootPolynomial k).natDegree = 2 * k - 1 := by
  unfold rootPolynomial
  rw [natDegree_prod_of_monic _ _ (fun (i : ℕ) _ ↦ monic_X_sub_C (i + 1 : ℚ))]
  simp only [natDegree_X_sub_C, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]

private theorem sharp_degrees (k : ℕ) (hk : 0 < k) :
    (sharpA k).natDegree < k ∧ (sharpO k).natDegree < k := by
  have ha := splitNth_degree_le (f := rootPolynomial k) (n := 2) (i := (0 : Fin 2))
  have ho := splitNth_degree_le (f := rootPolynomial k) (n := 2) (i := (1 : Fin 2))
  rw [rootPolynomial_degree] at ha ho
  constructor
  · exact lt_of_le_of_lt ha (by omega)
  · simpa [sharpO] using lt_of_le_of_lt ho (by omega : (2 * k - 1) / 2 < k)

private theorem sharp_eval (k : ℕ) (x : ℚ) :
    (rootPolynomial k).eval x =
      (sharpA k).eval (x ^ 2) - x * (sharpO k).eval (x ^ 2) := by
  simpa [sharpA, sharpO] using splitNth_two_eval (rootPolynomial k) x

private theorem sharp_root (k i : ℕ) (hi : i < 2 * k - 1) :
    (isoPoly (sharpA k) (sharpO k)).IsRoot ((i + 1 : ℚ) ^ 2) ∧
      (sharpO k).eval ((i + 1 : ℚ) ^ 2) ≠ 0 := by
  have hpos : (rootPolynomial k).eval (i + 1 : ℚ) = 0 := by
    simp only [rootPolynomial, eval_prod, eval_sub, eval_X, eval_C]
    apply Finset.prod_eq_zero (Finset.mem_range.mpr hi)
    simp
  have hneg : (rootPolynomial k).eval (-(i + 1 : ℚ)) ≠ 0 := by
    simp only [rootPolynomial, eval_prod, eval_sub, eval_X, eval_C]
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    have hi0 : (0 : ℚ) < i + 1 := by positivity
    have hj0 : (0 : ℚ) < j + 1 := by positivity
    linarith
  rw [sharp_eval] at hpos hneg
  have heq : (sharpA k).eval ((i + 1 : ℚ) ^ 2) =
      (i + 1 : ℚ) * (sharpO k).eval ((i + 1 : ℚ) ^ 2) := sub_eq_zero.mp hpos
  constructor
  · simp only [IsRoot.def, isoPoly, eval_sub, eval_pow, eval_mul, eval_X]
    rw [heq]
    ring
  · intro ho
    apply hneg
    simp only [neg_sq] at *
    rw [heq, ho]
    ring

/-- Every positive dimension attains `2 k - 1` isolated roots over `ℚ`. -/
theorem exists_sharp_isolated_roots (k : ℕ) (hk : 0 < k) :
    ∃ (A O : ℚ[X]) (s : Finset ℚ),
      A.natDegree < k ∧ O.natDegree < k ∧ s.card = 2 * k - 1 ∧
        ∀ x ∈ s, (isoPoly A O).IsRoot x ∧ O.eval x ≠ 0 := by
  classical
  let f : ℕ → ℚ := fun i ↦ (i + 1 : ℚ) ^ 2
  have hf : Function.Injective f := by
    intro i j hij
    have hsum : (i + 1 : ℚ) = j + 1 :=
      (sq_eq_sq₀ (by positivity) (by positivity)).mp hij
    have heq : (i : ℚ) = j := by linarith
    exact_mod_cast heq
  refine ⟨sharpA k, sharpO k, (Finset.range (2 * k - 1)).image f,
    (sharp_degrees k hk).1, (sharp_degrees k hk).2, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hf, Finset.card_range]
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact sharp_root k i (Finset.mem_range.mp hi)

/-- The recorded rational degree-only residual holds exactly below dimension three. -/
theorem isolatedNonCosetCountResidual_rat_iff (k : ℕ) :
    IsolatedNonCosetCountResidual ℚ k ↔ k ≤ 2 := by
  constructor
  · intro h
    by_contra hk
    obtain ⟨A, O, s, hA, hO, hcard, hs⟩ := exists_sharp_isolated_roots k (by omega)
    have hbound := h A O hA hO s hs
    omega
  · intro hk A O hA hO s hs
    have hbound := isolated_roots_card_le k A O hA hO s hs
    omega

#print axioms isoPoly_ne_zero
#print axioms isolated_roots_card_le
#print axioms exists_sharp_isolated_roots
#print axioms isolatedNonCosetCountResidual_rat_iff

end ProximityGap.Frontier.IsoSparsityMasonStothers
