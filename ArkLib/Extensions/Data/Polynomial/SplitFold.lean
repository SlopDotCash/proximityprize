/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.Data.Polynomial.SplitFold

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

omit [NoZeroDivisors 𝔽] in
/-- Coefficients of `splitNth` are the corresponding congruence-class coefficients of `f`. -/
lemma coeff_splitNth (f : 𝔽[X]) (n : ℕ) [NeZero n] (i : Fin n) (e : ℕ) :
    (splitNth f n i).coeff e = f.coeff (e * n + i.1) :=
  splitNth_coeff i e

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
          Polynomial.eval₂ Polynomial.C (Polynomial.X ^ n) (splitNth f n i) :=
  eq_sum_splitNth n f

/- Lemma bounding degree of each `n`-split polynomial. -/
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
noncomputable abbrev foldNth (n : ℕ) (f : 𝔽[X]) (β : 𝔽) [NeZero n] : 𝔽[X] :=
  FoldingPolynomial.polyFold f n β

lemma foldNth_eq_sum_splitNth {n : ℕ} [NeZero n] (f : 𝔽[X]) (β : 𝔽) :
    foldNth n f β = ∑ i : Fin n, C (β ^ i.val) * splitNth f n i :=
  polyFold_eq_sum_of_splitNth

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
