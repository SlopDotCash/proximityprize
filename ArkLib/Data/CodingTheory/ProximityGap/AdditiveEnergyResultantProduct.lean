/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib
import ArkLib.Data.CodingTheory.ProximityGap.AdditiveEnergyResultant

/-!
# The BGK resultant product formula (#232)

This file proves the clean product factorization of the resultant of `X^n - 1` and `(X+1)^n - 1`
over a field `F` that contains a primitive `n`-th root of unity. This is the BGK prize kernel
(#232): the resultant — which controls the additive-energy obstruction studied in
`AdditiveEnergyResultant` — is expressed as an explicit product over the `n`-th roots of unity.

## Main results

* `prod_one_add_mul_nthRootsFinset` — the **inner-product identity**
  `∏_{β ∈ μ_n} (1 + c·β) = 1 - (-1)^n · c^n`, obtained from
  `IsPrimitiveRoot.pow_sub_pow_eq_prod_sub_mul`. Clean and reusable.
* `resultant_X_pow_sub_one_eq_prod_eval` — `Res(X^n - 1, (X+1)^n - 1)` equals the product of the
  second polynomial evaluated over the `n`-th roots of unity, via Mathlib's
  `Polynomial.resultant_eq_prod_eval`.
* `resultant_X_pow_sub_one_eq_bgk_prod` — the **BGK product formula**
  `Res(X^n - 1, (X+1)^n - 1) = ∏_{γ ∈ μ_n} (1 - (-1)^n · (γ-1)^n)`, obtained by expanding each
  evaluation as a product over `μ_n` and reindexing `α = β·γ` using that `μ_n` is a group.
* `resultant_X_pow_sub_one_eq_bgk_prod_even` — for even `n`, `(-1)^n = 1`, so the formula simplifies
  to `Res = ∏_{γ ∈ μ_n} (1 - (γ-1)^n)`.
* `resultant_X_pow_sub_one_eq_zero_iff` — for even `n`, the resultant vanishes iff some `n`-th root
  of unity `γ` satisfies `(γ-1)^n = 1`, i.e. iff `γ - 1` is itself an `n`-th root of unity. This is
  exactly the BGK common-root / additive-energy obstruction of `AdditiveEnergyResultant`.

## Numeric sanity

The formula gives `Res = -3` for `n = 2` (over `μ_2 = {1, -1}`) and `Res = -375 = -3·5³` for
`n = 4` (over `μ_4 = {1, -1, i, -i}`), matching the classical values.

All results are axiom-clean.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open Finset Polynomial

namespace ArkLib.ProximityGap.AdditiveEnergyKernel

variable {F : Type*} [Field F] [DecidableEq F]

/-- **Inner-product identity over the `n`-th roots of unity.** For any `c : F`,
`∏_{β ∈ μ_n} (1 + c·β) = 1 - (-1)^n · c^n`. -/
theorem prod_one_add_mul_nthRootsFinset {n : ℕ} (hn : 0 < n) {ζ : F}
    (h : IsPrimitiveRoot ζ n) (c : F) :
    (∏ β ∈ nthRootsFinset n (1 : F), (1 + c * β)) = 1 - (-1) ^ n * c ^ n := by
  have key := h.pow_sub_pow_eq_prod_sub_mul (x := (1 : F)) (y := -c) hn
  rw [one_pow, neg_pow] at key
  rw [key]
  refine Finset.prod_congr rfl ?_
  intro β _
  ring

section Helpers

variable {n : ℕ}

/-- `X ^ n - 1` rewritten with `C` to match the monic / `nthRoots` lemmas. -/
theorem X_pow_sub_one_eq_X_pow_sub_C : (X ^ n - 1 : F[X]) = X ^ n - C 1 := by
  rw [map_one]

/-- The degree of `X ^ n - 1` is `n` (stated with `0 < n` for API symmetry with the
monic/splits lemmas below). -/
theorem natDegree_X_pow_sub_one (_hn : 0 < n) :
    (X ^ n - 1 : F[X]).natDegree = n := by
  rw [X_pow_sub_one_eq_X_pow_sub_C, natDegree_X_pow_sub_C]

/-- `X ^ n - 1` is monic (for `0 < n`). -/
theorem monic_X_pow_sub_one (hn : 0 < n) : (X ^ n - 1 : F[X]).Monic := by
  rw [X_pow_sub_one_eq_X_pow_sub_C]
  exact monic_X_pow_sub_C (1 : F) hn.ne'

/-- Given a primitive `n`-th root of unity, `X ^ n - 1` splits over `F`. -/
theorem splits_X_pow_sub_one {ζ : F} (hn : 0 < n) (h : IsPrimitiveRoot ζ n) :
    (X ^ n - 1 : F[X]).Splits := by
  rw [X_pow_sub_one_eq_prod hn h]
  exact Splits.prod (fun ζ _ => Splits.X_sub_C ζ)

/-- Given a primitive `n`-th root of unity, the multiset of roots of `X ^ n - 1` is `μ_n`. -/
theorem roots_X_pow_sub_one {ζ : F} (hn : 0 < n) (h : IsPrimitiveRoot ζ n) :
    (X ^ n - 1 : F[X]).roots = (nthRootsFinset n (1 : F)).val := by
  rw [X_pow_sub_one_eq_prod hn h, roots_prod_X_sub_C]

end Helpers

/-- **The resultant of `X^n - 1` and `(X+1)^n - 1` is the product of evaluations of the second
polynomial over the `n`-th roots of unity.** -/
theorem resultant_X_pow_sub_one_eq_prod_eval {n : ℕ} {ζ : F} (hn : 0 < n)
    (h : IsPrimitiveRoot ζ n) :
    resultant (X ^ n - 1 : F[X]) ((X + 1) ^ n - 1) n n
      = ∏ α ∈ nthRootsFinset n (1 : F), (((X + 1) ^ n - 1 : F[X]).eval α) := by
  have hgdeg : ((X + 1 : F[X]) ^ n - 1).natDegree ≤ n := by
    apply le_trans (natDegree_sub_le _ _)
    simp only [natDegree_one, max_le_iff]
    refine ⟨?_, Nat.zero_le _⟩
    calc ((X + 1 : F[X]) ^ n).natDegree ≤ n * (X + 1 : F[X]).natDegree := natDegree_pow_le
      _ = n := by
        rw [show (1 : F[X]) = C 1 by rw [map_one], natDegree_X_add_C, mul_one]
  have hfdeg : (X ^ n - 1 : F[X]).natDegree = n := natDegree_X_pow_sub_one hn
  have hlc : (X ^ n - 1 : F[X]).leadingCoeff = 1 := (monic_X_pow_sub_one hn)
  have key := resultant_eq_prod_eval (X ^ n - 1 : F[X]) ((X + 1) ^ n - 1) n hgdeg
    (splits_X_pow_sub_one hn h)
  rw [hfdeg] at key
  rw [key, hlc, one_pow, one_mul, roots_X_pow_sub_one hn h]
  rw [Finset.prod_eq_multiset_prod]

/-- `β⁻¹ ∈ μ_n` for `β ∈ μ_n`. -/
theorem inv_mem_nthRootsFinset {n : ℕ} (hn : 0 < n) {β : F}
    (hβ : β ∈ nthRootsFinset n (1 : F)) : β⁻¹ ∈ nthRootsFinset n (1 : F) := by
  rw [mem_nthRootsFinset hn] at hβ ⊢
  rw [inv_pow, hβ, inv_one]

/-- Reindexing `α = β·γ`: for fixed `β ∈ μ_n`, multiplication by `β` is a bijection of `μ_n`,
so `∏_{α ∈ μ_n} φ α = ∏_{γ ∈ μ_n} φ (β·γ)`. -/
theorem prod_nthRootsFinset_eval_reindex {n : ℕ} (hn : 0 < n) {β : F}
    (hβ : β ∈ nthRootsFinset n (1 : F)) (φ : F → F) :
    (∏ α ∈ nthRootsFinset n (1 : F), φ α)
      = ∏ γ ∈ nthRootsFinset n (1 : F), φ (β * γ) := by
  refine Finset.prod_nbij' (fun α => β⁻¹ * α) (fun γ => β * γ) ?_ ?_ ?_ ?_ ?_
  · intro α hα
    have : β⁻¹ * α ∈ nthRootsFinset n ((1 : F) * 1) :=
      mul_mem_nthRootsFinset (inv_mem_nthRootsFinset hn hβ) hα
    simpa using this
  · intro γ hγ
    have : β * γ ∈ nthRootsFinset n ((1 : F) * 1) := mul_mem_nthRootsFinset hβ hγ
    simpa using this
  · intro α _
    have hβ0 : β ≠ 0 := ne_zero_of_mem_nthRootsFinset one_ne_zero hβ
    field_simp
  · intro γ _
    have hβ0 : β ≠ 0 := ne_zero_of_mem_nthRootsFinset one_ne_zero hβ
    field_simp
  · intro α _
    have hβ0 : β ≠ 0 := ne_zero_of_mem_nthRootsFinset one_ne_zero hβ
    congr 1
    field_simp

/-- **The BGK resultant product formula (#232).** Over a field `F` containing a primitive `n`-th
root of unity, the resultant of `X^n - 1` and `(X+1)^n - 1` factors as a clean product over the
`n`-th roots of unity:
`Res(X^n - 1, (X+1)^n - 1) = ∏_{γ ∈ μ_n} (1 - (-1)^n · (γ-1)^n)`.
For even `n` this is `∏_{γ} (1 - (γ-1)^n)` (see `resultant_X_pow_sub_one_eq_bgk_prod_even`). -/
theorem resultant_X_pow_sub_one_eq_bgk_prod {n : ℕ} {ζ : F} (hn : 0 < n)
    (h : IsPrimitiveRoot ζ n) :
    resultant (X ^ n - 1 : F[X]) ((X + 1) ^ n - 1) n n
      = ∏ γ ∈ nthRootsFinset n (1 : F), (1 - (-1) ^ n * (γ - 1) ^ n) := by
  rw [resultant_X_pow_sub_one_eq_prod_eval hn h]
  -- `Res = ∏_α ((α+1)^n - 1) = ∏_α ∏_β (1 + α - β)`.
  have hstep1 : (∏ α ∈ nthRootsFinset n (1 : F),
        (((X + 1) ^ n - 1 : F[X]).eval α))
      = ∏ α ∈ nthRootsFinset n (1 : F), ∏ β ∈ nthRootsFinset n (1 : F), (1 + α - β) := by
    refine Finset.prod_congr rfl ?_
    intro α _
    simp only [eval_sub, eval_pow, eval_add, eval_X, eval_one]
    have := h.pow_sub_pow_eq_prod_sub_mul (x := α + 1) (y := (1 : F)) hn
    rw [one_pow] at this
    rw [this]
    refine Finset.prod_congr rfl ?_
    intro β _
    ring
  rw [hstep1, Finset.prod_comm]
  -- `∏_β ∏_α (1 + α - β)`; reindex inner `α = β*γ` for fixed `β`.
  have hstep2 : (∏ β ∈ nthRootsFinset n (1 : F), ∏ α ∈ nthRootsFinset n (1 : F), (1 + α - β))
      = ∏ β ∈ nthRootsFinset n (1 : F), ∏ γ ∈ nthRootsFinset n (1 : F), (1 + β * (γ - 1)) := by
    refine Finset.prod_congr rfl ?_
    intro β hβ
    rw [prod_nthRootsFinset_eval_reindex hn hβ (fun α => 1 + α - β)]
    refine Finset.prod_congr rfl ?_
    intro γ _
    ring
  rw [hstep2, Finset.prod_comm]
  -- `∏_γ ∏_β (1 + (γ-1)*β)`; apply the inner-product identity with `c = γ - 1`.
  refine Finset.prod_congr rfl ?_
  intro γ _
  rw [← prod_one_add_mul_nthRootsFinset hn h (γ - 1)]
  refine Finset.prod_congr rfl ?_
  intro β _
  ring

/-- **The BGK resultant product formula for even `n`.** For even `n`, `(-1)^n = 1`, so
`Res(X^n - 1, (X+1)^n - 1) = ∏_{γ ∈ μ_n} (1 - (γ-1)^n)`. -/
theorem resultant_X_pow_sub_one_eq_bgk_prod_even {n : ℕ} {ζ : F} (hn : 0 < n) (hne : Even n)
    (h : IsPrimitiveRoot ζ n) :
    resultant (X ^ n - 1 : F[X]) ((X + 1) ^ n - 1) n n
      = ∏ γ ∈ nthRootsFinset n (1 : F), (1 - (γ - 1) ^ n) := by
  rw [resultant_X_pow_sub_one_eq_bgk_prod hn h]
  refine Finset.prod_congr rfl ?_
  intro γ _
  rw [hne.neg_one_pow, one_mul]

/-- **The resultant vanishes iff a root of unity is a "Mersenne witness".** For even `n`, the
resultant `Res(X^n - 1, (X+1)^n - 1)` is zero iff there is an `n`-th root of unity `γ` with
`(γ-1)^n = 1` — i.e. iff `γ - 1` is itself an `n`-th root of unity. This is exactly the BGK
common-root / additive-energy obstruction of `AdditiveEnergyResultant`: the resultant carries each
cell's energy as the product of the per-`γ` factors `1 - (γ-1)^n`. -/
theorem resultant_X_pow_sub_one_eq_zero_iff {n : ℕ} {ζ : F} (hn : 0 < n) (hne : Even n)
    (h : IsPrimitiveRoot ζ n) :
    resultant (X ^ n - 1 : F[X]) ((X + 1) ^ n - 1) n n = 0
      ↔ ∃ γ ∈ nthRootsFinset n (1 : F), (γ - 1) ^ n = 1 := by
  rw [resultant_X_pow_sub_one_eq_bgk_prod_even hn hne h, Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨γ, hγ, hz⟩
    exact ⟨γ, hγ, by linear_combination -hz⟩
  · rintro ⟨γ, hγ, hz⟩
    exact ⟨γ, hγ, by rw [hz, sub_self]⟩

end ArkLib.ProximityGap.AdditiveEnergyKernel
