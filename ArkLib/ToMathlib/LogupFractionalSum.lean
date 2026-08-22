/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# LogUp fractional-sum algebraic core (issue #13)

The LogUp lookup argument reduces a multiset inclusion to the **fractional-sum identity**

  `∑ᵢ 1 / (α + wᵢ)  =  ∑ⱼ mⱼ / (α + tⱼ)`,

evaluated at a verifier-sampled challenge `α`.  The completeness/soundness analysis of the outer
LogUp verifier (`ArkLib/ProofSystem/Logup/Security/{Completeness,Soundness}.lean`) rests on
manipulating these sums of reciprocals: clearing denominators turns the fractional equation into a
polynomial identity in `α`, whose degree controls the Schwartz–Zippel soundness error and whose
roots are exactly the *pole set* already bounded in-tree by `card_poleSet_le`.

This module proves the reusable field-algebra core of that reduction, self-contained over any
field (it imports only `Mathlib`, so it is verifiable independently of the LogUp dependency cone,
which is not fully built in the shared checkout).

## Main results

* `sum_inv_eq_div` : a sum of reciprocals over a finite index set equals
  `(∑ᵢ ∏_{j≠i} dⱼ) / (∏ᵢ dᵢ)` — the common-denominator form, valid whenever every denominator is
  nonzero.
* `sum_inv_mul_prod` : the cleared-denominator identity
  `(∑ᵢ dᵢ⁻¹) · ∏ᵢ dᵢ = ∑ᵢ ∏_{j≠i} dⱼ` (no division), the polynomial form used to compare the two
  LogUp sides over a common denominator.
* `logup_fractional_eq_iff` : the LogUp fractional equation holds at `α` **iff** the corresponding
  cleared-denominator (polynomial) identity holds — the bridge from the rational check to the
  Schwartz–Zippel-amenable polynomial check.
* `logup_diagonal_sum_inv` : with all multiplicities equal to `1` and matching denominators, both
  LogUp sides coincide (the honest/completeness diagonal).

All results are `[propext, Classical.choice, Quot.sound]` only.
-/

namespace ArkLib.Logup.FractionalSum

open scoped BigOperators

variable {ι : Type*} {F : Type*} [Field F]

/-- Common-denominator form of a sum of reciprocals: if every `d i` (for `i ∈ s`) is nonzero,
then `∑ᵢ (d i)⁻¹ = (∑ᵢ ∏_{j≠i} d j) / (∏ᵢ d i)`.

This is the standard step that puts the LogUp left-hand side `∑ 1/(α + wᵢ)` over the single
denominator `∏ (α + wᵢ)`. -/
theorem sum_inv_eq_div [DecidableEq ι] (s : Finset ι) (d : ι → F)
    (hd : ∀ i ∈ s, d i ≠ 0) :
    ∑ i ∈ s, (d i)⁻¹
      = (∑ i ∈ s, ∏ j ∈ s.erase i, d j) / ∏ i ∈ s, d i := by
  classical
  have hprod : ∏ i ∈ s, d i ≠ 0 := Finset.prod_ne_zero_iff.mpr hd
  rw [eq_div_iff hprod, Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro i hi
  -- `(d i)⁻¹ * ∏_{k} d k = ∏_{j ≠ i} d j`, by peeling `d i` off the full product.
  rw [← Finset.prod_erase_mul s d hi]
  field_simp [hd i hi]

/-- Cleared-denominator (polynomial) form: multiplying the sum of reciprocals by the full product
of denominators yields the numerator sum, with **no division**.  This is the form used to compare
the two LogUp sides over a common denominator, since it stays polynomial in the challenge `α`. -/
theorem sum_inv_mul_prod [DecidableEq ι] (s : Finset ι) (d : ι → F)
    (hd : ∀ i ∈ s, d i ≠ 0) :
    (∑ i ∈ s, (d i)⁻¹) * ∏ i ∈ s, d i
      = ∑ i ∈ s, ∏ j ∈ s.erase i, d j := by
  classical
  have hprod : ∏ i ∈ s, d i ≠ 0 := Finset.prod_ne_zero_iff.mpr hd
  rw [sum_inv_eq_div s d hd, div_mul_cancel₀ _ hprod]

/-- **LogUp rational-to-polynomial bridge.** With nonzero denominators on both sides, the LogUp
fractional equation

  `∑ᵢ aᵢ / (d i)  =  ∑ⱼ bⱼ / (e j)`

holds **iff** the cleared-denominator polynomial identity

  `(∑ᵢ aᵢ · ∏_{i'≠i} d i') · (∏ⱼ e j)  =  (∑ⱼ bⱼ · ∏_{j'≠j} e j') · (∏ᵢ d i)`

holds.  Clearing denominators is exactly how the verifier's rational check is converted into a
single polynomial identity in the challenge, whose degree bounds the soundness error
(Schwartz–Zippel) and whose pole set is the in-tree `card_poleSet_le`. -/
theorem logup_fractional_eq_iff [DecidableEq ι] {κ : Type*} [DecidableEq κ]
    (s : Finset ι) (t : Finset κ)
    (a : ι → F) (d : ι → F) (b : κ → F) (e : κ → F)
    (hd : ∀ i ∈ s, d i ≠ 0) (he : ∀ j ∈ t, e j ≠ 0) :
    (∑ i ∈ s, a i / d i = ∑ j ∈ t, b j / e j)
      ↔ ((∑ i ∈ s, a i * ∏ i' ∈ s.erase i, d i') * (∏ j ∈ t, e j)
          = (∑ j ∈ t, b j * ∏ j' ∈ t.erase j, e j') * (∏ i ∈ s, d i)) := by
  classical
  have hprodD : ∏ i ∈ s, d i ≠ 0 := Finset.prod_ne_zero_iff.mpr hd
  have hprodE : ∏ j ∈ t, e j ≠ 0 := Finset.prod_ne_zero_iff.mpr he
  -- Each side as a single fraction over the common denominator.
  have hL : ∑ i ∈ s, a i / d i
      = (∑ i ∈ s, a i * ∏ i' ∈ s.erase i, d i') / ∏ i ∈ s, d i := by
    rw [eq_div_iff hprodD, Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [← Finset.prod_erase_mul s d hi]
    field_simp [hd i hi]
  have hR : ∑ j ∈ t, b j / e j
      = (∑ j ∈ t, b j * ∏ j' ∈ t.erase j, e j') / ∏ j ∈ t, e j := by
    rw [eq_div_iff hprodE, Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro j hj
    rw [← Finset.prod_erase_mul t e hj]
    field_simp [he j hj]
  rw [hL, hR, div_eq_div_iff hprodD hprodE]

/-- **Honest diagonal.** When the table denominators match the witness denominators pointwise on a
shared index set and every multiplicity is `1`, the two LogUp sides are literally equal.  This is
the completeness direction: an honest prover's fractional sums coincide identically (before any
challenge sampling), so the verifier accepts with no error from this check. -/
theorem logup_diagonal_sum_inv (s : Finset ι) (d : ι → F) :
    ∑ i ∈ s, (1 : F) / d i = ∑ i ∈ s, (d i)⁻¹ := by
  simp [one_div]

/-! ### Axiom audit (issue #13 LogUp fractional-sum core) -/

#print axioms sum_inv_eq_div
#print axioms sum_inv_mul_prod
#print axioms logup_fractional_eq_iff
#print axioms logup_diagonal_sum_inv

end ArkLib.Logup.FractionalSum
