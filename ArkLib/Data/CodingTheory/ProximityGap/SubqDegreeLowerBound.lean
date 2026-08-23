/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.StepanovNonVanishing

/-!
# A degree lower bound for the base-`q` substitution (#389, Stepanov-Weil substrate)

Complementing `natDegree_subq_le` (the upper bound `natDegree(subq q A) ≤ q·natDegree A + (q−1)`):
the base-`q` substitution `subq q A = ∑_j (A.coeff j)·X^{qj}` has its **top** block
`(A.coeff m)·X^{qm}` (`m = natDegree A`) reaching degree `qm + natDegree(A.coeff m)`, which no
lower block can cancel under the digit condition `natDegree(A.coeff j) < q` (the blocks are
separated: block `j` lives in degrees `[qj, qj+q)`).  Hence `natDegree(subq q A) ≥ q·natDegree A`.
Together with the upper bound this pins `natDegree(subq q A)` to the block `[qm, qm+q)`.
-/

set_option linter.unusedSectionVars false


open Polynomial

namespace ArkLib.ProximityGap.StepanovNonVanishing

variable {F : Type*} [Field F]

/-- **Lower bound on the base-`q` substitution degree.** Under the digit condition
`natDegree(A.coeff j) < q`, the top block is uncancelled, so `q · natDegree A ≤ natDegree (subq q A)`. -/
theorem natDegree_subq_ge (q : ℕ) (A : Polynomial (Polynomial F)) (hA : A ≠ 0)
    (hdig : ∀ j, (A.coeff j).natDegree < q) :
    q * A.natDegree ≤ (subq q A).natDegree := by
  set m := A.natDegree with hm
  set e := (A.coeff m).natDegree with he
  have hcoeffm : A.coeff m ≠ 0 := by
    rw [hm, Polynomial.coeff_natDegree]; exact Polynomial.leadingCoeff_ne_zero.mpr hA
  have hcoeff : (subq q A).coeff (q * m + e) ≠ 0 := by
    rw [subq_eq_sum, Polynomial.finset_sum_coeff, Finset.sum_eq_single m]
    · rw [Polynomial.coeff_mul_X_pow', if_pos (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
        he, Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr hcoeffm
    · intro j hj hjm
      have hjlt : j < m := by rw [Finset.mem_range] at hj; omega
      rw [Polynomial.coeff_mul_X_pow']
      split_ifs with hle
      · apply Polynomial.coeff_eq_zero_of_natDegree_lt
        have hd := hdig j
        have hge : q ≤ q * m + e - q * j := by
          have hstep : q * j + q ≤ q * m := by
            calc q * j + q = q * (j + 1) := by ring
              _ ≤ q * m := Nat.mul_le_mul_left q hjlt
          omega
        omega
      · rfl
    · intro hmrange
      exact absurd (Finset.mem_range.mpr (by omega)) hmrange
  have hle := Polynomial.le_natDegree_of_ne_zero hcoeff
  omega

end ArkLib.ProximityGap.StepanovNonVanishing
