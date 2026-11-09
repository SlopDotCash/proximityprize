/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: wangruowei49-gif
-/
import ArkLib.Research.ProximityGap.Frontier._IsoSparsityMasonStothers
import Mathlib.Algebra.CharP.Defs

/-!
# The unrestricted isolated-root residual fails in large finite characteristic

The rational counterexample discussed in PR #227 has an integer certificate, so it
also survives in every field in which 2, 3, 5 and 7 are nonzero. This rules out
repairing the unrestricted residual merely by restricting its field to a large
prime characteristic. Subgroup membership and the intended sub-coset exclusion
are still absent from the statement; this does not refute the production conjecture.
-/

set_option autoImplicit false

noncomputable section

open Polynomial

namespace ProximityGap.Frontier.IsoSparsityMasonStothers

private def witnessA (F : Type*) [Field F] : F[X] := C 15 * X ^ 2 + C 225 * X + C 120
private def witnessO (F : Type*) [Field F] : F[X] := X ^ 2 + C 85 * X + C 274

/-- The integer certificate factors over every field, including small characteristic. -/
theorem isolated_witness_factorization (F : Type*) [Field F] :
    isoPoly (witnessA F) (witnessO F) =
      -(X - C 1) * (X - C 4) * (X - C 9) * (X - C 16) * (X - C 25) := by
  simp only [isoPoly, witnessA, witnessO, map_ofNat, map_one]
  ring

/-- Five isolated roots contradict the unrestricted residual whenever 2, 3, 5, 7 survive. -/
theorem not_isolatedNonCosetCountResidual_of_small_primes_ne_zero
    (F : Type*) [Field F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (h5 : (5 : F) ≠ 0) (h7 : (7 : F) ≠ 0) :
    ¬ IsolatedNonCosetCountResidual F 3 := by
  classical
  have hn (a b c d : ℕ) : (2 : F)^a * 3^b * 5^c * 7^d ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ h2)
      (pow_ne_zero _ h3)) (pow_ne_zero _ h5)) (pow_ne_zero _ h7)
  have h8 : (8 : F) ≠ 0 := by convert hn 3 0 0 0 using 1; norm_num
  have h15 : (15 : F) ≠ 0 := by convert hn 0 1 1 0 using 1; norm_num
  have h24 : (24 : F) ≠ 0 := by convert hn 3 1 0 0 using 1; norm_num
  have h12 : (12 : F) ≠ 0 := by convert hn 2 1 0 0 using 1; norm_num
  have h21 : (21 : F) ≠ 0 := by convert hn 0 1 0 1 using 1; norm_num
  have h16 : (16 : F) ≠ 0 := by convert hn 4 0 0 0 using 1; norm_num
  have h9 : (9 : F) ≠ 0 := by convert hn 0 2 0 0 using 1; norm_num
  have h14 : (1 : F) ≠ 4 := by intro h; apply h3; linear_combination -h
  have h19 : (1 : F) ≠ 9 := by intro h; apply h8; linear_combination -h
  have h116 : (1 : F) ≠ 16 := by intro h; apply h15; linear_combination -h
  have h125 : (1 : F) ≠ 25 := by intro h; apply h24; linear_combination -h
  have h49 : (4 : F) ≠ 9 := by intro h; apply h5; linear_combination -h
  have h416 : (4 : F) ≠ 16 := by intro h; apply h12; linear_combination -h
  have h425 : (4 : F) ≠ 25 := by intro h; apply h21; linear_combination -h
  have h916 : (9 : F) ≠ 16 := by intro h; apply h7; linear_combination -h
  have h925 : (9 : F) ≠ 25 := by intro h; apply h16; linear_combination -h
  have h1625 : (16 : F) ≠ 25 := by intro h; apply h9; linear_combination -h
  have hcard : ({1, 4, 9, 16, 25} : Finset F).card = 5 := by
    simp [h14, h19, h116, h125, h49, h416, h425, h916, h925, h1625]
  have h360 : (360 : F) ≠ 0 := by convert hn 3 2 1 0 using 1; norm_num
  have h630 : (630 : F) ≠ 0 := by convert hn 1 2 1 1 using 1; norm_num
  have h1120 : (1120 : F) ≠ 0 := by convert hn 5 0 1 1 using 1; norm_num
  have h1890 : (1890 : F) ≠ 0 := by convert hn 1 3 1 1 using 1; norm_num
  have h3024 : (3024 : F) ≠ 0 := by convert hn 4 3 0 1 using 1; norm_num
  have hroots : ∀ x ∈ ({1, 4, 9, 16, 25} : Finset F),
      (isoPoly (witnessA F) (witnessO F)).IsRoot x ∧ (witnessO F).eval x ≠ 0 := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;>
      constructor
    all_goals first
      | solve | simp [isolated_witness_factorization, IsRoot.def]
      | solve | norm_num [witnessO]; assumption
  intro h
  have hA : (witnessA F).natDegree < 3 := by unfold witnessA; compute_degree!
  have hO : (witnessO F).natDegree < 3 := by unfold witnessO; compute_degree!
  have hbound := h _ _ hA hO _ hroots
  rw [hcard] at hbound
  norm_num at hbound

/-- Restricting the formal residual to any prime characteristic above seven cannot repair it. -/
theorem not_isolatedNonCosetCountResidual_of_char_gt_seven
    (F : Type*) [Field F] (p : ℕ) [CharP F p] (hp : 7 < p) :
    ¬ IsolatedNonCosetCountResidual F 3 := by
  have hsmall (n : ℕ) (hn : 0 < n) (hlt : n < p) : (n : F) ≠ 0 := by
    intro h
    have hdiv := (CharP.cast_eq_zero_iff F p n).mp h
    have hle := Nat.le_of_dvd hn hdiv
    omega
  exact not_isolatedNonCosetCountResidual_of_small_primes_ne_zero F
    (hsmall 2 (by norm_num) (by omega)) (hsmall 3 (by norm_num) (by omega))
    (hsmall 5 (by norm_num) (by omega)) (hsmall 7 (by norm_num) (by omega))

#print axioms isolated_witness_factorization
#print axioms not_isolatedNonCosetCountResidual_of_small_primes_ne_zero
#print axioms not_isolatedNonCosetCountResidual_of_char_gt_seven

end ProximityGap.Frontier.IsoSparsityMasonStothers
