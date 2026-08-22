/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumMoment

/-!
# Weighted collision moments for repeated-coordinate depth-seven strata

The repeated-coordinate part of the corrected depth-seven census is not naturally a positive
fourteenth moment.  After identifying equal coordinates, a stratum is a weighted equation

`sum_i c_i x_i = sum_j d_j y_j`.

This file proves its exact Fourier dictionary.  If `eta_b = sum_(x in G) psi(b*x)`, then

`sum_b (prod_i eta_(c_i*b)) (prod_j eta_(-d_j*b))
  = q * #{(x,y) in G^r x G^s : sum_i c_i*x_i = sum_j d_j*y_j}`.

Removing `b=0` subtracts exactly `|G|^(r+s)`.  Consequently collision partitions with repeated
coordinates produce **signed mixed moments**.  For example, identifying one pair on the left of a
depth-seven equality gives coefficients `(2,1,1,1,1,1)` against seven `1`s, hence a nonzero-frequency
term of shape

`sum_(b != 0) eta_(2b) * eta_b^5 * eta_(-b)^7`.

This is an unconditional identity and a socket for the G155 injective/repeated DC split.  It does
not bound the mixed moment.  Issue #466.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment (eta)
open ArkLib.ProximityGap.SubgroupGaussSumMoment (prod_addChar_eq)

namespace ArkLib.ProximityGap.Frontier.BGKWeightedCollisionMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Number of pairs of subgroup tuples satisfying one weighted additive equation. -/
noncomputable def weightedCollisionCount (G : Finset F)
    {r s : ℕ} (c : Fin r → F) (d : Fin s → F) : ℕ :=
  ∑ v ∈ Fintype.piFinset (fun _ : Fin r => G),
    ∑ w ∈ Fintype.piFinset (fun _ : Fin s => G),
      if (∑ i, c i * v i) = ∑ j, d j * w j then 1 else 0

/-- Expand a product of coefficient-shifted periods as a weighted tuple sum. -/
theorem prod_eta_weighted (psi : AddChar F ℂ) (G : Finset F)
    (b : F) {r : ℕ} (c : Fin r → F) :
    ∏ i, eta psi G (c i * b) =
      ∑ v ∈ Fintype.piFinset (fun _ : Fin r => G),
        psi (b * ∑ i, c i * v i) := by
  classical
  calc
    ∏ i, eta psi G (c i * b) =
        ∑ v ∈ Fintype.piFinset (fun _ : Fin r => G),
          ∏ i, psi ((c i * b) * v i) := by
      simp only [eta]
      rw [Finset.prod_univ_sum]
    _ = ∑ v ∈ Fintype.piFinset (fun _ : Fin r => G),
          psi (b * ∑ i, c i * v i) := by
      refine Finset.sum_congr rfl (fun v _ => ?_)
      rw [prod_addChar_eq]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- **Weighted moment/collision identity.**  Additive-character orthogonality turns the product
of shifted periods into the exact weighted collision count. -/
theorem sum_prod_eta_weighted_eq_card_mul_collision
    {psi : AddChar F ℂ} (hpsi : psi.IsPrimitive) (G : Finset F)
    {r s : ℕ} (c : Fin r → F) (d : Fin s → F) :
    ∑ b : F, (∏ i, eta psi G (c i * b)) * (∏ j, eta psi G (-(d j) * b)) =
      (Fintype.card F : ℂ) * weightedCollisionCount G c d := by
  classical
  rw [show (∑ b : F, (∏ i, eta psi G (c i * b)) *
      (∏ j, eta psi G (-(d j) * b))) =
      ∑ b : F, (∑ v ∈ Fintype.piFinset (fun _ : Fin r => G),
        psi (b * ∑ i, c i * v i)) *
        (∑ w ∈ Fintype.piFinset (fun _ : Fin s => G),
          psi (b * ∑ j, -(d j) * w j)) by
        apply Finset.sum_congr rfl
        intro b _
        rw [prod_eta_weighted psi G b c,
          prod_eta_weighted psi G b (fun j => -(d j))]]
  simp only [Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  refine calc
    (∑ v ∈ Fintype.piFinset (fun _ : Fin r => G),
      ∑ b : F, ∑ w ∈ Fintype.piFinset (fun _ : Fin s => G),
        psi (b * ∑ i, c i * v i) * psi (b * ∑ j, -(d j) * w j)) =
      ∑ v ∈ Fintype.piFinset (fun _ : Fin r => G),
        ∑ w ∈ Fintype.piFinset (fun _ : Fin s => G),
          ∑ b : F, psi (b * ((∑ i, c i * v i) - ∑ j, d j * w j)) := by
      apply Finset.sum_congr rfl
      intro v _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro w _
      apply Finset.sum_congr rfl
      intro b _
      rw [← AddChar.map_add_eq_mul]
      congr 1
      rw [show (∑ j, -(d j) * w j) = -(∑ j, d j * w j) by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro j _
        ring]
      ring
    _ = ∑ v ∈ Fintype.piFinset (fun _ : Fin r => G),
        ∑ w ∈ Fintype.piFinset (fun _ : Fin s => G),
          if (∑ i, c i * v i) = ∑ j, d j * w j
            then (Fintype.card F : ℂ) else 0 := by
      apply Finset.sum_congr rfl
      intro v _
      apply Finset.sum_congr rfl
      intro w _
      rw [AddChar.sum_mulShift ((∑ i, c i * v i) - ∑ j, d j * w j) hpsi]
      by_cases h : (∑ i, c i * v i) = ∑ j, d j * w j <;> simp [h, sub_eq_zero]
    _ = (Fintype.card F : ℂ) * weightedCollisionCount G c d := by
      simp only [weightedCollisionCount]
      push_cast
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      by_cases h : (∑ i, c i * v i) = ∑ j, d j * w j <;> simp [h]

/-- **DC-subtracted weighted moment.**  The zero frequency contributes exactly
`|G|^(r+s)`, independently of the coefficient vectors. -/
theorem sum_nonzero_prod_eta_weighted_eq_dcExcess
    {psi : AddChar F ℂ} (hpsi : psi.IsPrimitive) (G : Finset F)
    {r s : ℕ} (c : Fin r → F) (d : Fin s → F) :
    ∑ b ∈ Finset.univ.erase (0 : F),
        (∏ i, eta psi G (c i * b)) * (∏ j, eta psi G (-(d j) * b)) =
      (Fintype.card F : ℂ) * weightedCollisionCount G c d - (G.card : ℂ) ^ (r + s) := by
  have hfull := sum_prod_eta_weighted_eq_card_mul_collision hpsi G c d
  have hzero :
      (∏ i : Fin r, eta psi G (c i * 0)) * (∏ j : Fin s, eta psi G (-(d j) * 0)) =
        (G.card : ℂ) ^ (r + s) := by
    simp [eta, pow_add]
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ 0), hfull, hzero]

/-- Coefficients of the leading one-repeat stratum: one doubled variable and five single
variables on the repeated side. -/
def oneRepeatCoeff : Fin 6 → F := fun i => if i = 0 then 2 else 1

/-- The all-single coefficient vector. -/
def allOneCoeff (r : ℕ) : Fin r → F := fun _ => 1

/-- **Leading repeated-stratum Fourier socket.**  Identifying exactly one coordinate pair on
the left of a depth-seven equality produces a signed shifted thirteenth moment, with DC term
`|G|^13`. -/
theorem oneRepeat_sum_nonzero_eq_dcExcess
    {psi : AddChar F ℂ} (hpsi : psi.IsPrimitive) (G : Finset F) :
    ∑ b ∈ Finset.univ.erase (0 : F),
        eta psi G (2 * b) * eta psi G b ^ 5 * eta psi G (-b) ^ 7 =
      (Fintype.card F : ℂ) *
          weightedCollisionCount G (oneRepeatCoeff (F := F)) (allOneCoeff (F := F) 7) -
        (G.card : ℂ) ^ 13 := by
  have h := sum_nonzero_prod_eta_weighted_eq_dcExcess hpsi G
    (oneRepeatCoeff (F := F)) (allOneCoeff (F := F) 7)
  have hleft : ∀ b : F,
      (∏ i, eta psi G (oneRepeatCoeff (F := F) i * b)) =
        eta psi G (2 * b) * eta psi G b ^ 5 := by
    intro b
    norm_num [oneRepeatCoeff, Fin.prod_univ_succ, pow_succ]
  have hright : ∀ b : F,
      (∏ j, eta psi G (-(allOneCoeff (F := F) 7 j) * b)) = eta psi G (-b) ^ 7 := by
    intro b
    norm_num [allOneCoeff, Fin.prod_univ_succ, pow_succ]
  simpa only [hleft, hright, Nat.reduceAdd] using h

#print axioms prod_eta_weighted
#print axioms sum_prod_eta_weighted_eq_card_mul_collision
#print axioms sum_nonzero_prod_eta_weighted_eq_dcExcess
#print axioms oneRepeat_sum_nonzero_eq_dcExcess

end ArkLib.ProximityGap.Frontier.BGKWeightedCollisionMoment
