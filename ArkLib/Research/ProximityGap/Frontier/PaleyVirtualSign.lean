/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.PaleyInterpolationContact

/-! # The constant term in a signed Paley approximation

Changing the specified sign adds a constant to the interpolation polynomial. Its
normalized derivative matrix contributes one additional column to the factorization.
-/

namespace ProximityGap.PaleyDefectMinor

open Finset Matrix Polynomial

variable {K : Type*} [Field K] {e : ℕ}

/-- Adding a constant to the polynomial augments its derivative factorization by one column. -/
theorem normalizedHankel_add_C_factors (W : K[X]) (D h : ℕ) (z : K)
    (U : Matrix (Fin (h+1)) (Fin e) K[X]) (V : Matrix (Fin e) (Fin (h+1)) K[X])
    (hfac : normalizedHankel W D h = U * V) :
    ∃ (U' : Matrix (Fin (h+1)) (Fin (e+1)) K[X]) (V' : Matrix (Fin (e+1)) (Fin (h+1)) K[X]),
      normalizedHankel (W + C z) D h = U' * V' := by
  let U' : Matrix (Fin (h+1)) (Fin (e+1)) K[X] := fun i => Fin.cons
    (if i.val = 0 then C z else 0) (U i)
  let V' : Matrix (Fin (e+1)) (Fin (h+1)) K[X] := Fin.cons
    (fun j => if j.val = 0 then 1 else 0) V
  refine ⟨U', V', ?_⟩
  ext i j : 1
  rw [Matrix.mul_apply, Fin.sum_univ_succ]
  simp only [U', V', Fin.cons_zero, Fin.cons_succ]
  change _ = _ + (U * V) i j
  rw [← hfac]
  change C _ * derivative^[i.val+j.val] (W + C z) =
    (if i.val=0 then C z else 0) * (if j.val=0 then 1 else 0) +
      C _ * derivative^[i.val+j.val] W
  by_cases hi : i.val=0 <;> by_cases hj : j.val=0
  · simp [hi,hj,add_comm]
  all_goals
    have hk : 0 < i.val+j.val := by omega
    have hd : derivative^[i.val+j.val] (W + C z) = derivative^[i.val+j.val] W := by
      rw [← Module.End.pow_apply, map_add, Module.End.pow_apply, Module.End.pow_apply,
        iterate_derivative_C hk, add_zero]
    rw [hd]
    simp [hi,hj]

/-- Polynomial contact with a constant and `e` shifted powers charges `e+1` columns. -/
theorem pow_dvd_normalizedHankel_of_contact_add_C (F t : K[X]) (a c : Fin e → K)
    (D h s : ℕ) (z : K) (hD : 2*h ≤ D)
    (hunit : ∀ k ≤ 2*h, (D.descFactorial k : K) ≠ 0)
    (hcontact : t ^ (s + 2*h) ∣ F - ∑ l : Fin e, C (c l) * (X + C (a l)) ^ D) :
    let r := h + 1 - (e + 1)
    t ^ (r * s + r * (r - 1)) ∣ (normalizedHankel (F + C z) D h).det := by
  let W := ∑ l : Fin e, C (c l) * (X + C (a l)) ^ D
  obtain ⟨U,V,hfac⟩ := normalizedHankel_shifted_powers_factors a c D h hD hunit
  obtain ⟨U',V',hfac'⟩ := normalizedHankel_add_C_factors W D h z U V hfac
  apply pow_dvd_normalizedHankel_of_factored_contact (F+C z) (W+C z) t D h s U' V' hfac'
  simpa only [add_sub_add_right_eq_sub] using hcontact

end ProximityGap.PaleyDefectMinor

namespace ProximityGap.PaleyInterpolationContact

open Finset Polynomial

/-- Adding a constant to the signed interpolation polynomial permits a single extra
column in the determinant bound for the same exceptional sites. -/
theorem minority_determinant_add_const {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (A : Finset (ZMod p)) (b : ZMod p) {k h : ℕ} (hk : k < A.card)
    (hD : p/2+k < p)
    (hh : 2*h ≤ if -b ∈ A then k else k+1)
    {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) (c : ZMod p) :
    let D := p/2+k
    let E := A.filter fun u => quadraticChar (ZMod p) (b+u) = -σ
    let ν := if -b ∈ A then k else k+1
    let r := h+1-(E.card+1)
    let F := powerSum A A D - C (if k = A.card-1 then (σ : ZMod p) else 0)
    (X - C b) ^ (r*(ν-2*h)+r*(r-1)) ∣ (PaleyDefectMinor.normalizedHankel (F+C c) D h).det := by
  classical
  let E := A.filter fun u => quadraticChar (ZMod p) (b+u) = -σ
  let D := p/2+k
  let ν := if -b ∈ A then k else k+1
  let F := powerSum A A D - C (if k = A.card-1 then (σ : ZMod p) else 0)
  let site (i : Fin E.card) : ZMod p := E.equivFin.symm i
  let w := Lagrange.nodalWeight A id
  have htwo : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hwidth : 2*h ≤ D := by
    change _ ≤ p/2+k
    split at hh <;> omega
  have hunit (j : ℕ) (hj : j ≤ 2*h) : (D.descFactorial j : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd
    have hdvd' : p ∣ D.factorial := Nat.dvd_trans hdvd
      ⟨(D-j).factorial, by rw [mul_comm, Nat.factorial_mul_descFactorial (hj.trans hwidth)]⟩
    exact (not_le.mpr hD) ((Fact.out : p.Prime).dvd_factorial.mp hdvd')
  have hc := minority_contact (K := ZMod p) (by rwa [ZMod.ringChar_zmod_n]) A b hk hσ
  have hfull : (X - C b)^ν ∣ F - C 2 * powerSum A E D := by
    simpa only [ZMod.card, D, F, ν, E] using hc
  have hsum : (∑ i : Fin E.card, C (2*w (site i))*(X+C (site i))^D) =
      C 2 * powerSum A E D := by
    let g (u : ZMod p) : (ZMod p)[X] := C (2*w u)*(X+C u)^D
    change (∑ i, g (E.equivFin.symm i)) = _
    rw [E.equivFin.symm.sum_comp (fun u : E => g u.val)]
    simp [g, w, powerSum, Finset.mul_sum, mul_assoc]
    exact E.sum_attach (fun u : ZMod p => C 2 * (C (Lagrange.nodalWeight A id u) * (X+C u)^D))
  apply PaleyDefectMinor.pow_dvd_normalizedHankel_of_contact_add_C F (X-C b)
    site (fun i => 2*w (site i)) D h (ν-2*h) c hwidth hunit
  rw [hsum, Nat.sub_add_cancel hh]
  exact hfull

end ProximityGap.PaleyInterpolationContact

#print axioms ProximityGap.PaleyInterpolationContact.minority_determinant_add_const
