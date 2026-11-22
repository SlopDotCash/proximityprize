/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.FourInvolutionPairs

/-! # A non-dihedral projective involution exchanging three pairs on every even root orbit -/

namespace ProximityGap.ThreeInvolutionPairs

private def exponent (m : ℕ) : Fin 3 → Fin 2 → ℕ := ![![0,1],![2,m+2],![3,4]]

/-- The three pairs of exponents are (0,1), (2,m+2), and (3,4) in order 2m. -/
def points (m : ℕ) (hm : 4≤m) : Fin 3 × Fin 2 ↪ Fin (2*m) where
  toFun ij := ⟨exponent m ij.1 ij.2,by
    obtain ⟨i,j⟩ := ij
    fin_cases i <;> fin_cases j <;> simp [exponent] <;> omega⟩
  inj' := by
    rintro ⟨i,j⟩ ⟨k,l⟩ eq
    have h := congrArg Fin.val eq
    change exponent m i j=exponent m k l at h
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      simp_all [exponent] <;> omega

/-- On every primitive even orbit of order at least eight, the six indicated
distinct sites are exchanged by a trace-zero matrix with both diagonal and
lower-left coefficients nonzero. -/
theorem sharp {K : Type*} [Field K] (m : ℕ) (hm : 4≤m) (z : K)
    (hz : IsPrimitiveRoot z (2*m)) :
    ∃ (a b c : K), a≠0 ∧ c≠0 ∧ a^2+b*c≠0 ∧
      ∀ i : Fin 3, c*z^((points m hm (i,0)).val)*z^((points m hm (i,1)).val) -
        a*(z^((points m hm (i,0)).val)+z^((points m hm (i,1)).val))=b := by
  have nz := hz.ne_zero (by omega)
  have hneg : z^m = -1 := by
    apply (sq_eq_one_iff.mp ?_).resolve_left (hz.pow_ne_one_of_pos_of_lt (by omega) (by omega))
    rw [← pow_mul,Nat.mul_comm m 2]
    exact hz.pow_eq_one
  have ha : z*(z^2-z+1) ≠ 0 := by
    intro h
    have eq := (mul_eq_zero.mp h).resolve_left nz
    have eq3 : z^3+1=0 := by linear_combination (z+1)*eq
    exact hz.pow_ne_one_of_pos_of_lt (by decide : (6:ℕ)≠0) (by omega)
      (by linear_combination (z^3-1)*eq3)
  have h4 : z^2+1≠0 := by
    intro h
    exact hz.pow_ne_one_of_pos_of_lt (by decide : (4:ℕ)≠0) (by omega)
      (by linear_combination (z^2-1)*h)
  have h1 : z≠1 := by simpa using hz.pow_ne_one_of_pos_of_lt (by decide : (1:ℕ)≠0) (by omega)
  refine ⟨z*(z^2-z+1),-z^4,1,ha,one_ne_zero,?_,?_⟩
  · rw [show (z*(z^2-z+1))^2 + -z^4*1=z^2*(z-1)^2*(z^2+1) by ring]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ nz) (pow_ne_zero _ (sub_ne_zero.mpr h1))) h4
  · intro i
    fin_cases i <;> simp [points,exponent,pow_add,hneg] <;> ring

end ProximityGap.ThreeInvolutionPairs

#print axioms ProximityGap.ThreeInvolutionPairs.sharp
