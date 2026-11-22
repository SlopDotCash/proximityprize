/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.DyadicCrossRatioParity

/-! # Two cross pairs prevent a third same-parity pair on the exceptional conic

In the smaller grid of the dyadic descent the conic coefficient c changes
sign under the parity automorphism. The cross and same-parity equations
then force a chord identity whose rational norms are incompatible.
-/
namespace ProximityGap.DyadicExceptionalConic
open DyadicCrossRatioParity
variable {K : Type*} [Field K] [CharZero K]

/-- Algebraic elimination with the original coefficient and its parity conjugate.
The two cross pairs are (x,y) and (u,v). The same-parity pair is (a,b). -/
theorem chord_identity {B C c x y u v a b : K} (xn : x≠0) (different : x≠u)
    (x₁ : B*(x*y+c)+x+y=0) (x₂ : -C*(x*y+c)+x-y=0)
    (u₁ : B*(u*v+c)+u+v=0) (u₂ : -C*(u*v+c)+u-v=0)
    (a₁ : B*(a*b+c)+a+b=0) (a₂ : C*(a*b-c)+a+b=0) :
    (a+b)*(x+u)*x^2=(x^2-y^2)*(x*u) := by
  let P := (B-C)/2
  let Q := (B+C)/2
  have px : P*(x*y+c) = -x := by dsimp [P]; linear_combination (x₁+x₂)/2
  have qx : Q*(x*y+c) = -y := by dsimp [Q]; linear_combination (x₁-x₂)/2
  have pu : P*(u*v+c) = -u := by dsimp [P]; linear_combination (u₁+u₂)/2
  have qu : Q*(u*v+c) = -v := by dsimp [Q]; linear_combination (u₁-u₂)/2
  have pn : P≠0 := by intro eq; apply xn; simpa [eq] using px.symm
  let l := Q/P
  have lP : l*P=Q := div_mul_cancel₀ _ pn
  have xn' : l*x=y := by linear_combination l*px-qx-(x*y+c)*lP
  have un' : l*u=v := by linear_combination l*pu-qu-(u*v+c)*lP
  rw [← xn'] at px
  rw [← un'] at pu
  have root : (x-u)*(P*l*(x+u)+1)=0 := by linear_combination px-pu
  have scale := (mul_eq_zero.mp root).resolve_left (sub_ne_zero.mpr different)
  have const : c=l*x*u := by
    apply mul_left_cancel₀ pn
    linear_combination px-x*scale
  have prod : a*b= -l*c := by
    apply mul_left_cancel₀ pn
    have h : P*(a*b)+Q*c=0 := by dsimp [P,Q]; linear_combination (a₁-a₂)/2
    linear_combination h + c*lP
  have s : Q*(a*b)+P*c+(a+b)=0 := by
    dsimp [P,Q]; linear_combination (a₁+a₂)/2
  rw [prod,← lP,const] at s
  rw [← xn']
  linear_combination (x+u)*x^2*s + (l^2-1)*x^3*u*scale

section Dyadic

variable {L : Type*} [Field L] [Algebra ℚ L] {m : ℕ}
  [IsCyclotomicExtension {2^(m+1)} ℚ L] {z : L}

/-- The integer norms of the proposed chord identity are incompatible.
Here x and u are in the same parity class, while y is in the opposite class. -/
theorem no_chord_identity (hm : 0<m) (hz : IsPrimitiveRoot z (2^(m+1)))
    (x u y a b : ℕ) (xu : x%2=u%2) (ab : a%2=b%2) (xy : x%2≠y%2)
    (diff : z^x≠z^y) (sum : z^x+z^y≠0) :
    (z^a+z^b)*(z^x+z^u)*(z^x)^2 ≠ ((z^x)^2-(z^y)^2)*(z^x*z^u) := by
  have nz : z≠0 := by intro eq; simpa [eq] using hz.pow_eq_one
  have right : ((z^x)^2-(z^y)^2)*(z^x*z^u)≠0 := by
    rw [sq_sub_sq]
    exact mul_ne_zero (mul_ne_zero sum (sub_ne_zero.mpr diff))
      (mul_ne_zero (pow_ne_zero _ nz) (pow_ne_zero _ nz))
  intro eq
  have ab' : z^a+z^b≠0 := by intro zero; apply right; rw [← eq,zero]; ring
  have xu' : z^x+z^u≠0 := by intro zero; apply right; rw [← eq,zero]; ring
  have cost := congrArg size eq
  rw [sq_sub_sq,pow_two] at cost
  simp only [size_mul, size_root hm hz, one_mul, mul_one,
    opposite hm hz x y diff xy, opposite_sum hm hz x y sum xy] at cost
  have h₁ := same_sum hm hz a b ab' ab
  have h₂ := same_sum hm hz x u xu' xu
  have bound := mul_le_mul h₁ h₂ (by norm_num : (0:ℚ)≤4) (by linarith)
  linarith

end Dyadic

end ProximityGap.DyadicExceptionalConic
#print axioms ProximityGap.DyadicExceptionalConic.chord_identity
#print axioms ProximityGap.DyadicExceptionalConic.no_chord_identity
