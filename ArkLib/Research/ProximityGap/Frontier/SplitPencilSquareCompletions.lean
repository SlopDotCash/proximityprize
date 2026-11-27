/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.Tactic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Reconstructing the other two fibers of a split pencil

When one fiber and the holes are fixed, an unordered completion is a nonconstant
square member of an explicit polynomial pencil. All its square roots divide a
single critical polynomial. In a coordinate placing one point of the fixed fiber
at infinity, three pairwise coprime full-degree roots cannot divide that polynomial.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.SplitPencilSquareCompletions

open Polynomial

variable {K : Type*} [Field K]

/-- The sum and difference of the two scaled locators give the square member. -/
theorem square_member_forward (U V : K[X]) :
    (U-V)^2 + 4*(U*V) = (U+V)^2 := by ring

/-- A square member splits back into complementary factors. -/
theorem square_member_reverse {A F W : K[X]} {s : K} (hw : W^2 + C s*F = A^2) :
    (A-W)*(A+W) = C s*F := by linear_combination -hw

/-- Remove the known simple-pole locator from the derivative numerator of the rational
function whose denominator is its square. -/
noncomputable def critical (A F : K[X]) : K[X] := A*F.derivative - 2*(A.derivative*F)

/-- Every square root in the pencil divides the common critical polynomial. -/
theorem square_root_dvd_critical {A F W : K[X]} {s : K} (hs : s ≠ 0)
    (hw : W^2 + C s*F = A^2) : W ∣ critical A F := by
  have hd := congrArg derivative hw
  simp only [derivative_add, derivative_mul, derivative_C, zero_mul, zero_add,
    pow_two] at hd
  have hid : C s * critical A F = 2*W*(A.derivative*W-A*W.derivative) := by
    unfold critical
    linear_combination A*hd - 2*A.derivative*hw
  refine ⟨C s⁻¹*2*(A.derivative*W-A*W.derivative), ?_⟩
  calc critical A F = C s⁻¹*(C s*critical A F) := by
         rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hs, map_one, one_mul]
       _ = W*(C s⁻¹*2*(A.derivative*W-A*W.derivative)) := by rw [hid]; ring

/-- A simple zero of the uncolored polynomial outside the fixed fiber ensures that the
derivative numerator is nonzero, including in positive characteristic. -/
theorem critical_ne_zero {A F : K[X]} {x : K} (hA : A.eval x ≠ 0)
    (hF : F.eval x = 0) (hd : F.derivative.eval x ≠ 0) : critical A F ≠ 0 := by
  intro he
  have hv := congrArg (eval x) he
  simpa [critical, hF, hA, hd] using hv

/-- Square roots at distinct parameters are pairwise coprime. -/
theorem square_roots_coprime {A F U V : K[X]} {s t : K} (hst : s ≠ t)
    (hAF : IsCoprime A F) (hu : U^2+C s*F=A^2) (hv : V^2+C t*F=A^2) :
    IsCoprime U V := by
  have hpow : IsCoprime (A^2) F := hAF.pow_left
  obtain ⟨a, b, hab⟩ := hpow
  have hid : ((-a*C t-b)*U)*U + ((a*C s+b)*V)*V = (C s-C t)*(a*A^2+b*F) := by
    linear_combination (-a*C t-b)*hu + (a*C s+b)*hv
  rw [hab, mul_one, ← map_sub] at hid
  refine ⟨C (s-t)⁻¹*((-a*C t-b)*U), C (s-t)⁻¹*((a*C s+b)*V), ?_⟩
  calc C (s-t)⁻¹*((-a*C t-b)*U)*U + C (s-t)⁻¹*((a*C s+b)*V)*V =
         C (s-t)⁻¹*(((-a*C t-b)*U)*U + ((a*C s+b)*V)*V) := by ring
       _ = 1 := by rw [hid, ← map_mul, inv_mul_cancel₀ (sub_ne_zero.mpr hst), map_one]

/-- The critical polynomial has degree strictly below three full fiber degrees after moving
a root of the fixed fiber to infinity. -/
theorem critical_degree {A F : K[X]} {d : ℕ} (hA : A.natDegree < d)
    (hF : F.natDegree = 2*d) : (critical A F).natDegree < 3*d := by
  have h₁ := natDegree_mul_le (p := A) (q := F.derivative)
  have h₂ := natDegree_mul_le (p := A.derivative) (q := F)
  have h₃ := natDegree_derivative_le A
  have h₄ := natDegree_derivative_le F
  have hc := natDegree_C_mul_le (2 : K) (A.derivative*F)
  have hc' : (2*(A.derivative*F)).natDegree ≤ (A.derivative*F).natDegree := by
    simpa only [C_ofNat] using hc
  exact (natDegree_sub_le ..).trans_lt (max_lt (by omega) (by omega))

/-- Three pairwise coprime full-degree square roots would exceed the critical degree. -/
theorem no_three_full_roots {A F U V W : K[X]} {d : ℕ}
    (hA : A.natDegree < d) (hF : F.natDegree = 2*d) (hcrit : critical A F ≠ 0)
    (hU : U.natDegree=d) (hV : V.natDegree=d) (hW : W.natDegree=d)
    (hUV : IsCoprime U V) (hUW : IsCoprime U W) (hVW : IsCoprime V W)
    (du : U ∣ critical A F) (dv : V ∣ critical A F) (dw : W ∣ critical A F) : False := by
  have hd : 0 < d := by omega
  have hu : U ≠ 0 := fun h => by simp [h] at hU; omega
  have hv : V ≠ 0 := fun h => by simp [h] at hV; omega
  have hw : W ≠ 0 := fun h => by simp [h] at hW; omega
  have hall := (hUW.mul_left hVW).mul_dvd (hUV.mul_dvd du dv) dw
  have hle := Polynomial.natDegree_le_of_dvd hall hcrit
  rw [natDegree_mul (mul_ne_zero hu hv) hw, natDegree_mul hu hv, hU, hV, hW] at hle
  have := critical_degree hA hF
  omega

/-- The full two-completion cap, stated after the displayed change of source coordinate. -/
theorem no_three_square_members {A F U V W : K[X]} {d : ℕ} {x s t r : K}
    (hA : A.natDegree < d) (hF : F.natDegree=2*d) (hAF : IsCoprime A F)
    (hax : A.eval x ≠ 0) (hfx : F.eval x=0) (hdf : F.derivative.eval x ≠ 0)
    (hU : U.natDegree=d) (hV : V.natDegree=d) (hW : W.natDegree=d)
    (hs : s ≠ 0) (ht : t ≠ 0) (hr : r ≠ 0) (hst : s ≠ t) (hsr : s ≠ r) (htr : t ≠ r)
    (hu : U^2+C s*F=A^2) (hv : V^2+C t*F=A^2) (hw : W^2+C r*F=A^2) : False :=
  no_three_full_roots hA hF (critical_ne_zero hax hfx hdf) hU hV hW
    (square_roots_coprime hst hAF hu hv) (square_roots_coprime hsr hAF hu hw)
    (square_roots_coprime htr hAF hv hw) (square_root_dvd_critical hs hu)
    (square_root_dvd_critical ht hv) (square_root_dvd_critical hr hw)

/-- Two distinct scaled square members give a pair of reciprocal functions on the
conic. This identity constructs the common right factor. -/
theorem conic_product {L : Type*} [Field L] {u v r f s : L}
    (hu : u^2=1-(r^2*s)*f) (hv : v^2=1-s*f) :
    (u+r*v)*(u-r*v)=1-r^2 := by linear_combination hu - r^2*hv

/-- A square and its image under an involution differ by one of the two signs. -/
theorem square_sign {L : Type*} [Field L] {u v : L} (h : u^2=v^2) :
    u=v ∨ u = -v := by
  have he : (u-v)*(u+v)=0 := by linear_combination h
  rcases mul_eq_zero.mp he with he | he
  · left; linear_combination he
  · right; linear_combination he

/-- Clearing denominators in the two elliptic quotients of the genus-two curve gives
these identities. The coefficient of the middle term is arbitrary. -/
theorem two_elliptic_quotients {L : Type*} [Field L] {u y c a : L}
    (hy : y^2=c*(u^5+a*u^3+u)) :
    (y*(u+1))^2 = c*u*((u^2+1)^2+(a-2)*u^2)*(u^2+1+2*u) ∧
    (y*(u-1))^2 = c*u*((u^2+1)^2+(a-2)*u^2)*(u^2+1-2*u) := by
  constructor
  · linear_combination (u+1)^2*hy
  · linear_combination (u-1)^2*hy

/-- The elliptic order verified by the point certificate is in the Hasse interval, and
the certified prime divisor exceeds the width of that interval. -/
theorem elliptic_order_guards :
    let p : ℕ := 365375409332725729550921208179070755120141565953
    let t : ℕ := 1201616412679574549121762
    let q : ℕ := 52447244997910193717739548112237131
    t^2 ≤ 4*p ∧ 16*p < q^2 ∧ p+1-t = 6966531976032*q := by decide

/-- Numerical degrees for the first-prime quarter successor and the odd half successor. -/
theorem production_degrees :
    2*134217727=268435454 ∧ (2:ℕ)^30-3*268435454=268435462 ∧
    3*268435454-2=805306360 ∧ 268435455%2=1 := by decide

#print axioms square_root_dvd_critical
#print axioms critical_degree
#print axioms no_three_full_roots
#print axioms no_three_square_members
#print axioms conic_product
#print axioms two_elliptic_quotients

end ArkLib.ProximityGap.Frontier.SplitPencilSquareCompletions
