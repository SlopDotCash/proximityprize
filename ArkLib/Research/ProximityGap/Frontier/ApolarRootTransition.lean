/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.ApolarDividedPolynomial
import ArkLib.Research.ProximityGap.Frontier.ApolarDividedReversal

/-! # The coordinate transition of the polynomial attached to a pencil

Both the divided polynomial and its reciprocal representative are evaluated in
the same algebra. A unit at the universal root retains its multiplicity.
-/

set_option autoImplicit false
open Finset Polynomial
namespace ProximityGap.ApolarRootTransition
open ApolarDividedLocator ApolarDividedPolynomial ApolarDividedReversal

variable {A ι : Type*} [CommRing A]

noncomputable def measure (D : Finset ι) (y w : ι → A) : A[X] →ₗ[A] A :=
  ∑ i ∈ D, w i • Polynomial.leval (y i)

theorem eval_representative (D : Finset ι) (y w : ι → A) (f : A[X]) (x : A) :
    (representative D y w f).eval x = measure D y w (divided f x) := by
  simp only [representative,eval_finsetSum,eval_mul,eval_C,measure,LinearMap.sum_apply,
    LinearMap.smul_apply,Polynomial.leval,smul_eq_mul]
  apply sum_congr rfl
  intro i hi
  rw [eval_divided_comm]
  rfl

/-- Evaluation of a reversed bounded polynomial at a unit. -/
theorem eval_reflect (u : Aˣ) (d : ℕ) (g : A[X]) (hg : g.natDegree ≤ d) :
    (reflect d g).eval (u:A) = (u:A)^d*g.eval ((↑u⁻¹):A) := by
  let _ := u.isUnit.invertible
  have hdeg := (natDegree_reflect_le (N := d) (p := g)).trans (max_le le_rfl hg)
  simpa only [reflect_reflect,invOf_units,eval₂_id,mul_comm] using
    (eval₂_reflect_mul_pow (RingHom.id A) (u:A) d (reflect d g) hdeg).symm

/-- Reciprocal-coordinate error sites carry the weight y^d. -/
theorem reciprocal_measure (D : Finset ι) (y : ι → Aˣ) (w : ι → A) (g : A[X])
    {d : ℕ} (hg : g.natDegree ≤ d) :
    measure D (fun i => (↑(y i)⁻¹:A)) (fun i => w i*(y i:A)^d) g =
      measure D (fun i => (y i:A)) w (reflect d g) := by
  simp only [measure,LinearMap.sum_apply,LinearMap.smul_apply,Polynomial.leval,smul_eq_mul]
  apply sum_congr rfl
  intro i hi
  change _ = w i*(reflect d g).eval (y i:A)
  rw [eval_reflect _ _ _ hg,mul_assoc]
  rfl

variable [Nontrivial A]

/-- Both sides are ordinary polynomials formed from the original weights,
the reversed locator and the reciprocal coordinate. -/
theorem reciprocal_representative (D : Finset ι) (y : ι → Aˣ) (w : ι → A) (x : Aˣ)
    (f : A[X]) {r k : ℕ} (hk : 0<k) (hf : f.natDegree ≤ r+1) (hx : f.IsRoot (x:A))
    (ha : ApolarThrough (measure D (fun i => (y i:A)) w) f (k-1)) :
    (-(representative D (fun i => (↑(y i)⁻¹:A)) (fun i => w i*(y i:A)^(r+k))
      (reflect (r+1) f))).eval (↑x⁻¹:A) =
        (x:A)^(k+1)*(representative D (fun i => (y i:A)) w f).eval (x:A) := by
  have hdeg := (natDegree_reflect_le (N := r+1) (p := f)).trans (max_le le_rfl hf)
  have hd : (divided (reflect (r+1) f) (↑x⁻¹:A)).natDegree ≤ r+k := by
    rw [divided,natDegree_divByMonic _ (monic_X_sub_C _),natDegree_X_sub_C]
    omega
  rw [eval_neg,eval_representative,eval_representative,reciprocal_measure _ _ _ _ hd,
    functional_reverse _ hk x f hf hx ha]
  ring

omit [Nontrivial A] in
/-- Nonvanishing at the origin makes the universal root invertible, with no
restriction on repeated factors of the locator. -/
theorem unit_root {K : Type*} [Field K] (f : K[X]) (hf : f.eval 0 ≠ 0) :
    IsUnit (AdjoinRoot.root f) := by
  have hc : IsCoprime (X-C (0:K)) f := (irreducible_X_sub_C _).coprime_iff_not_dvd.mpr
    (fun hd => hf (dvd_iff_isRoot.mp hd))
  obtain ⟨a,b,h⟩ := hc
  have he : AdjoinRoot.mk f a * AdjoinRoot.root f = 1 := by
    simpa using congrArg (AdjoinRoot.mk f) h
  exact isUnit_of_mul_isUnit_right (he ▸ isUnit_one)

omit [Nontrivial A] in
private theorem cancel_unit (u : Aˣ) {a b : A} (h : (u:A)*a=(u:A)*b) : a=b := by
  simpa only [← mul_assoc,Units.inv_mul,one_mul] using congrArg (fun z : A => (↑u⁻¹:A)*z) h

/-- Coordinate reversal multiplies the P-th power of the representative by the
corresponding P-th power of the root. Here the exponent can be any natural number. -/
theorem power_remainders (power : ℕ) (D : Finset ι) (y : ι → Aˣ) (w : ι → A) (x s : Aˣ)
    (f V B B' : A[X]) {r k n : ℕ} (hk : 0<k) (hf : f.natDegree ≤ r+1)
    (hx : f.IsRoot (x:A)) (ha : ApolarThrough (measure D (fun i => (y i:A)) w) f (k-1))
    (hV : V.natDegree ≤ n)
    (hB : (s:A)*B.eval (x:A) = V.eval (x:A)*
      (representative D (fun i => (y i:A)) w f).eval (x:A)^power)
    (hB' : (s:A)*B'.eval (↑x⁻¹:A) = (reflect n V).eval (↑x⁻¹:A)*
      (-(representative D (fun i => (↑(y i)⁻¹:A)) (fun i => w i*(y i:A)^(r+k))
        (reflect (r+1) f))).eval (↑x⁻¹:A)^power) :
    (x:A)^n*B'.eval (↑x⁻¹:A) = (x:A)^((k+1)* power)*B.eval (x:A) := by
  have hv : (reflect n V).eval (↑x⁻¹:A)*(x:A)^n = V.eval (x:A) := by
    let _ := x.isUnit.invertible
    simpa only [invOf_units,eval₂_id] using eval₂_reflect_mul_pow (RingHom.id A) (x:A) n V hV
  apply cancel_unit s
  calc
    _ = (x:A)^n*((s:A)*B'.eval (↑x⁻¹:A)) := by ring
    _ = (x:A)^((k+1)* power)*((s:A)*B.eval (x:A)) := by
      rw [hB',reciprocal_representative D y w x f hk hf hx ha,hB,← hv,pow_mul,mul_pow]
      ring
    _ = _ := by ring

/-- The two cubic interpolation identities imply the precise Laurent transition
for their actual remainders in the universal root algebra. -/
theorem cubic_remainders (D : Finset ι) (y : ι → Aˣ) (w : ι → A) (x s : Aˣ)
    (f V B B' : A[X]) {r k n : ℕ} (hk : 0<k) (hf : f.natDegree ≤ r+1)
    (hx : f.IsRoot (x:A)) (ha : ApolarThrough (measure D (fun i => (y i:A)) w) f (k-1))
    (hV : V.natDegree ≤ n)
    (hB : (s:A)*B.eval (x:A) = V.eval (x:A)*
      (representative D (fun i => (y i:A)) w f).eval (x:A)^3)
    (hB' : (s:A)*B'.eval (↑x⁻¹:A) = (reflect n V).eval (↑x⁻¹:A)*
      (-(representative D (fun i => (↑(y i)⁻¹:A)) (fun i => w i*(y i:A)^(r+k))
        (reflect (r+1) f))).eval (↑x⁻¹:A)^3) :
    (x:A)^n*B'.eval (↑x⁻¹:A) = (x:A)^((k+1)*3)*B.eval (x:A) :=
  power_remainders 3 D y w x s f V B B' hk hf hx ha hV hB hB'

omit [Nontrivial A] in
/-- In a chart of nonnegative coordinate degree this is the cleared polynomial
identity needed for the two-variable remainder comparison. -/
theorem clear_positive (x : Aˣ) (B B' : A[X]) {m b a : ℕ} (hd : B'.natDegree ≤ m)
    (h : (x:A)^(a+b)*B'.eval (↑x⁻¹:A) = (x:A)^a*B.eval (x:A)) :
    (x:A)^b*(reflect m B').eval (x:A) = (x:A)^m*B.eval (x:A) := by
  have hs : (x:A)^b*B'.eval (↑x⁻¹:A) = B.eval (x:A) := by
    apply cancel_unit (x^a)
    simpa only [Units.val_pow_eq_pow_val,← mul_assoc,← pow_add] using h
  rw [eval_reflect x _ _ hd,← hs]
  ring

omit [Nontrivial A] in
/-- In a chart of strictly negative coordinate degree inversion separates the
positive and nonpositive powers. -/
theorem clear_negative (x : Aˣ) (B B' : A[X]) {m k a : ℕ} (hd : B'.natDegree ≤ m)
    (h : (x:A)^a*B'.eval (↑x⁻¹:A) = (x:A)^(a+k)*B.eval (x:A)) :
    (reflect m B').eval (x:A) = (x:A)^(m+k)*B.eval (x:A) := by
  have hs : B'.eval (↑x⁻¹:A) = (x:A)^k*B.eval (x:A) := by
    apply cancel_unit (x^a)
    simpa only [Units.val_pow_eq_pow_val,← mul_assoc,← pow_add] using h
  rw [eval_reflect x _ _ hd,hs,pow_add,mul_assoc]

omit [Nontrivial A] in
/-- Clear an arbitrary common coordinate power in the two chart equations. -/
theorem clear_twist (x : Aˣ) (B B' : A[X]) {m a n b c : ℕ} (hd : B'.natDegree ≤ m)
    (he : b + a = n + c)
    (h : (x:A)^n * B'.eval (↑x⁻¹:A) = (x:A)^a * B.eval (x:A)) :
    (x:A)^b * (reflect m B').eval (x:A) = (x:A)^(m+c) * B.eval (x:A) := by
  have hs : (x:A)^b * B'.eval (↑x⁻¹:A) = (x:A)^c * B.eval (x:A) := by
    apply cancel_unit (x^n)
    change (x:A)^n * _ = (x:A)^n * _
    calc
      _ = (x:A)^b * ((x:A)^n * B'.eval (↑x⁻¹:A)) := by ring
      _ = (x:A)^(b+a) * B.eval (x:A) := by rw [h,pow_add,mul_assoc]
      _ = _ := by rw [he,pow_add,mul_assoc]
  rw [eval_reflect x _ _ hd,pow_add,mul_assoc,← hs]
  ring

#print axioms clear_twist
#print axioms cubic_remainders
#print axioms clear_positive
#print axioms clear_negative
#print axioms reciprocal_representative
#print axioms unit_root
end ProximityGap.ApolarRootTransition
