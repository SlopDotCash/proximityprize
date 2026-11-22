/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.ToricInterpolationKernel
import ArkLib.Research.ProximityGap.Frontier.DyadicRationalGraph
import ArkLib.Research.ProximityGap.Frontier.SevenSiteTransfer
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-! # Rational-function intersections with a dyadic grid in a prime field -/

namespace ProximityGap.DyadicRationalPrime
open Finset Polynomial

/-- Under the stated determinant-height inequality, more than twelve times
the degree in distinct matched inputs forces the source rational function
to be a monomial quotient. The conclusion is a polynomial identity and
also applies to unreduced interpolating pairs. -/
theorem dichotomy {p m d n : ℕ} [Fact p.Prime] [NeZero ((2^m : ℕ) : ZMod p)]
    {z : ZMod p} (hz : IsPrimitiveRoot z (2^m)) (hn : 2<2^m)
    (large : (2*(d+1))^((d+1)*(2^m).totient)<p^2)
    (P Q : (ZMod p)[X]) (pd : P.natDegree≤d) (qd : Q.natDegree≤d) (qn : Q≠0)
    (A B : Fin n → ℕ) (inj : Function.Injective (fun i => z^(A i)))
    (law : ∀ i, P.eval (z^(A i))=z^(B i)*Q.eval (z^(A i))) :
    n≤12*d ∨ ∃ (r s : ℕ) (c : ZMod p), r≤d ∧ s≤d ∧ c≠0 ∧ X^s*P=C c*X^r*Q := by
  classical
  by_cases few : n≤12*d
  · exact Or.inl few
  right
  let N := 2^m
  let K := AlgebraicClosure ℚ
  let : NeZero N := ⟨by dsimp [N];positivity⟩
  obtain ⟨w,hw⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot K N
  have wx : Function.Injective (fun i => w^(A i)) := fun _ _ h =>
    inj (SevenSiteTransfer.powers (by omega : 0<N) hw hz _ _ h)
  obtain ⟨S,T,nz,sd,td,rel⟩ := ToricInterpolationKernel.transport hn hz hw large A B P Q pd qd qn law
  obtain ⟨good,r,s,c,mg,rd,ss,_,edges⟩ := DyadicRationalGraph.dense hw S T nz sd td
    A B wx rel (by omega)
  obtain ⟨o,ho⟩ := card_pos.mp (show 0<good.card by omega)
  let x (i : Fin n) := z^(A i)
  let y (i : Fin n) := z^(B i)
  have xn (i) : x i≠0 := pow_ne_zero _ (hz.ne_zero (by positivity))
  have yn (i) : y i≠0 := pow_ne_zero _ (hz.ne_zero (by positivity))
  have finite_edges (i) (hi : i∈good) : y i*x i^s*x o^r=y o*x o^s*x i^r := by
    have h : w^(B i)*(w^(A i))^s*(w^(A o))^r=w^(B o)*(w^(A o))^s*(w^(A i))^r := by
      rw [edges i hi,edges o ho]; ring
    change z^(B i)*(z^(A i))^s*(z^(A o))^r=z^(B o)*(z^(A o))^s*(z^(A i))^r
    simp only [←pow_mul,←pow_add] at h ⊢
    exact SevenSiteTransfer.powers (by omega) hw hz _ _ h
  let scalar := y o*x o^s/x o^r
  have scale : scalar*x o^r=y o*x o^s := div_mul_cancel₀ _ (pow_ne_zero _ (xn o))
  have cs : scalar≠0 := div_ne_zero (mul_ne_zero (yn o) (pow_ne_zero _ (xn o))) (pow_ne_zero _ (xn o))
  refine ⟨r,s,scalar,rd,ss,cs,?_⟩
  let H : (ZMod p)[X] := X^s*P-C scalar*X^r*Q
  have hd : H.natDegree≤2*d := by
    apply (natDegree_sub_le _ _).trans (max_le _ _)
    · exact natDegree_mul_le.trans (by rw [natDegree_X_pow];omega)
    · apply natDegree_mul_le.trans
      have cap := natDegree_C_mul_le scalar (X^r : (ZMod p)[X])
      rw [natDegree_X_pow] at cap
      omega
  have roots (i) (hi : i∈good) : H.eval (x i)=0 := by
    have h : y i*x i^s=scalar*x i^r := by
      apply mul_right_cancel₀ (pow_ne_zero r (xn o))
      calc
        _ = y o*x o^s*x i^r := finite_edges _ hi
        _ = scalar*x i^r*x o^r := by rw [←scale];ring
    have site : P.eval (x i)=y i*Q.eval (x i) := law i
    simp only [H,eval_sub,eval_mul,eval_C,eval_pow,eval_X,site]
    linear_combination Q.eval (x i)*h
  apply sub_eq_zero.mp
  change H=0
  by_contra nh
  have := DyadicRationalSites.zeros nh x inj good roots
  omega

end ProximityGap.DyadicRationalPrime
#print axioms ProximityGap.DyadicRationalPrime.dichotomy
