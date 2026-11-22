/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.DyadicParityPolynomial

/-! # A linear bound for all dyadic matches of a nonmonomial rational function

If the reduced fraction is even or odd, each polynomial has a single
exponent parity. Squaring the input and removing one monomial from the
output halves the degree. Each new input has at most two old preimages.
-/
namespace ProximityGap.DyadicRationalDegree
open Finset Polynomial DyadicRationalSites
variable {K : Type*} [Field K] [CharZero K]

/-- A polynomial with at most one nonzero coefficient. -/
def Single (P : K[X]) := ∃ (a : K) (j : ℕ), P=C a*X^j

private theorem single_expand {P U : K[X]} {r : ℕ} (eq : P=X^r*expand K 2 U)
    (h : Single U) : Single P := by
  obtain ⟨a,j,rfl⟩ := h
  refine ⟨a,r+2*j,?_⟩
  rw [eq,map_mul,map_pow,expand_C,expand_X,pow_add,pow_mul];ring

private theorem square_image [DecidableEq K] {n : ℕ} (x : Fin n → K) (inj : Function.Injective x) :
    n≤2*(univ.image (fun i => (x i)^2)).card := by
  classical
  let f (i : Fin n) := (x i)^2
  have cap (t : K) : (univ.filter fun i => f i=t).card≤2 := by
    let H : K[X] := X^2-C t
    have nh : H≠0 := by
      intro eq
      have e := congrArg (fun p : K[X] => p.coeff 2) eq
      norm_num [H,coeff_X_pow] at e
    apply le_trans _ (show H.natDegree≤2 by dsimp [H];compute_degree!)
    apply zeros nh x inj
    intro i hi
    simpa [H,sub_eq_zero] using (show (x i)^2=t from (mem_filter.mp hi).2)
  have h := card_eq_sum_card_image f univ
  have ub := sum_le_sum (s:=univ.image f) (fun t _ => cap t)
  simpa [mul_comm,f] using (show (univ : Finset (Fin n)).card≤(univ.image f).card*2 by
    rw [h]
    exact ub.trans (by simp))

/-- A reduced rational function over a normal extension of ℚ which is not a
monomial quotient maps at most 12d distinct dyadic roots to dyadic roots,
where d is the maximum of numerator and denominator degrees. No distinctness
condition is imposed on the output values. -/
theorem bound [Algebra ℚ K] [Normal ℚ K] {d m n : ℕ} {z : K}
    (hz : IsPrimitiveRoot z (2^m)) (P Q : K[X]) (p : P.natDegree≤d) (q : Q.natDegree≤d)
    (pn : P≠0) (qn : Q≠0) (cop : IsCoprime P Q) (nonmono : ¬ (Single P ∧ Single Q))
    (A B : Fin n → ℕ) (ix : Function.Injective (fun i => z^(A i)))
    (nz : ∀ i, Q.eval (z^(A i))≠0) (law : ∀ i, P.eval (z^(A i))=z^(B i)*Q.eval (z^(A i))) :
    n≤12*d := by
  classical
  induction d using Nat.strong_induction_on generalizing P Q n with
  | h d ih =>
    have hd : 0<d := by
      by_contra! ed
      have constant (T : K[X]) (le : T.natDegree≤d) : Single T := by
        refine ⟨T.coeff 0,0,?_⟩
        simpa using eq_C_of_natDegree_eq_zero (by omega : T.natDegree=0)
      exact nonmono ⟨constant P p,constant Q q⟩
    by_cases sy : ∃ e : K, e≠0 ∧ comparison P Q e=0
    · obtain ⟨e,en,eq⟩ := sy
      obtain ⟨r,s,U,V,hr,hs,un,vn,pu,qv,uv⟩ := DyadicParityPolynomial.split_pair pn qn cop en eq
      have ub : U.natDegree≤d/2 := by
        have hd := (natDegree_le_of_dvd (show expand K 2 U ∣ P by rw [pu];exact dvd_mul_left ..) pn).trans p
        rw [natDegree_expand] at hd; omega
      have vb : V.natDegree≤d/2 := by
        have hd := (natDegree_le_of_dvd (show expand K 2 V ∣ Q by rw [qv];exact dvd_mul_left ..) qn).trans q
        rw [natDegree_expand] at hd; omega
      have nm : ¬ (Single U ∧ Single V) := fun h => nonmono ⟨single_expand pu h.1,single_expand qv h.2⟩
      let x (i : Fin n) := z^(A i)
      let S := univ.image fun i => (x i)^2
      obtain ⟨f,members⟩ := DyadicSevenCombinatorics.select S S.card le_rfl
      have orig (j) := mem_image.mp (members j)
      choose g _ val using orig
      let A' (j : Fin S.card) := A (g j)*2
      let B' (j : Fin S.card) := B (g j)+A (g j)*s+A (g j)*(2^m-r)
      have arg (j) : z^(A' j)=(x (g j))^2 := by simp [A',x,pow_mul]
      have inj' : Function.Injective (fun j => z^(A' j)) := by
        intro i j h
        apply f.injective
        simpa only [arg,val] using h
      have qnz (j) : V.eval (z^(A' j))≠0 := by
        have ne := nz (g j)
        rw [qv,eval_mul,expand_eval] at ne
        rw [arg]
        exact right_ne_zero_of_mul ne
      have eq' (j) : U.eval (z^(A' j))=z^(B' j)*V.eval (z^(A' j)) := by
        let t := x (g j)
        have restore : t^r*t^(2^m-r)=1 := by
          have pos : 1≤2^m := Nat.one_le_two_pow
          rw [←pow_add,Nat.add_sub_of_le (hr.trans pos)]
          change (z^(A (g j)))^(2^m)=1
          rw [←pow_mul,Nat.mul_comm,pow_mul,hz.pow_eq_one,one_pow]
        have h := law (g j)
        rw [pu,qv,eval_mul,eval_pow,eval_X,expand_eval,eval_mul,eval_pow,eval_X,expand_eval] at h
        change t^r*U.eval (t^2)=z^(B (g j))*(t^s*V.eval (t^2)) at h
        rw [arg]
        change U.eval (t^2)=z^(B' j)*V.eval (t^2)
        have coeff : z^(B' j)=z^(B (g j))*t^s*t^(2^m-r) := by simp [B',pow_add,pow_mul,t,x]
        rw [coeff]
        linear_combination t^(2^m-r)*h-U.eval (t^2)*restore
      have hsmall := ih (d/2) (by omega) U V ub vb un vn uv nm A' B' inj' qnz eq'
      have size : n≤2*S.card := square_image x ix
      omega
    · apply DyadicRationalSites.bound hd hz P Q p q _ _ A B ix nz law
      · exact fun h => sy ⟨1,one_ne_zero,h⟩
      · exact fun h => sy ⟨-1,by simp,h⟩

end ProximityGap.DyadicRationalDegree
#print axioms ProximityGap.DyadicRationalDegree.bound
