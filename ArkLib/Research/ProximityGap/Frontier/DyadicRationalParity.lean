/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.DyadicSevenCombinatorics

/-! # Nonexceptional dyadic matches of a rational function

A rational function of degree at most d is determined by 2d+1 finite matches.
If these matches occupy a single dyadic parity class, conjugation forces every
other match in a different source class to bring a signed antipodal match.
-/
namespace ProximityGap.DyadicRationalParity
open Polynomial Finset
variable {K : Type*} [Field K]

/-- Two polynomial quotients agreeing at sufficiently many inputs agree after
cross multiplication everywhere. This includes arguments at poles. -/
theorem interpolate {d : ℕ} (x : Fin (2*d+1) ↪ K) {P Q S T : K[X]}
    (p : P.natDegree≤d) (q : Q.natDegree≤d) (s : S.natDegree≤d) (t : T.natDegree≤d)
    (same : ∀ i, P.eval (x i)*T.eval (x i)=S.eval (x i)*Q.eval (x i)) :
    P*T=S*Q := by
  apply sub_eq_zero.mp
  apply eq_zero_of_degree_lt_of_eval_index_eq_zero univ x.injective.injOn
  · have h₁ := (natDegree_mul_le (p:=P) (q:=T)).trans (Nat.add_le_add p t)
    have h₂ := (natDegree_mul_le (p:=S) (q:=Q)).trans (Nat.add_le_add s q)
    have h := (natDegree_sub_le (P*T) (S*Q)).trans (max_le h₁ h₂)
    rw [Finset.card_univ,Fintype.card_fin]
    exact lt_of_le_of_lt (degree_le_natDegree) (by exact_mod_cast (show (P*T-S*Q).natDegree<2*d+1 by omega))
  · intro i _
    simp only [eval_sub,eval_mul,sub_eq_zero]
    exact same i

/-- An automorphism fixing enough matched sites and values preserves every
finite match with nonzero denominator. -/
theorem covariance (σ : K ≃+* K) {d : ℕ} {P Q : K[X]} (p : P.natDegree≤d) (q : Q.natDegree≤d)
    (x : Fin (2*d+1) ↪ K) (y : Fin (2*d+1) → K)
    (sx : ∀ i, σ (x i)=x i) (sy : ∀ i, σ (y i)=y i)
    (given : ∀ i, P.eval (x i)=y i*Q.eval (x i)) {u v : K}
    (nz : Q.eval u≠0) (match' : P.eval u=v*Q.eval u) : P.eval (σ u)=σ v*Q.eval (σ u) := by
  let S := P.map σ.toRingHom
  let T := Q.map σ.toRingHom
  have se (a : K) : S.eval (σ a)=σ (P.eval a) := eval_map_apply (p:=P) σ.toRingHom a
  have te (a : K) : T.eval (σ a)=σ (Q.eval a) := eval_map_apply (p:=Q) σ.toRingHom a
  have eq := interpolate x p q (natDegree_map_le.trans p) (natDegree_map_le.trans q)
    (S:=S) (T:=T) (by
      intro i
      have hs : S.eval (x i)=σ (P.eval (x i)) := by simpa only [sx] using se (x i)
      have ht : T.eval (x i)=σ (Q.eval (x i)) := by simpa only [sx] using te (x i)
      rw [hs,ht,given,map_mul,sy]
      ring)
  have h := congrArg (eval (σ u)) eq
  simp only [eval_mul,se,te,match',map_mul] at h
  apply mul_right_cancel₀ (show σ (Q.eval u)≠0 by simpa using nz)
  linear_combination h

private theorem pins {n d : ℕ} (big : 8*d<n) (A B : Fin n → ℕ) :
    ∃ r s : ℕ, ∃ f : Fin (2*d+1) ↪ Fin n, ∀ i, (A (f i)+r)%2=0 ∧ (B (f i)+s)%2=0 := by
  classical
  let color (i : Fin n) : Fin 2 × Fin 2 := (⟨A i%2,by omega⟩,⟨B i%2,by omega⟩)
  obtain ⟨p,_,size⟩ := exists_lt_card_fiber_of_mul_lt_card_of_maps_to (s:=univ) (t:=univ)
    (f:=color) (n:=2*d) (by simp) (by simpa using (by omega : 4*(2*d)<n))
  obtain ⟨f,rows⟩ := DyadicSevenCombinatorics.select (univ.filter fun i => color i=p) (2*d+1) (by omega)
  refine ⟨p.1,p.2,f,?_⟩
  intro i
  have h := (mem_filter.mp (rows i)).2
  have hx : A (f i)%2=p.1.val := congrArg (fun t : Fin 2 × Fin 2 => t.1.val) h
  have hy : B (f i)%2=p.2.val := congrArg (fun t : Fin 2 × Fin 2 => t.2.val) h
  omega

/-- A finite nonexceptional match has no signed opposite match. The definition
uses cleared denominators so that it also treats a pole at the opposite site. -/
def Clean (P Q : K[X]) (x y : K) : Prop :=
  Q.eval x≠0 ∧ P.eval x=y*Q.eval x ∧ P.eval (-x)≠y*Q.eval (-x) ∧ P.eval (-x)≠ -y*Q.eval (-x)

private theorem even {n d : ℕ} {z : K} (σ : K ≃+* K) (flip : σ z= -z) [CharZero K] (zn : z≠0)
    (P Q : K[X]) (p : P.natDegree≤d) (q : Q.natDegree≤d) (A B : Fin n → ℕ)
    (xi : Function.Injective (fun i => z^(A i))) (law : ∀ i, Clean P Q (z^(A i)) (z^(B i)))
    (f : Fin (2*d+1) ↪ Fin n) (pins : ∀ i, A (f i)%2=0 ∧ B (f i)%2=0) :
    ∀ i, A i%2=0 ∧ B i%2=0 := by
  let x : Fin (2*d+1) ↪ K := ⟨fun i => z^(A (f i)),xi.comp f.injective⟩
  let y (i : Fin (2*d+1)) := z^(B (f i))
  have sx (i : Fin (2*d+1)) : σ (x i)=x i := by
    change σ (z^_)=z^_; rw [DyadicParityGalois.action σ flip,ite_eq_left (pins i).1]
  have sy (i : Fin (2*d+1)) : σ (y i)=y i := by
    dsimp only [y]; rw [DyadicParityGalois.action σ flip,ite_eq_left (pins i).2]
  intro i
  obtain ⟨nz,here,plus,minus⟩ := law i
  have e := covariance σ p q x y sx sy (fun j => (law (f j)).2.1) nz here
  simp only [DyadicParityGalois.action σ flip] at e
  by_cases ex : A i%2=0 <;> by_cases ey : B i%2=0
  · exact ⟨ex,ey⟩
  · simp only [ex,ey,ite_true,ite_false] at e
    have diff := mul_right_cancel₀ nz (here.symm.trans e)
    exact False.elim ((pow_ne_zero (B i) zn) (by linear_combination diff/2))
  · exact False.elim (plus (by simpa [ex,ey] using e))
  · exact False.elim (minus (by simpa [ex,ey] using e))

private noncomputable def scale (a : K) (P : K[X]) := P.comp (C a*X)

private theorem scale_degree (a : K) (P : K[X]) : (scale a P).natDegree≤P.natDegree := by
  apply natDegree_comp_le.trans
  simpa using Nat.mul_le_mul_left P.natDegree (natDegree_C_mul_le a X)

@[simp] private theorem scale_eval (a : K) (P : K[X]) (x : K) :
    (scale a P).eval x=P.eval (a*x) := by simp [scale,eval_comp]

private theorem rotate {P Q : K[X]} {x y u v : K} (un : u≠0) (vn : v≠0)
    (law : Clean P Q x y) : Clean (C v*scale u⁻¹ P) (scale u⁻¹ Q) (x*u) (y*v) := by
  obtain ⟨nz,here,plus,minus⟩ := law
  have push : u⁻¹*(x*u)=x := by field_simp
  simp only [Clean,scale_eval,eval_mul,eval_C,mul_neg,push]
  refine ⟨nz,by rw [here];ring,?_,?_⟩
  · intro h
    apply plus
    apply mul_left_cancel₀ vn
    linear_combination h
  · intro h
    apply minus
    apply mul_left_cancel₀ vn
    linear_combination h

private theorem grid_size {n m : ℕ} {z : K} (hz : IsPrimitiveRoot z (2^m)) (A : Fin n → ℕ)
    (inj : Function.Injective (fun i => z^(A i))) : n≤2^m := by
  let g (i : Fin n) : Fin (2^m) := ⟨A i%2^m,Nat.mod_lt _ (by positivity)⟩
  have one : Function.Injective g := by
    intro i j eq
    apply inj
    simpa only [g,hz.eq_orderOf,pow_mod_orderOf] using congrArg (fun t : Fin (2^m) => z^t.val) eq
  simpa using Fintype.card_le_of_injective g one

/-- For a rational function of degree at most d over a normal extension of ℚ,
at most 8d distinct dyadic inputs can match dyadic outputs without a signed
antipodal match. Denominators need only be nonzero at the given inputs. -/
theorem bound [CharZero K] [Algebra ℚ K] [Normal ℚ K] {m d n : ℕ} (hd : 0<d) {z : K}
    (hz : IsPrimitiveRoot z (2^m)) (P Q : K[X]) (p : P.natDegree≤d) (q : Q.natDegree≤d)
    (A B : Fin n → ℕ) (inj : Function.Injective (fun i => z^(A i)))
    (law : ∀ i, Clean P Q (z^(A i)) (z^(B i))) : n≤8*d := by
  induction m generalizing z P Q A B with
  | zero => have h := grid_size hz A inj; simp at h; omega
  | succ m ih =>
    cases m with
    | zero => have h := grid_size hz A inj; norm_num at h; omega
    | succ k =>
      by_contra! big
      obtain ⟨r,s,f,ss⟩ := pins big A B
      obtain ⟨σ,flip⟩ := DyadicParityGalois.exists_flip hz
      have zn := hz.ne_zero (by positivity)
      let u := z^r
      let v := z^s
      have un : u≠0 := pow_ne_zero _ zn
      have vn : v≠0 := pow_ne_zero _ zn
      let P' := C v*scale u⁻¹ P
      let Q' := scale u⁻¹ Q
      have p' : P'.natDegree≤d := (natDegree_C_mul_le ..).trans ((scale_degree _ _).trans p)
      have q' : Q'.natDegree≤d := (scale_degree _ _).trans q
      let A' (i : Fin n) := A i+r
      let B' (i : Fin n) := B i+s
      have inj' : Function.Injective (fun i => z^(A' i)) := fun _ _ eq =>
        inj (mul_right_cancel₀ un (by simpa only [A',pow_add] using eq))
      have law' (i : Fin n) : Clean P' Q' (z^(A' i)) (z^(B' i)) := by
        simpa only [A',B',pow_add] using rotate un vn (law i)
      have par := even σ.toRingEquiv flip zn P' Q' p' q' A' B' inj' law' f ss
      have half (j : ℕ) (hj : j%2=0) : (z^2)^(j/2)=z^j := by
        rw [←pow_mul,show 2*(j/2)=j by omega]
      have root : IsPrimitiveRoot (z^2) (2^(k+1)) :=
        IsPrimitiveRoot.pow (by positivity) hz (by rw [pow_succ];omega)
      apply (Nat.not_le_of_gt big)
      apply ih root P' Q' p' q' (fun i => A' i/2) (fun i => B' i/2)
      · intro i j eq
        apply inj'
        change (z^2)^(A' i/2)=(z^2)^(A' j/2) at eq
        rwa [half _ (par i).1,half _ (par j).1] at eq
      · intro i
        rw [half _ (par i).1,half _ (par i).2]
        exact law' i

end ProximityGap.DyadicRationalParity
#print axioms ProximityGap.DyadicRationalParity.bound
