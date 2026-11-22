/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.DyadicSevenDescent

/-! # Transfer of seven-site projective rigidity

After transporting the four-point determinant, three matched sites recover a
nonsingular matrix. Either of its two monomial forms implies a family of
equalities of powers, which transfer back without any further size bound.
-/
namespace ProximityGap.SevenSiteTransfer
open DyadicParityGalois DyadicSevenDescent CyclotomicProjectiveTransfer
variable {K L : Type*} [Field K] [Field L]

private theorem reduce {n : ℕ} {r : K} (h : IsPrimitiveRoot r n) (k : ℕ) :
    r^(k%n)=r^k := by rw [h.eq_orderOf]; exact pow_mod_orderOf _ _

/-- Equal powers at a primitive root give equal powers at every primitive root of the same order. -/
theorem powers {n : ℕ} (hn : 0<n) {z : K} {w : L}
    (hz : IsPrimitiveRoot z n) (hw : IsPrimitiveRoot w n) (i j : ℕ)
    (eq : z^i=z^j) : w^i=w^j := by
  have er : i%n=j%n := hz.pow_inj (Nat.mod_lt _ hn) (Nat.mod_lt _ hn)
    ((reduce hz i).trans (eq.trans (reduce hz j).symm))
  rw [← reduce hw i,← reduce hw j,er]

private theorem quadratic (X : Fin 7 → K) (inj : Function.Injective X) {a b c : K}
    (root : ∀ i, a*(X i)^2+b*(X i)+c=0) : a=0 ∧ c=0 := by
  have divisor (i j : Fin 7) (ne : i≠j) : a*(X i+X j)+b=0 := by
    have h : (X i-X j)*(a*(X i+X j)+b)=0 := by linear_combination root i-root j
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr (inj.ne ne))
  have one := divisor 0 1 (by decide)
  have two := divisor 0 2 (by decide)
  have h : a*(X 1-X 2)=0 := by linear_combination one-two
  have aa := (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr (inj.ne (by decide)))
  exact ⟨aa,by linear_combination root 0-X 0*one+(X 0*X 1)*aa⟩

private def pins (i : Fin 7) : Fin 4 → Fin 7 := ![0,1,2,i]

private theorem cross_graph {a b c d : K} (det : a*d≠b*c) (x y : Fin 4 → K)
    (law : ∀ i, Graph a b c d (x i) (y i)) : cross x y=0 := by
  let s : Fin 4 → Fin 4 := ![0,2,3,1]
  have h := DyadicSevenCombinatorics.cross det (fun i => x (s i)) (fun i => y (s i))
    (fun i => law (s i))
  dsimp [s] at h
  unfold cross
  linear_combination h

private theorem recover (x y : Fin 7 → K) (xi : Function.Injective x) (yi : Function.Injective y)
    (law : ∀ i, cross (fun j => x (pins i j)) (fun j => y (pins i j))=0) :
    ∃ a b c d : K, a*d≠b*c ∧ ∀ i, Graph a b c d (x i) (y i) := by
  let U := (x 0-x 2)*(y 1-y 2)
  let V := (x 1-x 2)*(y 0-y 2)
  let a := -U*y 0+V*y 1
  let b := U*x 1*y 0-V*x 0*y 1
  let c := -U+V
  let d := U*x 1-V*x 0
  have un : U≠0 := mul_ne_zero (sub_ne_zero.mpr (xi.ne (by decide))) (sub_ne_zero.mpr (yi.ne (by decide)))
  have vn : V≠0 := mul_ne_zero (sub_ne_zero.mpr (xi.ne (by decide))) (sub_ne_zero.mpr (yi.ne (by decide)))
  refine ⟨a,b,c,d,?_,?_⟩
  · rw [← sub_ne_zero,show a*d-b*c=U*V*(x 1-x 0)*(y 1-y 0) by dsimp [a,b,c,d];ring]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero un vn) (sub_ne_zero.mpr (xi.ne (by decide))))
      (sub_ne_zero.mpr (yi.ne (by decide)))
  · intro i
    have eq := law i
    dsimp [cross,pins] at eq
    dsimp [a,b,c,d,U,V,Graph]
    linear_combination eq

/-- A seven-site classification over any primitive comparison orbit implies
the same classification over the supplied prime-field orbit under the
four-point determinant height bound. -/
theorem transfer {p n : ℕ} [Fact p.Prime] [NeZero n] [NeZero (n : ZMod p)] [NeZero (n : K)]
    (hn : 2<n) {z : ZMod p} {w : K} (hz : IsPrimitiveRoot z n) (hw : IsPrimitiveRoot w n)
    (large : 16^n.totient<p^2) (rigid : Rigid w) : Rigid z := by
  intro A B ix iy a b c d det law
  let x (i : Fin 7) := z^(A i)
  let y (i : Fin 7) := z^(B i)
  let X (i : Fin 7) := w^(A i)
  let Y (i : Fin 7) := w^(B i)
  have xi : Function.Injective X := fun _ _ eq => ix (powers (by omega) hw hz _ _ eq)
  have yi : Function.Injective Y := fun _ _ eq => iy (powers (by omega) hw hz _ _ eq)
  have cr (i : Fin 7) : cross (fun j => X (pins i j)) (fun j => Y (pins i j))=0 := by
    exact CyclotomicProjectiveTransfer.transfer hn hz hw (fun j => A (pins i j)) (fun j => B (pins i j))
      (cross_graph det (fun j => x (pins i j)) (fun j => y (pins i j)) (fun j => law (pins i j))) large
  obtain ⟨α,β,γ,δ,nd,edges⟩ := recover X Y xi yi cr
  have xn : x 0≠0 := pow_ne_zero _ (hz.ne_zero (by omega))
  have yn : y 0≠0 := pow_ne_zero _ (hz.ne_zero (by omega))
  change ∀ i, a*x i+b=y i*(c*x i+d) at law
  change ∀ i, α*X i+β=Y i*(γ*X i+δ) at edges
  rcases rigid A B xi yi α β γ δ nd edges with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · simp only [add_zero,zero_mul,zero_add] at nd edges
    have dn : δ≠0 := right_ne_zero_of_mul nd
    have pr (i : Fin 7) : x i*y 0=x 0*y i := by
      have eq : X i*Y 0=X 0*Y i := by
        apply mul_left_cancel₀ dn
        linear_combination X 0*edges i-X i*edges 0
      dsimp [x,y,X,Y] at *
      rw [← pow_add,← pow_add] at eq ⊢
      exact powers (by omega) hw hz _ _ eq
    have q := quadratic x ix (a:=y 0*c) (b:=y 0*d-x 0*a) (c:= -(x 0*b)) (by
      intro i; linear_combination -(x 0)*law i+(c*x i+d)*pr i)
    exact Or.inl ⟨(mul_eq_zero.mp (neg_eq_zero.mp q.2)).resolve_left xn,
      (mul_eq_zero.mp q.1).resolve_left yn⟩
  · simp only [zero_mul,zero_add,add_zero,mul_zero] at nd edges
    have gn : γ≠0 := fun e => nd (by simp [e])
    have pr (i : Fin 7) : x i*y i=x 0*y 0 := by
      have eq : X i*Y i=X 0*Y 0 := by
        apply mul_left_cancel₀ gn
        linear_combination edges 0-edges i
      dsimp [x,y,X,Y] at *
      rw [← pow_add,← pow_add] at eq ⊢
      exact powers (by omega) hw hz _ _ eq
    have q := quadratic x ix (a:=a) (b:=b-c*(x 0*y 0)) (c:= -(d*(x 0*y 0))) (by
      intro i; linear_combination x i*law i+(c*x i+d)*pr i)
    exact Or.inr ⟨q.1,(mul_eq_zero.mp (neg_eq_zero.mp q.2)).resolve_right (mul_ne_zero xn yn)⟩

end ProximityGap.SevenSiteTransfer
#print axioms ProximityGap.SevenSiteTransfer.transfer
