/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.DyadicSevenCombinatorics

/-! # The seven-site induction for projectivities on dyadic roots -/

namespace ProximityGap.DyadicSevenDescent
open Finset DyadicParityGalois DyadicSevenCombinatorics DyadicProjectiveDescent
variable {K : Type*} [Field K]

/-- The five distinct source sites excluded by the odd-coefficient conic. -/
def NoFive (z : K) : Prop := ∀ (q : ℕ), q%2=1 → ∀ B : K, B≠0 → B^2*z^q≠1 →
  ∀ x y : Fin 5 → ℕ, Function.Injective (fun i => z^(x i)) → Function.Injective (fun i => z^(y i)) →
  (∀ i, B*(z^(x i))*(z^(y i))+z^(x i)+z^(y i)+B*z^q=0) → False

/-- Any seven distinct finite site matches on this grid force a dihedral map. -/
def Rigid (z : K) : Prop := ∀ (A B : Fin 7 → ℕ), Function.Injective (fun i => z^(A i)) →
  Function.Injective (fun i => z^(B i)) → ∀ a b c d : K, a*d≠b*c →
  (∀ i, Graph a b c d (z^(A i)) (z^(B i))) → (b=0 ∧ c=0) ∨ (a=0 ∧ d=0)

private theorem half {z : K} {j : ℕ} (even : j%2=0) : (z^2)^(j/2)=z^j := by
  rw [←pow_mul,show 2*(j/2)=j by omega]

private theorem normalized [CharZero K] [Algebra ℚ K] [Normal ℚ K] {m : ℕ} {z : K}
    (root : IsPrimitiveRoot z (2^(m+2))) (smaller : Rigid (z^2)) (conic : NoFive (z^2))
    (A B : Fin 7 → ℕ) (injA : Function.Injective (fun i => z^(A i)))
    (injB : Function.Injective (fun i => z^(B i))) (a b c d : K) (det : a*d≠b*c)
    (edges : ∀ i, Graph a b c d (z^(A i)) (z^(B i))) (pins : Fin 3 ↪ Fin 7)
    (labels : ∀ i, A (pins i)%2=0 ∧ B (pins i)%2=0) : (b=0∧c=0) ∨ (a=0∧d=0) := by
  classical
  obtain ⟨σ,flip⟩ := exists_flip root
  have nz := root.ne_zero (by positivity)
  let e := (⟨fun i => z^(A (pins i)),injA.comp pins.injective⟩ : Fin 3 ↪ K)
  have fx (i : Fin 3) : σ.toRingEquiv (e i)=e i := by
    change σ.toRingEquiv (z^(A (pins i)))=z^(A (pins i))
    rw [action σ.toRingEquiv flip,ite_eq_left (labels i).1]
  have fy (i : Fin 3) : σ.toRingEquiv (z^(B (pins i)))=z^(B (pins i)) := by
    rw [action σ.toRingEquiv flip,ite_eq_left (labels i).2]
  have per (i : Fin 7) := parity σ.toRingEquiv flip nz det e (fun j => z^(B (pins j))) fx fy
    (fun j => edges (pins j)) (edges i)
  by_cases odd : ∃ j, A j%2=1
  · obtain ⟨j,hj⟩ := odd
    by_contra other
    let u := z^(A j)
    let v := z^(B j)
    have au := (per j).2 hj
    have nu : u≠0 := pow_ne_zero _ nz
    have nv : v≠0 := pow_ne_zero _ nz
    have sq (i : Fin 7) (hi : A i%2=1) : (z^(A i))^2=u^2 := by
      by_contra neq
      exact other (two_antipodal det neq (edges i) ((per i).2 hi) (edges j) au)
    let G := univ.filter fun i => A i%2=1
    have small : G.card≤2 := by
      let X (i : Fin 7) := z^(A i)
      have sub : G.image X⊆{u,-u} := by
        intro y hy
        obtain ⟨i,hi,rfl⟩ := mem_image.mp hy
        simpa only [mem_insert,mem_singleton] using sq_eq_sq_iff_eq_or_eq_neg.mp (sq i (mem_filter.mp hi).2)
      exact (card_image_of_injective G injA) ▸ (card_le_card sub).trans ((card_insert_le ..).trans (by simp))
    obtain ⟨f,good⟩ := select Gᶜ 5 (by simp only [card_compl,Fintype.card_fin];omega)
    have evenA (i : Fin 5) : A (f i)%2=0 := by
      have no : A (f i)%2≠1 := by simpa [G] using good i
      omega
    have evenB (i : Fin 5) : B (f i)%2=0 := (per _).1 ▸ evenA i
    let h := 2^(m+1)
    have nzH : 0<h := by dsimp [h];positivity
    have length : 2^(m+2)=h*2 := by dsimp [h];rw [show m+2=m+1+1 by omega,pow_succ]
    have sqr : (z^h)^2=1 := by rw [←pow_mul,←length];exact root.pow_eq_one
    have minus : z^h= -1 := (sq_eq_one_iff.mp sqr).resolve_left (root.pow_ne_one_of_pos_of_lt nzH.ne' (by omega))
    have smallRoot : IsPrimitiveRoot (z^2) h := by
      apply IsPrimitiveRoot.pow (by positivity) root
      omega
    let l := -u/v
    have minusO (t : ℕ) (ot : t%2=1) : (z^t)^h= -1 := by
      rw [←pow_mul,Nat.mul_comm,pow_mul,minus,(Nat.odd_iff.mpr ot).neg_one_pow]
    have lv : l^h=1 := by
      have ev : Even h := ⟨2^m,by dsimp [h];rw [pow_succ];omega⟩
      rw [show l= -u/v from rfl,div_pow,ev.neg_pow,show u^h= -1 from minusO _ hj,
        show v^h= -1 from minusO _ ((per j).1 ▸ hj),div_self (by norm_num)]
    obtain ⟨t,_,ht⟩ := smallRoot.eq_pow_of_pow_eq_one lv
    obtain ⟨P,nP,valid,law⟩ := normalize_antipodal det other nu nv (edges j) au
    let X (i : Fin 5) := A (f i)/2
    let Y (i : Fin 5) := t+B (f i)/2
    have Xeq (i : Fin 5) : (z^2)^(X i)=z^(A (f i)) := half (evenA i)
    have Yeq (i : Fin 5) : (z^2)^(Y i)=l*z^(B (f i)) := by dsimp only [Y];rw [pow_add,ht,half (evenB i)]
    have uq : (z^2)^(A j)=u^2 := by rw [←pow_mul,Nat.mul_comm,pow_mul]
    have nl : l≠0 := div_ne_zero (neg_ne_zero.mpr nu) nv
    apply conic (A j) hj P nP (uq ▸ valid) X Y
    · intro i j e
      apply f.injective;apply injA
      simpa only [Xeq] using e
    · intro i j e
      apply f.injective;apply injB
      apply mul_left_cancel₀ nl
      simpa only [Yeq] using e
    · intro i
      simpa only [Xeq,Yeq,uq] using law _ _ (edges (f i))
  · have allA (i : Fin 7) : A i%2=0 := by by_contra! no;exact odd ⟨i,by omega⟩
    have allB (i : Fin 7) : B i%2=0 := (per i).1 ▸ allA i
    refine smaller (fun i => A i/2) (fun i => B i/2) ?_ ?_ a b c d det ?_
    · intro i j h;exact injA (by simpa only [half (allA _)] using h)
    · intro i j h;exact injB (by simpa only [half (allB _)] using h)
    · intro i;simpa only [half (allA _),half (allB _)] using edges i

/-- One parity descent, including independent rotation of the source and
target grids to the common even quadrant. -/
theorem step [CharZero K] [Algebra ℚ K] [Normal ℚ K] {m : ℕ} {z : K}
    (root : IsPrimitiveRoot z (2^(m+2))) (smaller : Rigid (z^2)) (conic : NoFive (z^2)) : Rigid z := by
  intro A B injA injB a b c d det edges
  obtain ⟨r,s,f,valid⟩ := majority (quadrants (by omega : 0<m+1) root) det A B injA injB edges
  let A' (i : Fin 7) := A i+r
  let B' (i : Fin 7) := B i+s
  have nz := root.ne_zero (by positivity)
  have nx := pow_ne_zero r nz
  have ny := pow_ne_zero s nz
  have ax : Function.Injective (fun i => z^(A' i)) := fun _ _ h => injA (mul_right_cancel₀ nx (by simpa only [A',pow_add] using h))
  have bx : Function.Injective (fun i => z^(B' i)) := fun _ _ h => injB (mul_right_cancel₀ ny (by simpa only [B',pow_add] using h))
  have det' : (z^s*a)*(z^r*d)≠(z^s*z^r*b)*c := by
    intro eq
    apply det
    apply mul_left_cancel₀ (mul_ne_zero ny nx)
    linear_combination eq
  have edges' (i : Fin 7) : Graph (z^s*a) (z^s*z^r*b) c (z^r*d) (z^(A' i)) (z^(B' i)) := by
    have e := edges i
    dsimp only [Graph,A',B'] at e ⊢
    rw [pow_add,pow_add]
    linear_combination (z^s*z^r)*e
  have result := normalized root smaller conic A' B' ax bx _ _ _ _ det' edges' f valid
  simpa [nx,ny,mul_ne_zero ny nx] using result

end ProximityGap.DyadicSevenDescent
#print axioms ProximityGap.DyadicSevenDescent.step
