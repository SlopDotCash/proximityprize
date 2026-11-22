/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Lagrange
import ArkLib.ToMathlib.Polynomial.RootMultiplicity
import ArkLib.Research.ProximityGap.Frontier.FourHeadCrossRatio

/-! # A four-head incidence bound

Three noncollinear degree-bounded heads and a distinct fourth admit a nonzero
quadratic evaluation minor. At each evaluation site, translating both
coordinates to the received pair makes every occupied row contribute a power
of the local parameter according to its selected monomial. The total weighted
overlap is therefore at most four times the degree.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace ProximityGap.FourHeadCoreDeterminant
open Finset Polynomial Matrix
variable {R : Type*} [CommRing R]
private def quad (j : Fin 3) (a b : R) : R := ![a*a,a*b,b*b] j
/-- The four columns evaluate one, the two coordinate functions, and one quadratic monomial. -/
def mat (j : Fin 3) (A B : Fin 4 → R) : Matrix (Fin 4) (Fin 4) R :=
  fun i => ![1,A i,B i,quad j (A i) (B i)]
private def minor (a b c d x y g h w : R) : R := (a*d-b*c)*w+(c*y-d*x)*g+(b*x-a*y)*h
private def red (j : Fin 3) (a b c d x y : R) :=
  minor a b c d x y (quad j a b) (quad j c d) (quad j x y)
private theorem reduce (j : Fin 3) (A B : Fin 4 → R) :
    (mat j A B).det = red j (A 1-A 0) (B 1-B 0) (A 2-A 0) (B 2-B 0) (A 3-A 0) (B 3-B 0) := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ,Matrix.det_fin_three, Matrix.submatrix_apply]
  fin_cases j <;> dsimp [mat,red,minor,quad,Fin.succAbove,Fin.insertNth] <;> ring

private theorem translate (j : Fin 3) (A B : Fin 4 → R) (a b : R) :
    (mat j A B).det = (mat j (fun i => A i-a) (fun i => B i-b)).det := by
  rw [reduce,reduce]
  simp only [sub_sub_sub_cancel_right]

private theorem choose_minor [IsDomain R] (a b c d x y : R)
    (hl : a*d-b*c≠0) (h0 : (x,y) ≠ (0,0)) (h1 : (x,y) ≠ (a,b)) (h2 : (x,y) ≠ (c,d)) :
    ∃ j, red j a b c d x y ≠ 0 := by
  by_contra! hn
  have ex := hn (0:Fin 3)
  have ey := hn (1:Fin 3)
  have ez := hn (2:Fin 3)
  dsimp [red,minor,quad] at ex ey ez
  let L := a*d-b*c
  let u := d*x-c*y
  let v := a*y-b*x
  have huu : u*(u-L)=0 := (mul_eq_zero.mp (show L*(u*(u-L))=0 by
    dsimp [L,u]; linear_combination d^2*ex-2*c*d*ey+c^2*ez)).resolve_left hl
  have hvv : v*(v-L)=0 := (mul_eq_zero.mp (show L*(v*(v-L))=0 by
    dsimp [L,v]; linear_combination b^2*ex-2*a*b*ey+a^2*ez)).resolve_left hl
  have huv : u*v=0 := (mul_eq_zero.mp (show L*(u*v)=0 by
    dsimp [u,v,L]; linear_combination -d*b*ex+(a*d+b*c)*ey-a*c*ez)).resolve_left hl
  have eqxy (s t : R) (hu : u=d*s-c*t) (hv : v=a*t-b*s) : (x,y)=(s,t) := by
    apply Prod.ext
    · apply sub_eq_zero.mp
      apply (mul_eq_zero.mp (show L*(x-s)=0 by
        dsimp [L,u,v] at *; linear_combination a*hu+c*hv)).resolve_left hl
    · apply sub_eq_zero.mp
      apply (mul_eq_zero.mp (show L*(y-t)=0 by
        dsimp [L,u,v] at *; linear_combination b*hu+d*hv)).resolve_left hl
  rcases mul_eq_zero.mp huv with hu|hv
  · rcases mul_eq_zero.mp hvv with hv|hv
    · exact h0 (eqxy 0 0 (by simpa using hu) (by simpa using hv))
    · exact h2 (eqxy c d (by rw [hu]; ring) (by rw [sub_eq_zero.mp hv]))
  · rcases mul_eq_zero.mp huu with hu|hu
    · exact h0 (eqxy 0 0 (by simpa using hu) (by simpa using hv))
    · exact h1 (eqxy a b (by rw [sub_eq_zero.mp hu]; dsimp [L]; ring) (by rw [hv]; ring))

private def weight : Fin 4 → ℕ := ![0,1,1,2]
/-- The least sum of the degrees of any `m` of the four columns. -/
def charge (m : ℕ) := m-1 + if m=4 then 1 else 0

private theorem charge_le (p : Fin 4 → Bool) :
    charge (∑ i, if p i then 1 else 0) ≤ ∑ i, if p i then weight i else 0 := by
  revert p
  decide

variable {F : Type*} [Field F]

private theorem local_dvd (j : Fin 3) (A B : Fin 4 → F[X]) (x u v : F) (S : Finset (Fin 4))
    (hS : ∀ i∈S, (A i).eval x=u ∧ (B i).eval x=v) :
    (X-C x)^charge S.card ∣ (mat j A B).det := by
  classical
  let M := mat j (fun i => A i-C u) (fun i => B i-C v)
  rw [translate j A B (C u) (C v), det_apply]
  apply dvd_sum
  intro σ _
  have hb := charge_le (fun i => decide (σ i ∈ S))
  simp only [decide_eq_true_eq] at hb
  have hs := Equiv.sum_comp σ (fun i => if i ∈ S then 1 else 0 : Fin 4 → ℕ)
  have hs' : (∑ i, if σ i ∈ S then 1 else 0) = S.card := hs.trans (by simp)
  rw [hs'] at hb
  have hd : (X-C x)^charge S.card ∣ ∏ i, M (σ i) i := by
    apply (pow_dvd_pow (X-C x) hb).trans
    rw [← prod_pow_eq_pow_sum]
    apply prod_dvd_prod_of_dvd
    intro i _
    by_cases hi : σ i ∈ S
    · simp only [hi,ite_true]
      obtain ⟨ha,hb'⟩ := hS _ hi
      have da : X-C x ∣ A (σ i)-C u := dvd_iff_isRoot.mpr (by simp [IsRoot,ha])
      have db : X-C x ∣ B (σ i)-C v := dvd_iff_isRoot.mpr (by simp [IsRoot,hb'])
      fin_cases i
      · simp [weight]
      · simpa [weight,M,mat] using da
      · simpa [weight,M,mat] using db
      · fin_cases j
        · simpa [weight,M,mat,quad,sq] using mul_dvd_mul da da
        · simpa [weight,M,mat,quad,sq] using mul_dvd_mul da db
        · simpa [weight,M,mat,quad,sq] using mul_dvd_mul db db
    · simp [hi]
  obtain ⟨w,hw⟩ := hd
  exact ⟨Equiv.Perm.sign σ • w, by change _ • (∏ i, M (σ i) i) = _; rw [hw,mul_smul_comm]⟩

private theorem degree_le (j : Fin 3) (A B : Fin 4 → F[X]) (d : ℕ)
    (ha : ∀ i, (A i).natDegree≤d) (hb : ∀ i, (B i).natDegree≤d) :
    (mat j A B).det.natDegree≤4*d := by
  rw [det_apply]
  apply natDegree_sum_le_of_forall_le
  intro σ _
  apply (natDegree_smul_le ..).trans <| (natDegree_prod_le ..).trans ?_
  have hh (i : Fin 4) : ((mat j A B) (σ i) i).natDegree≤weight i*d := by
    fin_cases i
    · simp [mat,weight]
    · simpa [mat,weight] using ha (σ 1)
    · simpa [mat,weight] using hb (σ 2)
    · fin_cases j <;> dsimp [mat,weight,quad] <;> apply natDegree_mul_le.trans <;>
        have a := ha (σ 3) <;> have b := hb (σ 3) <;> omega
  apply (sum_le_sum (fun i _ => hh i)).trans
  simp [Fin.sum_univ_succ,weight]
  omega

/-- One side from head zero and the opposite side in each of the three pairings. -/
def nearSide (v : Fin 4 → R) (i : Fin 3) := v i.succ - v 0

/-- The opposite side to the edge joining zero to the successor of the index. -/
def farSide (v : Fin 4 → R) : Fin 3 → R := ![v 3-v 2, v 3-v 1, v 2-v 1]

/-- Oriented determinant of three two-row heads. -/
def triangle (A B : Fin 4 → R) (i j k : Fin 4) :=
  (A j-A i)*(B k-B i)-(A k-A i)*(B j-B i)

set_option maxRecDepth 8192 in
/-- Discriminant of the quadratic pencil evaluated on the four heads. -/
theorem quadratic_discriminant (A B : Fin 4 → R) :
    (mat 1 A B).det^2 - (mat 0 A B).det*(mat 2 A B).det =
    triangle A B 0 1 2 * triangle A B 0 1 3 * triangle A B 0 2 3 * triangle A B 1 2 3 := by
  rw [reduce,reduce,reduce]
  dsimp [red,minor,quad,triangle]
  ring

private theorem opposite_identity (A B : Fin 4 → R) (i : Fin 3) :
    (mat 0 A B).det * (nearSide B i * farSide B i) -
    (mat 1 A B).det * (nearSide A i * farSide B i + nearSide B i * farSide A i) +
    (mat 2 A B).det * (nearSide A i * farSide A i) = 0 := by
  rw [reduce,reduce,reduce]
  fin_cases i <;> dsimp [nearSide,farSide,red,minor,quad,Fin.succ] <;> ring

/-- A deficit of at most `s` from the four-head core bound leaves three
polynomial coefficients of degree at most `s` for all three opposite-side
pairings. Their common discriminant is nonzero and has degree at most `2*s`. -/
theorem near_saturated_direction_form {I : Type*} [Fintype I] (D : I ↪ F)
    (u v : I → F) (A B : Fin 4 → F[X]) (d s : ℕ)
    (hA : ∀ i, (A i).natDegree ≤ d) (hB : ∀ i, (B i).natDegree ≤ d)
    (htr : triangle A B 0 1 2 * triangle A B 0 1 3 *
      triangle A B 0 2 3 * triangle A B 1 2 3 ≠ 0)
    (S : I → Finset (Fin 4))
    (hS : ∀ x, ∀ i ∈ S x, (A i).eval (D x) = u x ∧ (B i).eval (D x) = v x)
    (hinc : Fintype.card I + 4*d ≤ (∑ x, (S x).card) + s) :
    ∃ a b c : F[X], a.natDegree ≤ s ∧ b.natDegree ≤ s ∧ c.natDegree ≤ s ∧
      b^2-a*c ≠ 0 ∧ (b^2-a*c).natDegree ≤ 2*s ∧ ∀ i : Fin 3,
      a * (nearSide B i * farSide B i) -
      b * (nearSide A i * farSide B i + nearSide B i * farSide A i) +
      c * (nearSide A i * farSide A i) = 0 := by
  classical
  let L : F[X] := ∏ x, (X-C (D x)) ^ charge (S x).card
  have nonzero (x : I) : (X-C (D x)) ^ charge (S x).card ≠ 0 :=
    pow_ne_zero _ (X_sub_C_ne_zero _)
  have hL : L ≠ 0 := Finset.prod_ne_zero_iff.mpr fun x _ => nonzero x
  have degL : L.natDegree = ∑ x, charge (S x).card := by
    dsimp [L]
    rw [natDegree_prod _ _ (fun x _ => nonzero x)]
    simp
  have incidence := sum_le_sum (s := (univ : Finset I)) (f := fun x => (S x).card)
    (g := fun x => 1 + charge (S x).card) (fun x _ => by unfold charge; omega)
  simp only [sum_add_distrib, sum_const, card_univ, smul_eq_mul, mul_one] at incidence
  have bound : 4*d ≤ L.natDegree + s := by omega
  have coeff (j : Fin 3) : ∃ a : F[X], (mat j A B).det = L*a ∧ a.natDegree ≤ s := by
    have divides : L ∣ (mat j A B).det := by
      apply Fintype.prod_dvd_of_coprime
      · intro x y hxy
        exact (pairwise_coprime_X_sub_C D.injective hxy).pow
      · exact fun x => local_dvd j A B (D x) (u x) (v x) (S x) (hS x)
    obtain ⟨a,ha⟩ := divides
    refine ⟨a,ha,?_⟩
    by_cases hz : a = 0
    · simp [hz]
    · have hd := degree_le j A B d hA hB
      rw [ha,natDegree_mul hL hz] at hd
      omega
  obtain ⟨a,ha,da⟩ := coeff 0
  obtain ⟨b,hb,db⟩ := coeff 1
  obtain ⟨c,hc,dc⟩ := coeff 2
  refine ⟨a,b,c,da,db,dc,?_,?_,?_⟩
  · intro hz
    apply htr
    rw [← quadratic_discriminant,ha,hb,hc]
    linear_combination L^2 * hz
  · refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · rw [natDegree_pow]
      omega
    · exact natDegree_mul_le.trans (by omega)
  · intro i
    have h := opposite_identity A B i
    rw [ha,hb,hc] at h
    exact (mul_eq_zero.mp (show L * _ = 0 by linear_combination h)).resolve_left hL

/-- At full degree saturation, all three pairs of opposite projective side directions
are orthogonal for a single nonsingular constant symmetric form. -/
theorem saturated_direction_form (A B : Fin 4 → F[X]) (d : ℕ)
    (hA : ∀ i, (A i).natDegree ≤ d) (hB : ∀ i, (B i).natDegree ≤ d)
    (htr : triangle A B 0 1 2 * triangle A B 0 1 3 *
      triangle A B 0 2 3 * triangle A B 1 2 3 ≠ 0)
    (E : Finset F) (hE : E.card = 4*d)
    (hfit : ∀ x ∈ E, ∃ (S : Finset (Fin 4)) (u v : F), S.card = 2 ∧
      ∀ i ∈ S, (A i).eval x = u ∧ (B i).eval x = v) :
    ∃ a b c : F, b^2-a*c ≠ 0 ∧ ∀ i : Fin 3,
      C a * (nearSide B i * farSide B i) -
      C b * (nearSide A i * farSide B i + nearSide B i * farSide A i) +
      C c * (nearSide A i * farSide A i) = 0 := by
  classical
  let P := Lagrange.nodal E id
  have hP : P ≠ 0 := Lagrange.nodal_ne_zero
  have hdeg : P.natDegree ≤ 4*d := by rw [show P.natDegree = E.card from Lagrange.natDegree_nodal,hE]
  have coeff (i : Fin 3) : ∃ c : F, (mat i A B).det = C c * P := by
    by_contra! hh
    have h := FourHeadCrossRatio.pencil_charge_lt E (fun _ => 1) (mat i A B).det P (4*d)
      hP hh (degree_le i A B d hA hB) hdeg (by
        intro x hx
        obtain ⟨S,u,v,hS,h⟩ := hfit x hx
        simpa only [hS,show charge 2 = 1 by decide] using local_dvd i A B x u v S h)
      (fun x hx => by simpa only [pow_one,P,id_eq] using Lagrange.X_sub_C_dvd_nodal id hx)
    simp [hE] at h
  obtain ⟨a,ha⟩ := coeff 0
  obtain ⟨b,hb⟩ := coeff 1
  obtain ⟨c,hc⟩ := coeff 2
  refine ⟨a,b,c,?_,?_⟩
  · intro hyp
    apply htr
    rw [← quadratic_discriminant,ha,hb,hc]
    have hz : C (b^2-a*c) * P^2 = 0 := by rw [hyp,map_zero,zero_mul]
    simp only [map_sub,map_pow,map_mul] at hz
    linear_combination hz
  · intro i
    have h := opposite_identity A B i
    rw [ha,hb,hc] at h
    exact (mul_eq_zero.mp (show P * _ = 0 by linear_combination h)).resolve_left hP

/-- A linear representative of the projective involution on side directions. -/
def conjugateDirection (a b c : R) (u : R × R) : R × R :=
  (b*u.1-a*u.2, c*u.1-b*u.2)

/-- Applying the representative twice gives its nonzero projective scalar on a
nonsingular pencil. -/
theorem conjugateDirection_twice (a b c : R) (u : R × R) :
    conjugateDirection a b c (conjugateDirection a b c u) =
      ((b^2-a*c)*u.1,(b^2-a*c)*u.2) := by
  ext <;> dsimp [conjugateDirection] <;> ring

/-- The form equation identifies the opposite side with the conjugate projective
direction by vanishing of their two-by-two determinant. -/
theorem conjugateDirection_pair (a b c : R) (u v : R × R)
    (h : a*(u.2*v.2)-b*(u.1*v.2+u.2*v.1)+c*(u.1*v.1)=0) :
    (conjugateDirection a b c u).1*v.2-(conjugateDirection a b c u).2*v.1 = 0 := by
  dsimp [conjugateDirection]
  linear_combination -h

/-- If the first three polynomial heads are noncollinear and the fourth differs
from each, one quadratic evaluation minor is nonzero. -/
theorem exists_nonzero_minor (A B : Fin 4 → F[X])
    (htr : (A 1-A 0)*(B 2-B 0)-(B 1-B 0)*(A 2-A 0)≠0)
    (hneq : ∀ i : Fin 3, (A 3,B 3) ≠ (A i.castSucc,B i.castSucc)) :
    ∃ j, (mat j A B).det ≠ 0 := by
  have h (i : Fin 3) :
      (A 3-A 0,B 3-B 0) ≠ (A i.castSucc-A 0,B i.castSucc-B 0) := by
    simpa only [ne_eq,Prod.mk.injEq,sub_left_inj] using hneq i
  obtain ⟨j,hj⟩ := choose_minor (A 1-A 0) (B 1-B 0) (A 2-A 0) (B 2-B 0)
    (A 3-A 0) (B 3-B 0) htr (by simpa using h 0) (by simpa using h 1) (by simpa using h 2)
  exact ⟨j,by rwa [reduce]⟩

/-- Four noncollinear polynomial heads of degree at most `d` have at most `4d`
total excess core incidence, with an additional charge at each fourfold core. -/
theorem sum_charge_le {I : Type*} [Fintype I] (D : I ↪ F) (u v : I → F)
    (A B : Fin 4 → F[X]) (d : ℕ) (ha : ∀ i, (A i).natDegree≤d) (hb : ∀ i, (B i).natDegree≤d)
    (htr : (A 1-A 0)*(B 2-B 0)-(B 1-B 0)*(A 2-A 0)≠0)
    (hneq : ∀ i : Fin 3, (A 3,B 3) ≠ (A i.castSucc,B i.castSucc)) (S : I → Finset (Fin 4))
    (hS : ∀ x, ∀ i∈S x, (A i).eval (D x)=u x ∧ (B i).eval (D x)=v x) :
    ∑ x, charge (S x).card ≤ 4*d := by
  classical
  obtain ⟨j,hj⟩ := exists_nonzero_minor A B htr hneq
  let P := (mat j A B).det
  calc ∑ x, charge (S x).card ≤ ∑ x, P.rootMultiplicity (D x) := by
         apply sum_le_sum
         intro x _
         exact (le_rootMultiplicity_iff hj).mpr (local_dvd j A B (D x) (u x) (v x) (S x) (hS x))
       _ = ∑ x∈univ.image D, P.rootMultiplicity x := by rw [sum_image D.injective.injOn]
       _ ≤ P.natDegree := Polynomial.sum_rootMultiplicity_le_natDegree _
       _ ≤ _ := degree_le j A B d ha hb

/-- The four joint support sizes, plus the fourfold intersection size, never
exceed the size of their union plus four degree budgets. -/
theorem core_union_bound {I : Type*} [Fintype I] [DecidableEq I] (D : I ↪ F) (u v : I → F)
    (A B : Fin 4 → F[X]) (d : ℕ) (ha : ∀ i, (A i).natDegree≤d) (hb : ∀ i, (B i).natDegree≤d)
    (htr : (A 1-A 0)*(B 2-B 0)-(B 1-B 0)*(A 2-A 0)≠0)
    (hneq : ∀ i : Fin 3, (A 3,B 3) ≠ (A i.castSucc,B i.castSucc)) (C : Fin 4 → Finset I)
    (hc : ∀ j, ∀ x∈C j, (A j).eval (D x)=u x ∧ (B j).eval (D x)=v x) :
    (∑ j, (C j).card) + (C 0 ∩ C 1 ∩ C 2 ∩ C 3).card ≤ (univ.biUnion C).card + 4*d := by
  classical
  let S (x : I) := univ.filter fun j => x∈C j
  have h := sum_charge_le D u v A B d ha hb htr hneq S (fun x j hj => hc j x (mem_filter.mp hj).2)
  have eqsum : (∑ x, (S x).card) = ∑ j, (C j).card := by
    calc _ = ∑ x, ∑ j, if x∈C j then 1 else 0 := by simp [S]
         _ = _ := by rw [sum_comm]; simp
  let U := univ.biUnion C
  let T := C 0 ∩ C 1 ∩ C 2 ∩ C 3
  have eqpoint (x : I) :
      (S x).card+(if x∈T then 1 else 0) = (if x∈U then 1 else 0)+charge (S x).card := by
    have hfull : (S x).card=4 ↔ x∈T := by
      change (S x).card=Fintype.card (Fin 4) ↔ _
      rw [card_eq_iff_eq_univ]
      simp [S,T,Fin.forall_fin_succ]
    have hempty : (S x).card=0 ↔ x∉U := by simp [S,U,filter_eq_empty_iff]
    simp only [charge,hfull]
    by_cases hu : x∈U
    · have hp : (S x).card≠0 := fun hz => hempty.mp hz hu
      simp only [hu,ite_true]
      omega
    · have hz := hempty.mpr hu
      simp [hu,hz]
  have ht := Finset.sum_congr (s₁:=univ) rfl (fun x _ => eqpoint x)
  simp only [sum_add_distrib,eqsum] at ht
  simp at ht
  exact ht.le.trans (Nat.add_le_add_left h _)

/-- Every injective domain attains the weighted overlap bound at any chosen set
of degree-budget sites. These are full joint agreement cores with fixed zero rows. -/
theorem core_union_sharp {I : Type*} [Fintype I] [DecidableEq I] (D : I ↪ F) (T : Finset I) :
    ∃ (A B : Fin 4 → F[X]) (C : Fin 4 → Finset I),
      (∀ j, (A j).natDegree≤T.card ∧ (B j).natDegree≤T.card) ∧
      (A 1-A 0)*(B 2-B 0)-(B 1-B 0)*(A 2-A 0)≠0 ∧
      (∀ i : Fin 3, (A 3,B 3) ≠ (A i.castSucc,B i.castSucc)) ∧
      (∀ j x, x∈C j ↔ (A j).eval (D x)=0 ∧ (B j).eval (D x)=0) ∧
      (∑ j, (C j).card) + (C 0 ∩ C 1 ∩ C 2 ∩ C 3).card = (univ.biUnion C).card+4*T.card := by
  classical
  let P := Lagrange.nodal T D
  have hp : P≠0 := Lagrange.nodal_ne_zero
  have hd : P.natDegree=T.card := Lagrange.natDegree_nodal
  have hr (x : I) : P.eval (D x)=0 ↔ x∈T := by
    refine ⟨fun h => by_contra fun hx => ?_,Lagrange.eval_nodal_at_node⟩
    exact (Lagrange.eval_nodal_not_at_node (s:=T) (v:=D) (x:=D x) (fun i hi he => hx ((D.injective he).symm ▸ hi))) h
  refine ⟨![0,P,0,P],![0,0,P,P],![univ,T,T,T],?_,?_,?_,?_,?_⟩
  · intro j; fin_cases j <;> simp [hd]
  · simpa using mul_ne_zero hp hp
  · intro i; fin_cases i <;> simp [hp]
  · intro j x; fin_cases j <;> simp [hr]
  · have hun : univ.biUnion (![univ,T,T,T] : Fin 4 → Finset I)=univ := by
      apply eq_univ_of_forall; intro x
      exact mem_biUnion.mpr ⟨0,mem_univ _,mem_univ _⟩
    rw [hun]
    simp [Fin.sum_univ_succ]
    omega

/-- A folded witness exceeding the displayed incidence budget lies on one of
the four heads, at its original field scalar. -/
theorem folded_witness_on_head {I : Type*} [Fintype I] [DecidableEq I] (D : I ↪ F) (u v : I → F)
    (A B : Fin 4 → F[X]) (d : ℕ) (ha : ∀ i, (A i).natDegree≤d) (hb : ∀ i, (B i).natDegree≤d)
    (htr : (A 1-A 0)*(B 2-B 0)-(B 1-B 0)*(A 2-A 0)≠0)
    (hneq : ∀ i : Fin 3, (A 3,B 3) ≠ (A i.castSucc,B i.castSucc)) (C : Fin 4 → Finset I)
    (hc : ∀ j, ∀ x∈C j, (A j).eval (D x)=u x ∧ (B j).eval (D x)=v x)
    (z : F) (p : F[X]) (hp : p.natDegree≤d) (S : Finset I)
    (hs : ∀ x∈S, p.eval (D x)=u x+z*v x)
    (hsize : Fintype.card I+8*d < S.card+(∑ j, (C j).card)+(C 0 ∩ C 1 ∩ C 2 ∩ C 3).card) :
    ∃ j, p=A j+Polynomial.C z*B j := by
  classical
  by_contra! hout
  have hu := core_union_bound D u v A B d ha hb htr hneq C hc
  have hi (j : Fin 4) : (S∩C j).card≤d := by
    let f := p-(A j+Polynomial.C z*B j)
    have ne : f≠0 := sub_ne_zero.mpr (hout j)
    have sub : (S∩C j).image D ⊆ f.roots.toFinset := by
      intro x hx
      obtain ⟨i,h,rfl⟩ := mem_image.mp hx
      obtain ⟨l,r⟩ := mem_inter.mp h
      obtain ⟨a,b⟩ := hc j i r
      exact Multiset.mem_toFinset.mpr ((mem_roots ne).mpr (by simp [f,IsRoot,hs i l,a,b]))
    have h := card_le_card sub
    rw [card_image_of_injective _ D.injective] at h
    exact h.trans <| (Multiset.toFinset_card_le _).trans <| (card_roots' _).trans <|
      (natDegree_sub_le ..).trans (max_le hp (natDegree_add_le_of_degree_le (ha j) ((natDegree_C_mul_le z _).trans (hb j))))
  let U := univ.biUnion C
  have sub : S ⊆ (univ.biUnion fun j => S∩C j) ∪ (univ \ U) := by
    intro x hx
    by_cases h : x∈U
    · obtain ⟨j,hj,hxj⟩ := mem_biUnion.mp h
      exact mem_union_left _ (mem_biUnion.mpr ⟨j,hj,mem_inter.mpr ⟨hx,hxj⟩⟩)
    · exact mem_union_right _ (mem_sdiff.mpr ⟨mem_univ _,h⟩)
  have hparts : (univ.biUnion fun j => S∩C j).card≤4*d := by
    exact card_biUnion_le.trans ((sum_le_sum fun j _ => hi j).trans_eq (by simp))
  have houtside := card_sdiff_add_card_eq_card (subset_univ U)
  rw [card_univ] at houtside
  have upper := (card_le_card sub).trans (card_union_le ..)
  change _ ≤ U.card+4*d at hu
  omega

#print axioms near_saturated_direction_form
#print axioms quadratic_discriminant
#print axioms saturated_direction_form
#print axioms conjugateDirection_twice
#print axioms conjugateDirection_pair
#print axioms exists_nonzero_minor
#print axioms sum_charge_le
#print axioms core_union_bound
#print axioms core_union_sharp
#print axioms folded_witness_on_head
end ProximityGap.FourHeadCoreDeterminant
