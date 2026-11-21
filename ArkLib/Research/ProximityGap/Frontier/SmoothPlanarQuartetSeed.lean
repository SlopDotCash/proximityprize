/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.PlanarQuartetMass

/-! # Twelve disjoint pair coincidences for four planar cubics on sixteenth roots -/

set_option autoImplicit false
noncomputable section
namespace ArkLib.ProximityGap.Frontier.SmoothPlanarQuartetSeed

/-- Four planar cubics over the coefficient ring. The inputs satisfy
`b = w²` and `a = w¹⁴` for a primitive sixteenth root `w`. -/
def heads {K : Type*} [CommRing K] (b a t : K) : Fin 4 → K × K :=
  let R := t-a
  let S := t+a
  let C := t^2+b
  let D := t^2-a
  ![(0,0), (R*C-b*S*D,0), (R*C,S*C), (R*C,b*R*D)]

/-- Twice the oriented area of three planar points. -/
def det {K : Type*} [CommRing K] (p q r : K × K) : K :=
  (q.1-p.1)*(r.2-p.2)-(r.1-p.1)*(q.2-p.2)

/-- Pair coincidences and private owners in the sixteen fibers. -/
def group : Fin 16 → Finset (Fin 4) :=
  ![{0,1},{0},{0,1},{1},{0,1},{0,2},{1,2},{1,3},{2,3},{2},{2,3},{3},{2,3},{0,2},{0,3},{1,3}]

def owner : Fin 16 → Fin 4 := ![0,0,0,1,0,0,1,1,2,2,2,3,2,0,0,1]

variable {K : Type*} [Field K]

/-- The six edge locators split over the sixteenth roots in every characteristic
in which a primitive sixteenth root exists. -/
theorem factors (w t : K) (hw : w^8 = -1) :
    let b := w^2
    let a := w^14
    let R := t-a
    let S := t+a
    let C := t^2+b
    let D := t^2-a
    R*C-b*S*D = (1-b)*(t-1)*(t-w^2)*(t-w^4) ∧
    b*R*D-S*C = -(1-b)*(t-w^8)*(t-w^10)*(t-w^12) ∧
    C=(t-w^5)*(t-w^13) ∧ D=(t-w^7)*(t-w^15) ∧ S=t-w^6 := by
  dsimp only
  have hz : w^8+1=0 := by rw [hw]; ring
  constructor
  · linear_combination (t^2+w^22-w^14+w^8*(-t^2+t-1)+w^6*(1-t^2))*hz
  constructor
  · linear_combination (-t^2*w^8+t*w^10-t*w^2+w^24+w^16*(-t-1))*hz
  constructor
  · linear_combination (t*w^5-w^10+w^2)*hz
  constructor
  · linear_combination (t*w^7-w^14)*hz
  · linear_combination w^6*hz

private def sites : Fin 6 → Finset (Fin 16) :=
  ![{0,2,4}, {5,13}, {14}, {6}, {7,15}, {8,10,12}]
private def left : Fin 6 → Fin 4 := ![0,0,0,1,1,2]
private def right : Fin 6 → Fin 4 := ![1,2,3,2,3,3]
private def triangle : Fin 4 → Fin 3 → Fin 4 := ![![0,1,2],![0,1,3],![0,2,3],![1,2,3]]
private def edges : Fin 4 → Fin 3 → Fin 6 := ![![0,1,3],![0,2,4],![1,2,5],![3,4,5]]

private def loc (b a t : K) : Fin 6 → K :=
  let R := t-a
  let S := t+a
  let C := t^2+b
  let D := t^2-a
  ![R*C-b*S*D,C,R,S,D,b*R*D-S*C]

private theorem root_eq (w : K) (hw : orderOf w=16) (r : Fin 16) (e : Fin 6) :
    loc (w^2) (w^14) (w^r.val) e=0 ↔ r∈sites e := by
  have h8 : w^8 = -1 := by
    have h : (w^8)^2 = 1 := by rw [← pow_mul,show 8*2=orderOf w by omega,pow_orderOf_eq_one]
    exact (sq_eq_one_iff.mp h).resolve_left (fun e => by
      have hd := orderOf_dvd_of_pow_eq_one e
      rw [hw] at hd
      exact (by decide : ¬16 ∣ 8) hd)
  have p (j : ℕ) (hj : j<16) : w^r.val-w^j=0 ↔ r.val=j := by
    rw [sub_eq_zero]
    have hr : r.val < orderOf w := hw.symm ▸ r.isLt
    have he : j < orderOf w := hw.symm ▸ hj
    exact ⟨pow_injOn_Iio_orderOf hr he,fun h => by rw [h]⟩
  have hb : 1-w^2 ≠ 0 := by
    intro h
    have hd := orderOf_dvd_of_pow_eq_one (sub_eq_zero.mp h).symm
    rw [hw] at hd
    exact (by decide : ¬16 ∣ 2) hd
  obtain ⟨hA,hM,hC,hD,hS⟩ := factors w (w^r.val) h8
  have p0 := p 0 (by decide)
  rw [pow_zero] at p0
  fin_cases e
  · change (w^r.val-w^14)*((w^r.val)^2+w^2)-w^2*(w^r.val+w^14)*((w^r.val)^2-w^14)=0 ↔ r∈sites 0
    rw [hA]
    simp only [mul_eq_zero,hb,false_or,p0,p 2 (by decide),p 4 (by decide)]
    fin_cases r <;> decide
  · change ((w^r.val)^2+w^2)=0 ↔ r∈sites 1
    rw [hC]
    simp only [mul_eq_zero,p 5 (by decide),p 13 (by decide)]
    fin_cases r <;> decide
  · change (w^r.val-w^14)=0 ↔ r∈sites 2
    simp only [p 14 (by decide)]
    fin_cases r <;> decide
  · change (w^r.val+w^14)=0 ↔ r∈sites 3
    rw [hS]
    simp only [p 6 (by decide)]
    fin_cases r <;> decide
  · change ((w^r.val)^2-w^14)=0 ↔ r∈sites 4
    rw [hD]
    simp only [mul_eq_zero,p 7 (by decide),p 15 (by decide)]
    fin_cases r <;> decide
  · change w^2*(w^r.val-w^14)*((w^r.val)^2-w^14)-(w^r.val+w^14)*((w^r.val)^2+w^2)=0 ↔ r∈sites 5
    rw [hM]
    simp only [mul_eq_zero,neg_eq_zero,hb,false_or,p 8 (by decide),p 10 (by decide),p 12 (by decide)]
    fin_cases r <;> decide

private theorem edge_eq (b a t : K) (e : Fin 6) (hz : loc b a t e=0) :
    heads b a t (left e)=heads b a t (right e) := by
  let R := t-a
  let S := t+a
  let C := t^2+b
  let D := t^2-a
  fin_cases e
  · change R*C-b*S*D=0 at hz
    change ((0,0):K×K)=(R*C-b*S*D,0)
    rw [hz]
  · change C=0 at hz
    change ((0,0):K×K)=(R*C,S*C)
    simp [hz]
  · change R=0 at hz
    change ((0,0):K×K)=(R*C,b*R*D)
    simp [hz]
  · change S=0 at hz
    change (R*C-b*S*D,0)=(R*C,S*C)
    simp [hz]
  · change D=0 at hz
    change (R*C-b*S*D,0)=(R*C,b*R*D)
    simp [hz]
  · change b*R*D-S*C=0 at hz
    change (R*C,S*C)=(R*C,b*R*D)
    rw [sub_eq_zero.mp hz]

private theorem ordered_det (b a t : K) (hb : b≠0) (l : Fin 4)
    (h : ∀ v : Fin 3, loc b a t (edges l v)≠0) :
    det (heads b a t (triangle l 0)) (heads b a t (triangle l 1)) (heads b a t (triangle l 2))≠0 := by
  have hd : det (heads b a t (triangle l 0)) (heads b a t (triangle l 1)) (heads b a t (triangle l 2)) =
      (![1,b,1,b] : Fin 4 → K) l *
      loc b a t (edges l 0)*loc b a t (edges l 1)*loc b a t (edges l 2) := by
    fin_cases l <;> simp [triangle,heads,det,loc,edges] <;> ring
  rw [hd]
  apply mul_ne_zero (mul_ne_zero (mul_ne_zero _ (h 0)) (h 1)) (h 2)
  fin_cases l <;> simp [hb]

private def perm (a b c i j k : Fin 4) : Prop :=
  (a=i ∧ b=j ∧ c=k) ∨ (a=i ∧ b=k ∧ c=j) ∨ (a=j ∧ b=i ∧ c=k) ∨
  (a=j ∧ b=k ∧ c=i) ∨ (a=k ∧ b=i ∧ c=j) ∨ (a=k ∧ b=j ∧ c=i)

private instance (a b c i j k : Fin 4) : Decidable (perm a b c i j k) := by unfold perm; infer_instance

private theorem det_perm (z : Fin 4 → K × K) (a b c i j k : Fin 4)
    (hp : perm a b c i j k) (h : det (z i) (z j) (z k)≠0) : det (z a) (z b) (z c)≠0 := by
  rcases hp with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
  all_goals intro hz; apply h; unfold det at *; first | linear_combination hz | linear_combination -hz

/-- Every intended pair agrees. The owner and any two different foreign heads have
nonzero determinant at every quotient site. -/
theorem geometry (w : K) (hw : orderOf w=16) (r : Fin 16) :
    let z := heads (w^2) (w^14) (w^r.val)
    (∀ i, i∈group r → z i=z (owner r)) ∧
      (∀ i j, i∉group r → j∉group r → i≠j → det (z (owner r)) (z i) (z j)≠0) := by
  dsimp only
  have hb : w^2≠0 := pow_ne_zero _ (by intro h; simp [h] at hw)
  constructor
  · have cover : ∀ q i, i∈group q → i=owner q ∨
        ∃ e, i=right e ∧ owner q=left e ∧ q∈sites e := by decide
    intro i h
    rcases cover r i h with he|⟨e,hi,ho,he⟩
    · rw [he]
    · rw [hi,ho]
      exact (edge_eq _ _ _ e ((root_eq w hw r e).mpr he)).symm
  · have cover : ∀ q i j, i∉group q → j∉group q → i≠j → ∃ l,
        perm (owner q) i j (triangle l 0) (triangle l 1) (triangle l 2) ∧
          ∀ v, q∉sites (edges l v) := by decide
    intro i j hi hj hij
    obtain ⟨l,hp,he⟩ := cover r i j hi hj hij
    exact det_perm _ _ _ _ _ _ _ hp (ordered_det _ _ _ hb l
      (fun v hz => he v ((root_eq w hw r (edges l v)).mp hz)))

#print axioms geometry
end ArkLib.ProximityGap.Frontier.SmoothPlanarQuartetSeed
