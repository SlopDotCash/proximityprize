/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.DyadicExceptionalConic
import ArkLib.Research.ProximityGap.Frontier.DyadicSevenCombinatorics

/-! # Pair classes of the conic in dyadic parity descent -/
namespace ProximityGap.DyadicConicPairs
open DyadicExceptionalConic DyadicCrossRatioParity
variable {L : Type*} [Field L] [Algebra ℚ L]
abbrev Edge := ℕ × ℕ

def prod (z : L) (e : Edge) : L := z^e.1*z^e.2
def paired (z B c : L) (e : Edge) : Prop := B*(prod z e+c)+z^e.1+z^e.2=0

def kind (e : Edge) : ℕ := e.1%2+e.2%2

/-- Canonical ordering puts the even site first whenever the pair is mixed. -/
def orient (x y : ℕ) : Edge := if x%2≤y%2 then (x,y) else (y,x)

theorem oriented (x y : ℕ) : (orient x y).1%2 ≤ (orient x y).2%2 := by
  unfold orient; split <;> simp_all <;> omega

theorem prod_orient (z : L) (x y : ℕ) : prod z (orient x y)=z^x*z^y := by
  unfold orient prod; split <;> simp [mul_comm]

theorem paired_orient {z B c : L} {x y : ℕ} (h : B*z^x*z^y+z^x+z^y+B*c=0) :
    paired z B c (orient x y) := by
  unfold orient; split <;> dsimp [paired,prod] <;> linear_combination h

private theorem share {B c : L} (det : B^2*c≠1) {x y u v : L}
    (h : B*(x*y+c)+x+y=0) (g : B*(u*v+c)+u+v=0) (same : x=u) : y=v := by
  subst u
  have nz : B*x+1≠0 := by
    intro bad
    apply det
    linear_combination B*h-(B*y+1)*bad
  apply mul_left_cancel₀ nz
  linear_combination h-g

/-- Distinct transposition products on the same nonsingular conic have
disjoint endpoints, allowing a loop within a pair. -/
theorem disjoint {z B c : L} (det : B^2*c≠1) {e f : Edge} (he : paired z B c e)
    (hf : paired z B c f) (hne : prod z e≠prod z f) :
    z^e.1≠z^f.1 ∧ z^e.1≠z^f.2 ∧ z^e.2≠z^f.1 ∧ z^e.2≠z^f.2 := by
  have rev {i : Edge} (h : paired z B c i) : B*(z^i.2*z^i.1+c)+z^i.2+z^i.1=0 := by
    dsimp [paired,prod] at h; linear_combination h
  change z^e.1*z^e.2≠z^f.1*z^f.2 at hne
  refine ⟨fun h => hne (by rw [h,share det he hf h]),?_,?_,?_⟩
  · intro h; exact hne (by rw [h,share det he (rev hf) h,mul_comm])
  · intro h; exact hne (by rw [h,share det (rev he) hf h,mul_comm])
  · intro h; exact hne (by rw [h,share det (rev he) (rev hf) h])

variable {m : ℕ} [IsCyclotomicExtension {2^(m+1)} ℚ L] {z : L}
variable (hm : 0<m) (hz : IsPrimitiveRoot z (2^(m+1))) (σ : L ≃ₐ[ℚ] L) (flip : σ z= -z)
variable {B c : L} (Bc : B≠0) (anti : σ c= -c)

include flip anti

private theorem conjugate {e : Edge} (h : paired z B c e) :
    σ B*((if e.1%2=0 then z^e.1 else -z^e.1)*(if e.2%2=0 then z^e.2 else -z^e.2)-c)+
      (if e.1%2=0 then z^e.1 else -z^e.1)+(if e.2%2=0 then z^e.2 else -z^e.2)=0 := by
  have g := congrArg σ h
  change σ (B*(z^e.1*z^e.2+c)+z^e.1+z^e.2)=σ 0 at g
  have act (i : ℕ) : σ (z^i) = _ := DyadicParityGalois.action σ.toRingEquiv flip i
  simpa only [map_add,map_mul,map_zero,anti,act,
    sub_eq_add_neg] using g

private theorem core_cross {e : Edge} (o : e.1%2 ≤ e.2%2) (k : kind e=1) (h : paired z B c e) :
    -(σ B)*(prod z e+c)+z^e.1-z^e.2=0 := by
  unfold kind at k
  have q := conjugate σ flip anti h
  simp only [if_pos (by omega : e.1%2=0),if_neg (by omega : e.2%2≠0)] at q
  dsimp [prod]; linear_combination q

private theorem core_same {e : Edge} {s : ℕ} (hs : s=0 ∨ s=2) (k : kind e=s) (h : paired z B c e) :
    (if s=0 then σ B else -σ B)*(prod z e-c)+z^e.1+z^e.2=0 := by
  unfold kind at k
  have q := conjugate σ flip anti h
  rcases hs with rfl|rfl
  · simp only [if_pos (by omega : e.1%2=0),if_pos (by omega : e.2%2=0)] at q
    simpa [prod] using q
  · simp only [if_neg (by omega : e.1%2≠0),if_neg (by omega : e.2%2≠0)] at q
    dsimp [prod]; linear_combination -q

include Bc in
/-- Two same-parity pairs of the same type cannot have different products. -/
theorem same_products {e f : Edge} {s : ℕ} (cs : s=0 ∨ s=2)
    (ek : kind e=s) (fk : kind f=s) (he : paired z B c e) (hf : paired z B c f)
    (cn : c≠0) : prod z e=prod z f := by
  let : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  by_contra neq
  let C : L := if s=0 then σ B else -σ B
  have a := core_same σ flip anti cs ek he
  have b := core_same σ flip anti cs fk hf
  change C*(prod z e-c)+z^e.1+z^e.2=0 at a
  change C*(prod z f-c)+z^f.1+z^f.2=0 at b
  unfold paired at he hf
  have eq : (B-C)*(prod z e-prod z f)=0 := by linear_combination he-hf-a+b
  obtain equal := sub_eq_zero.mp ((mul_eq_zero.mp eq).resolve_right (sub_ne_zero.mpr neq))
  rw [← equal] at a
  have impossible : 2*B*c=0 := by linear_combination he-a
  exact mul_ne_zero (mul_ne_zero (by norm_num) Bc) cn impossible

omit anti in
private theorem opposite_sites (zn : z≠0) {i j : ℕ} (opp : i%2≠j%2) :
    z^i≠z^j ∧ z^i+z^j≠0 := by
  let : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  have act (a : ℕ) : σ (z^a) = _ := DyadicParityGalois.action σ.toRingEquiv flip a
  have proof {x y : L} (xn : x≠0) (sx : σ x=x) (sy : σ y= -y) :
      x≠y ∧ x+y≠0 := by
    constructor
    · intro eq
      have k := congrArg σ eq
      rw [sx,sy] at k
      apply xn
      linear_combination (eq+k)/2
    · intro eq
      have k := congrArg σ eq
      rw [map_add,sx,sy,map_zero] at k
      apply xn
      linear_combination (eq+k)/2
  by_cases even : i%2=0
  · exact proof (pow_ne_zero _ zn) (by simp [act,even]) (by simp [act,show j%2≠0 by omega])
  · have a := proof (pow_ne_zero j zn) (by simp [act,show j%2=0 by omega])
        (by simp [act,even] : σ (z^i)= -z^i)
    exact ⟨a.1.symm,by simpa [add_comm] using a.2⟩

include hm hz in
private theorem two_cross_one_same {e f g : Edge}
    (oe : e.1%2≤e.2%2) (of' : f.1%2≤f.2%2)
    (ek : kind e=1) (fk : kind f=1) (gk : kind g=0 ∨ kind g=2)
    (he : paired z B c e) (hf : paired z B c f) (hg : paired z B c g)
    (det : B^2*c≠1) (neq : prod z e≠prod z f) : False := by
  let : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  have zn : z≠0 := by intro eq; simpa [eq] using hz.pow_eq_one
  have sep := disjoint det he hf neq
  have ec := core_cross σ flip anti oe ek he
  have fc := core_cross σ flip anti of' fk hf
  have em : e.1%2=0 ∧ e.2%2=1 := by unfold kind at ek; omega
  have fm : f.1%2=0 ∧ f.2%2=1 := by unfold kind at fk; omega
  unfold paired prod at he hf hg
  unfold prod at ec fc
  rcases gk with gk|gk
  · have gc := core_same σ flip anti (Or.inl rfl) gk (show paired z B c g from hg)
    have gp : g.1%2=g.2%2 := by unfold kind at gk; omega
    simp only [ite_true,prod] at gc
    have ne := opposite_sites σ flip zn (i:=e.1) (j:=e.2) (by omega)
    exact no_chord_identity hm hz _ _ _ _ _ (by omega : e.1%2=f.1%2) gp (by omega)
      ne.1 ne.2 (chord_identity (pow_ne_zero _ zn) sep.1 he ec hf fc hg gc)
  · have gc := core_same σ flip anti (Or.inr rfl) gk (show paired z B c g from hg)
    have gp : g.1%2=g.2%2 := by unfold kind at gk; omega
    norm_num [prod] at gc
    have ne := opposite_sites σ flip zn (i:=e.2) (j:=e.1) (by omega)
    apply no_chord_identity hm hz _ _ _ _ _ (by omega : e.2%2=f.2%2) gp (by omega) ne.1 ne.2
    exact chord_identity (C:= -σ B) (c:=c) (v:=z^f.1) (pow_ne_zero _ zn) sep.2.2.2
      (by linear_combination he) (by linear_combination -ec)
      (by linear_combination hf) (by linear_combination -fc) hg (by linear_combination gc)

private theorem three_cross {e f g : Edge}
    (oe : e.1%2≤e.2%2) (of' : f.1%2≤f.2%2) (og : g.1%2≤g.2%2)
    (ek : kind e=1) (fk : kind f=1) (gk : kind g=1)
    (he : paired z B c e) (hf : paired z B c f) (hg : paired z B c g)
    (ef : prod z e≠prod z f) (eg : prod z e≠prod z g) (fg : prod z f≠prod z g) : False := by
  let : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  let P := (B-σ B)/2
  let Q := (B+σ B)/2
  have poly {u : Edge} (ord : u.1%2≤u.2%2) (k : kind u=1) (h : paired z B c u) :
      P*Q*(prod z u+c)^2=prod z u := by
    have cross := core_cross σ flip anti ord k h
    unfold paired at h
    have one : P*(prod z u+c)= -z^u.1 := by dsimp [P]; linear_combination (h+cross)/2
    have two : Q*(prod z u+c)= -z^u.2 := by dsimp [Q]; linear_combination (h-cross)/2
    calc P*Q*(prod z u+c)^2 = (P*(prod z u+c))*(Q*(prod z u+c)) := by ring
         _ = prod z u := by rw [one,two]; simp [prod]
  have compare {x y : L} (hx : P*Q*(x+c)^2=x) (hy : P*Q*(y+c)^2=y) (ne : x≠y) :
      P*Q*(x+y+2*c)=1 := by
    have factor : (x-y)*(P*Q*(x+y+2*c)-1)=0 := by linear_combination hx-hy
    exact sub_eq_zero.mp ((mul_eq_zero.mp factor).resolve_left (sub_ne_zero.mpr ne))
  have a := compare (poly oe ek he) (poly of' fk hf) ef
  have b := compare (poly oe ek he) (poly og gk hg) eg
  have zero : (P*Q)*(prod z f-prod z g)=0 := by linear_combination a-b
  rw [(mul_eq_zero.mp zero).resolve_right (sub_ne_zero.mpr fg)] at a
  simp at a

omit flip anti in
private theorem inject_four {T : Type*} (x : Fin 4 → T) (h01 : x 0≠x 1)
    (h02 : x 0≠x 2) (h03 : x 0≠x 3) (h12 : x 1≠x 2) (h13 : x 1≠x 3) (h23 : x 2≠x 3) :
    Function.Injective x := by
  intro i j eq
  fin_cases i <;> fin_cases j <;> first | rfl | exact False.elim (by solve_by_elim [Ne.symm])

include hm hz flip in
omit anti in
private theorem one_each {g e h : Edge} (ge : kind g=0) (o : e.1%2≤e.2%2) (ec : kind e=1)
    (ho : kind h=2) (pg : paired z B c g) (pe : paired z B c e) (ph : paired z B c h)
    (det : B^2*c≠1) (ne₁ : prod z g≠prod z e) (ne₂ : prod z g≠prod z h)
    (ne₃ : prod z e≠prod z h) : False := by
  let A : Fin 4 → ℕ := ![g.1,e.1,e.2,h.1]
  let E : Fin 4 → ℕ := ![g.2,e.2,e.1,h.2]
  have dge := disjoint det pg pe ne₁
  have dgh := disjoint det pg ph ne₂
  have deh := disjoint det pe ph ne₃
  unfold kind at ge ec ho
  have zn : z≠0 := by intro eq; simpa [eq] using hz.pow_eq_one
  have d := (opposite_sites σ flip zn (i:=e.1) (j:=e.2) (by omega)).1
  have ax := inject_four (fun i => z^(A i)) dge.1 dge.2.1 dgh.1 d deh.1 deh.2.2.1
  have ey := inject_four (fun i => z^(E i)) dge.2.2.2 dge.2.2.1 dgh.2.2.2 d.symm deh.2.2.2 deh.2.1
  have ex := excludes_quadrants hm hz A E ax ey (by dsimp [A]; omega)
    (by dsimp [A]; omega) (by dsimp [A]; omega) (by dsimp [E]; omega)
    (by dsimp [E]; omega) (by dsimp [E]; omega)
  apply ex
  unfold paired prod at pg pe ph
  refine DyadicSevenCombinatorics.cross (a:= -1) (b:= -(B*c)) (c:=B) (d:=1) ?_
    (fun i => z^(A i)) (fun i => z^(E i)) ?_
  · intro eq; apply det; linear_combination eq
  · intro i
    fin_cases i <;> dsimp [A,E,DyadicParityGalois.Graph] <;>
      first | linear_combination -pg | linear_combination -pe | linear_combination -ph

include hm hz Bc in
/-- No three oriented conic edges can have three distinct products. -/
theorem no_three {e f g : Edge} (oe : e.1%2≤e.2%2) (of' : f.1%2≤f.2%2) (og : g.1%2≤g.2%2)
    (he : paired z B c e) (hf : paired z B c f) (hg : paired z B c g)
    (det : B^2*c≠1) (cn : c≠0) (ef : prod z e≠prod z f) (eg : prod z e≠prod z g)
    (fg : prod z f≠prod z g) : False := by
  have cases' (u : Edge) : kind u=0 ∨ kind u=1 ∨ kind u=2 := by unfold kind; omega
  rcases cases' e with ek|ek|ek <;> rcases cases' f with fk|fk|fk <;>
    rcases cases' g with gk|gk|gk
  · exact ef (same_products σ flip Bc anti (Or.inl rfl) ek fk he hf cn)
  · exact ef (same_products σ flip Bc anti (Or.inl rfl) ek fk he hf cn)
  · exact ef (same_products σ flip Bc anti (Or.inl rfl) ek fk he hf cn)
  · exact eg (same_products σ flip Bc anti (Or.inl rfl) ek gk he hg cn)
  · exact two_cross_one_same hm hz σ flip anti of' og fk gk (Or.inl ek) hf hg he det fg
  · exact one_each hm hz σ flip ek of' fk gk he hf hg det ef eg fg
  · exact eg (same_products σ flip Bc anti (Or.inl rfl) ek gk he hg cn)
  · exact one_each hm hz σ flip ek og gk fk he hg hf det eg ef fg.symm
  · exact fg (same_products σ flip Bc anti (Or.inr rfl) fk gk hf hg cn)
  · exact fg (same_products σ flip Bc anti (Or.inl rfl) fk gk hf hg cn)
  · exact two_cross_one_same hm hz σ flip anti oe og ek gk (Or.inl fk) he hg hf det eg
  · exact one_each hm hz σ flip fk oe ek gk hf he hg det ef.symm fg eg
  · exact two_cross_one_same hm hz σ flip anti oe of' ek fk (Or.inl gk) he hf hg det ef
  · exact three_cross σ flip anti oe of' og ek fk gk he hf hg ef eg fg
  · exact two_cross_one_same hm hz σ flip anti oe of' ek fk (Or.inr gk) he hf hg det ef
  · exact one_each hm hz σ flip gk oe ek fk hg he hf det eg.symm fg.symm ef
  · exact two_cross_one_same hm hz σ flip anti oe og ek gk (Or.inr fk) he hg hf det eg
  · exact fg (same_products σ flip Bc anti (Or.inr rfl) fk gk hf hg cn)
  · exact fg (same_products σ flip Bc anti (Or.inl rfl) fk gk hf hg cn)
  · exact one_each hm hz σ flip fk og gk ek hf hg he det fg ef.symm eg.symm
  · exact eg (same_products σ flip Bc anti (Or.inr rfl) ek gk he hg cn)
  · exact one_each hm hz σ flip gk of' fk ek hg hf he det fg.symm eg.symm ef.symm
  · exact two_cross_one_same hm hz σ flip anti of' og fk gk (Or.inr ek) hf hg he det fg
  · exact eg (same_products σ flip Bc anti (Or.inr rfl) ek gk he hg cn)
  · exact ef (same_products σ flip Bc anti (Or.inr rfl) ek fk he hf cn)
  · exact ef (same_products σ flip Bc anti (Or.inr rfl) ek fk he hf cn)
  · exact ef (same_products σ flip Bc anti (Or.inr rfl) ek fk he hf cn)

end ProximityGap.DyadicConicPairs
#print axioms ProximityGap.DyadicConicPairs.no_three
