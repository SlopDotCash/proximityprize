/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Data.Polynomial.FiniteDomainQuotient
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Extensions.Data.CodingTheory.ProximityGap.Errors
import ArkLib.ToMathlib.Polynomial.CompositionDegree
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic

/-! # Counting consecutive equal singleton syndromes on multiplicative domains -/
set_option autoImplicit false
namespace ProximityGap.SyndromeMotion
open Finset Polynomial
variable {F : Type} [Field F]

noncomputable def turn (g : F) (P Q : F[X]) :=
  P.comp (C g*X)*Q - P*Q.comp (C g*X)

private theorem same_degree_of_turn_zero (g : F) (hg : g≠0) (P Q : F[X])
    (hp : P≠0) (hq : Q≠0) (hdp : P.natDegree<orderOf g) (hdq : Q.natDegree<orderOf g)
    (h : turn g P Q=0) : P.natDegree=Q.natDegree := by
  have hC : (C g*X).natDegree ≠ 0 := by simp [hg]
  have he := congrArg leadingCoeff (sub_eq_zero.mp h)
  simp only [leadingCoeff_mul,leadingCoeff_comp hC,leadingCoeff_C,leadingCoeff_X,mul_one] at he
  apply pow_injOn_Iio_orderOf hdp hdq
  have hLC : P.leadingCoeff*Q.leadingCoeff ≠0 := mul_ne_zero
    (leadingCoeff_ne_zero.mpr hp) (leadingCoeff_ne_zero.mpr hq)
  apply mul_left_cancel₀ hLC
  linear_combination he

/-- The folded two-column determinant is nonzero whenever the two evaluation
rows take projectively distinct values and the shift order exceeds their degree. -/
theorem turn_ne_zero (g : F) (hg : g≠0) (P Q : F[X]) (hdp : P.natDegree<orderOf g)
    (hdq : Q.natDegree<orderOf g) (x y : F) (hxy : P.eval x*Q.eval y ≠ P.eval y*Q.eval x) :
    turn g P Q≠0 := by
  have hp : P≠0 := by rintro rfl; simp at hxy
  have hq : Q≠0 := by rintro rfl; simp at hxy
  intro h
  have deg := same_degree_of_turn_zero g hg P Q hp hq hdp hdq h
  let c := P.leadingCoeff / Q.leadingCoeff
  have hc : c≠0 := div_ne_zero (leadingCoeff_ne_zero.mpr hp) (leadingCoeff_ne_zero.mpr hq)
  let R := P-C c*Q
  have hr : R≠0 := by
    intro hz
    have he := sub_eq_zero.mp hz
    rw [he] at hxy
    simp only [eval_mul,eval_C] at hxy
    exact hxy (by ring)
  have hdeg : R.natDegree<P.natDegree := by
    apply natDegree_lt_natDegree hr
    apply degree_sub_lt_left _ hp
    · simp [c,leadingCoeff_ne_zero.mpr hq]
    · simp [degree_eq_natDegree hp,degree_eq_natDegree hq,hc,deg]
  have ht : turn g R Q=0 := by
    dsimp [turn,R] at h ⊢
    simp only [sub_comp,mul_comp,C_comp]
    linear_combination h
  have heq := same_degree_of_turn_zero g hg R Q hr hq (hdeg.trans hdp) hdq ht
  omega

/-- The coefficient of degree `2*d` cancels in a folded two-column determinant. -/
theorem turn_natDegree_lt (g : F) (P Q : F[X]) (d : ℕ) (hp : P.natDegree ≤ d)
    (hq : Q.natDegree ≤ d) (hn : turn g P Q ≠ 0) : (turn g P Q).natDegree < 2*d := by
  have hp' := (natDegree_comp_C_mul_X_le P g).trans hp
  have hq' := (natDegree_comp_C_mul_X_le Q g).trans hq
  have hle : (turn g P Q).natDegree ≤ d+d := (natDegree_sub_le ..).trans
    (max_le ((natDegree_mul_le ..).trans (Nat.add_le_add hp' hq))
      ((natDegree_mul_le ..).trans (Nat.add_le_add hp hq')))
  have zero : (turn g P Q).coeff (d+d) = 0 := by
    simp only [turn, coeff_sub, coeff_mul_add_eq_of_natDegree_le hp' hq,
      coeff_mul_add_eq_of_natDegree_le hp hq', comp_C_mul_X_coeff]
    ring
  by_contra! h
  have eq : d+d = (turn g P Q).natDegree := by omega
  rw [eq] at zero
  exact (leadingCoeff_ne_zero.mpr hn) zero

/-- The common zeros count twice, and each equal projective value at a
consecutive pair contributes one additional root of the shift determinant. -/
theorem common_twice_add_edges_strict [DecidableEq F] (g : F) (hg : g≠0) (P Q : F[X])
    (d : ℕ) (hp : P.natDegree≤d) (hq : Q.natDegree≤d) (hord : d<orderOf g)
    (x y : F) (hxy : P.eval x*Q.eval y ≠ P.eval y*Q.eval x)
    (Z A : Finset F) (hz : ∀ z∈Z, P.eval z=0 ∧ Q.eval z=0)
    (ha : ∀ z∈A, z∉Z ∧ g*z∉Z ∧ P.eval (g*z)*Q.eval z=P.eval z*Q.eval (g*z)) :
    2*Z.card+(insert 0 A).card < 2*d := by
  classical
  let V := Lagrange.nodal Z id
  have hv : V≠0 := Lagrange.nodal_ne_zero
  have vd : V.natDegree=Z.card := Lagrange.natDegree_nodal
  obtain ⟨p,hp'⟩ := zeroOn_iff_nodal_dvd.mp (fun z ht => (hz z ht).1)
  obtain ⟨q,hq'⟩ := zeroOn_iff_nodal_dvd.mp (fun z ht => (hz z ht).2)
  change P=V*p at hp'
  change Q=V*q at hq'
  have hred : p.eval x*q.eval y ≠ p.eval y*q.eval x := by
    intro he
    apply hxy
    rw [hp',hq']
    simp only [eval_mul]
    linear_combination (V.eval x*V.eval y)*he
  have pn : p≠0 := by rintro rfl; simp at hred
  have qn : q≠0 := by rintro rfl; simp at hred
  rw [hp',natDegree_mul hv pn,vd] at hp
  rw [hq',natDegree_mul hv qn,vd] at hq
  let D := turn g p q
  have hn : D≠0 := turn_ne_zero g hg p q (by omega) (by omega) x y hred
  have sub : A ⊆ D.roots.toFinset := by
    intro z hzA
    obtain ⟨h₁,h₂,h⟩ := ha z hzA
    have v₁ : V.eval z≠0 := Lagrange.eval_nodal_not_at_node (fun i hi he => h₁ (he ▸ hi))
    have v₂ : V.eval (g*z)≠0 := Lagrange.eval_nodal_not_at_node (fun i hi he => h₂ (he ▸ hi))
    rw [hp',hq'] at h
    simp only [eval_mul] at h
    rw [Multiset.mem_toFinset,mem_roots hn]
    change (turn g p q).eval z=0
    simp only [turn,eval_sub,eval_comp,eval_mul,eval_C,eval_X]
    apply (mul_eq_zero.mp (show V.eval (g*z)*V.eval z*
      (p.eval (g*z)*q.eval z-p.eval z*q.eval (g*z))=0 by linear_combination h)).resolve_left
    exact mul_ne_zero v₂ v₁
  have sub' : insert 0 A ⊆ D.roots.toFinset := by
    apply insert_subset _ sub
    rw [Multiset.mem_toFinset,mem_roots hn]
    simp [D,turn]
  have bound := (card_le_card sub').trans ((Multiset.toFinset_card_le _).trans (card_roots' D))
  have size := turn_natDegree_lt g p q (d-Z.card) (by omega) (by omega) hn
  change D.natDegree < _ at size
  omega

/-- The common zeros count twice, and each equal projective value at a
consecutive pair contributes one additional root of the shift determinant. -/
theorem common_twice_add_edges_le [DecidableEq F] (g : F) (hg : g≠0) (P Q : F[X])
    (d : ℕ) (hp : P.natDegree≤d) (hq : Q.natDegree≤d) (hord : d<orderOf g)
    (x y : F) (hxy : P.eval x*Q.eval y ≠ P.eval y*Q.eval x)
    (Z A : Finset F) (hz : ∀ z∈Z, P.eval z=0 ∧ Q.eval z=0)
    (ha : ∀ z∈A, z∉Z ∧ g*z∉Z ∧ P.eval (g*z)*Q.eval z=P.eval z*Q.eval (g*z)) :
    2*Z.card+A.card ≤ 2*d := by
  have bound := common_twice_add_edges_strict g hg P Q d hp hq hord x y hxy Z A hz ha
  have hc := card_le_card (subset_insert 0 A)
  omega

private def weights (γ : Fin 4 → F) : Fin 4 → F := ![
    (γ 1-γ 2)*(γ 1-γ 3)*(γ 2-γ 3),
    -(γ 0-γ 2)*(γ 0-γ 3)*(γ 2-γ 3),
    (γ 0-γ 1)*(γ 0-γ 3)*(γ 1-γ 3),
    -(γ 0-γ 1)*(γ 0-γ 2)*(γ 1-γ 2)]

private noncomputable def checkRow (w : Fin 4 → F) (P : Fin 4 → F[X]) :=
  ∑ j, C (w j)*P j

private theorem check_deg {w : Fin 4 → F} {P : Fin 4 → F[X]} {d : ℕ}
    (hdeg : ∀ j, (P j).natDegree ≤ d) : (checkRow w P).natDegree≤d := by
  refine (natDegree_sum_le ..).trans ?_
  simp only [Finset.fold_max_le]
  exact ⟨Nat.zero_le _, fun j _ => (natDegree_C_mul_le ..).trans (hdeg j)⟩

private theorem check_eval {w γ : Fin 4 → F} {P : Fin 4 → F[X]} (x u v : F)
    (hw : ∑ j, w j=0) (hγ : ∑ j, w j*γ j=0) :
    (checkRow w P).eval x = ∑ j, w j*((P j).eval x - (u+γ j*v)) := by
  simp only [checkRow,eval_finsetSum,eval_mul,eval_C,mul_sub,mul_add,sum_sub_distrib,
    sum_add_distrib,← mul_assoc,← sum_mul, hw,hγ,zero_mul,add_zero,sub_zero]

/-- On a coordinate with at most one missed label, two polynomial parity checks
recover that label as their ratio. Both checks vanish at a common fit. -/
theorem four_check_rows (γ : Fin 4 → F) (hγ : Function.Injective γ) (P : Fin 4 → F[X])
    (d : ℕ) (hp : ∀ j, (P j).natDegree≤d) (u v : F → F) :
    ∃ s r : F[X], s.natDegree≤d ∧ r.natDegree≤d ∧ ∀ z a,
      (∀ b≠a, (P b).eval z=u z+γ b*v z) →
        r.eval z=γ a*s.eval z ∧ (s.eval z=0 ↔ (P a).eval z=u z+γ a*v z) := by
  classical
  let w := weights γ
  let w' := fun a => w a*γ a
  have wh0 : ∑ a, w a=0 := by simp [w,weights,Fin.sum_univ_succ]; ring
  have wh1 : ∑ a, w a*γ a=0 := by simp [w,weights,Fin.sum_univ_succ]; ring
  have wh2 : ∑ a, w' a*γ a=0 := by simp [w',w,weights,Fin.sum_univ_succ]; ring
  have wn (a : Fin 4) : w a ≠ 0 := by
    fin_cases a <;> simp [w,weights,sub_ne_zero,hγ.eq_iff]
  let s := checkRow w P
  let r := checkRow w' P
  let err := fun z a => (P a).eval z-(u z+γ a*v z)
  have val (z : F) (a : Fin 4) (h : ∀ b≠a, (P b).eval z=u z+γ b*v z) :
      s.eval z = w a*err z a ∧ r.eval z = w' a*err z a := by
    constructor
    · dsimp only [s]
      rw [check_eval z (u z) (v z) wh0 wh1, sum_eq_single a]
      · intro b _ hb; simp [h b hb]
      · simp
    · dsimp only [r]
      rw [check_eval z (u z) (v z) wh1 wh2, sum_eq_single a]
      · intro b _ hb; simp [h b hb]
      · simp
  refine ⟨s,r,check_deg hp,check_deg hp,?_⟩
  intro z a ha
  obtain ⟨sx,rx⟩ := val z a ha
  rw [sx,rx]
  exact ⟨by dsimp [w']; ring, by simp [err,wn a,sub_eq_zero]⟩

/-- Four literal affine-word decoding polynomials on a multiplicative domain
obey the transition inequality. Z contains common agreements. The set A marks
consecutive coordinates admitting the same possible singleton error. Two
distinct, genuinely missed singleton colors ensure independent check rows. -/
theorem four_fits_motion_strict [DecidableEq F] (g : F) (hg : g≠0) (d : ℕ)
    (hord : d<orderOf g) (γ : Fin 4 → F) (hγ : Function.Injective γ)
    (P : Fin 4 → F[X]) (hp : ∀ j, (P j).natDegree≤d) (u v : F → F)
    (Z A : Finset F)
    (hz : ∀ z∈Z, ∀ i, (P i).eval z=u z+γ i*v z)
    (ha : ∀ z∈A, z∉Z ∧ g*z∉Z ∧ ∃ i, ∀ j ≠ i,
      (P j).eval z=u z+γ j*v z ∧ (P j).eval (g*z)=u (g*z)+γ j*v (g*z))
    (x y : F) (i j : Fin 4) (hij : i≠j)
    (hx : ∀ a≠i, (P a).eval x = u x+γ a*v x)
    (hy : ∀ a≠j, (P a).eval y = u y+γ a*v y)
    (hxi : (P i).eval x≠u x+γ i*v x) (hyj : (P j).eval y≠u y+γ j*v y) :
    2*Z.card + (insert 0 A).card < 2*d := by
  classical
  obtain ⟨s,r,sd,rd,val⟩ := four_check_rows γ hγ P d hp u v
  refine common_twice_add_edges_strict g hg s r d sd rd hord x y ?_ Z A ?_ ?_
  · obtain ⟨rx,sx⟩ := val x i hx
    obtain ⟨ry,sy⟩ := val y j hy
    have sn := mul_ne_zero (mt sx.mp hxi) (mt sy.mp hyj)
    rw [ry,rx]
    intro he
    exact hγ.ne hij (mul_right_cancel₀ sn (by linear_combination -he))
  · intro z h
    obtain ⟨hr,hs⟩ := val z 0 (fun a _ => hz z h a)
    have z0 := hs.mpr (hz z h 0)
    simp [z0,hr]
  · intro z h
    obtain ⟨nz,ngz,a,hs⟩ := ha z h
    refine ⟨nz,ngz,?_⟩
    rw [(val z a (fun b hb => (hs b hb).1)).1, (val (g*z) a (fun b hb => (hs b hb).2)).1]
    ring

/-- Four literal affine-word decoding polynomials on a multiplicative domain
obey the transition inequality. Z contains common agreements. The set A marks
consecutive coordinates admitting the same possible singleton error. Two
distinct, genuinely missed singleton colors ensure independent check rows. -/
theorem four_fits_motion [DecidableEq F] (g : F) (hg : g≠0) (d : ℕ)
    (hord : d<orderOf g) (γ : Fin 4 → F) (hγ : Function.Injective γ)
    (P : Fin 4 → F[X]) (hp : ∀ j, (P j).natDegree≤d) (u v : F → F)
    (Z A : Finset F)
    (hz : ∀ z∈Z, ∀ i, (P i).eval z=u z+γ i*v z)
    (ha : ∀ z∈A, z∉Z ∧ g*z∉Z ∧ ∃ i, ∀ j ≠ i,
      (P j).eval z=u z+γ j*v z ∧ (P j).eval (g*z)=u (g*z)+γ j*v (g*z))
    (x y : F) (i j : Fin 4) (hij : i≠j)
    (hx : ∀ a≠i, (P a).eval x = u x+γ a*v x)
    (hy : ∀ a≠j, (P a).eval y = u y+γ a*v y)
    (hxi : (P i).eval x≠u x+γ i*v x) (hyj : (P j).eval y≠u y+γ j*v y) :
    2*Z.card + A.card ≤ 2*d := by
  have bound := four_fits_motion_strict g hg d hord γ hγ P hp u v Z A hz ha x y i j hij hx hy hxi hyj
  have hc := card_le_card (subset_insert 0 A)
  omega

/-- In a cyclic coset of size 4h, four degree-<2h decoders cannot have
distinct genuine faults on two of four consecutive disjoint error blocks
of length h when the first coordinate is common to all decoders. -/
theorem four_arcs_forbidden [DecidableEq F] {h : ℕ} (hh : 2≤h) (g v₀ : F) (hg : g≠0)
    (hv : v₀≠0) (ho : orderOf g=4*h) (γ : Fin 4 → F) (hγ : Function.Injective γ)
    (P : Fin 4 → F[X]) (hp : ∀ a, (P a).natDegree<2*h) (u v : F → F)
    (node : ℕ → F) (hn : ∀ i, node i=v₀*g^i)
    (hb : ∀ i : Fin 4, (P i).eval (node 0)=u (node 0)+γ i*v (node 0))
    (hf : ∀ (a i : Fin 4), i≠a → ∀ z<h, (P i).eval (node (h*a.val+z))=
      u (node (h*a.val+z))+γ i*v (node (h*a.val+z)))
    (i j : Fin 4) (hij : i≠j) {x y : ℕ} (hx : x<h) (hy : y<h)
    (hxi : (P i).eval (node (h*i.val+x))≠u (node (h*i.val+x))+γ i*v (node (h*i.val+x)))
    (hyj : (P j).eval (node (h*j.val+y))≠u (node (h*j.val+y))+γ j*v (node (h*j.val+y))) :
    False := by
  classical
  have inj {s t : ℕ} (hs : s<4*h) (ht : t<4*h) (eq : node s=node t) : s=t := by
    rw [hn,hn] at eq
    exact pow_injOn_Iio_orderOf (ho ▸ hs) (ho ▸ ht) (mul_left_cancel₀ hv eq)
  have top (a : Fin 4) {z : ℕ} (hz : z<h) : h*a.val+z<4*h := by
    have hh' := Nat.mul_le_mul_left h (show a.val+1≤4 by omega)
    nlinarith
  let interior := fun p : Fin 4 × Fin (h-1) => node (h*p.1.val+p.2.val)
  let Z : Finset F := {node 0}
  let edges := univ.image interior
  let A := edges.erase (node 0)
  have baseeq {a b : Fin 4} {s t : ℕ} (hs : s<h) (ht : t<h)
      (he : h*a.val+s=h*b.val+t) : a=b ∧ s=t := by
    have hmod := congrArg (· % h) he
    simp only [Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt ht] at hmod
    have e := Nat.add_right_cancel (hmod ▸ he)
    exact ⟨Fin.ext (Nat.eq_of_mul_eq_mul_left (by omega : 0<h) e),hmod⟩
  have insideinj : Function.Injective interior := by
    intro a b he
    have ha := a.2.isLt
    have hb' := b.2.isLt
    have e := inj (top a.1 (z:=a.2.val) (by omega)) (top b.1 (z:=b.2.val) (by omega)) he
    obtain ⟨eq,ev⟩ := baseeq (by omega) (by omega) e
    exact Prod.ext eq (Fin.ext ev)
  have esize : edges.card=4*(h-1) := by simp [edges,card_image_of_injective _ insideinj]
  have first : node 0 ∈ edges := by
    apply mem_image.mpr
    exact ⟨(0,⟨0,by omega⟩),mem_univ _,by simp [interior]⟩
  have asize : A.card=edges.card-1 := card_erase_of_mem first
  have zsize : Z.card=1 := card_singleton _
  have hnz : (0:F) ∉ A := by
    intro hz
    obtain ⟨p,_,he⟩ := mem_image.mp (mem_of_mem_erase hz)
    exact mul_ne_zero hv (pow_ne_zero _ hg) ((hn _).symm.trans he)
  have bsize := card_insert_of_notMem hnz
  have bound := four_fits_motion_strict g hg (2*h-1) (by omega) γ hγ P (fun a => by have := hp a; omega)
    u v Z A (fun z hz => by
      have e := mem_singleton.mp hz
      exact e ▸ hb) (fun z hz => by
      obtain ⟨ne, ez⟩ := mem_erase.mp hz
      obtain ⟨⟨a,b⟩,_,rfl⟩ := mem_image.mp ez
      have hbl := b.isLt
      have step : g*interior (a,b)=node (h*a.val+(b.val+1)) := by
        dsimp [interior]
        rw [hn,hn,show h*a.val+(b.val+1)=(h*a.val+b.val)+1 by omega,pow_succ]
        ring
      rw [step]
      refine ⟨fun hin => ne (mem_singleton.mp hin), ?_, a, fun j hj =>
        ⟨hf a j hj _ (by omega),hf a j hj _ (by omega)⟩⟩
      intro hin
      have he := inj (top a (z:=b.val+1) (by omega)) (show 0<4*h by omega) (mem_singleton.mp hin)
      omega)
    (node (h*i.val+x)) (node (h*j.val+y)) i j hij
    (fun a ha => hf i a ha x hx) (fun a ha => hf j a ha y hy) hxi hyj
  omega

open scoped NNReal

/-- Under the four-block decoding pattern both received rows globally belong to
the code. Consequently no scalar witnesses the literal MCA event at any radius. -/
theorem not_mca_of_four_arcs [DecidableEq F] {h : ℕ} (hh : 2≤h) (g v₀ : F) (hg : g≠0)
    (hv : v₀≠0) (ho : orderOf g=4*h) (γ : Fin 4 → F) (hγ : Function.Injective γ)
    (P : Fin 4 → F[X]) (hp : ∀ a, (P a).natDegree<2*h) (u v : F → F)
    (D : (Fin 4 × Fin h) ↪ F) (hD : ∀ a : Fin 4, ∀ b : Fin h, D (a,b)=v₀*g^(h*a.val+b.val))
    (hb : ∀ i : Fin 4, (P i).eval v₀=u v₀+γ i*v v₀)
    (hf : ∀ (a i : Fin 4), i≠a → ∀ z : Fin h, (P i).eval (D (a,z))=
      u (D (a,z))+γ i*v (D (a,z)))
    (δ : ℝ≥0) (β : F) :
    ¬ mcaEvent (F := F) (ReedSolomon.code D (2*h) : Set ((Fin 4 × Fin h) → F))
      δ (u ∘ D) (v ∘ D) β := by
  classical
  let Bad := fun a : Fin 4 => ∃ z : Fin h, (P a).eval (D (a,z))≠u (D (a,z))+γ a*v (D (a,z))
  have excl {a b : Fin 4} (hab : a≠b) (ha : Bad a) (hb' : Bad b) : False := by
    obtain ⟨x,hx⟩ := ha
    obtain ⟨y,hy⟩ := hb'
    rw [hD] at hx hy
    exact four_arcs_forbidden hh g v₀ hg hv ho γ hγ P hp u v (fun z => v₀*g^z)
      (fun _ => rfl) (by simpa using hb) (fun a i h z hz => by simpa only [hD] using hf a i h ⟨z,hz⟩)
      a b hab x.isLt y.isLt hx hy
  have pair : ∃ a b : Fin 4, a≠b ∧ ¬Bad a ∧ ¬Bad b := by
    by_cases e : ∃ c, Bad c
    · obtain ⟨c,hc⟩ := e
      have gap : ∃ a b : Fin 4, a≠b ∧ c≠a ∧ c≠b := by fin_cases c <;> decide
      obtain ⟨a,b,hab,ha,hb'⟩ := gap
      exact ⟨a,b,hab,excl ha hc,excl hb' hc⟩
    · exact ⟨0,1,by decide,fun h => e ⟨_,h⟩,fun h => e ⟨_,h⟩⟩
  obtain ⟨a,b,hab,ha,hb'⟩ := pair
  let C₀ := ReedSolomon.code D (2*h)
  let W := fun i => (u ∘ D)+γ i • (v ∘ D)
  have fit (i : Fin 4) (hi : ¬Bad i) : W i ∈ C₀ := by
    apply ReedSolomon.mem_code_of_polynomial_of_natDegree_lt_of_eval (P i) (hp i)
    intro p
    obtain ⟨c,z⟩ := p
    change u (D (c,z))+γ i*v (D (c,z))=(P i).eval (D (c,z))
    by_cases he : i=c
    · subst c
      by_contra hn
      exact hi ⟨z,Ne.symm hn⟩
    · exact (hf c i he z).symm
  have vmem : v ∘ D ∈ C₀ := by
    have m := C₀.smul_mem (γ a-γ b)⁻¹ (C₀.sub_mem (fit a ha) (fit b hb'))
    have he : (γ a-γ b)⁻¹ • (W a-W b) = v ∘ D := by
      change _ • ((u ∘ D+γ a • (v ∘ D))-(u ∘ D+γ b • (v ∘ D))) = _
      rw [add_sub_add_left_eq_sub, ← sub_smul, smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr (hγ.ne hab)), one_smul]
    exact he ▸ m
  have umem : u ∘ D ∈ C₀ := by
    simpa [W] using C₀.sub_mem (fit a ha) (C₀.smul_mem (γ a) vmem)
  rintro ⟨S,_,_,h⟩
  exact h ⟨u ∘ D,umem,v ∘ D,vmem,fun _ _ => ⟨rfl,rfl⟩⟩

#print axioms four_fits_motion_strict
#print axioms turn_natDegree_lt
#print axioms not_mca_of_four_arcs
#print axioms four_arcs_forbidden
#print axioms four_fits_motion
#print axioms turn_ne_zero
#print axioms common_twice_add_edges_le
end ProximityGap.SyndromeMotion
