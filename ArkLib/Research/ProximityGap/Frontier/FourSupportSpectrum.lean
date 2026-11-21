/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SyndromeMotion

/-! # The possible scalar ratios of four fixed error supports -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace ProximityGap.FourSupportSpectrum
open Finset Polynomial
variable {F I : Type} [Field F] [DecidableEq F] [Fintype I]

private theorem vanish (p : F[X]) (k : ℕ) (hp : p.natDegree < k) (U : Finset F)
    (hs : k ≤ U.card) (hz : ∀ x∈U, p.eval x=0) : p=0 := by
  by_contra hn
  have sub : U ⊆ p.roots.toFinset := fun x hx => Multiset.mem_toFinset.mpr ((mem_roots hn).mpr (hz x hx))
  have := (card_le_card sub).trans ((Multiset.toFinset_card_le _).trans (card_roots' p))
  omega

private noncomputable def comb (a : I → F) (P : I → F[X]) : F[X] := ∑ i, C (a i)*P i

private theorem comb_degree {k : ℕ} (kh : 0<k) (a : I → F) (P : I → F[X])
    (hd : ∀ i, (P i).natDegree<k) : (comb a P).natDegree<k := by
  have le : (comb a P).natDegree≤k-1 := by
    refine (natDegree_sum_le ..).trans ?_
    simp only [Finset.fold_max_le]
    exact ⟨Nat.zero_le _, fun i _ => (natDegree_C_mul_le ..).trans (by have := hd i; omega)⟩
  omega

private theorem comb_eval (a : I → F) (P : I → F[X]) (x : F) :
    (comb a P).eval x = ∑ i, a i*(P i).eval x := by simp [comb,eval_finsetSum]

/-- Weighted relations on vectors preserved by distinct scalar eigenvalues
force the vectors to be independent, even if no ambient operator is given. -/
private theorem indep {V : Type} [AddCommGroup V] [Module F V]
    (v : I → V) (hv : ∀ i, v i≠0) (z : I → F) (hinj : Function.Injective z)
    (carry : ∀ c : I → F, ∑ i, c i • v i=0 → ∑ i, (c i*z i) • v i=0) :
    LinearIndependent F v := by
  classical
  refine Fintype.linearIndependent_iff.mpr fun c rel j => ?_
  have cut (S : Finset I) : ∑ i, (c i*∏ b∈S, (z i-z b)) • v i=0 := by
    induction S using Finset.induction_on with
    | empty => simpa using rel
    | @insert b S hb ih =>
      have next := carry (fun i => c i*∏ a∈S, (z i-z a)) ih
      have remove := congrArg (fun w : V => z b • w) ih
      rw [smul_zero,smul_sum] at remove
      calc
        _ = ∑ i, (((c i*∏ a∈S, (z i-z a))*z i) • v i - z b • ((c i*∏ a∈S, (z i-z a)) • v i)) := by
          apply sum_congr rfl
          intro i _
          rw [prod_insert hb,smul_smul,← sub_smul]
          congr 1
          ring
        _ = 0 := by rw [sum_sub_distrib,next,remove,sub_zero]
  have one := cut (univ.erase j)
  rw [sum_eq_single j] at one
  · have hz := (smul_eq_zero.mp one).resolve_right (hv j)
    exact (mul_eq_zero.mp hz).resolve_right (prod_ne_zero_iff.mpr fun b hb => sub_ne_zero.mpr (hinj.ne (ne_of_mem_erase hb).symm))
  · intro b _ hbj
    have hb : b ∈ univ.erase j := by simp [hbj]
    have eq : (∏ a∈univ.erase j, (z b-z a))=0 := prod_eq_zero hb (by simp)
    simp [eq]
  · simp

/-- On four prescribed coordinate sets the fourth normalized scalar can have
at most `D.card` different values, even allowing each value its own pair of
polynomials. The two unions are the only coverage hypotheses. -/
theorem spectrum_le (k : ℕ) (kh : 0<k) (A B C₀ D : Finset F)
    (hac : k≤(A∪C₀).card) (hbd : k≤(B∪D).card) (z : I → F) (hinj : Function.Injective z)
    (P Q : I → F[X]) (hp : ∀ i, (P i).natDegree<k) (hq : ∀ i, (Q i).natDegree<k)
    (hn : ∀ i, Q i≠0) (ha : ∀ i, ∀ x∈A, (P i).eval x=0)
    (hb : ∀ i, ∀ x∈B, (Q i).eval x=0) (hc : ∀ i, ∀ x∈C₀, (P i).eval x=(Q i).eval x)
    (hd : ∀ i, ∀ x∈D, (P i).eval x=z i*(Q i).eval x) : Fintype.card I ≤ D.card := by
  classical
  let v := fun (i : I) (x : D) => (Q i).eval x.1
  have vne (i : I) : v i≠0 := by
    intro nz
    apply hn i (vanish _ k (hq i) (B∪D) hbd ?_)
    intro x hx
    obtain h|h := mem_union.mp hx
    · exact hb i x h
    · exact congrFun nz ⟨x,h⟩
  have li := indep v vne z hinj (fun c rel => by
    have q0 : comb c Q=0 := by
      apply vanish _ k (comb_degree kh c Q hq) (B∪D) hbd
      intro x hx
      rw [comb_eval]
      obtain h|h := mem_union.mp hx
      · simp [hb _ _ h]
      · simpa [v, Finset.sum_apply] using congrFun rel ⟨x,h⟩
    have p0 : comb c P=0 := by
      apply vanish _ k (comb_degree kh c P hp) (A∪C₀) hac
      intro x hx
      rw [comb_eval]
      obtain h|h := mem_union.mp hx
      · simp [ha _ _ h]
      · simpa [comb_eval, hc _ _ h] using congrArg (fun p : F[X] => p.eval x) q0
    funext x
    have final := congrArg (fun p : F[X] => p.eval x.1) p0
    simpa [comb_eval,hd _ _ x.2,v,Finset.sum_apply,mul_assoc] using final)
  simpa using li.fintype_card_le_finrank

private theorem fiber_factors (h : ℕ) (hh : 0<h) (H : F[X]) (hm : H.Monic) (hd : H.natDegree=h)
    (U : Fin 4 → Finset F) (α : Fin 4 → F)
    (hc : ∀ i, (U i).card=h) (hf : ∀ i, ∀ x∈U i, H.eval x=α i)
    (P Q : F[X]) (hp : P.natDegree<2*h) (hq : Q.natDegree<2*h) (hn : Q≠0)
    (h0 : ∀ x∈U 0, P.eval x=0) (h1 : ∀ x∈U 1, Q.eval x=0)
    (h2 : ∀ x∈U 2, P.eval x=Q.eval x) :
    ∃ p q : F[X], P=(H-C (α 0))*p ∧ Q=(H-C (α 1))*q ∧ q≠0 ∧ q.natDegree<h ∧
      C (α 2-α 0)*p=C (α 2-α 1)*q ∧ ∀ i : Fin 4, ∀ l : F,
      (∀ x∈U i, P.eval x=l*Q.eval x) → C (α i-α 0)*p=C (l*(α i-α 1))*q := by
  classical
  have nodal (i : Fin 4) : H-C (α i)=Lagrange.nodal (U i) id := by
    have lt : (C (α i)).degree<H.degree := degree_lt_degree (by simpa [hd] using hh)
    apply eq_of_monic_of_dvd_of_natDegree_le Lagrange.nodal_monic (hm.sub_of_left lt)
    · apply zeroOn_iff_nodal_dvd.mp
      intro x hx
      simp [hf _ _ hx]
    · simp [Lagrange.natDegree_nodal,hd,hc]
  obtain ⟨p,pdef⟩ := zeroOn_iff_nodal_dvd.mp h0
  obtain ⟨q,qdef⟩ := zeroOn_iff_nodal_dvd.mp h1
  rw [← nodal 0] at pdef
  rw [← nodal 1] at qdef
  have nq : q ≠ 0 := by rintro rfl; simp_all
  have small {R S : F[X]} {i : Fin 4} (eq : R=(H-C (α i))*S) (hr : R.natDegree<2*h) : S.natDegree<h := by
    by_cases hs : S=0
    · simpa [hs] using hh
    have nn : H-C (α i) ≠ 0 := by rw [nodal]; exact Lagrange.nodal_ne_zero
    rw [eq,natDegree_mul nn hs,natDegree_sub_C,hd] at hr
    omega
  have sp := small pdef hp
  have sq := small qdef hq
  have identity (i : Fin 4) (l : F) (hl : ∀ x∈U i, P.eval x=l*Q.eval x) :
      C (α i-α 0)*p=C (l*(α i-α 1))*q := by
    apply sub_eq_zero.mp
    apply vanish _ h (lt_of_le_of_lt (natDegree_sub_le ..) (max_lt
      (lt_of_le_of_lt (natDegree_C_mul_le ..) sp) (lt_of_le_of_lt (natDegree_C_mul_le ..) sq))) (U i) (hc i).ge
    intro x hx
    have e := hl x hx
    rw [pdef,qdef] at e
    simp only [eval_mul,eval_C,eval_sub,hf i x hx] at e ⊢
    linear_combination e
  have p2 := identity 2 1 (by simpa using h2)
  simp only [one_mul] at p2
  exact ⟨p,q,pdef,qdef,nq,sq,p2,identity⟩

/-- On four complete fibers of one monic degree-`h` polynomial, the normalized
fourth scalar is determined by the four fiber values. In particular the
fourth scalar admits at most one value on four multiplicative `h`-cosets. -/
theorem fiber_ratio (h : ℕ) (hh : 0<h) (H : F[X]) (hm : H.Monic) (hd : H.natDegree=h)
    (U : Fin 4 → Finset F) (α : Fin 4 → F)
    (hc : ∀ i, (U i).card=h) (hf : ∀ i, ∀ x∈U i, H.eval x=α i)
    (P Q : F[X]) (hp : P.natDegree<2*h) (hq : Q.natDegree<2*h) (hn : Q≠0) (z : F)
    (h0 : ∀ x∈U 0, P.eval x=0) (h1 : ∀ x∈U 1, Q.eval x=0)
    (h2 : ∀ x∈U 2, P.eval x=Q.eval x) (h3 : ∀ x∈U 3, P.eval x=z*Q.eval x) :
    z*((α 2-α 0)*(α 3-α 1))=(α 2-α 1)*(α 3-α 0) := by
  obtain ⟨p,q,_,_,nq,_,p2,identity⟩ := fiber_factors h hh H hm hd U α hc hf P Q hp hq hn h0 h1 h2
  have p3 := identity 3 z h3
  have eq : C (z*((α 2-α 0)*(α 3-α 1))-(α 2-α 1)*(α 3-α 0))*q=0 := by
    simp only [map_sub,map_mul] at p2 p3 ⊢
    linear_combination (C (α 3)-C (α 0))*p2 - (C (α 2)-C (α 0))*p3
  exact sub_eq_zero.mp (C_eq_zero.mp ((mul_eq_zero.mp eq).resolve_right nq))

/-- A nonzero parity check on four full fibers leaves at most `h−1`
common zero sites, even when they are spread among different fibers. -/
theorem fiber_common_lt (h : ℕ) (hh : 0<h) (H : F[X]) (hm : H.Monic) (hd : H.natDegree=h)
    (U : Fin 4 → Finset F) (α : Fin 4 → F) (hi : Function.Injective α)
    (hc : ∀ i, (U i).card=h) (hf : ∀ i, ∀ x∈U i, H.eval x=α i)
    (P Q : F[X]) (hp : P.natDegree<2*h) (hq : Q.natDegree<2*h) (hn : Q≠0)
    (h0 : ∀ x∈U 0, P.eval x=0) (h1 : ∀ x∈U 1, Q.eval x=0)
    (h2 : ∀ x∈U 2, P.eval x=Q.eval x) (Z : Finset F) (hz : ∀ x∈Z, P.eval x=0 ∧ Q.eval x=0) :
    Z.card<h := by
  obtain ⟨p,q,pdef,qdef,qn,qd,p2,_⟩ := fiber_factors h hh H hm hd U α hc hf P Q hp hq hn h0 h1 h2
  by_contra! le
  apply qn (vanish q h qd Z le ?_)
  intro x hx
  obtain ⟨px,qx⟩ := hz x hx
  rw [pdef,eval_mul,eval_sub,eval_C] at px
  rw [qdef,eval_mul,eval_sub,eval_C] at qx
  by_cases eq : H.eval x=α 1
  · rw [eq] at px
    have zz := (mul_eq_zero.mp px).resolve_left (sub_ne_zero.mpr (hi.ne (by decide : (1 : Fin 4)≠0)))
    have pa := congrArg (fun f : F[X] => f.eval x) p2
    simp only [eval_mul,eval_C,zz,mul_zero] at pa
    exact (mul_eq_zero.mp pa.symm).resolve_left (sub_ne_zero.mpr (hi.ne (by decide : (2 : Fin 4)≠1)))
  · exact (mul_eq_zero.mp qx).resolve_left (sub_ne_zero.mpr eq)

/-- The projective coordinate sending labels `0,1,2` to `0,∞,1`. -/
def ratio (γ : Fin 4 → F) : F :=
  ((γ 2-γ 1)*(γ 3-γ 0))/((γ 2-γ 0)*(γ 3-γ 1))

private theorem normalized (k : ℕ) (kh : 0<k) (U : Fin 4 → Finset F)
    (γ : Fin 4 → F) (hg : Function.Injective γ) (f : Fin 4 → F[X])
    (hd : ∀ j, (f j).natDegree<k) (u v : F → F)
    (fit : ∀ i, ∀ x∈U i, ∀ j≠i, (f j).eval x=u x+γ j*v x)
    (miss : ∃ i≠(1 : Fin 4), ∃ x∈U i, (f i).eval x≠u x+γ i*v x) :
    ∃ P Q : F[X], P.natDegree<k ∧ Q.natDegree<k ∧ Q≠0 ∧
      (∀ x∈U 0, P.eval x=0) ∧ (∀ x∈U 1, Q.eval x=0) ∧
      (∀ x∈U 2, P.eval x=Q.eval x) ∧ (∀ x∈U 3, P.eval x=ratio γ*Q.eval x) := by
  obtain ⟨s,r,sd,rd,val⟩ := SyndromeMotion.four_check_rows γ hg f (k-1) (fun j => by have := hd j; omega) u v
  let check := fun b c => C c*(r-C b*s)
  have degree (b c : F) : (check b c).natDegree<k := by
    refine lt_of_le_of_lt (natDegree_C_mul_le ..) ((natDegree_sub_le ..).trans_lt ?_)
    exact max_lt (by omega) ((natDegree_C_mul_le ..).trans_lt (by omega))
  have atSite (i : Fin 4) (x : F) (hx : x∈U i) (b c : F) :
      (check b c).eval x=c*(γ i-b)*s.eval x := by
    simp [check,(val x i (fit i x hx)).1]
    ring
  refine ⟨check (γ 0) (γ 2-γ 1),check (γ 1) (γ 2-γ 0),degree ..,degree ..,?_,?_,?_,?_,?_⟩
  · obtain ⟨i,hi,x,hx,miss⟩ := miss
    intro he
    have zero := congrArg (fun p : F[X] => p.eval x) he
    simp only [atSite i x hx,eval_zero] at zero
    have s0 := mt (val x i (fit i x hx)).2.mp miss
    exact (mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr (hg.ne (by decide : (2 : Fin 4)≠0)))
      (sub_ne_zero.mpr (hg.ne hi))) s0) zero
  · intro x hx; simp [atSite 0 x hx]
  · intro x hx; simp [atSite 1 x hx]
  · intro x hx; rw [atSite 2 x hx,atSite 2 x hx]; ring
  · intro x hx
    rw [atSite 3 x hx,atSite 3 x hx]
    dsimp [ratio]
    field_simp [sub_ne_zero.mpr (hg.ne (by decide : (2 : Fin 4)≠0)),
      sub_ne_zero.mpr (hg.ne (by decide : (3 : Fin 4)≠1))]

/-- The triple of reference labels is fixed. Every distinct fourth label gives a
distinct normalized ratio, over any field. -/
theorem ratio_injective (a b c : F) (w : I → F) (hw : Function.Injective w)
    (hab : a≠b) (hca : c≠a) (hcb : c≠b) (hwb : ∀ i, w i≠b) :
    Function.Injective fun i => ratio ![a,b,c,w i] := by
  intro i j he
  apply hw
  simp [ratio] at he
  field_simp [sub_ne_zero.mpr hca,sub_ne_zero.mpr (hwb _)] at he
  have hn := sub_ne_zero.mpr hab
  apply mul_left_cancel₀ hn
  linear_combination he

/-- Bounds the number of raw fourth scalar labels for an arbitrary family of
four decoding polynomials with these prescribed support regions. Each label
may have its own received words and its own four polynomials. -/
theorem four_fits_spectrum (k : ℕ) (kh : 0<k) (U : Fin 4 → Finset F)
    (hac : k≤(U 0∪U 2).card) (hbd : k≤(U 1∪U 3).card)
    (a b c : F) (w : I → F) (hw : Function.Injective w)
    (hg : ∀ i, Function.Injective (![a,b,c,w i] : Fin 4 → F))
    (f : I → Fin 4 → F[X]) (hd : ∀ i j, (f i j).natDegree<k) (u v : I → F → F)
    (fit : ∀ i m, ∀ x∈U m, ∀ j≠m, (f i j).eval x=u i x+![a,b,c,w i] j*v i x)
    (miss : ∀ i, ∃ m≠(1 : Fin 4), ∃ x∈U m, (f i m).eval x≠u i x+![a,b,c,w i] m*v i x) :
    Fintype.card I≤(U 3).card := by
  classical
  cases isEmpty_or_nonempty I with
  | inl => simp
  | inr inst =>
    let i₀ := Classical.choice inst
    have gd := hg i₀
    have hinj := ratio_injective a b c w hw (by simpa using gd.ne (by decide : (0 : Fin 4)≠1))
      (by simpa using gd.ne (by decide : (2 : Fin 4)≠0)) (by simpa using gd.ne (by decide : (2 : Fin 4)≠1))
      (fun i => by simpa using (hg i).ne (by decide : (3 : Fin 4)≠1))
    choose P Q hp hq hn h0 h1 h2 h3 using fun i => normalized k kh U _ (hg i) (f i) (hd i) (u i) (v i) (fit i) (miss i)
    exact spectrum_le k kh _ _ _ _ hac hbd _ hinj P Q hp hq hn h0 h1 h2 h3

/-- For genuine four-way decodings on four full polynomial fibers, the four
field labels have the same cross-ratio as the four corresponding fiber values. -/
theorem four_fits_fiber_ratio (h : ℕ) (hh : 0<h) (H : F[X]) (hm : H.Monic) (hd : H.natDegree=h)
    (U : Fin 4 → Finset F) (α : Fin 4 → F) (ha : Function.Injective α)
    (hc : ∀ i, (U i).card=h) (hf : ∀ i, ∀ x∈U i, H.eval x=α i)
    (γ : Fin 4 → F) (hg : Function.Injective γ) (f : Fin 4 → F[X]) (deg : ∀ j, (f j).natDegree<2*h)
    (u v : F → F) (fit : ∀ i, ∀ x∈U i, ∀ j≠i, (f j).eval x=u x+γ j*v x)
    (miss : ∃ i≠(1 : Fin 4), ∃ x∈U i, (f i).eval x≠u x+γ i*v x) : ratio γ=ratio α := by
  obtain ⟨P,Q,hp,hq,hn,h0,h1,h2,h3⟩ := normalized (2*h) (by omega) U γ hg f deg u v fit miss
  apply (eq_div_iff (mul_ne_zero (sub_ne_zero.mpr (ha.ne (by decide : (2 : Fin 4)≠0)))
    (sub_ne_zero.mpr (ha.ne (by decide : (3 : Fin 4)≠1))))).mpr
  exact fiber_ratio h hh H hm hd U α hc hf P Q hp hq hn _ h0 h1 h2 h3

/-- Under a genuine four-decoder pattern with each missed set in its own
fiber, fewer than `h` coordinates can be common agreements. -/
theorem four_fits_common_lt (h : ℕ) (hh : 0<h) (H : F[X]) (hm : H.Monic) (hd : H.natDegree=h)
    (U : Fin 4 → Finset F) (α : Fin 4 → F) (ha : Function.Injective α)
    (hc : ∀ i, (U i).card=h) (hf : ∀ i, ∀ x∈U i, H.eval x=α i)
    (γ : Fin 4 → F) (hg : Function.Injective γ) (f : Fin 4 → F[X]) (deg : ∀ j, (f j).natDegree<2*h)
    (u v : F → F) (fit : ∀ i, ∀ x∈U i, ∀ j≠i, (f j).eval x=u x+γ j*v x)
    (miss : ∃ i≠(1 : Fin 4), ∃ x∈U i, (f i).eval x≠u x+γ i*v x)
    (Z : Finset F) (hz : ∀ x∈Z, ∀ i, (f i).eval x=u x+γ i*v x) : Z.card<h := by
  let U' := fun i => U i ∪ Z
  obtain ⟨m,nm,x,xm,hm'⟩ := miss
  have mm : ∃ i≠(1 : Fin 4), ∃ x∈U' i, (f i).eval x≠u x+γ i*v x :=
    ⟨m,nm,x,mem_union_left _ xm,hm'⟩
  obtain ⟨P,Q,hp,hq,hn,h0,h1,h2,_⟩ := normalized (2*h) (by omega) U' γ hg f deg u v (by
    intro i y hy j hj
    obtain h|h := mem_union.mp hy
    · exact fit i y h j hj
    · exact hz y h j) mm
  exact fiber_common_lt h hh H hm hd U α ha hc hf P Q hp hq hn
    (fun y hy => h0 y (mem_union_left _ hy)) (fun y hy => h1 y (mem_union_left _ hy))
    (fun y hy => h2 y (mem_union_left _ hy)) Z fun y hy =>
      ⟨h0 y (mem_union_right _ hy),h1 y (mem_union_right _ hy)⟩

#print axioms four_fits_common_lt
#print axioms four_fits_fiber_ratio
#print axioms four_fits_spectrum
#print axioms ratio_injective

#print axioms fiber_ratio

#print axioms spectrum_le
end ProximityGap.FourSupportSpectrum
