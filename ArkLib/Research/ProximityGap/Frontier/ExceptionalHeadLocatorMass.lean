/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.ManyHeadLocatorMass

/-! # One exceptional evaluation point per polynomial head

Degree-`k-1` heads share a block of `k` points except for one different point
per head. On every other fresh site, the first label component recovers the
site and the second recovers its head. This also holds in characteristic two.
-/

set_option autoImplicit false
open Finset Polynomial ProximityGap
open scoped NNReal ENNReal
namespace ArkLib.ProximityGap.Frontier.ExceptionalHeadLocatorMass
open ManyHeadLocatorMass
variable {F : Type} [Field F] [Fintype F] {n k d r : ℕ} [NeZero n]

omit [Fintype F] in
/-- The two fresh-label equations follow from the univariate interpolation
identity, including when the common locator vanishes at the exceptional site. -/
private theorem fresh_identity (x a c Q W : F) (h : (x-a)*Q=(x-c)*W) :
    (-x)*(Q-W)=c*W-a*Q ∧ (-((a+c)*x-a*c))*(Q-W)=c^2*W-a^2*Q := by
  constructor
  · linear_combination -h
  · linear_combination -(a+c)*h

/-- Any selected number of fresh keys up to the full exceptional-site count
gives the averaged one-pair MCA lower bound, on arbitrary finite fields. -/
theorem mass_of_count (dom : Fin n ↪ F) (δ : ℝ≥0) (hr : 0 < r) (hk : d+1 ≤ k)
    (hn : k+(d+1)*r≤n) (hδ : (1-δ)*(n : ℝ≥0) ≤ ((k+r : ℕ):ℝ≥0))
    {L : ℕ} (hL : L ≤ (d+1)*(n-(k-1+r))) :
    ((AveragedPencilProjection.retained L (Fintype.card F) : ℕ):ℝ≥0∞)/(Fintype.card F : ℝ≥0∞)
      ≤ epsMCA (F:=F) (ReedSolomon.code dom k : Set (Fin n → F)) δ := by
  classical
  let base := univ.map (initialPositions hn)
  let pt : Fin (d+1) ↪ Fin n := (Fin.castLEEmb hk).trans (initialPositions hn)
  let a := pt.trans dom
  let pr (j : Fin (d+1)) := univ.map (slot hn j)
  have pt_in (j : Fin (d+1)) : pt j∈base := mem_map.mpr ⟨_,mem_univ _,rfl⟩
  have dis (j : Fin (d+1)) : Disjoint base (pr j) := private_disjoint hn j
  let G := Lagrange.nodal base dom
  let Q (j : Fin (d+1)) := Lagrange.nodal (base.erase (pt j)) dom
  let core (j : Fin (d+1)) := base.erase (pt j) ∪ pr j
  have hcard (j : Fin (d+1)) : (core j).card=k-1+r := by
    rw [show (core j).card = (base.erase (pt j)).card+(pr j).card from
      card_union_of_disjoint ((dis j).mono_left (erase_subset ..)),card_erase_of_mem (pt_in j)]
    simp [base,pr]
  let T := (j : Fin (d+1)) × ↥(univ \ core j)
  have ht : Fintype.card T=(d+1)*(n-(k-1+r)) := by simp [T,Fintype.card_sigma,hcard]
  let E : Fin L ↪ T := (Fin.castLEEmb (hL.trans_eq ht.symm)).trans (Fintype.equivFin T).symm.toEmbedding
  let head (i : Fin L) := (E i).1
  let site (i : Fin L) := (E i).2.1
  have outside (i : Fin L) : site i∉core (head i) := (mem_sdiff.mp (E i).2.2).2
  let anyPrivate := univ.biUnion pr
  let dummy := slot hn 0 (⟨0,hr⟩ : Fin r)
  have dh : dummy∈pr 0 := mem_map.mpr ⟨_,mem_univ _,rfl⟩
  have da : dummy∈anyPrivate := mem_biUnion.mpr ⟨_,mem_univ _,dh⟩
  have dx : dummy∉base := fun h => disjoint_left.mp (dis 0) h dh
  let c (x : Fin n) := if x∈anyPrivate then a (species d k x) else dom dummy
  have c_ne_x (x : Fin n) : dom x ≠ c x := by
    by_cases hx : x∈anyPrivate
    · obtain ⟨j,_,hxj⟩ := mem_biUnion.mp hx
      obtain ⟨y,_,rfl⟩ := mem_map.mp hxj
      simp only [c,hx,ite_true,species_slot]
      exact fun he => disjoint_left.mp (dis j) ((dom.injective he).symm ▸ pt_in j)
        (mem_map.mpr ⟨y,mem_univ _,rfl⟩)
    · have hnd : x≠dummy := fun he => hx (he.symm ▸ da)
      simpa [c,hx] using dom.injective.ne hnd
  have c_spec (j : Fin (d+1)) (x : Fin n) : c x=a j ↔ x∈pr j := by
    by_cases hx : x∈anyPrivate
    · obtain ⟨l,_,hl⟩ := mem_biUnion.mp hx
      obtain ⟨y,_,rfl⟩ := mem_map.mp hl
      simp only [c,hx,ite_true,species_slot]
      constructor
      · intro he
        rw [← a.injective he]
        exact mem_map.mpr ⟨y,mem_univ _,rfl⟩
      · intro hm
        obtain ⟨y',_,he⟩ := mem_map.mp hm
        have hj : j=l := by simpa only [species_slot] using congrArg (species d k) he
        rw [hj]
    · have non : x∉pr j := fun h => hx (mem_biUnion.mpr ⟨j,mem_univ _,h⟩)
      have he : dom dummy ≠ a j := fun h => dx ((dom.injective h).symm ▸ pt_in j)
      simp [c,hx,he,non]
  let W (x : Fin n) := G.eval (dom x)/(dom x-c x)
  have eqn (j : Fin (d+1)) (x : Fin n) :
      (dom x-a j)*(Q j).eval (dom x)=(dom x-c x)*W x := by
    have hg : G=(X-C (a j))*Q j := Lagrange.nodal_eq_mul_nodal_erase (pt_in j)
    have h := congrArg (fun f : F[X] => f.eval (dom x)) hg
    simp only [eval_mul,eval_sub,eval_X,eval_C] at h
    rw [← h, mul_comm, div_mul_cancel₀ _ (sub_ne_zero.mpr (c_ne_x x))]
  have qdeg (j : Fin (d+1)) : (Q j).degree < (k : WithBot ℕ) := by
    apply degree_le_natDegree.trans_lt
    rw [show (Q j).natDegree=k-1 by simp [Q,base,Lagrange.natDegree_nodal,card_erase_of_mem (pt_in j)]]
    exact_mod_cast (by omega : k-1<k)
  have cdeg (z : F) (j : Fin (d+1)) : (C z*Q j).degree < (k : WithBot ℕ) := by
    by_cases h : z=0
    · simp [h]
    · simpa [degree_C_mul h] using qdeg j
  let key (i : Fin L) : Fin 2 → F := ![-dom (site i),-((a (head i)+c (site i))*dom (site i)-a (head i)*c (site i))]
  have hinj : Function.Injective key := by
    intro i j he
    have hx : site i=site j := dom.injective (by simpa [key] using congrFun he 0)
    have he1 := congrFun he 1
    simp only [key,Matrix.cons_val_one,Matrix.cons_val_fin_one,neg_inj,hx] at he1
    have heq : head i=head j := a.injective (sub_eq_zero.mp ((mul_eq_zero.mp
      (show (a (head i)-a (head j))*(dom (site j)-c (site j))=0 by linear_combination he1)).resolve_right
      (sub_ne_zero.mpr (c_ne_x _))))
    apply E.injective
    apply Sigma.ext heq
    apply (Subtype.heq_iff_coe_eq (fun x => ?_)).mpr hx
    change x∈univ \ core (head i) ↔ x∈univ \ core (head j)
    rw [heq]
  have mass := AveragedPencilProjection.mass_averaged dom k δ (fun i => core (head i)) site
    (fun i => C (a (head i))*Q (head i)) (fun i => C ((a (head i))^2)*Q (head i)) (fun i => Q (head i))
    (fun x => c x*W x) (fun x => c x^2*W x) W key (fun _ => cdeg ..) (fun _ => cdeg ..) (fun _ => qdeg _)
    (by
      intro i x hx
      rcases mem_union.mp hx with h | h
      · have qz : (Q (head i)).eval (dom x)=0 := Lagrange.eval_nodal_at_node h
        have gz : G.eval (dom x)=0 := Lagrange.eval_nodal_at_node (mem_of_mem_erase h)
        simp [eval_mul,qz,W,gz]
      · have ca := (c_spec _ _).mpr h
        have eq := eqn (head i) x
        rw [← ca] at eq
        have qw := mul_left_cancel₀ (sub_ne_zero.mpr (c_ne_x _)) eq
        simp [eval_mul,qw,ca])
    (fun i => by rw [hcard]; omega)
    (fun i => by simpa only [hcard,Fintype.card_fin,show k-1+r+1=k+r by omega] using hδ)
    (by
      intro i he
      have qa : (Q (head i)).eval (dom (site i)) ≠ 0 := by
        apply Lagrange.eval_nodal_not_at_node
        intro x hx eq
        exact outside i (mem_union_left _ ((dom.injective eq).symm ▸ hx))
      have ca : c (site i)≠a (head i) := fun eq => outside i (mem_union_right _ ((c_spec _ _).mp eq))
      have eq := eqn (head i) (site i)
      rw [← he] at eq
      exact ca (by simpa using (mul_right_cancel₀ qa eq).symm))
    (by
      intro i
      simpa [key,eval_mul] using fresh_identity _ _ _ _ _ (eqn (head i) (site i)))
    hinj
  simpa only [Fintype.card_fin] using mass

/-- At agreement `t`, every head contributes `n-t+1` raw keys when
`m*(t-k)≤n-k`, including the sites omitted by the other heads. -/
theorem grid_mass (dom : Fin n ↪ F) (δ : ℝ≥0) {m t : ℕ}
    (hm : 0 < m) (hk : m ≤ k) (ht : k < t) (htn : t ≤ n)
    (hlayout : m*(t-k) ≤ n-k) (hδ : (1-δ)*(n : ℝ≥0) ≤ t) :
    ((AveragedPencilProjection.retained (m*(n-t+1)) (Fintype.card F) : ℕ):ℝ≥0∞)/(Fintype.card F : ℝ≥0∞)
      ≤ epsMCA (F:=F) (ReedSolomon.code dom k : Set (Fin n → F)) δ := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  change (d+1)*(t-k)≤n-k at hlayout
  apply mass_of_count (d:=d) (r:=t-k) dom δ (by omega) hk (by omega)
    (by simpa only [show k+(t-k)=t by omega] using hδ)
  rw [show n-(k-1+(t-k))=n-t+1 by omega]

/-- The complete two-parameter pencil exceeds the security budget throughout
the 128-bit field range as soon as the raw count is over budget. -/
theorem over_budget_128 (dom : Fin n ↪ F) (δ : ℝ≥0) {m t : ℕ}
    (hm : 0 < m) (hk : m ≤ k) (ht : k < t) (htn : t ≤ n)
    (hlayout : m*(t-k) ≤ n-k) (hδ : (1-δ)*(n : ℝ≥0) ≤ t)
    (hrange : Fintype.card F ≤ 2^256) (hbudget : Fintype.card F/2^128 < m*(n-t+1)) :
    1/(2:ℝ≥0∞)^128 < epsMCA (F:=F) (ReedSolomon.code dom k : Set (Fin n → F)) δ := by
  have hmass := grid_mass dom δ hm hk ht htn hlayout hδ
  have hb := AveragedPencilProjection.tolerance_budget_lt_retained (by decide : 0 < 2^128)
    (show Fintype.card F ≤ (2^128)^2 by convert hrange using 1) hbudget
  by_contra! safe
  apply hb.not_ge
  apply (BoundarySecurityBudget.count_ratio_le_iff Fintype.card_pos (by decide : 0 < 2^128)).mp
  exact hmass.trans (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using safe)

#print axioms mass_of_count
#print axioms grid_mass
#print axioms over_budget_128
end ArkLib.ProximityGap.Frontier.ExceptionalHeadLocatorMass
