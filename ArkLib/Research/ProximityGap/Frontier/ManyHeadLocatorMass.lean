/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.AveragedPencilProjection
import ArkLib.Research.ProximityGap.Frontier.BoundarySecurityBudget
import Mathlib.LinearAlgebra.Lagrange

/-! # Private cores sharing a polynomial locator

The sites outside each head’s core give distinct two-component keys.
Projecting them gives an explicit lower bound for one pair of received words
on any injective finite-field domain.
-/

open Polynomial Finset ProximityGap
open scoped NNReal ENNReal

namespace ArkLib.ProximityGap.Frontier.ManyHeadLocatorMass

variable {n h r k p d : ℕ} [Fact p.Prime]

/-- The first sites reserved for the common locator. -/
def initialPositions (hn : h + (d + 1) * r ≤ n) : Fin h ↪ Fin n where
  toFun x := ⟨x.val, by omega⟩
  inj' _ _ hxy := Fin.ext (congrArg (fun z : Fin n => z.val) hxy)

/-- The private sites of one head, interleaved after the common sites. -/
def slot (hn : h + (d + 1) * r ≤ n) (j : Fin (d + 1)) : Fin r ↪ Fin n where
  toFun x := ⟨h + ((d + 1) * x.val + j.val), by
    have hstep : (d + 1) * x.val + j.val < (d + 1) * (x.val + 1) := by
      simpa only [Nat.mul_add, Nat.mul_one] using Nat.add_lt_add_left j.isLt ((d + 1) * x.val)
    have hr : (d + 1) * (x.val + 1) ≤ (d + 1) * r := Nat.mul_le_mul_left _ x.isLt
    exact (Nat.add_lt_add_left (lt_of_lt_of_le hstep hr) h).trans_le hn⟩
  inj' x y hxy := by
    have hval := congrArg Fin.val hxy
    change h + ((d + 1) * x.val + j.val) = h + ((d + 1) * y.val + j.val) at hval
    have hm := Nat.add_right_cancel (Nat.add_left_cancel hval)
    exact Fin.ext (Nat.eq_of_mul_eq_mul_left (Nat.succ_pos d) hm)

/-- The head owning a private site. -/
def species (d h : ℕ) (x : Fin n) : Fin (d + 1) :=
  ⟨(x.val - h) % (d + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩

/-- The owner map recovers the head of each private slot. -/
lemma species_slot (hn : h + (d + 1) * r ≤ n) (j : Fin (d + 1)) (x : Fin r) :
    species d h (slot hn j x) = j := by
  apply Fin.ext
  change (h + ((d + 1) * x.val + j.val) - h) % (d + 1) = j.val
  simp [Nat.add_mod, Nat.mod_eq_of_lt j.isLt]

/-- The common sites are disjoint from the slots of any one head. -/
lemma private_disjoint (hn : h + (d + 1) * r ≤ n) (j : Fin (d + 1)) :
    Disjoint (univ.map (initialPositions hn)) (univ.map (slot hn j)) := by
  apply disjoint_left.mpr
  intro x hx hy
  obtain ⟨a, _, rfl⟩ := mem_map.mp hx
  obtain ⟨b, _, he⟩ := mem_map.mp hy
  have he' := congrArg Fin.val he
  change h + ((d + 1) * b.val + j.val) = a.val at he'
  omega

open Classical in
/-- A common locator realizes any bound on the image of its projected keys.
The first coordinate avoids its roots, and the second is a signed sum of
two prescribed head coefficients. -/
theorem mass_of_projectable {F : Type} [Field F] [Fintype F] [NeZero n] (dom : Fin n ↪ F) (δ : ℝ≥0)
    (hn : h + (d + 1) * r ≤ n) (hdegree : h + 2 ≤ k) (hdecode : k ≤ h + r)
    (hsize : (1 - δ) * (n : ℝ≥0) ≤ ((h + r + 1 : ℕ) : ℝ≥0))
    {L : ℕ} (hL : L≤(d+1)*(n-(h+r)))
    (emb : Fin (d+2) ↪ F) (keep : ℕ)
    (project : ∀ key : Fin L → Fin 2 → F, Function.Injective key →
      (∀ i, ∃ z ∉ univ.map (initialPositions hn), ∃ u v : Fin (d+2),
        key i 0 = -dom z ∧ key i 1 = -(emb u + emb v)) →
      ∃ a b : F, keep ≤ (univ.image fun i => a*key i 0+b*key i 1).card) :
    (keep : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤
      epsMCA (F := F) (ReedSolomon.code dom k : Set (Fin n → F)) δ := by
  classical
  let common := univ.map (initialPositions hn)
  let privateSites (j : Fin (d+1)) := univ.map (slot hn j)
  let C₀ (j : Fin (d+1)) := common ∪ privateSites j
  have hcard (j : Fin (d+1)) : (C₀ j).card=h+r := by
    simp [C₀,common,privateSites,card_union_of_disjoint (private_disjoint hn j)]
  let T := (j : Fin (d+1)) × ↥(univ \ C₀ j)
  have ht : Fintype.card T=(d+1)*(n-(h+r)) := by
    simp [T,Fintype.card_sigma,hcard]
  let E : Fin L ↪ T := (Fin.castLEEmb (hL.trans_eq ht.symm)).trans (Fintype.equivFin T).symm.toEmbedding
  let head (i : Fin L) := (E i).1
  let site (i : Fin L) := (E i).2.1
  have outside (i : Fin L) : site i∉C₀ (head i) := (mem_sdiff.mp (E i).2.2).2
  let b (j : Fin (d+1)) := emb j.castSucc
  let B (i : Fin L) := b (head i)
  let anyPrivate := univ.biUnion privateSites
  let c (x : Fin n) := if x∈anyPrivate then b (species d h x) else emb (Fin.last _)
  have c_spec (j : Fin (d+1)) (x : Fin n) : c x=b j ↔ x∈privateSites j := by
    by_cases hx : x ∈ anyPrivate
    · obtain ⟨l,_,hl⟩ := mem_biUnion.mp hx
      obtain ⟨y,_,rfl⟩ := mem_map.mp hl
      simp only [c,hx,ite_true,species_slot]
      have inj : Function.Injective b := fun a t he => Fin.castSucc_injective _ (emb.injective he)
      constructor
      · intro he
        rw [← inj he]
        exact mem_map.mpr ⟨y,mem_univ _,rfl⟩
      · intro hm
        obtain ⟨y',_,he⟩ := mem_map.mp hm
        have hj : j=l := by simpa only [species_slot] using congrArg (species d h) he
        rw [hj]
    · have hn' : x∉privateSites j := fun h => hx (mem_biUnion.mpr ⟨j,mem_univ _,h⟩)
      have he : emb (Fin.last (d+1))≠b j := fun e => Fin.castSucc_ne_last j (emb.injective e).symm
      simp [c,hx,he,hn']
  let H := Lagrange.nodal common (fun x => dom x)
  let key (i : Fin L) : Fin 2 → F := ![-dom (site i), -(B i+c (site i))]
  have hdegH : H.natDegree = h := by simp [H, common, Lagrange.natDegree_nodal]
  have hdegC (a : F) : (H * C a).natDegree ≤ h := by
    simpa [hdegH] using natDegree_mul_le (p := H) (q := C a)
  have degC (a : F) : (H * C a).degree < (k : WithBot ℕ) := by
    apply degree_le_natDegree.trans_lt
    exact_mod_cast lt_of_le_of_lt (hdegC a) (by omega : h < k)
  have degX (a : F) : (H * C a * X).degree < (k : WithBot ℕ) := by
    apply degree_le_natDegree.trans_lt
    have hle := natDegree_mul_le (p := H * C a) (q := (X : (F)[X]))
    rw [natDegree_X] at hle
    have := hdegC a
    exact_mod_cast (by omega : (H * C a * X).natDegree < k)
  have H_site (i : Fin L) : H.eval (dom (site i))≠0 := by
    apply Lagrange.eval_nodal_not_at_node
    intro x hx he
    exact outside i (mem_union_left _ ((dom.injective he).symm ▸ hx))
  have hinj : Function.Injective key := by
    intro i j he
    have hx : site i=site j := dom.injective (by simpa [key] using congrFun he 0)
    have he1 := congrFun he 1
    simp only [key,Matrix.cons_val_one,Matrix.cons_val_fin_one,neg_inj,hx,add_left_inj] at he1
    have heq : head i=head j := Fin.castSucc_injective _ (emb.injective he1)
    apply E.injective
    apply Sigma.ext heq
    apply (Subtype.heq_iff_coe_eq (fun x => ?_)).mpr hx
    change x∈univ \ C₀ (head i) ↔ x∈univ \ C₀ (head j)
    rw [heq]
  obtain ⟨aβ,bβ,kept⟩ := project key hinj (by
    intro i
    refine ⟨site i,fun hi => outside i (mem_union_left _ hi),(head i).castSucc,
      if site i∈anyPrivate then (species d h (site i)).castSucc else Fin.last _,rfl,?_⟩
    by_cases hs : site i∈anyPrivate <;> simp [key,B,b,c,hs])
  have raw := AveragedPencilProjection.mass_of_projection dom k δ (fun i => C₀ (head i)) site
    (fun i => H * C (B i) * X) (fun i => H * C (B i ^ 2)) (fun i => H * C (B i))
    (fun x => H.eval (dom x) * c x * dom x) (fun x => H.eval (dom x) * c x ^ 2)
    (fun x => H.eval (dom x) * c x) key (fun _ => degX _) (fun _ => degC _) (fun _ => degC _)
    (by
      intro i x hx
      rcases mem_union.mp hx with hc | hc
      · have hz : H.eval (dom x) = 0 := Lagrange.eval_nodal_at_node hc
        simp only [eval_mul, eval_C, eval_X, hz, zero_mul, and_self]
      · have he := (c_spec (head i) x).mpr hc
        simp only [eval_mul, eval_C, eval_X, he, B, and_self])
    (fun i => (hcard (head i)).symm ▸ hdecode)
    (fun i => by simpa only [hcard, Fintype.card_fin] using hsize)
    (by
      intro i he
      rw [eval_mul, eval_C] at he
      have hb := mul_left_cancel₀ (H_site i) he
      exact outside i (mem_union_right _ ((c_spec (head i) _).mp hb.symm)))
    (by
      intro i
      simp only [eval_mul, eval_C, eval_X, key, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one]
      constructor <;> ring)
    aβ bβ
  exact (ENNReal.div_le_div_right (by exact_mod_cast kept) _).trans raw

/-- Projective averaging retains an explicit number of bad labels for a common
locator and `d+1` heads on any injective finite-field domain. -/
theorem mass_of_count {F : Type} [Field F] [Fintype F] [NeZero n] (dom : Fin n ↪ F) (δ : ℝ≥0)
    (hn : h + (d + 1) * r ≤ n) (hdegree : h + 2 ≤ k) (hdecode : k ≤ h + r)
    (hsize : (1 - δ) * (n : ℝ≥0) ≤ ((h + r + 1 : ℕ) : ℝ≥0))
    {L : ℕ} (hL : L≤(d+1)*(n-(h+r))) :
    ((AveragedPencilProjection.retained L (Fintype.card F) : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤
      epsMCA (F := F) (ReedSolomon.code dom k : Set (Fin n → F)) δ := by
  classical
  have hr : 2≤r := by omega
  have hd : d+2≤n := by
    have hmul := Nat.mul_le_mul_left (d+1) hr
    omega
  apply mass_of_projectable dom δ hn hdegree hdecode hsize hL ((Fin.castLEEmb hd).trans dom)
  intro key hi _
  simpa only [Fintype.card_fin] using AveragedPencilProjection.exists_retained key hi

/-- Every head also receives a distinct key at each unassigned evaluation site. -/
theorem mass_over_field {F : Type} [Field F] [Fintype F] [NeZero n] (dom : Fin n ↪ F) (δ : ℝ≥0)
    (hn : h + (d + 1) * r ≤ n) (hdegree : h + 2 ≤ k) (hdecode : k ≤ h + r)
    (hsize : (1 - δ) * (n : ℝ≥0) ≤ ((h + r + 1 : ℕ) : ℝ≥0))
    :
    ((AveragedPencilProjection.retained ((d+1)*(n-(h+r))) (Fintype.card F) : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤
      epsMCA (F := F) (ReedSolomon.code dom k : Set (Fin n → F)) δ :=
  mass_of_count dom δ hn hdegree hdecode hsize le_rfl

/-- At agreement `t`, each of `m` heads supplies `n-t+1` distinct keys
provided `m*(t-k+1) ≤ n-k+2`. This form uses only the code parameters. -/
theorem grid_mass {F : Type} [Field F] [Fintype F] [NeZero n] (dom : Fin n ↪ F) (δ : ℝ≥0)
    {m t : ℕ} (hm : 0 < m) (hk : 2 ≤ k) (ht : k < t) (htn : t ≤ n)
    (hlayout : m*(t-k+1) ≤ n-k+2) (hδ : (1-δ)*(n : ℝ≥0) ≤ t) :
    ((AveragedPencilProjection.retained (m*(n-t+1)) (Fintype.card F) : ℕ) : ℝ≥0∞)/(Fintype.card F : ℝ≥0∞) ≤
      epsMCA (F:=F) (ReedSolomon.code dom k : Set (Fin n → F)) δ := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  change (d+1)*(t-k+1) ≤ n-k+2 at hlayout
  have mass := mass_over_field (d:=d) (h:=k-2) (r:=t-k+1) dom δ
    (by omega) (by omega : k-2+2≤k) (by omega)
    (by simpa only [show k-2+(t-k+1)+1=t by omega] using hδ)
  simpa only [show n-(k-2+(t-k+1))=n-t+1 by omega] using mass

/-- Projective averaging retains an explicit number of bad labels for a common
locator and `d+1` heads on any injective prime-field domain. -/
theorem mass_averaged [NeZero n] (dom : Fin n ↪ ZMod p) (δ : ℝ≥0)
    (hn : h + (d + 1) * r ≤ n) (hdegree : h + 2 ≤ k) (hdecode : k ≤ h + r)
    (hsize : (1 - δ) * (n : ℝ≥0) ≤ ((h + r + 1 : ℕ) : ℝ≥0))
    (_hp : 2 * d + 3 ≤ p) :
    ((AveragedPencilProjection.retained ((d+1)*d*r) p : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) ≤
      epsMCA (F := ZMod p) (ReedSolomon.code dom k : Set (Fin n → ZMod p)) δ := by
  have hslots : (d+1)*d*r ≤ (d+1)*(n-(h+r)) := by
    rw [Nat.mul_assoc]
    apply Nat.mul_le_mul_left
    rw [Nat.add_mul,Nat.one_mul] at hn
    omega
  simpa only [ZMod.card] using mass_of_count dom δ hn hdegree hdecode hsize hslots

/-- An arbitrary evaluation domain supports `d` bad labels per private site on
`d + 1` distinct heads with a common core of size `h`. -/
theorem mass [NeZero n] (dom : Fin n ↪ ZMod p) (δ : ℝ≥0)
    (hn : h + (d + 1) * r ≤ n) (hdegree : h + 2 ≤ k) (hdecode : k ≤ h + r)
    (hsize : (1 - δ) * (n : ℝ≥0) ≤ ((h + r + 1 : ℕ) : ℝ≥0))
    (hp : 2 * d + 3 ≤ p) (hfield : ((d + 1) * d * r).choose 2 ≤ p) :
    (((d + 1) * d * r : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) ≤
      epsMCA (F := ZMod p) (ReedSolomon.code dom k : Set (Fin n → ZMod p)) δ := by
  have h := mass_averaged dom δ hn hdegree hdecode hsize hp
  have hret : (d+1)*d*r ≤ AveragedPencilProjection.retained ((d+1)*d*r) p := by
    unfold AveragedPencilProjection.retained
    rw [Nat.div_eq_of_lt (Nat.lt_succ_of_le hfield),Nat.sub_zero]
    exact le_max_left _ _
  refine le_trans ?_ h
  gcongr

/-- Testing only one more key than the budget suffices whenever those
`B+1` keys can be separated in the field. -/
theorem over_budget {F : Type} [Field F] [Fintype F] [NeZero n] (dom : Fin n ↪ F) (δ : ℝ≥0)
    (hn : h+(d+1)*r ≤ n) (hdegree : h+2 ≤ k) (hdecode : k ≤ h+r)
    (hsize : (1-δ)*(n : ℝ≥0) ≤ ((h+r+1 : ℕ) : ℝ≥0)) {Q : ℕ} (hQ : 0 < Q)
    (hbudget : Fintype.card F/Q < (d+1)*(n-(h+r)))
    (hpair : (Fintype.card F/Q+1).choose 2 ≤ Fintype.card F) :
    1/(Q:ℝ≥0∞) < epsMCA (F:=F) (ReedSolomon.code dom k : Set (Fin n → F)) δ := by
  let B := Fintype.card F/Q
  have hmass := mass_of_count dom δ hn hdegree hdecode hsize (L:=B+1) hbudget
  have hret : B+1≤AveragedPencilProjection.retained (B+1) (Fintype.card F) := by
    unfold AveragedPencilProjection.retained
    rw [Nat.div_eq_of_lt (Nat.lt_succ_of_le hpair),Nat.sub_zero]
    exact le_max_left _ _
  by_contra! safe
  have bound := (BoundarySecurityBudget.count_ratio_le_iff Fintype.card_pos hQ).mp (hmass.trans safe)
  exact (Nat.not_succ_le_self B) (hret.trans bound)

/-- For the full 128-bit prize field range, the raw private-site count already
certifies failure once it exceeds the integer budget. -/
theorem over_budget_128 {F : Type} [Field F] [Fintype F] [NeZero n] (dom : Fin n ↪ F) (δ : ℝ≥0)
    (hn : h+(d+1)*r ≤ n) (hdegree : h+2 ≤ k) (hdecode : k ≤ h+r)
    (hsize : (1-δ)*(n : ℝ≥0) ≤ ((h+r+1 : ℕ) : ℝ≥0))
    (hrange : Fintype.card F ≤ 2^256) (hbudget : Fintype.card F / 2^128 < (d+1)*(n-(h+r))) :
    1/(2:ℝ≥0∞)^128 < epsMCA (F:=F) (ReedSolomon.code dom k : Set (Fin n → F)) δ := by
  have mass := mass_over_field dom δ hn hdegree hdecode hsize
  have hb := AveragedPencilProjection.tolerance_budget_lt_retained (by decide : 0 < 2^128)
    (show Fintype.card F ≤ (2^128)^2 by convert hrange using 1) hbudget
  by_contra! safe
  apply hb.not_ge
  apply (BoundarySecurityBudget.count_ratio_le_iff Fintype.card_pos (by decide : 0 < 2^128)).mp
  exact mass.trans (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using safe)

end ArkLib.ProximityGap.Frontier.ManyHeadLocatorMass

#print axioms ArkLib.ProximityGap.Frontier.ManyHeadLocatorMass.mass
#print axioms ArkLib.ProximityGap.Frontier.ManyHeadLocatorMass.mass_of_count
#print axioms ArkLib.ProximityGap.Frontier.ManyHeadLocatorMass.mass_over_field
#print axioms ArkLib.ProximityGap.Frontier.ManyHeadLocatorMass.grid_mass
#print axioms ArkLib.ProximityGap.Frontier.ManyHeadLocatorMass.mass_averaged
#print axioms ArkLib.ProximityGap.Frontier.ManyHeadLocatorMass.over_budget
#print axioms ArkLib.ProximityGap.Frontier.ManyHeadLocatorMass.over_budget_128
