/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.ManyHeadLocatorMass
import ArkLib.Research.ProximityGap.Frontier.CosetHeadSlopes

/-! # Many-head MCA mass on smooth domains in fields of linear size

Multiplicatively separated slopes keep all bad challenges distinct across
unordered head pairs. The private site recovers the owner, so each ordered
owner-target pair at a private coordinate contributes a new challenge.
-/

set_option autoImplicit false
namespace ProximityGap.SmoothManyHeadMass
open Finset Polynomial CosetHeadSlopes Code
open ArkLib.ProximityGap.Frontier.ManyHeadLocatorMass
open ArkLib.ProximityGap.Frontier.HalfPredecessorCoreFreshDecode
open scoped NNReal ENNReal

private def pair {m : ℕ} (u v : Fin m) : Edge m := (min u v, max u v)

private theorem slope_pair {m : ℕ} {F : Type} [Field F] (a b : Fin m → F)
    (u v : Fin m) : (a (pair u v).1-a (pair u v).2)/(b (pair u v).1-b (pair u v).2) =
    (a u-a v)/(b u-b v) := by
  rcases le_total u v with h|h
  · simp [pair,min_eq_left h,max_eq_right h]
  · simp only [pair,min_eq_right h,max_eq_left h]
    rw [←neg_sub (a u) (a v), ←neg_sub (b u) (b v), neg_div_neg_eq]

set_option maxHeartbeats 1600000 in
private theorem mass_of_assignment {F S : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype S]
    {m n k : ℕ} [NeZero n] (x : Fin n ↪ F) [ReedSolomon.Smooth x] (δ : ℝ≥0) (b : Fin m ↪ F)
    (common : Finset (Fin n)) (owner : Fin n → Fin m) (target : S → Fin m)
    (site : S → Fin n) (core : S → Finset (Fin n))
    (degree_room : common.card + 2 ≤ k)
    (degree_pin : ∀ s, k ≤ (core s).card)
    (size : ∀ s, (1-δ)*(n : ℝ≥0) ≤ (((core s).card+1 : ℕ) : ℝ≥0))
    (fits : ∀ s i, i ∈ core s → i ∈ common ∨ owner i = target s)
    (outside : ∀ s, site s ∉ common)
    (diff : ∀ s, target s ≠ owner (site s))
    (unique : Function.Injective (fun s => (target s,site s)))
    (room : ((edges m).card + (edges m).offDiag.card*n)*(m-1) < Fintype.card F) :
    (Fintype.card S : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤
      epsMCA (F:=F) (ReedSolomon.code x k : Set (Fin n → F)) δ := by
  classical
  obtain ⟨a,sep⟩ := smooth_labels x b (by simpa using room)
  let e (s : S) := pair (owner (site s)) (target s)
  have edge (s : S) : e s ∈ edges m := by
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    change min (owner (site s)) (target s) < max (owner (site s)) (target s)
    rcases lt_or_gt_of_ne (diff s) with h|h
    · simpa [min_eq_right h.le,max_eq_left h.le] using h
    · simpa [min_eq_left h.le,max_eq_right h.le] using h
  let z (s : S) := -(((a (e s).1-a (e s).2)/(b (e s).1-b (e s).2))*x (site s))
  have inject : Function.Injective z := by
    intro s t eq
    have both : (e s,site s)=(e t,site t) := sep (edge s) (edge t) (neg_inj.mp eq)
    have hsite : site s = site t := congrArg Prod.snd both
    apply unique
    refine Prod.ext ?_ hsite
    have em := congrArg (fun p : Edge m × Fin n => p.1.1.val+p.1.2.val) both
    simp only [e,pair,Fin.val_min,Fin.val_max,min_add_max] at em
    rw [hsite] at em
    exact Fin.ext <| Nat.add_left_cancel em
  let H := Lagrange.nodal common x
  let B (c : F) := H * Polynomial.C c
  let A (c : F) := B c * (Polynomial.X : F[X])
  let rows : WordStack F (Fin 2) (Fin n) :=
    ![fun i => H.eval (x i)*a (owner i)*x i, fun i => H.eval (x i)*b (owner i)]
  have bound (c : F) : (B c).natDegree ≤ common.card := by
    simpa [B,H,Lagrange.natDegree_nodal] using natDegree_mul_le (p:=H) (q:=Polynomial.C c)
  have degB (c : F) : (B c).degree < (k : WithBot ℕ) := by
    apply degree_le_natDegree.trans_lt
    exact_mod_cast (lt_of_le_of_lt (bound c) (by omega : common.card<k))
  have degA (c : F) : (A c).degree < (k : WithBot ℕ) := by
    apply degree_le_natDegree.trans_lt
    have aux := natDegree_mul_le (p:=B c) (q:=(Polynomial.X : F[X]))
    rw [natDegree_X] at aux
    have := bound c
    exact_mod_cast (show (A c).natDegree<k by dsimp [A];omega)
  have event (s : S) : mcaEvent (F:=F) (ReedSolomon.code x k : Set (Fin n → F)) δ
      (rows 0) (rows 1) (z s) := by
    have Hnz : H.eval (x (site s)) ≠ 0 := Lagrange.eval_nodal_not_at_node
      fun i hi eq => outside s (x.injective eq ▸ hi)
    have off : site s ∉ core s :=
      fun hi => (fits s _ hi).elim (outside s) (Ne.symm (diff s))
    have sepB := sub_ne_zero.mpr (b.injective.ne (diff s).symm)
    apply mcaEvent_of_affine_core_fresh x k δ rows (z s) (core s) (site s)
      (A (a (target s))) (B (b (target s))) off (degA _) (degB _)
    · apply degree_add_le _ _ |>.trans_lt
      apply max_lt (degA _)
      by_cases zero : z s=0
      · simp [zero]
      · simpa [degree_C_mul zero] using degB (b (target s))
    · exact degree_pin s
    · simpa using size s
    · intro i hi
      rcases fits s i hi with commonSite|owns
      · have hz : H.eval (x i)=0 := Lagrange.eval_nodal_at_node commonSite
        simp [A,B,rows,hz]
      · simp [A,B,rows,owns]
    · simp [A,B,rows,z,e,slope_pair]
      field_simp [sepB]
      ring
    · intro eq
      have bad := congrArg Prod.snd eq
      simp only [B,eval_mul,eval_C,rows,Matrix.cons_val_one,Matrix.cons_val_fin_one] at bad
      exact diff s <| b.injective <| mul_left_cancel₀ Hnz bad
  have raw := MCAWitnessSpread.epsMCA_ge_card_div_of_mcaEvent_set
    (ReedSolomon.code x k : Set (Fin n → F)) δ rows (univ.image z)
    (fun l hl => by obtain ⟨s,_,rfl⟩ := mem_image.mp hl;exact event s)
  simpa only [card_image_of_injective _ inject,card_univ] using raw

set_option maxHeartbeats 1800000 in
/-- Each of the (d+1)r private sites contributes d genuinely distinct bad
challenges. For fixed head count, the only size condition on the field is
linear in the evaluation length. The construction applies in any characteristic. -/
theorem mass {F : Type} [Field F] [Fintype F] [DecidableEq F] {n h d r k : ℕ} [NeZero n]
    (x : Fin n ↪ F) [ReedSolomon.Smooth x] (δ : ℝ≥0) (b : Fin (d+1) ↪ F)
    (hn : h+(d+1)*r ≤ n) (hd : h+2 ≤ k) (hc : k ≤ h+r)
    (hs : (1-δ)*(n : ℝ≥0) ≤ ((h+r+1 : ℕ) : ℝ≥0))
    (room : ((edges (d+1)).card + (edges (d+1)).offDiag.card*n)*d < Fintype.card F) :
    (((d+1)*d*r : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤
      epsMCA (F:=F) (ReedSolomon.code x k : Set (Fin n → F)) δ := by
  classical
  let S := (Fin (d+1) × Fin d) × Fin r
  let target (s : S) := s.1.1.succAbove s.1.2
  let site (s : S) := slot hn s.1.1 s.2
  let common := univ.map (initialPositions hn)
  let core (s : S) := common ∪ univ.map (slot hn (target s))
  have card (s : S) : (core s).card = h+r := by
    simp [core,common,card_union_of_disjoint (private_disjoint hn (target s))]
  have f (s : S) : species d h (site s)=s.1.1 := species_slot ..
  have raw := mass_of_assignment x δ b common (species d h) target site core
    (by simpa [common] using hd) (fun s => by rwa [card]) (fun s => by rwa [card])
    (by
      intro s i hi
      rcases mem_union.mp hi with hi|hi
      · exact Or.inl hi
      · obtain ⟨w,_,rfl⟩ := mem_map.mp hi
        exact Or.inr (species_slot ..))
    (fun s hi => disjoint_left.mp (private_disjoint hn s.1.1) hi (mem_map.mpr ⟨s.2,mem_univ _,rfl⟩))
    (fun s => by rw [f]; exact s.1.1.succAbove_ne s.1.2)
    (by
      rintro ⟨⟨i,j⟩,u⟩ ⟨⟨i',j'⟩,v⟩ eq
      have same := congrArg Prod.snd eq
      have ho : i=i' := by simpa [site,species_slot] using congrArg (species d h) same
      subst i'
      have ht : i.succAbove j=i.succAbove j' := congrArg Prod.fst eq
      exact Prod.ext (Prod.ext rfl (i.succAbove_right_injective ht)) ((slot hn i).injective same))
    (by simpa using room)
  simpa only [S,Fintype.card_prod,Fintype.card_fin] using raw

/-- Reserve one additional coefficient for sites without an assigned head.
Then every fresh site of every active core contributes exactly one label
to the constructed subset, including the sites outside all private blocks. -/
theorem all_fresh {F : Type} [Field F] [Fintype F] [DecidableEq F] {n h d r k : ℕ} [NeZero n]
    (x : Fin n ↪ F) [ReedSolomon.Smooth x] (δ : ℝ≥0) (b : Fin (d+2) ↪ F)
    (hn : h+(d+1)*r ≤ n) (hd : h+2 ≤ k) (hc : k ≤ h+r)
    (hs : (1-δ)*(n : ℝ≥0) ≤ ((h+r+1 : ℕ) : ℝ≥0))
    (room : ((edges (d+2)).card + (edges (d+2)).offDiag.card*n)*(d+1) < Fintype.card F) :
    (((d+1)*(n-(h+r)) : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤
      epsMCA (F:=F) (ReedSolomon.code x k : Set (Fin n → F)) δ := by
  classical
  let common := univ.map (initialPositions hn)
  let block (j : Fin (d+1)) := univ.map (slot hn j)
  let core (j : Fin (d+1)) := common ∪ block j
  have card (j : Fin (d+1)) : (core j).card = h+r := by
    simp [core,common,block,card_union_of_disjoint (private_disjoint hn j)]
  let S := (j : Fin (d+1)) × ↥((core j)ᶜ)
  let site (s : S) : Fin n := s.2.val
  let own (i : Fin n) : Fin (d+2) :=
    if ∃ j, i ∈ block j then (species d h i).castSucc else Fin.last (d+1)
  have in_block (j : Fin (d+1)) {i : Fin n} (hi : i ∈ block j) : own i=j.castSucc := by
    obtain ⟨v,_,rfl⟩ := mem_map.mp hi
    simp [own,show ∃ l, slot hn j v ∈ block l from ⟨j,hi⟩,species_slot]
  have fresh (s : S) : site s ∉ core s.1 := mem_compl.mp s.2.property
  have raw := mass_of_assignment x δ b common own (fun s : S => s.1.castSucc) site
    (fun s => core s.1) (by simpa [common] using hd) (fun s => by rwa [card])
    (fun s => by rwa [card])
    (fun s i hi => (mem_union.mp hi).imp_right (in_block s.1))
    (fun s hi => fresh s (mem_union_left _ hi))
    (by
      intro s eq
      by_cases used : ∃ j, site s ∈ block j
      · obtain ⟨j,hj⟩ := used
        have same : s.1=j := Fin.castSucc_injective _ (eq.trans (in_block j hj))
        exact fresh s (mem_union_right _ (same.symm ▸ hj))
      · have bad : s.1.castSucc = Fin.last (d+1) := by simpa [own,used] using eq
        exact Fin.castSucc_ne_last _ bad)
    (by
      intro s t eq
      obtain ⟨j,u⟩ := s
      obtain ⟨l,v⟩ := t
      have same : j=l := Fin.castSucc_injective _ (congrArg Prod.fst eq)
      subst l
      have he : u=v := Subtype.ext (congrArg Prod.snd eq)
      subst v
      rfl)
    (by simpa using room)
  have count : Fintype.card S=(d+1)*(n-(h+r)) := by
    simp [S,Fintype.card_sigma,card_compl,card]
  simpa only [count] using raw

/-- A direct finite ceiling at any requested error count. The packing
condition reserves n-k+1-e private coordinates per head. Every one of
the m(e+1) fresh labels is distinct when the smooth field-size test holds. -/
theorem ceiling_at_errors {n k d e p Q : ℕ} [Fact p.Prime] [NeZero n] (x : Fin n ↪ ZMod p)
    [ReedSolomon.Smooth x] (hk : 2 ≤ k) (errors : k+e+1 ≤ n) (hQ : 0 < Q)
    (packing : (d+1)*(n-k+1-e) ≤ n-k+2)
    (room : ((edges (d+2)).card + (edges (d+2)).offDiag.card*n)*(d+1) < p)
    (budget : p/Q < (d+1)*(e+1)) :
    MCAThresholdLedger.mcaDeltaStar (F:=ZMod p) (ReedSolomon.code x k : Set (Fin n → ZMod p))
      (1/(Q : ℝ≥0∞)) ≤ (e : ℝ≥0)/n := by
  let r := n-k+1-e
  have hr : 2 ≤ r := by dsimp [r]; omega
  have hn : k-2+(d+1)*r ≤ n := by dsimp [r]; omega
  have dp : d+2 ≤ Fintype.card (ZMod p) := by
    have grow := Nat.mul_le_mul_left (d+1) hr
    have inj : n ≤ Fintype.card (ZMod p) := by simpa using Fintype.card_le_of_injective x x.injective
    omega
  let b := (Fin.castLEEmb dp).trans (Fintype.equivFin (ZMod p)).symm.toEmbedding
  have ni : (n : ℝ≥0) ≠ 0 := by exact_mod_cast NeZero.ne n
  have size : (1-(e : ℝ≥0)/n)*n ≤ ((k-2+r+1 : ℕ) : ℝ≥0) := by
    rw [tsub_mul,one_mul,div_mul_cancel₀ _ ni,←Nat.cast_tsub]
    exact_mod_cast (show n-e ≤ k-2+r+1 by dsimp [r];omega)
  have h := all_fresh (k:=k) x ((e : ℝ≥0)/n) b hn (by omega) (by omega) size (by simpa using room)
  rw [ZMod.card,show n-(k-2+r)=e+1 by dsimp [r];omega] at h
  apply MCAThresholdLedger.mcaDeltaStar_le_of_bad
  apply lt_of_lt_of_le _ h
  apply lt_of_not_ge
  rw [BoundarySecurityBudget.count_ratio_le_iff (Fact.out (p:=p.Prime)).pos hQ]
  exact Nat.not_le_of_lt budget

/-- A numerical ceiling using the longest possible common locator. Put
r = floor((n-k+2)/(d+1)). Whenever the (d+1)d r actual bad challenges
exceed the scalar budget, the first failing radius is at most (n-k+1-r)/n. -/
theorem ceiling {n k d p Q : ℕ} [Fact p.Prime] [NeZero n] (x : Fin n ↪ ZMod p)
    [ReedSolomon.Smooth x] (hk : 2 ≤ k) (hkn : k ≤ n) (hQ : 0 < Q)
    (hr : 2 ≤ (n-k+2)/(d+1))
    (room : ((edges (d+1)).card + (edges (d+1)).offDiag.card*n)*d < p)
    (budget : p/Q < (d+1)*d*((n-k+2)/(d+1))) :
    MCAThresholdLedger.mcaDeltaStar (F:=ZMod p) (ReedSolomon.code x k : Set (Fin n → ZMod p))
      (1/(Q : ℝ≥0∞)) ≤ ((n-k+1-(n-k+2)/(d+1) : ℕ) : ℝ≥0)/n := by
  let r := (n-k+2)/(d+1)
  have packing : (d+1)*r ≤ n-k+2 := by
    simpa [r,Nat.mul_comm] using Nat.div_mul_le_self (n-k+2) (d+1)
  have hn : k-2+(d+1)*r ≤ n := by omega
  have dp : d+1 ≤ Fintype.card (ZMod p) := by
    have small : 1 ≤ r := by omega
    have h := Nat.mul_le_mul_left (d+1) small
    rw [Nat.mul_one] at h
    exact h.trans ((Nat.le_add_left _ _).trans (hn.trans <| by simpa using Fintype.card_le_of_injective x x.injective))
  let b := (Fin.castLEEmb dp).trans (Fintype.equivFin (ZMod p)).symm.toEmbedding
  let e := n-k+1-r
  have ni : (n : ℝ≥0) ≠ 0 := by exact_mod_cast NeZero.ne n
  have size : (1-(e : ℝ≥0)/n)*n ≤ ((k-2+r+1 : ℕ) : ℝ≥0) := by
    rw [tsub_mul,one_mul,div_mul_cancel₀ _ ni,←Nat.cast_tsub]
    exact_mod_cast (show n-e ≤ k-2+r+1 by dsimp [e];omega)
  have h := mass (k:=k) x ((e : ℝ≥0)/n) b hn (by omega) (by omega) size (by simpa using room)
  rw [ZMod.card] at h
  apply MCAThresholdLedger.mcaDeltaStar_le_of_bad
  apply lt_of_lt_of_le _ h
  apply lt_of_not_ge
  rw [BoundarySecurityBudget.count_ratio_le_iff (Fact.out (p:=p.Prime)).pos hQ]
  exact Nat.not_le_of_lt budget

end ProximityGap.SmoothManyHeadMass
#print axioms ProximityGap.SmoothManyHeadMass.mass
#print axioms ProximityGap.SmoothManyHeadMass.ceiling
#print axioms ProximityGap.SmoothManyHeadMass.all_fresh
#print axioms ProximityGap.SmoothManyHeadMass.ceiling_at_errors
