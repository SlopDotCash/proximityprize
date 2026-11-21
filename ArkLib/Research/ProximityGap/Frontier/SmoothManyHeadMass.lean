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
  obtain ⟨a,sep⟩ := smooth_labels x b (by simpa using room)
  let S := (Fin (d+1) × Fin d) × Fin r
  let owner (s : S) := s.1.1
  let target (s : S) := s.1.1.succAbove s.1.2
  let e (s : S) := pair (owner s) (target s)
  have diff (s : S) : target s ≠ owner s := s.1.1.succAbove_ne s.1.2
  have edge (s : S) : e s ∈ edges (d+1) := by
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    change min (owner s) (target s) < max (owner s) (target s)
    rcases lt_or_gt_of_ne (diff s) with h|h
    · simpa [min_eq_right h.le,max_eq_left h.le] using h
    · simpa [min_eq_left h.le,max_eq_right h.le] using h
  let site (s : S) := slot hn (owner s) s.2
  let z (s : S) := -(((a (e s).1-a (e s).2)/(b (e s).1-b (e s).2))*x (site s))
  have inject : Function.Injective z := by
    rintro ⟨⟨i,j⟩,u⟩ ⟨⟨i',j'⟩,v⟩ eq
    let s : S := ((i,j),u)
    let t : S := ((i',j'),v)
    have both : (e s,site s)=(e t,site t) :=
      sep (edge s) (edge t) ((neg_inj).mp (show z s=z t from eq))
    have hsite : site s=site t := congrArg Prod.snd both
    have ho : i=i' := by simpa [s,t,site,owner,species_slot] using congrArg (species d h) hsite
    subst i'
    have huv : u=v := (slot hn i).injective hsite
    subst v
    have em := congrArg (fun p : Edge (d+1) × Fin n => p.1.1.val+p.1.2.val) both
    change (min i (i.succAbove j)).val+(max i (i.succAbove j)).val =
      (min i (i.succAbove j')).val+(max i (i.succAbove j')).val at em
    simp only [Fin.val_min,Fin.val_max,min_add_max] at em
    have hj : j=j' := i.succAbove_right_injective (Fin.ext (Nat.add_left_cancel em))
    subst j'
    rfl
  let common := univ.map (initialPositions hn)
  let core (s : S) := common ∪ univ.map (slot hn (target s))
  let H := Lagrange.nodal common x
  let B (c : F) := H * Polynomial.C c
  let A (c : F) := B c * (Polynomial.X : F[X])
  let rows : WordStack F (Fin 2) (Fin n) :=
    ![fun i => H.eval (x i)*a (species d h i)*x i, fun i => H.eval (x i)*b (species d h i)]
  have bound (c : F) : (B c).natDegree ≤ h := by
    simpa [B,H,common,Lagrange.natDegree_nodal] using natDegree_mul_le (p:=H) (q:=Polynomial.C c)
  have degB (c : F) : (B c).degree < (k : WithBot ℕ) := by
    apply degree_le_natDegree.trans_lt
    exact_mod_cast (lt_of_le_of_lt (bound c) (by omega : h<k))
  have degA (c : F) : (A c).degree < (k : WithBot ℕ) := by
    apply degree_le_natDegree.trans_lt
    have aux := natDegree_mul_le (p:=B c) (q:=(Polynomial.X : F[X]))
    rw [natDegree_X] at aux
    have := bound c
    exact_mod_cast (show (A c).natDegree<k by dsimp [A];omega)
  have card (s : S) : (core s).card = h+r := by
    simp [core,common,card_union_of_disjoint (private_disjoint hn (target s))]
  have event (s : S) : mcaEvent (F:=F) (ReedSolomon.code x k : Set (Fin n → F)) δ
      (rows 0) (rows 1) (z s) := by
    have Hnz : H.eval (x (site s)) ≠ 0 := by
      apply Lagrange.eval_nodal_not_at_node
      intro i hi eq
      exact disjoint_left.mp (private_disjoint hn (owner s)) hi
        (x.injective eq ▸ mem_map.mpr ⟨s.2,mem_univ _,rfl⟩)
    have off : site s ∉ core s := by
      intro hi
      rcases mem_union.mp hi with hcommon|hslot
      · exact Hnz (Lagrange.eval_nodal_at_node hcommon)
      · obtain ⟨u,_,eq⟩ := mem_map.mp hslot
        apply diff s
        simpa [site,species_slot] using congrArg (species d h) eq
    have sepB : b (owner s) - b (target s) ≠ 0 := sub_ne_zero.mpr (b.injective.ne (diff s).symm)
    apply mcaEvent_of_affine_core_fresh x k δ rows (z s) (core s) (site s)
      (A (a (target s))) (B (b (target s))) off (degA _) (degB _)
    · apply degree_add_le _ _ |>.trans_lt
      apply max_lt (degA _)
      by_cases zero : z s=0
      · simp [zero]
      · simpa [degree_C_mul zero] using degB (b (target s))
    · rwa [card]
    · simpa only [card,Fintype.card_fin] using hs
    · intro i hi
      rcases mem_union.mp hi with hcommon|hslot
      · have hz : H.eval (x i)=0 := Lagrange.eval_nodal_at_node hcommon
        simp [A,B,rows,hz]
      · obtain ⟨u,_,rfl⟩ := mem_map.mp hslot
        simp [A,B,rows,species_slot]
    · simp [A,B,rows,z,e,slope_pair,site,species_slot]
      field_simp [sepB]
      ring
    · intro eq
      have bad := congrArg Prod.snd eq
      simp only [B,eval_mul,eval_C,rows,Matrix.cons_val_one,Matrix.cons_val_fin_one] at bad
      exact diff s <| b.injective <| mul_left_cancel₀ Hnz <| by simpa [site,species_slot] using bad
  have raw := MCAWitnessSpread.epsMCA_ge_card_div_of_mcaEvent_set
    (ReedSolomon.code x k : Set (Fin n → F)) δ rows (univ.image z)
    (fun l hl => by obtain ⟨s,_,rfl⟩ := mem_image.mp hl;exact event s)
  simpa only [card_image_of_injective _ inject,card_univ,S,Fintype.card_prod,Fintype.card_fin] using raw

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
