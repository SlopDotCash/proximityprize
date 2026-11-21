/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.GeneralTwoLineSafety
import ArkLib.Research.ProximityGap.Frontier.SmoothManyHeadMass

/-! # Covering a rich family by a prescribed number of polynomial lines

The cubic moment forces another large secant while enough bad challenges
remain. Pairwise intersections of its cores bound the space available to
one further point outside all the resulting lines.
-/
namespace ProximityGap.GeneralManyLineSafety

open Polynomial Finset Code
open ArkLib.ProximityGap.Frontier
open ArkLib.ProximityGap.Frontier.HalfPredecessorLineCoreGeometry
open ArkLib.ProximityGap.Frontier.HalfPredecessorSecantLines
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateEighthFullWiring
open scoped NNReal ENNReal BigOperators

private theorem union_cap {A B : Type*} [DecidableEq B] (s : Finset A) (f : A → Finset B)
    {k : ℕ} (h : ∀ a ∈ s, (f a).card ≤ k) : (s.biUnion f).card ≤ s.card*k := by
  classical
  apply card_biUnion_le.trans
  simpa only [sum_const,nsmul_eq_mul,Nat.cast_id] using (sum_le_sum (s := s) (fun a ha => h a ha))

/-- The pairwise Bonferroni bound with a uniform cap on each intersection. -/
theorem core_mass_le {A B : Type*} [DecidableEq B] (s : Finset A) (f : A → Finset B) {d : ℕ}
    (h : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → (f a ∩ f b).card ≤ d) :
    ∑ a ∈ s, (f a).card ≤ (s.biUnion f).card + s.card.choose 2*d := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have ih' := ih fun i hi j hj hn => h i (mem_insert_of_mem hi) j (mem_insert_of_mem hj) hn
    have hi : (f a ∩ s.biUnion f).card ≤ s.card*d := by
      rw [inter_biUnion]
      apply union_cap
      intro j hj
      exact h a (mem_insert_self _ _) j (mem_insert_of_mem hj) (fun e => ha (e ▸ hj))
    have hu := card_union_add_card_inter (f a) (s.biUnion f)
    rw [sum_insert ha,biUnion_insert,card_insert_of_notMem ha,Nat.choose_succ_succ,
      Nat.choose_one_right,Nat.add_mul]
    change _ ≤ _ + (s.card*d+s.card.choose 2*d)
    omega

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I]
  [Field F] [Fintype F] [DecidableEq F] {D : I ↪ F} {k : ℕ} {δ : ℝ≥0}
  {u : WordStack F (Fin 2) I}

/-- The uniform r-line cap on any rich family of selected worst-case challenges. -/
theorem family_card_le (fam : BadScalarRichPointFamily D k δ u) {n t e L r : ℕ}
    (hn : Fintype.card I = n) (he : e+t=n) (hk : 1≤k) (_htk : k≤t) (hL : 2≤L) (_hr : 1≤r)
    (ht : ⌈(1-δ)*(Fintype.card I : ℝ≥0)⌉₊ = t)
    (hm : (e+2)*k*n^2+(L+2)*n^3 < (e+2)*t^3)
    (hg : (n+(r.choose 2+r)*k)*L+r*n < (r+1)*t*L) : fam.G.card ≤ r*(e+1) := by
  classical
  by_contra! large
  let z := t-n/L
  let C (l : LineParameter F) := jointCore D (u 0) (u 1) l.1 l.2
  let pts := pointsOn fam
  have line_bound {s : Finset (LineParameter F)} (hsub : s ⊆ lineParameters fam) :
      (s.biUnion pts).card ≤ s.card*(e+1) :=
    union_cap s pts (fun l hl => TwoLargeCoreCount.line_occupancy_le fam (hn.trans he.symm) ht (hsub hl))
  have build (m : ℕ) (hmr : m≤r) : ∃ s : Finset (LineParameter F),
      s.card=m ∧ s ⊆ lineParameters fam ∧ ∀ l ∈ s, z ≤ (C l).card := by
    induction m with
    | zero => exact ⟨∅,rfl,empty_subset _,by simp⟩
    | succ m ih =>
      obtain ⟨s,hs,sub,hcore⟩ := ih (by omega)
      let H := fam.G \ s.biUnion pts
      have subG : s.biUnion pts ⊆ fam.G := by
        intro a ha
        obtain ⟨l,_,ha⟩ := mem_biUnion.mp ha
        exact pointsOn_subset_G fam l ha
      have occ := line_bound sub
      rw [hs] at occ
      have hle := Nat.mul_le_mul_right (e+1) hmr
      rw [Nat.succ_mul] at hle
      have enough : e+2 ≤ H.card := by
        rw [card_sdiff_of_subset subG]
        omega
      obtain ⟨a,ha,b,hb,hab,hz⟩ := GeneralTwoLineSafety.exists_large_core fam hn hk hL ht hm H
        sdiff_subset enough
      let l := secantParameter fam a b
      have haG := (mem_sdiff.mp ha).1
      have hbG := (mem_sdiff.mp hb).1
      have hl : l ∈ lineParameters fam := secantParameter_mem_lineParameters fam haG hbG hab
      have fresh : l ∉ s := fun h => (mem_sdiff.mp ha).2
        (mem_biUnion.mpr ⟨l,h,first_point_mem_pointsOn_secant fam (beta := b) haG⟩)
      exact ⟨insert l s,by rw [card_insert_of_notMem fresh,hs],insert_subset hl sub,
        fun a ha => (mem_insert.mp ha).elim (fun h => h ▸ hz) (hcore a)⟩
  obtain ⟨s,hs,sub,hcore⟩ := build r le_rfl
  have houts : ¬ fam.G ⊆ s.biUnion pts := by
    intro h
    have cap := (card_le_card h).trans (line_bound sub)
    rw [hs] at cap
    omega
  obtain ⟨a,ha,haout⟩ := Finset.not_subset.mp houts
  let A := fullAgreement D (u 0) (u 1) a (fam.q a)
  have rich : t ≤ A.card := ht ▸ fam.threshold_le a ha
  have bound (l : LineParameter F) (hl : l ∈ s) : (A ∩ C l).card ≤ k := by
    have hline := lineParameter_degree_lt fam (sub hl)
    apply (fullAgreement_inter_jointCore_card_le D (u 0) (u 1) hk (fam.degree_lt a ha)
      hline.1 hline.2 ?_).trans (Nat.sub_le _ _)
    intro eq
    exact haout (mem_biUnion.mpr ⟨l,hl,(mem_pointsOn_iff fam l a).mpr ⟨ha,eq⟩⟩)
  have inter : (A ∩ s.biUnion C).card ≤ r*k := by
    rw [inter_biUnion,←hs]
    exact union_cap _ _ bound
  have mass := core_mass_le s C (d := k) (fun l hl m hm hne =>
    (jointCore_inter_card_le_degree_pred fam hk (sub hl) (sub hm) hne).trans (Nat.sub_le _ _))
  have lower : s.card*z ≤ ∑ l ∈ s, (C l).card := by
    simpa only [sum_const,nsmul_eq_mul,Nat.cast_id] using sum_le_sum (s := s) (fun l hl => hcore l hl)
  rw [hs] at mass lower
  have eq := card_union_add_card_inter A (s.biUnion C)
  have total := Finset.card_le_univ (A ∪ s.biUnion C)
  rw [hn] at total
  have cap : t+r*z ≤ n+(r.choose 2+r)*k := by rw [Nat.add_mul]; omega
  have ha := Nat.mul_le_mul_right L cap
  have hdiv := Nat.div_mul_le_self n L
  have suble := Nat.mul_le_mul_right (r*L) (show t ≤ z+n/L by dsimp [z]; omega)
  nlinarith [Nat.mul_le_mul_left r hdiv]

open Classical in
/-- The actual count of bad challenge scalars for arbitrary received words. -/
theorem count_le (D : I ↪ F) (u₀ u₁ : I → F) (δ : ℝ≥0) {n k t e L r : ℕ}
    (hn : Fintype.card I = n) (he : e+t=n) (hk : 1≤k) (htk : k≤t) (hL : 2≤L) (hr : 1≤r)
    (ht : ⌈(1-δ)*(Fintype.card I : ℝ≥0)⌉₊ = t)
    (hm : (e+2)*k*n^2+(L+2)*n^3 < (e+2)*t^3)
    (hg : (n+(r.choose 2+r)*k)*L+r*n < (r+1)*t*L) :
    (univ.filter (mcaEvent (F := F) (ReedSolomon.code D k : Set (I → F)) δ u₀ u₁)).card ≤ r*(e+1) :=
  family_card_le (canonicalBadScalarRichPointFamily D (k := k) δ ![u₀,u₁] hk)
    hn he hk htk hL hr ht hm hg

/-- Worst-case proximity error in the r-line regime. -/
theorem epsMCA_le (D : I ↪ F) (δ : ℝ≥0) {n k t e L r : ℕ}
    (hn : Fintype.card I = n) (he : e+t=n) (hk : 1≤k) (htk : k≤t) (hL : 2≤L) (hr : 1≤r)
    (ht : ⌈(1-δ)*(Fintype.card I : ℝ≥0)⌉₊ = t)
    (hm : (e+2)*k*n^2+(L+2)*n^3 < (e+2)*t^3)
    (hg : (n+(r.choose 2+r)*k)*L+r*n < (r+1)*t*L) :
    epsMCA (F := F) (ReedSolomon.code D k : Set (I → F)) δ ≤
      ((r*(e+1) : ℕ) : ℝ≥0∞)/(Fintype.card F : ℝ≥0∞) :=
  epsMCA_le_of_badCount_le _ _ _ (fun u => count_le D (u 0) (u 1) δ hn he hk htk hL hr ht hm hg)

/-- On every injective domain the projected private cores attain all r(e+1)
labels as soon as the number of pairs of labels fits in the field. -/
theorem epsMCA_eq_of_pair_supply {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {n k t e L r : ℕ} [NeZero n] (D : Fin n ↪ F) (δ : ℝ≥0)
    (he : e+t=n) (hk : 2≤k) (htk : k<t) (hL : 2≤L) (hr : 1≤r)
    (ht : ⌈(1-δ)*(n : ℝ≥0)⌉₊ = t)
    (hm : (e+2)*k*n^2+(L+2)*n^3 < (e+2)*t^3)
    (hg : (n+(r.choose 2+r)*k)*L+r*n < (r+1)*t*L)
    (pack : r*(t-k+1)≤n-k+2) (room : (r*(e+1)).choose 2≤Fintype.card F) :
    epsMCA (F:=F) (ReedSolomon.code D k : Set (Fin n → F)) δ =
      ((r*(e+1):ℕ):ℝ≥0∞)/(Fintype.card F : ℝ≥0∞) := by
  refine le_antisymm (epsMCA_le D δ (Fintype.card_fin _) he (by omega) htk.le hL hr
    (by rwa [Fintype.card_fin]) hm hg) ?_
  have size : (1-δ)*(n : ℝ≥0) ≤ t := ht ▸ Nat.le_ceil _
  have lower := ManyHeadLocatorMass.grid_mass D δ hr hk htk (by omega) pack size
  rw [show n-t+1=e+1 by omega] at lower
  have allKeys : r*(e+1) ≤ AveragedPencilProjection.retained (r*(e+1)) (Fintype.card F) := by
    unfold AveragedPencilProjection.retained
    rw [Nat.div_eq_of_lt (Nat.lt_succ_of_le room),Nat.sub_zero]
    exact le_max_left ..
  exact (ENNReal.div_le_div_right (by exact_mod_cast allKeys) _).trans lower

/-- In the disjoint-block packing range, the smooth-domain all-fresh construction
attains the entire multiple-line upper bound over fields of linear size. -/
theorem epsMCA_eq {F : Type} [Field F] [Fintype F] [DecidableEq F] {n k t e L r : ℕ} [NeZero n]
    (D : Fin n ↪ F) [ReedSolomon.Smooth D] (δ : ℝ≥0) (b : Fin (r+1) ↪ F)
    (he : e+t=n) (hk : 2≤k) (htk : k<t) (hL : 2≤L) (hr : 1≤r)
    (ht : ⌈(1-δ)*(n : ℝ≥0)⌉₊ = t)
    (hm : (e+2)*k*n^2+(L+2)*n^3 < (e+2)*t^3)
    (hg : (n+(r.choose 2+r)*k)*L+r*n < (r+1)*t*L)
    (pack : k-2+r*(t-1-(k-2)) ≤ n)
    (room : ((CosetHeadSlopes.edges (r+1)).card+
      (CosetHeadSlopes.edges (r+1)).offDiag.card*n)*r < Fintype.card F) :
    epsMCA (F := F) (ReedSolomon.code D k : Set (Fin n → F)) δ =
      ((r*(e+1) : ℕ) : ℝ≥0∞)/(Fintype.card F : ℝ≥0∞) := by
  apply le_antisymm (epsMCA_le D δ (Fintype.card_fin _) he (by omega) htk.le hL hr
    (by rwa [Fintype.card_fin]) hm hg)
  obtain ⟨d,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  have core : k-2+(t-1-(k-2))=t-1 := by omega
  have size : (1-δ)*(n : ℝ≥0) ≤ ((k-2+(t-1-(k-2))+1 : ℕ) : ℝ≥0) := by
    rw [core,show t-1+1=t by omega,← ht]
    exact Nat.le_ceil _
  have lower := SmoothManyHeadMass.all_fresh (k:=k) (h:=k-2) (r:=t-1-(k-2)) D δ b pack
    (by omega) (by omega) size room
  rwa [core,show n-(t-1)=e+1 by omega] at lower

#print axioms family_card_le
#print axioms count_le
#print axioms epsMCA_le
#print axioms epsMCA_eq
#print axioms epsMCA_eq_of_pair_supply

end ProximityGap.GeneralManyLineSafety
