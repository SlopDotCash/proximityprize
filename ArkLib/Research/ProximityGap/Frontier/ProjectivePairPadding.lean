/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.ProjectivePairCompletions
import ArkLib.Research.ProximityGap.Frontier.LocatorShortening
import ArkLib.Research.ProximityGap.Frontier.OddRedundancySquareLift

/-! # Projective pairs survive changes to an evaluation domain -/

namespace ProximityGap.ProjectivePairPadding
open Finset DimensionThreeInvolution ProjectivePairCompletions MCAThresholdLedger ArkLib.ProximityGap.Frontier
open scoped NNReal ENNReal
variable {F : Type} [Field F] [DecidableEq F] [Fintype F]

private theorem select_pairs {α : Type} [DecidableEq α] (f : α → α) (m : ℕ)
    (S : Finset α) (room : 2*m≤S.card)
    (orbit : ∀ i∈S, f i∈S ∧ f i≠i ∧ f (f i)=i) :
    ∃ W⊆S, W.card=2*m ∧ ∀ i∈W, f i∈W := by
  induction m generalizing S with
  | zero => exact ⟨∅,empty_subset _,by simp,by simp⟩
  | succ m ih =>
    obtain ⟨x,hx⟩ := card_pos.mp (by omega : 0<S.card)
    obtain ⟨fx,neq,inv⟩ := orbit x hx
    let U := (S.erase x).erase (f x)
    have hU : U.card=S.card-2 := by
      rw [show U=(S.erase x).erase (f x) from rfl,card_erase_of_mem (mem_erase.mpr ⟨neq,fx⟩),card_erase_of_mem hx]
      omega
    have keep {z : α} (hz : z∈U) : f z∈U ∧ f z≠z ∧ f (f z)=z := by
      obtain ⟨nz,hz'⟩ := mem_erase.mp hz
      obtain ⟨nz',mem⟩ := mem_erase.mp hz'
      obtain ⟨fz,neq',inv'⟩ := orbit z mem
      exact ⟨mem_erase.mpr ⟨fun h => nz' (inv'.symm.trans ((congrArg f h).trans inv)),
        mem_erase.mpr ⟨fun h => nz (inv'.symm.trans (congrArg f h)),fz⟩⟩,neq',inv'⟩
    obtain ⟨W,hWU,cW,closed⟩ := ih U (by omega) fun _ hi => keep hi
    have nx : x∉W := fun hi => (mem_erase.mp (mem_erase.mp (hWU hi)).2).1 rfl
    have nf : f x∉W := fun hi => (mem_erase.mp (hWU hi)).1 rfl
    refine ⟨insert x (insert (f x) W),?_,?_,?_⟩
    · exact insert_subset hx (insert_subset fx (hWU.trans ((erase_subset ..).trans (erase_subset ..))))
    · rw [card_insert_of_notMem (by simp [nx,neq.symm]),card_insert_of_notMem nf,cW];omega
    · intro z hz
      rcases mem_insert.mp hz with rfl|hz
      · simp
      rcases mem_insert.mp hz with rfl|hz
      · simp [inv]
      exact mem_insert_of_mem (mem_insert_of_mem (closed z hz))

omit [Fintype F] in
/-- From an involutive set of sites, an arbitrary replacement of t sites
preserves at least |S|−2t paired sites, from which any even subsize is available. -/
theorem surviving {S R : Finset F} (paired : PairedSet S) (m : ℕ)
    (room : 2*m+2*(S\R).card≤S.card) :
    ∃ W⊆R, W.card=2*m ∧ PairedSet W := by
  classical
  obtain ⟨a,b,c,valid,given⟩ := paired
  let f := fun i : F => -(b*i+c)/(a*i+b)
  have unique {i j : F} (eq : a*i*j+b*(i+j)+c=0) : f i=j := by
    have den : a*i+b≠0 := by intro zero;exact valid (by linear_combination a*eq-(a*j+b)*zero)
    exact (div_eq_iff den).mpr (by linear_combination -eq)
  have orbit {i : F} (hi : i∈S) : f i∈S ∧ f i≠i ∧ f (f i)=i ∧ a*i*(f i)+b*(i+f i)+c=0 := by
    obtain ⟨j,hj,ij,rel⟩ := given i hi
    rw [unique rel]
    exact ⟨hj,ij.symm,unique (by linear_combination rel),rel⟩
  let L := S\R
  let U := S\(L∪L.image f)
  have count : 2*m≤U.card := by
    have union := card_union_le L (L.image f)
    have img : (L.image f).card≤L.card := card_image_le
    have lower := le_card_sdiff (L∪L.image f) S
    change 2*m+2*L.card≤S.card at room
    change 2*m≤(S\(L∪L.image f)).card
    omega
  have inR : U⊆R := by
    intro i hi
    obtain ⟨hS,out⟩ := mem_sdiff.mp hi
    by_contra bad
    exact out (mem_union_left _ (mem_sdiff.mpr ⟨hS,bad⟩))
  have closed (i : F) (hi : i∈U) : f i∈U ∧ f i≠i ∧ f (f i)=i := by
    obtain ⟨hS,out⟩ := mem_sdiff.mp hi
    obtain ⟨fi,neq,inv,_⟩ := orbit hS
    refine ⟨mem_sdiff.mpr ⟨fi,?_⟩,neq,inv⟩
    intro bad
    rcases mem_union.mp bad with miss|img
    · exact out (mem_union_right _ (mem_image.mpr ⟨f i,miss,inv⟩))
    obtain ⟨j,hj,eq⟩ := mem_image.mp img
    have ji : j=i := (orbit (mem_sdiff.mp hj).1).2.2.1.symm.trans ((congrArg f eq).trans inv)
    exact out (mem_union_left _ (ji ▸ hj))
  obtain ⟨W,hWU,size,hf⟩ := select_pairs f m U count closed
  refine ⟨W,hWU.trans inR,size,a,b,c,valid,?_⟩
  intro i hi
  have hiS := (mem_sdiff.mp (hWU hi)).1
  exact ⟨f i,hf i hi,(orbit hiS).2.1.symm,(orbit hiS).2.2.2⟩

/-- A domain containing 2h+2 paired sites attains the additional bad scalar
at dimension k. The k−3 other sites are the roots of the padding locator. -/
theorem padded_lower {n k h : ℕ} [NeZero n] (D : Fin n ↪ F) (length : n=k+2*h-1)
    (large : 3≤h) (odd : h%2=1) (hk : 3≤k) (W : Finset F)
    (inside : W⊆univ.image D) (size : W.card=2*(h+1)) (paired : PairedSet W) :
    ((h+1:ℕ):ℝ≥0∞)/Fintype.card F ≤ epsMCA (F:=F) (ReedSolomon.code D k : Set (Fin n → F))
      (((h-1:ℕ):ℝ≥0)/n) := by
  classical
  let E := (W.equivFinOfCardEq size).symm.toEmbedding.trans (Function.Embedding.subtype (·∈W))
  have image : univ.image E=W := by
    ext x
    constructor
    · rintro hx
      obtain ⟨i,_,rfl⟩ := mem_image.mp hx
      exact ((W.equivFinOfCardEq size).symm i).property
    · intro hx
      let w : W := ⟨x,hx⟩
      exact mem_image.mpr ⟨W.equivFinOfCardEq size w,mem_univ _,by simp [E,w]⟩
  have lift (i : Fin (2*(h+1))) : ∃ j, D j=E i := by
    have hi := inside (image ▸ mem_image_of_mem E (mem_univ i))
    simpa only [mem_image,mem_univ,true_and] using hi
  let old : Fin (2*(h+1)) ↪ Fin n := ⟨fun i => (lift i).choose,fun _ _ e => E.injective
    ((lift _).choose_spec.symm.trans ((congrArg D e).trans (lift _).choose_spec))⟩
  have same : old.trans D=E := by ext i;exact (lift i).choose_spec
  have inv := (reflects_iff E).2 (image ▸ paired)
  have base := DimensionThreePairCriterion.sufficient E (h:=h) (by simp;omega) large odd
    (DimensionThreeInvolution.sufficient E (by simp;omega) inv)
  have transfer := LocatorShortening.eps_le_extension (k:=3) old D (by decide) (h-1)
  rw [same,show 3+(n-2*(h+1))=k by omega] at transfer
  apply le_trans _ transfer
  simpa only [Fintype.card_fin] using base

/-- Robustness at arbitrary dimension. Any domain obtained from a fully
paired n-site domain by replacing ≤(k−3)/2 sites still attains h+1 labels. -/
theorem robust_lower {n k h : ℕ} [NeZero n] (D : Fin n ↪ F) (length : n=k+2*h-1)
    (large : 3≤h) (odd : h%2=1) (hk : 3≤k) (S : Finset F) (card : S.card=n)
    (paired : PairedSet S) (edits : 2*(S\univ.image D).card≤k-3) :
    ((h+1:ℕ):ℝ≥0∞)/Fintype.card F ≤ epsMCA (F:=F) (ReedSolomon.code D k : Set (Fin n → F))
      (((h-1:ℕ):ℝ≥0)/n) := by
  obtain ⟨W,inside,size,yes⟩ := surviving paired (h+1) (by omega :
    2*(h+1)+2*(S\univ.image D).card≤S.card)
  exact padded_lower D length large odd hk W inside size yes

omit [Fintype F] in
/-- Every even smooth domain is partitioned by its nontrivial square fibers. -/
theorem smooth_paired {n : ℕ} (E : Fin n ↪ F) [ReedSolomon.Smooth E] (even : n%2=0) :
    PairedSet (univ.image E) := by
  classical
  obtain ⟨V,_,on,fib,_⟩ := CodingTheory.AdditiveSetListDecoding.Smooth.exists_pow_projection_structure
    E (by simp;omega : Fintype.card (Fin n)=2*(n/2))
  apply (reflects_iff E).1
  refine ⟨0,1,0,by simp,?_⟩
  intro i
  let G := univ.filter fun j => E j^2=E i^2
  have size : G.card=2 := fib _ (on i)
  obtain ⟨z,hz,w,hw,zw⟩ := one_lt_card.mp (by omega : 1<G.card)
  obtain ⟨j,hj,ij⟩ : ∃ j∈G, i≠j := by
    by_cases iz : i=z
    · exact ⟨w,hw,iz ▸ zw⟩
    · exact ⟨z,hz,iz⟩
  have neg := (sq_eq_sq_iff_eq_or_eq_neg.mp (mem_filter.mp hj).2).resolve_left (E.injective.ne ij.symm)
  exact ⟨j,ij,by simp [neg]⟩

/-- Every supplied domain within the stated number of replacements of a
smooth coset has the same sharp exceptional mass. -/
theorem near_smooth_mass {n k h : ℕ} [NeZero n] (D E : Fin n ↪ F) [ReedSolomon.Smooth E]
    (length : n=k+2*h-1) (large : 4≤h) (odd : h%2=1) (hk : 3≤k) (rate : 3*k≤n)
    (even : n%2=0) (edits : 2*(univ.image E\univ.image D).card≤k-3) :
    epsMCA (F:=F) (ReedSolomon.code D k : Set (Fin n → F)) (((h-1:ℕ):ℝ≥0)/n)=
      ((h+1:ℕ):ℝ≥0∞)/Fintype.card F := by
  apply le_antisymm
  · simpa only [odd] using OddRedundancyApolar.endpoint_upper D hk rate length large
  · apply robust_lower D length (by omega) odd hk (univ.image E) _ (smooth_paired E even) edits
    rw [card_image_of_injective _ E.injective,card_univ,Fintype.card_fin]

/-- The same replacements preserve the real threshold at the exceptional
budget h, simultaneously for each positive interleaving width. -/
theorem near_smooth_threshold {n k h Q : ℕ} [NeZero n] (D E : Fin n ↪ F) [ReedSolomon.Smooth E]
    (length : n=k+2*h-1) (large : 4≤h) (odd : h%2=1) (hk : 3≤k) (rate : 3*k≤n)
    (even : n%2=0) (edits : 2*(univ.image E\univ.image D).card≤k-3)
    (positive : 0<Q) (budget : Fintype.card F/Q=h) (width : ℕ) [NeZero width] :
    let C := (ReedSolomon.code D k : Set (Fin n → F)) ^⋈ (Fin width)
    let r := ((h-1:ℕ):ℝ≥0)/n
    mcaDeltaStar (F:=F) C (1/(Q:ℝ≥0∞))=r ∧ ∀ δ, epsMCA (F:=F) C δ≤1/(Q:ℝ≥0∞) ↔ δ<r :=
  OddRedundancyApolar.exceptional_of_lower D hk rate length large positive budget
    (near_smooth_mass D E length large odd hk rate even edits).ge width

end ProximityGap.ProjectivePairPadding
#print axioms ProximityGap.ProjectivePairPadding.surviving
#print axioms ProximityGap.ProjectivePairPadding.robust_lower

#print axioms ProximityGap.ProjectivePairPadding.near_smooth_mass

#print axioms ProximityGap.ProjectivePairPadding.near_smooth_threshold
