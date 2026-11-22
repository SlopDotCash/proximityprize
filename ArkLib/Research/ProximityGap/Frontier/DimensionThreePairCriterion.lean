/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.DimensionThreeBalancedCores

/-! # A domain-only pairing criterion at the dimension-three odd predecessor -/

namespace ProximityGap.DimensionThreePairCriterion
open Finset Polynomial Code ArkLib.ProximityGap.Frontier
open HalfPredecessorBadEventRichPointBridge HalfPredecessorLineCoreGeometry
open HalfPredecessorSecantLines HalfPredecessorLargeCoreCollapse
open scoped NNReal ENNReal

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I] [Field F] [Fintype F] [DecidableEq F]

/-- The finite sites with a well-defined rational value z. -/
def fiber (D : I ↪ F) (a b : F[X]) (z : F) : Finset I :=
  univ.filter fun i => b.eval (D i) ≠ 0 ∧ a.eval (D i)=z*b.eval (D i)

/-- At least h+1 different two-site fibers of one ratio of quadratics. -/
def Paired (D : I ↪ F) (h : ℕ) : Prop :=
  ∃ a b : F[X], a.natDegree<3 ∧ b.natDegree<3 ∧
    ∃ G : Finset F, h<G.card ∧ ∀ z∈G, 2≤(fiber D a b z).card

private theorem fresh_pair {D : I ↪ F} {h : ℕ} {δ : ℝ≥0} {u : WordStack F (Fin 2) I}
    (fam : BadScalarRichPointFamily D 3 δ u) (l m : LineParameter F)
    (ht : ⌈(1-δ)*(Fintype.card I:ℝ≥0)⌉₊=h+3) {x : F} (on : x∈pointsOn fam l)
    (size : (jointCore D (u 0) (u 1) l.1 l.2).card=h+1)
    (opp : jointCore D (u 0) (u 1) m.1 m.2=(jointCore D (u 0) (u 1) l.1 l.2)ᶜ) :
    2≤(fiber D (m.1-l.1) (l.2-m.2) x).card := by
  let C := jointCore D (u 0) (u 1) l.1 l.2
  let P := fullAgreement D (u 0) (u 1) x (fam.q x)
  obtain ⟨xG,qx⟩ := (mem_pointsOn_iff ..).mp on
  have b := fam.threshold_le x xG
  rw [ht] at b
  change h+3≤P.card at b
  have sum := card_sdiff_add_card_inter P C
  have inter : (P∩C).card≤C.card := card_le_card inter_subset_right
  change C.card=h+1 at size
  have count : 2≤(P \ C).card := by omega
  apply count.trans
  apply card_le_card
  intro i hi
  obtain ⟨pi,ci⟩ := mem_sdiff.mp hi
  have mi : i∈jointCore D (u 0) (u 1) m.1 m.2 := opp ▸ mem_compl.mpr ci
  obtain ⟨m0,m1⟩ := (mem_filter.mp mi).2
  have p := (mem_filter.mp pi).2
  change (fam.q x).eval (D i)=u 0 i+x*u 1 i at p
  rw [qx,eval_add,eval_mul,eval_C] at p
  apply mem_filter.mpr
  refine ⟨mem_univ _,?_,?_⟩
  · rw [eval_sub,sub_ne_zero]
    intro fe
    apply ci
    apply mem_filter.mpr
    refine ⟨mem_univ _,?_,fe.trans m1⟩
    rw [fe,m1] at p
    exact add_right_cancel p
  · simp only [eval_sub,m0,m1]
    linear_combination -p

/-- Every over-budget received stack forces rationally paired sites on the
prescribed dimension-three evaluation domain. -/
theorem necessary {D : I ↪ F} {h : ℕ} {δ : ℝ≥0} {u : WordStack F (Fin 2) I}
    (fam : BadScalarRichPointFamily D 3 δ u) (large : 3≤h) (hn : Fintype.card I=2*h+2)
    (ht : ⌈(1-δ)*(Fintype.card I:ℝ≥0)⌉₊=h+3) (exceeds : h<fam.G.card) : Paired D h := by
  classical
  obtain ⟨l,hl,m,hm,size,opposite,_,_,others⟩ := DimensionThreeBalancedCores.balanced fam large hn ht exceeds
  have dl := lineParameter_degree_lt fam hl
  have dm := lineParameter_degree_lt fam hm
  refine ⟨m.1-l.1,l.2-m.2,natDegree_sub_le .. |>.trans_lt (max_lt dm.1 dl.1),
    natDegree_sub_le .. |>.trans_lt (max_lt dl.2 dm.2),fam.G,exceeds,?_⟩
  intro x hx
  by_cases on : x∈pointsOn fam l
  · exact fresh_pair fam l m ht on size opposite
  have outside : x∈outsideLine fam l := (mem_outsideLine_iff ..).mpr ⟨hx,fun he =>
    on ((mem_pointsOn_iff ..).mpr ⟨hx,he⟩)⟩
  have right := fresh_pair fam m l ht (others x outside)
    (by rw [opposite,card_compl,size,hn];omega) (by rw [opposite,compl_compl])
  apply right.trans_eq
  apply congrArg Finset.card
  ext i
  simp only [fiber,mem_filter,mem_univ,true_and,eval_sub,sub_ne_zero]
  constructor <;> rintro ⟨neq,eq⟩ <;> exact ⟨Ne.symm neq,by linear_combination -eq⟩

omit [Fintype F] [DecidableEq F] in
private theorem event (D : I ↪ F) (U T : Finset I) {h : ℕ} (hn : Fintype.card I=2*h+2)
    (large : 3≤h) (uc : h+1≤U.card) (tc : 2≤T.card) (dis : Disjoint U T)
    (c d u v : I → F) (hc : c∈ReedSolomon.code D 3) (hd : d∈ReedSolomon.code D 3)
    (base : ∀ i∈U, c i=u i ∧ d i=v i) (z : F)
    (matchZ : ∀ i∈T, c i+z*d i=u i+z*v i) (bad : ∀ i∈T, d i≠v i) :
    mcaEvent (F:=F) (ReedSolomon.code D 3 : Set (I → F)) (((h-1:ℕ):ℝ≥0)/Fintype.card I) u v z := by
  have nz : (Fintype.card I:ℝ≥0)≠0 := by exact_mod_cast Fintype.card_ne_zero
  refine ⟨U∪T,?_,⟨c+z • d,(ReedSolomon.code D 3).add_mem hc ((ReedSolomon.code D 3).smul_mem z hd),?_⟩,?_⟩
  · rw [card_union_of_disjoint dis,tsub_mul,one_mul,div_mul_cancel₀ _ nz,← Nat.cast_tsub]
    exact_mod_cast (by omega : Fintype.card I-(h-1)≤U.card+T.card)
  · intro i hi
    change c i+z*d i=u i+z*v i
    rcases mem_union.mp hi with hi|hi
    · rw [(base i hi).1,(base i hi).2]
    · exact matchZ i hi
  · rintro ⟨_,_,w,hw,h⟩
    have eq : w=d := ReedSolomon.eq_of_agree_of_card_le hw hd (by omega : 3≤U.card)
      fun j hj => ((h j (mem_union_left _ hj)).2).trans (base j hj).2.symm
    obtain ⟨i,hi⟩ := card_pos.mp (by omega : 0<T.card)
    exact bad i hi (eq ▸ (h i (mem_union_right _ hi)).2)

/-- An exactly balanced partition of the rational fibers constructs a
received stack with at least h+1 genuinely bad scalars. -/
theorem sufficient (D : I ↪ F) {h : ℕ} (length : Fintype.card I=2*h+2)
    (large : 3≤h) (odd : h%2=1) (paired : Paired D h) :
    ((h+1:ℕ):ℝ≥0∞)/Fintype.card F ≤ epsMCA (F:=F) (ReedSolomon.code D 3 : Set (I → F))
      (((h-1:ℕ):ℝ≥0)/Fintype.card I) := by
  classical
  obtain ⟨a,b,da,db,G,big,fib⟩ := paired
  obtain ⟨H,hHG,hH⟩ := exists_subset_card_eq (by omega : h+1≤G.card)
  obtain ⟨L,hLH,hL⟩ := exists_subset_card_eq (by omega : (h+1)/2≤H.card)
  let R := H \ L
  have hR : R.card=(h+1)/2 := by dsimp [R];rw [card_sdiff_of_subset hLH,hH,hL];omega
  let T (S : Finset F) := S.biUnion (fiber D a b)
  have disjoint {x y : F} (xy : x≠y) : Disjoint (fiber D a b x) (fiber D a b y) := by
    apply disjoint_left.mpr
    intro i hi hy
    obtain ⟨nz,hxi⟩ := (mem_filter.mp hi).2
    exact xy (mul_right_cancel₀ nz (hxi.symm.trans (mem_filter.mp hy).2.2))
  have size (S : Finset F) (hs : S⊆G) : S.card*2≤(T S).card := by
    dsimp only [T]
    rw [card_biUnion (fun _ _ _ _ ne => disjoint ne)]
    simpa using sum_le_sum (s:=S) (fun z hz => fib z (hs hz))
  have lsize : h+1≤(T L).card := by have lo := size L (hLH.trans hHG);omega
  have rsize : h+1≤(T R).card := by have lo := size R (sdiff_subset.trans hHG);omega
  have split : Disjoint (T L) (T R) := by
    apply disjoint_left.mpr
    intro i hl hr
    obtain ⟨z,hz,iz⟩ := mem_biUnion.mp hl
    obtain ⟨z',hz',iz'⟩ := mem_biUnion.mp hr
    have ne : z≠z' := fun he => (mem_sdiff.mp hz').2 (he ▸ hz)
    exact disjoint_left.mp (disjoint ne) iz iz'
  have notL {i : I} (hi : i∈T R) : i∉T L := fun hl => disjoint_left.mp split hl hi
  let aw (i : I) := a.eval (D i)
  let bw (i : I) := -b.eval (D i)
  let u (i : I) := if i∈T L then aw i else 0
  let v (i : I) := if i∈T L then bw i else 0
  have ac : aw∈ReedSolomon.code D 3 := ReedSolomon.mem_code_iff_eval_of_ne_zero.mpr ⟨a,da,fun _ => rfl⟩
  have bc : bw∈ReedSolomon.code D 3 := ReedSolomon.mem_code_iff_eval_of_ne_zero.mpr ⟨-b,by simpa using db,fun i => by simp [bw]⟩
  have zero {z : F} {i : I} (hi : i∈fiber D a b z) : aw i+z*bw i=0 ∧ bw i≠0 := by
    obtain ⟨nz,eq⟩ := (mem_filter.mp hi).2
    change a.eval (D i)+z*(-b.eval (D i))=0 ∧ -b.eval (D i)≠0
    simp [eq,nz]
  have enough := MCAWitnessSpread.epsMCA_ge_card_div_of_mcaEvent_set
    (ReedSolomon.code D 3 : Set (I → F)) (((h-1:ℕ):ℝ≥0)/Fintype.card I) ![u,v] H (by
      intro z hz
      by_cases lz : z∈L
      · have sub : fiber D a b z ⊆ T L := subset_biUnion_of_mem _ lz
        apply event D (T R) (fiber D a b z) length large rsize (fib z (hHG hz))
          (split.symm.mono_right sub) 0 0 u v (ReedSolomon.code D 3).zero_mem (ReedSolomon.code D 3).zero_mem _ z
        · intro i hi; simp [u,v,sub hi,(zero hi).1]
        · intro i hi; simp [v,sub hi,(zero hi).2.symm]
        · intro i hi; simp [u,v,notL hi]
      · have rz : z∈R := mem_sdiff.mpr ⟨hz,lz⟩
        have sub : fiber D a b z ⊆ T R := subset_biUnion_of_mem _ rz
        apply event D (T L) (fiber D a b z) length large lsize (fib z (hHG hz))
          (split.mono_right sub) aw bw u v ac bc _ z
        · intro i hi; simp [u,v,notL (sub hi),(zero hi).1]
        · intro i hi; simp [v,notL (sub hi),(zero hi).2]
        · intro i hi; simp [u,v,hi])
  simpa only [hH] using enough

/-- At the odd exceptional budget the rational pairing criterion determines
the exact MCA numerator on every prescribed evaluation domain. -/
theorem mass {n h : ℕ} [NeZero n] (D : Fin n ↪ F) (length : n=2*h+2) (large : 4≤h)
    (odd : h%2=1) [Decidable (Paired D h)] :
    epsMCA (F:=F) (ReedSolomon.code D 3 : Set (Fin n → F)) (((h-1:ℕ):ℝ≥0)/n) =
      ((if Paired D h then h+1 else h:ℕ):ℝ≥0∞)/Fintype.card F := by
  classical
  by_cases yes : Paired D h
  · rw [ite_eq_left yes]
    apply le_antisymm
    · have up := OddRedundancyApolar.endpoint_upper D (by decide : 3≤3) (by omega) (by omega : n=3+2*h-1) large
      rwa [odd] at up
    · simpa only [Fintype.card_fin] using sufficient D (by simpa using length) (by omega) odd yes
  · rw [ite_eq_right yes]
    apply le_antisymm
    · apply epsMCA_le_of_badCount_le
      intro u
      let fam := canonicalBadScalarRichPointFamily D (((h-1:ℕ):ℝ≥0)/n) u (by decide : 1≤3)
      change fam.G.card≤h
      by_contra! excess
      apply yes (necessary fam (by omega) (by simpa using length) _ excess)
      have nz : (n:ℝ≥0) ≠ 0 := by exact_mod_cast NeZero.ne n
      rw [Fintype.card_fin,tsub_mul,one_mul,div_mul_cancel₀ _ nz,←Nat.cast_tsub,Nat.ceil_natCast]
      omega
    · have lower := OddRedundancyApolar.spike_lower (e:=h-1) D (by decide : 3≤3) (by omega : n=3+2*h-1) large le_rfl
      simpa only [show h-1+1=h by omega] using lower

end ProximityGap.DimensionThreePairCriterion
#print axioms ProximityGap.DimensionThreePairCriterion.necessary
#print axioms ProximityGap.DimensionThreePairCriterion.mass
