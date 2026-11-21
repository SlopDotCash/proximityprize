/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic
import ArkLib.Research.ProximityGap.Frontier.ApolarMovingCount

/-! # A support obstruction for rate-half secant and circuit counts

The sets in this file are abstract coordinate supports. They do not specify
decoding polynomials, received words, or bad scalars. -/
set_option autoImplicit false
namespace ProximityGap.SupportObstruction
open Finset
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

private abbrev V (K : Type) := Fin 14 → K
private abbrev U (K : Type) := V K × K

private def form (a x : V K) := ∑ i, a i*x i

private theorem fiber_cap (a : V K) (j : Fin 14) (hj : a j ≠ 0) (b : K) :
    (univ.filter (fun x : V K => form a x = b)).card ≤ Fintype.card K^13 := by
  classical
  let R := (univ : Finset (Fin 14)).erase j
  let proj := fun (x : V K) (i : R) => x i
  have hi : Set.InjOn proj (↑(univ.filter (fun x : V K => form a x = b)) : Set (V K)) := by
    intro x hx y hy he
    have hsum : (∑ i ∈ R, a i*x i) = ∑ i ∈ R, a i*y i := by
      exact sum_congr rfl (fun i hi => congrArg (a i * ·) (congrFun he ⟨i,hi⟩))
    have hall := (mem_filter.mp hx).2.trans (mem_filter.mp hy).2.symm
    unfold form at hall
    rw [← add_sum_erase _ _ (mem_univ j), ← add_sum_erase _ (fun i => a i*y i) (mem_univ j)] at hall
    change a j*x j+ (∑ i ∈ R, a i*x i) = a j*y j+(∑ i ∈ R, a i*y i) at hall
    rw [hsum] at hall
    funext i
    by_cases h : i=j
    · subst i
      exact mul_left_cancel₀ hj (add_right_cancel hall)
    · exact congrFun he ⟨i,mem_erase.mpr ⟨h,mem_univ _⟩⟩
  have h := card_le_card_of_injOn proj (t := univ) (fun _ _ => mem_univ _) hi
  simpa [R, Fintype.card_fun] using h

private def graphSet (f : V K → K) : Finset (U K) :=
  univ.map ⟨fun x => (x,f x), fun _ _ h => congrArg Prod.fst h⟩

omit [Field K] [DecidableEq K] in
private theorem mem_graph {f : V K → K} {p : U K} :
    p ∈ graphSet f ↔ p.2 = f p.1 := by
  constructor
  · intro h
    obtain ⟨x,_,rfl⟩ := mem_map.mp h
    rfl
  · intro he
    refine mem_map.mpr ⟨p.1,mem_univ _,?_⟩
    exact Prod.ext rfl he.symm

private def fn (s : U K) (x : V K) := form s.1 x+s.2

private theorem graph_cap (H : Fintype.card K=4) (a b : U K) (hne : a ≠ b) :
    (graphSet (fn a) ∩ graphSet (fn b)).card ≤ 4^13 := by
  classical
  by_cases hs : a.1=b.1
  · have hz : graphSet (fn a) ∩ graphSet (fn b) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro p hp
      obtain ⟨ha,hb⟩ := mem_inter.mp hp
      have eq := (mem_graph.mp ha).symm.trans (mem_graph.mp hb)
      simp only [fn, hs, add_right_inj] at eq
      exact hne (Prod.ext hs eq)
    simp [hz]
  · obtain ⟨j,hj⟩ := Function.ne_iff.mp hs
    let E := univ.filter (fun x : V K => form (a.1-b.1) x=b.2-a.2)
    have h := card_le_card_of_injOn (fun p : U K => p.1)
      (s := graphSet (fn a) ∩ graphSet (fn b)) (t := E) (by
        intro p hp
        obtain ⟨ha,hb⟩ := mem_inter.mp hp
        have eq := (mem_graph.mp ha).symm.trans (mem_graph.mp hb)
        simp only [fn,form] at eq
        apply mem_filter.mpr
        refine ⟨mem_univ _, ?_⟩
        simp only [form,Pi.sub_apply,sub_mul,sum_sub_distrib]
        linear_combination eq) (by
        intro p hp v hv he
        exact Prod.ext he ((mem_graph.mp (mem_inter.mp hp).1).trans
          ((congrArg (fn a) he).trans (mem_graph.mp (mem_inter.mp hv).1).symm)))
    exact h.trans ((fiber_cap (a.1-b.1) j (sub_ne_zero.mpr hj) _).trans_eq (by rw [H]))

open Classical in
/-- An explicit family of n+1 distinct subsets of an n=2^30 coordinate set,
each of size n/4−1 and with all pair intersections at most n/16. -/
theorem error_family : ∃ (I J : Type) (_ : Fintype I) (_ : Fintype J) (E : J → Finset I),
    Fintype.card I = 1073741824 ∧ Fintype.card J = 1073741825 ∧
    (∀ a, (E a).card=268435455) ∧
    ∀ a b, a≠b → (E a ∩ E b).card ≤ 67108864 := by
  classical
  let K := GaloisField 2 2
  let : Fintype K := Fintype.ofFinite K
  have H : Fintype.card K=4 := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 2 (by decide : (2:ℕ) ≠ 0)
  have hV : Fintype.card (V K) = 4^14 := by simp [V,H]
  obtain ⟨W,_,hW⟩ := (univ : Finset (V K)).exists_subset_card_eq (by
    rw [card_univ,hV]; decide : 4^13 ≤ (univ : Finset (V K)).card)
  let raw (j : Option (U K)) : Finset (U K) := j.elim (W ×ˢ univ) (fun s => graphSet (fn s))
  have hsize (j : Option (U K)) : (raw j).card=268435456 := by
    cases j with
    | none => simp [raw,card_product,hW,H]
    | some a => simp [raw,graphSet,hV]
  have vert (a : U K) : ((W ×ˢ univ) ∩ graphSet (fn a)).card ≤ 67108864 := by
    have h := card_le_card_of_injOn (fun p : U K => p.1)
      (s := (W ×ˢ univ) ∩ graphSet (fn a)) (t := W)
      (fun p hp => (mem_product.mp (mem_inter.mp hp).1).1) (by
        intro p hp v hv he
        exact Prod.ext he ((mem_graph.mp (mem_inter.mp hp).2).trans
          ((congrArg (fn a) he).trans (mem_graph.mp (mem_inter.mp hv).2).symm)))
    exact h.trans_eq hW
  have cap (a b : Option (U K)) (hne : a≠b) : (raw a ∩ raw b).card ≤ 67108864 := by
    cases a <;> cases b
    · contradiction
    · exact vert _
    · rw [inter_comm]; exact vert _
    · exact graph_cap H _ _ (fun h => hne (congrArg some h))
  choose E hsub hsizeE using (fun a => (raw a).exists_subset_card_eq
    (show 268435455 ≤ (raw a).card by rw [hsize]; decide))
  refine ⟨U K,Option (U K),inferInstance,inferInstance,E,?_,?_,hsizeE,?_⟩
  · simp [U,hV,H]
  · simp [U,hV,H]
  · intro a b hne
    convert! (card_le_card (inter_subset_inter (hsub a) (hsub b))).trans (cap a b hne) using 1
    congr 3
    apply Subsingleton.elim

private theorem doubling (b k l : ℕ) (hbase : k < b) (hlim : b+l < 2*k) :
    2^l * b.choose (k+1) ≤ (b+l).choose (k+1) := by
  induction l with
  | zero => simp
  | succ l ih =>
    let n := b+l
    have hn : k+1 ≤ n := by dsimp [n]; omega
    have hhalf : n-(k+1)<n/2 := by dsimp [n]; omega
    have hh := Nat.choose_le_succ_of_lt_half_left hhalf
    rw [show n-(k+1)+1=n-k by omega,
      Nat.choose_symm (show k+1≤n by omega),Nat.choose_symm (show k≤n by omega)] at hh
    calc
      _ = 2*(2^l*b.choose (k+1)) := by rw [pow_succ]; ring
      _ ≤ 2*n.choose (k+1) := Nat.mul_le_mul_left _ (ih (by omega))
      _ ≤ (n+1).choose (k+1) := by rw [Nat.choose_succ_succ']; omega

open Classical in
private theorem private_circuits {I J : Type} [Fintype J] (A : J → Finset I) (a : J)
    (k b l : ℕ) (hbase : k < b) (hlim : b+l < 2*k)
    (hlen : b+l+1 ≤ (A a).card) (hM : Fintype.card J ≤ 2^l)
    (hcap : ∀ b' ≠ a, (A a ∩ A b').card ≤ b) :
    ((A a).card-1).choose k ≤ ((A a).powersetCard (k+1) |>.filter
      (fun T => ∀ j ≠ a, ¬ T ⊆ A j)).card := by
  classical
  let P := (A a).powersetCard (k+1)
  let S := P.filter (fun T => ∀ j ≠ a, ¬ T ⊆ A j)
  let U := (univ.erase a).biUnion (fun j => (A a ∩ A j).powersetCard (k+1))
  have hcover : P ⊆ S ∪ U := by
    intro T hT
    by_cases h : ∀ j ≠ a, ¬ T ⊆ A j
    · exact mem_union_left _ (mem_filter.mpr ⟨hT,h⟩)
    · push Not at h
      obtain ⟨j,hj,hin⟩ := h
      obtain ⟨hTa,ht⟩ := mem_powersetCard.mp hT
      exact mem_union_right _ (mem_biUnion.mpr ⟨j,mem_erase.mpr ⟨hj,mem_univ _⟩,
        mem_powersetCard.mpr ⟨subset_inter hTa hin, ht⟩⟩)
  have hU : U.card ≤ ((A a).card-1).choose (k+1) := by
    calc
      U.card ≤ ∑ j ∈ univ.erase a, ((A a ∩ A j).powersetCard (k+1)).card := card_biUnion_le
      _ ≤ ∑ _j ∈ univ.erase a, b.choose (k+1) := by
        apply sum_le_sum
        intro j hj
        rw [card_powersetCard]
        exact Nat.choose_le_choose _ (hcap j (mem_erase.mp hj).1)
      _ ≤ 2^l * b.choose (k+1) := by
        simp only [sum_const,smul_eq_mul]
        exact Nat.mul_le_mul_right _ ((card_le_univ _).trans hM)
      _ ≤ (b+l).choose (k+1) := doubling b k l hbase hlim
      _ ≤ _ := Nat.choose_le_choose _ (by omega)
  have cover := (card_le_card hcover).trans (card_union_le _ _)
  change ((A a).powersetCard (k+1)).card ≤ S.card+U.card at cover
  rw [card_powersetCard,show (A a).card=((A a).card-1)+1 by omega,Nat.choose_succ_succ'] at cover
  change _ ≤ S.card
  omega

open Classical in
/-- At the rate-half predecessor there are n+1 formal supports satisfying the
pair and triple overlap caps and the full lower bound on private circuits. -/
theorem support_obstruction : ∃ (I J : Type) (_ : Fintype I) (_ : Fintype J) (A : J → Finset I),
    Fintype.card I=1073741824 ∧ Fintype.card J=1073741825 ∧
    (∀ a, (A a).card=805306369) ∧
    (∀ a b, a≠b → (A a ∩ A b).card ≤ 603979778) ∧
    (∀ a b c, a≠b → a≠c → b≠c → ((A a ∩ A b) ∩ A c).card ≤ 469762051) ∧
    ∀ a, (805306368:ℕ).choose 536870912 ≤
      ((A a).powersetCard 536870913 |>.filter (fun T => ∀ j ≠ a, ¬ T ⊆ A j)).card := by
  classical
  obtain ⟨I,J,iI,iJ,E,hn,hm,hsize,hcap⟩ := error_family
  let A := fun a => (E a)ᶜ
  have size (a : J) : (A a).card=805306369 := by simp [A,card_compl,hn,hsize]
  have pair (a b : J) (hne : a≠b) : (A a ∩ A b).card≤603979778 := by
    rw [show A a∩A b=(E a∪E b)ᶜ by rw [compl_union],card_compl,hn]
    have h := card_union_add_card_inter (E a) (E b)
    have hi := hcap a b hne
    rw [hsize,hsize] at h
    omega
  refine ⟨I,J,iI,iJ,A,hn,hm,size,pair,?_,?_⟩
  · intro a b c hab hac hbc
    rw [show A a∩ A b ∩ A c=(E a∪E b∪E c)ᶜ by simp only [compl_union,A],card_compl,hn]
    have first := card_union_add_card_inter (E a) (E b)
    have both := card_union_add_card_inter (E a∪E b) (E c)
    have high : ((E a ∪ E b) ∩ E c).card ≤ (E a ∩ E c).card+(E b ∩ E c).card := by
      rw [union_inter_distrib_right]
      exact card_union_le _ _
    have h1 := hcap a b hab
    have h2 := hcap a c hac
    have h3 := hcap b c hbc
    rw [hsize,hsize] at first
    rw [hsize] at both
    omega
  · intro a
    have h := private_circuits A a 536870912 603979778 31 (by decide) (by decide)
      (by rw [size]; decide) (by rw [hm];decide) (fun b hne => pair a b hne.symm)
    simpa only [size] using h

open scoped NNReal
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge

open Classical in
/-- Actual polynomial pencils at this same predecessor have at most 357913942
bad scalars on any evaluation embedding. Together with the support construction,
this distinguishes the algebraic requirement from the support restrictions. -/
theorem actual_count_upper {I F : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype I] [Nonempty I] [DecidableEq I] (D : I ↪ F) (hn : Fintype.card I=1073741824)
    (u : Code.WordStack F (Fin 2) I) :
    (univ.filter (mcaEvent (F := F) (ReedSolomon.code D 536870912 : Set (I → F))
      ((268435455 : ℝ≥0)/1073741824) (u 0) (u 1))).card ≤ 357913942 := by
  classical
  let δ : ℝ≥0 := 268435455/1073741824
  let fam := canonicalBadScalarRichPointFamily (k := 536870912) D δ u (by decide)
  change fam.G.card ≤ 357913942
  have h := ApolarMovingCount.count_mca_family
    (algebraMap F (AlgebraicClosure F)) fam fam.G (Finset.Subset.rfl)
    (e := 268435455) (d := 536870911) (by decide) (by decide) (by decide) (by rw [hn]; decide)
    (by
      rw [hn, Nat.cast_ofNat, show (1-δ)*(1073741824 : ℝ≥0) = 805306369 by
        rw [tsub_mul, one_mul, show δ * 1073741824 = 268435455 by
          exact div_mul_cancel₀ _ (by norm_num)]
        rw [tsub_eq_iff_eq_add_of_le (by norm_num)]
        norm_num]
      norm_num)
  rcases h with h | h
  · omega
  · change (fam.G.card-1)*3 ≤ Fintype.card I at h
    omega

#print axioms actual_count_upper
#print axioms support_obstruction
#print axioms error_family
end ProximityGap.SupportObstruction
