/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SmoothFourHeadFibers
import ArkLib.Research.ProximityGap.Frontier.FourHeadWitness

/-! # Optimal three-head witnesses from pair and common root counts -/
namespace ArkLib.ProximityGap.Frontier.ThreeHeadRootScore
open Polynomial Finset Code _root_.ProximityGap
open SmoothFourHeadFibers SmoothFourHeadColored
open scoped NNReal ENNReal

private def project : Fin 4 → Fin 3 := ![0,1,2,0]

/-- A received pair realizes one label per ordinary site and three per hole.
Triple-coincidence sites may supply core agreements to all three heads. -/
theorem colored_mass {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I]
    [Field F] [Fintype F] [DecidableEq F] (dom : I ↪ F) (k : ℕ) (δ : ℝ≥0)
    (col : I → Fin 8) (f : Fin 3 → F[X]) (ord holes C : ℕ)
    (degree : ∀ i, 1+(f i).natDegree<k)
    (rank : k≤C) (support : (1-δ)*(Fintype.card I : ℝ≥0) ≤ ((C+1 : ℕ) : ℝ≥0))
    (ccard : ∀ i, (univ.filter fun x => col x ∈ coreClasses i).card=C)
    (ordinary : (univ.filter fun x => col x ∈ ordinaryClasses).card=ord)
    (special : (univ.filter fun x => col x=7).card=holes)
    (agree : ∀ x i, col x ∈ coreClasses i → (f i).eval (dom x)=(f (owner (col x))).eval (dom x))
    (misses : ∀ x, col x ∈ ordinaryClasses →
      (f (miss (col x))).eval (dom x) ≠ (f (owner (col x))).eval (dom x))
    (free : ∀ x, col x=7 → Function.Injective (fun i => (f i).eval (dom x)))
    (room : 4 < Fintype.card F) (fieldRoom : (ord+3*holes)^2 < Fintype.card F) :
    ((ord+3*holes : ℕ) : ℝ≥0∞)/Fintype.card F ≤
      epsMCA (F:=F) (ReedSolomon.code dom k : Set (I → F)) δ := by
  classical
  let select (s : Finset (Fin 8)) := univ.filter fun x => col x ∈ s
  let A : FourHeadWitness.CoreAllocation dom k δ := {
    head := fun h => f (project h)
    background := fun x => (f (owner (col x))).eval (dom x)
    ordinary := select ordinaryClasses
    special := univ.filter (fun x => col x=7)
    core := fun h => select (coreClasses (project h))
    degree_head := fun i => degree_le_natDegree.trans_lt (by
      have h : (f (project i)).natDegree < k := by have := degree (project i); omega
      exact_mod_cast h)
    degree_first := fun i => degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.mpr (by
      have h := natDegree_mul_le (p := (Polynomial.X : F[X])) (q := f (project i))
      rw [natDegree_X] at h
      exact h.trans_lt (degree _)))
    disjoint := disjoint_left.mpr (fun x ho hs => by
      have hm := (mem_filter.mp ho).2
      rw [(mem_filter.mp hs).2] at hm
      exact (by decide : (7:Fin 8)∉ordinaryClasses) hm)
    core_disjoint := fun h => disjoint_left.mpr (fun x hc hs => by
      have hm := (mem_filter.mp hc).2
      rw [(mem_filter.mp hs).2] at hm
      exact (by decide : ∀ i, (7:Fin 8)∉coreClasses i) _ hm)
    core_agrees := fun i x hx => agree x _ (mem_filter.mp hx).2
    core_rank := fun i => by rw [show (select _).card=C from ccard (project i)];exact rank
    core_size := fun i => by rw [show (select _).card=C from ccard (project i)];exact support
    ordinary_mismatch := fun x hx => by
      let j := miss (col x)
      have hj : project j.castSucc=j := (by decide : ∀ j:Fin 3, project j.castSucc=j) j
      refine ⟨j.castSucc,?_⟩
      rw [hj]
      exact misses x (mem_filter.mp hx).2 }
  have ocard : A.ordinary.card=ord := ordinary
  have spec : A.special.card=holes := special
  have roots (x : ↥A.special) : (univ.image fun h => (A.head h).eval (dom x.val)).card=3 := by
    let v (j : Fin 3) := (f j).eval (dom x.val)
    have inj : Function.Injective v := free x.val (mem_filter.mp x.property).2
    have eq : (univ.image (fun h => (A.head h).eval (dom x.val)))=univ.image v := by
      ext z
      simp only [mem_image,mem_univ,true_and]
      constructor
      · rintro ⟨h,rfl⟩; exact ⟨project h,rfl⟩
      · rintro ⟨j,rfl⟩
        exact ⟨j.castSucc,congrArg v ((by decide : ∀ t:Fin 3,project t.castSucc=t) j)⟩
    rw [eq,card_image_of_injective _ inj,card_univ,Fintype.card_fin]
  have count : A.count=ord+3*holes := by
    simp only [FourHeadWitness.CoreAllocation.count,ocard,roots,sum_const,card_univ,Fintype.card_coe,spec]
    change ord+holes*3=ord+3*holes
    rw [Nat.mul_comm holes]
  obtain ⟨u,G,hG,hit⟩ := FourHeadWitness.exists_bad_scalar_set_of_values A room (by rw [count];simpa [pow_two] using fieldRoom)
  have mass := MCAWitnessSpread.epsMCA_ge_card_div_of_mcaEvent_set _ _ u G hit
  rwa [hG,count] at mass


/-- Rows 0,1,2 hold the lone excluded index of a coincident pair. Row 3 is
the triple fiber and row 4 has three distinct values. -/
def rootBucket {F : Type} [Field F] [DecidableEq F] (p q : F) : Fin 5 :=
  if p=0 then (if q=0 then 3 else 2) else if q=0 then 1 else if p=q then 0 else 4

private def bucket8 : Fin 8 → Fin 5 := ![0,1,2,3,4,4,4,4]
private def refine (r : Fin 5) (z : Fin 4) : Fin 8 :=
  if r=4 then ![4,5,6,7] z else ![0,1,2,3,7] r

private theorem profile_refinement {I : Type} [Fintype I] (raw : I → Fin 5)
    (a b c r p₀ p₁ p₂ h : ℕ)
    (counts : ∀ i, (univ.filter fun x => raw x=i).card =
      (![a,b,c,r,p₀+p₁+p₂+h] : Fin 5 → ℕ) i) :
    ∃ col : I → Fin 8, (∀ x, bucket8 (col x)=raw x) ∧
      ∀ i, (univ.filter fun x => col x=i).card = (![a,b,c,r,p₀,p₁,p₂,h] : Fin 8 → ℕ) i := by
  classical
  let w : Fin 4 → ℕ := ![p₀,p₁,p₂,h]
  let s := univ.filter fun x => raw x=4
  obtain ⟨g,hg⟩ := partition_fibers s w (by
    change (univ.filter _).card=_
    rw [counts]
    simp [w, Fin.sum_univ_succ]
    omega)
  let col (x : I) := refine (raw x) (g x)
  refine ⟨col,fun x => (by decide : ∀ i j, bucket8 (refine i j)=i) _ _,?_⟩
  have low (z : Fin 8) (i : Fin 5) (eq : ∀ u v, refine u v=z ↔ u=i) :
      (univ.filter fun x => col x=z).card=(![a,b,c,r,p₀+p₁+p₂+h] : Fin 5 → ℕ) i := by
    simpa only [col,eq] using counts i
  have high (z : Fin 8) (i : Fin 4) (eq : ∀ u v, refine u v=z ↔ u=4 ∧ v=i) :
      (univ.filter fun x => col x=z).card=w i := by
    convert hg i using 2
    ext x
    simp [s,col,eq]
  intro i
  fin_cases i
  · exact low _ 0 (by decide)
  · exact low _ 1 (by decide)
  · exact low _ 2 (by decide)
  · exact low _ 3 (by decide)
  · exact high _ 0 (by decide)
  · exact high _ 1 (by decide)
  · exact high _ 2 (by decide)
  · exact high _ 3 (by decide)

private theorem bucket_rules {F : Type} [Field F] [DecidableEq F] (p q : F) (c : Fin 8)
    (hc : bucket8 c=rootBucket p q) :
    let f : Fin 3 → F := ![0,p,q]
    (∀ i, c∈coreClasses i → f i=f (owner c)) ∧
      (c∈ordinaryClasses → f (miss c)≠f (owner c)) ∧
      (c=7 → Function.Injective f) := by
  dsimp only
  by_cases hp : p=0
  · subst p
    by_cases hq : q=0
    · subst q; fin_cases c <;> simp_all [bucket8,rootBucket,coreClasses,ordinaryClasses,owner,miss]
      intro i hi; fin_cases i <;> rfl
    · fin_cases c <;> simp_all [bucket8,rootBucket,coreClasses,ordinaryClasses,owner,miss]
      all_goals intro i hi; fin_cases i <;> simp_all
  · by_cases hq : q=0
    · subst q
      fin_cases c <;> simp_all [bucket8,rootBucket,coreClasses,ordinaryClasses,owner,miss]
      all_goals intro i hi; fin_cases i <;> simp_all
    · by_cases h : p=q
      · subst p
        fin_cases c <;> simp_all [bucket8,rootBucket,coreClasses,ordinaryClasses,owner,miss,Ne.symm hq]
        all_goals intro i hi; fin_cases i <;> simp_all
      · fin_cases c <;> simp_all [bucket8,rootBucket,coreClasses,ordinaryClasses,owner,miss,Ne.symm hq,Ne.symm h]
        all_goals try constructor
        all_goals first
          | intro i i' eq; fin_cases i <;> fin_cases i' <;> simp_all [Ne.symm hp,Ne.symm hq,Ne.symm h]
          | intro i hi; fin_cases i <;> simp_all

/-- Actual polynomial root counts and room for the remaining singleton cores
give the sharp three-head label numerator for one received pair. -/
theorem mass_of_root_profile {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I]
    [Field F] [Fintype F] [DecidableEq F] (dom : I ↪ F) (k : ℕ) (δ : ℝ≥0)
    (P Q : F[X]) (a b c r p₀ p₁ p₂ h C : ℕ)
    (counts : ∀ i, (univ.filter fun x => rootBucket (P.eval (dom x)) (Q.eval (dom x))=i).card =
      (![a,b,c,r,p₀+p₁+p₂+h] : Fin 5 → ℕ) i)
    (rank : k≤C) (support : (1-δ)*(Fintype.card I : ℝ≥0) ≤ ((C+1 : ℕ) : ℝ≥0))
    (degP : 1+P.natDegree<k) (degQ : 1+Q.natDegree<k)
    (core₀ : b+c+r+p₀=C) (core₁ : a+c+r+p₁=C) (core₂ : a+b+r+p₂=C)
    (room : 4 < Fintype.card F) (fieldRoom : (a+b+c+p₀+p₁+p₂+3*h)^2 < Fintype.card F) :
    ((a+b+c+p₀+p₁+p₂+3*h : ℕ) : ℝ≥0∞)/Fintype.card F ≤
      epsMCA (F:=F) (ReedSolomon.code dom k : Set (I → F)) δ := by
  classical
  obtain ⟨col,hf,hc⟩ := profile_refinement _ a b c r p₀ p₁ p₂ h counts
  let f : Fin 3 → F[X] := ![0,P,Q]
  have ev (i : Fin 3) (x : I) : (f i).eval (dom x)=(![0,P.eval (dom x),Q.eval (dom x)] : Fin 3 → F) i := by
    fin_cases i <;> simp [f]
  have scard (v : Finset (Fin 8)) : (univ.filter fun x => col x∈v).card =
      ∑ i ∈ v, (![a,b,c,r,p₀,p₁,p₂,h] : Fin 8 → ℕ) i := by
    rw [← sum_card_fiberwise_eq_card_filter univ v col]
    exact Finset.sum_congr rfl (fun i _ => hc i)
  apply colored_mass dom k δ col f _ h C _ rank support _ _ (hc 7) _ _ _ room fieldRoom
  · intro i; fin_cases i <;> simp [f,degP,degQ]; omega
  · intro i; rw [scard];fin_cases i <;> norm_num [coreClasses] <;> omega
  · rw [scard];norm_num [ordinaryClasses];omega
  · intro x i hi
    simp only [ev]
    exact (bucket_rules _ _ _ (hf x)).1 i hi
  · intro x hi
    simp only [ev]
    exact (bucket_rules _ _ _ (hf x)).2.1 hi
  · intro x hx i i' he
    simp only [ev] at he
    exact (bucket_rules _ _ _ (hf x)).2.2 hx he

/-- The singleton deficits fit exactly when the optimal formula requires a
nonnegative number of holes. The mass increases by six per Hamming step. -/
theorem allocation_formula (n C a b c r : ℕ)
    (h₀ : b+c+r≤C) (h₁ : a+c+r≤C) (h₂ : a+b+r≤C)
    (good : 6*C < 2*n+3*r+2*(a+b+c)) :
    ∃ p₀ p₁ p₂ h, b+c+r+p₀=C ∧ a+c+r+p₁=C ∧ a+b+r+p₂=C ∧
      a+b+c+r+p₀+p₁+p₂+h=n ∧ n<a+b+c+p₀+p₁+p₂+3*h ∧
      a+b+c+p₀+p₁+p₂+3*h+6*C=3*n+3*r+2*(a+b+c) := by
  refine ⟨C-(b+c+r),C-(a+c+r),C-(a+b+r),n+2*r+(a+b+c)-3*C,?_⟩
  omega

/-- The integer first crossing for the maximal reduced root score. The known
cubic and the individual polynomial root bound bracket every possible value. -/
theorem first_crossing (S e : ℕ) (low : 603979776 ≤ S) (high : S ≤ 805306362)
    (he : e ≤ 480946859) :
    (6*(1073741824-e-1)+1073741824 < 3*1073741824+3*268435454+S ↔
      (3489660928-S)/6+1 ≤ e) ∧
    447392428 ≤ (3489660928-S)/6+1 ∧ (3489660928-S)/6+1 ≤ 480946859 ∧
    ((3489660928-S)/6+1 ≤ 469762048 ↔ 671088641 ≤ S) := by omega

/-- The score cannot be one below its trivial maximum. At the top degree
every lost root costs two and at smaller degree the maximum falls by three. -/
theorem top_score_gap (m x : ℕ) (dm : m ≤ 268435454) (roots : x ≤ 3*m)
    (high : 3*m+805306361 ≤ 2*x) : m=268435454 ∧ x=3*m := by omega

/-- Disjoint prescribed roots lose at most one selected incidence per gcd
degree. Removing that degree preserves the score threshold. -/
theorem cancel_score (m x m' x' g s : ℕ) (deg : m'+g ≤ m) (roots : x ≤ x'+g)
    (score : 3*m+s ≤ 2*x) : 3*m'+s+g ≤ 2*x' := by omega

#print axioms first_crossing
#print axioms top_score_gap
#print axioms colored_mass
#print axioms mass_of_root_profile
#print axioms allocation_formula

end ArkLib.ProximityGap.Frontier.ThreeHeadRootScore
