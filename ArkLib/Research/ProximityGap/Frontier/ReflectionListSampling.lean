/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.TwoErrorSliceCount

/-! # Arbitrary-length list bounds from a cap on nonreflection pair products -/
namespace ProximityGap.ReflectionListSampling

open Finset Polynomial Code TwoErrorSlice

variable {I J F : Type*} [Fintype I] [DecidableEq I] [Field F]

/-- Every nonreflection fiber together with the two base sites determines at
most T transpositions. -/
def PairCap (D : I ↪ F) (T : ℕ) : Prop :=
  ∀ u v : I, u≠v → D u ≠ -D v → ∀ t : F, t≠D u/D v →
    (alternatives D u v t).card+1 ≤ T

/-- Unit reward for every target distinct from the reflection product. -/
noncomputable def reward (D : I ↪ F) (u v : I) (t : F) : ℕ := by
  classical
  exact if t=D u/D v then 0 else 1

omit [Fintype I] [DecidableEq I] in
private theorem ratio_inj (D : I ↪ F) {u v x y : I} (huv : u≠v) (hx : x≠v) (hy : y≠v)
    (eq : ratio D u v x=ratio D u v y) : x=y := by
  have h := (div_eq_div_iff (sub_ne_zero.mpr (D.injective.ne hx.symm))
    (sub_ne_zero.mpr (D.injective.ne hy.symm))).mp eq
  have zero : (D u-D v)*(D x-D y)=0 := by linear_combination h
  exact D.injective (sub_eq_zero.mp ((mul_eq_zero.mp zero).resolve_left (sub_ne_zero.mpr (D.injective.ne huv))))

/-- Vary the final added correct site. Its ratio takes distinct values, so at
most one extension can hit the reflection product. -/
theorem final_site (D : I ↪ F) (E A Q : Finset I) (err : I → F)
    (herr : ∀ x∈E, err x≠0) (hc : A.card=2) (hA : A⊆E)
    (clean : ∀ u∈A,∀ v∈A,u≠v → D u≠-D v) (hQ : Q⊆univ\E) :
    ((univ\E)\Q).card-1 ≤ ∑ x ∈ (univ\E)\Q,
      sampleWeight D (reward D) E err ((E\A) ∪ insert x Q) := by
  classical
  let sites := (univ\E)\Q
  let u := (ends A hc).1
  let v := (ends A hc).2
  obtain ⟨ne,pair⟩ := ends_spec hc
  change A={u,v} at pair
  have hu : u∈E := hA (pair ▸ mem_insert_self ..)
  have hv : v∈E := hA (pair ▸ mem_insert_of_mem (mem_singleton_self _))
  have off {x : I} (hx : x∈sites) : x≠u ∧ x≠v := by
    have h := (mem_sdiff.mp (mem_sdiff.mp hx).1).2
    exact ⟨fun he => h (he ▸ hu),fun he => h (he ▸ hv)⟩
  let f := ratio D u v
  have nf {x : I} (hx : x∈sites) : f x≠0 := ratio_ne_zero D (off hx).1.symm (off hx).2.symm
  let μ := err v/err u * ∏ y∈sites,f y
  have nμ : μ≠0 := mul_ne_zero (div_ne_zero (herr v hv) (herr u hu))
    (prod_ne_zero_iff.mpr fun _ hy => nf hy)
  have val {x : I} (hx : x∈sites) : sampleWeight D (reward D) E err ((E\A) ∪ insert x Q) =
      if μ/f x=D u/D v then 0 else 1 := by
    have part : (univ\E)\insert x Q=sites.erase x := by ext; simp [sites]; tauto
    rw [sampleWeight_on_pair D _ E A _ err hc hA (insert_subset (mem_sdiff.mp hx).1 hQ) clean,part]
    have fx : err v/err u*(∏ y∈sites.erase x,f y)=μ/f x := by
      apply (eq_div_iff (nf hx)).mpr
      rw [mul_assoc,prod_erase_mul _ _ hx]
    change reward D u v (err v/err u*(∏ y∈sites.erase x,f y))=_
    rw [fx]
    rfl
  let bad := sites.filter fun x => μ/f x=D u/D v
  have small : bad.card≤1 := by
    apply card_le_one.mpr
    intro x hx y hy
    obtain ⟨mx,ex⟩ := mem_filter.mp hx
    obtain ⟨my,ey⟩ := mem_filter.mp hy
    have eq := (div_eq_div_iff (nf mx) (nf my)).mp (ex.trans ey.symm)
    exact ratio_inj D ne (off mx).2 (off my).2 (mul_left_cancel₀ nμ eq.symm)
  have total := sum_congr rfl (fun x (hx : x∈sites) => val hx)
  rw [total]
  change sites.card-1 ≤ ∑ x∈sites,if μ/f x=D u/D v then 0 else 1
  rw [sum_ite]
  simp only [sum_const_zero,zero_add,sum_const,nsmul_eq_mul,Nat.cast_id,mul_one]
  have split := card_filter_add_card_filter_not (s:=sites) (fun x => μ/f x=D u/D v)
  change (sites.filter _).card ≤ 1 at small
  omega

/-- At most T list members can receive positive weight in a puncture. -/
theorem column (D : I ↪ F) {cap k : ℕ} (rigid : PairCap D cap)
    (P : J → F[X]) (inj : Function.Injective P) (W : I → F) (T : Finset J) (E : J → Finset I)
    (he : ∀ j∈T,∀ x,x∈E j ↔ (P j).eval (D x)≠W x) (hd : ∀ j∈T,(P j).natDegree<k)
    (R : Finset I) (hU : (univ\R).card=k+3) :
    (∑ j∈T,sampleWeight D (reward D) (E j) (fun x => (P j).eval (D x)-W x) R) ≤ cap := by
  classical
  let w j := sampleWeight D (reward D) (E j) (fun x => (P j).eval (D x)-W x) R
  let S := T.filter fun j => (E j\R).card=2
  have eq : (∑ j∈S,w j)=∑ j∈T,w j := by
    apply sum_subset (filter_subset ..)
    intro j hj hn
    have ne : (E j\R).card≠2 := fun h => hn (mem_filter.mpr ⟨hj,h⟩)
    simp [w,sampleWeight,ne]
  change (∑ j∈T,w j)≤cap
  rw [←eq]
  by_cases hs : S.card≤cap
  · apply (sum_le_sum (g := fun _ => 1) _).trans (by simpa using hs)
    intro j hj
    simp only [w,sampleWeight,reward]
    split_ifs <;> decide
  · have zero (j) (hj : j∈S) : w j=0 := by
      have size {i} (h : i∈S) : (E i\R).card=2 := (mem_filter.mp h).2
      have count := local_population D P inj W S E (fun i h => he i (mem_filter.mp h).1)
        (fun i h => hd i (mem_filter.mp h).1) R hU (fun {i} h => size h) j hj
      let p := ends (E j\R) (size hj)
      let t := ((P j).eval (D p.2)-W p.2)/((P j).eval (D p.1)-W p.1) *
        ∏ x∈(univ\E j)\R,ratio D p.1 p.2 x
      change S.card ≤ (alternatives D p.1 p.2 t).card+1 at count
      have ne := (ends_spec (size hj)).1
      by_cases anti : D p.1 = -D p.2
      · simp [w,sampleWeight,size hj,p] at anti ⊢
        simp [anti]
      · have good : t=D p.1/D p.2 := by
          by_contra h
          exact hs (count.trans (rigid _ _ ne anti t h))
        change sampleWeight D (reward D) (E j) _ R=0
        simp only [sampleWeight,size hj,dite_true]
        change (if D p.1 = -D p.2 then 0 else reward D p.1 p.2 t)=0
        simp [reward,good]
    simp [sum_eq_zero zero]

end ProximityGap.ReflectionListSampling

#print axioms ProximityGap.ReflectionListSampling.column
#print axioms ProximityGap.ReflectionListSampling.final_site
