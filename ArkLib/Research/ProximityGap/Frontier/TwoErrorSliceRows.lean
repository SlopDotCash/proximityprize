/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.TwoErrorSliceWeight

/-! # Sample weights for a word with a fixed pair of true errors -/

namespace ProximityGap.TwoErrorSlice

open Finset

variable {I F : Type*} [Fintype I] [DecidableEq I] [Field F]

theorem sampleWeight_on_pair (D : I ↪ F) (reward : I → I → F → ℕ) (E A S : Finset I) (err : I → F)
    (hA : A.card=2) (hsub : A ⊆ E) (hS : S ⊆ univ \ E)
    (hc : ∀ u∈A, ∀ v∈A, u ≠ v → D u ≠ -D v) :
    sampleWeight D reward E err ((E \ A) ∪ S) = reward (ends A hA).1 (ends A hA).2
      (err (ends A hA).2 / err (ends A hA).1 *
        ∏ x ∈ (univ \ E) \ S, ratio D (ends A hA).1 (ends A hA).2 x) := by
  classical
  have he : E \ ((E \ A) ∪ S) = A := by
    ext x
    have hl : x ∈ A → x ∈ E := fun h => hsub h
    have hr : x ∈ S → x ∉ E := fun h => (mem_sdiff.mp (hS h)).2
    simp only [mem_sdiff,mem_union]; tauto
  have hg : (univ \ E) \ ((E \ A) ∪ S) = (univ \ E) \ S := by
    ext; simp; tauto
  obtain ⟨hd,hpair⟩ := ends_spec hA
  let p := ends A hA
  change A={p.1,p.2} at hpair
  have hu : p.1 ∈ A := hpair ▸ mem_insert_self ..
  have hv : p.2 ∈ A := hpair ▸ mem_insert_of_mem (mem_singleton_self _)
  have hn := hc _ hu _ hv hd
  change D (ends A hA).1 ≠ -D (ends A hA).2 at hn
  simp [sampleWeight,he,hg,hA,hn]

/-- Fix all but the final added site and both true errors. The domain-wide
penalty bound applies to one multiplicative scale throughout the resulting row. -/
theorem last_site_general (D : I ↪ F) {S N : ℕ} (cert : PenaltyCap D S) (E A Q : Finset I) (err : I → F)
    (herr : ∀ x ∈ E, err x ≠ 0) (hA : A.card=2) (hsub : A ⊆ E)
    (hc : ∀ u∈A, ∀ v∈A, u ≠ v → D u ≠ -D v)
    (hQ : Q ⊆ univ \ E) (size : ((univ \ E) \ Q).card=N) :
    3*N-S ≤ ∑ x ∈ (univ \ E) \ Q, credit D E err ((E \ A) ∪ insert x Q) := by
  classical
  let p := ends A hA
  obtain ⟨hnep,hpair⟩ := ends_spec hA
  change p.1 ≠ p.2 at hnep
  change A = {p.1,p.2} at hpair
  have h1 : p.1 ∈ A := hpair ▸ mem_insert_self ..
  have h2 : p.2 ∈ A := hpair ▸ mem_insert_of_mem (mem_singleton_self _)
  let X := (univ \ E) \ Q
  have Xsub : X ⊆ (univ.erase p.1).erase p.2 := by
    intro x hx
    have nx := (mem_sdiff.mp (mem_sdiff.mp hx).1).2
    simp only [mem_erase,mem_univ,and_true]
    exact ⟨fun h => nx (h ▸ hsub h2),fun h => nx (h ▸ hsub h1)⟩
  let f := ratio D p.1 p.2
  have nf {x} (hx : x ∈ X) : f x ≠ 0 := by
    obtain ⟨hx2,hx'⟩ := mem_erase.mp (Xsub hx)
    exact ratio_ne_zero D (mem_erase.mp hx').1.symm hx2.symm
  let μ := err p.2 / err p.1 * ∏ y ∈ X, f y
  have hμ : μ ≠ 0 := mul_ne_zero (div_ne_zero (herr _ (hsub h2)) (herr _ (hsub h1)))
    (Finset.prod_ne_zero_iff.mpr fun _ hy => nf hy)
  let costs x := penalty (alternatives D p.1 p.2 (μ / f x)).card
  have bound : (∑ x ∈ X, costs x) ≤ S :=
    (sum_le_sum_of_subset_of_nonneg Xsub (fun _ _ _ => Nat.zero_le _)).trans
      (cert p.1 p.2 hnep (hc _ h1 _ h2 hnep) μ hμ)
  have weight {x} (hx : x ∈ X) : credit D E err ((E \ A) ∪ insert x Q)+costs x=3 := by
    have hpart : (univ \ E) \ insert x Q = X.erase x := by ext; simp [X]; tauto
    rw [credit,sampleWeight_on_pair D _ E A (insert x Q) err hA hsub
      (insert_subset (mem_sdiff.mp hx).1 hQ) hc,hpart]
    have prod' := prod_erase_mul (s := X) f hx
    have same : err p.2 / err p.1 * (∏ y ∈ X.erase x, f y) = μ/f x := by
      apply (eq_div_iff (nf hx)).mpr
      dsimp only [μ]
      rw [mul_assoc,prod']
    change 3-penalty (alternatives D p.1 p.2 (err p.2 / err p.1 * ∏ y ∈ X.erase x, f y)).card +
      penalty (alternatives D p.1 p.2 (μ/f x)).card = 3
    rw [same]
    unfold penalty
    split_ifs <;> decide
  have total : (∑ x ∈ X, credit D E err ((E \ A) ∪ insert x Q)) + (∑ x ∈ X, costs x) = 3*N := by
    rw [← sum_add_distrib, sum_congr rfl (fun x hx => weight hx)]
    simp [X,size,Nat.mul_comm]
  change 3*N-S ≤ ∑ x ∈ X, credit D E err ((E \ A) ∪ insert x Q)
  omega

/-- Specialization to 66 available final sites and the twelve-unit penalty. -/
theorem last_site (D : I ↪ F) (cert : PenaltyBound D) (E A Q : Finset I) (err : I → F)
    (herr : ∀ x ∈ E, err x ≠ 0) (hA : A.card=2) (hsub : A ⊆ E)
    (hc : ∀ u∈A, ∀ v∈A, u ≠ v → D u ≠ -D v)
    (hQ : Q ⊆ univ \ E) (h66 : ((univ \ E) \ Q).card=66) :
    186 ≤ ∑ x ∈ (univ \ E) \ Q, credit D E err ((E \ A) ∪ insert x Q) :=
  last_site_general D cert E A Q err herr hA hsub hc hQ h66

end ProximityGap.TwoErrorSlice

#print axioms ProximityGap.TwoErrorSlice.last_site
