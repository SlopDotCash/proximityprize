/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

/-! # Antipodal imbalance in odd split locator fibers -/

set_option autoImplicit false
namespace ArkLib.ProximityGap.Frontier.ApolarAntipodalFiber
open Finset Polynomial
variable {I K : Type*} [Fintype I] [DecidableEq I]

/-- The signed occupancy of one antipodal pair. -/
def imbalance (S : Finset (I × Bool)) (i : I) : ℤ :=
  (if (i,false) ∈ S then 1 else 0) - (if (i,true) ∈ S then 1 else 0)

omit [Fintype I] in
private theorem same_site {S U : Finset (I × Bool)} {i : I}
    (h : imbalance S i = imbalance U i) (hs : imbalance S i ≠ 0) :
    ∀ b : Bool, (i,b) ∈ S → (i,b) ∈ U := by
  cases hf : decide ((i,false) ∈ S) <;> cases ht : decide ((i,true) ∈ S) <;>
    cases huf : decide ((i,false) ∈ U) <;> cases hut : decide ((i,true) ∈ U) <;>
      simp_all [imbalance]

/-- An odd subset has a pair with nonzero signed occupancy. -/
theorem exists_unbalanced (S : Finset (I × Bool)) (h : S.card % 2 = 1) :
    ∃ i, imbalance S i ≠ 0 := by
  by_contra! hz
  let v := univ.filter (fun i : I => (i,false) ∈ S)
  have both (i : I) : (i,false) ∈ S ↔ (i,true) ∈ S := by
    have z := hz i
    by_cases h₀ : (i,false) ∈ S <;> by_cases h₁ : (i,true) ∈ S <;>
      simp_all [imbalance]
  have eq : S = v ×ˢ (univ : Finset Bool) := by
    ext ⟨i,b⟩
    cases b <;> simp [v,both]
  have hc := congrArg card eq
  simp only [card_product,card_univ,Fintype.card_bool] at hc
  omega

/-- Equal signed occupancies on odd fibers force a common coordinate. -/
theorem common_site {T : Finset K} (hT : T.Nonempty) (fiber : K → Finset (I × Bool))
    (hodd : ∀ t ∈ T, (fiber t).card % 2 = 1)
    (hsame : ∀ t ∈ T, ∀ u ∈ T, ∀ i, imbalance (fiber t) i = imbalance (fiber u) i) :
    ∃ x : I × Bool, ∀ t ∈ T, x ∈ fiber t := by
  obtain ⟨t,ht⟩ := hT
  obtain ⟨i,hi⟩ := exists_unbalanced (fiber t) (hodd t ht)
  obtain ⟨b,hb⟩ : ∃ b : Bool, (i,b) ∈ fiber t := by
    by_contra! hz
    simp [imbalance,hz] at hi
  exact ⟨(i,b), fun u hu => same_site (hsame t ht u hu i) hi b hb⟩

/-- If every coordinate occurs as a root of a nonzero parameter polynomial
of degree at most l, at most l odd fibers can share their complete imbalance. -/
theorem card_le_param_degree [Field K] (T : Finset K) (fiber : K → Finset (I × Bool))
    (f : I × Bool → K[X]) (l : ℕ) (hnz : ∀ x, f x ≠ 0)
    (hdeg : ∀ x, (f x).natDegree ≤ l)
    (hroot : ∀ t ∈ T, ∀ x ∈ fiber t, (f x).eval t = 0)
    (hodd : ∀ t ∈ T, (fiber t).card % 2 = 1)
    (hsame : ∀ t ∈ T, ∀ u ∈ T, ∀ i, imbalance (fiber t) i = imbalance (fiber u) i) :
    T.card ≤ l := by
  by_contra! too_many
  obtain ⟨x,hx⟩ := common_site (card_pos.mp (by omega : 0 < T.card)) fiber hodd hsame
  exact hnz x (eq_zero_of_natDegree_lt_card_of_eval_eq_zero' (f x) T
    (fun t ht => hroot t ht x (hx t ht)) ((hdeg x).trans_lt too_many))

/-- The three sufficient width cutoffs in the split-norm comparison. -/
theorem width_cutoffs :
    2*51622204+165191046+1 = 268435455 ∧ 30*268435456 ≤ 156*51622204 ∧
    2*50968758+166497938+1 = 268435455 ∧ 30*268435456 ≤ 158*50968758 ∧
    2*50648200+167139054+1 = 268435455 ∧ 30*268435456 ≤ 159*50648200 := by decide

#print axioms exists_unbalanced
#print axioms common_site
#print axioms card_le_param_degree
#print axioms width_cutoffs

end ArkLib.ProximityGap.Frontier.ApolarAntipodalFiber
