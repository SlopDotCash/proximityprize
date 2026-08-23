/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Whir.MCAJohnsonCurveExtract
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Curve quantified joint agreement (general-parℓ MCA, capstone)

Combines `curve_mutual_extract` (Vandermonde recovery of the word stack from
`parℓ` collinear proximates) with the Bonferroni intersection bound: `parℓ`
proximates with agreement sets `A i` recover the whole stack `f` as a codeword
tuple on `⋂ᵢ A i`, of size `≥ Σᵢ|A i| − (parℓ−1)·n`. The complete quantified
general-`parℓ` correlated-agreement statement (curve axis). -/

namespace MCAJohnson

open Polynomial Finset

variable {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι]
  (domain : ι ↪ F)

-- Bonferroni intersection lower bound.
/-- **Bonferroni lower bound on a finite intersection.** -/
theorem card_inf_ge {κ : Type*} (s : Finset κ) (A : κ → Finset ι) :
    (∑ i ∈ s, (A i).card : ℤ) - (s.card - 1) * (Fintype.card ι : ℤ)
      ≤ ((s.inf A).card : ℤ) := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp only [Finset.sum_empty, Finset.card_empty, Finset.inf_empty]
      have : (Finset.univ : Finset ι).card = Fintype.card ι := Finset.card_univ
      push_cast [this]
      ring_nf
      simp
  | insert a s ha ih =>
      rw [Finset.inf_insert, Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
      -- |A a ∩ inf s A| ≥ |A a| + |inf s A| - n
      have hpair : ((A a ⊓ s.inf A).card : ℤ)
          ≥ (A a).card + (s.inf A).card - (Fintype.card ι : ℤ) := by
        have hu : ((A a ∪ s.inf A).card : ℤ) ≤ (Fintype.card ι : ℤ) := by
          have : (A a ∪ s.inf A).card ≤ Fintype.card ι := by
            rw [← Finset.card_univ]; exact Finset.card_le_card (Finset.subset_univ _)
          exact_mod_cast this
        have hie : (A a ⊓ s.inf A).card + (A a ∪ s.inf A).card
            = (A a).card + (s.inf A).card := Finset.card_inter_add_card_union _ _
        have : ((A a ⊓ s.inf A).card : ℤ) + ((A a ∪ s.inf A).card : ℤ)
            = (A a).card + (s.inf A).card := by exact_mod_cast hie
        linarith
      have hscard : ((s.card : ℤ) + 1 - 1) = (s.card : ℤ) := by ring
      push_cast at ih ⊢
      nlinarith [ih, hpair]


/-- **Curve quantified joint agreement.** -/
theorem curve_joint_agreement {parℓ : ℕ} {deg : ℕ}
    (αs : Fin parℓ → F) (hα : Function.Injective αs)
    (c : Fin parℓ → F[X]) (hc : ∀ i, c i ∈ Polynomial.degreeLT F deg)
    (f : Fin parℓ → ι → F) (A : Fin parℓ → Finset ι)
    (h : ∀ i, ∀ x ∈ A i, (c i).eval (domain x) = ∑ j : Fin parℓ, (αs i) ^ (j : ℕ) * f j x) :
    ∃ (p : Fin parℓ → F[X]) (S : Finset ι),
      (∀ j, p j ∈ Polynomial.degreeLT F deg) ∧
      S = Finset.univ.inf A ∧
      (∑ i : Fin parℓ, (A i).card : ℤ) - ((parℓ : ℤ) - 1) * (Fintype.card ι : ℤ) ≤ (S.card : ℤ) ∧
      (∀ x ∈ S, ∀ j, (p j).eval (domain x) = f j x) := by
  classical
  set S : Finset ι := Finset.univ.inf A with hS
  have hagree : ∀ x ∈ S, ∀ i, (c i).eval (domain x) = ∑ j : Fin parℓ, (αs i) ^ (j : ℕ) * f j x := by
    intro x hx i
    refine h i x ?_
    have hmem := Finset.mem_inf.mp (by rw [← hS]; exact hx)
    exact hmem i (Finset.mem_univ i)
  obtain ⟨p, hpmem, hpeval⟩ := curve_mutual_extract domain αs hα c hc f (S := S) hagree
  refine ⟨p, S, hpmem, rfl, ?_, hpeval⟩
  have hb := card_inf_ge (Finset.univ : Finset (Fin parℓ)) A
  rw [Finset.card_univ, Fintype.card_fin] at hb
  rw [hS]
  exact_mod_cast hb

end MCAJohnson
