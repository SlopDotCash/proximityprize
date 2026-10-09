/-
Copyright (c) 2026 Mikhail Izhutkin. All rights reserved.
Released under MIT and Apache-2.0 licenses as described in LICENSE.
Authors: Mikhail Izhutkin
-/
import Research.ProximityPrize.Frontier._P1RateQuarterAgreementOverlapGraph
import Research.ProximityPrize.Frontier._P1RateQuarterPencilCountCharge
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Sum
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Tauto

/-!
# Full-owner linear-direction bad-scalar budget at the P1 predecessor

For the received pair `(x * r(x), r(x))`, this file proves the bound of `N` bad scalars
at `N = 2^30`, dimension `K = 2^28`, and agreement threshold `T = 592794966`.
The heads are arbitrary Reed-Solomon codewords and are nonjoint on their witness supports.
No factorization of the heads is assumed.

Division by `X + gamma` splits heads into polynomial and proper-pole approximants.
The existing integral five-set Johnson inequality bounds their combined family by four.
When three polynomial approximants coexist with one proper pole, polynomial root bounds
and a three-set incidence count force at least 11184814 common coordinates outside the
pole support. This closes the final counting case.

The theorem applies on every injective evaluation domain and in every field. The final
production corollary consumes the canonical `BadFamilyData` for this received pair.
It does not establish full ownership of a general stack, handle partial owners or general
rational directions, prove `SwarmResidual`, or close the Proximity Prize.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterLinearOwnerBudget

namespace PolePolynomialIntersection

open Polynomial

variable {F ι : Type*} [Field F] [DecidableEq F]

/-- Bounds agreement intersections using the degree of a nonzero polynomial numerator. -/
theorem intersection_card_le
    (dom : ι ↪ F) (S : Finset ι) (h q : F[X]) (γ c : F) (d : ℕ)
    (hc : c ≠ 0) (hh : h.natDegree ≤ d) (hq : q.natDegree ≤ d)
    (hagree : ∀ i ∈ S, (dom i + γ) * (h.eval (dom i) - q.eval (dom i)) = c) :
    S.card ≤ d + 1 := by
  classical
  let P : F[X] := (X + C γ) * (h - q) - C c
  have hP : P ≠ 0 := by
    intro hz
    have heval := congrArg (Polynomial.eval (-γ)) hz
    have hc₀ : c = 0 := by simpa [P] using heval
    exact hc hc₀
  have hX : (X + C γ : F[X]).natDegree ≤ 1 := by
    exact (natDegree_add_le _ _).trans (by simp)
  have hsub : (h - q).natDegree ≤ d :=
    (natDegree_sub_le _ _).trans (max_le hh hq)
  have hmul : ((X + C γ) * (h - q)).natDegree ≤ d + 1 := by
    have hm : ((X + C γ) * (h - q)).natDegree ≤
        (X + C γ).natDegree + (h - q).natDegree := natDegree_mul_le
    omega
  have hdeg : P.natDegree ≤ d + 1 := by
    exact (natDegree_sub_le _ _).trans (max_le hmul (by simp))
  have hroots : (S.image dom).val ⊆ P.roots := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    apply (mem_roots hP).mpr
    have ha := hagree i hi
    simpa [P] using sub_eq_zero.mpr ha
  have hcard := card_le_degree_of_subset_roots hroots
  rw [Finset.card_image_of_injective S dom.injective] at hcard
  exact hcard.trans hdeg

end PolePolynomialIntersection


namespace DistinctPoleIntersection

open Polynomial

/-- Bounds agreement intersections using the degree of a nonzero polynomial numerator. -/
theorem intersection_card_le
    {F ι : Type*} [Field F] [DecidableEq F]
    (dom : ι ↪ F) (S : Finset ι) (r : ι → F)
    (q q' : F[X]) (γ δ c c' : F) (d : ℕ)
    (hγδ : γ ≠ δ) (hc : c ≠ 0)
    (hq : q.natDegree ≤ d) (hq' : q'.natDegree ≤ d)
    (ha : ∀ i ∈ S, (dom i + γ) * r i =
      (dom i + γ) * q.eval (dom i) + c)
    (hb : ∀ i ∈ S, (dom i + δ) * r i =
      (dom i + δ) * q'.eval (dom i) + c') :
    S.card ≤ d + 2 := by
  classical
  let P : F[X] := (X + C γ) * (X + C δ) * (q - q') +
    C c * (X + C δ) - C c' * (X + C γ)
  have hP : P ≠ 0 := by
    intro hz
    have heval := congrArg (Polynomial.eval (-γ)) hz
    have he : c * (-γ + δ) = 0 := by simpa [P] using heval
    have hdiff : -γ + δ ≠ 0 := by
      intro hd
      apply hγδ
      linear_combination -hd
    exact (mul_ne_zero hc hdiff) he
  have hlin (a : F) : (X + C a : F[X]).natDegree ≤ 1 :=
    (natDegree_add_le _ _).trans (by simp)
  have hsub : (q - q').natDegree ≤ d :=
    (natDegree_sub_le _ _).trans (max_le hq hq')
  have hprod : ((X + C γ) * (X + C δ)).natDegree ≤ 2 := by
    have h : ((X + C γ) * (X + C δ)).natDegree ≤
      (X + C γ).natDegree + (X + C δ).natDegree := natDegree_mul_le
    have hγ := hlin γ
    have hδ := hlin δ
    omega
  have hmain : ((X + C γ) * (X + C δ) * (q - q')).natDegree ≤ d + 2 := by
    have h : ((X + C γ) * (X + C δ) * (q - q')).natDegree ≤
      ((X + C γ) * (X + C δ)).natDegree + (q - q').natDegree := natDegree_mul_le
    omega
  have hterm (a b : F) : (C a * (X + C b)).natDegree ≤ 1 := by
    have h : (C a * (X + C b)).natDegree ≤
      (C a).natDegree + (X + C b).natDegree := natDegree_mul_le
    simpa using h.trans (Nat.add_le_add_left (hlin b) (C a).natDegree)
  have hdeg : P.natDegree ≤ d + 2 := by
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · exact (natDegree_add_le _ _).trans
        (max_le hmain ((hterm c δ).trans (by omega)))
    · exact (hterm c' γ).trans (by omega)
  have hroots : (S.image dom).val ⊆ P.roots := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    apply (mem_roots hP).mpr
    have h₀ := ha i hi
    have h₁ := hb i hi
    change P.eval (dom i) = 0
    simp only [P, eval_sub, eval_add, eval_mul, eval_X, eval_C]
    linear_combination (dom i + γ) * h₁ - (dom i + δ) * h₀
  have hcard := card_le_degree_of_subset_roots hroots
  rw [Finset.card_image_of_injective S dom.injective] at hcard
  exact hcard.trans hdeg

end DistinctPoleIntersection

namespace CombinedApproximants

open Polynomial
open ArkLib.ProximityGap.Frontier.P1RateQuarterAgreementOverlapGraph

/-- Applies integral five-set Johnson at the production parameters. -/
theorem support_family_card_le_four
    {β : Type*} [DecidableEq β] (J : Finset β)
    (S : β → Finset (Fin 1073741824))
    (hs : ∀ a ∈ J, 592794965 ≤ (S a).card)
    (hp : ∀ a ∈ J, ∀ b ∈ J, a ≠ b → (S a ∩ S b).card ≤ 268435456) :
    J.card ≤ 4 := by
  classical
  by_contra hn
  have hfive : 5 ≤ J.card := by omega
  obtain ⟨I, hIJ, hI⟩ := Finset.exists_subset_card_eq hfive
  have heq : Fintype.card I = 5 := by simpa using hI
  let e := (Fintype.equivFinOfCardEq heq).symm
  have hJ := fiveSet_integral_johnson (fun i : Fin 5 ↦ S (e i))
    (fun i ↦ hs (e i) (hIJ (e i).property))
    (fun i j hij ↦ hp (e i) (hIJ (e i).property)
      (e j) (hIJ (e j).property) (by
        intro h
        exact hij (e.injective (Subtype.ext h))))
  simp only [Fintype.card_fin] at hJ
  omega

/-- Distinct degree-d polynomials agree at no more than d domain coordinates. -/
theorem polynomial_intersection_card_le
    {F ι : Type*} [Field F] [DecidableEq F]
    (dom : ι ↪ F) (r : ι → F) (h h' : F[X]) (d : ℕ)
    (hne : h ≠ h') (hh : h.natDegree ≤ d) (hh' : h'.natDegree ≤ d)
    (S : Finset ι)
    (ha : ∀ i ∈ S, h.eval (dom i) = r i)
    (hb : ∀ i ∈ S, h'.eval (dom i) = r i) :
    S.card ≤ d := by
  classical
  have hz : h - h' ≠ 0 := sub_ne_zero.mpr hne
  have hroots : (S.image dom).val ⊆ (h - h').roots := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    apply (mem_roots hz).mpr
    change (h - h').eval (dom i) = 0
    simp only [eval_sub, ha i hi, hb i hi, sub_self]
  have hcard := card_le_degree_of_subset_roots hroots
  rw [Finset.card_image_of_injective S dom.injective] at hcard
  exact hcard.trans ((natDegree_sub_le _ _).trans (max_le hh hh'))

/-- Polynomial and distinct-pole approximants form a family of at most four. -/
theorem combined_family_card_le_four
    {F : Type*} [Field F] [DecidableEq F]
    (dom : Fin 1073741824 ↪ F) (r : Fin 1073741824 → F)
    (q : F → F[X]) (c : F → F)
    (J : Finset (F[X] ⊕ F)) (S : F[X] ⊕ F → Finset (Fin 1073741824))
    (hs : ∀ a ∈ J, 592794965 ≤ (S a).card)
    (hl : ∀ h, Sum.inl h ∈ J → h.natDegree ≤ 268435454 ∧
      ∀ i ∈ S (Sum.inl h), h.eval (dom i) = r i)
    (hr : ∀ γ, Sum.inr γ ∈ J → (q γ).natDegree ≤ 268435454 ∧
      c γ ≠ 0 ∧ ∀ i ∈ S (Sum.inr γ), (dom i + γ) * r i =
        (dom i + γ) * (q γ).eval (dom i) + c γ) :
    J.card ≤ 4 := by
  apply support_family_card_le_four J S hs
  intro a ha b hb hne
  cases a with
  | inl h =>
    cases b with
    | inl h' =>
      have hh := hl h ha
      have hh' := hl h' hb
      have hpoly : h ≠ h' := by
        intro he
        exact hne (congrArg Sum.inl he)
      have hcap := polynomial_intersection_card_le dom r h h' 268435454
        hpoly hh.1 hh'.1 (S (Sum.inl h) ∩ S (Sum.inl h'))
        (fun i hi ↦ hh.2 i (Finset.mem_inter.mp hi).1)
        (fun i hi ↦ hh'.2 i (Finset.mem_inter.mp hi).2)
      omega
    | inr γ =>
      have hh := hl h ha
      have hγ := hr γ hb
      have hcap := PolePolynomialIntersection.intersection_card_le dom
        (S (Sum.inl h) ∩ S (Sum.inr γ)) h (q γ) γ (c γ) 268435454
        hγ.2.1 hh.1 hγ.1 (by
          intro i hi
          obtain ⟨hi₀, hi₁⟩ := Finset.mem_inter.mp hi
          have he := hγ.2.2 i hi₁
          rw [← hh.2 i hi₀] at he
          linear_combination he)
      omega
  | inr γ =>
    cases b with
    | inl h =>
      have hh := hl h hb
      have hγ := hr γ ha
      have hcap := PolePolynomialIntersection.intersection_card_le dom
        (S (Sum.inr γ) ∩ S (Sum.inl h)) h (q γ) γ (c γ) 268435454
        hγ.2.1 hh.1 hγ.1 (by
          intro i hi
          obtain ⟨hi₀, hi₁⟩ := Finset.mem_inter.mp hi
          have he := hγ.2.2 i hi₀
          rw [← hh.2 i hi₁] at he
          linear_combination he)
      omega
    | inr δ =>
      have hγ := hr γ ha
      have hδ := hr δ hb
      have hdiff : γ ≠ δ := by
        intro he
        exact hne (congrArg Sum.inr he)
      exact DistinctPoleIntersection.intersection_card_le dom
        (S (Sum.inr γ) ∩ S (Sum.inr δ)) r (q γ) (q δ) γ δ
        (c γ) (c δ) 268435454 hdiff hγ.2.1 hγ.1 hδ.1
        (fun i hi ↦ hγ.2.2 i (Finset.mem_inter.mp hi).1)
        (fun i hi ↦ hδ.2.2 i (Finset.mem_inter.mp hi).2)

end CombinedApproximants

namespace CombinedApproximants

open Polynomial

/-- Bounds the combined polynomial family and proper-pole scalar family by four. -/
theorem split_family_card_le_four
    {F : Type*} [Field F] [DecidableEq F]
    (dom : Fin 1073741824 ↪ F) (r : Fin 1073741824 → F)
    (P : Finset F[X]) (R : Finset F)
    (A : F[X] → Finset (Fin 1073741824))
    (B : F → Finset (Fin 1073741824)) (q : F → F[X]) (c : F → F)
    (hs : ∀ h ∈ P, 592794965 ≤ (A h).card)
    (hl : ∀ h ∈ P, h.natDegree ≤ 268435454 ∧
      ∀ i ∈ A h, h.eval (dom i) = r i)
    (hr : ∀ γ ∈ R, 592794966 ≤ (B γ).card ∧
      (q γ).natDegree ≤ 268435454 ∧ c γ ≠ 0 ∧
      ∀ i ∈ B γ, (dom i + γ) * r i =
        (dom i + γ) * (q γ).eval (dom i) + c γ) :
    P.card + R.card ≤ 4 := by
  classical
  have h := combined_family_card_le_four dom r q c (P.disjSum R) (Sum.elim A B)
    (by
      intro a ha
      cases a with
      | inl h => exact hs h (Finset.inl_mem_disjSum.mp ha)
      | inr γ =>
        have hb := (hr γ (Finset.inr_mem_disjSum.mp ha)).1
        exact Nat.le_trans (by decide) hb)
    (fun h hh ↦ hl h (Finset.inl_mem_disjSum.mp hh))
    (fun γ hγ ↦ (hr γ (Finset.inr_mem_disjSum.mp hγ)).2)
  simpa only [Finset.card_disjSum] using h

end CombinedApproximants


namespace PoleTripleIncidence

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
/-- Bounds three-set incidence by twice the ambient size plus the common intersection. -/
theorem triple_mass_le_two_ambient_add_common
    (A B C U : Finset ι) (hA : A ⊆ U) (hB : B ⊆ U) (hC : C ⊆ U) :
    A.card + B.card + C.card ≤ 2 * U.card + ((A ∩ B) ∩ C).card := by
  have h₁ := Finset.card_union_add_card_inter A B
  have h₂ := Finset.card_union_add_card_inter (A ∩ B) C
  have hu₁ : (A ∪ B).card ≤ U.card :=
    Finset.card_le_card (Finset.union_subset hA hB)
  have hu₂ : ((A ∩ B) ∪ C).card ≤ U.card :=
    Finset.card_le_card (Finset.union_subset ((Finset.inter_subset_left).trans hA) hC)
  omega

/-- Counts triple incidence outside a fourth support using mixed intersection caps. -/
theorem pole_triple_incidence
    (A₀ A₁ A₂ B : Finset ι) (c : ℕ)
    (h₀ : (A₀ ∩ B).card ≤ c)
    (h₁ : (A₁ ∩ B).card ≤ c)
    (h₂ : (A₂ ∩ B).card ≤ c) :
    A₀.card + A₁.card + A₂.card + 2 * B.card ≤
      3 * c + 2 * Fintype.card ι + (((A₀ ∩ A₁) ∩ A₂) \ B).card := by
  have hout (A : Finset ι) : A \ B ⊆ Finset.univ \ B := by
    intro x hx
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, (Finset.mem_sdiff.mp hx).2⟩
  have hm := triple_mass_le_two_ambient_add_common
    (A₀ \ B) (A₁ \ B) (A₂ \ B) (Finset.univ \ B)
    (hout A₀) (hout A₁) (hout A₂)
  have heq : (((A₀ \ B) ∩ (A₁ \ B)) ∩ (A₂ \ B)) =
      ((A₀ ∩ A₁) ∩ A₂) \ B := by
    ext x
    simp
    tauto
  rw [heq] at hm
  have hp₀ := Finset.card_sdiff_add_card_inter A₀ B
  have hp₁ := Finset.card_sdiff_add_card_inter A₁ B
  have hp₂ := Finset.card_sdiff_add_card_inter A₂ B
  have hu := Finset.card_sdiff_add_card_inter (Finset.univ : Finset ι) B
  simp only [Finset.univ_inter, Finset.card_univ] at hu
  omega

/-- Production support sizes force 11184814 common positions outside the pole support. -/
theorem production_common_agreement_floor
    (A₀ A₁ A₂ B : Finset (Fin 1073741824))
    (h₀ : 592794965 ≤ A₀.card) (h₁ : 592794965 ≤ A₁.card)
    (h₂ : 592794965 ≤ A₂.card) (hB : 592794966 ≤ B.card)
    (hc₀ : (A₀ ∩ B).card ≤ 268435455)
    (hc₁ : (A₁ ∩ B).card ≤ 268435455)
    (hc₂ : (A₂ ∩ B).card ≤ 268435455) :
    11184814 ≤ (((A₀ ∩ A₁) ∩ A₂) \ B).card := by
  have hm := pole_triple_incidence A₀ A₁ A₂ B 268435455 hc₀ hc₁ hc₂
  simp only [Fintype.card_fin] at hm
  omega

end PoleTripleIncidence

namespace PoleGeometryConsumer

open Polynomial

/-- Derives the common-agreement floor directly from polynomial and pole equations. -/
theorem production_common_agreement
    {F : Type*} [Field F] [DecidableEq F]
    (dom : Fin 1073741824 ↪ F) (r : Fin 1073741824 → F)
    (h₀ h₁ h₂ q : F[X]) (γ c : F) (hc : c ≠ 0)
    (hh₀ : h₀.natDegree ≤ 268435454)
    (hh₁ : h₁.natDegree ≤ 268435454)
    (hh₂ : h₂.natDegree ≤ 268435454)
    (hq : q.natDegree ≤ 268435454)
    (A₀ A₁ A₂ B : Finset (Fin 1073741824))
    (hA₀ : ∀ i ∈ A₀, h₀.eval (dom i) = r i)
    (hA₁ : ∀ i ∈ A₁, h₁.eval (dom i) = r i)
    (hA₂ : ∀ i ∈ A₂, h₂.eval (dom i) = r i)
    (hB : ∀ i ∈ B, (dom i + γ) * r i =
      (dom i + γ) * q.eval (dom i) + c)
    (hs₀ : 592794965 ≤ A₀.card) (hs₁ : 592794965 ≤ A₁.card)
    (hs₂ : 592794965 ≤ A₂.card) (hsB : 592794966 ≤ B.card) :
    11184814 ≤ (((A₀ ∩ A₁) ∩ A₂) \ B).card := by
  have hcap (h : F[X]) (A : Finset (Fin 1073741824))
      (hh : h.natDegree ≤ 268435454)
      (ha : ∀ i ∈ A, h.eval (dom i) = r i) :
      (A ∩ B).card ≤ 268435455 := by
    apply PolePolynomialIntersection.intersection_card_le dom (A ∩ B)
      h q γ c 268435454 hc hh hq
    intro i hi
    obtain ⟨hiA, hiB⟩ := Finset.mem_inter.mp hi
    have hb := hB i hiB
    rw [← ha i hiA] at hb
    linear_combination hb
  exact PoleTripleIncidence.production_common_agreement_floor A₀ A₁ A₂ B
    hs₀ hs₁ hs₂ hsB (hcap h₀ A₀ hh₀ hA₀)
    (hcap h₁ A₁ hh₁ hA₁) (hcap h₂ A₂ hh₂ hA₂)

end PoleGeometryConsumer


namespace PoleComplementBudget

/-- Charges each scalar to a pole outside the common agreement set. -/
theorem card_add_common_le_domain
    {F ι : Type*} [Field F] [Fintype ι]
    (dom : ι → F) (Z : Finset F) (H : Finset ι)
    (hw : ∀ γ ∈ Z, ∃ i, i ∉ H ∧ dom i + γ = 0) :
    Z.card + H.card ≤ Fintype.card ι := by
  classical
  have hsub : Z ⊆ (Finset.univ \ H).image (fun i ↦ -dom i) := by
    intro γ hγ
    obtain ⟨i, hi, he⟩ := hw γ hγ
    apply Finset.mem_image.mpr
    refine ⟨i, Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hi⟩, ?_⟩
    linear_combination -he
  have hcard : Z.card ≤ (Finset.univ \ H).card :=
    (Finset.card_le_card hsub).trans (Finset.card_image_le)
  rw [Finset.card_sdiff] at hcard
  have hH := Finset.card_le_card (Finset.subset_univ H)
  simp only [Finset.card_univ, Finset.inter_univ] at hcard hH
  omega

end PoleComplementBudget


namespace ZeroRemainderWitness

/-- Nonjoint factored agreement forces a mismatch at a pole coordinate. -/
theorem exists_pole_mismatch
    {F ι : Type*} [Field F]
    (dom r h : ι → F) (γ : F) (S : Finset ι)
    (C : Set (ι → F))
    (hcode₀ : (fun i ↦ dom i * h i) ∈ C) (hcode₁ : h ∈ C)
    (hagree : ∀ i ∈ S, (dom i + γ) * h i = (dom i + γ) * r i)
    (hnotjoint : ¬ ∃ c₀ ∈ C, ∃ c₁ ∈ C, ∀ i ∈ S,
      c₀ i = dom i * r i ∧ c₁ i = r i) :
    ∃ i ∈ S, dom i + γ = 0 ∧ r i ≠ h i := by
  classical
  by_contra hn
  apply hnotjoint
  refine ⟨_, hcode₀, h, hcode₁, ?_⟩
  intro i hi
  have hr : r i = h i := by
    by_contra hne
    have hm : (dom i + γ) * (r i - h i) = 0 := by
      linear_combination -(hagree i hi)
    have hz : dom i + γ = 0 :=
      (mul_eq_zero.mp hm).resolve_right (sub_ne_zero.mpr hne)
    exact hn ⟨i, hi, hz, hne⟩
  exact ⟨by rw [hr], hr.symm⟩

end ZeroRemainderWitness


namespace DecodedLinearDivision

open Polynomial

/-- Divides a decoded head by X + gamma and identifies its constant remainder. -/
theorem decomposition
    {F : Type*} [Field F] (p : F[X]) (γ : F) :
    p = (X + C γ) * (p /ₘ (X + C γ)) + C (p.eval (-γ)) := by
  have h := modByMonic_add_div p (X - C (-γ))
  rw [modByMonic_X_sub_C_eq_C_eval] at h
  simpa [sub_neg_eq_add, add_comm] using h.symm

/-- Bounds the degree of the linear quotient of a degree-below-k head. -/
theorem quotient_degree
    {F : Type*} [Field F] (p : F[X]) (γ : F) (k : ℕ)
    (hk : 2 ≤ k) (hp : p.natDegree < k) :
    (p /ₘ (X + C γ)).natDegree ≤ k - 2 := by
  have hmonic : (X + C γ : F[X]).Monic := by
    simpa using (monic_X_sub_C (-γ))
  rw [natDegree_divByMonic p hmonic]
  have hdeg : (X + C γ : F[X]).natDegree = 1 := by
    simp
  rw [hdeg]
  omega

/-- Transfers decoded-head agreement to its quotient-and-remainder equation. -/
theorem agreement_equation
    {F ι : Type*} [Field F] (p : F[X]) (γ : F)
    (dom r : ι → F) (S : Finset ι)
    (ha : ∀ i ∈ S, p.eval (dom i) = (dom i + γ) * r i) :
    ∀ i ∈ S, (dom i + γ) * r i =
      (dom i + γ) * (p /ₘ (X + C γ)).eval (dom i) + p.eval (-γ) := by
  intro i hi
  have h := congrArg (Polynomial.eval (dom i)) (decomposition p γ)
  simp only [eval_add, eval_mul, eval_X, eval_C] at h
  exact (ha i hi).symm.trans h

/-- A zero remainder gives quotient agreement after removing at most one coordinate. -/
theorem zero_remainder_agreement
    {F ι : Type*} [Field F] [DecidableEq F]
    (p : F[X]) (γ : F) (dom : ι ↪ F) (r : ι → F) (S : Finset ι)
    (hc : p.eval (-γ) = 0)
    (ha : ∀ i ∈ S, p.eval (dom i) = (dom i + γ) * r i) :
    ∃ A : Finset ι, A.card + 1 ≥ S.card ∧
      ∀ i ∈ A, (p /ₘ (X + C γ)).eval (dom i) = r i := by
  classical
  let A := S.filter (fun i ↦ dom i + γ ≠ 0)
  let B := S.filter (fun i ↦ dom i + γ = 0)
  have hB : B.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    have hi₀ := (Finset.mem_filter.mp hi).2
    have hj₀ := (Finset.mem_filter.mp hj).2
    apply dom.injective
    linear_combination hi₀ - hj₀
  have hsplit : B.card + A.card = S.card := by
    exact Finset.card_filter_add_card_filter_not (s := S) (fun i ↦ dom i + γ = 0)
  refine ⟨A, by omega, ?_⟩
  intro i hi
  obtain ⟨hiS, hi₀⟩ := Finset.mem_filter.mp hi
  have he := agreement_equation p γ dom r S ha i hiS
  rw [hc, add_zero] at he
  exact (mul_left_cancel₀ hi₀ he).symm

end DecodedLinearDivision

namespace LinearApproximantBudget

open Polynomial

/-- Combines the four-approximant bound and pole injection into the production budget. -/
theorem production_budget
    {F : Type*} [Field F] [DecidableEq F]
    (dom : Fin 1073741824 ↪ F) (r : Fin 1073741824 → F)
    (P : Finset F[X]) (Z R : Finset F)
    (A : F[X] → Finset (Fin 1073741824))
    (B : F → Finset (Fin 1073741824)) (q : F → F[X]) (c : F → F)
    (H : Finset (Fin 1073741824))
    (hH : ∀ i, i ∈ H ↔ ∀ h ∈ P, i ∈ A h)
    (hsize : ∀ h ∈ P, 592794965 ≤ (A h).card)
    (hpoly : ∀ h ∈ P, h.natDegree ≤ 268435454 ∧
      ∀ i ∈ A h, h.eval (dom i) = r i)
    (hpole : ∀ γ ∈ R, 592794966 ≤ (B γ).card ∧
      (q γ).natDegree ≤ 268435454 ∧ c γ ≠ 0 ∧
      ∀ i ∈ B γ, (dom i + γ) * r i =
        (dom i + γ) * (q γ).eval (dom i) + c γ)
    (hfour : P.card + R.card ≤ 4)
    (hzempty : P = ∅ → Z = ∅)
    (hw : ∀ γ ∈ Z, ∃ i, i ∉ H ∧ dom i + γ = 0) :
    Z.card + R.card ≤ 1073741824 := by
  classical
  have hZ := PoleComplementBudget.card_add_common_le_domain dom Z H hw
  simp only [Fintype.card_fin] at hZ
  by_cases hR : R = ∅
  · simp only [hR, Finset.card_empty, add_zero]
    omega
  have hRpos : 1 ≤ R.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hR)
  have hcases : P.card = 0 ∨ P.card = 1 ∨ P.card = 2 ∨ P.card = 3 := by omega
  rcases hcases with h₀ | h₁ | h₂ | h₃
  · have hP : P = ∅ := Finset.card_eq_zero.mp h₀
    rw [hzempty hP, Finset.card_empty, zero_add]
    omega
  · obtain ⟨a, hP⟩ := Finset.card_eq_one.mp h₁
    have hHa : H = A a := by
      ext i
      simp only [hH, hP, Finset.mem_singleton, forall_eq]
    have hs := hsize a (by simp [hP])
    rw [hHa] at hZ
    omega
  · obtain ⟨a, b, hab, hP⟩ := Finset.card_eq_two.mp h₂
    have hHab : H = A a ∩ A b := by
      ext i
      simp [hH, hP]
    have ha := hsize a (by simp [hP])
    have hb := hsize b (by simp [hP])
    have hu : (A a ∪ A b).card ≤ 1073741824 := by
      simpa using Finset.card_le_card (Finset.subset_univ (A a ∪ A b))
    have hi := Finset.card_union_add_card_inter (A a) (A b)
    rw [hHab] at hZ
    omega
  · obtain ⟨a, b, e, hab, hae, hbe, hP⟩ := Finset.card_eq_three.mp h₃
    have hHabc : H = (A a ∩ A b) ∩ A e := by
      ext i
      simp [hH, hP]
    obtain ⟨γ, hγ⟩ := Finset.nonempty_iff_ne_empty.mpr hR
    have haP : a ∈ P := by simp [hP]
    have hbP : b ∈ P := by simp [hP]
    have heP : e ∈ P := by simp [hP]
    have ha := hpoly a haP
    have hb := hpoly b hbP
    have he := hpoly e heP
    have hr := hpole γ hγ
    have hfloor := PoleGeometryConsumer.production_common_agreement dom r
      a b e (q γ) γ (c γ) hr.2.2.1 ha.1 hb.1 he.1 hr.2.1
      (A a) (A b) (A e) (B γ) ha.2 hb.2 he.2 hr.2.2.2
      (hsize a haP) (hsize b hbP) (hsize e heP) hr.1
    rw [← hHabc] at hfloor
    have hle : (H \ B γ).card ≤ H.card :=
      Finset.card_le_card Finset.sdiff_subset
    omega

end LinearApproximantBudget

namespace FullOwnerLinearBudget

open Polynomial

/-- Bounds bad scalars for arbitrary decoded polynomial heads in the linear owner. -/
theorem bad_scalar_budget
    {F : Type*} [Field F] [DecidableEq F]
    (dom : Fin 1073741824 ↪ F) (r : Fin 1073741824 → F)
    (C : Set (Fin 1073741824 → F))
    (hC : ∀ p : F[X], p.natDegree < 268435456 → (fun i ↦ p.eval (dom i)) ∈ C)
    (G : Finset F) (p : F → F[X]) (S : F → Finset (Fin 1073741824))
    (hdegree : ∀ γ ∈ G, (p γ).natDegree < 268435456)
    (hsize : ∀ γ ∈ G, 592794966 ≤ (S γ).card)
    (hagree : ∀ γ ∈ G, ∀ i ∈ S γ,
      (p γ).eval (dom i) = (dom i + γ) * r i)
    (hno : ∀ γ ∈ G, ¬ ∃ c₀ ∈ C, ∃ c₁ ∈ C, ∀ i ∈ S γ,
      c₀ i = dom i * r i ∧ c₁ i = r i) :
    G.card ≤ 1073741824 := by
  classical
  let q : F → F[X] := fun γ ↦ p γ /ₘ (X + Polynomial.C γ)
  let c : F → F := fun γ ↦ (p γ).eval (-γ)
  let Z := G.filter (fun γ ↦ c γ = 0)
  let R := G.filter (fun γ ↦ c γ ≠ 0)
  let P := Z.image q
  let A : F[X] → Finset (Fin 1073741824) :=
    fun h ↦ Finset.univ.filter (fun i ↦ h.eval (dom i) = r i)
  let H := Finset.univ.filter (fun i ↦ ∀ h ∈ P, i ∈ A h)
  have hq : ∀ γ ∈ G, (q γ).natDegree ≤ 268435454 := by
    intro γ hγ
    exact DecodedLinearDivision.quotient_degree (p γ) γ 268435456
      (by decide) (hdegree γ hγ)
  have hA (h : F[X]) (i : Fin 1073741824) :
      i ∈ A h ↔ h.eval (dom i) = r i := by simp [A]
  have hH (i : Fin 1073741824) : i ∈ H ↔ ∀ h ∈ P, i ∈ A h := by simp [H]
  have hpoly : ∀ h ∈ P, h.natDegree ≤ 268435454 ∧
      ∀ i ∈ A h, h.eval (dom i) = r i := by
    intro h hh
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hh
    exact ⟨hq γ (Finset.mem_filter.mp hγ).1, fun i hi ↦ (hA _ i).mp hi⟩
  have hpolySize : ∀ h ∈ P, 592794965 ≤ (A h).card := by
    intro h hh
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hh
    obtain ⟨hγG, hc⟩ := Finset.mem_filter.mp hγ
    obtain ⟨W, hWsize, hWagree⟩ := DecodedLinearDivision.zero_remainder_agreement
      (p γ) γ dom r (S γ) hc (hagree γ hγG)
    have hsub : W ⊆ A (q γ) := by
      intro i hi
      exact (hA _ i).mpr (hWagree i hi)
    have hcard := Finset.card_le_card hsub
    have hs := hsize γ hγG
    omega
  have hpole : ∀ γ ∈ R, 592794966 ≤ (S γ).card ∧
      (q γ).natDegree ≤ 268435454 ∧ c γ ≠ 0 ∧
      ∀ i ∈ S γ, (dom i + γ) * r i =
        (dom i + γ) * (q γ).eval (dom i) + c γ := by
    intro γ hγ
    obtain ⟨hγG, hc⟩ := Finset.mem_filter.mp hγ
    exact ⟨hsize γ hγG, hq γ hγG, hc,
      DecodedLinearDivision.agreement_equation (p γ) γ dom r (S γ) (hagree γ hγG)⟩
  have hfour := CombinedApproximants.split_family_card_le_four dom r P R A S q c
    hpolySize hpoly hpole
  have hempty : P = ∅ → Z = ∅ := by
    intro hP
    exact Finset.image_eq_empty.mp hP
  have hw : ∀ γ ∈ Z, ∃ i, i ∉ H ∧ dom i + γ = 0 := by
    intro γ hγ
    obtain ⟨hγG, hc⟩ := Finset.mem_filter.mp hγ
    have hqdeg := hq γ hγG
    have hqcode : (fun i ↦ (q γ).eval (dom i)) ∈ C :=
      hC (q γ) (by omega)
    have hxdeg : (X * q γ).natDegree < 268435456 := by
      have hm : (X * q γ).natDegree ≤ (X : F[X]).natDegree + (q γ).natDegree :=
        natDegree_mul_le
      simp only [natDegree_X] at hm
      omega
    have hxcode : (fun i ↦ dom i * (q γ).eval (dom i)) ∈ C := by
      simpa only [eval_mul, eval_X] using hC (X * q γ) hxdeg
    have he : ∀ i ∈ S γ, (dom i + γ) * (q γ).eval (dom i) =
        (dom i + γ) * r i := by
      intro i hi
      have ha := DecodedLinearDivision.agreement_equation
        (p γ) γ dom r (S γ) (hagree γ hγG) i hi
      change (dom i + γ) * r i = (dom i + γ) * (q γ).eval (dom i) + c γ at ha
      rw [hc, add_zero] at ha
      exact ha.symm
    obtain ⟨i, hiS, hiPole, hiMismatch⟩ := ZeroRemainderWitness.exists_pole_mismatch
      dom r (fun i ↦ (q γ).eval (dom i)) γ (S γ) C hxcode hqcode he (hno γ hγG)
    refine ⟨i, ?_, hiPole⟩
    intro hiH
    have hqP : q γ ∈ P := Finset.mem_image.mpr ⟨γ, hγ, rfl⟩
    have hiA := (hH i).mp hiH (q γ) hqP
    exact hiMismatch ((hA _ i).mp hiA).symm
  have hbudget := LinearApproximantBudget.production_budget dom r P Z R A S q c H
    hH hpolySize hpoly hpole hfour hempty hw
  have hsplit : Z.card + R.card = G.card :=
    Finset.card_filter_add_card_filter_not (s := G) (fun γ ↦ c γ = 0)
  omega

end FullOwnerLinearBudget

#print axioms FullOwnerLinearBudget.bad_scalar_budget

namespace FullOwnerLinearBudget

open Polynomial

/-- Specializes the linear-owner budget to arbitrary Reed-Solomon decoded codewords. -/
theorem reed_solomon_bad_scalar_budget
    {F : Type*} [Field F] [DecidableEq F]
    (dom : Fin 1073741824 ↪ F) (r : Fin 1073741824 → F)
    (G : Finset F) (pf : F → Fin 1073741824 → F)
    (S : F → Finset (Fin 1073741824))
    (hcode : ∀ γ ∈ G, pf γ ∈ ReedSolomon.code dom 268435456)
    (hsize : ∀ γ ∈ G, 592794966 ≤ (S γ).card)
    (hagree : ∀ γ ∈ G, ∀ i ∈ S γ, pf γ i = (dom i + γ) * r i)
    (hno : ∀ γ ∈ G, ¬ ∃ c₀ ∈ ReedSolomon.code dom 268435456,
      ∃ c₁ ∈ ReedSolomon.code dom 268435456, ∀ i ∈ S γ,
        c₀ i = dom i * r i ∧ c₁ i = r i) :
    G.card ≤ 1073741824 := by
  classical
  have hpoly : ∀ γ ∈ G, ∃ p : F[X], p.natDegree < 268435456 ∧
      ∀ i, pf γ i = p.eval (dom i) := by
    intro γ hγ
    obtain ⟨p, hp, he⟩ := ReedSolomon.mem_code_iff_exists_polynomial_of_ne_zero.mp
      (hcode γ hγ)
    exact ⟨p, hp, fun i ↦ congrFun he i⟩
  let p : F → F[X] := fun γ ↦ if hγ : γ ∈ G then Classical.choose (hpoly γ hγ) else 0
  have hspec : ∀ γ ∈ G, (p γ).natDegree < 268435456 ∧
      ∀ i, pf γ i = (p γ).eval (dom i) := by
    intro γ hγ
    simpa only [p, dif_pos hγ] using Classical.choose_spec (hpoly γ hγ)
  have hC : ∀ p : F[X], p.natDegree < 268435456 →
      (fun i ↦ p.eval (dom i)) ∈ ReedSolomon.code dom 268435456 := by
    intro p hp
    exact ReedSolomon.mem_code_of_polynomial_of_natDegree_lt_of_eval p hp (fun _ ↦ rfl)
  apply bad_scalar_budget dom r (ReedSolomon.code dom 268435456) hC G p S
    (fun γ hγ ↦ (hspec γ hγ).1) hsize ?_ hno
  intro γ hγ i hi
  rw [← (hspec γ hγ).2 i]
  exact hagree γ hγ i hi

end FullOwnerLinearBudget

#print axioms FullOwnerLinearBudget.reed_solomon_bad_scalar_budget
namespace Production

open ArkLib.ProximityGap.PrizeShapePrimeP30
open ArkLib.ProximityGap.Frontier.P1RateQuarterScaleArithmetic
open ArkLib.ProximityGap.Frontier.P1RateQuarterSharedFreshCoordinate
open ArkLib.ProximityGap.Frontier.P1RateQuarterPencilCountCharge

local instance : Fact (Nat.Prime P) := ⟨prime_P⟩

/-- The canonical bad family has at most N scalars when its received rows are (x*r,r). -/
theorem badFamilyData_linear_owner_card_le
    (dom : Fin N ↪ F) (r : Fin N → F) (G : Finset F)
    (Sf : F → Finset (Fin N)) (pf : F → Fin N → F)
    (hdata : BadFamilyData dom (fun i ↦ dom i * r i) r G Sf pf) :
    G.card ≤ N := by
  apply FullOwnerLinearBudget.reed_solomon_bad_scalar_budget dom r G pf Sf
  · intro γ hγ
    exact (hdata γ hγ).2.1
  · intro γ hγ
    simpa only [predecessorThreshold_eq] using (hdata γ hγ).1
  · intro γ hγ i hi
    simpa only [add_mul] using (hdata γ hγ).2.2.1 i hi
  · intro γ hγ
    exact (hdata γ hγ).2.2.2

end Production

#print axioms Production.badFamilyData_linear_owner_card_le

end ArkLib.ProximityGap.Frontier.P1RateQuarterLinearOwnerBudget
