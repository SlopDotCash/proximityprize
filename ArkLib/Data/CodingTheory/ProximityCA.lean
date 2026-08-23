/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.Data.Finset.Card
import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic.Choose
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

/-!
# Correlated-agreement counting leaves

Verified generic linear-code leaves for the proximity-prize correlated-agreement track.
The core arguments are adapted from the public IoTeX `rs-proximity-gaps` Lean
development (Apache-2.0): distinct bad line parameters can be solved as a
two-by-two linear system, producing a joint codeword pair and contradicting the
joint-distance premise.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

namespace ProximityPrizeCA

open Finset Fintype

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Field F] [DecidableEq F]

/-- The agreement set of two words. -/
def agreeSet (f g : ι → F) : Finset ι :=
  Finset.univ.filter (fun x => f x = g x)

/-- The joint agreement set of two word pairs. -/
def jointAgreeSet (f₁ f₂ g₁ g₂ : ι → F) : Finset ι :=
  Finset.univ.filter (fun x => f₁ x = g₁ x ∧ f₂ x = g₂ x)

/-- The affine line word `f₁ + γ • f₂`. -/
def linComb (f₁ f₂ : ι → F) (γ : F) : ι → F :=
  fun x => f₁ x + γ * f₂ x

/-- Package two words as a single word over the product alphabet. -/
def pairWord (f₁ f₂ : ι → F) : ι → F × F :=
  fun x => (f₁ x, f₂ x)

/-- A Hamming-distance lower bound for paired words is the same as an upper
bound on the joint agreement set. -/
theorem jointAgreeSet_card_add_lt_of_hammingDist_gt
    {f₁ f₂ g₁ g₂ : ι → F} {w : ℕ}
    (h : w < hammingDist (pairWord f₁ f₂) (pairWord g₁ g₂)) :
    (jointAgreeSet f₁ f₂ g₁ g₂).card + w < Fintype.card ι := by
  classical
  have hpartition :
      (jointAgreeSet f₁ f₂ g₁ g₂).card +
        hammingDist (pairWord f₁ f₂) (pairWord g₁ g₂) = Fintype.card ι := by
    simpa [jointAgreeSet, pairWord, hammingDist] using
      (Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset ι))
        (p := fun x : ι => f₁ x = g₁ x ∧ f₂ x = g₂ x))
  omega

/-- If two words have Hamming distance at most `d`, then they agree on at
least `|ι| - d` coordinates. -/
theorem card_le_agreeSet_card_add_of_hammingDist_le
    {f g : ι → F} {d : ℕ} (h : hammingDist f g ≤ d) :
    Fintype.card ι ≤ (agreeSet f g).card + d := by
  classical
  have hpartition :
      (agreeSet f g).card + hammingDist f g = Fintype.card ι := by
    simpa [agreeSet, hammingDist] using
      (Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset ι)) (p := fun x : ι => f x = g x))
  omega

/-- A Hamming-distance lower bound is the same as an upper bound on the
agreement set. -/
theorem agreeSet_card_add_lt_of_hammingDist_gt
    {f g : ι → F} {w : ℕ} (h : w < hammingDist f g) :
    (agreeSet f g).card + w < Fintype.card ι := by
  classical
  have hpartition :
      (agreeSet f g).card + hammingDist f g = Fintype.card ι := by
    simpa [agreeSet, hammingDist] using
      (Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset ι)) (p := fun x : ι => f x = g x))
  omega

/-- Inclusion-exclusion in the form used by the halved-threshold CA argument. -/
theorem card_inter_add_card_univ_ge (A B : Finset ι) :
    (A ∩ B).card + Fintype.card ι ≥ A.card + B.card := by
  have h := (Finset.card_union_add_card_inter A B).symm
  have hle : (A ∪ B).card ≤ Fintype.card ι := Finset.card_le_univ _
  omega

/-- Half-threshold correlated agreement, two-parameter contradiction. -/
theorem ca_halved
    (C : Submodule F (ι → F))
    (f₁ f₂ : ι → F) (d : ℕ)
    (hprem : ∀ g₁ ∈ C, ∀ g₂ ∈ C,
      (jointAgreeSet f₁ f₂ g₁ g₂).card + 2 * d < Fintype.card ι)
    {γ₁ γ₂ : F} (hne : γ₁ ≠ γ₂)
    {h₁ h₂ : ι → F} (hh₁ : h₁ ∈ C) (hh₂ : h₂ ∈ C)
    (hS₁ : Fintype.card ι ≤ (agreeSet (linComb f₁ f₂ γ₁) h₁).card + d)
    (hS₂ : Fintype.card ι ≤ (agreeSet (linComb f₁ f₂ γ₂) h₂).card + d) :
    False := by
  set S₁ := agreeSet (linComb f₁ f₂ γ₁) h₁ with hS₁_def
  set S₂ := agreeSet (linComb f₁ f₂ γ₂) h₂ with hS₂_def
  have hie := card_inter_add_card_univ_ge (ι := ι) S₁ S₂
  have hγ : γ₁ - γ₂ ≠ 0 := sub_ne_zero.mpr hne
  set g₂ : ι → F := (γ₁ - γ₂)⁻¹ • (h₁ - h₂) with hg₂_def
  set g₁ : ι → F := h₁ - γ₁ • g₂ with hg₁_def
  have hg₂C : g₂ ∈ C := C.smul_mem _ (C.sub_mem hh₁ hh₂)
  have hg₁C : g₁ ∈ C := C.sub_mem hh₁ (C.smul_mem _ hg₂C)
  have hsub : S₁ ∩ S₂ ⊆ jointAgreeSet f₁ f₂ g₁ g₂ := by
    intro x hx
    rw [Finset.mem_inter] at hx
    simp only [S₁, S₂, agreeSet, linComb, Finset.mem_filter, mem_univ, true_and] at hx
    obtain ⟨eq1, eq2⟩ := hx
    have hf₂ : f₂ x = g₂ x := by
      simp only [hg₂_def, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      rw [eq_comm, inv_mul_eq_div, div_eq_iff hγ]
      rw [eq_comm, mul_comm]
      linear_combination eq1 - eq2
    have hf₁ : f₁ x = g₁ x := by
      simp only [hg₁_def, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [← hf₂]
      linear_combination eq1
    simp only [jointAgreeSet, Finset.mem_filter, mem_univ, true_and]
    exact ⟨hf₁, hf₂⟩
  have hcard : (S₁ ∩ S₂).card ≤ (jointAgreeSet f₁ f₂ g₁ g₂).card :=
    Finset.card_le_card hsub
  have hcontra := hprem g₁ hg₁C g₂ hg₂C
  omega

open Classical in
/-- Half-threshold correlated agreement, count form. -/
theorem ca_halved_count_le_one [Fintype F]
    (C : Submodule F (ι → F))
    (f₁ f₂ : ι → F) (d : ℕ)
    (hprem : ∀ g₁ ∈ C, ∀ g₂ ∈ C,
      (jointAgreeSet f₁ f₂ g₁ g₂).card + 2 * d < Fintype.card ι) :
    ((Finset.univ : Finset F).filter
      (fun γ => ∃ h ∈ C, Fintype.card ι ≤ (agreeSet (linComb f₁ f₂ γ) h).card + d)).card
    ≤ 1 := by
  rw [Finset.card_le_one]
  intro γ₁ hγ₁ γ₂ hγ₂
  rw [Finset.mem_filter] at hγ₁ hγ₂
  obtain ⟨_, h₁, hh₁, hA₁⟩ := hγ₁
  obtain ⟨_, h₂, hh₂, hA₂⟩ := hγ₂
  by_contra hne
  exact ca_halved C f₁ f₂ d hprem hne hh₁ hh₂ hA₁ hA₂

open Classical in
/-- Half-threshold correlated agreement, with the separation premise stated as a Hamming-distance
lower bound on paired words. -/
theorem ca_halved_count_le_one_of_hammingDist [Fintype F]
    (C : Submodule F (ι → F))
    (f₁ f₂ : ι → F) (d : ℕ)
    (hprem : ∀ g₁ ∈ C, ∀ g₂ ∈ C,
      2 * d < hammingDist (pairWord f₁ f₂) (pairWord g₁ g₂)) :
    ((Finset.univ : Finset F).filter
      (fun γ => ∃ h ∈ C, Fintype.card ι ≤ (agreeSet (linComb f₁ f₂ γ) h).card + d)).card
    ≤ 1 :=
  ca_halved_count_le_one C f₁ f₂ d
    (fun g₁ hg₁ g₂ hg₂ =>
      jointAgreeSet_card_add_lt_of_hammingDist_gt (hprem g₁ hg₁ g₂ hg₂))

private def IsBadWitness
    (C : Submodule F (ι → F))
    (f₁ f₂ : ι → F) (w : ℕ) (γ : F)
    (h : ι → F) (A : Finset ι) : Prop :=
  h ∈ C ∧ A.card = Fintype.card ι - w ∧ A ⊆ agreeSet (linComb f₁ f₂ γ) h

omit [DecidableEq ι] in
private lemma exists_witness
    (C : Submodule F (ι → F))
    (f₁ f₂ : ι → F) (w : ℕ) (γ : F)
    (hbad : ∃ h ∈ C, Fintype.card ι ≤ (agreeSet (linComb f₁ f₂ γ) h).card + w) :
    ∃ (h : ι → F) (A : Finset ι), IsBadWitness C f₁ f₂ w γ h A := by
  obtain ⟨h, hC, hcard⟩ := hbad
  have hagree_card : Fintype.card ι - w ≤ (agreeSet (linComb f₁ f₂ γ) h).card := by
    omega
  obtain ⟨A, hAsub, hAcard⟩ :=
    Finset.exists_subset_card_eq hagree_card
  exact ⟨h, A, hC, hAcard, hAsub⟩

private theorem ca_equal_threshold_pair
    (C : Submodule F (ι → F))
    (f₁ f₂ : ι → F) (w : ℕ)
    (hprem : ∀ g₁ ∈ C, ∀ g₂ ∈ C,
      (jointAgreeSet f₁ f₂ g₁ g₂).card + w < Fintype.card ι)
    {γ₁ γ₂ : F} (hne : γ₁ ≠ γ₂)
    {h₁ h₂ : ι → F} (hh₁ : h₁ ∈ C) (hh₂ : h₂ ∈ C)
    {A : Finset ι} (hAcard : A.card + w = Fintype.card ι)
    (hAgree₁ : A ⊆ agreeSet (linComb f₁ f₂ γ₁) h₁)
    (hAgree₂ : A ⊆ agreeSet (linComb f₁ f₂ γ₂) h₂) :
    False := by
  have hγ : γ₁ - γ₂ ≠ 0 := sub_ne_zero.mpr hne
  set g₂ : ι → F := (γ₁ - γ₂)⁻¹ • (h₁ - h₂) with hg₂_def
  set g₁ : ι → F := h₁ - γ₁ • g₂ with hg₁_def
  have hg₂C : g₂ ∈ C := C.smul_mem _ (C.sub_mem hh₁ hh₂)
  have hg₁C : g₁ ∈ C := C.sub_mem hh₁ (C.smul_mem _ hg₂C)
  have hsub : A ⊆ jointAgreeSet f₁ f₂ g₁ g₂ := by
    intro x hxA
    have h1 : f₁ x + γ₁ * f₂ x = h₁ x := by
      have := hAgree₁ hxA
      simp only [agreeSet, linComb, Finset.mem_filter, mem_univ, true_and] at this
      exact this
    have h2 : f₁ x + γ₂ * f₂ x = h₂ x := by
      have := hAgree₂ hxA
      simp only [agreeSet, linComb, Finset.mem_filter, mem_univ, true_and] at this
      exact this
    have hf₂ : f₂ x = g₂ x := by
      simp only [hg₂_def, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      rw [eq_comm, inv_mul_eq_div, div_eq_iff hγ]
      rw [eq_comm, mul_comm]
      linear_combination h1 - h2
    have hf₁ : f₁ x = g₁ x := by
      simp only [hg₁_def, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [← hf₂]
      linear_combination h1
    simp only [jointAgreeSet, Finset.mem_filter, mem_univ, true_and]
    exact ⟨hf₁, hf₂⟩
  have hcard : A.card ≤ (jointAgreeSet f₁ f₂ g₁ g₂).card :=
    Finset.card_le_card hsub
  have hcontra := hprem g₁ hg₁C g₂ hg₂C
  omega

/-- Equal-threshold correlated-agreement upper bound. -/
theorem ca_equal_threshold
    (C : Submodule F (ι → F))
    (f₁ f₂ : ι → F) (w : ℕ) (hw : w ≤ Fintype.card ι)
    (hprem : ∀ g₁ ∈ C, ∀ g₂ ∈ C,
      (jointAgreeSet f₁ f₂ g₁ g₂).card + w < Fintype.card ι)
    (Γ : Finset F)
    (hbad : ∀ γ ∈ Γ,
      ∃ h ∈ C, Fintype.card ι ≤ (agreeSet (linComb f₁ f₂ γ) h).card + w) :
    Γ.card ≤ Nat.choose (Fintype.card ι) w := by
  classical
  let pickH : ∀ γ ∈ Γ, ι → F := fun γ hγ =>
    Classical.choose (exists_witness C f₁ f₂ w γ (hbad γ hγ))
  let pickA : ∀ γ ∈ Γ, Finset ι := fun γ hγ =>
    Classical.choose
      (Classical.choose_spec (exists_witness C f₁ f₂ w γ (hbad γ hγ)))
  have pickSpec : ∀ γ (hγ : γ ∈ Γ),
      IsBadWitness C f₁ f₂ w γ (pickH γ hγ) (pickA γ hγ) := fun γ hγ =>
    Classical.choose_spec
      (Classical.choose_spec (exists_witness C f₁ f₂ w γ (hbad γ hγ)))
  have hmem : ∀ γ (hγ : γ ∈ Γ),
      pickA γ hγ ∈ (Finset.univ : Finset ι).powersetCard (Fintype.card ι - w) := by
    intro γ hγ
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, (pickSpec γ hγ).2.1⟩
  have hinj : Set.InjOn (fun γ => if hγ : γ ∈ Γ then pickA γ hγ else ∅) Γ := by
    intro γ₁ hmem₁ γ₂ hmem₂ hAeq
    have hγ₁ : γ₁ ∈ Γ := hmem₁
    have hγ₂ : γ₂ ∈ Γ := hmem₂
    by_contra hne
    simp only [dif_pos hγ₁, dif_pos hγ₂] at hAeq
    set A := pickA γ₁ hγ₁ with hA_def
    have hA_card : A.card + w = Fintype.card ι := by
      have : A.card = Fintype.card ι - w := (pickSpec γ₁ hγ₁).2.1
      omega
    obtain ⟨hC₁, _, hsub₁⟩ := pickSpec γ₁ hγ₁
    obtain ⟨hC₂, _, hsub₂_raw⟩ := pickSpec γ₂ hγ₂
    have hsub₂ : A ⊆ agreeSet (linComb f₁ f₂ γ₂) (pickH γ₂ hγ₂) := by
      rw [hAeq]
      exact hsub₂_raw
    exact ca_equal_threshold_pair C f₁ f₂ w hprem hne hC₁ hC₂ hA_card hsub₁ hsub₂
  calc Γ.card
      ≤ ((Finset.univ : Finset ι).powersetCard (Fintype.card ι - w)).card := by
        refine Finset.card_le_card_of_injOn
          (fun γ => if hγ : γ ∈ Γ then pickA γ hγ else ∅) ?_ hinj
        intro γ hγ
        rw [Finset.mem_coe] at hγ
        simp only [dif_pos hγ, Finset.mem_coe]
        exact hmem γ hγ
    _ = Nat.choose (Fintype.card ι) (Fintype.card ι - w) := by
        rw [Finset.card_powersetCard, Finset.card_univ]
    _ = Nat.choose (Fintype.card ι) w := Nat.choose_symm hw

/-- Equal-threshold correlated-agreement upper bound, with the separation premise stated as a
Hamming-distance lower bound on paired words. -/
theorem ca_equal_threshold_of_hammingDist
    (C : Submodule F (ι → F))
    (f₁ f₂ : ι → F) (w : ℕ) (hw : w ≤ Fintype.card ι)
    (hprem : ∀ g₁ ∈ C, ∀ g₂ ∈ C,
      w < hammingDist (pairWord f₁ f₂) (pairWord g₁ g₂))
    (Γ : Finset F)
    (hbad : ∀ γ ∈ Γ,
      ∃ h ∈ C, Fintype.card ι ≤ (agreeSet (linComb f₁ f₂ γ) h).card + w) :
    Γ.card ≤ Nat.choose (Fintype.card ι) w :=
  ca_equal_threshold C f₁ f₂ w hw
    (fun g₁ hg₁ g₂ hg₂ =>
      jointAgreeSet_card_add_lt_of_hammingDist_gt (hprem g₁ hg₁ g₂ hg₂))
    Γ hbad

/-- The joint agreement set is contained in the second component's agreement set. -/
theorem jointAgreeSet_subset_agreeSet_snd (f₁ f₂ g₁ g₂ : ι → F) :
    jointAgreeSet f₁ f₂ g₁ g₂ ⊆ agreeSet f₂ g₂ := by
  intro x hx
  simp only [jointAgreeSet, agreeSet, Finset.mem_filter, mem_univ, true_and] at hx ⊢
  exact hx.2

/-- If the second word is `2 * d`-far from every codeword, then any pair with it as
second component satisfies the halved-threshold joint-distance premise. -/
theorem far_implies_joint_far
    (C : Submodule F (ι → F))
    (rest fᵢ : ι → F) (d : ℕ)
    (hfar : ∀ g ∈ C, (agreeSet fᵢ g).card + 2 * d < Fintype.card ι) :
    ∀ g₁ ∈ C, ∀ g₂ ∈ C,
      (jointAgreeSet rest fᵢ g₁ g₂).card + 2 * d < Fintype.card ι := by
  intro g₁ _hg₁ g₂ hg₂
  have hsub := jointAgreeSet_subset_agreeSet_snd rest fᵢ g₁ g₂
  have hcard := Finset.card_le_card hsub
  have hg := hfar g₂ hg₂
  omega

/-- Hamming-distance form of `far_implies_joint_far`. -/
theorem far_implies_joint_far_of_hammingDist
    (C : Submodule F (ι → F))
    (rest fᵢ : ι → F) (d : ℕ)
    (hfar : ∀ g ∈ C, 2 * d < hammingDist fᵢ g) :
    ∀ g₁ ∈ C, ∀ g₂ ∈ C,
      (jointAgreeSet rest fᵢ g₁ g₂).card + 2 * d < Fintype.card ι :=
  far_implies_joint_far C rest fᵢ d
    (fun g hg => agreeSet_card_add_lt_of_hammingDist_gt (hfar g hg))

/-- Per-coordinate batch correlated agreement: after fixing an arbitrary `rest`,
there are not two distinct coefficients that make `rest + α • fᵢ` close to the
code, provided `fᵢ` itself is `2 * d`-far from the code. -/
theorem batch_ca_per_coord
    (C : Submodule F (ι → F))
    (rest fᵢ : ι → F) (d : ℕ)
    (hfar : ∀ g ∈ C, (agreeSet fᵢ g).card + 2 * d < Fintype.card ι)
    {α₁ α₂ : F} (hne : α₁ ≠ α₂)
    {c₁ c₂ : ι → F} (hc₁ : c₁ ∈ C) (hc₂ : c₂ ∈ C)
    (hA₁ : Fintype.card ι ≤ (agreeSet (linComb rest fᵢ α₁) c₁).card + d)
    (hA₂ : Fintype.card ι ≤ (agreeSet (linComb rest fᵢ α₂) c₂).card + d) :
    False :=
  ca_halved C rest fᵢ d (far_implies_joint_far C rest fᵢ d hfar) hne hc₁ hc₂ hA₁ hA₂

/-- Hamming-distance form of the per-coordinate batch CA contradiction. -/
theorem batch_ca_per_coord_of_hammingDist
    (C : Submodule F (ι → F))
    (rest fᵢ : ι → F) (d : ℕ)
    (hfar : ∀ g ∈ C, 2 * d < hammingDist fᵢ g)
    {α₁ α₂ : F} (hne : α₁ ≠ α₂)
    {c₁ c₂ : ι → F} (hc₁ : c₁ ∈ C) (hc₂ : c₂ ∈ C)
    (hA₁ : Fintype.card ι ≤ (agreeSet (linComb rest fᵢ α₁) c₁).card + d)
    (hA₂ : Fintype.card ι ≤ (agreeSet (linComb rest fᵢ α₂) c₂).card + d) :
    False :=
  batch_ca_per_coord C rest fᵢ d
    (fun g hg => agreeSet_card_add_lt_of_hammingDist_gt (hfar g hg))
    hne hc₁ hc₂ hA₁ hA₂

/-- Contrapositive singleton form for the per-coordinate batch CA argument. -/
theorem batch_ca_at_most_one
    (C : Submodule F (ι → F))
    (rest fᵢ : ι → F) (d : ℕ)
    (hfar : ∀ g ∈ C, (agreeSet fᵢ g).card + 2 * d < Fintype.card ι)
    {α₁ α₂ : F}
    (hα₁ : ∃ c ∈ C, Fintype.card ι ≤ (agreeSet (linComb rest fᵢ α₁) c).card + d)
    (hα₂ : ∃ c ∈ C, Fintype.card ι ≤ (agreeSet (linComb rest fᵢ α₂) c).card + d) :
    α₁ = α₂ := by
  by_contra hne
  obtain ⟨c₁, hc₁, hA₁⟩ := hα₁
  obtain ⟨c₂, hc₂, hA₂⟩ := hα₂
  exact batch_ca_per_coord C rest fᵢ d hfar hne hc₁ hc₂ hA₁ hA₂

open Classical in
/-- For fixed `rest`, the bad coefficient set for one batch coordinate has cardinality at
most one. -/
theorem batch_ca_per_coord_bad_card [Fintype F]
    (C : Submodule F (ι → F))
    (rest fᵢ : ι → F) (d : ℕ)
    (hfar : ∀ g ∈ C, (agreeSet fᵢ g).card + 2 * d < Fintype.card ι) :
    ((Finset.univ : Finset F).filter
      (fun α => ∃ c ∈ C, Fintype.card ι ≤
        (agreeSet (linComb rest fᵢ α) c).card + d)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro α₁ hα₁ α₂ hα₂
  rw [Finset.mem_filter] at hα₁ hα₂
  exact batch_ca_at_most_one C rest fᵢ d hfar hα₁.2 hα₂.2

open Classical in
/-- Hamming-distance form of `batch_ca_per_coord_bad_card`. -/
theorem batch_ca_per_coord_bad_card_of_hammingDist [Fintype F]
    (C : Submodule F (ι → F))
    (rest fᵢ : ι → F) (d : ℕ)
    (hfar : ∀ g ∈ C, 2 * d < hammingDist fᵢ g) :
    ((Finset.univ : Finset F).filter
      (fun α => ∃ c ∈ C, Fintype.card ι ≤
        (agreeSet (linComb rest fᵢ α) c).card + d)).card ≤ 1 :=
  batch_ca_per_coord_bad_card C rest fᵢ d
    (fun g hg => agreeSet_card_add_lt_of_hammingDist_gt (hfar g hg))

/-- A finite union of bad scalar sets, one per batch coordinate, has cardinality bounded by
the number of coordinates when each coordinate contributes at most one bad scalar. -/
theorem batch_ca_bad_count {κ : Type*} [Fintype κ] [DecidableEq κ]
    {A : Type*} [DecidableEq A]
    (bad : κ → Finset A) (hbad : ∀ i, (bad i).card ≤ 1) :
    (Finset.univ.biUnion bad).card ≤ Fintype.card κ := by
  calc
    (Finset.univ.biUnion bad).card
        ≤ Finset.univ.sum (fun i => (bad i).card) := Finset.card_biUnion_le
    _ ≤ Finset.univ.sum (fun _ : κ => 1) :=
        Finset.sum_le_sum fun i _ => hbad i
    _ = Fintype.card κ := by simp

open Classical in
/-- Fixed-rest aggregate batch CA bound. For each coordinate `i`, if `f i` is
`2 * d`-far from `C`, then the union of all fixed-rest bad scalar sets has size at
most the number of coordinates. This is the reusable counting core behind the
tuple-form batch CA probability statement. -/
theorem batch_ca_aggregate [Fintype F]
    (C : Submodule F (ι → F))
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (rest : κ → ι → F) (f : κ → ι → F) (d : ℕ)
    (hfar : ∀ i, ∀ g ∈ C, (agreeSet (f i) g).card + 2 * d < Fintype.card ι) :
    (Finset.univ.biUnion (fun i =>
      (Finset.univ : Finset F).filter
        (fun α => ∃ c ∈ C,
          Fintype.card ι ≤ (agreeSet (linComb (rest i) (f i) α) c).card + d))).card
    ≤ Fintype.card κ :=
  batch_ca_bad_count
    (fun i => (Finset.univ : Finset F).filter
      (fun α => ∃ c ∈ C,
        Fintype.card ι ≤ (agreeSet (linComb (rest i) (f i) α) c).card + d))
    (fun i => batch_ca_per_coord_bad_card C (rest i) (f i) d (hfar i))

open Classical in
/-- Hamming-distance form of `batch_ca_aggregate`. -/
theorem batch_ca_aggregate_of_hammingDist [Fintype F]
    (C : Submodule F (ι → F))
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (rest : κ → ι → F) (f : κ → ι → F) (d : ℕ)
    (hfar : ∀ i, ∀ g ∈ C, 2 * d < hammingDist (f i) g) :
    (Finset.univ.biUnion (fun i =>
      (Finset.univ : Finset F).filter
        (fun α => ∃ c ∈ C,
          Fintype.card ι ≤ (agreeSet (linComb (rest i) (f i) α) c).card + d))).card
    ≤ Fintype.card κ :=
  batch_ca_aggregate C rest f d
    (fun i g hg => agreeSet_card_add_lt_of_hammingDist_gt (hfar i g hg))

end ProximityPrizeCA
