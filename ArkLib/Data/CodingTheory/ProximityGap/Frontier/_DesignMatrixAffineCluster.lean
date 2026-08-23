/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.HighMultiplicityBadCount
import ArkLib.Data.CodingTheory.ProximityGap.Errors

/-!
# Affine clusters of MCA witness polynomials have at most one point per pin coordinate

View a Reed–Solomon witness polynomial `f_γ` through its scalar and coefficient vector.
Agreement at coordinate `i` is incidence with the affine hyperplane

`f_γ(x_i) = u₀(i) + γ u₁(i)`.

If a family of such points lies on one nonvertical affine line, its polynomials have the form
`c₀ + γ c₁` for fixed codewords `c₀,c₁`.  This file proves the exact cluster bound.
Let `D` be the locked coordinates where both `c₀ = u₀` and `c₁ = u₁`.  Every witness
set has at least `a - |D|` coordinates outside `D`; even when `|D| ≥ a`, the MCA no-joint clause
forces at least one such coordinate.  Outside `D`, agreement pins at most one scalar.  Hence

`max(1, a - |D|) * |G| ≤ |supp(u₁-c₁)|`,

and in particular `|G| ≤ |supp(u₁-c₁)| ≤ n`.

The first inequality strengthens the previously landed per-pencil heavy-scalar bound precisely in
its excluded saturated branch `|D| ≥ a`: the no-joint clause still supplies one pin there.  It
also shows why a cluster count alone cannot close the prize: one must bound how many affine
clusters the witness points occupy.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset
open scoped NNReal

namespace ProximityGap.Frontier.DesignMatrixAffineCluster

open ProximityGap
open ArkLib.ProximityGap.HighMultiplicity

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- Coordinates on which the codeword pencil `c₀ + γ c₁` agrees with the word line
`u₀ + γ u₁` for every scalar. -/
noncomputable def lockedSet (c₀ c₁ u₀ u₁ : Fin n → F) : Finset (Fin n) :=
  Finset.univ.filter (fun i => c₀ i = u₀ i ∧ c₁ i = u₁ i)

open Classical in
/-- The exact part of the existing `mcaEvent` bad-scalar set whose event has a witness explained
by one fixed codeword pencil `c₀ + γ c₁`.  The cardinality, agreement, and no-joint clauses
are the three clauses of `mcaEvent`; only its existential codeword is pinned to this pencil. -/
noncomputable def affineClusterBadScalars (C : Submodule F (Fin n → F)) (δ : ℝ≥0)
    (c₀ c₁ u₀ u₁ : Fin n → F) : Finset F :=
  Finset.univ.filter (fun γ => ∃ S : Finset (Fin n),
    (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ (S.card : ℝ≥0) ∧
    (∀ i ∈ S, c₀ i + γ * c₁ i = u₀ i + γ * u₁ i) ∧
    ¬ pairJointAgreesOn (C : Set (Fin n → F)) S u₀ u₁)

open Classical in
/-- A scalar in `affineClusterBadScalars` is genuinely `mcaEvent`-bad.  Thus the cluster theorem
below is about an explicit subfamily of the production event, not a detached incidence surrogate. -/
theorem affineClusterBadScalars_subset_mcaEvent
    (C : Submodule F (Fin n → F)) (δ : ℝ≥0) (c₀ c₁ u₀ u₁ : Fin n → F)
    (hc₀ : c₀ ∈ C) (hc₁ : c₁ ∈ C) :
    affineClusterBadScalars C δ c₀ c₁ u₀ u₁ ⊆
      Finset.univ.filter (fun γ : F =>
        mcaEvent (F := F) (C : Set (Fin n → F)) δ u₀ u₁ γ) := by
  classical
  intro γ hγ
  rw [affineClusterBadScalars, Finset.mem_filter] at hγ
  obtain ⟨_, S, hcard, hagree, hno⟩ := hγ
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, S, hcard, ?_, hno⟩
  refine ⟨fun i => c₀ i + γ * c₁ i, C.add_mem hc₀ (C.smul_mem γ hc₁), ?_⟩
  intro i hi
  simpa [smul_eq_mul] using hagree i hi

/-- **Affine-cluster multiplicity bound.**

For every `γ ∈ G`, suppose the fixed codeword pencil `c₀ + γ c₁` explains the word
line on a witness `S γ` of size at least `a`, while `(u₀,u₁)` has no joint codeword
explanation on that same witness.  Then every scalar owns at least
`max 1 (a - |lockedSet|)` distinct pin coordinates, and different scalars own disjoint pins. -/
theorem affineCluster_card_mul_le_support
    (C : Submodule F (Fin n → F)) (c₀ c₁ u₀ u₁ : Fin n → F)
    (hc₀ : c₀ ∈ C) (hc₁ : c₁ ∈ C) (a : ℕ) (G : Finset F)
    (S : F → Finset (Fin n))
    (hsize : ∀ γ ∈ G, a ≤ (S γ).card)
    (hagree : ∀ γ ∈ G, ∀ i ∈ S γ,
      c₀ i + γ * c₁ i = u₀ i + γ * u₁ i)
    (hno : ∀ γ ∈ G,
      ¬ pairJointAgreesOn (C : Set (Fin n → F)) (S γ) u₀ u₁) :
    max 1 (a - (lockedSet c₀ c₁ u₀ u₁).card) * G.card
      ≤ (Finset.univ.filter (fun i => u₁ i - c₁ i ≠ 0)).card := by
  classical
  let e₀ : Fin n → F := fun i => u₀ i - c₀ i
  let e₁ : Fin n → F := fun i => u₁ i - c₁ i
  let D : Finset (Fin n) := lockedSet c₀ c₁ u₀ u₁
  let μ : ℕ := max 1 (a - D.card)
  have hGsub : G ⊆ Finset.univ.filter (fun γ : F => μ ≤ mult e₀ e₁ γ) := by
    intro γ hγ
    let T : Finset (Fin n) := S γ \ D
    have hTpos : 1 ≤ T.card := by
      rw [Nat.one_le_iff_ne_zero]
      intro hTzero
      have hTempty : T = ∅ := Finset.card_eq_zero.mp hTzero
      apply hno γ hγ
      refine ⟨c₀, hc₀, c₁, hc₁, ?_⟩
      intro i hi
      have hiD : i ∈ D := by
        by_contra hiNotD
        have : i ∈ T := Finset.mem_sdiff.mpr ⟨hi, hiNotD⟩
        simpa [hTempty] using this
      simp only [D, lockedSet, Finset.mem_filter, Finset.mem_univ, true_and] at hiD
      exact hiD
    have hTsub : T ⊆ Finset.univ.filter
        (fun i => e₁ i ≠ 0 ∧ e₀ i + γ * e₁ i = 0) := by
      intro i hi
      obtain ⟨hiS, hiNotD⟩ := Finset.mem_sdiff.mp hi
      have hag := hagree γ hγ i hiS
      have hroot : e₀ i + γ * e₁ i = 0 := by
        dsimp [e₀, e₁]
        linear_combination -hag
      have he₁ : e₁ i ≠ 0 := by
        intro he₁zero
        have he₀zero : e₀ i = 0 := by
          rw [he₁zero, mul_zero, add_zero] at hroot
          exact hroot
        apply hiNotD
        simp only [D, lockedSet, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨?_, ?_⟩
        · dsimp [e₀] at he₀zero
          exact (sub_eq_zero.mp he₀zero).symm
        · dsimp [e₁] at he₁zero
          exact (sub_eq_zero.mp he₁zero).symm
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, he₁, hroot⟩
    have hsubCard : a - D.card ≤ T.card := by
      have hcover : S γ ⊆ D ∪ T := by
        intro i hi
        by_cases hiD : i ∈ D
        · exact Finset.mem_union.mpr (Or.inl hiD)
        · exact Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hi, hiD⟩))
      have hcard : (S γ).card ≤ D.card + T.card :=
        le_trans (Finset.card_le_card hcover) (Finset.card_union_le D T)
      exact (Nat.sub_le_iff_le_add).mpr
        (by simpa [Nat.add_comm] using le_trans (hsize γ hγ) hcard)
    have hμT : μ ≤ T.card := max_le hTpos hsubCard
    have hTmult : T.card ≤ mult e₀ e₁ γ := Finset.card_le_card hTsub
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, le_trans hμT hTmult⟩
  have hcard : G.card ≤
      (Finset.univ.filter (fun γ : F => μ ≤ mult e₀ e₁ γ)).card :=
    Finset.card_le_card hGsub
  have hmul : μ * G.card ≤
      μ * (Finset.univ.filter (fun γ : F => μ ≤ mult e₀ e₁ γ)).card :=
    Nat.mul_le_mul_left μ hcard
  have hhigh := card_highMult_mul_le e₀ e₁ μ
  change μ * G.card ≤ (Finset.univ.filter (fun i => e₁ i ≠ 0)).card
  exact le_trans hmul hhigh

/-- Every affine cluster of MCA witness polynomials has at most `n` points.  The sharper theorem
above also records the number of pin coordinates each point consumes. -/
theorem affineCluster_card_le_length
    (C : Submodule F (Fin n → F)) (c₀ c₁ u₀ u₁ : Fin n → F)
    (hc₀ : c₀ ∈ C) (hc₁ : c₁ ∈ C) (a : ℕ) (G : Finset F)
    (S : F → Finset (Fin n))
    (hsize : ∀ γ ∈ G, a ≤ (S γ).card)
    (hagree : ∀ γ ∈ G, ∀ i ∈ S γ,
      c₀ i + γ * c₁ i = u₀ i + γ * u₁ i)
    (hno : ∀ γ ∈ G,
      ¬ pairJointAgreesOn (C : Set (Fin n → F)) (S γ) u₀ u₁) :
    G.card ≤ n := by
  have hmul := affineCluster_card_mul_le_support C c₀ c₁ u₀ u₁ hc₀ hc₁ a G S
    hsize hagree hno
  calc G.card = 1 * G.card := by simp
    _ ≤ max 1 (a - (lockedSet c₀ c₁ u₀ u₁).card) * G.card :=
      Nat.mul_le_mul_right G.card (le_max_left 1 _)
    _ ≤ (Finset.univ.filter (fun i => u₁ i - c₁ i ≠ 0)).card := hmul
    _ ≤ (Finset.univ : Finset (Fin n)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = n := by rw [Finset.card_univ, Fintype.card_fin]

end ProximityGap.Frontier.DesignMatrixAffineCluster

#print axioms ProximityGap.Frontier.DesignMatrixAffineCluster.affineCluster_card_mul_le_support
#print axioms ProximityGap.Frontier.DesignMatrixAffineCluster.affineCluster_card_le_length
#print axioms ProximityGap.Frontier.DesignMatrixAffineCluster.affineClusterBadScalars_subset_mcaEvent
