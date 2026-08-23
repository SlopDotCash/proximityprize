/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.Finset.PickSubset
import ArkLib.Data.Probability.Notation
import Mathlib.Data.Fintype.Powerset
import Mathlib.Probability.Distributions.Uniform

/-!
# Uniform sampling of fixed-size finite subsets

ABF26 random Reed-Solomon statements quantify over a uniformly random size-`n`
evaluation domain `L ⊆ F`. This file provides the small probability primitive
needed to state those theorems without handwaving:

* `SizedSubset α n`, the type of `n`-element finite subsets of `α`;
* `uniformSizedSubset`, the uniform PMF on that type when `n ≤ |α|`;
* support, cardinality, point-mass, and equivalence-invariance lemmas.

The random-RS theorem statements in `ListDecoding/Bounds.lean` and
`ProximityGap/CapacityBounds.lean` can now quantify over
`L ← uniformSizedSubset F n hn`.
-/

namespace Probability

open scoped ProbabilityTheory NNReal ENNReal

universe u v

variable {α : Type u} {β : Type v} {n : ℕ}

/-- The type of finite subsets of `α` with cardinality exactly `n`. -/
abbrev SizedSubset (α : Type u) (n : ℕ) : Type u :=
  {s : Finset α // s.card = n}

namespace SizedSubset

@[simp]
theorem card (S : SizedSubset α n) : S.1.card = n :=
  S.property

/-- A witness `n`-element subset of a finite type when `n ≤ |α|`. -/
noncomputable def some [Fintype α] [DecidableEq α] (h : n ≤ Fintype.card α) :
    SizedSubset α n :=
  ⟨(Finset.univ : Finset α).pickSubset n, by
    rw [Finset.card_pick_subset, Finset.card_univ]
    exact min_eq_right h⟩

/-- Map an `n`-element subset across an equivalence of ambient finite types. -/
noncomputable def mapEquiv [DecidableEq α] [DecidableEq β] (e : α ≃ β) :
    SizedSubset α n ≃ SizedSubset β n where
  toFun S := ⟨S.1.map e.toEmbedding, by simp [S.property]⟩
  invFun T := ⟨T.1.map e.symm.toEmbedding, by simp [T.property]⟩
  left_inv S := by
    apply Subtype.ext
    ext x
    simp
  right_inv T := by
    apply Subtype.ext
    ext x
    simp

end SizedSubset

noncomputable instance instFintypeSizedSubset [Fintype α] [DecidableEq α] :
    Fintype (SizedSubset α n) :=
  Fintype.ofFinset ((Finset.univ : Finset α).powersetCard n) (by
    intro s
    change s ∈ (Finset.univ : Finset α).powersetCard n ↔ s.card = n
    simp)

/-- Cardinality of the type of `n`-element subsets of a finite type. -/
theorem card_sizedSubset [Fintype α] [DecidableEq α] :
    Fintype.card (SizedSubset α n) = Nat.choose (Fintype.card α) n := by
  classical
  change Fintype.card {s : Finset α // s.card = n} = Nat.choose (Fintype.card α) n
  rw [Fintype.card_of_subtype ((Finset.univ : Finset α).powersetCard n)]
  · rw [Finset.card_powersetCard, Finset.card_univ]
  · intro s
    change s ∈ (Finset.univ : Finset α).powersetCard n ↔ s.card = n
    simp

/-- Uniform distribution over all `n`-element subsets of `α`, available when `n ≤ |α|`. -/
noncomputable def uniformSizedSubset [Fintype α] [DecidableEq α]
    (h : n ≤ Fintype.card α) : PMF (SizedSubset α n) :=
  letI : Nonempty (SizedSubset α n) := ⟨SizedSubset.some h⟩
  PMF.uniformOfFintype (SizedSubset α n)

@[simp]
theorem uniformSizedSubset_apply [Fintype α] [DecidableEq α]
    (h : n ≤ Fintype.card α) (S : SizedSubset α n) :
    uniformSizedSubset (α := α) (n := n) h S =
      (Nat.choose (Fintype.card α) n : ℝ≥0∞)⁻¹ := by
  classical
  simp [uniformSizedSubset, card_sizedSubset]

@[simp]
theorem support_uniformSizedSubset [Fintype α] [DecidableEq α]
    (h : n ≤ Fintype.card α) :
    (uniformSizedSubset (α := α) (n := n) h).support = ⊤ := by
  classical
  simp [uniformSizedSubset]

theorem mem_support_uniformSizedSubset [Fintype α] [DecidableEq α]
    (h : n ≤ Fintype.card α) (S : SizedSubset α n) :
    S ∈ (uniformSizedSubset (α := α) (n := n) h).support := by
  rw [support_uniformSizedSubset h]
  trivial

/-- Uniform fixed-size subset sampling is invariant under equivalence of ambient finite types. -/
theorem uniformSizedSubset_apply_mapEquiv [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ≃ β)
    (hα : n ≤ Fintype.card α) (hβ : n ≤ Fintype.card β)
    (S : SizedSubset α n) :
    uniformSizedSubset (α := β) (n := n) hβ (SizedSubset.mapEquiv e S) =
      uniformSizedSubset (α := α) (n := n) hα S := by
  classical
  simp [uniformSizedSubset, card_sizedSubset, Fintype.card_congr e]

end Probability
