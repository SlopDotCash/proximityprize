/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Data.Fintype.BigOperators

/-!
# Higher-order MDS: the generic-intersection foundation (#389)

The abstract core of higher-order MDS codes (Roth 2022; Brakensiek–Gopi–Makam 2023),
the machinery behind beyond-Johnson list decoding.  A configuration of subspaces is
*higher-order MDS* when its intersections are as transversal as the dimension budget
permits.  This file develops the dimension calculus those statements rest on, over an
arbitrary finite-dimensional space — independent of the existing `AGL24` GM-MDS
dual-basis residual (`GMMDSDualZeroPatternTheorem`), which is a different object.

## Results (all axiom-clean)

* `codim_inf_le` — Grassmann subadditivity: `codim(W₁ ⊓ W₂) ≤ codim W₁ + codim W₂`.
* `codim_biInf_le` / `codim_iInf_le` — finite-family subadditivity
  `codim(⋂ᵢ Wᵢ) ≤ Σᵢ codim(Wᵢ)` (the **always-true** direction).
* `codim_iInf_le_min` — the universal cap `codim(⋂) ≤ min(dim V, Σ codim)`.
* `IsGenericInter` — **higher-order MDS position**: the intersection codimension
  *attains* that cap.  This is the defining transversality property.
* `finrank_iInf_of_generic` / `iInf_eq_bot_of_generic` — in generic position the
  intersection has the exact expected dimension `dim V − Σ codim` (or is `0` once the
  budget saturates).

This is layer 1 of the higher-order-MDS programme: the dimension calculus.  Layer 2
(MDS(ℓ) for a code via its generator-column subspaces) and layer 3 (the
list-decoding consequence: MDS(L+1) ⟹ list size ≤ L past the Johnson radius) build
on these.

Issue #389.
-/

open Finset Module

namespace ArkLib.HigherOrderMDS

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Codimension of a subspace. -/
noncomputable def codim (W : Submodule K V) : ℕ := finrank K V - finrank K W

theorem codim_le (W : Submodule K V) : codim W ≤ finrank K V := by
  unfold codim; omega

@[simp] theorem codim_top : codim (⊤ : Submodule K V) = 0 := by
  simp [codim, finrank_top]

/-- Two-subspace codimension subadditivity (Grassmann): the heart. -/
theorem codim_inf_le (W₁ W₂ : Submodule K V) :
    codim (W₁ ⊓ W₂) ≤ codim W₁ + codim W₂ := by
  have hgr := Submodule.finrank_sup_add_finrank_inf_eq W₁ W₂
  have hle : finrank K ↥(W₁ ⊔ W₂) ≤ finrank K V := Submodule.finrank_le _
  have h1 : finrank K ↥W₁ ≤ finrank K V := Submodule.finrank_le _
  have h2 : finrank K ↥W₂ ≤ finrank K V := Submodule.finrank_le _
  have h3 : finrank K ↥(W₁ ⊓ W₂) ≤ finrank K V := Submodule.finrank_le _
  unfold codim
  omega

/-- **Codimension subadditivity over a finite intersection** (Finset form). -/
theorem codim_biInf_le {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (W : ι → Submodule K V) :
    codim (⨅ i ∈ s, W i) ≤ ∑ i ∈ s, codim (W i) := by
  classical
  induction s using Finset.induction with
  | empty =>
      have htop : (⨅ i ∈ (∅ : Finset ι), W i) = ⊤ := by simp
      rw [htop]; simp
  | insert a s ha ih =>
      rw [Finset.iInf_insert, Finset.sum_insert ha]
      exact le_trans (codim_inf_le _ _) (Nat.add_le_add_left ih _)

/-- **Codimension subadditivity over a finite intersection** (Fintype form):
the always-true direction of higher-order MDS, `codim(⋂ᵢ Wᵢ) ≤ Σᵢ codim(Wᵢ)`. -/
theorem codim_iInf_le {ι : Type*} [Fintype ι] [DecidableEq ι] (W : ι → Submodule K V) :
    codim (⨅ i, W i) ≤ ∑ i, codim (W i) := by
  have := codim_biInf_le (Finset.univ) W
  simpa using this

/-- The universal upper bound on intersection codimension: `≤ min(dim V, Σ codim)`. -/
theorem codim_iInf_le_min {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : ι → Submodule K V) :
    codim (⨅ i, W i) ≤ min (finrank K V) (∑ i, codim (W i)) :=
  le_min (codim_le _) (codim_iInf_le W)

/-- **Generic intersection position** (= higher-order MDS for this family):
the intersection codimension attains its universal maximum `min(dim V, Σ codim)`.
This is the defining property of higher-order MDS configurations: the subspaces
meet as transversally as the dimension budget allows. -/
def IsGenericInter {ι : Type*} [Fintype ι] (W : ι → Submodule K V) : Prop :=
  codim (⨅ i, W i) = min (finrank K V) (∑ i, codim (W i))

/-- In generic position, when the codimension budget does not exceed `dim V`, the
intersection has the **exact** expected dimension `dim V − Σ codim`. -/
theorem finrank_iInf_of_generic {ι : Type*} [Fintype ι] [DecidableEq ι]
    {W : ι → Submodule K V} (hgen : IsGenericInter W)
    (hbudget : ∑ i, codim (W i) ≤ finrank K V) :
    finrank K ↥(⨅ i, W i) = finrank K V - ∑ i, codim (W i) := by
  have h := hgen
  rw [IsGenericInter, min_eq_right hbudget] at h
  have hle : finrank K ↥(⨅ i, W i) ≤ finrank K V := Submodule.finrank_le _
  have hc : codim (⨅ i, W i) = finrank K V - finrank K ↥(⨅ i, W i) := rfl
  rw [hc] at h
  omega

/-- In generic position, if the codimension budget is `≥ dim V`, the intersection
is the zero subspace (the subspaces are jointly "spanning enough" to leave nothing). -/
theorem iInf_eq_bot_of_generic {ι : Type*} [Fintype ι] [DecidableEq ι]
    {W : ι → Submodule K V} (hgen : IsGenericInter W)
    (hbudget : finrank K V ≤ ∑ i, codim (W i)) :
    finrank K ↥(⨅ i, W i) = 0 := by
  have h := hgen
  rw [IsGenericInter, min_eq_left hbudget] at h
  have hle : finrank K ↥(⨅ i, W i) ≤ finrank K V := Submodule.finrank_le _
  have hc : codim (⨅ i, W i) = finrank K V - finrank K ↥(⨅ i, W i) := rfl
  rw [hc] at h
  omega

end ArkLib.HigherOrderMDS

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.HigherOrderMDS.codim_iInf_le
#print axioms ArkLib.HigherOrderMDS.finrank_iInf_of_generic
