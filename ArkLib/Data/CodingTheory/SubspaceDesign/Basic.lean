import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Subspace Designs

This file provides the basic definitions and geometric properties of subspace designs.
A collection of subspaces `H` is called an `(s, τ)`-strong subspace design if every
subspace `W` of dimension at most `s` intersects the subspaces in `H` with total
dimension bounded by `τ`. These structures are fundamental in the construction of
list-decodable codes, such as in the Guruswami-Guo 2025 bounds for Reed-Solomon codes.

## Main definitions
* `intersectionMultiplicity`: The sum of dimensions of the intersections of a subspace `W`
  with a family of subspaces `H`.
* `IsTauSubspaceDesign`: The property that a family `H` forms a `τ`-subspace design
  for a given dimension bound `s`.

## Main theorems
* `intersectionMultiplicity_mono`: The intersection multiplicity is monotonically
  increasing with respect to subspace inclusion.
* `intersectionMultiplicity_bound`: A geometric lemma bounding the intersection
  multiplicity of a larger subspace `W` based on a smaller subspace `W'`.
-/

open Submodule
open scoped BigOperators

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable {ι : Type*} [Fintype ι] (H : ι → Submodule F V)

/-- The intersection multiplicity of a subspace `W` with a family of subspaces `H`. -/
noncomputable def intersectionMultiplicity (W : Submodule F V) : ℕ :=
  ∑ i, Module.finrank F ↥(H i ⊓ W)

/-- The definition of a strong `τ`-subspace design.
A family `H` of subspaces is an `(s, τ)`-strong subspace design if for every
subspace `W` of dimension at most `s`, its intersection multiplicity with `H`
is bounded by `τ`. -/
def IsTauSubspaceDesign (s τ : ℕ) : Prop :=
  ∀ W : Submodule F V, Module.finrank F W ≤ s → intersectionMultiplicity H W ≤ τ

-- Monotonicity lemma
lemma intersectionMultiplicity_mono [FiniteDimensional F V] {W₁ W₂ : Submodule F V} (h : W₁ ≤ W₂) :
    intersectionMultiplicity H W₁ ≤ intersectionMultiplicity H W₂ := by
  apply Finset.sum_le_sum
  intro i _
  apply Submodule.finrank_mono
  exact inf_le_inf_left (H i) h

-- Key geometric lemma: Dimension of intersection bound
lemma finrank_inf_le_finrank_inf_add_finrank_sub [FiniteDimensional F V]
    {W W' : Submodule F V} (h : W' ≤ W) (H_i : Submodule F V) :
    Module.finrank F ↥(H_i ⊓ W) ≤
      Module.finrank F ↥(H_i ⊓ W') + (Module.finrank F W - Module.finrank F W') := by
  have eq1 : Module.finrank F ↥((H_i ⊓ W) ⊔ W') + Module.finrank F ↥((H_i ⊓ W) ⊓ W') =
      Module.finrank F ↥(H_i ⊓ W) + Module.finrank F W' :=
    Submodule.finrank_sup_add_finrank_inf_eq (H_i ⊓ W) W'
  have eq2 : (H_i ⊓ W) ⊓ W' = H_i ⊓ W' := by
    ext x
    simp only [mem_inf]
    tauto
  rw [eq2] at eq1
  have le1 : Module.finrank F ↥((H_i ⊓ W) ⊔ W') ≤ Module.finrank F W := by
    apply Submodule.finrank_mono
    rw [sup_le_iff]
    exact ⟨inf_le_right, h⟩
  have le2 : Module.finrank F W' ≤ Module.finrank F W := Submodule.finrank_mono h
  omega

-- Bounding intersection multiplicity for larger spaces
lemma intersectionMultiplicity_bound [FiniteDimensional F V]
    {W W' : Submodule F V} (h : W' ≤ W) :
    intersectionMultiplicity H W ≤
      intersectionMultiplicity H W' +
        Fintype.card ι * (Module.finrank F W - Module.finrank F W') := by
  unfold intersectionMultiplicity
  calc
    (∑ i : ι, Module.finrank F ↥(H i ⊓ W))
      ≤ ∑ i : ι, (Module.finrank F ↥(H i ⊓ W') + (Module.finrank F W - Module.finrank F W')) := by
        apply Finset.sum_le_sum
        intro i _
        exact finrank_inf_le_finrank_inf_add_finrank_sub h (H i)
    _ = (∑ i : ι, Module.finrank F ↥(H i ⊓ W')) +
          ∑ i : ι, (Module.finrank F W - Module.finrank F W') := by
        exact Finset.sum_add_distrib
    _ = (∑ i : ι, Module.finrank F ↥(H i ⊓ W')) +
          Fintype.card ι * (Module.finrank F W - Module.finrank F W') := by
        simp
