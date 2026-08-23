/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ListDecoding.SubspacePolyDecomp
import ArkLib.Data.CodingTheory.ListDecoding.SubspacePolyBiUnion
import ArkLib.Data.CodingTheory.ListDecoding.SubspacePolyCompSub
import ArkLib.Data.CodingTheory.ListDecoding.SubspacePolyTranslate

/-!
# The subspace-polynomial recursion

For an `𝔽_q`-subspace `W = span{u} ⊕ W'` of `K`, grouping the roots of `W` into the `|F|` cosets
`W' + c·u` gives the recursion

`subspacePoly (subFinset W) = ∏_{c∈F} (subspacePoly (subFinset W') - C (subspacePoly (subFinset W')).eval (ι c · u))`.

This combines the coset decomposition of `subFinset W` (a disjoint union, from the line⊕hyperplane
decomposition) with `subspacePoly_biUnion`, `subspacePoly_image_add_eq_comp` (translation) and
`subspacePoly_comp_X_sub_C_eq`.  It is the BKR06 linearized recursion `s_{V'⊕𝔽_q·u} = ∏_c(s_{V'} - c·s_{V'}(u))`
at the polynomial level (before applying 𝔽_q-homogeneity of `s_{V'}`).
-/

open Polynomial BigOperators

namespace BKR06

variable {F : Type*} [Field F] [Fintype F]
variable {K : Type*} [Field K] [DecidableEq K] [Algebra F K]

private lemma sf0 (W : Submodule F K) [Fintype W] : (0 : K) ∈ subFinset W :=
  mem_subFinset.mpr W.zero_mem
private lemma sfsub (W : Submodule F K) [Fintype W] :
    ∀ x ∈ subFinset W, ∀ y ∈ subFinset W, x - y ∈ subFinset W :=
  fun x hx y hy => mem_subFinset.mpr (W.sub_mem (mem_subFinset.mp hx) (mem_subFinset.mp hy))
private lemma sfadd (W : Submodule F K) [Fintype W] :
    ∀ x ∈ subFinset W, ∀ y ∈ subFinset W, x + y ∈ subFinset W :=
  fun x hx y hy => mem_subFinset.mpr (W.add_mem (mem_subFinset.mp hx) (mem_subFinset.mp hy))

/-- Coset decomposition of the root finset: `subFinset W = ⊔_{c∈F} (subFinset W' + ι c · u)`. -/
lemma subFinset_eq_coset_biUnion (W W' : Submodule F K) [Fintype W] [Fintype W'] (u : K)
    (hdecomp : W = Submodule.span F {u} ⊔ W') :
    subFinset W = (Finset.univ : Finset F).biUnion
      (fun c => (subFinset W').image (· + algebraMap F K c * u)) := by
  classical
  ext x
  simp only [mem_subFinset, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · intro hx
    rw [hdecomp] at hx
    obtain ⟨s, hs, w', hw', rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hs
    exact ⟨c, w', hw', by rw [Algebra.smul_def, add_comm]⟩
  · rintro ⟨c, w', hw', rfl⟩
    rw [hdecomp]
    refine Submodule.mem_sup.mpr ⟨algebraMap F K c * u, ?_, w', hw', by rw [add_comm]⟩
    rw [← Algebra.smul_def]
    exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self u)

/-- The cosets `subFinset W' + ι c · u` are pairwise disjoint for distinct `c` (since `u ∉ W'`). -/
lemma coset_pairwiseDisjoint (W' : Submodule F K) [Fintype W'] (u : K) (hu : u ∉ W') :
    (↑(Finset.univ : Finset F) : Set F).PairwiseDisjoint
      (fun c => (subFinset W').image (· + algebraMap F K c * u)) := by
  intro c _ c' _ hcc'
  simp only [Function.onFun, Finset.disjoint_left, Finset.mem_image, mem_subFinset]
  rintro x ⟨w1, hw1, rfl⟩ ⟨w2, hw2, heq⟩
  apply hu
  have hkey : (c' - c) • u = w1 - w2 := by
    rw [sub_smul, Algebra.smul_def, Algebra.smul_def]; linear_combination heq
  have hcne : c' - c ≠ 0 := sub_ne_zero.mpr (Ne.symm hcc')
  have : u = (c' - c)⁻¹ • (w1 - w2) := by
    rw [← hkey, smul_smul, inv_mul_cancel₀ hcne, one_smul]
  rw [this]
  exact W'.smul_mem _ (W'.sub_mem hw1 hw2)

/-- **Subspace-polynomial recursion.** For `W = span{u} ⊕ W'` (with `u ∉ W'`),
`subspacePoly (subFinset W) = ∏_{c∈F} (subspacePoly (subFinset W') - C ((subspacePoly (subFinset W')).eval (ι c · u)))`. -/
lemma subspacePoly_subFinset_recursion (W W' : Submodule F K) [Fintype W] [Fintype W'] (u : K)
    (hdecomp : W = Submodule.span F {u} ⊔ W') (hu : u ∉ W') :
    subspacePoly (subFinset W)
      = ∏ c : F, (subspacePoly (subFinset W')
          - C ((subspacePoly (subFinset W')).eval (algebraMap F K c * u))) := by
  classical
  rw [subFinset_eq_coset_biUnion W W' u hdecomp,
    subspacePoly_biUnion _ _ (coset_pairwiseDisjoint W' u hu)]
  refine Finset.prod_congr rfl (fun c _ => ?_)
  rw [subspacePoly_image_add_eq_comp,
    subspacePoly_comp_X_sub_C_eq (subFinset W') (sf0 W') (sfsub W') (sfadd W') (algebraMap F K c * u)]

end BKR06

-- Axiom audit.
#print axioms BKR06.subspacePoly_subFinset_recursion
