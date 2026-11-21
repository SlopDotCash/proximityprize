/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BoundaryGenericFarExact
import ArkLib.ToMathlib.LinearAlgebra.Submodule.Union

/-! # Exact boundary mass after separating unordered pairs of supports

At exactly k+1 required agreements every selected support supplies a bad scalar for the line
with second row X^k. A polynomial first row separates any m selected supports if the field has at
least choose(m,2) elements. This gives both an exact numerator when m is the full support count
and a large-list lower bound when the full support count exceeds that window.
-/

open Finset Polynomial Code
open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap.Ownership ProximityGap.SpikeFloor
namespace ProximityGap.BoundaryPairSeparation

variable {F : Type} [Field F] [Fintype F] {n : ℕ} [NeZero n]

private def equalOn (D : Fin n ↪ F) (k : ℕ) (T : Finset (Finset (Fin n))) : Submodule F F[X] where
  carrier := {w | ∀ x ∈ T, ∀ y ∈ T, coeffFn D k x w = coeffFn D k y w}
  zero_mem' := by simp [coeffFn]
  add_mem' := by
    classical
    intro a b ha hb x hx y hy
    rw [coeffFn_add, coeffFn_add, ha x hx y hy, hb x hx y hy]
  smul_mem' := by
    classical
    intro c w hw x hx y hy
    rw [smul_eq_C_mul, coeffFn_smul, coeffFn_smul, hw x hx y hy]

/-- A single polynomial separates a selected family of support functionals. -/
theorem exists_separating (D : Fin n ↪ F) {k : ℕ} (A : Finset (Finset (Fin n)))
    (hsizes : ∀ S ∈ A, S.card = k + 1) (hq : A.card.choose 2 ≤ Fintype.card F) :
    ∃ Q : F[X], Set.InjOn (fun S => coeffFn D k S Q) (↑A : Set _) := by
  classical
  have hproper : ∀ T ∈ A.powersetCard 2, equalOn D k T ≠ ⊤ := by
    intro T hT htop
    obtain ⟨hsubset, htwo⟩ := Finset.mem_powersetCard.mp hT
    obtain ⟨x, y, hne, rfl⟩ := Finset.card_eq_two.mp htwo
    have hx : x ∈ ({x, y} : Finset _) := by simp
    have hy : y ∈ ({x, y} : Finset _) := by simp
    obtain ⟨j, hjx, hjy⟩ := coeffFn_separation D (hsizes x (hsubset hx))
      (hsizes y (hsubset hy)) hne
    have hm : X ^ (j : ℕ) * nodePoly D y ∈ equalOn D k {x, y} := htop ▸ Submodule.mem_top
    exact hjx ((hm x hx y hy).trans hjy)
  obtain ⟨Q, hQ⟩ := Submodule.exists_forall_notMem_of_card_le
    (A.powersetCard 2) (equalOn D k) hproper (by simpa using hq)
  refine ⟨Q, ?_⟩
  intro x hx y hy hxy
  by_contra hne
  have hpair : ({x, y} : Finset _) ∈ A.powersetCard 2 := by
    apply Finset.mem_powersetCard.mpr
    refine ⟨?_, by simp [hne]⟩
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact hx
    · exact (Finset.mem_singleton.mp hw) ▸ hy
  apply hQ _ hpair
  intro u hu v hv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · rfl
  · exact hxy
  · exact hxy.symm
  · rfl

open Classical in
/-- At a boundary band, some actual stack attains at least m bad scalars whenever there are
enough supports and at most q distinct unordered pairs to separate. -/
theorem partial_mass (D : Fin n ↪ F) {k m : ℕ} (hk : 1 ≤ k) {δ : ℝ≥0}
    (hlo : (k : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ (k + 1 : ℕ))
    (hm : m ≤ n.choose (k + 1)) (hq : m.choose 2 ≤ Fintype.card F) :
    ∃ Q : F[X], m ≤ (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
      ((rsCode D k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
      (fun i => Q.eval (D i)) (fun i => (X ^ k : F[X]).eval (D i)) γ)).card := by
  classical
  let allS := (Finset.univ : Finset (Fin n)).powersetCard (k + 1)
  have hnum : m ≤ allS.card := by simpa [allS] using hm
  obtain ⟨A, hA, hAm⟩ := Finset.exists_subset_card_eq hnum
  have hsizes : ∀ S ∈ A, S.card = k + 1 := fun S h => (Finset.mem_powersetCard.mp (hA h)).2
  obtain ⟨Q, hQ⟩ := exists_separating D A hsizes (hAm ▸ hq)
  refine ⟨Q, ?_⟩
  rw [boundary_slice_badSet_modular_of_natDegree D hk hlo hhi Q (X ^ k) (natDegree_X_pow k)]
  let f := fun S : Finset (Fin n) => -coeffFn D k S Q / coeffFn D k S (X ^ k)
  have hinj : Set.InjOn f (↑A : Set _) := by
    intro x hx y hy h
    apply hQ hx hy
    simpa [f, coeffFn_X_pow_self D (hsizes x hx), coeffFn_X_pow_self D (hsizes y hy)] using h
  have hle := Finset.card_le_card (Finset.image_subset_image (f := f) hA)
  rw [Finset.card_image_of_injOn hinj, hAm] at hle
  exact hle

/-- Exact affine-line MCA error at the boundary whenever choose(N,2) ≤ q,
where N is the number of minimal detecting supports. -/
theorem epsMCA_exact (D : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) {δ : ℝ≥0}
    (hlo : (k : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ (k + 1 : ℕ))
    (hq : (n.choose (k + 1)).choose 2 ≤ Fintype.card F) :
    epsMCA (F := F) ((rsCode D k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ =
      ((n.choose (k + 1) : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  classical
  apply le_antisymm (epsMCA_le_boundary_choose D hk hlo hhi)
  obtain ⟨Q, hQ⟩ := partial_mass D hk hlo hhi le_rfl hq
  let u := Code.finMapTwoWords (fun i => Q.eval (D i)) (fun i => (X ^ k : F[X]).eval (D i))
  have hupper := mcaEvent_prob_le_epsMCA (F := F)
    (((rsCode D k : Submodule F (Fin n → F)) : Set (Fin n → F))) δ u
  rw [prob_uniform_eq_card_filter_div_card] at hupper
  apply le_trans _ hupper
  gcongr <;> first | exact_mod_cast hQ | simp

#print axioms exists_separating
#print axioms partial_mass
#print axioms epsMCA_exact
end ProximityGap.BoundaryPairSeparation
