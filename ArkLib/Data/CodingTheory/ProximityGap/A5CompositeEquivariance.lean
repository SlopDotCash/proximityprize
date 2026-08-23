/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAEquivariance

/-!
# A5 stretch — the COMBINED group-equivariance lemma for the orbit-reduction probe (#334)

`MCAEquivariance.lean` proves the FIVE generator invariances of the per-stack bad-scalar
probability separately:

* rotation `(u₀,u₁) ↦ (u₀∘σ, u₁∘σ)`  (`prob_mcaEvent_comp_perm`; RS instance `mcaEvent_rs_rotate`)
* whole-stack scaling `(u₀,u₁) ↦ (a•u₀, a•u₁)`, `a ≠ 0`  (`prob_mcaEvent_smul_both`)
* direction-row scaling `u₁ ↦ c•u₁`, `c ≠ 0`  (`prob_mcaEvent_smul_right`)
* shear `u₀ ↦ u₀ + β•u₁`  (`prob_mcaEvent_shift`)

The exact-`n=12` probe (`probe_epsmca_orbit_exact_n12.py`) reduces over the orbits of the
COMBINED group element
  `G : (s₀, s₁) ↦ (a · Rᵗ s₀ + b · Rᵗ s₁ , c · Rᵗ s₁)`,  order `n·p·(p-1)²`.
On the stack (word) side this is the single composite transform
  `(u₀, u₁) ↦ ( a•(u₀∘σ) + b•(u₁∘σ) , c•(u₁∘σ) )`   with `a,c ≠ 0`,  σ a code rotation.
Until now the probe's *combined* orbit invariance was only the (asserted) conjunction of the
five separate Lean lemmas; this file BUNDLES them into one composite probability-invariance
theorem `prob_mcaEvent_affine_rotate`, so a concrete transversal can DISCHARGE the covering
hypothesis `hT` of `epsMCA_eq_iSup_subtype_of_reps` rather than leave it asserted.

## What is proven here (target: axiom-clean `propext, Classical.choice, Quot.sound`)

* `prob_mcaEvent_affine_rotate` — the probability-level composite invariance: the full
  group element `(u₀,u₁) ↦ (a•(u₀∘σ) + b•(u₁∘σ), c•(u₁∘σ))` preserves the per-stack
  bad-scalar probability, for ANY code-preserving permutation `σ` and `a,c ≠ 0`, `b`;
* `prob_mcaEvent_rs_affine_rotate` — the same for a Reed–Solomon code under a multiplicative
  domain rotation `domain (σ i) = g · domain i`, `g ≠ 0` (the probe's exact setting; consumes
  `comp_perm_mem_code`, no separate code-stability hypothesis needed).

These consume ONLY the proven `MCAEquivariance` lemmas; no new structural argument, no `sorry`.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*.
  ePrint 2026/680. Issue #334 A5 (orbit-reduced exact profile).
-/

set_option linter.unusedSectionVars false

open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code
open ProximityGap.MCAEquivariance

namespace ProximityGap.A5Composite

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

open Classical in
/-- **The combined group-element probability invariance (general code).** For a submodule
code `C ⊆ (ι → F)` and a code-preserving permutation `σ`, scalars `a, c ≠ 0`, `b : F`, the
composite transform `(u₀,u₁) ↦ (a•(u₀∘σ) + b•(u₁∘σ), c•(u₁∘σ))` preserves the per-stack
bad-scalar probability of `mcaEvent`.

Factored through the proven generators: direction-scale `c·a⁻¹` (`prob_mcaEvent_smul_right`),
shear `b·a⁻¹` (`prob_mcaEvent_shift`), whole-stack scale `a` (`prob_mcaEvent_smul_both`),
strip rotation (`prob_mcaEvent_comp_perm`). This is the single statement the
`probe_epsmca_orbit_exact_n12.py` orbit reduction needs: its group element acts on the WORD
side exactly as this composite, so the per-threshold bad-γ count is invariant, which is what
makes the sup in `ε_mca` attained on orbit representatives. -/
theorem prob_mcaEvent_affine_rotate
    (C : Submodule F (ι → F)) {δ : ℝ≥0}
    (σ : Equiv.Perm ι)
    (hσ : ∀ w ∈ C, w ∘ ⇑σ ∈ C) (hσ' : ∀ w ∈ C, w ∘ ⇑σ⁻¹ ∈ C)
    {a c : F} (ha : a ≠ 0) (hc : c ≠ 0) (b : F)
    (u₀ u₁ : ι → F) :
    Pr_{ let γ ←$ᵖ F }[mcaEvent (F := F) (C : Set (ι → F)) δ
        (a • (u₀ ∘ ⇑σ) + b • (u₁ ∘ ⇑σ)) (c • (u₁ ∘ ⇑σ)) γ]
      = Pr_{ let γ ←$ᵖ F }[mcaEvent (F := F) (C : Set (ι → F)) δ u₀ u₁ γ] := by
  set r₀ : ι → F := u₀ ∘ ⇑σ with hr₀
  set r₁ : ι → F := u₁ ∘ ⇑σ with hr₁
  have hca : (c * a⁻¹) ≠ 0 := mul_ne_zero hc (inv_ne_zero ha)
  have hrow1 : c • r₁ = (c * a⁻¹) • (a • r₁) := by
    rw [smul_smul]; congr 1; field_simp
  have hrow0 : a • r₀ + b • r₁ = (a • r₀ + (b * a⁻¹) • (a • r₁)) := by
    congr 1; rw [smul_smul]; congr 1; field_simp
  calc
    Pr_{ let γ ←$ᵖ F }[mcaEvent (F := F) (C : Set (ι → F)) δ
        (a • r₀ + b • r₁) (c • r₁) γ]
        = Pr_{ let γ ←$ᵖ F }[mcaEvent (F := F) (C : Set (ι → F)) δ
            (a • r₀ + (b * a⁻¹) • (a • r₁)) ((c * a⁻¹) • (a • r₁)) γ] := by
              rw [hrow1, hrow0]
      _ = Pr_{ let γ ←$ᵖ F }[mcaEvent (F := F) (C : Set (ι → F)) δ
            (a • r₀ + (b * a⁻¹) • (a • r₁)) (a • r₁) γ] :=
              prob_mcaEvent_smul_right C hca
      _ = Pr_{ let γ ←$ᵖ F }[mcaEvent (F := F) (C : Set (ι → F)) δ
            (a • r₀) (a • r₁) γ] :=
              prob_mcaEvent_shift C (b * a⁻¹)
      _ = Pr_{ let γ ←$ᵖ F }[mcaEvent (F := F) (C : Set (ι → F)) δ r₀ r₁ γ] :=
              prob_mcaEvent_smul_both C ha
      _ = Pr_{ let γ ←$ᵖ F }[mcaEvent (F := F) (C : Set (ι → F)) δ
            (u₀ ∘ ⇑σ) (u₁ ∘ ⇑σ) γ] := by rw [hr₀, hr₁]
      _ = Pr_{ let γ ←$ᵖ F }[mcaEvent (F := F) (C : Set (ι → F)) δ u₀ u₁ γ] :=
              prob_mcaEvent_comp_perm C σ hσ hσ'

open Classical in
/-- **The combined group element for a Reed–Solomon code (the probe's exact setting).** For
`RS[domain, k]` and any multiplicative domain rotation `σ` (`domain (σ i) = g · domain i`,
`g ≠ 0`), the full group element `(u₀,u₁) ↦ (a•(u₀∘σ) + b•(u₁∘σ), c•(u₁∘σ))` (`a,c ≠ 0`)
preserves the per-stack bad-scalar probability. Code-stability of `σ` is discharged from the
rotation hypothesis via `comp_perm_mem_code`, matching the probe's syndrome rotation `R`
(`Rᵗ`) composed with the field scalings — the per-threshold bad-γ count invariance behind the
exact orbit-reduced profile. -/
theorem prob_mcaEvent_rs_affine_rotate
    (domain : ι ↪ F) (k : ℕ) {δ : ℝ≥0}
    (σ : Equiv.Perm ι) (g : F) (hg0 : g ≠ 0) (hg : ∀ i, domain (σ i) = g * domain i)
    {a c : F} (ha : a ≠ 0) (hc : c ≠ 0) (b : F)
    (u₀ u₁ : ι → F) :
    Pr_{ let γ ←$ᵖ F }[mcaEvent (F := F) (ReedSolomon.code domain k : Set (ι → F)) δ
        (a • (u₀ ∘ ⇑σ) + b • (u₁ ∘ ⇑σ)) (c • (u₁ ∘ ⇑σ)) γ]
      = Pr_{ let γ ←$ᵖ F }[mcaEvent (F := F) (ReedSolomon.code domain k : Set (ι → F)) δ
          u₀ u₁ γ] := by
  have hginv : ∀ i, domain (σ⁻¹ i) = g⁻¹ * domain i := by
    intro i
    have h := hg (σ⁻¹ i)
    simp only [Equiv.Perm.inv_def, Equiv.apply_symm_apply] at h ⊢
    rw [h, ← mul_assoc, inv_mul_cancel₀ hg0, one_mul]
  exact prob_mcaEvent_affine_rotate (ReedSolomon.code domain k) σ
    (fun w hw => comp_perm_mem_code σ g hg hw)
    (fun w hw => comp_perm_mem_code σ⁻¹ g⁻¹ hginv hw)
    ha hc b u₀ u₁

/-! ## Source audit -/

#print axioms prob_mcaEvent_affine_rotate
#print axioms prob_mcaEvent_rs_affine_rotate

end ProximityGap.A5Composite
