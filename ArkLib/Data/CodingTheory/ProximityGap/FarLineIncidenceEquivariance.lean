/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.FarCosetExplosion
import ArkLib.Data.CodingTheory.ProximityGap.MCAEquivariance

/-!
# Automorphism-equivariance of the far-line MCA incidence (issue #389)

The governing law for the MCA threshold is `δ* = sup{δ : I(δ) ≤ q·ε*}` where `I(δ)` is the maximum,
over far directions `u₁` and offsets `u₀`, of the **far-line incidence**

  `#{γ : the line u₀ + γ·u₁ agrees with some codeword on a witness-sized (≥ (1−δ)n) set}`

(`FarCosetExplosion.epsMCA_ge_far_incidence` makes `ε_mca ≥ I(δ)/q` exact on the far stratum).
Two independent attacks on the prize converge to the same residual: the *average-term* closed form
`δ* = H_q⁻¹(1 − ρ − log_q(1/ε*)/n)` is the **first moment** of `I`, and its residual
`(R): worst ≤ average·(1+o(1))` is exactly the higher-MDS **failure-correction** `κ_d` (the
worst−average excess = the spectral error of the line–ball incidence operator; the `d=2` case is the
additive energy `E(μ_n)`). The prize is to bound that spectral error in the regime `n ≪ √q`, where
the additive-character (Weil) bound over `F_q` is vacuous.

This file builds the structural lever that neither attack had used: **the incidence is invariant
under code automorphisms.** Concretely, if a permutation `σ` of the coordinates fixes the code `C`
(setwise, `w ∈ C ↔ w ∘ σ ∈ C`), then relabelling the line by `σ` leaves the *bad-scalar set itself*
unchanged:

  `explainableScalars C δ (u₀ ∘ σ) (u₁ ∘ σ) = explainableScalars C δ u₀ u₁`.

For Reed–Solomon on a multiplicative subgroup `μ_n` (the prize domain), the dilations `x ↦ g·x`
(`g ∈ μ_n`) are coordinate permutations that fix the code — `p(g·x)` is again a degree-`<k`
polynomial — so the incidence carries the **full `Z/n` cyclic symmetry**. The maximizing line may
therefore be sought in a fundamental domain, and on a dilation-*fixed* line (a monomial direction
`u₁ = x^a`) the line–ball incidence operator commutes with the cyclic shift, i.e. it is **circulant**
and block-diagonalizes over the multiplicative characters of `μ_n ≅ Z/n`. That is the right home for
the missing spectral bound on `(R)`/`κ_d`: a per-`Z/n`-frequency estimate rather than a single
additive-character sum over `F_q`.

The core equivariance is purely combinatorial and unconditional — axiom-clean
`[propext, Classical.choice, Quot.sound]`.
-/

open Finset
open scoped NNReal ENNReal

namespace ProximityGap.FarCosetExplosion

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

open Classical in
/-- The **far-line incidence (bad-scalar) set**: the scalars `γ` for which the affine line
`u₀ + γ·u₁` agrees with some codeword of `C` on a witness-sized (`≥ (1−δ)n`) set. On the far
stratum this is the bad set whose size `ε_mca · q` equals (`FarCosetExplosion.badScalars_eq_explainable`,
`epsMCA_ge_far_incidence`). -/
noncomputable def explainableScalars (C : Set (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) : Finset F :=
  Finset.univ.filter (fun γ : F =>
    ∃ S : Finset ι, (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι ∧
      ∃ w ∈ C, ∀ i ∈ S, w i = u₀ i + γ • u₁ i)

/-- **One inclusion of the equivariance.** If the permutation `σ` maps codewords into `C` under
precomposition (`w ∘ σ ∈ C → w ∈ C`), then every bad scalar of the `σ`-relabelled line `(u₀∘σ, u₁∘σ)`
is already a bad scalar of `(u₀, u₁)`: push the witness set forward by `σ` and the witnessing
codeword back by `σ⁻¹`. -/
theorem explainableScalars_subset_of_aut (C : Set (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A)
    (σ : ι ≃ ι) (hC : ∀ w : ι → A, w ∘ σ ∈ C → w ∈ C) :
    explainableScalars (F := F) C δ (u₀ ∘ σ) (u₁ ∘ σ)
      ⊆ explainableScalars (F := F) C δ u₀ u₁ := by
  classical
  intro γ hγ
  simp only [explainableScalars, mem_filter, mem_univ, true_and] at hγ ⊢
  obtain ⟨S, hsz, w, hwC, hw⟩ := hγ
  refine ⟨S.map σ.toEmbedding, ?_, w ∘ σ.symm, ?_, ?_⟩
  · -- the witness set keeps its size under the relabelling
    rwa [Finset.card_map]
  · -- the witnessing codeword stays in `C`: `(w ∘ σ.symm) ∘ σ = w ∈ C`
    refine hC (w ∘ σ.symm) ?_
    have : (w ∘ σ.symm) ∘ σ = w := by
      funext i; simp
    rwa [this]
  · -- agreement transports along `σ`
    intro j hj
    rw [Finset.mem_map] at hj
    obtain ⟨i, hiS, hij⟩ := hj
    simp only [Equiv.coe_toEmbedding] at hij
    subst hij
    have := hw i hiS
    simpa using this

/-- **Automorphism-equivariance of the far-line incidence (the structural lever).** If a coordinate
permutation `σ` fixes the code `C` setwise (`w ∈ C ↔ w ∘ σ ∈ C`), then the bad-scalar set of the line
`(u₀, u₁)` is *unchanged* by relabelling the line through `σ`:

  `explainableScalars C δ (u₀ ∘ σ) (u₁ ∘ σ) = explainableScalars C δ u₀ u₁`.

Consequently the far-line incidence `I(δ)` is invariant under the automorphism group of `C`. For
Reed–Solomon on `μ_n`, that group contains all dilations `x ↦ g·x` (`g ∈ μ_n`), giving `I(δ)` the
full `Z/n` cyclic symmetry — the symmetry that block-diagonalizes the line–ball incidence operator
over the multiplicative characters of `μ_n` (the computational home of the residual `(R)`/`κ_d`). -/
theorem explainableScalars_comp_aut (C : Set (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A)
    (σ : ι ≃ ι) (hC : ∀ w : ι → A, w ∈ C ↔ w ∘ σ ∈ C) :
    explainableScalars (F := F) C δ (u₀ ∘ σ) (u₁ ∘ σ)
      = explainableScalars (F := F) C δ u₀ u₁ := by
  classical
  refine Finset.Subset.antisymm
    (explainableScalars_subset_of_aut C δ u₀ u₁ σ (fun w h => (hC w).mpr h)) ?_
  -- reverse inclusion: apply the forward lemma to `σ.symm`, after rewriting `(u • ∘ σ) ∘ σ.symm = u`
  have hCsymm : ∀ w : ι → A, w ∘ σ.symm ∈ C → w ∈ C := by
    intro w hw
    have h2 := (hC (w ∘ σ.symm)).mp hw
    rwa [show (w ∘ σ.symm) ∘ σ = w from by funext i; simp] at h2
  -- direct reverse inclusion
  intro γ hγ
  have hsub := explainableScalars_subset_of_aut (F := F) C δ (u₀ ∘ σ) (u₁ ∘ σ) σ.symm hCsymm
  have hrw₀ : (u₀ ∘ σ) ∘ σ.symm = u₀ := by funext i; simp
  have hrw₁ : (u₁ ∘ σ) ∘ σ.symm = u₁ := by funext i; simp
  rw [hrw₀, hrw₁] at hsub
  exact hsub hγ

/-- **The incidence count is automorphism-invariant.** The cardinality form of
`explainableScalars_comp_aut`: relabelling a far line by a code automorphism preserves its bad-scalar
*count* — hence preserves the lower bound `ε_mca ≥ #/q` of `epsMCA_ge_far_incidence`. The far-line
incidence `I(δ)` is a class function on the automorphism orbits of lines. -/
theorem explainableScalars_card_comp_aut (C : Set (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A)
    (σ : ι ≃ ι) (hC : ∀ w : ι → A, w ∈ C ↔ w ∘ σ ∈ C) :
    (explainableScalars (F := F) C δ (u₀ ∘ σ) (u₁ ∘ σ)).card
      = (explainableScalars (F := F) C δ u₀ u₁).card := by
  rw [explainableScalars_comp_aut C δ u₀ u₁ σ hC]

/-! ## Reed-Solomon multiplicative rotations -/

/-- **RS-domain rotation instance of far-line incidence equivariance.** If a coordinate
permutation `σ` scales the evaluation domain by `g`, `domain (σ i) = g * domain i`, then the
Reed-Solomon code `ReedSolomon.code domain k` is fixed by precomposition with `σ`. Consequently
the far-line bad-scalar set itself is invariant:

`explainableScalars RS δ (u₀ ∘ σ) (u₁ ∘ σ) = explainableScalars RS δ u₀ u₁`.

This is the generic smooth-domain rotation bridge needed by the #389 cyclic/Fourier attack: for
`μ_n`, choosing `σ` to be multiplication by a subgroup generator gives the `Z/n` symmetry of the
line-incidence operator. -/
theorem explainableScalars_rs_rotate (domain : ι ↪ F) (k : ℕ) (σ : Equiv.Perm ι) (g : F)
    (hg0 : g ≠ 0) (hg : ∀ i, domain (σ i) = g * domain i)
    (δ : ℝ≥0) (u₀ u₁ : ι → F) :
    explainableScalars (F := F) (ReedSolomon.code domain k : Set (ι → F)) δ
        (u₀ ∘ ⇑σ) (u₁ ∘ ⇑σ)
      = explainableScalars (F := F) (ReedSolomon.code domain k : Set (ι → F)) δ u₀ u₁ := by
  have hginv : ∀ i, domain (σ⁻¹ i) = g⁻¹ * domain i := by
    intro i
    have h := hg (σ⁻¹ i)
    simp only [Equiv.Perm.inv_def, Equiv.apply_symm_apply] at h ⊢
    rw [h, ← mul_assoc, inv_mul_cancel₀ hg0, one_mul]
  refine explainableScalars_comp_aut (F := F)
    (ReedSolomon.code domain k : Set (ι → F)) δ u₀ u₁ σ ?_
  intro w
  constructor
  · intro hw
    exact ProximityGap.MCAEquivariance.comp_perm_mem_code σ g hg hw
  · intro hw
    have hback :=
      ProximityGap.MCAEquivariance.comp_perm_mem_code σ⁻¹ g⁻¹ hginv (w := w ∘ ⇑σ) hw
    have hwid : (w ∘ ⇑σ) ∘ ⇑(Equiv.symm σ) = w := by
      funext i
      simp [Function.comp]
    simpa [hwid] using hback

/-- Cardinality form of `explainableScalars_rs_rotate`: RS multiplicative domain rotations preserve
the far-line incidence count. -/
theorem explainableScalars_card_rs_rotate (domain : ι ↪ F) (k : ℕ) (σ : Equiv.Perm ι) (g : F)
    (hg0 : g ≠ 0) (hg : ∀ i, domain (σ i) = g * domain i)
    (δ : ℝ≥0) (u₀ u₁ : ι → F) :
    (explainableScalars (F := F) (ReedSolomon.code domain k : Set (ι → F)) δ
        (u₀ ∘ ⇑σ) (u₁ ∘ ⇑σ)).card
      = (explainableScalars (F := F) (ReedSolomon.code domain k : Set (ι → F)) δ u₀ u₁).card := by
  rw [explainableScalars_rs_rotate domain k σ g hg0 hg δ u₀ u₁]

end ProximityGap.FarCosetExplosion

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms ProximityGap.FarCosetExplosion.explainableScalars_subset_of_aut
#print axioms ProximityGap.FarCosetExplosion.explainableScalars_comp_aut
#print axioms ProximityGap.FarCosetExplosion.explainableScalars_card_comp_aut
#print axioms ProximityGap.FarCosetExplosion.explainableScalars_rs_rotate
#print axioms ProximityGap.FarCosetExplosion.explainableScalars_card_rs_rotate
