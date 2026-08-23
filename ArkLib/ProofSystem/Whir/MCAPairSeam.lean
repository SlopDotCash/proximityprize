/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Whir.MutualCorrAgreement

/-!
# The pair-generator seam: `hasMutualCorrAgreement` for the affine-line `genRSC` from `ε_mca`

The WHIR-side MCA notion (`hasMutualCorrAgreement`) samples a combiner from the power
generator `genRSC` and bounds the per-row `proximityCondition`; the ABF26/Hab25 side proves
bounds on `ε_mca` (the sup over word stacks of the uniform-scalar `mcaEvent` probability).
This file closes the seam for the **pair case** (`parℓ = Fin 2` with exponents `(0, 1)`,
i.e. the affine-line combiner `(1, γ)`):

* `pr_uniform_subtype_image` — sampling uniformly from the image finset of an injective map
  is the same as sampling the parameter: pure counting through
  `prob_uniform_eq_card_filter_div_card` and a `Finset.card_bij`;
* `hasMutualCorrAgreement_genRSC_pair_of_epsMCA_le` — the seam: if
  `ε_mca(C, δ) ≤ errStar δ` for all `δ` in the admissible range, then the affine-line
  `genRSC` has mutual correlated agreement with that error. The combiner identification
  `(γ^0, γ^1) = (1, γ)` feeds the proven predicate bridge
  `proximityCondition_imp_mcaEvent_affineLine`, and the sup over stacks lands on `ε_mca`.

Consequently the Johnson-side chain (`JohnsonNumericBound` ⇒
`ε_mca ≤ ofReal (johnsonBoundReal …)`) discharges the WHIR pair-generator MCA obligation as
soon as the closed-form comparison `ofReal (johnsonBoundReal …) ≤ errStar δ` holds — the
remaining inputs are parameter arithmetic and the `parℓ > 2` extension, no probability or
sampling content remains.

Axiom-clean: `[propext, Classical.choice, Quot.sound]`.
-/

namespace MutualCorrAgreement

open NNReal Generator ProbabilityTheory ReedSolomon Finset

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
         {ι : Type} [Fintype ι] [Nonempty ι]

open Classical in
/-- **Uniform sampling from the image of an injective map is parameter sampling** —
pure counting: both probabilities are `#filter / #total`, the totals agree
(`card_image_of_injective`), and the filters biject along the map. -/
lemma pr_uniform_subtype_image {β : Type} [DecidableEq β]
    (g : F → β) (hg : Function.Injective g) (E : β → Prop) :
    haveI : Nonempty ↥(Finset.univ.image g) :=
      Finset.nonempty_coe_sort.mpr (Finset.image_nonempty.mpr Finset.univ_nonempty)
    (Pr_{let r ←$ᵖ ↥(Finset.univ.image g)}[E ↑r]) = Pr_{let γ ←$ᵖ F}[E (g γ)] := by
  haveI : Nonempty ↥(Finset.univ.image g) :=
    Finset.nonempty_coe_sort.mpr (Finset.image_nonempty.mpr Finset.univ_nonempty)
  rw [prob_uniform_eq_card_filter_div_card, prob_uniform_eq_card_filter_div_card]
  -- denominators agree
  have hden : Fintype.card ↥(Finset.univ.image g) = Fintype.card F := by
    rw [Fintype.card_coe, Finset.card_image_of_injective _ hg, Finset.card_univ]
  rw [hden]
  -- numerators biject
  have hnum : (Finset.univ.filter
      (fun r : ↥(Finset.univ.image g) => E ↑r)).card =
      (Finset.univ.filter (fun γ : F => E (g γ))).card := by
    refine (Finset.card_bij
      (i := fun (γ : F) (hγ : γ ∈ Finset.univ.filter (fun γ : F => E (g γ))) =>
        (⟨g γ, Finset.mem_image_of_mem g (Finset.mem_univ γ)⟩ :
          ↥(Finset.univ.image g)))
      ?_ ?_ ?_).symm
    · intro γ hγ
      rw [Finset.mem_filter] at hγ ⊢
      exact ⟨Finset.mem_univ _, hγ.2⟩
    · intro γ₁ h₁ γ₂ h₂ heq
      exact hg (by simpa [Subtype.ext_iff] using heq)
    · intro r hr
      rw [Finset.mem_filter] at hr
      obtain ⟨γ, _, hγ⟩ := Finset.mem_image.mp r.2
      refine ⟨γ, ?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [hγ]
        exact hr.2
      · exact Subtype.ext hγ
  rw [hnum]

open Classical in
/-- **The pair-generator seam.** For the affine-line power generator
(`parℓ = Fin 2`, exponents `(0, 1)`, combiner `(1, γ)` with `γ` uniform), an
`ε_mca`-bound on the underlying code yields `hasMutualCorrAgreement`:

  `ε_mca(C, δ) ≤ errStar δ` for `0 < δ < 1 − B*`  ⟹  the generator has MCA `(B*, errStar)`.

Sampling the generator is parameter sampling (`pr_uniform_subtype_image`), the per-row
event implies the ABF26 `mcaEvent` at the same scalar
(`proximityCondition_imp_mcaEvent_affineLine`), and the stack sup is `ε_mca`. -/
theorem hasMutualCorrAgreement_genRSC_pair_of_epsMCA_le
    (φ : ι ↪ F) (m : ℕ) [Smooth φ] (exp : Fin 2 ↪ ℕ)
    (hexp0 : exp 0 = 0) (hexp1 : exp 1 = 1)
    (BStar : ℝ) (hB : 0 ≤ BStar) (errStar : ℝ → ENNReal)
    (heps : ∀ δ : ℝ≥0, 0 < δ → (δ : ℝ) < 1 - BStar →
      _root_.ProximityGap.epsMCA (F := F) (A := F)
        (((RSGenerator.genRSC (Fin 2) φ m exp).C : Set (ι → F))) δ ≤ errStar δ) :
    haveI : Fintype (RSGenerator.genRSC (Fin 2) φ m exp).parℓ :=
      (RSGenerator.genRSC (Fin 2) φ m exp).hℓ
    hasMutualCorrAgreement (RSGenerator.genRSC (Fin 2) φ m exp) BStar errStar := by
  intro f δ hδ
  -- work at the literal `Fin 2`; everything transfers by definitional unfolding of `genRSC`
  let f₂ : Fin 2 → ι → F := f
  let C : LinearCode ι F := smoothCode φ m
  -- the radius is below 1
  have hδ1 : δ < 1 := by
    have h2 := hδ.2
    have : (δ : ℝ) < 1 := lt_of_lt_of_le h2 (by linarith)
    exact_mod_cast this
  -- the power map and its injectivity
  set g : F → (Fin 2 → F) := fun r => fun j => r ^ (exp j) with hg_def
  have hginj : Function.Injective g := by
    intro a b hab
    have h1 := congrFun hab 1
    simpa [hg_def, hexp1] using h1
  haveI : Nonempty ↥(Finset.univ.image g) :=
    Finset.nonempty_coe_sort.mpr (Finset.image_nonempty.mpr Finset.univ_nonempty)
  -- sampling the generator is sampling the parameter
  have hpr := pr_uniform_subtype_image g hginj
    (fun r => proximityCondition f₂ δ r C)
  -- the per-scalar event implies the ABF26 `mcaEvent`
  have hcomb : ∀ γ : F, g γ = (fun j : Fin 2 => if j = 0 then 1 else γ) := by
    intro γ
    funext j
    fin_cases j <;> simp [hg_def, hexp0, hexp1]
  have himp : ∀ γ : F, proximityCondition f₂ δ (g γ) C →
      _root_.ProximityGap.mcaEvent (F := F) (A := F)
        ((C : Set (ι → F))) δ (f₂ 0) (f₂ 1) γ := by
    intro γ h
    refine proximityCondition_imp_mcaEvent_affineLine hδ1 f₂ γ ?_
    rwa [hcomb γ] at h
  have hmain : (Pr_{let r ←$ᵖ ↥(Finset.univ.image g)}[
      proximityCondition f₂ δ (↑r) C]) ≤ errStar δ :=
    calc (Pr_{let r ←$ᵖ ↥(Finset.univ.image g)}[proximityCondition f₂ δ (↑r) C])
        = Pr_{let γ ←$ᵖ F}[proximityCondition f₂ δ (g γ) C] := hpr
      _ ≤ Pr_{let γ ←$ᵖ F}[_root_.ProximityGap.mcaEvent (F := F) (A := F)
            ((C : Set (ι → F))) δ (f₂ 0) (f₂ 1) γ] :=
          Pr_le_Pr_of_implies _ _ _ himp
      _ ≤ _root_.ProximityGap.epsMCA (F := F) (A := F) ((C : Set (ι → F))) δ :=
          le_iSup (fun u : Code.WordStack F (Fin 2) ι =>
            Pr_{let γ ←$ᵖ F}[_root_.ProximityGap.mcaEvent (F := F) (A := F)
              ((C : Set (ι → F))) δ (u 0) (u 1) γ]) f₂
      _ ≤ errStar δ := heps δ hδ.1 hδ.2
  exact hmain

end MutualCorrAgreement

/-! ## Axiom audit — all kernel-clean. -/
#print axioms MutualCorrAgreement.pr_uniform_subtype_image
#print axioms MutualCorrAgreement.hasMutualCorrAgreement_genRSC_pair_of_epsMCA_le
