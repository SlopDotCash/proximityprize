/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Whir.MCAPairSeam
import ArkLib.Data.CodingTheory.ProximityGap.Hab25CellWiring

/-!
# The Hab25 → WHIR bridge: the complete wiring composition for the pair generator

This file is the **final wiring composition** for issue #302's Johnson MCA chain: it
splices the proven Hab25-side derivation (per-stack Claim-1 cells ⟹ `JohnsonNumericBound`,
`Hab25CellWiring.lean`) into the proven WHIR-side seam
(`ε_mca`-bound ⟹ `hasMutualCorrAgreement (genRSC (Fin 2))`, `MCAPairSeam.lean`), using
that `smoothCode φ m` is *definitionally* `ReedSolomon.code φ (2^m)`:

* `hasMutualCorrAgreement_genRSC_pair_of_johnsonNumericBound` — `JohnsonNumericBound` on
  the admissible range + the closed-form comparison `ofReal (johnsonBoundReal) ≤ errStar`
  yield the WHIR pair-generator MCA;
* `hasMutualCorrAgreement_genRSC_pair_of_claim1_cells` — the full conditional: per-stack
  Claim-1 cell data (the capture-above-`n` hypothesis = BCIKS20 Steps 5–7, the single
  remaining deep input) + the GS list-shape cell count + the closed-form comparison give
  the WHIR pair-generator MCA **end-to-end**.

With this file, *all* wiring of the #302 Johnson MCA chain is complete: every remaining
obligation is a self-contained mathematical unit (BCIKS20 Steps 5–7 capture; the bad-`z`
denominator budget inside the cell production; the `johnsonBoundReal ≤ errStar` parameter
arithmetic; the `parℓ > 2` extension), none of it plumbing.

Axiom-clean: `[propext, Classical.choice, Quot.sound]`.
-/

namespace MutualCorrAgreement

open NNReal Generator ProbabilityTheory ReedSolomon Finset
open CodingTheory.ProximityGap.Hab25Core
open CodingTheory.ProximityGap.Hab25Core.Hab25Johnson
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame
open scoped Polynomial

attribute [local instance] Classical.propDecidable

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
         {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- **WHIR pair-generator MCA from the Johnson numeric residual.** If
`JohnsonNumericBound φ (2^m) η δ` holds on the admissible range and the closed-form
comparison `ofReal (johnsonBoundReal …) ≤ errStar δ` holds there too, the affine-line
power generator has mutual correlated agreement `(B*, errStar)`. -/
theorem hasMutualCorrAgreement_genRSC_pair_of_johnsonNumericBound
    (φ : ι ↪ F) (m : ℕ) [Smooth φ] (exp : Fin 2 ↪ ℕ)
    (hexp0 : exp 0 = 0) (hexp1 : exp 1 = 1)
    (η : ℝ≥0) (BStar : ℝ) (hB : 0 ≤ BStar) (errStar : ℝ → ENNReal)
    (hJNB : ∀ δ : ℝ≥0, 0 < δ → (δ : ℝ) < 1 - BStar →
      JohnsonNumericBound (F₀ := F) (ι₀ := ι) φ (2 ^ m) η δ)
    (hcmp : ∀ δ : ℝ≥0, 0 < δ → (δ : ℝ) < 1 - BStar →
      ENNReal.ofReal (johnsonBoundReal (F := F) (ι := ι) φ (2 ^ m) η δ) ≤ errStar δ) :
    haveI : Fintype (RSGenerator.genRSC (Fin 2) φ m exp).parℓ :=
      (RSGenerator.genRSC (Fin 2) φ m exp).hℓ
    hasMutualCorrAgreement (RSGenerator.genRSC (Fin 2) φ m exp) BStar errStar := by
  classical
  refine hasMutualCorrAgreement_genRSC_pair_of_epsMCA_le φ m exp hexp0 hexp1
    BStar hB errStar ?_
  intro δ h1 h2
  exact le_trans (hJNB δ h1 h2) (hcmp δ h1 h2)

omit [DecidableEq ι] in
/-- **The end-to-end conditional: per-stack Claim-1 cells ⟹ WHIR pair-generator MCA.**

For every admissible `δ`, suppose every word stack's bad scalars decompose into `≤ L`
cells satisfying the Claim-1 dichotomy hypothesis at threshold `n` (capture-above-`n` —
the BCIKS20 Steps 5–7 output, the single remaining deep input), with `L` in the GS
list-size shape. Together with the closed-form comparison `johnsonBoundReal ≤ errStar`,
the affine-line power generator has mutual correlated agreement — the complete #302
Johnson MCA wiring, composed. -/
theorem hasMutualCorrAgreement_genRSC_pair_of_claim1_cells
    (φ : ι ↪ F) (m : ℕ) [Smooth φ] (exp : Fin 2 ↪ ℕ)
    (hexp0 : exp 0 = 0) (hexp1 : exp 1 = 1)
    (η : ℝ≥0) (BStar : ℝ) (hB : 0 ≤ BStar) (errStar : ℝ → ENNReal) (L : ℕ)
    (hk : 2 ^ m ≤ Fintype.card ι)
    (hL : (L : ℝ) ≤ (hab25M (Fintype.card ι) (2 ^ m) η + 1 / 2) /
      hab25RhoPlus (Fintype.card ι) (2 ^ m) ^ ((1 : ℝ) / 2))
    (hdata : ∀ δ : ℝ≥0, 0 < δ → (δ : ℝ) < 1 - BStar →
      ∀ u : Code.WordStack F (Fin 2) ι,
        ∃ (Idx : Type) (Index : Finset Idx) (Ecell : Idx → Finset F),
          Index.card ≤ L ∧
          (Finset.univ.filter
            (fun γ : F => _root_.ProximityGap.mcaEvent (F := F)
              ((ReedSolomon.code φ (2 ^ m) : Set (ι → F))) δ (u 0) (u 1) γ)) ⊆
            Index.biUnion Ecell ∧
          ∀ ij ∈ Index, Fintype.card ι < (Ecell ij).card →
            ∃ a b : F[X], a.natDegree < 2 ^ m ∧ b.natDegree < 2 ^ m ∧
              ∀ γ ∈ Ecell ij,
                AffineCaptured φ (2 ^ m) δ u γ (a, b))
    (hcmp : ∀ δ : ℝ≥0, 0 < δ → (δ : ℝ) < 1 - BStar →
      ENNReal.ofReal (johnsonBoundReal (F := F) (ι := ι) φ (2 ^ m) η δ) ≤ errStar δ) :
    haveI : Fintype (RSGenerator.genRSC (Fin 2) φ m exp).parℓ :=
      (RSGenerator.genRSC (Fin 2) φ m exp).hℓ
    hasMutualCorrAgreement (RSGenerator.genRSC (Fin 2) φ m exp) BStar errStar := by
  classical
  refine hasMutualCorrAgreement_genRSC_pair_of_johnsonNumericBound φ m exp hexp0 hexp1
    η BStar hB errStar ?_ hcmp
  intro δ h1 h2
  exact johnsonNumericBound_of_claim1_cells φ (2 ^ m) η δ L hk hL (hdata δ h1 h2)

end MutualCorrAgreement

/-! ## Axiom audit — all kernel-clean. -/
#print axioms MutualCorrAgreement.hasMutualCorrAgreement_genRSC_pair_of_johnsonNumericBound
#print axioms MutualCorrAgreement.hasMutualCorrAgreement_genRSC_pair_of_claim1_cells
