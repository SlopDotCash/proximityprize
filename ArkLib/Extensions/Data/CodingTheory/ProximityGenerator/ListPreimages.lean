/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude

Ported from mitschabaude-bot/ArkLib:reduced-rate (commit 93fd4833b88fb0b964a29d9ca8cbbcd7ca781ba4).
-/

import ArkLib.Data.CodingTheory.ProximityGenerator.Interleaving

/-!
# List preimages outside the MCA event

A code determined by the agreement threshold has exact list preimages outside MCA.
The conclusion concerns the entire agreement set and works for interleaved module codes.
-/


namespace CoreDefinitions

/-- Every nearby generated codeword has simultaneous codeword preimages outside MCA.
Determination at the radius threshold makes their generated combination exactly the candidate;
their common agreement set is exactly its agreement set with the generated received word. -/
theorem list_preimages_of_not_isMCA {ι F A ℓ S : Type} [Fintype ι] [Field F]
    [AddCommMonoid A] [Module F A] [Fintype ℓ] [Nonempty S] [Fintype S]
    (G : Generator S ℓ F) (C : ModuleCode ι F A) (δ : ℝ)
    (determined : Code.DeterminedByAgreement C ⌈(Fintype.card ι : ℝ) * (1 - δ)⌉₊)
    (x : S) (U : ℓ → ι → A) (good : ¬ IsMCA G C x U δ)
    (c : ι → A) (hc : c ∈ C) (T : Finset ι)
    (large : (Fintype.card ι : ℝ) * (1 - δ) ≤ T.card)
    (agree : ∀ i ∈ T, c i = ∑ j, G x j • U j i) :
    Code.HasExactAgreement G C x U c := by
  apply Code.hasExactAgreement_of_not_isProjectionBad determined
    (fun bad => good ((isMCA_iff_isProjectionBad G C x U δ).mpr bad)) hc
    (Nat.ceil_le.mpr large) agree

end CoreDefinitions

#print axioms CoreDefinitions.list_preimages_of_not_isMCA
