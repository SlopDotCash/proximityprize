/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAForallDoubleCoverRefutation

/-!
# LineDecoding: repair the refuted black-box ABF26 T4.21 statement (issue #140)

The previous `mcaForallDoubleCover_holds`, backed by the unsound `axiom mcaForallDoubleCover_residual`
(which asserted `MCAForallDoubleCover` for *all* codes/radii), has been removed: that universal claim
is genuinely FALSE. The honest result — a `ZMod 2` counterexample — is
`ProximityGap.exists_not_mcaForallDoubleCover` in
`ArkLib/Data/CodingTheory/ProximityGap/MCAForallDoubleCoverRefutation.lean`; here we package it as
the `¬ ∀` form. The per-instance double cover remains a genuine hypothesis supplied by the GS
interpolation route.
-/

namespace CodingTheory

/-- Re-export of the proven refutation: the universal T4.21 double-cover hypothesis is false. -/
theorem mcaForallDoubleCover_not_universal :
    ¬ (∀ {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
         {F : Type} [Field F] [Fintype F] [DecidableEq F]
         {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]
         (C : Set (ι → A)) (δ : NNReal),
         ProximityGap.MCAForallDoubleCover (F := F) (A := A) C δ) := by
  intro H
  obtain ⟨ι, iι, nι, dι, F, fF, ftF, dF, A, ftA, dA, acA, mA, C, δ, hC⟩ :=
    ProximityGap.exists_not_mcaForallDoubleCover
  exact hC (@H ι iι nι dι F fF ftF dF A ftA dA acA mA C δ)

end CodingTheory
