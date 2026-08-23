/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2BijectionApply

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2

namespace BCIKS20.HenselNumerator

variable {F : Type} [Field F]
variable {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- **Per-coefficient embedding commutation** (the generalization of `embed_W𝒪`):
the `𝒪`-class of a constant `C c` embeds to the direct function-field lift of `c`. This is the
factoring `liftToFunctionField = emb ∘ mk ∘ C` that lets `coeffHom` (hence `Q` and the assembled
series) descend from `𝕃` to the `ξ`-inverted localization of `𝒪`. -/
theorem emb_mk_C (c : F[X]) :
    embeddingOf𝒪Into𝕃 H
        (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) (Polynomial.C c))
      = liftToFunctionField (H := H) c := by
  rw [embeddingOf𝒪Into𝕃_mk, liftBivariate_C]

end BCIKS20.HenselNumerator

#print axioms BCIKS20.HenselNumerator.emb_mk_C
