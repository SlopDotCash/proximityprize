/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.Extensions.ProofSystem.Sumcheck.Structured

/-!
# Compatibility for prismalinear structured sumcheck

The canonical structured sumcheck accepts a per-variable multiplier bound. The old
specialization names abbreviate that same implementation.
-/

noncomputable section
namespace Sumcheck.Structured.Prismalinear

abbrev SumcheckMultiplierParam (L : Type) [CommSemiring L] {ℓ : ℕ} (Context : Type)
    (multpolyBound : Fin ℓ → ℕ) :=
  Sumcheck.Structured.SumcheckMultiplierParam L ℓ Context multpolyBound

abbrev computeRoundPoly {L : Type} [CommSemiring L] {ℓ : ℕ} {Context : Type}
    {multpolyBound : Fin ℓ → ℕ} (param : SumcheckMultiplierParam L Context multpolyBound)
    (ctx : Context) (t : Sumcheck.Structured.MultilinearPoly L ℓ) :=
  Sumcheck.Structured.computeRoundPoly ℓ param ctx t

end Sumcheck.Structured.Prismalinear
