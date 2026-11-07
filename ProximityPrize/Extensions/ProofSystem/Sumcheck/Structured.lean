/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.ProofSystem.Sumcheck.Structured

/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.Data.MvPolynomial.RestrictDegree
import ProximityPrize.Extensions.ProofSystem.Sumcheck.Domain

/-!
# Structured (Witness-Mode) Sumcheck — Types and Helpers

This file collects the data types and degree-bookkeeping helpers used by the
**structured sumcheck**: the witness-mode degree-2 multilinear-times-multilinear sumcheck
that underlies Binius BinaryBasefold, Binius RingSwitching, and (in the future) Hachi.

Unlike the canonical, oracle-mode sumcheck in `ArkLib/ProofSystem/Sumcheck/Spec/*`, where
the polynomial being sumchecked is an oracle statement accessible to the verifier, here
the polynomial `H = m · t` is the prover's *witness*: `t` is a committed multilinear, `m`
is a context-dependent multilinear multiplier, and `H` is their degree-2 product. The
verifier sees only the prover's round polynomials `pᵢ`, not `H` directly.

The two modes coexist as parallel primitives under `Sumcheck`.

## Future work (option C, tracked separately)

A refinement theorem connecting the two modes — given `H = m · t`, derive structured-mode
soundness from canonical-mode soundness — is left for follow-up work. Until then, the two
modes carry independent proofs.

## Contents (lifted from `Binius.BinaryBasefold.Basic` § `SumcheckOperations` and
`RingSwitching.SumcheckWitness`)

- `MultilinearPoly`, `MultiquadraticPoly` — degree-1 / degree-2 `MvPolynomial` abbreviations.
- `SumcheckMultiplierParam` — bundles a `Context → MultilinearPoly` (the multiplier `m`).
- `computeInitialSumcheckPoly` — `H := m · t` with the degree-2 proof.
- `projectToMidSumcheckPoly`, `projectToNextSumcheckPoly` — partial evaluation of `H` at
  the verifier's previous challenges.
- `SumcheckBaseContext` — `(t_eval_point, original_claim)` shared input.
- `Statement Context i` — per-round state: `(sumcheck_target, challenges, ctx)`.
- `sumcheckConsistencyProp` — claim equals hypercube sum.
- `SumcheckWitness` — per-round witness `(t', H)` (the committed multilinear + projected
  round polynomial).
-/

noncomputable section

namespace Sumcheck.Structured

open Finset MvPolynomial

section SumcheckOperations

/-- Belt-and-braces: lock in the `rfl` claim from the `PrismalinearPoly` docstring. The multilinear
case is *definitionally* the constant-1 prismalinear case, so existing multilinear consumers
(`SumcheckMultiplierParam`) compose with the prismalinear surface
(`Sumcheck.Structured.Prismalinear.SumcheckMultiplierParam` in `Structured/Prismalinear.lean`, when
`multpolyBound = fun _ => 1`) without any coercion. -/
example {L : Type} [CommSemiring L] {ℓ : ℕ} :
    MultilinearPoly L ℓ = PrismalinearPoly L (fun _ : Fin ℓ => 1) := rfl

variable {L : Type} [CommRing L] (ℓ : ℕ) [NeZero ℓ]

/-- `Hᵢ(Xᵢ, ..., X_{ℓ-1}) = ∑ ω ∈ 𝓑ᵢ, H₀(ω₀, …, ω_{i-1}, Xᵢ, …, X_{ℓ-1}) (where H₀=h)` -/
def projectToMidSumcheckPoly (t : MultilinearPoly L ℓ)
    (m : MultilinearPoly L ℓ) (i : Fin (ℓ + 1))
    (challenges : Fin i → L)
    : MultiquadraticPoly L (ℓ-i) :=
  let H₀: MultiquadraticPoly L ℓ := computeInitialSumcheckPoly (ℓ:=ℓ) t m
  let Hᵢ := fixFirstVariablesOfMQP (ℓ := ℓ) (v := ⟨i, by omega⟩)
    (H := H₀) (challenges := challenges)
  ⟨Hᵢ, by
    have hp := H₀.property
    simpa using
      (fixFirstVariablesOfMQP_degreeLE (L := L) (ℓ := ℓ) (v := ⟨i, by omega⟩)
        (poly := H₀.val) (challenges := challenges) (deg := 2) hp)
  ⟩

end SumcheckOperations

section ContextAndStatement

variable {L : Type} {ℓ : ℕ} [NeZero ℓ]

end ContextAndStatement

section ConsistencyProp

variable {L : Type} [CommRing L]

end ConsistencyProp

section Witness

end Witness

end Sumcheck.Structured
