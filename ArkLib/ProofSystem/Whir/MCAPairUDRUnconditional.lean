/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Whir.MCARscPairUDR

/-!
# The pair-generator UDR mutual correlated agreement, unconditionally

`mca_rsc_pair_holds` establishes the pair power generator's mutual correlated agreement
below the unique-decoding radius for every smooth Reed–Solomon code, parameterized over an
exponent embedding `exp : Fin 2 ↪ ℕ` with the side condition `∀ j, exp j = j`.  This file
instantiates it at the canonical exponents `(0, 1)`, discharging the side condition by
`rfl` — the unconditional form ready for the folding recursion (issue #302, cheap-win C).
-/

namespace ProximityGap

open MutualCorrAgreement ReedSolomon

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
         {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-- The canonical pair-exponent embedding `(0, 1) : Fin 2 ↪ ℕ`. -/
def pairExp : Fin 2 ↪ ℕ := ⟨fun j => (j : ℕ), Fin.val_injective⟩

/-- **Pair-generator MCA below the unique-decoding radius, unconditional.**  The
`(1, γ)`-combiner pair generator at the canonical exponents `(0, 1)` has mutual correlated
agreement for every smooth Reed–Solomon code `RS[F, φ, 2^m]` with `2^m ≤ |ι|`: the
`B* = (1+ρ)/2`, `errStar = |ι|/|F|` bounds of `mca_rsc`, with no exponent side
condition. -/
theorem mca_rsc_pair_unconditional (α : F) (φ : ι ↪ F) (m : ℕ) [Smooth φ]
    (hk : 2 ^ m ≤ Fintype.card ι) :
    mca_rsc α φ m (Fin 2) pairExp :=
  mca_rsc_pair_holds α φ m pairExp hk (fun _ => rfl)

end ProximityGap

/-! ## Axiom audit -/
#print axioms ProximityGap.mca_rsc_pair_unconditional
