/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Whir.ProximityGen

/-!
# Affine-line WHIR proximity generator

This sidecar packages the concrete `parℓ = Fin 2` generator `γ ↦ (1, γ)`
used by the ABF26 `epsMCA` bridge in `MutualCorrAgreement.lean`.
-/

namespace Generator

open ProbabilityTheory

variable {ι F : Type} [Semiring F] [Fintype F] [DecidableEq F] [Fintype ι] [Nonempty ι]

/-- The affine-line generator map `γ ↦ (1, γ)` used by the ABF26 `epsMCA`
bridge for the `parℓ = 2` WHIR case. -/
def whirAffineLineGenMap (γ : F) : Fin 2 → F :=
  fun j => if j = 0 then 1 else γ

omit [Fintype F] [DecidableEq F] in
lemma whirAffineLineGenMap_injective [One F] :
    Function.Injective (whirAffineLineGenMap (F := F)) := by
  intro γ γ' h
  have := congrFun h 1
  simpa [whirAffineLineGenMap] using this

/-- The WHIR `ProximityGenerator` whose randomness rows are exactly the
affine-line tuples `(1, γ)`. The analytic parameters are call-site data: the
probability bound is supplied separately by the `epsMCA` bridge. -/
noncomputable def whirAffineLineProximityGenerator
    (C : LinearCode ι F) (rate : ℝ)
    (B : LinearCode ι F → Type → ℝ)
    (err : LinearCode ι F → Type → ℝ → ENNReal) :
    ProximityGenerator ι F :=
  { C := C
    parℓ := Fin 2
    hℓ := inferInstance
    Gen := Finset.image (whirAffineLineGenMap (F := F)) (Finset.univ : Finset F)
    Gen_nonempty := by
      exact ⟨⟨whirAffineLineGenMap (F := F) (Classical.ofNonempty), by simp⟩⟩
    rate := rate
    B := B
    err := err }

end Generator
