/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import ArkLib.Data.CodingTheory.ProximityGap.StepanovVanisherExistence
import ArkLib.Data.CodingTheory.ProximityGap.HasseMultiplicityBridge

/-!
# Concrete high-multiplicity Stepanov vanisher (Issue #232, Stepanov route)

This assembles the two genuinely-provable halves of Stepanov's auxiliary into a single concrete
existence statement: from a linearly independent family of polynomial generators with **more
generators than vanishing conditions**, there exists a *nonzero, degree-controlled* polynomial that
vanishes to multiplicity `≥ M` at every point of a prescribed finite set `P`.

The vanishing conditions are the `P.card · M` Hasse-derivative evaluations
`(hasseDeriv j Ψ).eval a = 0` for `a ∈ P`, `j < M`. Each is **linear** in the generator
coefficients, so they assemble into a single linear map `Φ` (built from `Fintype.linearCombination`,
`Polynomial.hasseDeriv`, `Polynomial.leval`, `LinearMap.pi`). When `P.card · M < #generators`,
`exists_nonzero_vanishing_combination` produces a nonzero coefficient vector in `ker Φ`; the
char-free bridge `le_rootMultiplicity_iff_hasseDeriv` upgrades the Hasse-vanishing to multiplicity
`≥ M`, and `degree_combination_le` controls the degree.

## Main result

* `exists_highMult_vanisher` — nonzero `Ψ`, `deg Ψ ≤ B`, with `M ≤ Ψ.rootMultiplicity a` for all
  `a ∈ P`, whenever `P.card · M < #generators` and the generators are linearly independent of degree
  `≤ B`. Feeds directly into the counting engine (`|P|·M ≤ deg Ψ ≤ B`).

## Honest scope

This is the assembled *existence* of a high-multiplicity vanisher — genuinely complete and
axiom-clean — but it does **not** by itself produce the Weil `√q` saving: that requires the caller's
*special-form* generator family (Frobenius-reduced, so `#generators` exceeds `P.card · M` **with `B`
small**) together with the reduced auxiliary being a nonzero *function* on `𝔽_q` (see
`StepanovFrobeniusReduction.lean`). Those remain the open construction core; `advancesOpenCore =
false`, #232 stays open.
-/

open Polynomial Finset

namespace ArkLib.CodingTheory.StepanovHighMult

open ArkLib.CodingTheory.StepanovVanisher ArkLib.CodingTheory.HasseMultiplicityBridge

variable {F : Type*} [Field F]

/-- **Existence of a high-multiplicity Stepanov vanisher from a dimension count.** Given linearly
independent polynomial generators `g : ι → F[X]` each of degree `≤ B`, a finite point set `P ⊆ F`,
and a multiplicity `M` with `P.card · M < #ι`, there is a **nonzero** `Ψ` of degree `≤ B` that
vanishes to multiplicity `≥ M` at every point of `P`.

The `P.card · M` Hasse-derivative conditions are linear in the coefficients, so a kernel/dimension
argument (`exists_nonzero_vanishing_combination`) yields the combination; the char-free Hasse bridge
turns the vanishing into the multiplicity bound. -/
theorem exists_highMult_vanisher {ι : Type*} [Fintype ι]
    (g : ι → F[X]) (hg : LinearIndependent F g) {B : ℕ}
    (hB : ∀ i, (g i).degree ≤ (B : WithBot ℕ)) (P : Finset F) (M : ℕ)
    (hlt : P.card * M < Fintype.card ι) :
    ∃ Ψ : F[X], Ψ ≠ 0 ∧ Ψ.degree ≤ (B : WithBot ℕ) ∧ ∀ a ∈ P, M ≤ Ψ.rootMultiplicity a := by
  classical
  -- the linear "evaluate Hasse derivative `j` at `a`" constraint map on the coefficient space.
  let Φ : (ι → F) →ₗ[F] ((↥P × Fin M) → F) :=
    LinearMap.pi fun p =>
      (Polynomial.leval (p.1 : F)).comp
        ((Polynomial.hasseDeriv (p.2 : ℕ)).comp (Fintype.linearCombination F g))
  have hcard : Fintype.card (↥P × Fin M) < Fintype.card ι := by
    rw [Fintype.card_prod, Fintype.card_coe, Fintype.card_fin]; exact hlt
  obtain ⟨c, hne, hΦc⟩ := exists_nonzero_vanishing_combination g hg Φ hcard
  refine ⟨∑ i, c i • g i, hne, degree_combination_le g c hB, fun a ha => ?_⟩
  refine rootMultiplicity_ge_of_hasseDeriv_vanish hne a M (fun j hj => ?_)
  -- read off the `(a, j)` coordinate of `Φ c = 0`.
  have hzero : Φ c (⟨⟨a, ha⟩, ⟨j, hj⟩⟩ : ↥P × Fin M) = 0 := by rw [hΦc]; rfl
  simpa only [Φ, LinearMap.pi_apply, LinearMap.comp_apply, Polynomial.leval_apply,
    Fintype.linearCombination_apply] using hzero

end ArkLib.CodingTheory.StepanovHighMult

/-! ## Axiom audit -/
section AxiomAudit
open ArkLib.CodingTheory.StepanovHighMult
#print axioms exists_highMult_vanisher
end AxiomAudit
