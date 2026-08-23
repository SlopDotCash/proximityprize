/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumSecondMoment

/-!
# Coset-invariance of the subgroup Gauss sum (#389)

The incomplete character sum `η_b = ∑_{y∈G} ψ(b·y)` is invariant under multiplying the frequency
`b` by any element `g` that permutes `G` (e.g. `g ∈ G` when `G` is a multiplicative subgroup):
`η_{g·b} = η_b`.  Hence the spectrum `{‖η_b‖ : b}` is constant on the `μ_n`-cosets of `F^×`, so it
takes only `(q−1)/|G|` distinct values — the worst-case incomplete-sum bound (the δ\* interior
residual, CLAUDE.md face #3) need only be checked on one representative per coset, not all `q`
frequencies. Axiom-clean. Issue #389.
-/

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

namespace ArkLib.ProximityGap.SubgroupGaussSumCosetInv

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Coset-invariance.** If left-multiplication by `g` (a unit) maps `G` into itself both ways,
then `η_{g·b} = η_b`. -/
theorem eta_smul_invariant {ψ : AddChar F ℂ} (G : Finset F) {g b : F}
    (hmem : ∀ x ∈ G, g * x ∈ G) (hmem' : ∀ x ∈ G, g⁻¹ * x ∈ G) (hg : g ≠ 0) :
    eta ψ G (g * b) = eta ψ G b := by
  unfold eta
  refine Finset.sum_nbij' (fun x => g * x) (fun y => g⁻¹ * y) ?_ ?_ ?_ ?_ ?_
  · intro x hx; exact hmem x hx
  · intro y hy; exact hmem' y hy
  · intro x _; field_simp
  · intro y _; field_simp
  · intro x _
    congr 1
    ring

end ArkLib.ProximityGap.SubgroupGaussSumCosetInv

#print axioms ArkLib.ProximityGap.SubgroupGaussSumCosetInv.eta_smul_invariant
