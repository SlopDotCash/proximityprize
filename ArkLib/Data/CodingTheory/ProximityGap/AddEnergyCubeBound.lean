/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumFourthMoment

/-!
# The trivial upper bound on additive energy: `E(G) ≤ |G|³` (#357)

`SubgroupGaussSumFourthMoment` defines the additive energy
`E(G) = #{(y₁,y₂,y₃,y₄) ∈ G⁴ : y₁ + y₂ = y₃ + y₄}` and proves the lower bound `E(G) ≥ |G|²`
(`addEnergy_ge_sq`, the diagonal quadruples). This file supplies the matching **upper** bound,
completing the two-sided elementary `|G|² ≤ E(G) ≤ |G|³` API the anti-concentration ladder
(`SubgroupGaussSum{Markov,FourthMarkov,AntiConc}`, dossier §24–25) consumes:

  `addEnergy_le_cube`:  `E(G) ≤ |G|³`.

Reason: for each triple `(y₁,y₂,y₃)` the equation `y₁ + y₂ = y₃ + y₄` determines `y₄ = y₁+y₂−y₃`
uniquely, so the inner count over `y₄` is at most `1`. Pure counting; no Weil, no sum-product input.

The genuine sum-product *improvement* `E(G) ≪ |G|^{5/2}` (Heath-Brown–Konyagin/Shkredov) — the bound
that would make the fourth-moment anti-concentration `E(G)/q` sharp in the deployed regime — is the
hard open input (dossier §24); this file lands only the trivial cube ceiling, which is the honest,
elementary endpoint. With it, the combined bound `#{Johnson freqs} ≤ min(|G|, E(G)/q)` is fully
elementary-bounded as `≤ min(|G|, |G|³/q)`.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset

namespace ArkLib.ProximityGap.SubgroupGaussSumFourthMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Trivial upper bound on additive energy: `E(G) ≤ |G|³`.** For each `(y₁,y₂,y₃)` the constraint
`y₁ + y₂ = y₃ + y₄` pins `y₄ = y₁+y₂−y₃`, so the inner sum over `y₄` is `≤ 1`; summing the constant
`1` over the `|G|³` triples gives the bound. Pure counting. Matches `addEnergy_ge_sq` (`≥ |G|²`) to
bracket `E(G)` elementarily between `|G|²` and `|G|³`. -/
theorem addEnergy_le_cube (G : Finset F) : addEnergy G ≤ G.card ^ 3 := by
  rw [addEnergy]
  have hcube : G.card ^ 3 = ∑ _y₁ ∈ G, ∑ _y₂ ∈ G, ∑ _y₃ ∈ G, (1 : ℕ) := by
    simp [Finset.sum_const, smul_eq_mul]; ring
  rw [hcube]
  refine Finset.sum_le_sum (fun y₁ _ => ?_)
  refine Finset.sum_le_sum (fun y₂ _ => ?_)
  refine Finset.sum_le_sum (fun y₃ _ => ?_)
  -- inner: `∑_{y₄∈G} [y₁+y₂ = y₃+y₄] ≤ 1`, since `y₄` is determined as `y₁+y₂−y₃`.
  have heq : (∑ y₄ ∈ G, (if y₁ + y₂ = y₃ + y₄ then (1 : ℕ) else 0))
      = ∑ y₄ ∈ G, (if y₁ + y₂ - y₃ = y₄ then (1 : ℕ) else 0) := by
    refine Finset.sum_congr rfl (fun y₄ _ => ?_)
    congr 1
    rw [eq_iff_iff, sub_eq_iff_eq_add, add_comm y₄ y₃]
  rw [heq, Finset.sum_ite_eq]
  split_ifs <;> simp

end ArkLib.ProximityGap.SubgroupGaussSumFourthMoment

/-! ## Axiom audit — kernel-clean. -/
#print axioms ArkLib.ProximityGap.SubgroupGaussSumFourthMoment.addEnergy_le_cube
