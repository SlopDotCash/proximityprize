/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.AddEnergyMathlibBridge
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupRepresentationRoots

/-!
# Additive energy bounded by the sum of squared gcd-degrees (#357)

Assembling the HBK/Stepanov chain. The Mathlib moment identity (`Finset.addEnergy_eq_sum_sq`, via the
bridge `addEnergy_eq_mathlib`) gives `E(G) = Σ_c r(c)²` where `r(c) = #{(x,y)∈G² : x+y = c}`; the
representation bound (`SubgroupRepresentationRoots.representationCount_le_gcd_degree`) gives
`r(c) ≤ deg gcd(Xⁿ−1, (C c−X)ⁿ−1)`. Composing:

  `addEnergy_le_sum_gcd_degree_sq` :  `E(G) ≤ Σ_{c∈F} (deg gcd(Xⁿ−1, (C c−X)ⁿ−1))²`.

This reduces the open sum-product estimate `E(G) ≪ |G|^{5/2}` (⟺ `N ≪ |G|^{3/2}`, dossier §27–28) to a
**resultant count**: bounding `Σ_c (deg gcd_c)²`. Since `gcd(Xⁿ−1, (C c−X)ⁿ−1)` is nontrivial only when
`c ∈ G+G` (a common root `ω + ω'` exists), and its degree measures the multiplicity of additive
coincidences, the remaining task is the Stepanov/resultant bound on how the gcd degrees distribute over
`c` — the genuine open core, now reduced to an explicit polynomial-resultant statement.

**Honest scope:** an exact assembly; it does NOT bound `Σ_c (deg gcd_c)²` (that is the open Stepanov
input). It transforms the open estimate into a clean resultant-count target. Does not pin `δ*`.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Polynomial
open ArkLib.ProximityGap.SubgroupRepresentationRoots

namespace ArkLib.ProximityGap.SubgroupGaussSumFourthMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The moment identity via the Mathlib bridge.** `E(G) = Σ_a r(a)²` with
`r(a) = #{(x,y)∈G² : x+y = a}`. -/
theorem addEnergy_eq_sum_repFilter_sq (G : Finset F) :
    addEnergy G
      = ∑ a : F, ((G ×ˢ G).filter (fun xy => xy.1 + xy.2 = a)).card ^ 2 := by
  rw [addEnergy_eq_mathlib, Finset.addEnergy_eq_sum_sq]

/-- The two forms of the representation count agree: `#{(x,y)∈G² : x+y = c} = #{z∈G : c−z∈G}`. -/
theorem repFilter_card_eq (G : Finset F) (c : F) :
    ((G ×ˢ G).filter (fun xy => xy.1 + xy.2 = c)).card
      = (G.filter (fun z => c - z ∈ G)).card := by
  classical
  refine Finset.card_nbij' (fun xy => xy.1) (fun z => (z, c - z)) ?_ ?_ ?_ ?_
  · intro xy hxy
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hxy ⊢
    refine ⟨hxy.1.1, ?_⟩
    have hcz : c - xy.1 = xy.2 := by rw [← hxy.2]; ring
    rw [hcz]; exact hxy.1.2
  · intro z hz
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hz ⊢
    exact ⟨⟨hz.1, hz.2⟩, by ring⟩
  · intro xy hxy
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hxy
    have hcz : c - xy.1 = xy.2 := by rw [← hxy.2]; ring
    exact Prod.ext rfl hcz
  · intro z _; rfl

/-- **Additive energy bounded by the sum of squared gcd-degrees.** For the root-of-unity subgroup
`G = {z : zⁿ = 1}`, `E(G) ≤ Σ_{c∈F} (deg gcd(Xⁿ−1, (C c−X)ⁿ−1))²`. Reduces the open sum-product
estimate to a resultant count on the gcd degrees — the Stepanov frontier. -/
theorem addEnergy_le_sum_gcd_degree_sq (G : Finset F) {n : ℕ} (hn : 0 < n)
    (hGmem : ∀ z, z ∈ G ↔ z ^ n = 1) :
    addEnergy G
      ≤ ∑ c : F, ((gcd (Polynomial.X ^ n - 1 : F[X]) (reprPoly c n)).natDegree) ^ 2 := by
  rw [addEnergy_eq_sum_repFilter_sq]
  refine Finset.sum_le_sum (fun c _ => ?_)
  rw [repFilter_card_eq]
  exact Nat.pow_le_pow_left (representationCount_le_gcd_degree G hn hGmem c) 2

end ArkLib.ProximityGap.SubgroupGaussSumFourthMoment

/-! ## Axiom audit — kernel-clean. -/
#print axioms ArkLib.ProximityGap.SubgroupGaussSumFourthMoment.addEnergy_le_sum_gcd_degree_sq
