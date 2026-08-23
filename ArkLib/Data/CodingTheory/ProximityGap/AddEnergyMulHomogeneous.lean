/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.AddEnergyCubeBound

/-!
# Multiplicative homogeneity of additive energy for a subgroup (#357)

The additive energy `E(G) = #{(y₁,y₂,y₃,y₄)∈G⁴ : y₁+y₂ = y₃+y₄}` of a *multiplicative* subgroup `G`
(the smooth FRI evaluation domain `⟨ω⟩`) has extra structure: dividing the energy equation by `y₄`
(a unit, since `0 ∉ G`) and using that `G` is closed under multiplication and inverses, the four-
variable count collapses to `|G|` copies of a **three-variable** count normalized at `1`:

  `addEnergy_eq_card_mul_normalizedCount`:
  `E(G) = |G| · #{(z₁,z₂,z₃)∈G³ : z₁+z₂ = z₃+1}`.

This is the standard first step of every sum-product bound on a multiplicative subgroup
(Heath-Brown–Konyagin/Shkredov): it reduces bounding `E(G) ≪ |G|^{5/2}` to bounding the normalized
count `N := #{z₁+z₂ = z₃+1}` by `≪ |G|^{3/2}`. The reduction is **elementary** (a multiplicative
reindexing bijection `y_i ↦ z_i·y₄`); the bound on `N` is the hard open sum-product input (dossier
§24). Here we land only the exact reduction — the honest, completable bridge.

**Honest scope:** an algebraic identity for the additive-energy API; it does not bound `N` (hence does
not pin `δ*`). It is the formal entry point a future `N ≪ |G|^{3/2}` estimate plugs into to sharpen
the anti-concentration ladder.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset

namespace ArkLib.ProximityGap.SubgroupGaussSumFourthMoment

variable {F : Type*} [Field F] [DecidableEq F]

/-- The normalized three-variable count `N = #{(z₁,z₂,z₃)∈G³ : z₁+z₂ = z₃+1}`. -/
def normalizedEnergyCount (G : Finset F) : ℕ :=
  ∑ z₁ ∈ G, ∑ z₂ ∈ G, ∑ z₃ ∈ G, (if z₁ + z₂ = z₃ + 1 then 1 else 0)

/-- **Reindexing helper: multiplication by a subgroup unit permutes `G`-sums.** For `c ∈ G` (a unit,
as `0 ∉ G`), `∑_{y∈G} f y = ∑_{z∈G} f (z·c)`, since `z ↦ z·c` is a bijection `G → G`. -/
theorem sum_mul_unit_reindex (G : Finset F)
    (hmul : ∀ a ∈ G, ∀ b ∈ G, a * b ∈ G) (hinv : ∀ a ∈ G, a⁻¹ ∈ G) (h0 : (0 : F) ∉ G)
    {c : F} (hc : c ∈ G) (f : F → ℕ) :
    ∑ y ∈ G, f y = ∑ z ∈ G, f (z * c) := by
  have hcne : c ≠ 0 := fun h => h0 (h ▸ hc)
  refine Finset.sum_nbij' (fun y => y * c⁻¹) (fun z => z * c) ?_ ?_ ?_ ?_ ?_
  · intro y hy; exact hmul y hy c⁻¹ (hinv c hc)
  · intro z hz; exact hmul z hz c hc
  · intro y _; show y * c⁻¹ * c = y; rw [mul_assoc, inv_mul_cancel₀ hcne, mul_one]
  · intro z _; show z * c * c⁻¹ = z; rw [mul_assoc, mul_inv_cancel₀ hcne, mul_one]
  · intro y _; show f y = f (y * c⁻¹ * c); rw [mul_assoc, inv_mul_cancel₀ hcne, mul_one]

/-- **Multiplicative homogeneity of additive energy.** For a finite multiplicative subgroup `G`
(closed under product and inverse, `0 ∉ G`), `E(G) = |G| · N` where
`N = #{(z₁,z₂,z₃)∈G³ : z₁+z₂ = z₃+1}`. Reduces the 4-variable energy to the normalized 3-variable
count — the entry point of the sum-product program. -/
theorem addEnergy_eq_card_mul_normalizedCount (G : Finset F)
    (hmul : ∀ a ∈ G, ∀ b ∈ G, a * b ∈ G) (hinv : ∀ a ∈ G, a⁻¹ ∈ G) (h0 : (0 : F) ∉ G) :
    addEnergy G = G.card * normalizedEnergyCount G := by
  classical
  -- Step A: bring `y₄` to the outermost position.
  have stepA : addEnergy G
      = ∑ y₄ ∈ G, ∑ y₁ ∈ G, ∑ y₂ ∈ G, ∑ y₃ ∈ G,
          (if y₁ + y₂ = y₃ + y₄ then (1 : ℕ) else 0) := by
    rw [addEnergy]
    -- swap innermost (y₃,y₄)
    have e1 : (∑ y₁ ∈ G, ∑ y₂ ∈ G, ∑ y₃ ∈ G, ∑ y₄ ∈ G,
        (if y₁ + y₂ = y₃ + y₄ then (1 : ℕ) else 0))
        = ∑ y₁ ∈ G, ∑ y₂ ∈ G, ∑ y₄ ∈ G, ∑ y₃ ∈ G,
          (if y₁ + y₂ = y₃ + y₄ then (1 : ℕ) else 0) :=
      Finset.sum_congr rfl (fun y₁ _ => Finset.sum_congr rfl (fun y₂ _ => Finset.sum_comm))
    rw [e1]
    -- swap (y₂,y₄)
    have e2 : (∑ y₁ ∈ G, ∑ y₂ ∈ G, ∑ y₄ ∈ G, ∑ y₃ ∈ G,
        (if y₁ + y₂ = y₃ + y₄ then (1 : ℕ) else 0))
        = ∑ y₁ ∈ G, ∑ y₄ ∈ G, ∑ y₂ ∈ G, ∑ y₃ ∈ G,
          (if y₁ + y₂ = y₃ + y₄ then (1 : ℕ) else 0) :=
      Finset.sum_congr rfl (fun y₁ _ => Finset.sum_comm)
    rw [e2, Finset.sum_comm]
  rw [stepA]
  -- Step B: each inner triple sum (over y₁,y₂,y₃) equals `N`, independent of `y₄`.
  have stepB : ∀ y₄ ∈ G,
      (∑ y₁ ∈ G, ∑ y₂ ∈ G, ∑ y₃ ∈ G, (if y₁ + y₂ = y₃ + y₄ then (1 : ℕ) else 0))
        = normalizedEnergyCount G := by
    intro y₄ hy₄
    have hy4ne : y₄ ≠ 0 := fun h => h0 (h ▸ hy₄)
    rw [sum_mul_unit_reindex G hmul hinv h0 hy₄
      (fun y₁ => ∑ y₂ ∈ G, ∑ y₃ ∈ G, (if y₁ + y₂ = y₃ + y₄ then (1 : ℕ) else 0))]
    refine Finset.sum_congr rfl (fun z₁ _ => ?_)
    rw [sum_mul_unit_reindex G hmul hinv h0 hy₄
      (fun y₂ => ∑ y₃ ∈ G, (if z₁ * y₄ + y₂ = y₃ + y₄ then (1 : ℕ) else 0))]
    refine Finset.sum_congr rfl (fun z₂ _ => ?_)
    rw [sum_mul_unit_reindex G hmul hinv h0 hy₄
      (fun y₃ => (if z₁ * y₄ + z₂ * y₄ = y₃ + y₄ then (1 : ℕ) else 0))]
    refine Finset.sum_congr rfl (fun z₃ _ => ?_)
    -- predicate equivalence after cancelling the unit `y₄`
    have hiff : (z₁ * y₄ + z₂ * y₄ = z₃ * y₄ + y₄) ↔ (z₁ + z₂ = z₃ + 1) := by
      rw [show z₁ * y₄ + z₂ * y₄ = (z₁ + z₂) * y₄ from by ring,
        show z₃ * y₄ + y₄ = (z₃ + 1) * y₄ from by ring]
      constructor
      · intro h; exact mul_right_cancel₀ hy4ne h
      · intro h; rw [h]
    exact if_congr hiff rfl rfl
  rw [Finset.sum_congr rfl stepB, Finset.sum_const, smul_eq_mul]

end ArkLib.ProximityGap.SubgroupGaussSumFourthMoment

/-! ## Axiom audit — kernel-clean. -/
#print axioms ArkLib.ProximityGap.SubgroupGaussSumFourthMoment.addEnergy_eq_card_mul_normalizedCount
