/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R46GaussModulus

/-!
# LANE A (#466 round 48): the classical bridge — `∑_b ‖η_b‖⁴ = q·E₊(G)` — welding the
  unified tower to the original A-side energy ledger

The exact identity (pure `ψ`-orthogonality):

  **`eta_fourth_moment`** :  `∑_{b∈F} ‖η_b‖⁴ = q · #{(y₁,y₂,y₃,y₄) ∈ G⁴ : y₁+y₂ = y₃+y₄}`.

Consequence: through the round-44 collapse, the A-side r = 2 ladder rung is EXACTLY
expressible in the additive energy `E₊(μ_n)` and lower moments — the campaign's ORIGINAL
A-side objects, with their in-tree exact results.  The new unified calculus and the old
energy ledger are one bookkeeping system.

Axiom-clean (`propext, Classical.choice, Quot.sound`).  Issue #466, round 48, LANE A.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R48EtaFourthMoment

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The additive energy of `G` (ordered quadruples with `y₁+y₂ = y₃+y₄`). -/
def addEnergy (G : Finset F) : ℕ :=
  ((G ×ˢ G) ×ˢ (G ×ˢ G)).filter
    (fun z => z.1.1 + z.1.2 = z.2.1 + z.2.2) |>.card

/-- **THE CLASSICAL BRIDGE (round-48 main theorem)**:
`∑_b ‖η_b‖⁴ = q·E₊(G)`. -/
theorem eta_fourth_moment {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) :
    ∑ b : F, ‖eta ψ G b‖ ^ 4 = (Fintype.card F : ℝ) * (addEnergy G : ℝ) := by
  classical
  have hchar : (0 : ℕ) < ringChar F := by
    haveI := ringChar.charP F
    exact Nat.pos_of_ne_zero (CharP.char_ne_zero_of_finite F (ringChar F))
  have hconjψ : ∀ a : F, (starRingEnd ℂ) (ψ a) = ψ (-a) := by
    intro a; rw [AddChar.starComp_apply hchar, AddChar.inv_apply]
  have hcx : (∑ b : F, (eta ψ G b * (starRingEnd ℂ) (eta ψ G b)) ^ 2)
      = (Fintype.card F : ℂ) * (addEnergy G : ℂ) := by
    have hexp : ∀ b : F, (eta ψ G b * (starRingEnd ℂ) (eta ψ G b)) ^ 2
        = ∑ z ∈ (G ×ˢ G) ×ˢ (G ×ˢ G),
            ψ (b * (z.2.1 + z.2.2 - z.1.1 - z.1.2)) := by
      intro b
      have hconjeta : (starRingEnd ℂ) (eta ψ G b) = ∑ y ∈ G, ψ (-(b * y)) := by
        rw [eta, map_sum]
        exact Finset.sum_congr rfl (fun y _ => hconjψ (b * y))
      rw [sq, hconjeta, eta]
      rw [show ((∑ y ∈ G, ψ (b*y)) * (∑ y ∈ G, ψ (-(b*y))))
            * ((∑ y ∈ G, ψ (b*y)) * (∑ y ∈ G, ψ (-(b*y))))
          = ((∑ y ∈ G, ψ (b*y)) * (∑ y ∈ G, ψ (b*y)))
            * ((∑ y ∈ G, ψ (-(b*y))) * (∑ y ∈ G, ψ (-(b*y)))) from by ring]
      symm
      calc ∑ z ∈ (G ×ˢ G) ×ˢ (G ×ˢ G), ψ (b * (z.2.1 + z.2.2 - z.1.1 - z.1.2))
          = ∑ p ∈ G ×ˢ G, ∑ p' ∈ G ×ˢ G,
              ψ (b * (p'.1 + p'.2 - p.1 - p.2)) := by rw [Finset.sum_product]
        _ = ∑ y₁ ∈ G, ∑ y₂ ∈ G, ∑ y₃ ∈ G, ∑ y₄ ∈ G,
              ψ (b * (y₃ + y₄ - y₁ - y₂)) := by
            rw [Finset.sum_product]
            refine Finset.sum_congr rfl (fun y₁ _ => Finset.sum_congr rfl (fun y₂ _ => ?_))
            rw [Finset.sum_product]
        _ = ((∑ y ∈ G, ψ (b * y)) * (∑ y ∈ G, ψ (b * y)))
            * ((∑ y ∈ G, ψ (-(b * y))) * (∑ y ∈ G, ψ (-(b * y)))) := by
            simp only [Finset.sum_mul, Finset.mul_sum]
            refine Finset.sum_congr rfl (fun y₁ _ => Finset.sum_congr rfl (fun y₂ _ =>
              Finset.sum_congr rfl (fun y₃ _ => Finset.sum_congr rfl (fun y₄ _ => ?_))))
            rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul,
              ← AddChar.map_add_eq_mul]
            congr 1
            ring
    rw [Finset.sum_congr rfl (fun b _ => hexp b), Finset.sum_comm]
    have hz : ∀ z ∈ (G ×ˢ G) ×ˢ (G ×ˢ G),
        ∑ b : F, ψ (b * (z.2.1 + z.2.2 - z.1.1 - z.1.2))
          = if z.1.1 + z.1.2 = z.2.1 + z.2.2 then (Fintype.card F : ℂ) else 0 := by
      intro z _
      have h0 := AddChar.sum_mulShift (ψ := ψ) (z.2.1 + z.2.2 - z.1.1 - z.1.2) hψ
      rw [h0]
      by_cases h : z.1.1 + z.1.2 = z.2.1 + z.2.2
      · rw [if_pos (by linear_combination -h : z.2.1 + z.2.2 - z.1.1 - z.1.2 = 0),
          if_pos h]
        try simp
      · rw [if_neg (fun hc => h (by linear_combination -hc)), if_neg h]
        try simp
    rw [Finset.sum_congr rfl hz]
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const]
    simp only [smul_zero, add_zero, nsmul_eq_mul]
    rw [mul_comm, addEnergy]
  have hpt : ∀ b : F, (eta ψ G b * (starRingEnd ℂ) (eta ψ G b)) ^ 2
      = ((‖eta ψ G b‖ ^ 4 : ℝ) : ℂ) := by
    intro b
    have h1 : eta ψ G b * (starRingEnd ℂ) (eta ψ G b) = ((‖eta ψ G b‖ ^ 2 : ℝ) : ℂ) := by
      rw [RCLike.mul_conj]; norm_cast
    rw [h1]
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun b _ => hpt b)] at hcx
  have hfin : ((∑ b : F, ‖eta ψ G b‖ ^ 4 : ℝ) : ℂ)
      = (((Fintype.card F : ℝ) * (addEnergy G : ℝ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    push_cast
    exact_mod_cast hcx
  exact_mod_cast hfin

end ArkLib.ProximityGap.Frontier.R48EtaFourthMoment

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.R48EtaFourthMoment.eta_fourth_moment
